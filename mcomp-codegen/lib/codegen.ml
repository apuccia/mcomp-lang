open Ast
open Symbol_table
open Easy_logging

let logger =
  let file_h = Handlers.File ("Code generation", Logging.Debug) in
  let cli_h = Handlers.Cli Logging.Debug in
  Logging.make_logger "Code generation" Logging.Debug [ cli_h; file_h ]

let dbg_llvalue msg llv = logger#debug "%s\n%s" msg (Llvm.string_of_llvalue llv)
let ( ++ ) cname id = "__" ^ cname ^ "_" ^ id
let ll_context = Llvm.global_context ()
let ll_module = Llvm.create_module ll_context "mcomp-lang"
let ll_i32type = Llvm.i32_type ll_context
let ll_i1type = Llvm.i1_type ll_context
let ll_i8type = Llvm.i8_type ll_context
let ll_ftype = Llvm.float_type ll_context
let ll_voidtype = Llvm.void_type ll_context

let rec to_llvm_type t =
  match t with
  | TInt -> ll_i32type
  | TBool -> ll_i1type
  | TChar -> ll_i8type
  | TArray (t', None) -> Llvm.pointer_type (to_llvm_type t')
  | TArray (t', Some s) -> Llvm.array_type (to_llvm_type t') s
  | TRef t' -> Llvm.pointer_type (to_llvm_type t')
  | TFun (args, rtype) ->
      Llvm.function_type (to_llvm_type rtype)
        (Array.of_list (List.map (fun x -> to_llvm_type x) args))
  | TVoid -> ll_voidtype
  | _ -> failwith "impossible case"

let rec get_default_v t =
  match t with
  | TInt -> Llvm.const_null ll_i32type
  | TBool -> Llvm.const_null ll_i1type
  | TChar -> Llvm.const_null ll_i8type
  | TArray (t', s) ->
      Llvm.const_array (to_llvm_type t')
        (Array.make (Option.get s) (get_default_v t'))
  | TRef _ -> Llvm.const_pointer_null (to_llvm_type t)
  | _ -> failwith "impossible case"

let codegen_globals m cname =
  match m.node with
  | FunDecl fd ->
      let mangled_name =
        if equal_identifier fd.fname "main" then fd.fname else cname ++ fd.fname
      in
      (* get function type *)
      let llt_f = to_llvm_type m.annot in
      (* define function *)
      let llv_f = Llvm.define_function mangled_name llt_f ll_module in

      dbg_llvalue ("Define function " ^ mangled_name) llv_f
  | VarDecl (i, t) ->
      let mangled_name = cname ++ i in
      (* get initial value *)
      let def_value = get_default_v t in
      (* add to global *)
      let llv_v = Llvm.define_global mangled_name def_value ll_module in

      dbg_llvalue ("Define global variable " ^ mangled_name) llv_v

let rec codegen_stmt stmt cname scope llv_f llbuilder =
  match stmt.node with
  | If (e, s1, s2) ->
      let llblock_t = Llvm.append_block ll_context "then" llv_f in
      let llblock_e = Llvm.append_block ll_context "else" llv_f in
      let llblock_c = Llvm.append_block ll_context "cont" llv_f in

      (* get value from evaluating e *)
      let llv_e = codegen_expr e cname scope llv_f llbuilder in
      (* build instruction to jump to then or else according to e *)
      let llv_c = Llvm.build_cond_br llv_e llblock_t llblock_e llbuilder in
      dbg_llvalue "Build if condition" llv_c;

      (* position in then block, generate further instructions and jump to cont *)
      Llvm.position_at_end llblock_t llbuilder |> ignore;
      let ret_then = codegen_stmt s1 cname scope llv_f llbuilder in
      if ret_then then () else Llvm.build_br llblock_c llbuilder |> ignore;

      (* position in else block, generate further instructions and jump to cont *)
      Llvm.position_at_end llblock_e llbuilder |> ignore;
      let ret_else = codegen_stmt s2 cname scope llv_f llbuilder in
      if ret_else then () else Llvm.build_br llblock_c llbuilder |> ignore;

      (* continue generating from cont *)
      Llvm.position_at_end llblock_c llbuilder |> ignore;
      ret_then && ret_else
  | While (e, s) ->
      let llblock_cond = Llvm.append_block ll_context "test_cond" llv_f in
      let llblock_w = Llvm.append_block ll_context "while_body" llv_f in
      let llblock_cont = Llvm.append_block ll_context "cont" llv_f in

      (* jump to cond block *)
      Llvm.build_br llblock_cond llbuilder |> ignore;
      (* in cond block add e instructions *)
      Llvm.position_at_end llblock_cond llbuilder;
      let llv_e = codegen_expr e cname scope llv_f llbuilder in

      (* continue loop or go to cont block according to value of e *)
      Llvm.build_cond_br llv_e llblock_w llblock_cont llbuilder |> ignore;

      (* go to while body and start generating its instructions *)
      Llvm.position_at_end llblock_w llbuilder;
      let ret = codegen_stmt s cname scope llv_f llbuilder in

      (* if there is a return statement in body stop otherwise jump to
         to cond testing *)
      if ret then () else Llvm.build_br llblock_cond llbuilder |> ignore;

      (* continue generating at cont block *)
      Llvm.position_at_end llblock_cont llbuilder;
      ret
  | DoWhile (s, e) ->
      let llblock_cond = Llvm.append_block ll_context "test_cond" llv_f in
      let llblock_dow = Llvm.append_block ll_context "dowhile_body" llv_f in
      let llblock_cont = Llvm.append_block ll_context "cont" llv_f in

      (* jump to dowhile block *)
      Llvm.build_br llblock_dow llbuilder |> ignore;

      (* in cond block generate e instructions *)
      Llvm.position_at_end llblock_dow llbuilder;
      let ret = codegen_stmt s cname scope llv_f llbuilder in
      (* if there is a return statement in body stop otherwise jump to
         to cond testing *)
      if ret then () else Llvm.build_br llblock_cond llbuilder |> ignore;

      (* in cond block generate e instructions *)
      Llvm.position_at_end llblock_cond llbuilder;
      let llv_e = codegen_expr e cname scope llv_f llbuilder in
      (* continue loop or go to cont block according to value of e *)
      Llvm.build_cond_br llv_e llblock_dow llblock_cont llbuilder |> ignore;

      logger#debug "%s\n" (Llvm.string_of_llmodule ll_module);
      (* continue generating at cont block *)
      Llvm.position_at_end llblock_cont llbuilder;
      ret
  | Expr e ->
      codegen_expr e cname scope llv_f llbuilder |> ignore;
      false
  | Return (Some e) ->
      let llv_e = codegen_expr e cname scope llv_f llbuilder in
      let llv_r = Llvm.build_ret llv_e llbuilder in
      dbg_llvalue "Build return (some) instruction" llv_r;
      true
  | Return None ->
      let llv_r = Llvm.build_ret_void llbuilder in
      dbg_llvalue "Build return (void) instruction" llv_r;
      true
  | Block sl ->
      (* create new block scope *)
      let block_scope = begin_block scope in
      let has_return =
        List.fold_left
          (fun ret s ->
            (* generate instructions of the block, if there is a return it will
               generate the following instructions but will be removed later *)
            codegen_stmt_ordec s cname block_scope llv_f llbuilder || ret)
          false sl
      in
      end_block block_scope |> ignore;
      has_return
  | Skip -> false

and codegen_lv lv cname scope llv_f llbuilder load addr =
  let load_lv llv_lv t =
    match t with
    | TRef _ ->
        if addr then llv_lv
        else
          let llv_ref = Llvm.build_load llv_lv "" llbuilder in
          if load then (
            let llv_deref = Llvm.build_load llv_ref "" llbuilder in
            dbg_llvalue "Dereferencing" llv_deref;
            llv_deref)
          else (
            dbg_llvalue "Loading reference" llv_ref;
            llv_ref)
    | TArray (_, Some _) ->
        let llv_aea =
          Llvm.build_in_bounds_gep llv_lv
            [| Llvm.const_int ll_i32type 0; Llvm.const_int ll_i32type 0 |]
            "" llbuilder
        in
        dbg_llvalue "Load address of array first element" llv_aea;
        llv_aea
    | _ ->
        if load then (
          let llv_e = Llvm.build_load llv_lv "" llbuilder in
          dbg_llvalue "Accessing basic type var" llv_e;
          llv_e)
        else llv_lv
  in

  match (lv.node, lv.annot) with
  | AccVar (None, id), t ->
      let llv_lv = lookup id scope in
      load_lv llv_lv t
  | AccVar (Some cname, id), t ->
      let mangled_name = cname ++ id in
      let llv_gvar = Llvm.lookup_global mangled_name ll_module |> Option.get in
      load_lv llv_gvar t
  | AccIndex (lv, e), _ -> (
      (* generate instructions for array indexing *)
      let llv_e = codegen_expr e cname scope llv_f llbuilder in
      (* retrieve lv address *)
      let llv_lv =
        match lv.node with
        | AccVar (Some id1, id2) ->
            Llvm.lookup_global (id1 ++ id2) ll_module |> Option.get
        | AccVar (None, id2) -> lookup id2 scope
        | _ -> failwith "impossible case"
      in
      match lv.annot with
      | TArray (TRef _, Some _) ->
          (* array of references *)
          let llv_aea =
            Llvm.build_in_bounds_gep llv_lv
              [| Llvm.const_int ll_i32type 0; llv_e |]
              "" llbuilder
          in
          if load then (
            (* dereference *)
            let llv_ref = Llvm.build_load llv_aea "" llbuilder in
            dbg_llvalue "Loading reference" llv_ref;
            let llv_deref = Llvm.build_load llv_ref "" llbuilder in
            dbg_llvalue "Deref" llv_deref;
            llv_deref)
          else llv_aea
      | TArray (_, Some _) ->
          (* accessing array of basic type *)
          let llv_aea =
            Llvm.build_in_bounds_gep llv_lv
              [| Llvm.const_int ll_i32type 0; llv_e |]
              "" llbuilder
          in
          dbg_llvalue "Loading address of array element" llv_aea;
          if load then (
            let llv_ae = Llvm.build_load llv_aea "" llbuilder in
            dbg_llvalue "Loading array element" llv_ae;
            llv_ae)
          else llv_aea
      | TArray (_, None) | TRef _ ->
          (* pass array to function or accessing array from function *)
          let llv_aa = Llvm.build_load llv_lv "" llbuilder in
          (* get address of element *)
          let llv_aea =
            Llvm.build_in_bounds_gep llv_aa [| llv_e |] "" llbuilder
          in
          dbg_llvalue "Loading address" llv_aea;
          if load then (
            let llv_ae = Llvm.build_load llv_aea "" llbuilder in
            dbg_llvalue "Loading element" llv_ae;
            llv_ae)
          else llv_aea
      | _ -> failwith "impossible case")

and codegen_expr expr cname scope llv_f llbuilder =
  match expr.node with
  | LV lv -> codegen_lv lv cname scope llv_f llbuilder true false
  | ILiteral i -> Llvm.const_int ll_i32type i
  | FLiteral f -> Llvm.const_float ll_ftype f
  | Assign (lv, e) ->
      let addr = match e.node with Address _ -> true | _ -> false in
      let llv_e = codegen_expr e cname scope llv_f llbuilder in
      let llv_lv = codegen_lv lv cname scope llv_f llbuilder false addr in

      let llv_slv = Llvm.build_store llv_e llv_lv llbuilder in
      dbg_llvalue "Build store instruction" llv_slv;
      llv_e
  | CLiteral c -> Llvm.const_int ll_i8type (Char.code c)
  | BLiteral b ->
      if b then Llvm.const_int ll_i1type 1 else Llvm.const_int ll_i1type 0
  | UnaryOp (op, e) -> (
      let llv_e = codegen_expr e cname scope llv_f llbuilder in
      match op with
      | Neg ->
          let llv_neg = Llvm.build_neg llv_e "temp_neg" llbuilder in
          dbg_llvalue "Build neg instruction" llv_neg;
          llv_neg
      | Not ->
          let llv_not = Llvm.build_not llv_e "temp_not" llbuilder in
          dbg_llvalue "Build not instruction" llv_not;
          llv_not)
  | Address lv -> codegen_lv lv cname scope llv_f llbuilder false true
  | BinaryOp (op, e1, e2) -> (
      match op with
      | And ->
          let llv_e1 = codegen_expr e1 cname scope llv_f llbuilder in
          (* retrieve block where we finished generating e1 instructions *)
          let llblock_e1 = Llvm.insertion_block llbuilder in

          let llblock_t = Llvm.append_block ll_context "and_true" llv_f in
          let llblock_f = Llvm.append_block ll_context "and_false" llv_f in

          (* if e1 is true then jump to "and_true" and start generating
             instructions to check e2 *)
          Llvm.build_cond_br llv_e1 llblock_t llblock_f llbuilder |> ignore;
          Llvm.position_at_end llblock_t llbuilder |> ignore;
          let llv_e2 = codegen_expr e2 cname scope llv_f llbuilder in

          (* retrieve block where we finished generating e2 instructions *)
          let llblock_e2 = Llvm.insertion_block llbuilder in

          Llvm.build_br llblock_f llbuilder |> ignore;
          Llvm.position_at_end llblock_f llbuilder |> ignore;

          let phi_node = Llvm.build_empty_phi ll_i1type "" llbuilder in
          Llvm.add_incoming (llv_e1, llblock_e1) phi_node;
          Llvm.add_incoming (llv_e2, llblock_e2) phi_node;

          dbg_llvalue "Build phi instruction" phi_node;
          phi_node
      | Or ->
          let llv_e1 = codegen_expr e1 cname scope llv_f llbuilder in
          (* retrieve block where we finished generating e1 instructions *)
          let llblock_e1 = Llvm.insertion_block llbuilder in

          let llblock_t = Llvm.append_block ll_context "or_true" llv_f in
          let llblock_f = Llvm.append_block ll_context "or_false" llv_f in

          (* if e1 is false then jump to "or_false" and start generating
             instructions to check e2 *)
          Llvm.build_cond_br llv_e1 llblock_t llblock_f llbuilder |> ignore;
          Llvm.position_at_end llblock_f llbuilder |> ignore;
          let llv_e2 = codegen_expr e2 cname scope llv_f llbuilder in

          (* retrieve block where we finished generating e2 instructions *)
          let llblock_e2 = Llvm.insertion_block llbuilder in

          Llvm.build_br llblock_t llbuilder |> ignore;
          Llvm.position_at_end llblock_t llbuilder |> ignore;

          let phi_node = Llvm.build_empty_phi ll_i1type "" llbuilder in
          Llvm.add_incoming (llv_e1, llblock_e1) phi_node;
          Llvm.add_incoming (llv_e2, llblock_e2) phi_node;

          dbg_llvalue "Build phi instruction" phi_node;
          phi_node
      | _ -> (
          let llv_e1 = codegen_expr e1 cname scope llv_f llbuilder in
          let llv_e2 = codegen_expr e2 cname scope llv_f llbuilder in
          match (op, e1.annot) with
          | Add, TInt ->
              let llv_iadd =
                Llvm.build_add llv_e1 llv_e2 "temp_iadd" llbuilder
              in
              dbg_llvalue "Build iadd instruction" llv_iadd;
              llv_iadd
          | Add, TFloat ->
              let llv_fadd =
                Llvm.build_fadd llv_e1 llv_e2 "temp_fadd" llbuilder
              in
              dbg_llvalue "Build fadd instruction" llv_fadd;
              llv_fadd
          | Sub, TInt ->
              let llv_isub =
                Llvm.build_sub llv_e1 llv_e2 "temp_isub" llbuilder
              in
              dbg_llvalue "Build sub instruction" llv_isub;
              llv_isub
          | Sub, TFloat ->
              let llv_fsub =
                Llvm.build_fsub llv_e1 llv_e2 "temp_fsub" llbuilder
              in
              dbg_llvalue "Build fsub instruction" llv_fsub;
              llv_fsub
          | Mult, TInt ->
              let llv_imul =
                Llvm.build_mul llv_e1 llv_e2 "temp_imult" llbuilder
              in
              dbg_llvalue "Build imult instruction" llv_imul;
              llv_imul
          | Mult, TFloat ->
              let llv_fmul =
                Llvm.build_fmul llv_e1 llv_e2 "temp_fmul" llbuilder
              in
              dbg_llvalue "Build fmul instruction" llv_fmul;
              llv_fmul
          | Div, TInt ->
              let llv_isdiv =
                Llvm.build_sdiv llv_e1 llv_e2 "temp_idiv" llbuilder
              in
              dbg_llvalue "Build idiv instruction" llv_isdiv;
              llv_isdiv
          | Div, TFloat ->
              let llv_fdiv =
                Llvm.build_fdiv llv_e1 llv_e2 "temp_fdiv" llbuilder
              in
              dbg_llvalue "Build fdiv instruction" llv_fdiv;
              llv_fdiv
          | Mod, TInt ->
              let llv_isrem =
                Llvm.build_srem llv_e1 llv_e2 "temp_imod" llbuilder
              in
              dbg_llvalue "Build imod instruction" llv_isrem;
              llv_isrem
          | Mod, TFloat ->
              let llv_fsrem =
                Llvm.build_frem llv_e1 llv_e2 "temp_fmod" llbuilder
              in
              dbg_llvalue "Build fmod instruction" llv_fsrem;
              llv_fsrem
          | Equal, TInt ->
              let llv_icmp_eq =
                Llvm.build_icmp Llvm.Icmp.Eq llv_e1 llv_e2 "temp_iequal"
                  llbuilder
              in
              dbg_llvalue "Build iequal instruction" llv_icmp_eq;
              llv_icmp_eq
          | Equal, TFloat ->
              let llv_fcmp_eq =
                Llvm.build_fcmp Llvm.Fcmp.Oeq llv_e1 llv_e2 "temp_fequal"
                  llbuilder
              in
              dbg_llvalue "Build fequal instruction" llv_fcmp_eq;
              llv_fcmp_eq
          | Neq, TInt ->
              let llv_icmp_ne =
                Llvm.build_icmp Llvm.Icmp.Ne llv_e1 llv_e2 "temp_ineq" llbuilder
              in
              dbg_llvalue "Build i not equal instruction" llv_icmp_ne;
              llv_icmp_ne
          | Neq, TFloat ->
              let llv_fcmp_neq =
                Llvm.build_fcmp Llvm.Fcmp.One llv_e1 llv_e2 "temp_fneq"
                  llbuilder
              in
              dbg_llvalue "Build fnequal instruction" llv_fcmp_neq;
              llv_fcmp_neq
          | Less, TInt ->
              let llv_icmp_slt =
                Llvm.build_icmp Llvm.Icmp.Slt llv_e1 llv_e2 "temp_less"
                  llbuilder
              in
              dbg_llvalue "Build iless instruction" llv_icmp_slt;
              llv_icmp_slt
          | Less, TFloat ->
              let llv_fcmp_olt =
                Llvm.build_fcmp Llvm.Fcmp.Olt llv_e1 llv_e2 "temp_fless"
                  llbuilder
              in
              dbg_llvalue "Build fless instruction" llv_fcmp_olt;
              llv_fcmp_olt
          | Leq, TInt ->
              let llv_icmp_sle =
                Llvm.build_icmp Llvm.Icmp.Sle llv_e1 llv_e2 "temp_ileq"
                  llbuilder
              in
              dbg_llvalue "Build i less or equal instruction" llv_icmp_sle;
              llv_icmp_sle
          | Leq, TFloat ->
              let llv_fcmp_ole =
                Llvm.build_fcmp Llvm.Fcmp.Ole llv_e1 llv_e2 "temp_fleq"
                  llbuilder
              in
              dbg_llvalue "Build f less or equal instruction" llv_fcmp_ole;
              llv_fcmp_ole
          | Greater, TInt ->
              let llv_icmp_sgt =
                Llvm.build_icmp Llvm.Icmp.Sgt llv_e1 llv_e2 "temp_igreater"
                  llbuilder
              in
              dbg_llvalue "Build igreater instruction" llv_icmp_sgt;
              llv_icmp_sgt
          | Greater, TFloat ->
              let llv_fcmp_ogt =
                Llvm.build_fcmp Llvm.Fcmp.Ogt llv_e1 llv_e2 "temp_fgreater"
                  llbuilder
              in
              dbg_llvalue "Build fgreater instruction" llv_fcmp_ogt;
              llv_fcmp_ogt
          | Geq, TInt ->
              let llv_icmp_sge =
                Llvm.build_icmp Llvm.Icmp.Sge llv_e1 llv_e2 "temp_igeq"
                  llbuilder
              in
              dbg_llvalue "Build i greater or equal instruction" llv_icmp_sge;
              llv_icmp_sge
          | Geq, TFloat ->
              let llv_fcmp_oge =
                Llvm.build_fcmp Llvm.Fcmp.Oge llv_e1 llv_e2 "temp_fgeq"
                  llbuilder
              in
              dbg_llvalue "Build f greater or equal instruction" llv_fcmp_oge;
              llv_fcmp_oge
          | _ -> failwith "impossible case"))
  | Call (id1, id2, el) -> (
      let mangled_name =
        if Option.is_some id1 then Option.get id1 ++ id2 else cname ++ id2
      in
      let llv_ftocall =
        Llvm.lookup_function mangled_name ll_module |> Option.get
      in
      let llv_args =
        List.map (fun x -> codegen_expr x cname scope llv_f llbuilder) el
      in
      match expr.annot with
      | TVoid ->
          (* if fun return void we cannot provide to the instruction a name *)
          Llvm.build_call llv_ftocall (Array.of_list llv_args) "" llbuilder
      | _ ->
          Llvm.build_call llv_ftocall (Array.of_list llv_args) ("call_" ^ id2)
            llbuilder)

and codegen_stmt_ordec stmt_ordec cname scope llv_f llbuilder =
  match stmt_ordec.node with
  | Stmt s -> codegen_stmt s cname scope llv_f llbuilder
  | LocalDecl (i, t) -> (
      (* alloc space for local var *)
      match t with
      | TArray (t', s) ->
          let size = Option.get s in
          (* pass t because build_array_alloca wants a type array *)
          let llv_aa =
            Llvm.build_array_alloca (to_llvm_type t)
              (Llvm.const_int ll_i32type size)
              ("alloc_array_" ^ i) llbuilder
          in
          dbg_llvalue
            ("Build array alloca instruction for local array " ^ i)
            llv_aa;

          (* storing default values for each element of the array *)
          for y = 0 to size - 1 do
            let llv_ae =
              Llvm.build_in_bounds_gep llv_aa
                [| Llvm.const_int ll_i32type 0; Llvm.const_int ll_i32type y |]
                (i ^ "[" ^ Int.to_string y ^ "]")
                llbuilder
            in
            dbg_llvalue "Build gep instruction for array element" llv_ae;
            let llv_aes =
              Llvm.build_store (get_default_v t') llv_ae llbuilder
            in
            dbg_llvalue "Build store instruction for array element" llv_aes
          done;

          add_entry i llv_aa scope |> ignore;
          false
      | _ ->
          let llv_a =
            Llvm.build_alloca (to_llvm_type t) ("alloc_var_" ^ i) llbuilder
          in
          dbg_llvalue ("Build alloca instruction for local variable " ^ i) llv_a;
          (* store *)
          let llv_s = Llvm.build_store (get_default_v t) llv_a llbuilder in
          dbg_llvalue ("Build store instruction for local variable " ^ i) llv_s;
          add_entry i llv_a scope |> ignore;
          false)

let codegen_body fd cname =
  let mangled_name =
    if equal_identifier fd.fname "main" then fd.fname else cname ++ fd.fname
  in

  let llv_f = Llvm.lookup_function mangled_name ll_module |> Option.get in
  let llbuilder_f = Llvm.builder_at_end ll_context (Llvm.entry_block llv_f) in

  let scope = empty_table () |> begin_block in

  List.iter2
    (fun (i, t) llv_p ->
      (* alloc parameter and get address *)
      let lli_ba = Llvm.build_alloca (to_llvm_type t) i llbuilder_f in
      dbg_llvalue
        ("Build alloca instruction for function " ^ mangled_name
       ^ ", parameter " ^ i)
        lli_ba;
      (* add address to symbol table *)
      add_entry i lli_ba scope |> ignore;
      (* store parameter *)
      let lli_s = Llvm.build_store llv_p lli_ba llbuilder_f in
      dbg_llvalue
        ("Build store instruction for function " ^ mangled_name ^ ", parameter "
       ^ i)
        lli_s)
    fd.formals
    (Array.to_list (Llvm.params llv_f));

  let has_return =
    codegen_stmt (Option.get fd.body) cname scope llv_f llbuilder_f
  in
  end_block scope |> ignore;
  (if not has_return then
   (* if generating the body we haven't seen any return stmt
      (or if there is a case where return is in then and not else
       or viceversa) then add return instruction to end function
       block *)
   match fd.rtype with
   | TVoid -> Llvm.build_ret_void llbuilder_f |> ignore
   | _ -> Llvm.build_ret (get_default_v fd.rtype) llbuilder_f |> ignore);

  (* check all blocks of the function *)
  Llvm.iter_blocks
    (fun llblock ->
      let nrets = ref 0 in
      let instrs_to_delete =
        Llvm.fold_left_instrs
          (fun instrs ins ->
            (* if we have already reached one return instruction
               then add instruction to the ones to delete*)
            if !nrets > 0 then ins :: instrs
            else
              (* first return instruction found in the block *)
              match (Llvm.is_terminator ins, Llvm.instr_opcode ins) with
              | true, Llvm.Opcode.Ret ->
                  nrets := !nrets + 1;
                  instrs
              | _, _ -> instrs)
          [] llblock
      in
      List.iter Llvm.delete_instruction instrs_to_delete)
    llv_f
  |> ignore;

  let blocks_to_delete =
    Llvm.fold_left_blocks
      (fun acc bb ->
        match Llvm.block_terminator bb with Some _ -> acc | None -> bb :: acc)
      [] llv_f
  in
  List.iter (fun llblock -> Llvm.delete_block llblock) blocks_to_delete

let to_llvm_module (CompilationUnit decls : typ compilation_unit) =
  (* declare prelude functions: print & getint *)
  List.iter
    (fun (name, tfun) ->
      let llt_f = to_llvm_type tfun in
      (* declare function *)
      let llv_f = Llvm.declare_function name llt_f ll_module in

      dbg_llvalue ("Declare function " ^ name) llv_f)
    Mcomp_stdlib.prelude_signature;

  List.iter
    (fun c ->
      match c.node with
      | ComponentDecl cd ->
          List.iter (fun m -> codegen_globals m cd.cname) cd.definitions)
    decls.components;

  List.iter
    (fun c ->
      match c.node with
      | ComponentDecl cd ->
          List.iter
            (fun m ->
              match m.node with
              | FunDecl fd -> codegen_body fd cd.cname
              | _ -> ())
            cd.definitions)
    decls.components;

  ll_module
