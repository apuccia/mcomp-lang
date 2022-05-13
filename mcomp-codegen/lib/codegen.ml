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

let rec codegen_stmt stmt cname scope llv_f llbuilder return =
  match stmt.node with
  | If (e, s1, s2) ->
      let llblock_t = Llvm.append_block ll_context "then" llv_f in
      let llblock_e = Llvm.append_block ll_context "else" llv_f in
      let llblock_c = Llvm.append_block ll_context "cont" llv_f in

      (* get value from evaluating e *)
      let llv_e = codegen_expr e cname scope llbuilder in
      (* build instruction to jump to then or else according to e *)
      let llv_c = Llvm.build_cond_br llv_e llblock_t llblock_e llbuilder in
      dbg_llvalue "Build if condition" llv_c;

      (* position in then block, generate further instructions and jump to cont *)
      Llvm.position_at_end llblock_t llbuilder |> ignore;
      let ret1 = codegen_stmt s1 cname scope llv_f llbuilder return in
      Llvm.build_br llblock_c llbuilder |> ignore;

      (* position in else block *)
      Llvm.position_at_end llblock_e llbuilder |> ignore;
      let ret2 = codegen_stmt s2 cname scope llv_f llbuilder return in
      Llvm.build_br llblock_c llbuilder |> ignore;

      Llvm.position_at_end llblock_c llbuilder |> ignore;
      ret1 || ret2
  | While (e, s) ->
    let llblock_cond = Llvm.append_block ll_context "cond_test" llv_f in
      let llblock_w = Llvm.append_block ll_context "while" llv_f in
      let llblock_cont = Llvm.append_block ll_context "cont" llv_f in

      Llvm.build_br llblock_cond llbuilder |> ignore;
      Llvm.position_at_end llblock_cond llbuilder;
      (* get value from evaluating e *)
      let llv_e = codegen_expr e cname scope llbuilder in

      Llvm.build_cond_br llv_e llblock_w llblock_cont llbuilder |> ignore;

      Llvm.position_at_end llblock_w llbuilder;

      (* build while body instructions *)
      let ret = codegen_stmt s cname scope llv_f llbuilder return in
      if ret then () else Llvm.build_br llblock_cond llbuilder |> ignore;

      Llvm.position_at_end llblock_cont llbuilder;

      (* build instruction to jump to while body or cont according to e *)
      ret
  | Expr e ->
      codegen_expr e cname scope llbuilder |> ignore;
      return
  | Return (Some e) ->
      let llv_e = codegen_expr e cname scope llbuilder in
      let llv_r = Llvm.build_ret llv_e llbuilder in
      dbg_llvalue "Build return (some) instruction" llv_r;
      true
  | Return None ->
      let llv_r = Llvm.build_ret_void llbuilder in
      dbg_llvalue "Build return (void) instruction" llv_r;
      true
  | Block sl -> (
      try
        let block_scope = begin_block scope in
        (* List.iter
           (fun x -> codegen_stmt_ordec x cname block_scope llv_f llbuilder)
           sl; *)
        let _ =
          List.find
            (fun x ->
              codegen_stmt_ordec x cname block_scope llv_f llbuilder return)
            sl
        in
        end_block scope |> ignore;
        true
      with Not_found -> false)
  | Skip ->
      ();
      false

and codegen_lv lv cname scope llbuilder load addr =
  let aux_load lv_llvalue t =
    match t with
    | TRef _ ->
        if addr then lv_llvalue
        else
          let llv_ref = Llvm.build_load lv_llvalue "" llbuilder in
          if load then Llvm.build_load llv_ref "" llbuilder else llv_ref
    | TArray (_, Some _) ->
        Llvm.build_in_bounds_gep lv_llvalue
          [| Llvm.const_int ll_i32type 0; Llvm.const_int ll_i32type 0 |]
          "" llbuilder
    | _ -> if load then Llvm.build_load lv_llvalue "" llbuilder else lv_llvalue
  in

  match (lv.node, lv.annot) with
  | AccVar (None, id), t ->
      let llv_lv = lookup id scope in
      aux_load llv_lv t
  | AccVar (Some cname, id), t ->
      let mangled_name = cname ++ id in
      let llv_gvar = Llvm.lookup_global mangled_name ll_module |> Option.get in
      aux_load llv_gvar t
  | AccIndex (lv, e), _ ->
      let llv_e = codegen_expr e cname scope llbuilder in
      let aux' lv index =
        let llv_lv =
          match lv.node with
          | AccVar (Some cname, vid) ->
              Llvm.lookup_global (cname ++ vid) ll_module |> Option.get
          | AccVar (None, vid) -> lookup vid scope
          | _ -> failwith "impossible case"
        in
        match lv.annot with
        | TArray (TRef _, Some _) ->
            let llv_aea =
              Llvm.build_in_bounds_gep llv_lv
                [| Llvm.const_int ll_i32type 0; index |]
                "" llbuilder
            in
            if load then
              let llv_refv = Llvm.build_load llv_aea "" llbuilder in
              Llvm.build_load llv_refv "" llbuilder
            else llv_aea
        | TArray (_, Some _) ->
            let llv_aea =
              Llvm.build_in_bounds_gep llv_lv
                [| Llvm.const_int ll_i32type 0; index |]
                "" llbuilder
            in
            if load then Llvm.build_load llv_aea "" llbuilder else llv_aea
        | TArray (_, None) | TRef _ ->
            let llv_aa = Llvm.build_load llv_lv "" llbuilder in
            let llv_aea =
              Llvm.build_in_bounds_gep llv_aa [| index |] "" llbuilder
            in
            if load then Llvm.build_load llv_aea "" llbuilder else llv_aea
        | _ -> failwith "impossible case"
      in
      aux' lv llv_e

and codegen_expr expr cname scope llbuilder =
  match expr.node with
  | LV lv -> codegen_lv lv cname scope llbuilder true false
  | ILiteral i -> Llvm.const_int ll_i32type i
  | Assign (lv, e) ->
      let is_addr =
        match (lv.annot, e.node) with TRef _, Address _ -> true | _ -> false
      in
      let llv_e = codegen_expr e cname scope llbuilder in
      let llv_lv = codegen_lv lv cname scope llbuilder false is_addr in

      Llvm.build_store llv_e llv_lv llbuilder |> ignore;
      llv_e
  | CLiteral c -> Llvm.const_int ll_i8type (Char.code c)
  | BLiteral b ->
      if b then Llvm.const_int ll_i1type 1 else Llvm.const_int ll_i1type 0
  | UnaryOp (op, e) -> (
      let llv_e = codegen_expr e cname scope llbuilder in
      match op with
      | Neg ->
          let llv_neg = Llvm.build_neg llv_e "temp_neg" llbuilder in
          dbg_llvalue "Build neg instruction" llv_neg;
          llv_neg
      | Not ->
          let llv_not = Llvm.build_not llv_e "temp_not" llbuilder in
          dbg_llvalue "Build not instruction" llv_not;
          llv_not)
  | Address lv -> codegen_lv lv cname scope llbuilder false true
  | BinaryOp (op, e1, e2) -> (
      let llv_e1 = codegen_expr e1 cname scope llbuilder in
      let llv_e2 = codegen_expr e2 cname scope llbuilder in
      match op with
      | Add ->
          let llv_add = Llvm.build_add llv_e1 llv_e2 "temp_add" llbuilder in
          dbg_llvalue "Build add instruction" llv_add;
          llv_add
      | Sub ->
          let llv_sub = Llvm.build_sub llv_e1 llv_e2 "temp_sub" llbuilder in
          dbg_llvalue "Build sub instruction" llv_sub;
          llv_sub
      | Mult ->
          let llv_mul = Llvm.build_mul llv_e1 llv_e2 "temp_mult" llbuilder in
          dbg_llvalue "Build mult instruction" llv_mul;
          llv_mul
      | Div ->
          let llv_sdiv = Llvm.build_sdiv llv_e1 llv_e2 "temp_div" llbuilder in
          dbg_llvalue "Build div instruction" llv_sdiv;
          llv_sdiv
      | Mod ->
          let llv_srem = Llvm.build_srem llv_e1 llv_e2 "temp_mod" llbuilder in
          dbg_llvalue "Build mod instruction" llv_srem;
          llv_srem
      | Equal ->
          let llv_icmp_eq =
            Llvm.build_icmp Llvm.Icmp.Eq llv_e1 llv_e2 "temp_equal" llbuilder
          in
          dbg_llvalue "Build equal instruction" llv_icmp_eq;
          llv_icmp_eq
      | Neq ->
          let llv_icmp_ne =
            Llvm.build_icmp Llvm.Icmp.Ne llv_e1 llv_e2 "temp_neq" llbuilder
          in
          dbg_llvalue "Build not equal instruction" llv_icmp_ne;
          llv_icmp_ne
      | Less ->
          let llv_icmp_slt =
            Llvm.build_icmp Llvm.Icmp.Slt llv_e1 llv_e2 "temp_less" llbuilder
          in
          dbg_llvalue "Build less instruction" llv_icmp_slt;
          llv_icmp_slt
      | Leq ->
          let llv_icmp_sle =
            Llvm.build_icmp Llvm.Icmp.Sle llv_e1 llv_e2 "temp_leq" llbuilder
          in
          dbg_llvalue "Build less or equal instruction" llv_icmp_sle;
          llv_icmp_sle
      | Greater ->
          let llv_icmp_sgt =
            Llvm.build_icmp Llvm.Icmp.Sgt llv_e1 llv_e2 "temp_greater" llbuilder
          in
          dbg_llvalue "Build greater instruction" llv_icmp_sgt;
          llv_icmp_sgt
      | Geq ->
          let llv_icmp_sge =
            Llvm.build_icmp Llvm.Icmp.Sge llv_e1 llv_e2 "temp_geq" llbuilder
          in
          dbg_llvalue "Build greater or equal instruction" llv_icmp_sge;
          llv_icmp_sge
      | And ->
          let llv_and = Llvm.build_and llv_e1 llv_e2 "temp_and" llbuilder in
          dbg_llvalue "Build and instruction" llv_and;
          llv_and
      | Or ->
          let llv_or = Llvm.build_or llv_e1 llv_e2 "temp_or" llbuilder in
          dbg_llvalue "Build or instruction" llv_or;
          llv_or)
  | Call (id1, id2, el) ->
      let mangled_name =
        if Option.is_some id1 then Option.get id1 ++ id2 else cname ++ id2
      in
      let llv_f = Llvm.lookup_function mangled_name ll_module |> Option.get in
      let llv_args =
        List.map (fun x -> codegen_expr x cname scope llbuilder) el
      in
      Llvm.build_call llv_f (Array.of_list llv_args) "" llbuilder

and codegen_stmt_ordec stmt_ordec cname scope llv_f llbuilder return =
  match stmt_ordec.node with
  | Stmt s -> codegen_stmt s cname scope llv_f llbuilder return
  | LocalDecl (i, t) ->
      (* alloc space for local var *)
      (match t with
      | TArray (t', s) ->
          let size = Option.get s in
          (* pass t because build_array_alloca wants a type array *)
          let llv_aa =
            Llvm.build_array_alloca (to_llvm_type t)
              (Llvm.const_int ll_i32type size)
              "" llbuilder
          in
          dbg_llvalue
            ("Build array alloca instruction for local array " ^ i)
            llv_aa;

          for i = 0 to size - 1 do
            let llv_ae =
              Llvm.build_in_bounds_gep llv_aa
                [| Llvm.const_int ll_i32type 0; Llvm.const_int ll_i32type i |]
                "" llbuilder
            in
            dbg_llvalue "Build gep instruction for array element" llv_ae;
            let llv_aes =
              Llvm.build_store (get_default_v t') llv_ae llbuilder
            in
            dbg_llvalue "Build store instruction for array element" llv_aes
          done;

          add_entry i llv_aa scope |> ignore
      | _ ->
          let llv_a = Llvm.build_alloca (to_llvm_type t) "" llbuilder in
          dbg_llvalue ("Build alloca instruction for local variable " ^ i) llv_a;
          (* store *)
          let llv_s = Llvm.build_store (get_default_v t) llv_a llbuilder in
          dbg_llvalue ("Build store instruction for local variable " ^ i) llv_s;
          add_entry i llv_a scope |> ignore);
      false

let codegen_body fd cname =
  let mangled_name =
    if equal_identifier fd.fname "main" then (
      Printf.printf "%s" fd.fname;
      fd.fname)
    else cname ++ fd.fname
  in

  (* Printf.printf "***%s\n\n" fd.fname; *)
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
    codegen_stmt (Option.get fd.body) cname scope llv_f llbuilder_f false
  in
  if not has_return then
    match fd.rtype with
    | TVoid -> Llvm.build_ret_void llbuilder_f |> ignore
    | _ ->
        Llvm.build_ret (get_default_v fd.rtype) llbuilder_f |> ignore;

        end_block scope |> ignore

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

  logger#debug "%s" (Llvm.string_of_llmodule ll_module);

  ll_module