open Ast
open Symbol_table

let llcontext = Llvm.global_context ()
let llmodule = Llvm.create_module llcontext "mcomp"

(* name mangling *)
let ( ++ ) cname id = cname ^ "_" ^ id

let rec to_llvm_type t =
  match t with
  | TInt -> Llvm.i32_type llcontext
  | TBool -> Llvm.i1_type llcontext
  | TChar -> Llvm.i8_type llcontext
  | TArray (t', None) -> Llvm.pointer_type (to_llvm_type t')
  | TArray (t', Some s) -> Llvm.array_type (to_llvm_type t') s
  | TRef t' -> Llvm.pointer_type (to_llvm_type t')
  | TVoid -> Llvm.void_type llcontext
  | TFun (l, r) ->
      Llvm.function_type (to_llvm_type r)
        (Array.of_list (List.map (fun t -> to_llvm_type t) l))
  | _ -> failwith (show_typ t)

let add_terminator builder after =
  let terminator = Llvm.block_terminator (Llvm.insertion_block builder) in
  if Option.is_none terminator then after builder |> ignore else ()

let generate_par_types t =
  match t with
  | TArray (t1, _) -> to_llvm_type t1 |> Llvm.pointer_type
  | _ -> to_llvm_type t

let component_scopes = Hashtbl.create 0

let rec codegen_expr cname scope builder e =
  match e.node with
  | LV lv ->
      let llv_v = codegen_lv cname scope builder lv in
      Llvm.build_load llv_v "lv" builder
  | Assign (lv, e) ->
      let llv_lv = codegen_lv cname scope builder lv in
      let llv_e = codegen_expr cname scope builder e in
      Llvm.build_store llv_e llv_lv builder |> ignore;
      llv_e
  | ILiteral i -> Llvm.const_int (Llvm.i32_type llcontext) i
  | CLiteral c -> Llvm.const_int (Llvm.i8_type llcontext) (Char.code c)
  | BLiteral b ->
      if b then Llvm.const_int (Llvm.i1_type llcontext) 1
      else Llvm.const_int (Llvm.i1_type llcontext) 0
  | UnaryOp (op, e) -> (
      let llv_e = codegen_expr cname scope builder e in
      match op with
      | Neg -> Llvm.build_neg llv_e "neg" builder
      | Not -> Llvm.build_not llv_e "not" builder)
  | Address a -> codegen_lv cname scope builder a
  | BinaryOp (op, e1, e2) -> (
      let llv_e1 = codegen_expr cname scope builder e1 in
      let llv_e2 = codegen_expr cname scope builder e2 in
      match op with
      | Add -> Llvm.build_add llv_e1 llv_e2 "add" builder
      | Sub -> Llvm.build_sub llv_e1 llv_e2 "sub" builder
      | Mult -> Llvm.build_mul llv_e1 llv_e2 "mult" builder
      | Div -> Llvm.build_sdiv llv_e1 llv_e2 "div" builder
      | Mod -> Llvm.build_srem llv_e1 llv_e2 "mod" builder
      | Equal -> Llvm.build_icmp Llvm.Icmp.Eq llv_e1 llv_e2 "equal" builder
      | Neq -> Llvm.build_icmp Llvm.Icmp.Ne llv_e1 llv_e2 "neq" builder
      | Less -> Llvm.build_icmp Llvm.Icmp.Slt llv_e1 llv_e2 "less" builder
      | Leq -> Llvm.build_icmp Llvm.Icmp.Sle llv_e1 llv_e2 "leq" builder
      | Greater -> Llvm.build_icmp Llvm.Icmp.Sgt llv_e1 llv_e2 "greater" builder
      | Geq -> Llvm.build_icmp Llvm.Icmp.Sge llv_e1 llv_e2 "geq" builder
      | And -> Llvm.build_and llv_e1 llv_e2 "and" builder
      | Or -> Llvm.build_or llv_e1 llv_e2 "or" builder)
  | Call (None, id2, el) ->
      let llv_f = lookup (cname ++ id2) scope in
      let el = List.map (fun x -> codegen_expr cname scope builder x) el in
      let el =
        List.map
          (fun llv_e ->
            let llt_e = llv_e |> Llvm.type_of |> Llvm.classify_type in
            match llt_e with
            | Llvm.TypeKind.Array ->
                Llvm.build_gep llv_e
                  [|
                    Llvm.const_int (Llvm.i32_type llcontext) 0;
                    Llvm.const_int (Llvm.i32_type llcontext) 0;
                  |]
                  "" builder
            | _ -> llv_e)
          el
      in
      Llvm.build_call llv_f (Array.of_list el) "" builder
  | Call (Some id1, id2, el) ->
      let llv_f = Hashtbl.find component_scopes id1 |> lookup (id1 ++ id2) in
      let el = List.map (fun x -> codegen_expr cname scope builder x) el in
      Llvm.build_call llv_f (Array.of_list el) "" builder

and codegen_lv cname scope builder lv =
  match lv.node with
  | AccVar (None, id2) -> lookup (cname ++ id2) scope
  | AccVar (Some id1, id2) ->
      Hashtbl.find component_scopes id1 |> lookup (id1 ++ id2)
  | AccIndex (lv, e) -> (
      let llv_e = codegen_expr cname scope builder e in
      let llv_lv = codegen_lv cname scope builder lv in
      let llt_lv = llv_lv |> Llvm.type_of in
      match llt_lv |> Llvm.classify_type with
      | Llvm.TypeKind.Pointer -> (
          match llt_lv |> Llvm.element_type |> Llvm.classify_type with
          | Llvm.TypeKind.Array ->
              Llvm.build_in_bounds_gep llv_lv
                [| Llvm.const_int (Llvm.i32_type llcontext) 0; llv_e |]
                "" builder
          | _ ->
              let llv_loaded = Llvm.build_load llv_lv "" builder in
              Llvm.build_in_bounds_gep llv_loaded [| llv_e |] "" builder)
      | _ ->
          Llvm.build_in_bounds_gep llv_lv
            [| Llvm.const_int (Llvm.i32_type llcontext) 0; llv_e |]
            "" builder)

let rec codegen_stmt cname llv_f scope builder body =
  match body.node with
  | If (e, s1, s2) ->
      let then_block = Llvm.append_block llcontext "then" llv_f in
      let llb_then = Llvm.builder_at_end llcontext then_block in

      let else_block = Llvm.append_block llcontext "else" llv_f in
      let llb_else = Llvm.builder_at_end llcontext else_block in

      let next_block = Llvm.append_block llcontext "next" llv_f in

      let e = codegen_expr cname scope builder e in
      Llvm.build_cond_br e then_block else_block builder |> ignore;

      codegen_stmt cname llv_f scope llb_then s1 |> ignore;
      add_terminator llb_then (Llvm.build_br next_block);

      codegen_stmt cname llv_f scope llb_else s2 |> ignore;
      add_terminator llb_else (Llvm.build_br next_block);
      Llvm.position_at_end next_block builder
  | While (e, s) ->
      let cond_block = Llvm.append_block llcontext "condition" llv_f in
      let llb_cond = Llvm.builder_at_end llcontext cond_block in

      let body_block = Llvm.append_block llcontext "body" llv_f in
      let llb_body = Llvm.builder_at_end llcontext body_block in

      let cont_block = Llvm.append_block llcontext "cont" llv_f in
      cond_block |> Llvm.build_br |> add_terminator builder |> ignore;
      let llv_e = codegen_expr cname scope llb_cond e in
      Llvm.build_cond_br llv_e body_block cont_block llb_cond |> ignore;
      codegen_stmt cname llv_f scope llb_body s |> ignore;
      Llvm.build_br cond_block |> add_terminator llb_body;
      Llvm.position_at_end cont_block builder
  | Expr e -> codegen_expr cname scope builder e |> ignore
  | Return e ->
      if Option.is_none e then Llvm.build_ret_void |> add_terminator builder
      else
        let e_val = Option.get e |> codegen_expr cname scope builder in
        e_val |> Llvm.build_ret |> add_terminator builder
  | Block sl ->
      let bscope = begin_block scope in
      List.iter (fun s -> codegen_stmtordec cname llv_f bscope builder s) sl;
      end_block bscope |> ignore
  | Skip -> ()

and codegen_stmtordec cname llv_f scope builder stmt =
  match stmt.node with
  | LocalDecl (i, t) ->
      let llv_var = Llvm.build_alloca (to_llvm_type t) (cname ++ i) builder in
      Printf.printf "%s*****\n" (cname ++ i);
      add_entry (cname ++ i) llv_var scope |> ignore;
      Llvm.build_store (Llvm.undef (to_llvm_type t)) llv_var builder |> ignore
  | Stmt s -> codegen_stmt cname llv_f scope builder s

let codegen_fundecl cname fd cscope =
  let llv_f = lookup (cname ++ fd.fname) cscope in
  let llb_f = Llvm.entry_block llv_f |> Llvm.builder_at_end llcontext in
  let fscope = begin_block cscope in

  List.iter2
    (fun llvm_v (i, t) ->
      let llvm_t = generate_par_types t in

      (* store function parameters *)
      let par_addr = Llvm.build_alloca llvm_t (cname ++ i) llb_f in
      Llvm.build_store llvm_v par_addr llb_f |> ignore;
      add_entry (cname ++ i) par_addr fscope |> ignore)
    (Llvm.params llv_f |> Array.to_list)
    fd.formals;

  codegen_stmt cname llv_f fscope llb_f (Option.get fd.body) |> ignore;
  end_block fscope |> ignore;

  let ret_type = to_llvm_type fd.rtype in
  match fd.rtype with
  | TVoid -> add_terminator llb_f Llvm.build_ret_void
  | _ -> add_terminator llb_f (ret_type |> Llvm.undef |> Llvm.build_ret)

let to_llvm_module (CompilationUnit decls : typ compilation_unit) =
  let scope = empty_table () in
  let pscope = begin_block scope in

  Hashtbl.add component_scopes "Prelude" pscope;
  List.map
    (fun (i, t) ->
      let lt = to_llvm_type t in
      (i, lt))
    Mcomp_stdlib.prelude_signature
  |> List.iter (fun (i, t) ->
         let f = Llvm.declare_function i t llmodule in
         add_entry ("Prelude" ++ i) f pscope |> ignore)
  |> ignore;
  end_block |> ignore;

  List.iter
    (fun x ->
      match x.node with
      | ComponentDecl cd ->
          let cscope = begin_block scope in

          Hashtbl.add component_scopes cd.cname cscope;
          List.iter
            (fun x ->
              (match x.node with
              | FunDecl fd ->
                  let llt_args =
                    List.map (fun (_, t) -> generate_par_types t) fd.formals
                  in
                  let llt_rtype = to_llvm_type fd.rtype in
                  let llt_f =
                    Llvm.function_type llt_rtype (Array.of_list llt_args)
                  in
                  let llv_f =
                    Llvm.define_function (cd.cname ++ fd.fname) llt_f llmodule
                  in
                  add_entry (cd.cname ++ fd.fname) llv_f cscope |> ignore
              | VarDecl (i, t) ->
                  let llv_v =
                    Llvm.define_global (cd.cname ++ i)
                      (Llvm.undef (to_llvm_type t))
                      llmodule
                  in
                  add_entry (cd.cname ++ i) llv_v cscope |> ignore);
              end_block cscope |> ignore)
            cd.definitions)
    decls.components;

  List.iter
    (fun x ->
      match x.node with
      | ComponentDecl cd ->
          let cscope = Hashtbl.find component_scopes cd.cname in
          List.iter
            (fun x ->
              match x.node with
              | FunDecl fd -> codegen_fundecl cd.cname fd cscope
              | _ -> ())
            cd.definitions)
    decls.components;

  llmodule