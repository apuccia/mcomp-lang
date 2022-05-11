open Ast
open Symbol_table
open Easy_logging

let logger =
  let file_h = Handlers.File ("Code generation", Logging.Debug) in
  let cli_h = Handlers.Cli Logging.Debug in
  Logging.make_logger "Code generation" Logging.Debug [ cli_h; file_h ]

let dbg_llvalue llv = logger#debug "\n%s" (Llvm.string_of_llvalue llv)
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
  | TRef t' -> Llvm.const_pointer_null (to_llvm_type t')
  | _ -> failwith "impossible case"

let codegen_globals m cname =
  match m.node with
  | FunDecl fd ->
      let mangled_name = cname ++ fd.fname in
      (* get function type *)
      let llt_f = to_llvm_type m.annot in
      (* define function *)
      let llv_f = Llvm.define_function mangled_name llt_f ll_module in

      dbg_llvalue llv_f
  | VarDecl (i, t) ->
      let mangled_name = cname ++ i in
      (* get initial value *)
      let def_value = get_default_v t in
      (* add to global *)
      let llv_v = Llvm.define_global mangled_name def_value ll_module in

      dbg_llvalue llv_v

let rec codegen_stmt stmt cname scope llv_f llbuilder =
  match stmt.node with 
  | If (e, s1, s2) -> 
    let llblock_t = Llvm.append_block ll_context "then" llv_f in
    let llblock_e = Llvm.append_block ll_context "else" llv_f in
    let llblock_c = Llvm.append_block ll_context "cont" llv_f in 

    (* get instruction from evaluating e TODO *)
    (*
      jump to then or else accordingly
      Llvm.build_cond_br icmp llblock_t llblock_e llbuilder

      position at end of then 
      Llvm.position_at_end llblock_t llbuilder
      add instructions to then block
      add final instruction that jump to cont
      Llvm.build_br llblock_c llbuilder

      position at end of else 
      Llvm.position_at_end llblock_e llbuilder
      add instructions to else block
      add final instruction that jump to cont
      Llvm.build_br llblock_c llbuilder
    *)
    ()
  | _ -> cname |> ignore; scope |> ignore; llbuilder |> ignore; ()

let codegen_body fd cname =
  let mangled_name = cname ++ fd.fname in

  let llv_f = Llvm.lookup_function mangled_name ll_module |> Option.get in
  let llbuilder_f = Llvm.builder_at_end ll_context (Llvm.entry_block llv_f) in

  let scope = empty_table () |> begin_block in

  List.iter2
    (fun (i, _) llv_p ->
      (* alloc parameter and get address *)
      let lli_ba = Llvm.build_alloca (Llvm.type_of llv_p) i llbuilder_f in
      dbg_llvalue lli_ba;
      (* add address to symbol table *)
      add_entry i scope |> ignore;
      (* store parameter *)
      let lli_s = Llvm.build_store llv_p lli_ba llbuilder_f in
      dbg_llvalue lli_s)
    fd.formals
    (Array.to_list (Llvm.params llv_f));

  codegen_stmt (Option.get fd.body) cname scope llv_f llbuilder_f |> ignore;

  (match fd.rtype with
  | TInt | TChar | TBool ->
      let llv_vr = Llvm.build_ret (get_default_v fd.rtype) llbuilder_f in
      dbg_llvalue llv_vr
  | TVoid ->
      let llv_vr = Llvm.build_ret_void llbuilder_f in
      dbg_llvalue llv_vr
  | _ -> failwith "impossible case");

  llbuilder_f |> ignore;
  cname |> ignore;
  ()

let to_llvm_module (CompilationUnit decls : typ compilation_unit) =
  (* declare prelude functions: print & getint *)
  List.iter
    (fun (name, tfun) ->
      let mangled_name = "Prelude" ++ name in
      let llt_f = to_llvm_type tfun in
      (* declare function *)
      let llv_f = Llvm.declare_function mangled_name llt_f ll_module in

      dbg_llvalue llv_f)
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