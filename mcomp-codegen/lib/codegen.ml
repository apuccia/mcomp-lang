open Ast
open Symbol_table

let llcontext = Llvm.global_context ()

let rec to_llvm_type t =
  match t with
  | TInt -> Llvm.i32_type llcontext
  | TBool -> Llvm.i1_type llcontext
  | TChar -> Llvm.i8_type llcontext
  | TArray (t', None) -> Llvm.pointer_type (to_llvm_type t')
  | TArray (t', Some s) -> Llvm.array_type (to_llvm_type t') s
  | TRef t' -> Llvm.pointer_type (to_llvm_type t')
  | TVoid -> Llvm.void_type llcontext
  | _ -> failwith ""

let component_scopes = Hashtbl.create 0

let codegen_fundecl fd cscope llmodule =
  let scope = empty_table () in
  ()

let to_llvm_module (CompilationUnit decls : typ compilation_unit) =
  let llmodule = Llvm.create_module llcontext "mcomp" in
  let scope = empty_table () in
  Hashtbl.add component_scopes "Prelude" scope;
  List.map
    (fun (i, t) ->
      let lt = to_llvm_type t in
      (i, lt))
    Mcomp_stdlib.prelude_signature
  |> List.iter (fun (i, t) ->
         let f = Llvm.declare_function i t llmodule in
         add_entry i f scope |> ignore)
  |> ignore;

  List.iter
    (fun x ->
      match x.node with
      | ComponentDecl cd ->
          let cscope = empty_table () in
          Hashtbl.add component_scopes cd.cname cscope;
          List.iter
            (fun x ->
              match x.node with
              | FunDecl fd ->
                  let args =
                    List.map
                      (fun (_, t) ->
                        match t with
                        | TArray (t', _) -> to_llvm_type t' |> Llvm.pointer_type
                        | _ -> to_llvm_type t)
                      fd.formals
                  in
                  let rtype = to_llvm_type fd.rtype in
                  let f_type = Llvm.function_type rtype (Array.of_list args) in
                  let f = Llvm.define_function fd.fname f_type llmodule in
                  add_entry fd.fname f cscope |> ignore;
                  codegen_fundecl fd llmodule cscope
              | VarDecl (i, t) ->
                  let v =
                    Llvm.define_global i (Llvm.undef (to_llvm_type t)) llmodule
                  in
                  add_entry i v cscope |> ignore)
            cd.definitions)
    decls.components;

  llmodule