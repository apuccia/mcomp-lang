exception Semantic_error of Location.code_pos * string
exception NotFoundEntry of Ast.identifier

open Ast
open Symbol_table
open Mcomp_stdlib
open Location

let ( <@> ) n f = { node = n; annot = f }
let ints_scopes = Hashtbl.create 0
let used_interfaces = Hashtbl.create 0

let get_q cname ide =
  let rec g l =
    match l with
    | [] -> failwith "not found"
    | x :: xs -> (
        let scope = Hashtbl.find ints_scopes x in
        try
          let t = lookup ide scope in
          (x, t)
        with NotFoundEntry _ -> g xs)
  in
  g (Hashtbl.find used_interfaces cname)

let check_vardecl v =
  match v with
  | i, TInt -> VarDecl (i, TInt) <@> TInt
  | i, TBool -> VarDecl (i, TBool) <@> TBool
  | i, TChar -> VarDecl (i, TChar) <@> TChar
  | i, TArray (t, s) -> VarDecl (i, TArray (t, s)) <@> TArray (t, s)
  | i, TRef t -> VarDecl (i, TRef t) <@> TRef t
  | _, _ -> failwith "Not allowed type"

let check_member_decl m scope =
  match m.node with
  | FunDecl f ->
      add_entry f.fname f.rtype scope |> ignore;
      (* f.body will be None because it is a prototype *)
      if Option.is_some f.body then failwith "Not a prototype"
      else
        FunDecl
          { rtype = f.rtype; fname = f.fname; formals = f.formals; body = None }
        <@> TFun
              (List.map (fun m -> match m with _, t -> t) f.formals, f.rtype)
  | VarDecl v -> check_vardecl v

let check_interface_decl i scope =
  match i.node with
  | InterfaceDecl { iname; declarations } ->
      (* add declarations to scope of interface *)
      let iscope = begin_block scope in
      let ideclarations =
        List.map (fun m -> check_member_decl m iscope) declarations
      in
      end_block iscope |> ignore;
      Hashtbl.add ints_scopes iname iscope;
      (* add interface definition to scope *)
      add_entry iname (TInterface iname) scope |> ignore;
      (* return typed InterfaceDecl *)
      InterfaceDecl { iname; declarations = ideclarations } <@> TInterface iname

let rec check_exp e cname scope =
  match e.node with
  | LV lv ->
      let t_lv = check_lvalue lv cname scope in
      LV t_lv <@> t_lv.annot
  | Assign (lv, e) ->
      let t_e = check_exp e cname scope in
      let t_lv = check_lvalue lv cname scope in
      if t_lv.annot != t_e.annot then failwith "not same type"
      else Assign (t_lv, t_e) <@> t_lv.annot
  | ILiteral i -> ILiteral i <@> TInt
  | CLiteral c -> CLiteral c <@> TChar
  | BLiteral b -> BLiteral b <@> TBool
  | UnaryOp (op, e) -> (
      let t_e = check_exp e cname scope in
      match (op, t_e.annot) with
      | Not, TBool -> UnaryOp (op, t_e.node <@> TBool) <@> TBool
      | Not, _ -> failwith "not a valid expression for not operation"
      | Neg, TInt -> UnaryOp (op, t_e.node <@> TInt) <@> TInt
      | Neg, _ -> failwith "not a valid expression for negative operation")
  | Address lv ->
      let t_lv = check_lvalue lv cname scope in
      Address t_lv <@> t_lv.annot
  | BinaryOp (op, e1, e2) ->
      check_binary_op op e1 e2 cname scope
  | Call (_, ide_f, args) -> 
      let args_list = List.map (fun x -> check_exp x cname scope) args in
      try
        let tfun = lookup ide_f scope in
        match tfun with
        | TFun(typ_args_list, rt) -> (
            try
              List.iter2
                (fun x y -> if x.annot != y then failwith "arguments with different types wrt declaration of function")
                args_list typ_args_list;
              Call (None, ide_f, args_list) <@> rt
            with Invalid_argument _ -> failwith "missing arguments for the function")
        | _ -> failwith "not a function"
      with NotFoundEntry _ -> (
        let q = get_q cname ide_f in
        match q with
        | iname, t -> (
            match t with
            | TFun(typ_args_list, rt) -> (
                try
                  List.iter2
                    (fun x y -> if x.annot != y then failwith "arguments with different types wrt declaration of function")
                    args_list typ_args_list;
                  Call (Some iname, ide_f, args_list) <@> rt
                with Invalid_argument _ -> failwith "missing argument for function")
            | _ -> failwith "not a function"))

and check_lvalue lv cname scope =
  match lv.node with
  | AccVar (_, id2) -> (
      try
        let x = lookup id2 scope in
        AccVar (None, id2) <@> x
      with NotFoundEntry _ -> (
        let q = get_q cname id2 in
        match q with iname, t -> AccVar (Some iname, id2) <@> t))
  | AccIndex (lv', e) -> (
      let t_e = check_exp e cname scope in
      let t_lv = check_lvalue lv' cname scope in
      match t_lv.node with
      | AccVar (_, _) -> AccIndex (t_lv, t_e) <@> t_lv.annot
      | _ -> failwith "cannot define multidimensional arrays")

and check_binary_op op e1 e2 cname scope =
  let t_e1 = check_exp e1 cname scope in 
  let t_e2 = check_exp e2 cname scope in
  match (op, t_e1.annot, t_e2.annot) with
  (* Add *)
  | Add, TInt, TInt -> BinaryOp (Add, t_e1, t_e2) <@> TInt
  | Add, _, _ -> failwith "Invalid operand types for add"
  (* Sub *)
  | Sub, TInt, TInt -> BinaryOp (Sub, t_e1, t_e2) <@> TInt
  | Sub, _, _ -> failwith "Invalid operand types for sub"
  (* Mult *)
  | Mult, TInt, TInt -> BinaryOp (Mult, t_e1, t_e2) <@> TInt
  | Mult, _, _ -> failwith "Invalid operand types for mult"
  (* Div *)
  | Div, TInt, TInt -> BinaryOp (Div, t_e1, t_e2) <@> TInt
  | Div, _, _ -> failwith "Invalid operand types for div"
  (* Mod *)
  | Mod, TInt, TInt -> BinaryOp (Mod, t_e1, t_e2) <@> TInt
  | Mod, _, _ -> failwith "Invalid operand types for mod"
  (* Equal *)
  | Equal, TInt, TInt -> BinaryOp (Equal, t_e1, t_e2) <@> TInt
  | Equal, TBool, TBool -> BinaryOp (Equal, t_e1, t_e2) <@> TBool
  | Equal, _, _ -> failwith "Invalid operand types for equal"
  (* Not Equal *)
  | Neq, TInt, TInt -> BinaryOp (Equal, t_e1, t_e2) <@> TInt
  | Neq, TBool, TBool -> BinaryOp (Equal, t_e1, t_e2) <@> TBool
  | Neq, _, _ -> failwith "Invalid operand types for not equal"
  (* Less *)
  | Less, TInt, TInt -> BinaryOp (Equal, t_e1, t_e2) <@> TInt
  | Less, TBool, TBool -> BinaryOp (Equal, t_e1, t_e2) <@> TBool
  | Less, _, _ -> failwith "Invalid operand types for less"
  (* Less And Equal *)
  | Leq, TInt, TInt -> BinaryOp (Equal, t_e1, t_e2) <@> TInt
  | Leq, TBool, TBool -> BinaryOp (Equal, t_e1, t_e2) <@> TBool
  | Leq, _, _ -> failwith "Invalid operand types for less and equal"
  (* Greater *)
  | Greater, TInt, TInt -> BinaryOp (Equal, t_e1, t_e2) <@> TInt
  | Greater, TBool, TBool -> BinaryOp (Equal, t_e1, t_e2) <@> TBool
  | Greater, _, _ -> failwith "Invalid operand types for greater"
  (* Greater And Equal *)
  | Geq, TInt, TInt -> BinaryOp (Equal, t_e1, t_e2) <@> TInt
  | Geq, TBool, TBool -> BinaryOp (Equal, t_e1, t_e2) <@> TBool
  | Geq, _, _ -> failwith "Invalid operand types for greater and equal"
  (* And  *)
  | And, TBool, TBool -> BinaryOp (Equal, t_e1, t_e2) <@> TBool
  | And, _, _ -> failwith "Invalid operand types for and"
  (* Or *)
  | Or, TBool, TBool -> BinaryOp (Equal, t_e1, t_e2) <@> TBool
  | Or, _, _ -> failwith "Invalid operand types for or"

let rec check_stmt body cname fscope rtype =
  match body.node with
  | If (e, s1, s2) -> (
      let t_e = check_exp e cname fscope in
      let t_s1 = check_stmt s1 cname fscope rtype in
      let t_s2 = check_stmt s2 cname fscope rtype in
      match t_e.annot with
      | TBool ->
          if t_s1.annot == t_s2.annot then If (t_e, t_s1, t_s2) <@> t_s1.annot
          else failwith "Then and else statement have different types"
      | _ -> failwith "Not a boolean type for if condition")
  | While (e, s) -> (
      let t_e = check_exp e cname fscope in
      let t_s = check_stmt s cname fscope rtype in
      match t_e.annot with
      | TBool -> While (t_e, t_s) <@> t_s.annot
      | _ -> failwith "Not a boolean type for if condition")
  | Expr e ->
      let t_e = check_exp e cname fscope in
      Expr t_e <@> t_e.annot
  | Return e -> (
      match e with
      | None ->
          if Option.get rtype == TVoid then Return None <@> TVoid
          else failwith "Returned type not matching function return type"
      | Some v ->
          let t_e = check_exp v cname fscope in
          if t_e.annot == Option.get rtype then Return (Some t_e) <@> t_e.annot
          else failwith "Returned type not matching function return type")
  | Block sordec -> check_ordec_list sordec cname fscope
  | Skip -> Skip <@> TVoid

and check_ordec_list stmt_list cname scope =
  let bscope = begin_block scope in
  let t_stmts =
    List.map
      (fun s ->
        match s.node with
        | LocalDecl vdecl -> (
            match vdecl with
            | i, t ->
                add_entry i t bscope |> ignore;
                LocalDecl vdecl <@> t)
        | Stmt st ->
            let t_stmt = check_stmt st cname bscope None in
            Stmt t_stmt <@> t_stmt.annot)
      stmt_list
  in
  end_block bscope |> ignore;
  Block t_stmts <@> TVoid

let check_member_def m cname scope =
  match m.node with
  | FunDecl f ->
      add_entry f.fname f.rtype scope |> ignore;
      let fscope = begin_block scope |> of_alist f.formals in
      (* f.body will be Some because we are considering the implementation *)
      if Option.is_none f.body then failwith "Empty body"
      else
        let fbody =
          check_stmt (Option.get f.body) cname fscope (Some f.rtype)
        in
        FunDecl
          {
            rtype = f.rtype;
            fname = f.fname;
            formals = f.formals;
            body = Some fbody;
          }
        <@> TFun
              (List.map (fun m -> match m with _, t -> t) f.formals, f.rtype)
  | VarDecl v -> check_vardecl v

let rec check_component_def c interfaces scope =
  match c.node with
  | ComponentDecl { cname; uses; provides; definitions } ->
      (* get provided interfaces declarations *)
      let provints_declarations =
        List.filter
          (fun x ->
            match x.node with
            | InterfaceDecl { iname; _ } -> List.mem iname provides)
          interfaces
        |> List.map (fun x ->
               match x.node with
               | InterfaceDecl { iname = _; declarations } -> declarations)
        |> List.flatten
      in
      (* check that all provided definitions are implemented *)
      List.iter
        (fun x ->
          if List.mem x.node (List.map (fun y -> y.node) definitions) then ()
          else failwith "not implemented")
        provints_declarations;
      (* check to see if there are declarations with same name but different types *)
      if Bool.not (check_same_types provints_declarations) then
        failwith "conflicting names in definitions of provided interfaces";
      (* add definitions to component scope *)
      let cscope = begin_block scope in
      add_entry cname (TComponent cname) scope |> ignore;
      let cdefinitions =
        List.map (fun m -> check_member_def m cname cscope) definitions
      in
      end_block cscope |> ignore;
      (* add component definition to scope *)
      Hashtbl.add used_interfaces cname uses;
      (* return typed ComponentDecl *)
      ComponentDecl { cname; uses; provides; definitions = cdefinitions }
      <@> TComponent cname

and check_same_types decs =
  match decs with
  | [] -> true
  | x :: xs -> (
      match x.node with
      | FunDecl f ->
          List.for_all
            (fun y ->
              match y.node with
              | FunDecl f' ->
                  f.fname != f'.fname
                  || (f.rtype == f'.rtype && f.formals == f'.formals)
              | VarDecl _ -> true)
            xs
      | VarDecl (i, t) ->
          List.for_all
            (fun y ->
              match y.node with
              | VarDecl (i', t') -> i != i' || t == t'
              | FunDecl _ -> true)
            xs)

let rec check_connection_decl c cmps scope =
  match c with
  | Link (c1, used_int, c2, provided_int) ->
      (try lookup c1 scope |> ignore
       with NotFoundEntry _ -> failwith "component not found");
      (try lookup c2 scope |> ignore
       with NotFoundEntry _ -> failwith "component not found");
      (try
         lookup used_int scope |> ignore;
         if check_notusedprovided_int c1 used_int cmps then
           failwith "the interface is not used"
       with NotFoundEntry _ -> failwith "interface not found");
      (try
         lookup provided_int scope |> ignore;
         if check_notusedprovided_int c2 provided_int cmps then
           failwith "the interface is not used"
       with NotFoundEntry _ -> failwith "interface not found");

      Link (c1, used_int, c2, provided_int)

and check_notusedprovided_int component interface l =
  match l with
  | [] -> true
  | x :: xs -> (
      match x.node with
      | ComponentDecl { cname; uses; provides; definitions = _ } ->
          if component == cname then
            Bool.not (List.mem interface uses || List.mem interface provides)
          else check_notusedprovided_int component interface xs)

let check_top_decls ints comps conns scope =
  let interfaces = List.map (fun i -> check_interface_decl i scope) ints in
  let components =
    List.map (fun cmp -> check_component_def cmp ints scope) comps
  in
  let connections =
    List.map (fun con -> check_connection_decl con components scope) conns
  in
  CompilationUnit { interfaces; components; connections }

let type_check (CompilationUnit decls : code_pos compilation_unit) =
  let global_scope =
    empty_table ()
    |> add_entry "Prelude" (TInterface "Prelude")
    |> add_entry "App" (TInterface "App")
  in

  begin_block global_scope |> of_alist prelude_signature |> end_block |> ignore;

  begin_block global_scope |> of_alist app_signature |> end_block |> ignore;

  check_top_decls decls.interfaces decls.components decls.connections
    global_scope
