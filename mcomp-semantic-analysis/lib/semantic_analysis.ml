open Ast
open Symbol_table
open Mcomp_stdlib
open Location
open Easy_logging

exception Semantic_error of Location.code_pos * string

let logger =
  let file_h = Handlers.File ("Semantic analysis", Logging.Debug) in
  let cli_h = Handlers.Cli Logging.Debug in
  Logging.make_logger "Semantic analysis" Logging.Debug [ cli_h; file_h ]

let raise_semantic_error pos msg =
  logger#error "Error at lines %d:%d, columns %d:%d: %s" pos.start_line
    pos.end_line pos.start_column pos.end_column msg;
  raise (Semantic_error (pos, msg))

let dbg_typ msg pos =
  logger#debug "%s at lines %d:%d, columns %d:%d" msg pos.start_line
    pos.end_line pos.start_column pos.end_column

let ( <@> ) n f = { node = n; annot = f }
let ints_scopes = Hashtbl.create 0
let used_interfaces = Hashtbl.create 0

let get_interface_qualifier cname ide pos =
  let rec g l =
    match l with
    | [] -> raise_semantic_error pos "Qualifier not found"
    | x :: xs -> (
        let scope = Hashtbl.find ints_scopes x in
        try
          let t = lookup ide scope in
          (x, t)
        with NotFoundEntry -> g xs)
  in
  g (Hashtbl.find used_interfaces cname)

let check_vardecl v pos =
  match v with
  | i, TInt -> VarDecl (i, TInt) <@> TInt
  | i, TBool -> VarDecl (i, TBool) <@> TBool
  | i, TChar -> VarDecl (i, TChar) <@> TChar
  | i, TArray (t, s) -> VarDecl (i, TArray (t, s)) <@> TArray (t, s)
  | i, TRef t -> VarDecl (i, TRef t) <@> TRef t
  | _, _ ->
      raise_semantic_error pos "Not an allowed type for variable declaration"

let check_member_decl m scope =
  match m.node with
  | FunDecl f ->
      add_entry f.fname f.rtype scope |> ignore;
      (* f.body will be None because we are in an interface *)
      FunDecl
        { rtype = f.rtype; fname = f.fname; formals = f.formals; body = None }
      <@> TFun (List.map (fun m -> match m with _, t -> t) f.formals, f.rtype)
  | VarDecl v -> check_vardecl v m.annot

let check_interface_decl i scope =
  match i.node with
  | InterfaceDecl { iname; declarations } ->
      (* add declarations to scope of interface *)
      let iscope = begin_block scope in
      let declarations =
        List.map (fun m -> check_member_decl m iscope) declarations
      in
      end_block iscope |> ignore;
      Hashtbl.add ints_scopes iname iscope;
      (* add interface definition to scope *)
      add_entry iname (TInterface iname) scope |> ignore;
      (* return typed InterfaceDecl *)
      let t_i = InterfaceDecl { iname; declarations } <@> TInterface iname in
      dbg_typ (show_interface_decl pp_typ t_i) i.annot;
      t_i

let rec check_exp e cname scope =
  match e.node with
  | LV lv ->
      let t_lv = check_lvalue lv cname scope in
      let typed_lv = LV t_lv <@> t_lv.annot in
      dbg_typ (show_expr pp_typ typed_lv) e.annot;
      typed_lv
  | Assign (lv, e) ->
      let t_e = check_exp e cname scope in
      let t_lv = check_lvalue lv cname scope in
      if t_lv.annot != t_e.annot then
        raise_semantic_error e.annot "Not same type"
      else
        let t_a = Assign (t_lv, t_e) <@> t_lv.annot in
        dbg_typ (show_expr pp_typ t_a) e.annot;
        t_a
  | ILiteral i ->
      let t_il = ILiteral i <@> TInt in
      dbg_typ (show_expr pp_typ t_il) e.annot;
      t_il
  | CLiteral c ->
      let t_cl = CLiteral c <@> TChar in
      dbg_typ (show_expr pp_typ t_cl) e.annot;
      t_cl
  | BLiteral b ->
      let t_bl = BLiteral b <@> TBool in
      dbg_typ (show_expr pp_typ t_bl) e.annot;
      t_bl
  | UnaryOp (op, e) -> (
      let t_e = check_exp e cname scope in
      match (op, t_e.annot) with
      | Not, TBool ->
          let t_uo = UnaryOp (op, t_e.node <@> TBool) <@> TBool in
          dbg_typ (show_expr pp_typ t_uo) e.annot;
          t_uo
      | Not, _ ->
          raise_semantic_error e.annot
            "Not a valid expression for not operation"
      | Neg, TInt ->
          let t_uo = UnaryOp (op, t_e.node <@> TInt) <@> TInt in
          dbg_typ (show_expr pp_typ t_uo) e.annot;
          t_uo
      | Neg, _ ->
          raise_semantic_error e.annot
            "Not a valid expression for negative operation")
  | Address lv ->
      let t_lv = check_lvalue lv cname scope in
      let t_a = Address t_lv <@> t_lv.annot in
      dbg_typ (show_expr pp_typ t_a) e.annot;
      t_a
  | BinaryOp (op, e1, e2) ->
      let t_bo = check_binary_op op e1 e2 e.annot cname scope in
      dbg_typ (show_expr pp_typ t_bo) e.annot;
      t_bo
  | Call (_, ide_f, args) -> (
      let args_list = List.map (fun x -> check_exp x cname scope) args in
      try
        (* Searching fun in local scope *)
        let tfun = lookup ide_f scope in
        match tfun with
        | TFun (typ_args_list, rt) -> (
            try
              List.iter2
                (fun x y ->
                  if x.annot != y then
                    raise_semantic_error e.annot
                      "Arguments with different types wrt declaration of \
                       function")
                args_list typ_args_list;
              let t_c = Call (None, ide_f, args_list) <@> rt in
              dbg_typ (show_expr pp_typ t_c) e.annot;
              t_c
            with Invalid_argument _ ->
              raise_semantic_error e.annot
                "Missing arguments for the function call")
        | _ -> raise_semantic_error e.annot "Not a function"
      with NotFoundEntry -> (
        let q = get_interface_qualifier cname ide_f e.annot in
        match q with
        | iname, t -> (
            match t with
            | TFun (typ_args_list, rt) -> (
                try
                  List.iter2
                    (fun x y ->
                      if x.annot != y then
                        raise_semantic_error e.annot
                          "Arguments with different types wrt declaration of \
                           function")
                    args_list typ_args_list;
                  let t_c = Call (Some iname, ide_f, args_list) <@> rt in
                  dbg_typ (show_expr pp_typ t_c) e.annot;
                  t_c
                with Invalid_argument _ ->
                  raise_semantic_error e.annot
                    "Missing arguments for the function call")
            | _ -> raise_semantic_error e.annot "Not a function")))

and check_lvalue lv cname scope =
  match lv.node with
  | AccVar (_, id2) -> (
      try
        let x = lookup id2 scope in
        let t_av = AccVar (None, id2) <@> x in
        dbg_typ (show_lvalue pp_typ t_av) lv.annot;
        t_av
      with NotFoundEntry -> (
        let q = get_interface_qualifier cname id2 lv.annot in
        match q with
        | iname, t ->
            let t_av = AccVar (Some iname, id2) <@> t in
            dbg_typ (show_lvalue pp_typ t_av) lv.annot;
            t_av))
  | AccIndex (lv', e) -> (
      let t_e = check_exp e cname scope in
      let t_lv = check_lvalue lv' cname scope in
      match t_lv.node with
      | AccVar (_, _) ->
          let t_ai = AccIndex (t_lv, t_e) <@> t_lv.annot in
          dbg_typ (show_lvalue pp_typ t_ai) lv.annot;
          t_ai
      (* impossible case, grammar does not allow it *)
      | _ ->
          raise_semantic_error lv.annot "Cannot define multidimensional arrays")

and check_binary_op op e1 e2 bo_pos cname scope =
  let t_e1 = check_exp e1 cname scope in
  let t_e2 = check_exp e2 cname scope in
  match (op, t_e1.annot, t_e2.annot) with
  (* Add *)
  | Add, TInt, TInt -> BinaryOp (op, t_e1, t_e2) <@> TInt
  | Add, TInt, _ ->
      raise_semantic_error e2.annot
        "Invalid operand type at right expression for add"
  | Add, _, TInt ->
      raise_semantic_error e1.annot
        "Invalid operand type at left expression for add"
  | Add, _, _ ->
      raise_semantic_error bo_pos
        "Invalid operands types in both expressions for add"
  (* Sub *)
  | Sub, TInt, TInt -> BinaryOp (op, t_e1, t_e2) <@> TInt
  | Sub, TInt, _ ->
      raise_semantic_error e2.annot
        "Invalid operand type at right expression for sub"
  | Sub, _, TInt ->
      raise_semantic_error e1.annot
        "Invalid operand type at left expression for sub"
  | Sub, _, _ ->
      raise_semantic_error bo_pos
        "Invalid operands types in both expressions for sub"
  (* Mult *)
  | Mult, TInt, TInt -> BinaryOp (op, t_e1, t_e2) <@> TInt
  | Mult, TInt, _ ->
      raise_semantic_error e2.annot
        "Invalid operand type at right expression for mult"
  | Mult, _, TInt ->
      raise_semantic_error e1.annot
        "Invalid operand type at left expression for mult"
  | Mult, _, _ ->
      raise_semantic_error bo_pos
        "Invalid operands types in both expressions for mult"
  (* Div *)
  | Div, TInt, TInt -> BinaryOp (op, t_e1, t_e2) <@> TInt
  | Div, TInt, _ ->
      raise_semantic_error e2.annot
        "Invalid operand type at right expression for div"
  | Div, _, TInt ->
      raise_semantic_error e1.annot
        "Invalid operand type at left expression for div"
  | Div, _, _ ->
      raise_semantic_error bo_pos
        "Invalid operands types in both expressions for div"
  (* Mod *)
  | Mod, TInt, TInt -> BinaryOp (op, t_e1, t_e2) <@> TInt
  | Mod, TInt, _ ->
      raise_semantic_error e2.annot
        "Invalid operand type at right expression for mod"
  | Mod, _, TInt ->
      raise_semantic_error e1.annot
        "Invalid operand type at left expression for mod"
  | Mod, _, _ ->
      raise_semantic_error bo_pos
        "Invalid operands types in both expressions for mod"
  (* Equal *)
  | Equal, TInt, TInt -> BinaryOp (op, t_e1, t_e2) <@> TInt
  | Equal, TBool, TBool -> BinaryOp (op, t_e1, t_e2) <@> TBool
  | Equal, (TInt | TBool), _ ->
      raise_semantic_error e2.annot
        "Invalid operand type at right expression for equal"
  | Equal, _, (TInt | TBool) ->
      raise_semantic_error e1.annot
        "Invalid operand type at left expression for equal"
  | Equal, _, _ ->
      raise_semantic_error bo_pos
        "Invalid operands types in both expressions for equal"
  (* Not Equal *)
  | Neq, TInt, TInt -> BinaryOp (op, t_e1, t_e2) <@> TInt
  | Neq, TBool, TBool -> BinaryOp (op, t_e1, t_e2) <@> TBool
  | Neq, (TInt | TBool), _ ->
      raise_semantic_error e2.annot
        "Invalid operand type at right expression for not equal"
  | Neq, _, (TInt | TBool) ->
      raise_semantic_error e1.annot
        "Invalid operand type at left expression for not equal"
  | Neq, _, _ ->
      raise_semantic_error bo_pos
        "Invalid operands types in both expressions for not equal"
  (* Less *)
  | Less, TInt, TInt -> BinaryOp (op, t_e1, t_e2) <@> TInt
  | Less, TBool, TBool -> BinaryOp (op, t_e1, t_e2) <@> TBool
  | Less, (TInt | TBool), _ ->
      raise_semantic_error e2.annot
        "Invalid operand type at right expression for less"
  | Less, _, (TInt | TBool) ->
      raise_semantic_error e1.annot
        "Invalid operand type at left expression for less"
  | Less, _, _ ->
      raise_semantic_error bo_pos
        "Invalid operands types in both expressions for less"
  (* Less And Equal *)
  | Leq, TInt, TInt -> BinaryOp (op, t_e1, t_e2) <@> TInt
  | Leq, TBool, TBool -> BinaryOp (op, t_e1, t_e2) <@> TBool
  | Leq, (TInt | TBool), _ ->
      raise_semantic_error e2.annot
        "Invalid operand type at right expression for less and equal"
  | Leq, _, (TInt | TBool) ->
      raise_semantic_error e1.annot
        "Invalid operand type at left expression for less and equal"
  | Leq, _, _ ->
      raise_semantic_error bo_pos
        "Invalid operands types in both expressions for less and equal"
  (* Greater *)
  | Greater, TInt, TInt -> BinaryOp (op, t_e1, t_e2) <@> TInt
  | Greater, TBool, TBool -> BinaryOp (op, t_e1, t_e2) <@> TBool
  | Greater, (TInt | TBool), _ ->
      raise_semantic_error e2.annot
        "Invalid operand type at right expression for greater"
  | Greater, _, (TInt | TBool) ->
      raise_semantic_error e1.annot
        "Invalid operand type at left expression for greater"
  | Greater, _, _ ->
      raise_semantic_error bo_pos
        "Invalid operands types in both expressions for greater"
  (* Greater And Equal *)
  | Geq, TInt, TInt -> BinaryOp (op, t_e1, t_e2) <@> TInt
  | Geq, TBool, TBool -> BinaryOp (op, t_e1, t_e2) <@> TBool
  | Geq, (TInt | TBool), _ ->
      raise_semantic_error e2.annot
        "Invalid operand type at right expression for greater and equal"
  | Geq, _, (TInt | TBool) ->
      raise_semantic_error e1.annot
        "Invalid operand type at left expression for greater and equal"
  | Geq, _, _ ->
      raise_semantic_error bo_pos
        "Invalid operands types in both expressions for greater and equal"
  (* And  *)
  | And, TBool, TBool -> BinaryOp (op, t_e1, t_e2) <@> TBool
  | And, TBool, _ ->
      raise_semantic_error e2.annot
        "Invalid operand type at right expression for and"
  | And, _, TBool ->
      raise_semantic_error e1.annot
        "Invalid operand type at left expression for and"
  | And, _, _ ->
      raise_semantic_error bo_pos
        "Invalid operands types in both expressions for and"
  (* Or *)
  | Or, TBool, TBool -> BinaryOp (op, t_e1, t_e2) <@> TBool
  | Or, TBool, _ ->
      raise_semantic_error e2.annot
        "Invalid operand type at right expression for or"
  | Or, _, TBool ->
      raise_semantic_error e1.annot
        "Invalid operand type at left expression for or"
  | Or, _, _ ->
      raise_semantic_error bo_pos
        "Invalid operands types in both expressions for or"

let rec check_stmt body cname fscope rtype =
  match body.node with
  | If (e, s1, s2) -> (
      let t_e = check_exp e cname fscope in
      let t_s1 = check_stmt s1 cname fscope rtype in
      let t_s2 = check_stmt s2 cname fscope rtype in
      match t_e.annot with
      | TBool ->
          let t_if = If (t_e, t_s1, t_s2) <@> TVoid in
          dbg_typ (show_stmt pp_typ t_if) body.annot;
          t_if
      | _ -> raise_semantic_error e.annot "Not a boolean type for condition")
  | While (e, s) -> (
      let t_e = check_exp e cname fscope in
      let t_s = check_stmt s cname fscope rtype in
      match t_e.annot with
      | TBool ->
          let t_while = While (t_e, t_s) <@> TVoid in
          dbg_typ (show_stmt pp_typ t_while) body.annot;
          t_while
      | _ -> raise_semantic_error e.annot "Not a boolean type for condition")
  | Expr e ->
      let t_e = Expr (check_exp e cname fscope) <@> TVoid in
      dbg_typ (show_stmt pp_typ t_e) body.annot;
      t_e
  | Return e -> (
      match e with
      | None ->
          if Option.get rtype == TVoid then (
            let t_r = Return None <@> TVoid in
            dbg_typ (show_stmt pp_typ t_r) body.annot;
            t_r)
          else
            raise_semantic_error body.annot
              "Returned type not matching function return type"
      | Some v ->
          let t_e = check_exp v cname fscope in
          if t_e.annot == Option.value rtype ~default:TVoid then (
            let t_r = Return (Some t_e) <@> t_e.annot in
            dbg_typ (show_stmt pp_typ t_r) body.annot;
            t_r)
          else
            raise_semantic_error v.annot
              "Returned type not matching function return type")
  | Block sordec -> check_ordec_list sordec cname fscope rtype
  | Skip -> Skip <@> TVoid

and check_ordec_list stmt_list cname scope rtype =
  let bscope = begin_block scope in
  let t_stmts =
    List.map
      (fun s ->
        match s.node with
        | LocalDecl (i, t) ->
            add_entry i t bscope |> ignore;
            let typed_ld = LocalDecl (i, t) <@> t in
            dbg_typ (show_stmtordec pp_typ typed_ld) s.annot;
            typed_ld
        | Stmt st ->
            let t_stmt = check_stmt st cname bscope rtype in
            let typed_stmt = Stmt t_stmt <@> t_stmt.annot in
            dbg_typ (show_stmtordec pp_typ typed_stmt) s.annot;
            typed_stmt)
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
      let fbody = check_stmt (Option.get f.body) cname fscope (Some f.rtype) in
      let f_typed =
        FunDecl
          {
            rtype = f.rtype;
            fname = f.fname;
            formals = f.formals;
            body = Some fbody;
          }
        <@> TFun
              (List.map (fun m -> match m with _, t -> t) f.formals, f.rtype)
      in
      dbg_typ (show_member_decl pp_typ f_typed) m.annot;
      f_typed
  | VarDecl v -> check_vardecl v m.annot

let rec check_component_def c interfaces scope =
  match c.node with
  | ComponentDecl { cname; uses; provides; definitions } ->
      (* get provided interfaces declarations *)
      let provints_declarations =
        List.filter
          (fun x ->
            match x.node with InterfaceDecl y -> List.mem y.iname provides)
          interfaces
        |> List.map (fun x ->
               match x.node with InterfaceDecl y -> y.declarations)
        |> List.flatten
      in
      Hashtbl.add used_interfaces cname uses;
      (* check that all provided definitions are implemented *)
      List.iter
        (fun x ->
          if
            List.mem x.node
              (List.map
                 (fun y ->
                   match y.node with
                   | FunDecl f ->
                       FunDecl
                         {
                           rtype = f.rtype;
                           fname = f.fname;
                           formals = f.formals;
                           body = Option.None;
                         }
                   | _ -> y.node)
                 definitions)
          then ()
          else raise_semantic_error x.annot "Function not implemented")
        provints_declarations;
      (* check to see if there are declarations with same name but different types *)
      if Bool.not (check_same_types provints_declarations) then
        raise_semantic_error c.annot
          "Conflicting names in definitions of provided interfaces";
      (* add definitions to component scope *)
      let cscope = begin_block scope in
      let definitions =
        List.map (fun m -> check_member_def m cname cscope) definitions
      in
      end_block cscope |> ignore;
      (* add component definition to scope *)
      add_entry cname (TComponent cname) scope |> ignore;
      (* return typed ComponentDecl *)
      let t_c =
        ComponentDecl { cname; uses; provides; definitions }
        <@> TComponent cname
      in
      dbg_typ (show_component_decl pp_typ t_c) c.annot;
      t_c

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
      | VarDecl _ -> true)

let rec check_connection_decl c cmps scope =
  match c with
  | Link (c1, used_int, c2, provided_int) ->
      (try lookup c1 scope |> ignore
       with NotFoundEntry -> failwith "component not found");
      (try lookup c2 scope |> ignore
       with NotFoundEntry -> failwith "component not found");
      (try
         lookup used_int scope |> ignore;
         if check_notusedprovided_int c1 used_int cmps then
           failwith "the interface is not used"
       with NotFoundEntry -> failwith "interface not found");
      (try
         lookup provided_int scope |> ignore;
         if check_notusedprovided_int c2 provided_int cmps then
           failwith "the interface is not used"
       with NotFoundEntry -> failwith "interface not found");

      dbg_typ (show_connection c) dummy_code_pos;
      Link (c1, used_int, c2, provided_int)

and check_notusedprovided_int component interface l =
  match l with
  | [] -> true
  | x :: xs -> (
      match x.node with
      | ComponentDecl { cname; uses; provides; _ } ->
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

  logger#info "Added Prelude and App interface into global scope";

  begin_block global_scope |> of_alist prelude_signature |> end_block |> ignore;
  logger#info "Added Prelude definitions into Prelude scope";

  begin_block global_scope |> of_alist app_signature |> end_block |> ignore;
  logger#info "Added App definitions into global scope";

  check_top_decls decls.interfaces decls.components decls.connections
    global_scope
