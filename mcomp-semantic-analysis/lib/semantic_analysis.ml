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
  logger#debug "\n%s at lines %d:%d, columns %d:%d" msg pos.start_line
    pos.end_line pos.start_column pos.end_column

let ( <@> ) n f = { node = n; annot = f }
let ints_scopes = Hashtbl.create 0
let used_interfaces = Hashtbl.create 0

let get_interface_qualifier cname ide =
  let rec g l =
    match l with
    | [] -> failwith ""
    | x :: xs -> (
        let scope = Hashtbl.find ints_scopes x in
        try
          let t = lookup ide scope in
          (x, t)
        with NotFoundEntry _ -> g xs)
  in
  g (Hashtbl.find used_interfaces cname)

let compare_mdecl x y =
  match (x.node, y.node) with
  | FunDecl fd, FunDecl fd' -> compare fd.fname fd'.fname
  | VarDecl (i, _), VarDecl (i', _) -> compare i i'
  | FunDecl fd, VarDecl (i, _) -> compare fd.fname i
  | VarDecl (i, _), FunDecl fd -> compare i fd.fname

let check_vardecl v pos =
  match v with
  | i, TInt -> (i, TInt)
  | i, TBool -> (i, TBool)
  | i, TChar -> (i, TChar)
  | i, TArray (t, s) ->
      (* arrays should have a size of at least 1 element *)
      let size = Option.get s in
      if size == 0 then
        raise_semantic_error pos "Array should have a size of at least 1"
      else if size < 0 then raise_semantic_error pos "Negative size for array"
      else (i, TArray (t, s))
  | i, TRef ((TInt | TBool | TChar) as t) -> (i, TRef t)
  | _, TRef _ ->
      raise_semantic_error pos "Can't declare a reference to an array"
  | _, TVoid ->
      raise_semantic_error pos
        (show_typ TVoid ^ " is not an allowed type for variable declaration")
  | _, _ -> failwith "Impossible case"

let rec check_fun_formals args pos =
  match args with
  | [] -> ()
  | ( _,
      ( TInt | TBool | TChar
      | TRef
          ( TInt | TBool | TChar
          | TArray (TInt, None)
          | TArray (TBool, None)
          | TArray (TChar, None) ) ) )
    :: xs ->
      check_fun_formals xs pos
  | (_, t) :: _ ->
      raise_semantic_error pos
        (show_typ t ^ " is not a valid argument type for function")

let check_member_decl m scope =
  match m.node with
  | FunDecl f ->
      (*
          f.body will be None because we are in an interface, f.rtype will be a
          basic type due to grammar
      *)
      let formals =
        List.map
          (fun (i, t) ->
            match t with
            | TArray (t', s) -> (i, TRef (TArray (t', s)))
            | _ -> (i, t))
          f.formals
      in
      check_fun_formals formals m.annot;
      let t_fd =
        FunDecl { rtype = f.rtype; fname = f.fname; formals; body = None }
        <@> TFun (List.map (fun m -> match m with _, t -> t) formals, f.rtype)
      in
      (try add_entry f.fname t_fd.annot scope |> ignore
       with DuplicateEntry _ ->
         raise_semantic_error m.annot
           ("Function " ^ f.fname ^ " already defined"));
      dbg_typ (show_member_decl pp_typ t_fd) m.annot;
      t_fd
  | VarDecl ((i, t) as v) ->
      let t_vd = VarDecl (check_vardecl v m.annot) <@> t in
      (* add entry to scope *)
      (try add_entry i t_vd.annot scope |> ignore
       with DuplicateEntry _ ->
         raise_semantic_error m.annot ("Variable " ^ i ^ " already defined"));
      dbg_typ (show_member_decl pp_typ t_vd) m.annot;
      t_vd

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
      (try add_entry iname (TInterface iname) scope |> ignore
       with DuplicateEntry _ ->
         raise_semantic_error i.annot ("Interface " ^ iname ^ " already defined"));
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
  | Assign (lv, e') ->
      let t_e = check_exp e' cname scope in
      (*
         when a reference does not occur in the left hand-side of
         an assignment, it is automatically dereferenced and
         its type is T
      *)
      let t_lv = check_lvalue lv cname scope in

      let t_a =
        match (t_lv.annot, t_e.annot) with
        (*
          when a reference does not occur in the left hand-side of
          an assignment, it is automatically dereferenced and
          its type is T
        *)
        | TInt, (TInt | TRef TInt)
        | TChar, (TChar | TRef TChar)
        | TBool, (TBool | TRef TBool) ->
            Assign (t_lv, t_e) <@> t_lv.annot
        (*
          when a reference x of type T& is on the left hand-side of
          an assignment: if e has type T, the assignment is well typed
        *)
        | TRef TInt, TInt | TRef TChar, TChar | TRef TBool, TBool ->
            Assign (t_lv, t_e) <@> t_lv.annot
        (*
          when a reference x of type T& is on the left hand-side of
          an assignment: if e has type T&, the assignment is well typed
        *)
        | TRef TInt, TRef TInt | TRef TChar, TRef TChar | TRef TBool, TRef TBool
          ->
            Assign (t_lv, t_e) <@> t_lv.annot
        | (TInt | TChar | TBool), _ ->
            raise_semantic_error e'.annot
              ("This expression has type " ^ show_typ t_e.annot
             ^ " but was expected of type " ^ show_typ t_lv.annot ^ " or "
             ^ show_typ (TRef t_lv.annot))
        | TRef ((TInt | TChar | TBool) as t), _ ->
            raise_semantic_error e'.annot
              ("This expression has type " ^ show_typ t_e.annot
             ^ " but was expected of type " ^ show_typ t ^ " or "
             ^ show_typ t_lv.annot)
        | TArray _, _ ->
            raise_semantic_error e.annot "Impossible to assign arrays"
        | _, _ ->
            raise_semantic_error e.annot
              ("This expression has type " ^ show_typ t_e.annot
             ^ " but was expected of type " ^ show_typ t_lv.annot)
      in
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
      | Not, (TBool as t) | Neg, (TInt as t) ->
          let t_uo = UnaryOp (op, t_e) <@> t in
          dbg_typ (show_expr pp_typ t_uo) e.annot;
          t_uo
      | Not, _ ->
          raise_semantic_error e.annot
            ("This expression has type " ^ show_typ t_e.annot
           ^ " but was expected of type " ^ show_typ TBool)
      | Neg, _ ->
          raise_semantic_error e.annot
            ("This expression has type " ^ show_typ t_e.annot
           ^ " but was expected of type " ^ show_typ TInt))
  | Address lv ->
      let t_lv = check_lvalue lv cname scope in
      let t_a = Address t_lv <@> TRef t_lv.annot in
      dbg_typ (show_expr pp_typ t_a) e.annot;
      t_a
  | BinaryOp (op, e1, e2) ->
      let t_bo = check_binary_op op e1 e2 e.annot cname scope in
      dbg_typ (show_expr pp_typ t_bo) e.annot;
      t_bo
  | Call (_, ide_f, args) -> (
      let args_list = List.map (fun x -> check_exp x cname scope) args in
      try
        (* searching fun in local scope *)
        let tfun = lookup ide_f scope in
        match tfun with
        (* only functions can be invoked *)
        | TFun (typ_args_list, rt) ->
            let t_c = Call (None, ide_f, args_list) <@> rt in
            dbg_typ (show_expr pp_typ t_c) e.annot;
            check_fun_call e.annot args_list typ_args_list;
            t_c
        | _ -> raise_semantic_error e.annot (ide_f ^ " is not a function")
      with NotFoundEntry _ -> (
        (* searching fun in used interfaces scope *)
        try
          let q = get_interface_qualifier cname ide_f in
          match q with
          | iname, t -> (
              match t with
              (* only functions can be invoked *)
              | TFun (typ_args_list, rt) ->
                  let t_c = Call (Some iname, ide_f, args_list) <@> rt in
                  dbg_typ (show_expr pp_typ t_c) e.annot;
                  check_fun_call e.annot args_list typ_args_list;
                  t_c
              | _ -> raise_semantic_error e.annot (ide_f ^ " is not a function")
              )
        with Not_found | Failure _ ->
          raise_semantic_error e.annot
            ("Could not find function " ^ show_identifier ide_f ^ " definition"))
      )

and check_fun_call pos passed_args typ_args_list =
  try
    List.iter2
      (fun x y ->
        match (x.annot, y) with
        | TInt, TInt
        | TBool, TBool
        | TChar, TChar
        | TRef TInt, TInt
        | TRef TBool, TBool
        | TRef TChar, TChar
        | TRef TInt, TRef TInt
        | TRef TChar, TRef TChar
        | TRef TBool, TRef TBool
        | ( (TRef (TArray (_, _)) | TArray (_, _)),
            (TRef (TArray (_, _)) | TArray (_, _)) ) ->
            ()
        | _ ->
            Printf.printf "%s---%s" (show_typ x.annot) (show_typ y);
            raise_semantic_error pos
              "Arguments with different types wrt declaration of function")
      passed_args typ_args_list
  with Invalid_argument _ ->
    (*
      function call must provides a number of arguments equals
      to the parameters of the function
    *)
    raise_semantic_error pos "Missing arguments for the function call"

and check_lvalue lv cname scope =
  match lv.node with
  | AccVar (_, id2) -> (
      try
        let x = lookup id2 scope in
        let t_av = AccVar (None, id2) <@> x in
        dbg_typ (show_lvalue pp_typ t_av) lv.annot;
        t_av
      with NotFoundEntry _ -> (
        try
          let q = get_interface_qualifier cname id2 in
          match q with
          | iname, t ->
              let t_av = AccVar (Some iname, id2) <@> t in
              dbg_typ (show_lvalue pp_typ t_av) lv.annot;
              t_av
        with Not_found | Failure _ ->
          raise_semantic_error lv.annot ("Variable " ^ id2 ^ " not declared")))
  | AccIndex (lv', e) -> (
      let t_e = check_exp e cname scope in
      (* in a[i] we expect i to be an integer value *)
      if not (equal_typ t_e.annot TInt) then
        raise_semantic_error e.annot
          ("This expression has type " ^ show_typ t_e.annot
         ^ " but was expected of type " ^ show_typ TInt);
      let t_lv = check_lvalue lv' cname scope in
      match (t_lv.node, t_lv.annot) with
      (* in a[i] we expect a to be to be an array or a reference to an array *)
      | AccVar _, (TArray (t, _) | TRef (TArray (t, _))) ->
          let t_ai = AccIndex (t_lv, t_e) <@> t in
          dbg_typ (show_lvalue pp_typ t_ai) lv.annot;
          t_ai
      | AccVar (_, id), _ ->
          raise_semantic_error lv.annot
            (id ^ " is not an array or reference to array")
      (* impossible case, grammar does not allow it *)
      | AccIndex _, _ ->
          raise_semantic_error lv.annot "Cannot define multidimensional arrays")

and check_binary_op op e1 e2 bo_pos cname scope =
  let t_e1 = check_exp e1 cname scope in
  let t_e2 = check_exp e2 cname scope in
  match (e1.annot, e2.annot, op, t_e1.annot, t_e2.annot) with
  (* correct operations *)
  | _, _, (Add | Sub | Mult | Div | Mod), (TRef TInt | TInt), (TRef TInt | TInt)
    ->
      BinaryOp (op, t_e1, t_e2) <@> TInt
  | _, _, Equal, (TRef TInt | TInt), (TRef TInt | TInt)
  | _, _, Equal, (TRef TBool | TBool), (TRef TBool | TBool) ->
      BinaryOp (op, t_e1, t_e2) <@> TBool
  | _, _, Neq, (TRef TInt | TInt), (TRef TInt | TInt)
  | _, _, Neq, (TRef TBool | TBool), (TRef TBool | TBool) ->
      BinaryOp (op, t_e1, t_e2) <@> TBool
  | _, _, (Less | Leq | Greater | Geq), (TRef TInt | TInt), (TRef TInt | TInt)
    ->
      BinaryOp (op, t_e1, t_e2) <@> TBool
  | _, _, (And | Or), (TRef TBool | TBool), (TRef TBool | TBool) ->
      BinaryOp (op, t_e1, t_e2) <@> TBool
  (* one of the operand has wrong type *)
  | ( pos,
      _,
      (Add | Sub | Mult | Div | Mod | Greater | Geq | Less | Leq),
      (TRef TInt | TInt),
      (_ as t) )
  | ( _,
      pos,
      (Add | Sub | Mult | Div | Mod | Greater | Geq | Less | Leq),
      (_ as t),
      (TRef TInt | TInt) ) ->
      raise_semantic_error pos
        ("This expression has type " ^ show_typ t ^ " but was expected of type "
       ^ show_typ TInt ^ " or " ^ show_typ (TRef TInt))
  | pos, _, (Equal | Neq), (_ as t), (TRef TInt | TInt)
  | _, pos, (Equal | Neq), (TRef TInt | TInt), (_ as t) ->
      raise_semantic_error pos
        ("This expression has type " ^ show_typ t ^ " but was expected of type "
       ^ show_typ TInt ^ " or " ^ show_typ (TRef TInt))
  | pos, _, (Equal | Neq), (_ as t), (TRef TBool | TBool)
  | _, pos, (Equal | Neq), (TRef TBool | TBool), (_ as t) ->
      raise_semantic_error pos
        ("This expression has type " ^ show_typ t ^ " but was expected of type "
       ^ show_typ TBool ^ " or " ^ show_typ (TRef TBool))
  | pos, _, (And | Or), (TRef TBool | TBool), (_ as t)
  | _, pos, (And | Or), (_ as t), (TRef TBool | TBool) ->
      raise_semantic_error pos
        ("This expression has type " ^ show_typ t ^ " but was expected of type "
       ^ show_typ TBool ^ " or " ^ show_typ (TRef TBool))
  (* both operands have wrong type *)
  | _, _, (Add | Sub | Div | Mult | Mod | Greater | Geq | Less | Leq), _, _ ->
      raise_semantic_error bo_pos
        ("Left expression has type " ^ show_typ t_e1.annot
       ^ " right expression has type " ^ show_typ t_e2.annot
       ^ " but both were expected of type " ^ show_typ TInt ^ " or "
       ^ show_typ (TRef TInt))
  | _, _, (Equal | Neq), _, _ ->
      raise_semantic_error bo_pos
        ("Left expression has type " ^ show_typ t_e1.annot
       ^ " right expression has type " ^ show_typ t_e2.annot
       ^ " but were expected of type " ^ show_typ TInt ^ "(or type "
       ^ show_typ (TRef TInt) ^ ") or " ^ show_typ TBool ^ "(or type "
       ^ show_typ (TRef TInt) ^ ")")
  | _, _, (And | Or), _, _ ->
      raise_semantic_error bo_pos
        ("Left expression has type " ^ show_typ t_e1.annot
       ^ " right expression has type " ^ show_typ t_e2.annot
       ^ " but were expected of type " ^ show_typ TBool ^ " or "
       ^ show_typ (TRef TBool))

let rec check_stmt body cname fscope rtype =
  match body.node with
  | If (e, s1, s2) -> (
      let t_e = check_exp e cname fscope in
      let t_s1 = check_stmt s1 cname fscope rtype in
      let t_s2 = check_stmt s2 cname fscope rtype in
      match t_e.annot with
      (* Conditional guard in if statement expect boolean values *)
      | TBool ->
          let t_if = If (t_e, t_s1, t_s2) <@> TVoid in
          dbg_typ (show_stmt pp_typ t_if) body.annot;
          t_if
      | _ ->
          raise_semantic_error e.annot
            ("This expression has type " ^ show_typ t_e.annot
           ^ " but was expected of type " ^ show_typ TBool))
  | While (e, s) -> (
      let t_e = check_exp e cname fscope in
      let t_s = check_stmt s cname fscope rtype in
      match t_e.annot with
      (* Conditional guard in while/for statement expect boolean values *)
      | TBool ->
          let t_while = While (t_e, t_s) <@> TVoid in
          dbg_typ (show_stmt pp_typ t_while) body.annot;
          t_while
      | _ ->
          raise_semantic_error e.annot
            ("This expression has type " ^ show_typ t_e.annot
           ^ " but was expected with type " ^ show_typ TBool))
  | Expr e ->
      let t_e = Expr (check_exp e cname fscope) <@> TVoid in
      dbg_typ (show_stmt pp_typ t_e) body.annot;
      t_e
  | Return e -> (
      match e with
      | None ->
          let r = Option.value rtype ~default:TVoid in
          if equal_typ (Option.get rtype) TVoid then (
            let t_r = Return None <@> r in
            dbg_typ (show_stmt pp_typ t_r) body.annot;
            t_r)
          else
            raise_semantic_error body.annot
              ("This expression has type " ^ show_typ TVoid
             ^ " but was expected with type " ^ show_typ r)
      | Some v ->
          let t_e = check_exp v cname fscope in
          let r = Option.value rtype ~default:TVoid in
          if equal_typ t_e.annot r then (
            let t_r = Return (Some t_e) <@> t_e.annot in
            dbg_typ (show_stmt pp_typ t_r) body.annot;
            t_r)
          else
            raise_semantic_error v.annot
              ("This expression has type " ^ show_typ t_e.annot
             ^ " but was expected with type " ^ show_typ r))
  | Block sordec -> check_ordec_list sordec cname fscope rtype
  | Skip -> Skip <@> TVoid

and check_ordec_list stmt_list cname scope rtype =
  let bscope = begin_block scope in
  let t_stmts =
    List.map
      (fun s ->
        match s.node with
        | LocalDecl ((i, t) as v) ->
            (try add_entry i t bscope |> ignore
             with DuplicateEntry _ ->
               raise_semantic_error s.annot
                 ("Variable " ^ i ^ " already defined"));
            let typed_ld = LocalDecl (check_vardecl v s.annot) <@> t in
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
      (* no function overloading *)
      List.iter
        (fun i ->
          let scope = Hashtbl.find ints_scopes i in
          try
            let _ = lookup f.fname scope |> ignore in
            raise_semantic_error m.annot
              ("Function " ^ show_identifier f.fname
             ^ " already defined in interface " ^ i)
          with NotFoundEntry _ -> ())
        (Hashtbl.find used_interfaces cname);
      let formals =
        List.map
          (fun (i, t) ->
            match t with
            | TArray (t', s) -> (i, TRef (TArray (t', s)))
            | _ -> (i, t))
          f.formals
      in
      let fscope = begin_block scope in
      (try of_alist formals fscope |> ignore
       with DuplicateEntry i ->
         raise_semantic_error m.annot
           ("Duplicate formal argument " ^ show_identifier i));
      check_fun_formals formals m.annot;
      (* f.body will be Some because we are considering the implementation *)
      let fbody = check_stmt (Option.get f.body) cname fscope (Some f.rtype) in
      end_block fscope |> ignore;
      let t =
        TFun (List.map (fun m -> match m with _, t -> t) formals, f.rtype)
      in
      let f_typed =
        FunDecl
          {
            rtype = f.rtype;
            fname = f.fname;
            formals = f.formals;
            body = Some fbody;
          }
        <@> t
      in
      dbg_typ (show_member_decl pp_typ f_typed) m.annot;
      f_typed
  | VarDecl ((_, t) as v) ->
      let t_vd = VarDecl (check_vardecl v m.annot) <@> t in
      t_vd

let rec check_component_def c interfaces scope =
  match c.node with
  | ComponentDecl { cname; uses; provides; definitions } ->
      (* adding Prelude in uses clause, if it not explicitly used *)
      let uses =
        if not (List.mem "Prelude" uses) then "Prelude" :: uses else uses
      in

      (* check that Prelude is not provided *)
      if List.mem "Prelude" provides then
        raise_semantic_error c.annot "Can't provide interface Prelude";

      (* check that interface App is provided by only one component *)
      if List.mem "App" provides then (
        if !app_provided then
          raise_semantic_error c.annot
            "Interface App provided by multiple components";

        app_provided := true;
        (* if the component provides App then search main function *)
        try
          List.find
            (fun x ->
              match x.node with
              | FunDecl d ->
                  equal_identifier d.fname "main"
                  && List.length d.formals == 0
                  && equal_typ d.rtype TInt
              | _ -> false)
            definitions
          |> ignore
        with Not_found ->
          raise_semantic_error c.annot
            ("The component " ^ show_identifier cname
           ^ " provides App but does not define main function"));

      (* check that interface App is not used *)
      if List.mem "App" uses then
        raise_semantic_error c.annot "Can't use interface App";

      (* check that there aren't multiple occurrences of an interface in uses clause *)
      if not (check_no_reps uses) then
        raise_semantic_error c.annot
          "Multiple occurrences of the same interface in uses clause";

      (* check that there aren't multiple occurrences of an interface in provides clause *)
      if not (check_no_reps provides) then
        raise_semantic_error c.annot
          "Multiple occurrences of the same interface in provides clause";

      (* check that in use clause we have only interfaces *)
      (try
         List.iter
           (fun x ->
             match lookup x scope with
             | TInterface _ -> ()
             | _ ->
                 raise_semantic_error c.annot
                   ("In use clause " ^ show_identifier x
                  ^ " is not an interface"))
           uses
       with NotFoundEntry i ->
         raise_semantic_error c.annot
           ("The interface " ^ show_identifier i
          ^ " specified in use clause does not exist"));

      (* check that in provides clause we have only interfaces *)
      (try
         List.iter
           (fun x ->
             match lookup x scope with
             | TInterface _ -> ()
             | _ ->
                 raise_semantic_error c.annot
                   ("In provides clause " ^ show_identifier x
                  ^ " is not an interface"))
           provides
       with NotFoundEntry i ->
         raise_semantic_error c.annot
           ("The interface " ^ show_identifier i
          ^ " specified in provides clause does not exist"));

      (* get provided interfaces declarations *)
      let provints_declarations = get_declarations provides interfaces in
      (* check to see if there are conflicting provided declarations *)
      if not (check_same_types provints_declarations) then
        raise_semantic_error c.annot
          "Conflicts in definitions of provided interfaces";

      (* remove duplicates *)
      let provints_declarations =
        let rec remove_dup l =
          match l with
          | [] -> []
          | [ x ] -> [ x ]
          | x :: y :: xs -> (
              match (x.node, y.node) with
              | FunDecl fd, FunDecl fd' ->
                  if equal_identifier fd.fname fd'.fname then x :: remove_dup xs
                  else x :: y :: remove_dup xs
              | VarDecl (i, _), VarDecl (i', _) ->
                  if equal_identifier i i' then x :: remove_dup xs
                  else x :: y :: remove_dup xs
              | _, _ -> x :: y :: remove_dup xs)
        in
        remove_dup provints_declarations
      in
      let usesints_declarations = get_declarations uses interfaces in

      (* check that there aren't same definitions in used interfaces *)
      if not (check_ambiguities usesints_declarations) then
        raise_semantic_error c.annot
          "Conflicts in definitions of used interfaces";

      (* check that there aren't conflicting declarations between used and
         provided interfaces *)
      if
        not
          (check_ambiguities
             (List.append provints_declarations usesints_declarations
             |> List.sort compare_mdecl))
      then
        raise_semantic_error c.annot
          "Conflicts in definitions of used and provided interfaces";
      Hashtbl.add used_interfaces cname uses;

      (* add definitions to component scope *)
      let cscope = begin_block scope in
      (* check types of each member definition *)
      let definitions =
        List.map
          (fun m ->
            (match m.node with
            | FunDecl f -> (
                (* add entry to scope *)
                try
                  add_entry f.fname
                    (TFun (List.map (fun (_, t) -> t) f.formals, f.rtype))
                    cscope
                  |> ignore
                with DuplicateEntry _ ->
                  raise_semantic_error m.annot
                    ("Function " ^ show_identifier f.fname ^ " already defined")
                )
            | VarDecl (i, t) -> (
                try add_entry i t cscope |> ignore
                with DuplicateEntry _ ->
                  raise_semantic_error m.annot
                    ("Variable " ^ show_identifier i ^ " already defined")));
            check_member_def m cname cscope)
          definitions
      in
      end_block cscope |> ignore;

      (* check that all provided definitions are implemented *)
      List.iter
        (fun x ->
          (* iterating on all declarations that the component must provide *)
          match x.node with
          | FunDecl fd -> (
              try
                List.find
                  (fun y ->
                    match y.node with
                    | FunDecl fd' ->
                        if equal_identifier fd.fname fd'.fname then
                          if equal_typ x.annot y.annot then true
                          else
                            raise_semantic_error c.annot
                              ("Function " ^ show_identifier fd.fname
                             ^ " has not the same signature of the one defined \
                                in the corresponding interface")
                        else false
                    | _ -> false)
                  definitions
                |> ignore
              with Not_found ->
                raise_semantic_error c.annot
                  ("Function " ^ show_identifier fd.fname ^ " not defined"))
          | VarDecl (i, _) -> (
              try
                List.find
                  (fun y ->
                    match y.node with
                    | VarDecl (i', _) ->
                        if equal_identifier i i' then
                          if equal_typ x.annot y.annot then true
                          else
                            raise_semantic_error c.annot
                              ("Variable " ^ show_identifier i
                             ^ " has not the same signature of the one defined \
                                in the corrispective interface")
                        else false
                    | _ -> false)
                  definitions
                |> ignore
              with Not_found ->
                raise_semantic_error c.annot
                  ("Variable " ^ show_identifier i ^ " not defined")))
        provints_declarations;

      (* return typed ComponentDecl *)
      let t_c =
        ComponentDecl { cname; uses; provides; definitions }
        <@> TComponent cname
      in
      dbg_typ (show_component_decl pp_typ t_c) c.annot;
      t_c

and app_provided = ref false

and get_declarations l all_interfaces =
  List.filter
    (fun x -> match x.node with InterfaceDecl y -> List.mem y.iname l)
    all_interfaces
  |> List.map (fun x -> match x.node with InterfaceDecl y -> y.declarations)
  |> List.flatten |> List.sort compare_mdecl

and check_same_types decs =
  match decs with
  | [ _ ] | [] -> true
  | x :: y :: xs -> (
      match (x.node, y.node) with
      | FunDecl fd, FunDecl fd' ->
          if equal_identifier fd.fname fd'.fname then
            if equal_typ x.annot y.annot then check_same_types (y :: xs)
            else false
          else check_same_types (y :: xs)
      | VarDecl (i, _), VarDecl (i', _) ->
          if equal_identifier i i' then
            if equal_typ x.annot y.annot then check_same_types (y :: xs)
            else false
          else check_same_types (y :: xs)
      | FunDecl fd, VarDecl (i, _) ->
          if equal_identifier fd.fname i then
            if equal_typ x.annot y.annot then check_same_types (y :: xs)
            else false
          else check_same_types (y :: xs)
      | VarDecl (i, _), FunDecl fd ->
          if equal_identifier i fd.fname then
            if equal_typ x.annot y.annot then check_same_types (y :: xs)
            else false
          else check_same_types (y :: xs))

and check_ambiguities l =
  match l with
  | [ _ ] | [] -> true
  | x :: y :: xs -> (
      match (x.node, y.node) with
      | FunDecl fd, FunDecl fd' ->
          if equal_identifier fd.fname fd'.fname then false
          else check_same_types (y :: xs)
      | VarDecl (i, _), VarDecl (i', _) ->
          if equal_identifier i i' then false else check_same_types (y :: xs)
      | FunDecl fd, VarDecl (i, _) ->
          if equal_identifier fd.fname i then false
          else check_same_types (y :: xs)
      | VarDecl (i, _), FunDecl fd ->
          if equal_identifier i fd.fname then false
          else check_same_types (y :: xs))

and check_no_reps l =
  match List.sort compare l with
  | [] | [ _ ] -> true
  | x :: y :: xs ->
      if equal_identifier x y then false else check_no_reps (y :: xs)

let check_links links scope =
  List.iter
    (fun x ->
      match x with
      | Link (c1, i1, c2, i2) -> (
          (try
             let x = lookup c1 scope in
             match x with
             | TComponent _ -> ()
             | _ ->
                 raise_semantic_error dummy_code_pos
                   (show_identifier c1 ^ " is not a component")
           with NotFoundEntry _ ->
             raise_semantic_error dummy_code_pos
               ("Component " ^ show_identifier c1 ^ " is not defined"));
          (try
             let x = lookup c2 scope in
             match x with
             | TComponent _ -> ()
             | _ ->
                 raise_semantic_error dummy_code_pos
                   (show_identifier c2 ^ " is not a component")
           with NotFoundEntry _ ->
             raise_semantic_error dummy_code_pos
               ("Component " ^ show_identifier c2 ^ " is not defined"));
          (try
             let x = lookup i1 scope in
             match x with
             | TInterface _ -> ()
             | _ ->
                 raise_semantic_error dummy_code_pos
                   (show_identifier i1 ^ " is not an interface")
           with NotFoundEntry _ ->
             raise_semantic_error dummy_code_pos
               ("Interface " ^ show_identifier i1 ^ " is not defined"));
          try
            let x = lookup i2 scope in
            match x with
            | TInterface _ -> ()
            | _ ->
                raise_semantic_error dummy_code_pos
                  (show_identifier i2 ^ " is not an interface")
          with NotFoundEntry _ ->
            raise_semantic_error dummy_code_pos
              ("Interface " ^ show_identifier i2 ^ " is not defined")))
    links

let check_top_decls ints comps conns scope =
  let interfaces = List.map (fun i -> check_interface_decl i scope) ints in

  (* adding the components into scope here just to not have problems due to list ordering *)
  List.iter
    (fun x ->
      match x.node with
      | ComponentDecl c -> (
          try add_entry c.cname (TComponent c.cname) scope |> ignore
          with DuplicateEntry _ ->
            raise_semantic_error x.annot
              ("Component " ^ show_identifier c.cname ^ " already defined")))
    comps;

  let components =
    List.map (fun cmp -> check_component_def cmp interfaces scope) comps
  in

  check_links conns scope;
  if not !app_provided then
    raise_semantic_error dummy_code_pos "No component provides interface App";
  CompilationUnit { interfaces; components; connections = conns }

let type_check (CompilationUnit decls : code_pos compilation_unit) =
  let global_scope =
    empty_table ()
    |> add_entry "Prelude" (TInterface "Prelude")
    |> add_entry "App" (TInterface "App")
  in

  logger#info "Added Prelude and App interface into global scope";

  let p = begin_block global_scope |> of_alist prelude_signature in
  end_block p |> ignore;
  Hashtbl.add ints_scopes "Prelude" p;
  logger#info "Added Prelude definitions into Prelude scope";

  let a = begin_block global_scope |> of_alist app_signature in
  end_block a |> ignore;
  Hashtbl.add ints_scopes "App" a;
  logger#info "Added App definitions into global scope";

  check_top_decls decls.interfaces decls.components decls.connections
    global_scope
