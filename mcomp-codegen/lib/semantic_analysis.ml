open Ast
open Symbol_table
open Mcomp_stdlib
open Location
open Easy_logging

exception Semantic_error of Location.code_pos * string

let logger =
  let file_h = Handlers.File ("Semantic analysis", Logging.Debug) in
  let cli_h = Handlers.Cli Logging.Info in
  Logging.make_logger "Semantic analysis" Logging.Debug [ cli_h; file_h ]

let raise_semantic_error pos msg =
  logger#error "Error at lines %d:%d, columns %d:%d: %s" pos.start_line
    pos.end_line pos.start_column pos.end_column msg;
  raise (Semantic_error (pos, msg))

let dbg_typ msg pos =
  logger#debug "\n%s at lines %d:%d, columns %d:%d" msg pos.start_line
    pos.end_line pos.start_column pos.end_column

let ( <@> ) n f = { node = n; annot = f }

(* used to keep track of interfaces scopes *)
let ints_scopes = Hashtbl.create 0

(* used to keep track of used interfaces of each component *)
let used_interfaces = Hashtbl.create 0

(* recover interface name if a component uses a declaration
   of an interface *)
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

(* comparator function used when sorting *)
let compare_mdecl x y =
  match (x.node, y.node) with
  | FunDecl fd, FunDecl fd' -> compare fd.fname fd'.fname
  | VarDecl (i, _), VarDecl (i', _) -> compare i i'
  | FunDecl fd, VarDecl (i, _) -> compare fd.fname i
  | VarDecl (i, _), FunDecl fd -> compare i fd.fname

let check_vardecl v pos =
  match v with
  | i, ((TInt | TFloat | TBool | TChar) as t) -> (i, t)
  | i, TArray (((TInt | TFloat | TBool | TChar | TRef _) as t), s) ->
      if Option.is_none s then
        raise_semantic_error pos "Array declaration needs to have a size";

      let size = Option.get s in
      (* arrays should have a size of at least 1 element *)
      if size == 0 then
        raise_semantic_error pos "Array should have a size of at least 1"
      else if size < 0 then raise_semantic_error pos "Negative size for array"
      else (i, TArray (t, s))
  | i, TRef ((TInt | TBool | TChar | TFloat) as t) -> (i, TRef t)
  | _, TRef (TArray _) ->
      raise_semantic_error pos "Can't declare a reference to an array"
  | _, TVoid ->
      raise_semantic_error pos
        (show_typ TVoid ^ " is not an allowed type for variable declaration")
  | _, _ -> failwith "impossible case"

let check_fun_formals arg pos =
  match arg with
  | ( _,
      ( TInt | TFloat | TBool | TChar
      | TRef (TInt | TFloat | TBool | TChar)
      | TArray ((TInt | TFloat | TBool | TChar), None)
      | TArray (TRef (TInt | TFloat | TBool | TChar), None) ) ) ->
      ()
  | _, t ->
      raise_semantic_error pos
        (show_typ t ^ " is not a valid argument type for function")

let check_member_decl m scope =
  match m.node with
  | FunDecl f ->
      (*
          f.body will be None because we are in an interface, f.rtype will be a
          basic type due to grammar
      *)
      (* check that formal arguments types are ok *)
      List.iter (fun x -> check_fun_formals x m.annot) f.formals;

      let t_fd =
        FunDecl
          { rtype = f.rtype; fname = f.fname; formals = f.formals; body = None }
        <@> TFun
              (List.map (fun m -> match m with _, t -> t) f.formals, f.rtype)
      in
      (* add entry to scope *)
      (try add_entry f.fname t_fd.annot scope |> ignore
       with DuplicateEntry _ ->
         raise_semantic_error m.annot
           ("Function " ^ show_identifier f.fname ^ " already defined"));

      dbg_typ (show_member_decl pp_typ t_fd) m.annot;
      t_fd
  | VarDecl ((i, t) as v) ->
      let t_vd = VarDecl (check_vardecl v m.annot) <@> t in
      (* add entry to scope *)
      (try add_entry i t_vd.annot scope |> ignore
       with DuplicateEntry _ ->
         raise_semantic_error m.annot
           ("Variable " ^ show_identifier i ^ " already defined"));

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
         raise_semantic_error i.annot
           ("Interface " ^ show_identifier iname ^ " already defined"));
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
      let t_lv = check_lvalue lv cname scope in
      let t_a =
        match (t_lv.annot, t_e.annot) with
        (*
          when a reference does not occur in the left hand-side of
          an assignment, it is automatically dereferenced and
          its type is T
        *)
        | ( ((TInt | TFloat | TChar | TBool) as t),
            (((TInt | TFloat | TChar | TBool) as t') | TRef t') )
          when equal_typ t t' ->
            Assign (t_lv, t_e) <@> t_lv.annot
        (*
          when a reference x of type T& is on the left hand-side of
          an assignment: if e has type T, the assignment is well typed
        *)
        | TRef t, t' when equal_typ t t' -> Assign (t_lv, t_e) <@> t_lv.annot
        (*
          when a reference x of type T& is on the left hand-side of
          an assignment: if e has type T&, the assignment is well typed
        *)
        | TRef t, TRef t' when equal_typ t t' ->
            Assign (t_lv, t_e) <@> t_lv.annot
        | (TInt | TFloat | TChar | TBool), _ ->
            raise_semantic_error e'.annot
              ("This expression has type " ^ show_typ t_e.annot
             ^ " but was expected of type " ^ show_typ t_lv.annot ^ " or "
             ^ show_typ (TRef t_lv.annot))
        | TRef ((TInt | TFloat | TChar | TBool) as t), _ ->
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
  | FLiteral f ->
      let t_fl = FLiteral f <@> TFloat in

      dbg_typ (show_expr pp_typ t_fl) e.annot;
      t_fl
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
      | Not, ((TBool as t) | TRef (TBool as t)) ->
          let t_uo = UnaryOp (op, t_e) <@> t in

          dbg_typ (show_expr pp_typ t_uo) e.annot;
          t_uo
      | Not, _ ->
          raise_semantic_error e.annot
            ("This expression has type " ^ show_typ t_e.annot
           ^ " but was expected of type " ^ show_typ TBool)
      | ( Neg,
          ((TInt as t) | (TFloat as t) | TRef (TInt as t) | TRef (TFloat as t))
        ) ->
          let t_uo = UnaryOp (op, t_e) <@> t in

          dbg_typ (show_expr pp_typ t_uo) e.annot;
          t_uo
      | Neg, _ ->
          raise_semantic_error e.annot
            ("This expression has type " ^ show_typ t_e.annot
           ^ " but was expected of type " ^ show_typ TInt ^ " (or "
           ^ show_typ (TRef TInt) ^ ") or type " ^ show_typ TFloat ^ " (or "
           ^ show_typ (TRef TFloat) ^ ")"))
  | DoubleOp (op, lv) -> (
      let t_lv = check_lvalue lv cname scope in

      match (op, t_lv.annot) with
      | ( (PreIncr | PostIncr | PreDecr | PostDecr),
          ((TInt as t) | (TFloat as t) | TRef (TInt as t) | TRef (TFloat as t))
        ) ->
          let t_o = DoubleOp (op, t_lv) <@> t in

          dbg_typ (show_expr pp_typ t_o) e.annot;
          t_o
      | (PreIncr | PostIncr | PreDecr | PostDecr), _ ->
          raise_semantic_error e.annot
            ("This expression has type " ^ show_typ t_lv.annot
           ^ " but was expected of type " ^ show_typ TInt ^ " (or "
           ^ show_typ (TRef TInt) ^ ") or type " ^ show_typ TFloat ^ " (or "
           ^ show_typ (TRef TFloat) ^ ")"))
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
      (* function used to check passed arguments types *)
      let check_fun_call pos passed_args typ_args_list =
        try
          List.iter2
            (fun x y ->
              match (x.annot, y) with
              | t, t' when equal_typ t t' -> ()
              | TRef t, t' when equal_typ t t' -> ()
              | TArray (t, _), TArray (t', _) when equal_typ t t' -> ()
              | _ ->
                  raise_semantic_error pos
                    "Arguments with different types wrt declaration of function")
            passed_args typ_args_list
        with Invalid_argument _ ->
          (*
            function call must provide a number of arguments equals
            to the parameters of the function
          *)
          raise_semantic_error pos "Missing arguments for the function call"
      in
      let args_list = List.map (fun x -> check_exp x cname scope) args in

      try
        (* searching fun in scope *)
        let tfun = lookup ide_f scope in
        (* only functions can be invoked *)
        match tfun with
        | TFun (typ_args_list, rt) ->
            let t_c = Call (None, ide_f, args_list) <@> rt in

            dbg_typ (show_expr pp_typ t_c) e.annot;
            check_fun_call e.annot args_list typ_args_list;
            t_c
        | _ ->
            raise_semantic_error e.annot
              (show_identifier ide_f ^ " is not a function")
      with NotFoundEntry _ -> (
        (* searching fun in used interfaces scope *)
        try
          let q = get_interface_qualifier cname ide_f in

          match q with
          | iname, t -> (
              (* only functions can be invoked *)
              match t with
              | TFun (typ_args_list, rt) ->
                  let t_c = Call (Some iname, ide_f, args_list) <@> rt in

                  dbg_typ (show_expr pp_typ t_c) e.annot;
                  check_fun_call e.annot args_list typ_args_list;
                  t_c
              | _ ->
                  raise_semantic_error e.annot
                    (show_identifier ide_f ^ " is not a function"))
        with Not_found | Failure _ ->
          raise_semantic_error e.annot
            ("Could not find function " ^ show_identifier ide_f ^ " definition"))
      )

and check_lvalue lv cname scope =
  match lv.node with
  | AccVar (_, id2) -> (
      try
        let t = lookup id2 scope in
        let t_av = AccVar (None, id2) <@> t in

        dbg_typ (show_lvalue pp_typ t_av) lv.annot;
        t_av
      with NotFoundEntry _ -> (
        (* variable declared in an interface used *)
        try
          let q = get_interface_qualifier cname id2 in

          match q with
          | iname, t ->
              let t_av = AccVar (Some iname, id2) <@> t in

              dbg_typ (show_lvalue pp_typ t_av) lv.annot;
              t_av
        with Not_found | Failure _ ->
          raise_semantic_error lv.annot
            ("Variable " ^ show_identifier id2 ^ " not declared")))
  | AccIndex (lv', e) -> (
      let t_e = check_exp e cname scope in

      (* in a[i] we expect i to be an integer value *)
      if not (equal_typ t_e.annot TInt) then
        raise_semantic_error e.annot
          ("This expression has type " ^ show_typ t_e.annot
         ^ " but was expected of type " ^ show_typ TInt);

      let t_lv = check_lvalue lv' cname scope in

      match (t_lv.node, t_lv.annot) with
      (* in a[i] we expect a to be to be an array *)
      | AccVar _, TArray (t, _) ->
          let t_ai = AccIndex (t_lv, t_e) <@> t in
          dbg_typ (show_lvalue pp_typ t_ai) lv.annot;
          t_ai
      | AccVar (_, id), _ ->
          raise_semantic_error lv'.annot
            (show_identifier id ^ " is not an array")
      (* impossible case, grammar does not allow it *)
      | AccIndex _, _ -> assert false)

and check_binary_op op e1 e2 bo_pos cname scope =
  let t_e1 = check_exp e1 cname scope in
  let t_e2 = check_exp e2 cname scope in
  match (e1.annot, e2.annot, op, t_e1.annot, t_e2.annot) with
  (* correct operations *)
  | ( _,
      _,
      (Add | Sub | Mult | Div | Mod),
      (TRef t | ((TInt | TFloat) as t)),
      (TRef t' | ((TInt | TFloat) as t')) )
    when equal_typ t t' ->
      BinaryOp (op, t_e1, t_e2) <@> t
  | ( _,
      _,
      (Equal | Neq),
      (TRef t | ((TInt | TFloat | TBool) as t)),
      (TRef t' | ((TInt | TFloat | TBool) as t')) )
    when equal_typ t t' ->
      BinaryOp (op, t_e1, t_e2) <@> TBool
  | ( _,
      _,
      (Less | Leq | Greater | Geq),
      (TRef t | ((TInt | TFloat) as t)),
      (TRef t' | ((TInt | TFloat) as t')) )
    when equal_typ t t' ->
      BinaryOp (op, t_e1, t_e2) <@> TBool
  | _, _, (And | Or), (TRef TBool | TBool), (TRef TBool | TBool) ->
      BinaryOp (op, t_e1, t_e2) <@> TBool
  (* one of the operands has wrong type *)
  | ( _,
      pos,
      (Add | Sub | Mult | Div | Mod | Greater | Geq | Less | Leq),
      (TRef TInt | TInt),
      (_ as t) )
  | ( pos,
      _,
      (Add | Sub | Mult | Div | Mod | Greater | Geq | Less | Leq),
      (_ as t),
      (TRef TInt | TInt) ) ->
      raise_semantic_error pos
        (show_binop op ^ " This expression has type " ^ show_typ t
       ^ " but was expected of type " ^ show_typ TInt ^ " or "
       ^ show_typ (TRef TInt))
  | ( _,
      pos,
      (Add | Sub | Mult | Div | Mod | Greater | Geq | Less | Leq),
      (TRef TFloat | TFloat),
      (_ as t) )
  | ( pos,
      _,
      (Add | Sub | Mult | Div | Mod | Greater | Geq | Less | Leq),
      (_ as t),
      (TRef TFloat | TFloat) ) ->
      raise_semantic_error pos
        (show_binop op ^ " This expression has type " ^ show_typ t
       ^ " but was expected of type " ^ show_typ TFloat ^ " or "
       ^ show_typ (TRef TFloat))
  | pos, _, (Equal | Neq), (_ as t), (TRef TInt | TInt)
  | _, pos, (Equal | Neq), (TRef TInt | TInt), (_ as t) ->
      raise_semantic_error pos
        (show_binop op ^ " This expression has type " ^ show_typ t
       ^ " but was expected of type " ^ show_typ TInt ^ " or "
       ^ show_typ (TRef TInt))
  | pos, _, (Equal | Neq), (_ as t), (TRef TFloat | TFloat)
  | _, pos, (Equal | Neq), (TRef TFloat | TFloat), (_ as t) ->
      raise_semantic_error pos
        (show_binop op ^ " This expression has type " ^ show_typ t
       ^ " but was expected of type " ^ show_typ TFloat ^ " or "
       ^ show_typ (TRef TFloat))
  | pos, _, (Equal | Neq), (_ as t), (TRef TBool | TBool)
  | _, pos, (Equal | Neq), (TRef TBool | TBool), (_ as t) ->
      raise_semantic_error pos
        (show_binop op ^ " This expression has type " ^ show_typ t
       ^ " but was expected of type " ^ show_typ TBool ^ " or "
       ^ show_typ (TRef TBool))
  | pos, _, (And | Or), (TRef TBool | TBool), (_ as t)
  | _, pos, (And | Or), (_ as t), (TRef TBool | TBool) ->
      raise_semantic_error pos
        (show_binop op ^ " This expression has type " ^ show_typ t
       ^ " but was expected of type " ^ show_typ TBool ^ " or "
       ^ show_typ (TRef TBool))
  (* both operands have wrong type *)
  | _, _, (Add | Sub | Div | Mult | Mod | Greater | Geq | Less | Leq), _, _ ->
      raise_semantic_error bo_pos
        (show_binop op ^ " Left expression has type " ^ show_typ t_e1.annot
       ^ " right expression has type " ^ show_typ t_e2.annot
       ^ " but both were expected of type " ^ show_typ TInt ^ " (or type "
       ^ show_typ (TRef TInt) ^ ") or " ^ show_typ TFloat ^ "(or type "
       ^ show_typ (TRef TFloat) ^ ")")
  | _, _, (Equal | Neq), _, _ ->
      raise_semantic_error bo_pos
        (show_binop op ^ " Left expression has type " ^ show_typ t_e1.annot
       ^ " right expression has type " ^ show_typ t_e2.annot
       ^ " but were expected of type " ^ show_typ TInt ^ "(or type "
       ^ show_typ (TRef TInt) ^ ") or " ^ show_typ TBool ^ "(or type "
       ^ show_typ (TRef TInt) ^ ") or " ^ show_typ TFloat ^ "(or type "
       ^ show_typ (TRef TFloat) ^ ")")
  | _, _, (And | Or), _, _ ->
      raise_semantic_error bo_pos
        (show_binop op ^ " Left expression has type " ^ show_typ t_e1.annot
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
      (* conditional guard in if statement expect boolean values *)
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
      (* conditional guard in while/for statement expect boolean values *)
      | TBool ->
          let t_while = While (t_e, t_s) <@> TVoid in

          dbg_typ (show_stmt pp_typ t_while) body.annot;
          t_while
      | _ ->
          raise_semantic_error e.annot
            ("This expression has type " ^ show_typ t_e.annot
           ^ " but was expected with type " ^ show_typ TBool))
  | DoWhile (s, e) -> (
      let t_e = check_exp e cname fscope in
      let t_s = check_stmt s cname fscope rtype in

      match t_e.annot with
      (* conditional guard in do while statement expect boolean values *)
      | TBool ->
          let t_dowhile = DoWhile (t_s, t_e) <@> TVoid in

          dbg_typ (show_stmt pp_typ t_dowhile) body.annot;
          t_dowhile
      | _ ->
          raise_semantic_error e.annot
            ("This expression has type " ^ show_typ t_e.annot
           ^ " but was expected with type " ^ show_typ TBool))
  | Expr e ->
      let t_e = Expr (check_exp e cname fscope) <@> TVoid in

      dbg_typ (show_stmt pp_typ t_e) body.annot;
      t_e
  | Return e -> (
      let r = Option.value rtype ~default:TVoid in
      match e with
      | None ->
          if equal_typ r TVoid then (
            let t_r = Return None <@> r in

            dbg_typ (show_stmt pp_typ t_r) body.annot;
            t_r)
          else
            raise_semantic_error body.annot
              ("This expression has type " ^ show_typ TVoid
             ^ " but was expected with type " ^ show_typ r)
      | Some v ->
          let t_e = check_exp v cname fscope in

          (* only basic type return, if it is a ref it will be dereferenced *)
          if equal_typ t_e.annot r || equal_typ t_e.annot (TRef r) then (
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
  (* create new scope *)
  let bscope = begin_block scope in
  let t_stmts =
    List.map
      (fun s ->
        match s.node with
        | LocalDecl ((i, t) as v) ->
            (* add local variable to scope *)
            (try add_entry i t bscope |> ignore
             with DuplicateEntry _ ->
               raise_semantic_error s.annot
                 ("Variable " ^ show_identifier i ^ " already defined"));

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
             ^ " already defined in interface " ^ show_identifier i)
          with NotFoundEntry _ -> ())
        (Hashtbl.find used_interfaces cname);

      (* create new scope and add formal args *)
      let fscope = begin_block scope in
      (try of_alist f.formals fscope |> ignore
       with DuplicateEntry i ->
         raise_semantic_error m.annot
           ("Duplicate formal argument " ^ show_identifier i));

      (* check that formal arguments types are ok *)
      List.iter (fun x -> check_fun_formals x m.annot) f.formals;

      (* f.body will be Some because we are considering the implementation,
         start checking statements *)
      let fbody = check_stmt (Option.get f.body) cname fscope (Some f.rtype) in
      end_block fscope |> ignore;

      (* create typed FunDecl *)
      let t =
        TFun (List.map (fun m -> match m with _, t -> t) f.formals, f.rtype)
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

      dbg_typ (show_member_decl pp_typ t_vd) m.annot;
      t_vd

let rec check_component_def c interfaces scope =
  match c.node with
  | ComponentDecl { cname; uses; provides; definitions } ->
      (* adding Prelude in uses clause, if it is not explicitly used *)
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

      (* check for same identifier "provides"/"use" clause *)
      let rec check_no_reps l =
        match List.sort compare l with
        | [] | [ _ ] -> true
        | x :: y :: xs ->
            if equal_identifier x y then false else check_no_reps (y :: xs)
      in

      (* check that there aren't multiple occurrences of an interface in uses clause *)
      if not (check_no_reps uses) then
        raise_semantic_error c.annot
          "Multiple occurrences of the same interface in uses clause";

      (* check that there aren't multiple occurrences of an interface in provides clause *)
      if not (check_no_reps provides) then
        raise_semantic_error c.annot
          "Multiple occurrences of the same interface in provides clause";

      (* used to check that in "provide" or "use" clause we have only
         interfaces *)
      let check_in_clause clause_name clause_args =
        try
          List.iter
            (fun x ->
              match lookup x scope with
              | TInterface _ -> ()
              | _ ->
                  raise_semantic_error c.annot
                    ("In " ^ clause_name ^ " clause " ^ show_identifier x
                   ^ " is not an interface"))
            clause_args
        with NotFoundEntry i ->
          raise_semantic_error c.annot
            ("The interface " ^ show_identifier i ^ " specified in "
           ^ clause_name ^ " clause does not exist")
      in
      check_in_clause "uses" uses;
      check_in_clause "provides" provides;

      (* used to retrieve declarations of the interfaces specified in
         "provide" or "used" clause *)
      let get_declarations l all_interfaces =
        List.filter
          (fun x -> match x.node with InterfaceDecl y -> List.mem y.iname l)
          all_interfaces
        |> List.map (fun x ->
               match x.node with InterfaceDecl y -> y.declarations)
        |> List.flatten |> List.sort compare_mdecl
      in

      (* get provided interfaces declarations *)
      let provints_declarations = get_declarations provides interfaces in
      (* check to see if there are conflicting provided declarations
         (declarations that have same name but different types) *)
      let rec check_same_types decs =
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
            | FunDecl _, VarDecl _ | VarDecl _, FunDecl _ -> false)
      in
      if not (check_same_types provints_declarations) then
        raise_semantic_error c.annot
          "Conflicts in definitions of provided interfaces";

      (* remove duplicates (if there are two or more interfaces
         that provide the same member) *)
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
      (* get used interfaces declarations *)
      let usesints_declarations = get_declarations uses interfaces in

      (* function used to check if there are members with same name in
         used interfaces *)
      let rec check_ambiguities l =
        match l with
        | [ _ ] | [] -> true
        | x :: y :: xs -> (
            match (x.node, y.node) with
            | FunDecl fd, FunDecl fd' ->
                if equal_identifier fd.fname fd'.fname then false
                else check_ambiguities (y :: xs)
            | VarDecl (i, _), VarDecl (i', _) ->
                if equal_identifier i i' then false
                else check_ambiguities (y :: xs)
            | FunDecl _, VarDecl _ | VarDecl _, FunDecl _ -> false)
      in

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
      List.iter
        (fun m ->
          match m.node with
          (* add entries to scope *)
          | FunDecl f -> (
              try
                add_entry f.fname
                  (TFun (List.map (fun (_, t) -> t) f.formals, f.rtype))
                  cscope
                |> ignore
              with DuplicateEntry _ ->
                raise_semantic_error m.annot
                  ("Function " ^ show_identifier f.fname ^ " already defined"))
          | VarDecl (i, t) -> (
              try add_entry i t cscope |> ignore
              with DuplicateEntry _ ->
                raise_semantic_error m.annot
                  ("Variable " ^ show_identifier i ^ " already defined")))
        definitions;

      (* check types of each member definition *)
      let definitions =
        List.map (fun m -> check_member_def m cname cscope) definitions
      in
      end_block cscope |> ignore;

      let check_fun_signature y fd ftyp =
        match y.node with
        | FunDecl fd' ->
            if equal_identifier fd.fname fd'.fname then
              if equal_typ ftyp y.annot then true
              else
                raise_semantic_error c.annot
                  ("Function " ^ show_identifier fd.fname
                 ^ " has not the same signature of the one(s) defined in the \
                    corresponding interface(s)")
            else false
        | _ -> false
      in
      let check_var y name vtyp =
        match y.node with
        | VarDecl (i', _) ->
            if equal_identifier name i' then
              if equal_typ vtyp y.annot then true
              else
                raise_semantic_error c.annot
                  ("Variable " ^ show_identifier name
                 ^ " has not the same signature of the one(s) defined in the \
                    corresponding interface(s")
            else false
        | _ -> false
      in
      let check_provided def =
        match def.node with
        | FunDecl fd -> (
            try
              List.find
                (fun y -> check_fun_signature y fd def.annot)
                definitions
              |> ignore
            with Not_found ->
              raise_semantic_error c.annot
                ("Function " ^ show_identifier fd.fname ^ " not defined"))
        | VarDecl (i, _) -> (
            try
              List.find (fun y -> check_var y i def.annot) definitions |> ignore
            with Not_found ->
              raise_semantic_error c.annot
                ("Variable " ^ show_identifier i ^ " not defined"))
      in
      (* check that all provided definitions are implemented *)
      List.iter (fun x -> check_provided x) provints_declarations;

      (* return typed ComponentDecl *)
      let t_c =
        ComponentDecl { cname; uses; provides; definitions }
        <@> TComponent cname
      in

      dbg_typ (show_component_decl pp_typ t_c) c.annot;
      t_c

(* used to check that exists only one component that provides
   App interface *)
and app_provided = ref false

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

  (* adding the components into global scope *)
  List.iter
    (fun x ->
      match x.node with
      | ComponentDecl c -> (
          try add_entry c.cname (TComponent c.cname) scope |> ignore
          with DuplicateEntry _ ->
            raise_semantic_error x.annot
              ("Component " ^ show_identifier c.cname ^ " already defined")))
    comps;

  (* check component definitions *)
  let components =
    List.map (fun cmp -> check_component_def cmp interfaces scope) comps
  in

  (* check that in links we have interfaces and components that are defined and
     that are at the right place *)
  check_links conns scope;

  (* at least one component has to provide App *)
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

  (* add Prelude definitions *)
  let p = begin_block global_scope in
  List.iter
    (fun (i, t) ->
      add_entry (String.sub i 10 (String.length i - 10)) t p |> ignore)
    prelude_signature;
  end_block p |> ignore;
  Hashtbl.add ints_scopes "Prelude" p;
  logger#info "Added Prelude definitions into Prelude scope";

  (* add App definitions *)
  let a = begin_block global_scope |> of_alist app_signature in
  end_block a |> ignore;
  Hashtbl.add ints_scopes "App" a;
  logger#info "Added App definitions into global scope";

  (* start checks *)
  check_top_decls decls.interfaces decls.components decls.connections
    global_scope
