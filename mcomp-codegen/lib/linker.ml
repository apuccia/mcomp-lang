open Ast
open Easy_logging
open Symbol_table

exception LinkingError of string

let ( <@> ) n f = { node = n; annot = f }

let logger =
  let file_h = Handlers.File ("Linker", Logging.Debug) in
  let cli_h = Handlers.Cli Logging.Debug in
  Logging.make_logger "Linker" Logging.Debug [ cli_h; file_h ]

let dbg_link msg = logger#debug "\n%s" msg

let raise_linking_error msg =
  logger#error "Error: %s" msg;
  raise (LinkingError msg)

let linked_interfaces = Hashtbl.create 0
let comps_globals = Hashtbl.create 0

let check_connection connection components =
  match connection with
  | Link (c1, used, c2, provided) ->
      (if equal_identifier c1 c2 then
         raise_linking_error
           ("Trying to link component " ^ show_identifier c1 ^ " with itself");
       if not (equal_identifier used provided) then
         raise_linking_error
           ("Trying to link using two different interfaces: "
          ^ show_identifier used ^ " and " ^ show_identifier provided);
       if equal_identifier used "App" || equal_identifier provided "App" then
         raise_linking_error "Interface App can't be linked";
       if equal_identifier used "Prelude" || equal_identifier provided "Prelude"
       then raise_linking_error "Interface Prelude can't be linked";

       try
         let c = Hashtbl.find linked_interfaces c1 in
         try
           let _ = Hashtbl.find c used in
           raise_linking_error "Trying to overwrite a connection"
         with Not_found -> Hashtbl.add c used c2
       with Not_found ->
         let c = Hashtbl.create 0 in
         Hashtbl.add c used c2;
         Hashtbl.add linked_interfaces c1 c);

      List.iter
        (fun x ->
          match x.node with
          | ComponentDecl cd ->
              if equal_identifier c1 cd.cname && not (List.mem used cd.uses)
              then
                raise_linking_error
                  ("Interface " ^ used ^ " is not used by component " ^ c1)
              else if
                equal_identifier c2 cd.cname
                && not (List.mem provided cd.provides)
              then
                raise_linking_error
                  ("Interface " ^ provided ^ " is not provided by component "
                 ^ c2))
        components

let check_used_interfaces component connections =
  match component.node with
  | ComponentDecl cd ->
      let filtered_connections =
        List.filter
          (fun y ->
            match y with Link (a, _, _, _) -> equal_identifier a cd.cname)
          connections
      in
      (* -1 because there is also interface Prelude *)
      if List.length filtered_connections != List.length cd.uses - 1 then
        raise_linking_error
          ("Not all used interface are linked for component "
         ^ show_identifier cd.cname)

let rec qualify_component component =
  match component.node with
  | ComponentDecl cd ->
      let comp =
        ComponentDecl
          {
            cname = cd.cname;
            uses = cd.uses;
            provides = cd.provides;
            definitions =
              List.map (fun x -> qualify_definition x cd.cname) cd.definitions;
          }
        <@> component.annot
      in
      let pr =
        List.filter
          (fun x -> match x.node with VarDecl _ -> true | _ -> false)
          cd.definitions
      in
      let globals = List.map (fun x -> x.node) pr in
      Hashtbl.add comps_globals cd.cname globals;
      dbg_link (show_component_decl pp_typ comp);
      comp

and qualify_lv lv cname scope =
  match lv.node with
  | AccVar (id1, id2) ->
      let av =
        if Option.is_some id1 then
          let h = Hashtbl.find linked_interfaces cname in
          let q = Hashtbl.find h (Option.get id1) in
          AccVar (Some q, id2) <@> lv.annot
        else
          try
            let _ = lookup id2 scope in
            AccVar (None, id2) <@> lv.annot
          with NotFoundEntry _ -> AccVar (Some cname, id2) <@> lv.annot
      in

      dbg_link (show_lvalue pp_typ av);
      av
  | AccIndex (lv', e) ->
      let ai =
        AccIndex (qualify_lv lv' cname scope, qualify_expr e cname scope)
        <@> lv.annot
      in
      dbg_link (show_lvalue pp_typ ai);
      ai

and qualify_expr e cname scope =
  match e.node with
  | LV lv ->
      let lv' = LV (qualify_lv lv cname scope) <@> e.annot in
      dbg_link (show_expr pp_typ lv');
      lv'
  | Assign (lv, e) ->
      let a =
        Assign (qualify_lv lv cname scope, qualify_expr e cname scope)
        <@> e.annot
      in
      dbg_link (show_expr pp_typ a);
      a
  | ILiteral _ | CLiteral _ | BLiteral _ -> e
  | UnaryOp (op, e) ->
      let uo = UnaryOp (op, qualify_expr e cname scope) <@> e.annot in
      dbg_link (show_expr pp_typ uo);
      uo
  | Address lv ->
      let a = Address (qualify_lv lv cname scope) <@> e.annot in
      dbg_link (show_expr pp_typ a);
      a
  | BinaryOp (op, e1, e2) ->
      let bo =
        BinaryOp (op, qualify_expr e1 cname scope, qualify_expr e2 cname scope)
        <@> e.annot
      in
      dbg_link (show_expr pp_typ bo);
      bo
  | Call (id1, id2, el) ->
      let c =
        if Option.is_some id1 then
          let id1 = Option.get id1 in
          if not (equal_identifier id1 "Prelude") then
            let h = Hashtbl.find linked_interfaces cname in
            let q = Hashtbl.find h id1 in
            Call (Some q, id2, List.map (fun x -> qualify_expr x cname scope) el)
            <@> e.annot
          else
            Call
              (Some id1, id2, List.map (fun x -> qualify_expr x cname scope) el)
            <@> e.annot
        else
          Call (id1, id2, List.map (fun x -> qualify_expr x cname scope) el)
          <@> e.annot
      in

      dbg_link (show_expr pp_typ c);
      c

and qualify_stmt body cname scope =
  match body.node with
  | If (e, s1, s2) ->
      let i =
        If
          ( qualify_expr e cname scope,
            qualify_stmt s1 cname scope,
            qualify_stmt s2 cname scope )
        <@> body.annot
      in

      dbg_link (show_stmt pp_typ i);
      i
  | While (e, s) ->
      let w =
        While (qualify_expr e cname scope, qualify_stmt s cname scope)
        <@> body.annot
      in

      dbg_link (show_stmt pp_typ w);
      w
  | Expr e ->
      let e' = Expr (qualify_expr e cname scope) <@> body.annot in

      dbg_link (show_stmt pp_typ e');
      e'
  | Return e ->
      let r =
        if Option.is_some e then
          Return (Some (qualify_expr (Option.get e) cname scope)) <@> body.annot
        else Return e <@> body.annot
      in

      dbg_link (show_stmt pp_typ r);
      r
  | Block sl ->
      let bscope = begin_block scope in
      let b =
        Block (List.map (fun x -> qualify_stmt_ordec x cname bscope) sl)
        <@> body.annot
      in

      dbg_link (show_stmt pp_typ b);
      b
  | Skip -> body

and qualify_stmt_ordec stmt cname scope =
  match stmt.node with
  | LocalDecl (i, t) ->
      add_entry i t scope |> ignore;
      stmt
  | Stmt s ->
      let s' = Stmt (qualify_stmt s cname scope) <@> stmt.annot in

      dbg_link (show_stmtordec pp_typ s');
      s'

and qualify_definition definition cname =
  match definition.node with
  | FunDecl fd ->
      let fscope = empty_table () |> begin_block in
      List.iter
        (fun x -> match x with i, t -> add_entry i t fscope |> ignore)
        fd.formals;
      let fd' =
        FunDecl
          {
            rtype = fd.rtype;
            fname = fd.fname;
            formals = fd.formals;
            body = Some (qualify_stmt (Option.get fd.body) cname fscope);
          }
        <@> definition.annot
      in
      end_block fscope |> ignore;
      dbg_link (show_member_decl pp_typ fd');
      fd'
  | _ -> definition

let wire_components (CompilationUnit decls : typ compilation_unit) =
  List.iter (fun x -> check_connection x decls.components) decls.connections;

  List.iter
    (fun x -> check_used_interfaces x decls.connections)
    decls.components;

  let components = List.map qualify_component decls.components in

  CompilationUnit
    {
      interfaces = decls.interfaces;
      components;
      connections = decls.connections;
    }
