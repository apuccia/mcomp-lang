/**
 mComp parser specification 
 */
%{ 
  open Ast
  open Location
  open Easy_logging

  exception Camelcase_error of string

  type 'a program_element = 
  | I of 'a interface_decl
  | Comp of 'a component_decl
  | Conns of connection list

  let (<@>) n f = {node = n; annot = f}
  
  let logger = 
    let file_h = Handlers.File("Parser", Logging.Debug) in 
      let cli_h = Handlers.Cli Logging.Debug in
        Logging.make_logger "Parser" Logging.Debug [cli_h; file_h]

  let is_upper c =
    match c with 
    | 'A' .. 'Z' -> true 
    | _ -> false

  let notation_error spos epos msg =
    let pos = to_code_position(spos, epos) in 
      raise (
        Camelcase_error (
          "\n*** Error at line " ^ (Int.to_string pos.start_line) ^
          " (" ^ (Int.to_string pos.start_column) ^ ":" ^ 
          (Int.to_string pos.end_column) ^ ").\n*** " ^ msg))

  let dbg_pos msg pos =  
    logger#debug "\n%s at lines %d:%d, columns %d:%d" msg
      pos.start_line pos.end_line pos.start_column pos.end_column

  let () =
    Printexc.register_printer
      (function
        | Camelcase_error msg -> Some (Printf.sprintf "%s" msg)
        | _ -> None (* for other exceptions *)
      )
%} 

/* Token declarations */

/* Identifier token */
%token <string> ID 

/* Keywords tokens */
%token VAR "var"
%token IF "if"
%token RETURN "return"
%token ELSE "else"
%token WHILE "while"
%token INT "int"
%token CHAR "char"
%token VOID "void"
%token BOOL "bool"
%token INTERFACE "interface"
%token USES "uses"
%token PROVIDES "provides"
%token COMPONENT "component"
%token CONNECT "connect"
%token DEF "def"
%token FOR "for"
%token DO "do"

%token <int32> T_INT // integers are 32bit values
%token <float> T_FLOAT
%token <char> T_CHAR
%token <bool> T_BOOL

/* Operators tokens */
%token REF "&"
%token PLUS "+"
%token MINUS "-"
%token TIMES "*"
%token DIV "/"
%token MOD "%"
%token ASSIGN "="
%token EQUAL "=="
%token NEQ "!="
%token LESS "<"
%token LEQ "<="
%token GREATER ">"
%token GEQ ">="
%token AND "&&"
%token OR "||"
%token NEG "!"

/* Other tokens */
%token LRBRACK "("
%token RRBRACK ")"
%token LCBRACK "{"
%token RCBRACK "}"
%token LSBRACK "["
%token RSBRACK "]"
%token DOT "."
%token COMMA ","
%token SEMICOLON ";"
%token CONN "<-"
%token TYPESIG ":"
%token EOF

/* Precedence and associativity specification */
%nonassoc then_prec
%nonassoc "else"
%right "="
%left "||"
%left "&&"
%left "==", "!=" 
%nonassoc ">", "<", ">=", "<="
%left "+", "-"
%left "*", "/", "%" 
%nonassoc "!"

/* Start symbol */
%start compilation_unit
%type <located_compilation_unit> compilation_unit 

%% 


/* Grammar Specification */

compilation_unit:
| t_decls = top_declaration* EOF  
  { 
    logger#info "Reducing: top_declaration* EOF -> compilation_unit";
    let interfaces = List.fold_left 
			(fun l x -> match x with I(y) -> y::l | _ -> l ) [] t_decls in 
    let components = List.fold_left 
			(fun l x -> match x with Comp(y) -> y::l | _ -> l) [] t_decls in 
    let connections = List.fold_left 
			(fun l x -> match x with Conns(y) -> y@l | _ -> l) [] t_decls in 
    
      logger#debug "Number of interfaces: %d" (List.length interfaces);
      logger#debug "Number of components: %d" (List.length components);
      logger#debug "Number of connections: %d" (List.length connections);

    CompilationUnit {
      interfaces = interfaces;
      components = components;
      connections = connections;
    } 
  }   
;

top_declaration:
| "interface" 
  i_name = ID 
  "{" i_m_decls = i_member_declaration+ "}"
  { 
    if is_upper i_name.[0] then (
      logger#info 
        "Reducing: interface %s { i_member_declaration+ } \
        -> top_declaration" i_name;

      logger#debug 
        "Interface %s, number of member declarations %d"
        i_name (List.length i_m_decls);

      let pos = to_code_position($startpos, $endpos) in
        let i = InterfaceDecl { 
            iname = i_name; 
            declarations = i_m_decls
          } in 
            dbg_pos (show_interface_decl_node pp_code_pos i) pos;
            I(i <@> pos)
    )
    else (
      logger#error 
        "Interface %s does not start with a capital letter" i_name;
      notation_error $startpos(i_name) $endpos(i_name)
        "Interfaces must start with a capital letter" 
    )
	}
| "component" 
  c_name = ID 
  p = provide_clause?
  u = use_clause?
  "{" defs = c_member_declaration+ "}"
  { 
    if is_upper c_name.[0] then (
      logger#info 
        "Reducing: component %s provide_clause? use_clause? \
        { c_member_declaration+ }\ -> top_declaration" c_name;

      let provides = Option.value p ~default:[] in 
      let uses = Option.value u ~default:[] in
      let pos = to_code_position($startpos, $endpos) in 
        logger#debug 
          "Component %s, number of provided interfaces: %d" 
          c_name (List.length provides);
        logger#debug 
          "Component %s, number of used interfaces: %d" 
          c_name (List.length uses);
        logger#debug
          "Component %s, number of member declarations: %d" 
          c_name (List.length defs);

      let c = ComponentDecl {
        cname = c_name; 
        provides = provides; 
        uses = uses; 
        definitions = defs 
      } in
        dbg_pos (show_component_decl_node pp_code_pos c) pos;
        Comp(c <@> pos) 
    )
    else (
      logger#error 
        "Component %s does not start with a capital letter" c_name;
      notation_error $startpos(c_name) $endpos(c_name) 
        "Components must start with a capital letter" 
    )
	}
| "connect" l = link
  { 
    logger#info "Reducing: connect link; -> top_declaration";
    logger#debug "Number of links: 1";
    
    Conns([l]) 
  } 
| "connect" 
  "{" l_list = list(link) "}"
  { 
    logger#info 
      "Reducing: connect { (link ;)* } -> top_declaration";
    logger#debug "Number of links: %d" (List.length l_list);

    Conns(l_list)
  }
;

link:
| c1 = ID "." c1_use = ID "<-" c2 = ID "." c2_provide = ID ";"
  { 
    let pos = to_code_position($startpos, $endpos) in 
      if is_upper c1.[0] then 
        if is_upper c2.[0] then 
          if is_upper c1_use.[0] then 
            if is_upper c2_provide.[0] then (
              logger#info 
                "Reducing: %s.%s <- %s.%s -> link" c1 c1_use c2 c2_provide;

              let l = Link(c1, c1_use, c2, c2_provide) in 
                dbg_pos (show_connection l) pos;
                l;
            )
            else (
              logger#error 
                "Interface %s does not start with a capital letter" c2_provide;
              notation_error $startpos(c2_provide) $endpos(c2_provide)
                "Interfaces must start with a capital letter" 
            )
          else (
            logger#error 
              "Interface %s does not start with a capital letter" c1_use;
            notation_error $startpos(c1_use) $endpos(c1_use)
              "Interfaces must start with a capital letter" 
          )
        else (
          logger#error 
            "Interface %s does not start with a capital letter" c2;
          notation_error $startpos(c2) $endpos(c2)
            "Components must start with a capital letter" 
        )
      else (
        logger#error 
          "Interface %s does not start with a capital letter" c1;
        notation_error $startpos(c1) $endpos(c1)
          "Components must start with a capital letter" 
      )
  }
;

i_member_declaration:
| "var" vs = var_sign ";"
  { 
    logger#info "Reducing: var var_sign; -> i_member_declaration";

    let pos = to_code_position($startpos, $endpos) in 
      let vd = VarDecl(vs) in 
        dbg_pos (show_member_decl_node pp_code_pos vd) pos;
        vd <@> pos;
  }

| fp = fun_prototype ";"
  { 
    logger#info "Reducing: fun_prototype; -> i_member_declaration";

    let pos = to_code_position($startpos, $endpos) in 
      let fd = FunDecl(fp) in 
        dbg_pos (show_member_decl_node pp_code_pos fd) pos;
        fd <@> pos
  }
;

provide_clause:
| "provides" p_l = separated_nonempty_list(",", ID)
  { 
    logger#info "Reducing: provides (ID ,)*";

    p_l 
  }
;

use_clause:
| "uses" u_l = separated_nonempty_list(",", ID)
  { 
    logger#info "Reducing: uses (ID ,)*";

    u_l 
  }
;

var_sign:
| id = ID ":" t = type_
  { 
    if Bool.not (is_upper id.[0]) then (
      logger#info "Reducing: %s : %s -> var_sign" id (show_typ t);

      let pos = to_code_position($startpos, $endpos) in 
        let vd = id, t in 
          dbg_pos (show_vdecl vd) pos;
          vd 
    )
    else (
      logger#error 
        "Variable %s does not start with a lowercase letter" id;
      notation_error $startpos(id) $endpos(id)
        "Variable names must start with lowercase letter" 
    )
  }
;

fun_prototype:
| "def" 
  id = ID 
  "(" p = separated_list(",", var_sign) ")"
  rt = preceded(":", basic_type)?
  { 
    if Bool.not (is_upper id.[0]) then (
      logger#info 
        "Reducing: def %s ((var_sign ,)* var_sign)? (: basic_type)? \
        -> fun_prototype" id;
      
      let pos = to_code_position($startpos, $endpos) in 
        let fd = {
          rtype = Option.value rt ~default:TVoid;
          fname = id;
          formals = p;
          body = None
        } in
          dbg_pos (show_fun_decl pp_code_pos fd) pos;
          fd
    )
    else (
      logger#error 
        "Function %s does not start with a lowercase letter" id;
      notation_error $startpos(id) $endpos(id)
        "Function names must start with lowercase letter"
    )
	}
;

c_member_declaration:
| "var" vd = var_sign ";"
  { 
    logger#info 
      "Reducing: var var_sign; -> c_member_declaration";

    let pos = to_code_position($startpos, $endpos) in 
      let vd' = VarDecl(vd) in
        dbg_pos (show_member_decl_node pp_code_pos vd') pos;
        vd' <@> pos
  }
| fd = fun_declaration
  { 
    logger#info "Reducing: fun_declaration -> c_member_declaration";

    let pos = to_code_position($startpos, $endpos) in 
      let fd'  = FunDecl(fd) in 
        dbg_pos (show_member_decl_node pp_code_pos fd') pos;
        fd' <@> pos
  }
;

fun_declaration:
| fp = fun_prototype b = block
  { 
    logger#info "Reducing: fun_prototype block -> fun_declaration";

    let pos = to_code_position($startpos, $endpos) in 
      let fp' = {
        rtype = fp.rtype;
        fname = fp.fname;
        formals = fp.formals;
        body = Some b 
      } in 
        dbg_pos (show_fun_decl pp_code_pos fp') pos;
        fp'
	}
;

// inlining because block could be considered as an alias of delimited
%inline block:
| c = delimited("{", block_content*, "}")
  { 
    logger#info 
      "Reducing: { block_content* } -> block";

    let pos = to_code_position($startpos, $endpos) in 
      let b = Block(c) in 
        dbg_pos (show_stmt_node pp_code_pos b) pos;
        b <@> pos
  }
;

block_content:
| s = stmt
  { 
    logger#info "Reducing: stmt -> block_content";

    let pos = to_code_position($startpos, $endpos) in 
      let st = Stmt(s) in 
        dbg_pos (show_stmtordec_node pp_code_pos st) pos;
        st <@> pos
      
  }
| "var" ld = var_sign ";"
  { 
    logger#info "Reducing: var var_sign; -> block_content";

    let pos = to_code_position($startpos, $endpos) in
      let ld = LocalDecl(ld) in 
        dbg_pos (show_stmtordec_node pp_code_pos ld) pos;
        ld <@> pos
  }
;

type_:
| bt = basic_type
  { 
    logger#info "Reducing: basic_type -> type_";
    bt 
  }
/* t = type_ "[" "]", following the grammar provided
this would allow the possibility do declare multidimensional arrays. */
| t = no_multidim "[" "]"
  { 
    logger#info "Reducing: no_multidim [] -> type_";
    let pos = to_code_position($startpos, $endpos) in 
      let a = TArray(t, None) in 
        dbg_pos (show_typ a) pos;
        a 
  }
// t = type_ s = delimited("[", T_INT, "]")
| t = no_multidim s = delimited("[", T_INT, "]")
  { 
    logger#info 
      "Reducing: no_multidim [T_INT] -> type_";
    let pos = to_code_position($startpos, $endpos) in 
      let a = TArray(t, Some (Int32.to_int s)) in 
        dbg_pos (show_typ a) pos;
        a
  }
| "&" t = basic_type
  { 
    logger#info "Reducing: &basic_type -> type_";
    let pos = to_code_position($startpos, $endpos) in 
      let r = TRef(t) in 
        dbg_pos (show_typ r) pos;
        r
  }
;

no_multidim:
// array
| bt = basic_type
  { 
    logger#info "Reducing: basic_type -> no_multidim";
    bt 
  }
// reference to array
| "&" t = basic_type
  { 
    logger#info "Reducing: &basic_type -> no_multidim";
    let pos = to_code_position($startpos, $endpos) in 
      let r = TRef(t) in 
        dbg_pos (show_typ r) pos;
        r 
  }
; 

basic_type:
| "int"
  { 
    logger#info "Reducing: int -> basic_type";
    let pos = to_code_position($startpos, $endpos) in
      let i = TInt in
        dbg_pos (show_typ i) pos;
        i
  }
| "float"
  { 
    logger#info "Reducing: float -> basic_type";
    let pos = to_code_position($startpos, $endpos) in
      let i = TFloat in
        dbg_pos (show_typ i) pos;
        i
  }
| "char"
  { 
    logger#info "Reducing: char -> basic_type";
    let pos = to_code_position($startpos, $endpos) in
      let c = TChar in
        dbg_pos (show_typ c) pos;
        c
  }
| "void"
  { 
    logger#info "Reducing: void -> basic_type";
    let pos = to_code_position($startpos, $endpos) in
      let v = TVoid in
        dbg_pos (show_typ v) pos;
        v
  }
| "bool"
  { 
    logger#info "Reducing: bool -> basic_type";
    let pos = to_code_position($startpos, $endpos) in
      let b = TBool in
        dbg_pos (show_typ b) pos;
        b 
  }
;

stmt:
| r = delimited("return", expr?, ";")
  { 
    logger#info 
      "Reducing: return expr?; -> stmt";

    let pos = to_code_position($startpos, $endpos) in 
      let r' = Return(r) in 
        dbg_pos (show_stmt_node pp_code_pos r') pos;
        r' <@> pos 
  }
| e = expr? ";"
  { 
    logger#info "Reducing: expr?; -> stmt";

    let pos = to_code_position($startpos, $endpos) in 
      let e' = 
      (Option.value (Option.map (fun x -> Expr(x)) e) ~default:(Skip)) in
        dbg_pos (show_stmt_node pp_code_pos e') pos;
        e' <@> pos
  }
| b = block
  { 
    logger#info "Reducing: block -> stmt";

    b 
  }
| "while" cond = delimited("(", expr, ")") b = stmt 
  { 
    logger#info "Reducing: while (expr) stmt -> stmt";

    let pos = to_code_position($startpos, $endpos) in 
      let w = While(cond, b) in
        dbg_pos (show_stmt_node pp_code_pos w) pos;
        w <@> pos
  }
| "if" cond = delimited("(", expr, ")") a = stmt "else" b = stmt 
  { 
    logger#info "Reducing: if (expr) stmt else stmt -> stmt";

    let pos = to_code_position($startpos, $endpos) in 
      let if_ = If(cond, a, b) in 
        dbg_pos (show_stmt_node pp_code_pos if_) pos;
        if_ <@> pos
  }
| "if" cond = delimited("(", expr, ")") a = stmt %prec then_prec
  { 
    logger#info "Reducing: if (expr) stmt -> stmt";

    let pos = to_code_position($startpos, $endpos) in 
      let if_ = If(cond, a, Skip <@> pos) in
        dbg_pos (show_stmt_node pp_code_pos if_) pos;
        if_ <@> pos
	}
| "for" "(" init = expr? ";" cond = expr? ";" step = expr? ")" body = stmt
  { 
    logger#info "Reducing: for (expr?; expr?; expr?) stmt -> stmt";

  	(* creating the statement for counter variable initialization *)
    let stmt_i = 
			Stmt((Option.value (Option.map (fun x -> Expr(x)) init) ~default:(Skip))
    					<@> 
      			to_code_position($startpos(init), $endpos(init))) 
				<@> to_code_position($startpos(init), $endpos(init)) in 
    (* creating condition expression *)
    let expr_c = 
      Option.value cond ~default:(BLiteral(true) 
				<@> 
			to_code_position($startpos(cond), $endpos(cond))) in
    (* creating the statement for counter modification *)
    let stmt_s = 
			Stmt((Option.value (Option.map (fun x -> Expr(x)) step) ~default:(Skip))
        			<@> 
      			to_code_position($startpos(step), $endpos(step))) 
				<@> to_code_position($startpos(step), $endpos(step)) in
		(* creating the statement for body *)
    let stmt_b = 
      Stmt(body) <@> to_code_position($startpos(body), $endpos(body)) in
    (* creating while *)
    let stmt_w = 
			Stmt(While(
							expr_c, 
							(* block of body stmt followed by counter modification *)
							Block([stmt_b; stmt_s]) <@> to_code_position($startpos, $endpos)) 
					<@> to_code_position($startpos, $endpos)) 
				<@> to_code_position($startpos, $endpos) in
    (* creating final block composed of initialization and while *)
    let pos = to_code_position($startpos, $endpos) in
      let b = Block[stmt_i; stmt_w] in 
        dbg_pos (show_stmt_node pp_code_pos b) pos;
        b <@> pos
  }
| "do" body = stmt "while" "(" cond = expr ")" ";"
  {
    logger#info "Reducing: do stmt while (expr) -> stmt";

    let pos = to_code_position($startpos, $endpos) in 
      let dow = DoWhile(body, cond) in
        dbg_pos (show_stmt_node pp_code_pos dow) pos;
        dow <@> pos
  }
;

expr:
| i = T_INT
  { 
    logger#info "Reducing: T_INT -> expr";

    let pos = to_code_position($startpos, $endpos) in 
      let il = ILiteral(Int32.to_int i) in
        dbg_pos (show_expr_node pp_code_pos il) pos;
        il <@> pos 
  }
| i = T_FLOAT
  { 
    logger#info "Reducing: T_FLOAT -> expr";

    let pos = to_code_position($startpos, $endpos) in 
      let fl = FLiteral(Int32.to_int i) in
        dbg_pos (show_expr_node pp_code_pos il) pos;
        il <@> pos 
  }
| c = T_CHAR
  { 
    logger#info "Reducing: T_CHAR -> expr";

    let pos = to_code_position($startpos, $endpos) in 
      let cl = CLiteral(c) in
        dbg_pos (show_expr_node pp_code_pos cl) pos;
        cl <@> pos
  }
| b = T_BOOL
  { 
    logger#info "Reducing: T_BOOL -> expr";

    let pos = to_code_position($startpos, $endpos) in 
      let bl = BLiteral(b) in
        dbg_pos (show_expr_node pp_code_pos bl) pos;
        bl <@> pos
  }
| e = delimited("(", expr, ")")
  { 
    logger#info "Reducing: (expr) -> expr";
    e 
  }
| "&" addr = l_value
  { 
    logger#info "Reducing: &l_value -> expr";

    let pos = to_code_position($startpos, $endpos) in 
      let a = Address(addr) in
        dbg_pos (show_expr_node pp_code_pos a) pos;
        a <@> pos
  }
| l = l_value "=" e = expr
  { 
    logger#info "Reducing: l_value = expr -> expr";

    let pos = to_code_position($startpos, $endpos) in 
      let a = Assign(l, e) in
        dbg_pos (show_expr_node pp_code_pos a) pos;
        a <@> pos 
  }
| "!" e = expr
  { 
    logger#info "Reducing: !expr -> expr";

    let pos = to_code_position($startpos, $endpos) in 
      let uo = UnaryOp(Not, e) in 
        dbg_pos (show_expr_node pp_code_pos uo) pos;
        uo <@> pos 
  }
| fname = ID "(" args = separated_list(",", expr) ")"
  { 
    logger#info "Reducing: ID(expr, ..., expr) -> expr";

    if Bool.not (is_upper fname.[0]) then (
      let pos = to_code_position($startpos, $endpos) in 
        let c = Call(None, fname, args) in 
          dbg_pos (show_expr_node pp_code_pos c) pos;
          c <@> pos 
    )
    else (
      logger#error 
        "Function %s does not start with a capital letter" fname;
      notation_error $startpos(fname) $endpos(fname)
        "Function names must start with lowercase letter"
    )
  }
| l = l_value
  { 
    logger#info "Reducing: l_value -> expr";

    let pos = to_code_position($startpos, $endpos) in 
      let lv = LV(l) in
        dbg_pos (show_expr_node pp_code_pos lv) pos;
        lv <@> pos
  }
| "-" e = expr
  { 
    logger#info "Reducing: -expr -> expr";

    let pos = to_code_position($startpos, $endpos) in 
      let uo = UnaryOp(Neg, e) in
        dbg_pos (show_expr_node pp_code_pos uo) pos;
        uo <@> pos
  }
| e1 = expr b = bin_op e2 = expr
  { 
    logger#info "Reducing: expr bin_op expr -> expr";

    let pos = to_code_position($startpos, $endpos) in 
      let bo = BinaryOp(b, e1, e2) in
        dbg_pos (show_expr_node pp_code_pos bo) pos;
        bo <@> pos
  }
;

l_value:
| id = ID 
  { 
    logger#info "Reducing: ID -> l_value";

    if Bool.not (is_upper id.[0]) then (
      let pos = to_code_position($startpos, $endpos) in 
        let av = AccVar(None, id) in
          dbg_pos (show_lvalue_node pp_code_pos av) pos;
          av <@> pos 
    )
    else (
      logger#error 
        "Variable %s does not start with a capital letter" id;
      notation_error $startpos $endpos
        "Variable names must start with lowercase letter"
    )
  }
| id = ID "[" e = expr "]"
  {  
    logger#info "Reducing: ID[expr] -> l_value";

    if Bool.not (is_upper id.[0]) then (
      let pos = to_code_position($startpos, $endpos) in 
        let ai = 
          AccIndex
            (AccVar(None, id) <@> to_code_position($startpos, $endpos), e) in
          dbg_pos (show_lvalue_node pp_code_pos ai) pos;
          ai <@> pos
    )
    else (
      logger#error 
        "Variable %s does not start with a capital letter" id;
      notation_error $startpos(id) $endpos(id)
        "Variable names must start with lowercase letter"
    )
	}

%inline bin_op:
| "+"
  { 
    logger#info "Reducing + -> bin_op";
    Add 
  }
| "-"
  { 
    logger#info "Reducing - -> bin_op";
    Sub 
  }
| "*"
  { 
    logger#info "Reducing * -> bin_op";
    Mult 
  }
| "%"
  { 
    logger#info "Reducing %% -> bin_op";
    Mod 
  }  
| "/"
  { 
    logger#info "Reducing / -> bin_op";
    Div 
  }
| "&&"
  { 
    logger#info "Reducing && -> bin_op";
    And 
  }
| "||"
  { 
    logger#info "Reducing || -> bin_op";
    Or 
  }
| "<"
  { 
    logger#info "Reducing < -> bin_op";
    Less 
  }
| ">"
	{ 
    logger#info "Reducing > -> bin_op";
    Greater 
  }
| "<="
  { 
    logger#info "Reducing <= -> bin_op";
    Leq 
  }
| ">="
  { 
    logger#info "Reducing >= -> bin_op";
    Geq 
  }
| "=="
  { 
    logger#info "Reducing == -> bin_op";
    Equal 
  }
| "!="
  { 
    logger#info "Reducing != -> bin_op";
    Neq 
  }
;