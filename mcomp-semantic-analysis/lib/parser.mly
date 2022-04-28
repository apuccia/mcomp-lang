/**
 mComp parser specification 
 */
%{ 
  open Ast
  open Location

  exception Camelcase_error of string

  type 'a program_element = 
  | I of 'a interface_decl
  | Comp of 'a component_decl
  | Conns of connection list

  let (<@>) n f = {node = n; annot = f}

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

%token <int32> T_INT // integers are 32bit values
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
    CompilationUnit {
      interfaces = 
				List.fold_left 
					(fun l x -> match x with I(y) -> y::l | _ -> l ) [] t_decls;
      components = 
				List.fold_left 
					(fun l x -> match x with Comp(y) -> y::l | _ -> l) [] t_decls;
      connections = 
				List.fold_left 
					(fun l x -> match x with Conns(y) -> y@l | _ -> l) [] t_decls
    }
  }   
;

top_declaration:
| "interface" 
  i_name = ID 
  "{" i_m_decls = i_member_declaration+ "}"
  { 
    if is_upper i_name.[0] then
		  I(
        InterfaceDecl { 
          iname = i_name; 
          declarations = i_m_decls
        } <@> to_code_position($startpos, $endpos)) 
    else notation_error $startpos $endpos
      "Interfaces must start with a capital letter"
	}
| "component" 
  c_name = ID 
  p = provide_clause?
  u = use_clause?
  "{" defs = c_member_declaration+ "}"
  { 
    if is_upper c_name.[0] then
      Comp(
        ComponentDecl {
          cname = c_name; 
          provides = Option.value p ~default:[]; 
          uses = Option.value u ~default:[]; 
          definitions = defs } 
        <@>
        to_code_position($startpos, $endpos)) 
    else notation_error $startpos $endpos 
      "Components must start with a capital letter"
	}
| "connect" l = link ";"
  { Conns([l]) } 
| "connect" 
  "{" l_list = separated_list(";", link) "}"
  { Conns(l_list) }
;

link:
| c1 = ID "." c1_use = ID "<-" c2 = ID "." c2_provide = ID
  { 
    if is_upper c1.[1] then 
      if is_upper c2.[1] then 
        if is_upper c1_use.[1] then 
          if is_upper c2_provide.[1] then 
            Link(c1, c1_use, c2, c2_provide) 
          else notation_error $startpos(c2_provide) $endpos(c2_provide)
            "Interfaces must start with a capital letter"
        else notation_error $startpos(c1_use) $endpos(c1_use)
          "Interfaces must start with a capital letter"
      else notation_error $startpos(c2) $endpos(c2)
        "Components must start with a capital letter"
    else notation_error $startpos(c1) $endpos(c1)
      "Components must start with a capital letter"
  }
;

i_member_declaration:
| "var" vs = var_sign ";"
  { VarDecl(vs) <@> to_code_position($startpos, $endpos) }

| fp = fun_prototype ";"
  { FunDecl(fp) <@> to_code_position($startpos, $endpos) }
;

provide_clause:
| "provides" p_l = separated_nonempty_list(",", ID)
  { p_l }
;

use_clause:
| "uses" u_l = separated_nonempty_list(",", ID)
  { u_l }
;

var_sign:
| id = ID ":" t = type_
  { 
    if Bool.not (is_upper id.[0]) then
      id, t 
    else notation_error $startpos(id) $endpos(id)
      "Variable names must start with lowercase letter"
  }
;

fun_prototype:
| "def" 
  id = ID 
  "(" p = separated_list(",", var_sign) ")"
  rt = preceded(":", basic_type)?
  { 
    if Bool.not (is_upper id.[0]) then
      {
        rtype = Option.value rt ~default:TVoid;
        fname = id;
        formals = p;
        body = None
      } 
    else notation_error $startpos(id) $endpos(id)
      "Function names must start with lowercase letter"
	}
;

c_member_declaration:
| "var" vd = var_sign ";"
  { VarDecl(vd) <@> to_code_position($startpos, $endpos) }
| fd = fun_declaration
  { FunDecl(fd) <@> to_code_position($startpos, $endpos) }
;

fun_declaration:
| fp = fun_prototype b = stmt
  { 
		{
      rtype = fp.rtype;
      fname = fp.fname;
      formals = fp.formals;
      body = Some b 
		} 
	}
;

// inlining because block could be considered as an alias of delimited
%inline block:
| c = delimited("{", block_content*, "}")
  { Block(c) <@> to_code_position($startpos, $endpos) }
;

block_content:
| s = stmt
  { Stmt(s) <@> to_code_position($startpos, $endpos) }
| "var" ld = var_sign ";"
  { LocalDecl(ld) <@> to_code_position($startpos, $endpos) }
;

type_:
| bt = basic_type
  { bt }
/* t = type_ "[" "]", following strictly the grammar provided
this would allow the possibility do declare multidimensional arrays. */
| t = no_multidim "[" "]"
  { 
    TArray(t, None) 
  }
// t = type_ s = delimited("[", T_INT, "]")
| t = no_multidim s = delimited("[", T_INT, "]")
  { 
    TArray(t, Some (Int32.to_int s)) 
  }
| "&" t = basic_type
  { TRef(t) }
;

no_multidim:
| bt = basic_type
  { bt }
| "&" t = basic_type
  { TRef(t) }
; 

basic_type:
| "int"
  { TInt }
| "char"
  { TChar }
| "void"
  { TVoid }
| "bool"
  { TBool }
;

stmt:
| r = delimited("return", expr?, ";")
  { Return(r) <@> to_code_position($startpos, $endpos) }
| e = expr? ";"
  { 
    (Option.value (Option.map (fun x -> Expr(x)) e) ~default:(Skip))
      <@> 
    to_code_position($startpos, $endpos)
  }
| b = block
  { b }
| "while" cond = delimited("(", expr, ")") b = stmt 
  { While(cond, b) <@> to_code_position($startpos, $endpos) }
| "if" cond = delimited("(", expr, ")") a = stmt "else" b = stmt 
  { If(cond, a, b) <@> to_code_position($startpos, $endpos) }
| "if" cond = delimited("(", expr, ")") a = stmt %prec then_prec
  { 
		let skip_node = Skip <@> to_code_position($startpos, $endpos) in 
    If(cond, a, skip_node) <@> to_code_position($startpos, $endpos)
	}
| "for" "(" init = expr? ";" cond = expr? ";" step = expr? ")" body = stmt
  { 
  	(* creating the statement for counter variable initialization *)
    let stmt_i = 
			Stmt((Option.value (Option.map (fun x -> Expr(x)) init) ~default:(Skip))
    					<@> 
      			to_code_position($startpos, $endpos)) 
				<@> to_code_position($startpos, $endpos) in 
    (* creating condition expression *)
    let expr_c = 
      Option.value cond ~default:(BLiteral(true) 
				<@> 
			to_code_position($startpos, $endpos)) in
    (* creating the statement for counter modification *)
    let stmt_s = 
			Stmt((Option.value (Option.map (fun x -> Expr(x)) step) ~default:(Skip))
        			<@> 
      			to_code_position($startpos, $endpos)) 
				<@> to_code_position($startpos, $endpos) in
		(* creating the statement for body *)
    let stmt_b = Stmt(body) <@> to_code_position($startpos, $endpos) in
    (* creating while *)
    let stmt_w = 
			Stmt(While(
							expr_c, 
							(* block of body stmt followed by counter modification *)
							Block([stmt_b; stmt_s]) <@> to_code_position($startpos, $endpos)) 
					<@> to_code_position($startpos, $endpos)) 
				<@> to_code_position($startpos, $endpos) in
    (* creating final block composed of initialization and while *)
    Block[stmt_i; stmt_w] <@> to_code_position($startpos, $endpos)
  }
;

expr:
| i = T_INT
  { ILiteral(Int32.to_int i) <@> to_code_position($startpos, $endpos) }
| c = T_CHAR
  { CLiteral(c) <@> to_code_position($startpos, $endpos) }
| b = T_BOOL
  { BLiteral(b) <@> to_code_position($startpos, $endpos) }
| e = delimited("(", expr, ")")
  { e }
| "&" addr = l_value
  { Address(addr) <@> to_code_position($startpos, $endpos) }
| l = l_value "=" e = expr
  { Assign(l, e) <@> to_code_position($startpos, $endpos) }
| "!" e = expr
  { UnaryOp(Not, e) <@> to_code_position($startpos, $endpos) }
| fname = ID "(" args = separated_list(",", expr) ")"
  { 
    if Bool.not (is_upper fname.[0]) then
      Call(None, fname, args) <@> to_code_position($startpos, $endpos) 
    else notation_error $startpos(fname) $endpos(fname)
      "Function names must start with lowercase letter"
  }
| l = l_value
  { LV(l) <@> to_code_position($startpos, $endpos) }
| "-" e = expr
  { UnaryOp(Neg, e) <@> to_code_position($startpos, $endpos) }
| e1 = expr b = bin_op e2 = expr
  { BinaryOp(b, e1, e2) <@> to_code_position($startpos, $endpos) }
;

l_value:
| id = ID 
  { 
    if Bool.not (is_upper id.[0]) then
      AccVar(None, id) <@> to_code_position($startpos, $endpos) 
    else notation_error $startpos $endpos
      "Variable names must start with lowercase letter"
  }
| id = ID "[" e = expr "]"
  { 
    if Bool.not (is_upper id.[0]) then
      AccIndex(AccVar(None, id) <@> to_code_position($startpos, $endpos), e) 
        <@> 
      to_code_position($startpos, $endpos)
    else notation_error $startpos(id) $endpos(id)
      "Variable names must start with lowercase letter"
	}

%inline bin_op:
| "+"
  { Add }
| "-"
  { Sub }
| "*"
  { Mult }
| "%"
  { Mod }
| "/"
  { Div }
| "&&"
  { And }
| "||"
  { Or }
| "<"
  { Less }
| ">"
	{ Greater }
| "<="
  { Leq }
| ">="
  { Geq }
| "=="
  { Equal }
| "!="
  { Neq }
;