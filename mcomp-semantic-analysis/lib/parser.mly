/**
 mComp parser specification 
 */
%{
    (* Here code *)  
    open Ast
    open Location

    type 'a program_element = 
      | I of 'a interface_decl
      | Comp of 'a component_decl
      | Conns of connection list

    let (<@>) n f = {node = n; annot = f}
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
        CompilationUnit{
            interfaces = List.fold_left (fun l x -> match x with I(y) -> y::l | _ -> l ) [] t_decls;
            components = List.fold_left (fun l x -> match x with Comp(y) -> y::l | _ -> l) [] t_decls;
            connections = List.fold_left (fun l x -> match x with Conns(y) -> y@l | _ -> l) [] t_decls
        }
      }   
;

top_declaration:
  | "interface" 
    i_name = ID 
    "{" i_m_decls = i_member_declaration+ "}"
      { I(InterfaceDecl{iname = i_name; declarations = i_m_decls} <@> to_code_position($startpos, $endpos)) }
  | "component" 
    c_name = ID 
    p = provide_clause?
    u = use_clause?
    "{" defs = c_member_declaration+ "}"
      { Comp(ComponentDecl{
                cname = c_name; 
                provides = Option.value p ~default:[]; 
                uses = Option.value u ~default:[]; 
                definitions = defs} 
            <@>
            to_code_position($startpos, $endpos)) }
  | "connect" l = link ";"
      { Conns([l]) } 
  | "connect" 
    "{" l_list = separated_list(";", link) "}"
      { Conns(l_list) }
;

link:
  | c1 = ID "." c1_use = ID "<-" c2 = ID "." c2_provide = ID
      { Link(c1, c1_use, c2, c2_provide) }
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
      { id, t }
;

fun_prototype:
  | "def" 
    id = ID 
    "(" p = separated_list(",", var_sign) ")"
    rt = preceded(":", basic_type)?
      { {
          rtype = Option.value rt ~default:TVoid;
          fname = id;
          formals = p;
          body = None
        } }
;

c_member_declaration:
  | "var" vd = var_sign ";"
      { VarDecl(vd) <@> to_code_position($startpos, $endpos) }
  | fd = fun_declaration
      { FunDecl(fd) <@> to_code_position($startpos, $endpos) }
;

fun_declaration:
  | fp = fun_prototype b = stmt
      { {
          rtype = fp.rtype;
          fname = fp.fname;
          formals = fp.formals;
          body = Some b } }
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
  | t = type_ "[" "]"
      { TArray(t, None) }
  | t = type_ s = delimited("[", T_INT, "]")
      { TArray(t, Some (Int32.to_int s)) }
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
      { let skip_node = Skip <@> to_code_position($startpos, $endpos) in 
        If(cond, a, skip_node) <@> to_code_position($startpos, $endpos)
    }
  | "for" "(" init = expr? ";" cond = expr? ";" step = expr? ")" body = stmt
      { 
        (* creating the statement for counter variable initialization *)
        let i = 
            (Option.value (Option.map (fun x -> Expr(x)) init) ~default:(Skip))
                <@> 
            to_code_position($startpos, $endpos) in
        let stmt_i = Stmt(i) <@> to_code_position($startpos, $endpos) in
        (* creating condition expression *)
        let c_expr = 
            Option.value cond ~default:(BLiteral(true) <@> to_code_position($startpos, $endpos)) in
        (* creating the statement for counter modification *)
        let s = 
            (Option.value (Option.map (fun x -> Expr(x)) step) ~default:(Skip))
                <@> 
            to_code_position($startpos, $endpos) in
        let stmt_s = Stmt(s) <@> to_code_position($startpos, $endpos) in
        (* creating while *)
        let stmt_b = Stmt(body) <@> to_code_position($startpos, $endpos) in
        let w_block = Block([stmt_b; stmt_s]) <@> to_code_position($startpos, $endpos) in
        let w = While(c_expr, w_block) <@> to_code_position($startpos, $endpos) in
        let stmt_w = Stmt(w) <@> to_code_position($startpos, $endpos) in
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
      { Call(None, fname, args) <@> to_code_position($startpos, $endpos) }
  | l = l_value
      { LV(l) <@> to_code_position($startpos, $endpos) }
  | "-" e = expr
      { UnaryOp(Neg, e) <@> to_code_position($startpos, $endpos) }
  | e1 = expr b = bin_op e2 = expr
      { BinaryOp(b, e1, e2) <@> to_code_position($startpos, $endpos) }
;

l_value:
  | id = ID 
      { AccVar(None, id) <@> to_code_position($startpos, $endpos) }
  | id = ID "[" e = expr "]"
      { AccIndex(AccVar(None, id) <@> to_code_position($startpos, $endpos), e) 
          <@> 
        to_code_position($startpos, $endpos) }

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