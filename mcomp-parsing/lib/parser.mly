/**
 mComp parser specification 
 */
// TODO: verify all the grammar
%{
    (* Here code *)  
    open Ast
    open Location

    type 'a program_element = 
      | I of 'a interface_decl
      | Comp of 'a component_decl
      | Conns of connection list

    let make_node n f = 
        {node = n; annot = f}
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
// TODO: check this precedence, also ".", "[" and "&" are never useful precedences 
%nonassoc then_prec
%nonassoc "else"
%right "="
%left "||"
%left "&&"
%left "==", "!=" 
%nonassoc ">", "<", ">=", "<="
%left "+", "-"
%left "*", "/", "%" 
%nonassoc "!", "&"
%nonassoc "[", "."

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
      { I(make_node (InterfaceDecl{iname = i_name; declarations = i_m_decls}) (to_code_position($startpos, $endpos))) }
  | "component" 
    c_name = ID 
    p = provide_clause?
    u = use_clause?
    "{" defs = c_member_declaration+ "}"
      { Comp(make_node (ComponentDecl{
                            cname = c_name; 
                            provides = Option.value p ~default:[]; 
                            uses = Option.value u ~default:[]; 
                            definitions = defs};) 
                       (to_code_position($startpos, $endpos))) }
  | "connect" l = link ";"
      { Conns([l]) } 
  /*| "connect" 
    "{" l_list = terminated(link, ";")* "}"
      { Conns(l_list) }*/
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
      { make_node (VarDecl(vs)) (to_code_position($startpos, $endpos)) }

  | fp = fun_prototype ";"
      { make_node (FunDecl(fp)) (to_code_position($startpos, $endpos)) }
;

provide_clause:
  /*| "provides" l_p = terminated(ID, ",")* last = ID
      { l_p @ [last] }*/
    | "provides" p_l = separated_nonempty_list(",", ID)
      { p_l }
;

use_clause:
  /*| "uses" u_l = terminated(ID, ",")* last = ID
      { u_l @ [last] }*/
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
      { make_node (VarDecl(vd)) (to_code_position($startpos, $endpos)) }
  | fd = fun_declaration
      { make_node (FunDecl(fd)) (to_code_position($startpos, $endpos)) }
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
      { make_node (Block(c)) (to_code_position($startpos, $endpos)) }
;

block_content:
  | s = stmt
      { make_node (Stmt(s)) (to_code_position($startpos, $endpos)) }
  | "var" ld = var_sign ";"
      { make_node (LocalDecl(ld)) (to_code_position($startpos, $endpos)) }
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
      { make_node (Return(r)) (to_code_position($startpos, $endpos)) }
  | e = expr? ";"
      /*{ 
        let x = make_node (Skip) (to_code_position($startpos, $endpos)) in
          make_node (Option.value e ~default:x) (to_code_position($startpos, $endpos)) 
      }*/
      {
        match e with
          | None -> make_node (Skip) (to_code_position($startpos, $endpos))
          | Some v -> make_node (Expr(v)) (to_code_position($startpos, $endpos))
      }
  | b = block
      { b }
  | "while" cond = delimited("(", expr, ")") b = stmt 
      { make_node (While(cond, b)) (to_code_position($startpos, $endpos)) }
  | "if" cond = delimited("(", expr, ")") a = stmt "else" b = stmt 
      { make_node (If(cond, a, b)) (to_code_position($startpos, $endpos)) }
  | "if" cond = delimited("(", expr, ")") a = stmt %prec then_prec
      { let skip_node = make_node (Skip) (to_code_position($startpos, $endpos)) in 
        make_node (If(cond, a, skip_node)) (to_code_position($startpos, $endpos))
    }
  | "for" "(" init = expr? ";" cond = expr? ";" step = expr? ")" body = stmt
      { 
        (* creating the statement for counter variable initialization *)
        let i = match init with
          | None -> make_node (Skip) (to_code_position($startpos, $endpos))
          | Some v -> make_node (Expr(v)) (to_code_position($startpos, $endpos)) in
        let stmt_i = make_node (Stmt(i)) (to_code_position($startpos, $endpos)) in
        (* creating condition expression *)
        let c_expr = match cond with
          | None -> make_node (BLiteral(true)) (to_code_position($startpos, $endpos))
          | Some v -> v in
        (* creating the statement for counter modification *)
        let s = match step with
          | None -> make_node (Skip) (to_code_position($startpos, $endpos))
          | Some v -> make_node (Expr(v)) (to_code_position($startpos, $endpos)) in
        let stmt_s = make_node (Stmt(s)) (to_code_position($startpos, $endpos)) in
        (* creating while body *)
        let stmt_b = make_node (Stmt(body)) (to_code_position($startpos, $endpos)) in
        let w_block = make_node (Block([stmt_b; stmt_s])) (to_code_position($startpos, $endpos)) in
        let w = make_node (While(c_expr, w_block)) (to_code_position($startpos, $endpos)) in
        let stmt_w = make_node (Stmt(w)) (to_code_position($startpos, $endpos)) in
        (* creating final block composed of initialization and while *)
        make_node (Block[stmt_i; stmt_w]) (to_code_position($startpos, $endpos)) 
      }
  ;

expr:
  | i = T_INT
      { make_node (ILiteral(Int32.to_int i)) (to_code_position($startpos, $endpos)) }
  | c = T_CHAR
      { make_node (CLiteral(c)) (to_code_position($startpos, $endpos)) }
  | b = T_BOOL
      { make_node (BLiteral(b)) (to_code_position($startpos, $endpos)) }
  | e = delimited("(", expr, ")")
      { e }
  | "&" addr = l_value
      { make_node (Address(addr)) (to_code_position($startpos, $endpos)) }
  | l = l_value "=" e = expr
      { make_node (Assign(l, e)) (to_code_position($startpos, $endpos)) }
  | "!" e = expr
      { make_node (UnaryOp(Not, e)) (to_code_position($startpos, $endpos)) }
  | fname = ID "(" args = separated_list(",", expr) ")"
      { make_node (Call(None, fname, args)) (to_code_position($startpos, $endpos)) }
  | l = l_value
      { make_node (LV(l)) (to_code_position($startpos, $endpos)) }
  | "-" e = expr
      { make_node (UnaryOp(Neg, e)) (to_code_position($startpos, $endpos)) }
  | e1 = expr b = bin_op e2 = expr
      { make_node (BinaryOp(b, e1, e2)) (to_code_position($startpos, $endpos)) }
;

l_value:
  | id = ID 
      { make_node (AccVar(None, id)) (to_code_position($startpos, $endpos)) }
  // TODO: try to understand how to do this
  | id = ID "[" expr "]"
      { make_node (AccVar(None, id)) (to_code_position($startpos, $endpos)) }

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