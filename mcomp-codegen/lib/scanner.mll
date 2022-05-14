{
  (* OCaml declaration*)   
  open Parser
  open Lexing
  open Location
  open Easy_logging

  exception Lexing_error of lexeme_pos * string    

  let create_hashtable size init =
    let tbl = Hashtbl.create size in
    List.iter (fun (key, data) -> Hashtbl.add tbl key data) init;
    tbl

  let keyword_table =
    create_hashtable 18 [
      ("var", VAR);
      ("if", IF);
      ("return", RETURN);
      ("else", ELSE);
      ("while", WHILE);
      ("int", INT);
      ("char", CHAR);
      ("void", VOID);
      ("bool", BOOL);
      ("interface", INTERFACE);
      ("uses", USES);
      ("provides", PROVIDES);
      ("component", COMPONENT);
      ("connect", CONNECT);
      ("def", DEF);
      ("for", FOR);
      ("true", T_BOOL(true));
      ("false", T_BOOL(false));
    ]
  
  let kw_to_string t =
    match t with 
    | VAR -> "VAR"
    | IF -> "IF"
    | RETURN -> "RETURN"
    | ELSE -> "ELSE"
    | WHILE -> "WHILE"
    | INT -> "INT"
    | CHAR -> "CHAR"
    | VOID -> "VOID"
    | BOOL -> "BOOL"
    | INTERFACE -> "INTERFACE"
    | USES -> "USES"
    | PROVIDES -> "PROVIDES"
    | COMPONENT -> "COMPONENT"
    | CONNECT -> "CONNECT"
    | DEF -> "DEF"
    | FOR -> "FOR"
    | DO -> "DO"
    | T_BOOL(true) -> "T_BOOL(true)"
    | T_BOOL(false) -> "T_BOOL(false)"
    | _ -> ""

  let generate_pos l sc ec = 
    { line = l; start_column = sc; end_column = ec }

  let logger = 
    let file_h = Handlers.File("Scanner", Logging.Debug) in 
      let cli_h = Handlers.Cli Logging.Debug in
        Logging.make_logger "Scanner" Logging.Debug [cli_h; file_h]
}

(* Declaration of regular expressions *)

let digit = ['0' - '9']
let upper = ['A' - 'Z']
let lower = ['a' - 'z']
let hexadigit = ['0' - '9' 'a' - 'f' 'A' - 'F']
let exaint = "0x"hexadigit+
let exafloat = "0x"hexadigit+.hexadigit+
(* \f not supported by OCaml, I use its byte representation *)
let special = ['\'' '\b' '\t' '\x0c' '\\' '\r' '\n']
let characters = [^ '\'' '\b' '\x0c' '\t' '\\' '\r' '\n']

(* identifiers starts with a letter or an underscore 
and then can contain letters, underscore and numbers *)
let id = (upper | lower)['a' - 'z' 'A' - 'Z' '0' - '9' '_']*

(* Declaration of scanner functions *)

rule next_token = parse
| exaint | digit+ as inum    
  {
    try 
      let integer = Int32.of_string inum
      in
        logger#info "Recognized integer literal T_INT";
        T_INT(integer)
    with
    | Failure(_) -> 
      let init_pos = Lexing.lexeme_start_p lexbuf in
      let end_pos = Lexing.lexeme_end_p lexbuf in
      let sc = init_pos.pos_cnum - init_pos.pos_bol in
      let ec = end_pos.pos_cnum - end_pos.pos_bol in
      raise (Lexing_error (generate_pos init_pos.pos_lnum sc ec,
        "Value " ^ inum ^ " overflows/underflows 32 bits"))
  }
| exafloat | digit+'.'digit+ as fnum
  {
    {
    try 
      let fnumber = Float.of_string fnum
      in
        logger#info "Recognized float literal T_FLOAT";
        T_FLOAT(integer)
    with
    | Failure(_) -> 
      let init_pos = Lexing.lexeme_start_p lexbuf in
      let end_pos = Lexing.lexeme_end_p lexbuf in
      let sc = init_pos.pos_cnum - init_pos.pos_bol in
      let ec = end_pos.pos_cnum - end_pos.pos_bol in
      raise (Lexing_error (generate_pos init_pos.pos_lnum sc ec,
        "Value " ^ fnum ^ " is not a valid float"))
  }
  }
| '\''          
  { character lexbuf }
| id as word    
  {
    try
      let kw = Hashtbl.find keyword_table word in
        logger#info "Recognized keyword %s = %s" word (kw_to_string kw);
        kw
    with Not_found -> 
      if String.length word > 64 then
        let init_pos = Lexing.lexeme_start_p lexbuf in
        let end_pos = Lexing.lexeme_end_p lexbuf in
        let sc = init_pos.pos_cnum - init_pos.pos_bol in
        let ec = end_pos.pos_cnum - end_pos.pos_bol in
          logger#error "Identifier %s too long" word;
          raise (Lexing_error (generate_pos init_pos.pos_lnum sc ec,
            "Identifier " ^ word ^ " exceeding 64 characters length")) 
      else
        logger#info "Recognized identifier ID(%s)" word;
        ID(word)
  }
| '&'           
  { logger#info "Recognized '&' = REF"; REF }
| '+'           
  { logger#info "Recognized '+' = PLUS"; PLUS }
| '-'           
  { logger#info "Recognized '-' = MINUS"; MINUS }
| '*'           
  { logger#info "Recognized '*' = TIMES"; TIMES }
| '/'           
  { logger#info "Recognized '/' = DIV"; DIV }
| '%'           
  { logger#info "Recognized '%%' = MOD"; MOD }
| '='           
  { logger#info "Recognized '=' = ASSIGN"; ASSIGN }
| "=="          
  { logger#info "Recognized '==' = EQUAL"; EQUAL }
| "!="          
  { logger#info "Recognized '!=' = NEQ"; NEQ }
| '<'           
  { logger#info "Recognized '<' = LESS"; LESS }
| "<="          
  { logger#info "Recognized '<=' = LEQ"; LEQ }
| '>'           
  { logger#info "Recognized '>' = GREATER"; GREATER }
| ">="          
  { logger#info "Recognized '<' = GEQ"; GEQ }
| "&&"          
  { logger#info "Recognized '&&' = AND"; AND }
| "||"          
  { logger#info "Recognized '||' = OR"; OR }
| '!'           
  { logger#info "Recognized '!' = NEG"; NEG }
| '('           
  { logger#info "Recognized '(' = LRBRACK"; LRBRACK }
| ')'           
  { logger#info "Recognized ')' = RRBRACK"; RRBRACK }
| '{'           
  { logger#info "Recognized '{' = LCBRACK"; LCBRACK }
| '}'           
  { logger#info "Recognized '}' = RCBRACK"; RCBRACK }
| '['           
  { logger#info "Recognized '[' = LSBRACK"; LSBRACK }
| ']'           
  { logger#info "Recognized ']' = RSBRACK"; RSBRACK }
| '.'           
  { logger#info "Recognized '.' = DOT"; DOT }
| ','           
  { logger#info "Recognized ',' = COMMA"; COMMA }
| ';'           
  { logger#info "Recognized ';' = SEMICOLON"; SEMICOLON }
| "<-"          
  { logger#info "Recognized '<-' = CONN"; CONN }
| ':'           
  { logger#info "Recognized ':' = TYPESIG"; TYPESIG }
| "//"          
  { 
    logger#info "Started recognizing inline comment"; 
    inline_comment lexbuf 
  }
| "/*"          
  { 
    logger#info "Started recognizing block comment";
    block_comment lexbuf 
  }
| [' ' '\t']    
  { next_token lexbuf }
| '\n'          
  { logger#info "Recognized \\n"; Lexing.new_line lexbuf; next_token lexbuf }
| eof { EOF }
| _             
  { 
    let init_pos = Lexing.lexeme_start_p lexbuf in
    let end_pos = Lexing.lexeme_end_p lexbuf in
    let sc = init_pos.pos_cnum - init_pos.pos_bol in
    let ec = end_pos.pos_cnum - end_pos.pos_bol in
      logger#error "Unexpected character %s" (Lexing.lexeme lexbuf);
      raise (Lexing_error (generate_pos init_pos.pos_lnum sc ec, 
        "Unexpected character: " ^ (Lexing.lexeme lexbuf))) 
  }
and inline_comment = parse
| '\n'          
  { 
    logger#info "Finished recognizing inline comment"; 
    Lexing.new_line lexbuf;
    next_token lexbuf 
  }
| eof { EOF }
| _             
  { inline_comment lexbuf }
and block_comment = parse (* ignore other nested comments *)
| "*/"          
  { logger#info "Finished recognizing block comment"; next_token lexbuf }
| '\n' 
  {
    Lexing.new_line lexbuf;
    block_comment lexbuf
  }
| eof           
  { 
    let init_pos = Lexing.lexeme_start_p lexbuf in
    let end_pos = Lexing.lexeme_end_p lexbuf in
    let sc = init_pos.pos_cnum - init_pos.pos_bol in
    let ec = end_pos.pos_cnum - end_pos.pos_bol in
      logger#error "Not terminating comment block";
      raise (Lexing_error (generate_pos init_pos.pos_lnum sc ec, 
        "Comment block not terminated"))
  }
| _             
  { block_comment lexbuf }
and character = parse 
| (characters | special) as c
  { 
    logger#info "Recognized character literal T_CHAR(%c)" c;
    T_CHAR(c)
  }
| '\''          
  { next_token lexbuf }