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
    | T_BOOL(true) -> "T_BOOL(true)"
    | T_BOOL(false) -> "T_BOOL(false)"
    | _ -> ""

  let generate_pos l sc ec = 
    { line = l; start_column = sc; end_column = ec }

  let info_logger = 
    Logging.make_logger "Scanner" Logging.Info [Handlers.Cli Logging.Info]
}

(* Declaration of regular expressions *)

let exa = "0x"?
let digit = ['0' - '9']
let upper = ['A' - 'Z']
let lower = ['a' - 'z']
(* \f not supported by OCaml, I use its byte representation *)
let special = ['\'' '\b' '\t' '\x0c' '\\' '\r' '\n']
let characters = [^ '\'' '\b' '\x0c' '\t' '\\' '\r' '\n']

(* identifiers starts with a letter or an underscore 
and then can contain letters, underscore and numbers *)
let id = (upper | lower)['a' - 'z' 'A' - 'Z' '0' - '9' '_']*

(* Declaration of scanner functions *)

rule next_token = parse
| exa digit+ as inum    
  {
    let integer = Int32.of_string inum
    in
      info_logger#info "Recognized integer literal T_INT(%ld)" integer;
      T_INT(integer)
  }
| '\''          
  { character lexbuf }
| id as word    
  {
    try
      let kw = Hashtbl.find keyword_table word in
        info_logger#info "Recognized keyword %s = %s" word (kw_to_string kw);
        kw
    with Not_found -> 
      if String.length word > 64 then
        let init_pos = Lexing.lexeme_start_p lexbuf in
        let end_pos = Lexing.lexeme_end_p lexbuf in
        let sc = init_pos.pos_cnum - init_pos.pos_bol in
        let ec = end_pos.pos_cnum - end_pos.pos_bol in
          info_logger#error "Identifier %s too long" word;
          raise (Lexing_error (generate_pos init_pos.pos_lnum sc ec,
            "Identifier " ^ word ^ " exceeding 64 characters length")) 
      else
        info_logger#info "Recognized identifier ID(%s)" word;
        ID(word)
  }
| '&'           
  { info_logger#info "Recognized '&' = REF"; REF }
| '+'           
  { info_logger#info "Recognized '+' = PLUS"; PLUS }
| '-'           
  { info_logger#info "Recognized '-' = MINUS"; MINUS }
| '*'           
  { info_logger#info "Recognized '*' = TIMES"; TIMES }
| '/'           
  { info_logger#info "Recognized '/' = DIV"; DIV }
| '%'           
  { info_logger#info "Recognized '%%' = MOD"; MOD }
| '='           
  { info_logger#info "Recognized '=' = ASSIGN"; ASSIGN }
| "=="          
  { info_logger#info "Recognized '==' = EQUAL"; EQUAL }
| "!="          
  { info_logger#info "Recognized '!=' = NEQ"; NEQ }
| '<'           
  { info_logger#info "Recognized '<' = LESS"; LESS }
| "<="          
  { info_logger#info "Recognized '<=' = LEQ"; LEQ }
| '>'           
  { info_logger#info "Recognized '>' = GREATER"; GREATER }
| ">="          
  { info_logger#info "Recognized '<' = GEQ"; GEQ }
| "&&"          
  { info_logger#info "Recognized '&&' = AND"; AND }
| "||"          
  { info_logger#info "Recognized '||' = OR"; OR }
| '!'           
  { info_logger#info "Recognized '!' = NEG"; NEG }
| '('           
  { info_logger#info "Recognized '(' = LRBRACK"; LRBRACK }
| ')'           
  { info_logger#info "Recognized ')' = RRBRACK"; RRBRACK }
| '{'           
  { info_logger#info "Recognized '{' = LCBRACK"; LCBRACK }
| '}'           
  { info_logger#info "Recognized '}' = RCBRACK"; RCBRACK }
| '['           
  { info_logger#info "Recognized '[' = LSBRACK"; LSBRACK }
| ']'           
  { info_logger#info "Recognized ']' = RSBRACK"; RSBRACK }
| '.'           
  { info_logger#info "Recognized '.' = DOT"; DOT }
| ','           
  { info_logger#info "Recognized ',' = COMMA"; COMMA }
| ';'           
  { info_logger#info "Recognized ';' = SEMICOLON"; SEMICOLON }
| "<-"          
  { info_logger#info "Recognized '<-' = CONN"; CONN }
| ':'           
  { info_logger#info "Recognized ':' = TYPESIG"; TYPESIG }
| "//"          
  { 
    info_logger#info "Started recognizing inline comment"; 
    inline_comment lexbuf 
  }
| "/*"          
  { 
    info_logger#info "Started recognizing block comment";
    block_comment lexbuf 
  }
| [' ' '\t']    
  { next_token lexbuf }
| '\n'          
  { info_logger#info "Recognized \\n"; Lexing.new_line lexbuf; next_token lexbuf }
| eof           
  { EOF }
| _             
  { 
    let init_pos = Lexing.lexeme_start_p lexbuf in
    let end_pos = Lexing.lexeme_end_p lexbuf in
    let sc = init_pos.pos_cnum - init_pos.pos_bol in
    let ec = end_pos.pos_cnum - end_pos.pos_bol in
      info_logger#error "Unexpected characters %s" (Lexing.lexeme lexbuf);
      raise (Lexing_error (generate_pos init_pos.pos_lnum sc ec, 
        "Unexpected character: " ^ (Lexing.lexeme lexbuf))) 
  }
and inline_comment = parse
| '\n'          
  { info_logger#info "Finished recognizing inline comment"; next_token lexbuf }
| _             
  { inline_comment lexbuf }
and block_comment = parse (* ignore other nested comments *)
| "*/"          
  { info_logger#info "Finished recognizing block comment"; next_token lexbuf }
| eof           
  { 
    let init_pos = Lexing.lexeme_start_p lexbuf in
    let end_pos = Lexing.lexeme_end_p lexbuf in
    let sc = init_pos.pos_cnum - init_pos.pos_bol in
    let ec = end_pos.pos_cnum - end_pos.pos_bol in
      info_logger#error "Not terminating comment block";
      raise (Lexing_error (generate_pos init_pos.pos_lnum sc ec, 
        "Comment block not terminated"))
  }
| _             
  { block_comment lexbuf }
and character = parse 
| (characters | special) as c
  { 
    info_logger#info "Recognized character literal T_CHAR(%c)" c;
    T_CHAR(c)
  }
| '\''          
  { next_token lexbuf }