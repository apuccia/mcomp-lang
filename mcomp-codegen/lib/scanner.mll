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
    create_hashtable 20 [
      ("var", VAR);
      ("if", IF);
      ("return", RETURN);
      ("else", ELSE);
      ("while", WHILE);
      ("int", INT);
      ("float", FLOAT);
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
      ("do", DO);
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

  let generate_pos lexbuf = 
    let init_pos = Lexing.lexeme_start_p lexbuf in
    let end_pos = Lexing.lexeme_end_p lexbuf in
    let sc = init_pos.pos_cnum - init_pos.pos_bol in
    let ec = end_pos.pos_cnum - end_pos.pos_bol in

    { line = init_pos.pos_lnum; start_column = sc; end_column = ec }

  let logger = 
    let file_h = Handlers.File("Scanner", Logging.Debug) in 
    let cli_h = Handlers.Cli Logging.Info in
    
    Logging.make_logger "Scanner" Logging.Debug [cli_h; file_h]

  let check_multiple c is_multiple lexbuf rule = 
    if is_multiple then (
      logger#info "Not a single character";
      raise (Lexing_error (Location.to_lexeme_position lexbuf, "Not a single character between '")))
    else
      rule c true lexbuf
}

(* Declaration of regular expressions *)

let digit = ['0' - '9']
let upper = ['A' - 'Z']
let lower = ['a' - 'z']
let hexadigit = ['0' - '9' 'a' - 'f' 'A' - 'F']
let exaint = "0x"hexadigit+
let exafloat = "0x"hexadigit+"."hexadigit+

(* identifiers starts with a letter or an underscore 
and then can contain letters, underscore and numbers *)
let id = (upper | lower)['a' - 'z' 'A' - 'Z' '0' - '9' '_']*

(* Declaration of scanner functions *)

rule next_token = parse
| exaint | digit+ as inum    
  {
    try
      let integer = Int32.of_string inum in

      logger#info "Recognized integer literal T_INT";
      T_INT integer
    with Failure _ ->
      raise
        (Lexing_error
          (generate_pos lexbuf, "Value " ^ inum ^ " overflows/underflows 32 bits"))

  }
| exafloat | digit+'.'digit+ as fnum
  {
    try 
      let fnumber = Float.of_string fnum in

      logger#info "Recognized float literal T_FLOAT";
      T_FLOAT(fnumber)
    with
    | Failure _ -> 
      raise 
        (Lexing_error (generate_pos lexbuf,
          "Value " ^ fnum ^ " is not a valid float"))
  }
| ''' 
  {
    logger#info "Started recognizing character";
    character ' ' false lexbuf
  }
| id as word    
  {
    try
      let kw = Hashtbl.find keyword_table word in
        
      logger#info "Recognized keyword %s = %s" word (kw_to_string kw);
      kw
    with Not_found -> 
      if String.length word > 64 then (
        logger#error "Identifier %s too long" word;
        raise (Lexing_error (generate_pos lexbuf,
          "Identifier " ^ word ^ " exceeding 64 characters length")))
      else (
        logger#info "Recognized identifier ID(%s)" word;
        ID(word))
  }
| '&'           
  { 
    logger#info "Recognized '&' = REF"; 
    REF 
  }
| '+'           
  { 
    logger#info "Recognized '+' = PLUS"; 
    PLUS 
  }
| "++"           
  { 
    logger#info "Recognized '++' = PLUSPLUS"; 
    PLUSPLUS 
  }
| '-'           
  { 
    logger#info "Recognized '-' = MINUS"; 
    MINUS 
  }
| "--"           
  { 
    logger#info "Recognized '--' = MINUSMINUS"; 
    MINUSMINUS 
  }
| '*'           
  { 
    logger#info "Recognized '*' = TIMES"; 
    TIMES 
  }
| '/'           
  { 
    logger#info "Recognized '/' = DIV"; 
    DIV 
  }
| '%'           
  { 
    logger#info "Recognized '%%' = MOD"; 
    MOD 
  }
| '='           
  { 
    logger#info "Recognized '=' = ASSIGN"; 
    ASSIGN 
  }
| "+="           
  { 
    logger#info "Recognized '+=' = PASSIGN"; 
    PASSIGN 
  }
| "-="           
  { 
    logger#info "Recognized '-=' = MINASSIGN"; 
    MINASSIGN 
  }
| "*="           
  { 
    logger#info "Recognized '*=' = TASSIGN"; 
    TASSIGN 
  }
| "/="           
  { 
    logger#info "Recognized '/=' = DASSIGN"; 
    DASSIGN 
  }
| "%="           
  { 
    logger#info "Recognized '%%=' = MODASSIGN"; 
    MODASSIGN 
  }
| "=="          
  { 
    logger#info "Recognized '==' = EQUAL"; 
    EQUAL 
  }
| "!="          
  { 
    logger#info "Recognized '!=' = NEQ"; 
    NEQ 
  }
| '<'           
  { 
    logger#info "Recognized '<' = LESS"; 
    LESS 
  }
| "<="          
  { 
    logger#info "Recognized '<=' = LEQ"; 
    LEQ 
  }
| '>'           
  { 
    logger#info "Recognized '>' = GREATER"; 
    GREATER 
  }
| ">="          
  { 
    logger#info "Recognized '<' = GEQ"; 
    GEQ 
  }
| "&&"          
  { 
    logger#info "Recognized '&&' = AND"; 
    AND 
  }
| "||"          
  { 
    logger#info "Recognized '||' = OR"; 
    OR 
  }
| '!'           
  { 
    logger#info "Recognized '!' = NOT"; 
    NOT 
  }
| '('           
  { 
    logger#info "Recognized '(' = LRBRACK"; 
    LRBRACK 
  }
| ')'           
  { 
    logger#info "Recognized ')' = RRBRACK"; 
    RRBRACK 
  }
| '{'           
  { 
    logger#info "Recognized '{' = LCBRACK"; 
    LCBRACK 
  }
| '}'           
  { 
    logger#info "Recognized '}' = RCBRACK"; 
    RCBRACK 
  }
| '['           
  { 
    logger#info "Recognized '[' = LSBRACK"; 
    LSBRACK 
  }
| ']'           
  { 
    logger#info "Recognized ']' = RSBRACK"; 
    RSBRACK 
  }
| '.'           
  { 
    logger#info "Recognized '.' = DOT"; 
    DOT 
  }
| ','           
  { 
    logger#info "Recognized ',' = COMMA"; 
    COMMA 
  }
| ';'           
  { 
    logger#info "Recognized ';' = SEMICOLON"; 
    SEMICOLON 
  }
| "<-"          
  { 
    logger#info "Recognized '<-' = CONN"; 
    CONN 
  }
| ':'           
  { 
    logger#info "Recognized ':' = TYPESIG"; 
    TYPESIG 
  }
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
  { 
    next_token lexbuf 
  }
| '\n'          
  { 
    logger#info "Recognized \\n"; Lexing.new_line lexbuf; 
    next_token lexbuf 
  }
| eof 
  { 
    EOF 
  }
| _             
  { 
    logger#error "Unexpected character %s" (Lexing.lexeme lexbuf);
    raise (Lexing_error (generate_pos lexbuf, 
      "Unexpected character: " ^ (Lexing.lexeme lexbuf))) 
  }
and inline_comment = parse
  | '\n'          
    { 
      logger#info "Finished recognizing inline comment"; 
      Lexing.new_line lexbuf;
      next_token lexbuf 
    }
  | eof 
    { 
      EOF 
    }
  | _             
    { 
      inline_comment lexbuf 
    }
and block_comment = parse
  | "*/"          
    { 
      logger#info "Finished recognizing block comment"; 
      next_token lexbuf 
    }
  | '\n' 
    {
      Lexing.new_line lexbuf;
      block_comment lexbuf
    }
  | "/*" 
    {
      logger#error "Starting a nested comment block";
      raise (Lexing_error (generate_pos lexbuf, 
        "Nested comment blocks are not supported"))
    }
  | eof           
    { 
      logger#error "Not terminating comment block";
      raise (Lexing_error (generate_pos lexbuf, 
        "Comment block not terminated"))
    }
  | _             
    { 
      block_comment lexbuf 
    }
and character c is_multiple = parse
  | '''
    { 
      logger#info "Recognized character T_CHAR(%c)" c;
      T_CHAR(c) 
    }
  | '\\' 'a'
    { 
      check_multiple '\x07' is_multiple lexbuf character 
    } 
  | '\\' 'b'
    { 
      check_multiple '\x08' is_multiple lexbuf character 
    }
  | '\\' 't'
    { 
      check_multiple '\x09' is_multiple lexbuf character 
    }
  | '\\' 'n'
    { 
      check_multiple '\x0a' is_multiple lexbuf character 
    }
  | '\\' 'f'
    { 
      check_multiple '\x0c' is_multiple lexbuf character 
    }
  | '\\' 'r'
    { 
      check_multiple '\x0d' is_multiple lexbuf character 
    }
  | '\\' '''        
    { 
      check_multiple '\'' is_multiple lexbuf character 
    }
  | [^'''] as c'
    { 
      check_multiple c' is_multiple lexbuf character 
    }
  | _
    { 
      logger#error "Character not recognized";
      raise (Lexing_error((Location.to_lexeme_position lexbuf), "Unrecognized character"))
    }