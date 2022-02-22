{
  (* OCaml declaration*)   
  open Parser
  open Lexing
  open Location

  exception Lexing_error of lexeme_pos * string    
  exception Comment_error of lexeme_pos * string    

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

    let generate_pos l sc ec = 
      { line = l; start_column = sc; end_column = ec }
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
let id = (upper | lower)['a' - 'z' '0' - '9' '_']*

(* Declaration of scanner functions *)

rule next_token = parse
  | exa digit+ as inum    
                  {
                    let integer = Int32.of_string inum
                    in T_INT(integer)
                  }
  | (characters|special) as c
                  { T_CHAR(c)}
  | id as word    {
                    try
                      Hashtbl.find keyword_table word
                      with Not_found -> ID(word)
                  }
  | '&'           { REF }
  | '+'           { PLUS }
  | '-'           { MINUS }
  | '*'           { TIMES }
  | '/'           { DIV }
  | '%'           { MOD }
  | '='           { ASSIGN }
  | "=="          { EQUAL }
  | "!="          { NEQ }
  | '<'           { LESS }
  | "<="          { LEQ }
  | '>'           { GREATER }
  | ">="          { GEQ }
  | "&&"          { AND }
  | "||"          { OR }
  | '!'           { NEG }
  | '('           { LRBRACK }
  | ')'           { RRBRACK }
  | '{'           { LCBRACK }
  | '}'           { RCBRACK }
  | '['           { LSBRACK }
  | ']'           { RSBRACK }
  | '.'           { DOT }
  | ','           { COMMA }
  | ';'           { SEMICOLON }
  | "<-"          { CONN }
  | ':'           { TYPESIG }
  | "//"          { inline_comment lexbuf }
  | "/*"          { block_comment lexbuf }

  | [' ' '\t']    { next_token lexbuf }
  | '\n'          { Lexing.new_line lexbuf; next_token lexbuf }
  | eof           { EOF }
  | _             { 
    (* TODO: check this solution for lexeme_pos *)
    let init_pos = Lexing.lexeme_start_p lexbuf in
    let end_pos = Lexing.lexeme_end_p lexbuf in
    let sc = init_pos.pos_cnum - init_pos.pos_bol in
    let ec = end_pos.pos_cnum - end_pos.pos_bol in
    raise (Lexing_error (generate_pos init_pos.pos_lnum sc ec, "Unexpected character: " ^ (Lexing.lexeme lexbuf))) }
and inline_comment = parse (* ignore other nested comments *)
  | '\n'          { next_token lexbuf }
  | _             { inline_comment lexbuf }
and block_comment = parse (* ignore other nested comments *)
  | "*/"          { next_token lexbuf }
  | eof           { 
    let init_pos = Lexing.lexeme_start_p lexbuf in
    let end_pos = Lexing.lexeme_end_p lexbuf in
    let sc = init_pos.pos_cnum - init_pos.pos_bol in
    let ec = end_pos.pos_cnum - end_pos.pos_bol in
    raise (Comment_error (generate_pos init_pos.pos_lnum sc ec, "Comment block not terminated at: " ^ (Lexing.lexeme lexbuf)))}
  | _             { inline_comment lexbuf }