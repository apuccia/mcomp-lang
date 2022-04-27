{
  (* OCaml declaration*)   
  open Parser
  open Lexing
  open Location
  open Printf

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
let id = (upper | lower)['a' - 'z' 'A' - 'Z' '0' - '9' '_']*

(* Declaration of scanner functions *)

rule next_token = parse
| exa digit+ as inum    
  {
    printf "Recognized integer literal\n";
    let integer = Int32.of_string inum
    in T_INT(integer)
  }
| '\''          
  { character lexbuf }
| id as word    
  {
    try
      let kw = Hashtbl.find keyword_table word in
        printf "Recognized keyword: %s\n" word;
        kw
    with Not_found -> 
      if String.length word > 64 then
        let init_pos = Lexing.lexeme_start_p lexbuf in
        let end_pos = Lexing.lexeme_end_p lexbuf in
        let sc = init_pos.pos_cnum - init_pos.pos_bol in
        let ec = end_pos.pos_cnum - end_pos.pos_bol in
          raise (Lexing_error (generate_pos init_pos.pos_lnum sc ec,
            "Identifier " ^ word ^ " exceeding 64 characters length")) 
      else
        printf "Recognized identifier: %s\n" word; 
        ID(word)
  }
| '&'           
  { printf "Recognized &\n"; REF }
| '+'           
  { printf "Recognized +\n"; PLUS }
| '-'           
  { printf "Recognized -\n"; MINUS }
| '*'           
  { printf "Recognized *\n"; TIMES }
| '/'           
  { printf "Recognized /\n"; DIV }
| '%'           
  { printf "Recognized mod\n"; MOD }
| '='           
  { printf "Recognized =\n"; ASSIGN }
| "=="          
  { printf "Recognized ==\n"; EQUAL }
| "!="          
  { printf "Recognized !=\n"; NEQ }
| '<'           
  { printf "Recognized <\n"; LESS }
| "<="          
  { printf "Recognized <=\n"; LEQ }
| '>'           
  { printf "Recognized >\n"; GREATER }
| ">="          
  { printf "Recognized >=\n"; GEQ }
| "&&"          
  { printf "Recognized &&\n"; AND }
| "||"          
  { printf "Recognized ||\n"; OR }
| '!'           
  { printf "Recognized !\n"; NEG }
| '('           
  { printf "Recognized (\n"; LRBRACK }
| ')'           
  { printf "Recognized )\n"; RRBRACK }
| '{'           
  { printf "Recognized {\n"; LCBRACK }
| '}'           
  { printf "Recognized }\n"; RCBRACK }
| '['           
  { printf "Recognized [\n"; LSBRACK }
| ']'           
  { printf "Recognized ]\n"; RSBRACK }
| '.'           
  { printf "Recognized .\n"; DOT }
| ','           
  { printf "Recognized ,\n"; COMMA }
| ';'           
  { printf "Recognized ;\n"; SEMICOLON }
| "<-"          
  { printf "Recognized <-\n"; CONN }
| ':'           
  { printf "Recognized :\n"; TYPESIG }
| "//"          
  { 
    printf "Started recognizing inline comment\n"; 
    inline_comment lexbuf 
  }
| "/*"          
  { 
    printf "Started recognizing block comment\n"; 
    block_comment lexbuf 
  }
| [' ' '\t']    
  { next_token lexbuf }
| '\n'          
  { printf "Recognized \\n\n"; Lexing.new_line lexbuf; next_token lexbuf }
| eof           
  { EOF }
| _             
  { 
    let init_pos = Lexing.lexeme_start_p lexbuf in
    let end_pos = Lexing.lexeme_end_p lexbuf in
    let sc = init_pos.pos_cnum - init_pos.pos_bol in
    let ec = end_pos.pos_cnum - end_pos.pos_bol in
      raise (Lexing_error (generate_pos init_pos.pos_lnum sc ec, 
        "Unexpected character: " ^ (Lexing.lexeme lexbuf))) 
  }
and inline_comment = parse
| '\n'          
  { printf "Finished recognizing inline comment\n"; next_token lexbuf }
| _             
  { inline_comment lexbuf }
and block_comment = parse (* ignore other nested comments *)
| "*/"          
  { printf "Finished recognizing block comment\n"; next_token lexbuf }
| eof           
  { 
    let init_pos = Lexing.lexeme_start_p lexbuf in
    let end_pos = Lexing.lexeme_end_p lexbuf in
    let sc = init_pos.pos_cnum - init_pos.pos_bol in
    let ec = end_pos.pos_cnum - end_pos.pos_bol in
      raise (Comment_error (generate_pos init_pos.pos_lnum sc ec, 
        "Comment block not terminated at: " ^ (Lexing.lexeme lexbuf)))
  }
| _             
  { inline_comment lexbuf }
and character = parse 
| (characters|special) as c
  { 
    printf "Recognized character\n"; 
    T_CHAR(c)
  }
| '\''          
  { next_token lexbuf }