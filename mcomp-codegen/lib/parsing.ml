exception Syntax_error of Location.lexeme_pos * string

open Parser

let parse next_token lexbuf = compilation_unit next_token lexbuf
