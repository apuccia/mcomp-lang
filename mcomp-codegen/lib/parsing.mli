exception Syntax_error of Location.lexeme_pos * string

val parse :
  Lexing.lexbuf ->
  Ast.located_compilation_unit
