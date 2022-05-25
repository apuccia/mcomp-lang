open Lexing

exception Syntax_error of Location.lexeme_pos * string

module I = Parser.MenhirInterpreter

let env checkpoint =
  match checkpoint with I.HandlingError env -> env | _ -> assert false

let state checkpoint =
  match I.top (env checkpoint) with
  | Some (I.Element (s, _, _, _)) -> I.number s
  | None -> 0

let rec parse_buf next_token lexbuf checkpoint =
  match checkpoint with
  | I.InputNeeded _env ->
      (* get next token *)
      let token = next_token lexbuf in
      let startp = lexbuf.lex_start_p and endp = lexbuf.lex_curr_p in
      let checkpoint = I.offer checkpoint (token, startp, endp) in
      parse_buf next_token lexbuf checkpoint
  | I.Shifting _ | I.AboutToReduce _ ->
      let checkpoint = I.resume checkpoint in
      parse_buf next_token lexbuf checkpoint
  | I.HandlingError _env ->
      (* get the corresponding message and raise a syntax error *)
      let message = Parser_messages.message (state checkpoint) in
      let pos = Location.to_lexeme_position lexbuf in
      raise (Syntax_error (pos, message))
  | I.Accepted v -> v
  (* we stop at the first error, so this is never reached *)
  | I.Rejected -> assert false

let parse next_token lexbuf =
  parse_buf next_token lexbuf (Parser.Incremental.compilation_unit lexbuf.lex_curr_p)
