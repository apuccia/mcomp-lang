exception DuplicateEntry of Ast.identifier
exception NotFoundEntry

type 'a t = Dummy | Table of 'a t * (Ast.identifier, 'a) Hashtbl.t  (* A Dummy type *)

let empty_table () = 
  Table(Dummy, Hashtbl.create 0) 

let begin_block parent_block = 
  Table(parent_block, Hashtbl.create 0)

let end_block closing_block = 
  match closing_block with
    | Table(parent_block, _) -> parent_block
    | Dummy -> Dummy

let rec lookup ide table =
  match table with
    | Table(parent, hash_tbl) -> 
      (try 
        Hashtbl.find hash_tbl ide
      with
        | Not_found -> lookup ide parent)
    | Dummy -> raise (NotFoundEntry)

let add_entry ide value table = 
  match table with
    | Table(parent_block, hash_tbl) -> 
      (try
        let _ = lookup ide table in raise (DuplicateEntry ide)
      with 
        NotFoundEntry -> let _ = Hashtbl.add hash_tbl ide value in Table(parent_block, hash_tbl))
    | Dummy -> failwith "No scope"

let rec scan_list l table = 
  match l with
    | [] -> table
    | (ide, value)::xs -> let nt = add_entry ide value table in
                            scan_list xs nt

let of_alist list table =
  scan_list list table