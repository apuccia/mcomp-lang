open Ast

let prelude_signature =
  [
    ("__Prelude_print", TFun ([ TInt ], TVoid));
    ("__Prelude_getint", TFun ([], TInt));
  ]

let app_signature = [ ("main", TFun ([], TInt)) ]
