type token =
  | INT of (int)
  | VAR of (string)
  | TRUE
  | FALSE
  | SUCC
  | BEQUAL
  | EQUAL
  | LPAREN
  | RPAREN
  | LBRACKET
  | RBRACKET
  | COLON
  | COMMA
  | DOT
  | LAMBDA
  | LET
  | IN
  | IF
  | THEN
  | ELSE
  | ARROW
  | FORALL
  | EOF

open Parsing;;
let _ = parse_error;;
# 1 "type_parser.mly"
 
  open Type_grammar
# 32 "type_parser.ml"
let yytransl_const = [|
  259 (* TRUE *);
  260 (* FALSE *);
  261 (* SUCC *);
  262 (* BEQUAL *);
  263 (* EQUAL *);
  264 (* LPAREN *);
  265 (* RPAREN *);
  266 (* LBRACKET *);
  267 (* RBRACKET *);
  268 (* COLON *);
  269 (* COMMA *);
  270 (* DOT *);
  271 (* LAMBDA *);
  272 (* LET *);
  273 (* IN *);
  274 (* IF *);
  275 (* THEN *);
  276 (* ELSE *);
  277 (* ARROW *);
  278 (* FORALL *);
    0 (* EOF *);
    0|]

let yytransl_block = [|
  257 (* INT *);
  258 (* VAR *);
    0|]

let yylhs = "\255\255\
\003\000\004\000\004\000\002\000\002\000\002\000\001\000\001\000\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\000\000\000\000"

let yylen = "\002\000\
\001\000\003\000\001\000\001\000\003\000\003\000\001\000\001\000\
\001\000\001\000\003\000\002\000\008\000\004\000\002\000\006\000\
\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\008\000\001\000\009\000\010\000\000\000\
\000\000\000\000\000\000\000\000\007\000\000\000\000\000\004\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\011\000\000\000\000\000\000\000\006\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000"

let yydgoto = "\003\000\
\022\000\015\000\013\000\000\000"

let yysindex = "\026\000\
\067\255\002\255\000\000\000\000\000\000\000\000\000\000\067\255\
\067\255\022\255\067\255\067\255\000\000\002\255\250\254\000\000\
\067\255\058\255\018\255\010\255\039\255\067\255\004\255\002\255\
\000\000\038\255\067\255\067\255\000\000\250\254\002\255\067\255\
\031\255\005\255\067\255\032\255\067\255\067\255\067\255"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\052\000\000\000\000\000\055\000\000\000\
\001\000\000\000\000\000\000\000\000\000\003\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\002\000\000\000\005\000\
\000\000\000\000\000\000\000\000\007\000\000\000\009\000"

let yygindex = "\000\000\
\010\000\248\255\254\255\000\000"

let yytablesize = 285
let yytable = "\016\000\
\012\000\005\000\015\000\005\000\014\000\023\000\016\000\020\000\
\013\000\014\000\012\000\016\000\029\000\036\000\024\000\030\000\
\026\000\017\000\018\000\005\000\021\000\016\000\034\000\005\000\
\024\000\024\000\001\000\002\000\016\000\019\000\027\000\004\000\
\005\000\006\000\007\000\008\000\032\000\033\000\009\000\004\000\
\005\000\006\000\007\000\008\000\037\000\010\000\009\000\039\000\
\011\000\031\000\035\000\017\000\038\000\010\000\018\000\000\000\
\011\000\028\000\004\000\005\000\006\000\007\000\008\000\000\000\
\000\000\009\000\025\000\004\000\005\000\006\000\007\000\008\000\
\010\000\000\000\009\000\011\000\000\000\000\000\000\000\000\000\
\000\000\010\000\000\000\000\000\011\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\012\000\005\000\015\000\000\000\014\000\000\000\016\000\
\000\000\013\000\000\000\012\000\012\000\015\000\015\000\014\000\
\014\000\016\000\016\000\013\000\013\000"

let yycheck = "\002\000\
\000\000\000\000\000\000\002\001\000\000\014\000\000\000\010\000\
\000\000\008\001\001\000\014\000\009\001\009\001\021\001\024\000\
\019\000\008\000\009\000\002\001\011\000\024\000\031\000\002\001\
\021\001\021\001\001\000\002\000\031\000\008\001\021\001\001\001\
\002\001\003\001\004\001\005\001\027\000\028\000\008\001\001\001\
\002\001\003\001\004\001\005\001\035\000\015\001\008\001\038\000\
\018\001\012\001\020\001\000\000\021\001\015\001\000\000\255\255\
\018\001\019\001\001\001\002\001\003\001\004\001\005\001\255\255\
\255\255\008\001\009\001\001\001\002\001\003\001\004\001\005\001\
\015\001\255\255\008\001\018\001\255\255\255\255\255\255\255\255\
\255\255\015\001\255\255\255\255\018\001\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\009\001\009\001\009\001\255\255\009\001\255\255\009\001\
\255\255\009\001\255\255\019\001\020\001\019\001\020\001\019\001\
\020\001\019\001\020\001\019\001\020\001"

let yynames_const = "\
  TRUE\000\
  FALSE\000\
  SUCC\000\
  BEQUAL\000\
  EQUAL\000\
  LPAREN\000\
  RPAREN\000\
  LBRACKET\000\
  RBRACKET\000\
  COLON\000\
  COMMA\000\
  DOT\000\
  LAMBDA\000\
  LET\000\
  IN\000\
  IF\000\
  THEN\000\
  ELSE\000\
  ARROW\000\
  FORALL\000\
  EOF\000\
  "

let yynames_block = "\
  INT\000\
  VAR\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 19 "type_parser.mly"
      ( _1 )
# 212 "type_parser.ml"
               : 'var))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'var) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'var_list) in
    Obj.repr(
# 23 "type_parser.mly"
                     ( _1 :: _3 )
# 220 "type_parser.ml"
               : 'var_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'var) in
    Obj.repr(
# 24 "type_parser.mly"
                     ( [_1] )
# 227 "type_parser.ml"
               : 'var_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'var) in
    Obj.repr(
# 28 "type_parser.mly"
                    ( match _1 with  
		      | "nat"  -> TyNat
		      | "bool" -> TyBool
		      | _      -> TyId _1 )
# 237 "type_parser.ml"
               : Type_grammar.ty))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Type_grammar.ty) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Type_grammar.ty) in
    Obj.repr(
# 32 "type_parser.mly"
                    ( (TyArr (_1, _3)) )
# 245 "type_parser.ml"
               : Type_grammar.ty))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Type_grammar.ty) in
    Obj.repr(
# 33 "type_parser.mly"
                    ( _2 )
# 252 "type_parser.ml"
               : Type_grammar.ty))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'var) in
    Obj.repr(
# 37 "type_parser.mly"
                                  ( TmVar (_1,Unk) )
# 259 "type_parser.ml"
               : Type_grammar.term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 38 "type_parser.mly"
                                  ( int_to_term _1 )
# 266 "type_parser.ml"
               : Type_grammar.term))
; (fun __caml_parser_env ->
    Obj.repr(
# 39 "type_parser.mly"
                                  ( TmTrue )
# 272 "type_parser.ml"
               : Type_grammar.term))
; (fun __caml_parser_env ->
    Obj.repr(
# 40 "type_parser.mly"
                                  ( TmFalse )
# 278 "type_parser.ml"
               : Type_grammar.term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : Type_grammar.term) in
    Obj.repr(
# 41 "type_parser.mly"
                                  ( _2 )
# 285 "type_parser.ml"
               : Type_grammar.term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Type_grammar.term) in
    Obj.repr(
# 42 "type_parser.mly"
                                  ( TmSucc _2 )
# 292 "type_parser.ml"
               : Type_grammar.term))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : 'var) in
    let _5 = (Parsing.peek_val __caml_parser_env 3 : Type_grammar.ty) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : Type_grammar.term) in
    Obj.repr(
# 43 "type_parser.mly"
                                                ( TmAbs (_3,_5,_8) )
# 301 "type_parser.ml"
               : Type_grammar.term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'var) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : Type_grammar.term) in
    Obj.repr(
# 44 "type_parser.mly"
                                  ( TmAbs (_2,Unk,_4) )
# 309 "type_parser.ml"
               : Type_grammar.term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Type_grammar.term) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Type_grammar.term) in
    Obj.repr(
# 45 "type_parser.mly"
                                  ( TmApp (_1,_2) )
# 317 "type_parser.ml"
               : Type_grammar.term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : Type_grammar.term) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : Type_grammar.term) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : Type_grammar.term) in
    Obj.repr(
# 46 "type_parser.mly"
                                  ( TmIf  (_2,_4,_6,Unk) )
# 326 "type_parser.ml"
               : Type_grammar.term))
(* Entry expr *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
(* Entry typ *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let expr (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Type_grammar.term)
let typ (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 2 lexfun lexbuf : Type_grammar.ty)
