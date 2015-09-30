(*************************************************************)
(* Simple grammar for types, all beginning with Ty.          *)
(*************************************************************)
open Type_grammar

(* Exception for error handling *)
exception Exn of string
let fail_exn s = raise (Exn s);

(*************************************************************)
(* Context and constraints types                             *)
(*************************************************************)
type context     = Ctxt of (string * ty) list
type constraints = Cstr of (ty * ty) list

(*************************************************************)
(*                  Helper functions                         *)
(*************************************************************)
(* Remove all occurrences of an association in an assoc list *)
let rec remove_assoc (l:('a*'b) list) (x:'a) = match l with 
  | []   -> []
  | (y,z)::c -> if (y=x) then remove_assoc c x 
                else (y,z)::(remove_assoc c x);;

(* Mostly, these functions convert the values into strings that 
   can be displayed. *)
let red_string  s = "\x1B[31;1m"^s^"\x1B[0m"
let blue_string s = "\x1B[34;1m"^s^"\x1B[0m"
let bold_string s = "\x1B[1m"^s^"\x1B[0m "

let rec ty_to_string t = match t with
  | TyBool -> "Bool"
  | TyNat  -> "Nat"
  | TyArr (x,y) -> "("^(ty_to_string x)^" -> "^(ty_to_string y)^")"
  | TyId s -> red_string s
  | Unk    -> "unknown"

let rec term_to_string t = match t with
  | TmTrue   -> "T"
  | TmFalse  -> "F"
  | TmZero   -> "0"
  | TmSucc t -> (bold_string "S")^(term_to_string t)
  | TmIf (i,t,e,ty) -> (bold_string "if")^(term_to_string i)^
    " : Bool "^(bold_string "then")^(term_to_string t)^
    " : "^(ty_to_string ty)^" "^(bold_string "else")^
    (term_to_string e)^" : "^(ty_to_string ty)
  | TmVar (s,t)  -> (blue_string s)^" : "^(ty_to_string t)
  | TmAbs (v,t,e) -> "( "^(bold_string "λ")^(blue_string v)^
    " : "^(ty_to_string t)^
    " . "^(term_to_string e)^" )"
  | TmApp (a,b)   -> (term_to_string a)^" "^(term_to_string b)

let context_to_string (Ctxt c) = 
  Printf.printf "--- Context : \n";
  List.iter (fun (s,t) -> Printf.printf "%s : %s" s 
	       (ty_to_string t)) c;
  Printf.printf "--------------------------\n";;

let constraints_to_string (Cstr c) = 
  Printf.printf "--- Constraints : \n";
  List.iter (fun (s,t) -> Printf.printf ". %s = %s\n" 
	       (ty_to_string s) (ty_to_string t)) c;;

(*************************************************************)
(* Fresh variable names generator - with imperative features
   inside. A function that, each time it is called, returns a
   new variable name. *)
(*************************************************************)
let fresh_var_name_gen = 
  let x = ref 0 in
  let rec gen_rec () = 
    incr x; TyId ("X_"^(string_of_int !x))
  in gen_rec;;
let gen = fresh_var_name_gen;; (* shorter name *)

(*************************************************************)
(*                  Constraints inference                    *)
(*************************************************************)
(* Arguments  : - a context (possibly empty, at least at the beginning),
                - and a term.
   It returns : - a type,
                - an updated context
                - a list of constraints
                - and an equivalent term that is typed without Unk. *)
let rec compute_constraints (Ctxt ct:context) (t:term) = match t with
  | TmTrue       -> (TyBool, Ctxt ct, Cstr [], t)
  | TmFalse      -> (TyBool, Ctxt ct, Cstr [], t)
  | TmZero       -> (TyNat,  Ctxt ct, Cstr [], t)
  | TmSucc u     ->
    let (nt, nct, Cstr ncon, tu) = compute_constraints (Ctxt ct) u in
      (TyNat, nct, Cstr ((nt, TyNat)::ncon), TmSucc tu)

  | TmVar (s,ty) -> 
     if (ty != Unk) then (ty, Ctxt ct, Cstr [], t)
     else begin try
              let nt = List.assoc s ct in
              (nt,    Ctxt ct, Cstr [], TmVar(s, nt))
            with Not_found ->
              let newty = gen() in
              (newty, Ctxt ((s,newty)::ct), Cstr [], TmVar(s, newty))
          end

  | TmIf (i,t,e,ty) ->
     let (ni, _, Cstr icon, ti) = compute_constraints (Ctxt ct) i in
     let (nt, _, Cstr tcon, tt) = compute_constraints (Ctxt ct) t in
     let (ne, _, Cstr econ, te) = compute_constraints (Ctxt ct) e in
     let rest = TmIf (ti,tt,te,nt) in
     let bcon = (ni, TyBool)::(nt, ne)::(icon@tcon@econ) in 
       (nt, Ctxt ct, Cstr (if (ty != Unk) then ((ty,nt)::bcon)
                         else bcon), rest)

  | TmAbs (x,ty,e) -> 
     let newty = if (ty != Unk) then ty else gen() in 
     let tmpct = Ctxt ((x,newty)::ct) in
     let (nt, Ctxt nct, Cstr ncon, te) = compute_constraints tmpct e in
     let resty = TyArr (newty,nt) in
     let newct = Ctxt (remove_assoc nct x) in
     (resty, newct, Cstr ncon, TmAbs(x,newty,te))

  | TmApp (a,b)    ->
    let (na, Ctxt nct, Cstr acon, ta) = compute_constraints (Ctxt ct) a in
    let (nb, Ctxt pct, Cstr bcon, tb) = compute_constraints (Ctxt nct) b in
    let newty = gen() in
    (newty, Ctxt pct,
     Cstr ((na, TyArr (nb, newty))::(acon@bcon)),
     TmApp(ta,tb))

(*************************************************************)
(*          Helper functions on type transformations         *)
(*************************************************************)
(* Types transformation functions *)

(* Apply a transformation on a list of constraints or a context *)
let apply_simple_constraints_transform cl (f:ty -> ty) = 
  List.map (fun (u,v) -> (f u,f v)) cl;;

(* Apply a recursive renaming to a type. May not terminate *)
let rec apply_rename_type (f:ty -> ty) (t:ty) = match t with
  | TyBool      -> TyBool
  | TyNat       -> TyNat
  | TyId i      -> let fi = f (TyId i) in
		   if (fi = TyId i) then TyId i else apply_rename_type f fi
  | TyArr (a,b) -> TyArr (apply_rename_type f a, apply_rename_type f b)
  | Unk         -> fail_exn "Apply_rename_type : unknown type";;

let rec apply_rename_term (f:ty_trans) (x:term) =
  (* print_endline (term_to_string x); *)
  match x with
  | TmIf   (i,t,e,ti)    -> TmIf   (apply_rename_term f i,
                                    apply_rename_term f t,
                                    apply_rename_term f e,
                                    apply_rename_type f ti)
  | TmVar  (s,ts)        -> TmVar  (s,apply_rename_type f ts)
  | TmAbs  (s,ts,t)      -> TmAbs  (s,apply_rename_type f ts,
                                    apply_rename_term f t)
  | TmApp  (u,v)         -> TmApp  (apply_rename_term f u,
                                    apply_rename_term f v)
  | TmSucc  u            -> TmSucc (apply_rename_term f u)
  | _ -> x

(* Apply recursive transformation on a list of constraints or a
   context. May not terminate. *)
let apply_constraints_transform cl (f:ty -> ty) = 
  List.map (fun (u,v) -> (apply_rename_type f u, apply_rename_type f v)) cl;;

(* Create a simple transformation mapping a variable into a term *)
let simple_transform s t = 
  let f x = if (x = TyId s) then t else x in f;;

(* Computation of the free variables in a term *)
let rec belongs_to (s:string) (t:ty) = match t with 
  | TyBool      -> false
  | TyNat       -> false
  | TyId i      -> (i=s)
  | TyArr (a,b) -> (belongs_to s a) || (belongs_to s b)
  | Unk         -> fail_exn "Belongs_to : unknown type";;

let rec free_vars t = match t with 
  | TyBool      -> []
  | TyNat       -> []
  | TyId i      -> [TyId i]
  | TyArr (a,b) -> (free_vars a) @ (free_vars b)
  | Unk         -> fail_exn "Free_vars : unknown type";;

(* Remove doubles from a list, tail-recursive version with sort *)
let uniq_list (l:'a list) =
  let rec uniq_rec m r = match m with 
    | []       -> List.rev r
    | [x]      -> List.rev (x::r)
    | x::y::xs -> if (x = y) then uniq_rec (y::xs) r 
                             else uniq_rec (y::xs) (x::r)
  in uniq_rec (List.sort compare l) [];; 

(* Get the list of free variables in a list of constraints *)
let constraint_free_vars (Cstr c) = 
  let fv = List.fold_left (fun l (u,v) -> 
			     (free_vars u)@(free_vars v)@l) [] c in
    uniq_list fv;;

(* Compute the fixed point of the transformation f *)
let fixed_point (f:ty -> ty) = 
  let rec g x = if (f x = x) then x else g (f x) in g;;

(*************************************************************)
(*                     Unification part                      *)
(*************************************************************)
(* Takes a list of constraints and returns a function on types *)
let solve_constraints (Cstr cs) = 
  let f (x : ty) = x in 
  let rec compute_rec l g = match l with 
    | []        -> g
    | (s,t)::cs -> begin
	if s = t then compute_rec cs g
	else match (s,t) with 
	  | (TyId ss, _) -> 
	      if (not(belongs_to ss t)) 
	      then let tr = simple_transform ss t in
		compute_rec (apply_simple_constraints_transform cs tr) (fun x -> g (tr x))
	      else fail_exn (Printf.sprintf "Impossible to unify %s with %s"
                                            (ty_to_string s) (ty_to_string t))

	  | (_, TyId tt) ->
	      if (not(belongs_to tt s)) 
	      then let tr = simple_transform tt s in
		compute_rec (apply_simple_constraints_transform cs tr) (fun x -> g (tr x))
	      else fail_exn (Printf.sprintf "Impossible to unify %s with %s"
                                            (ty_to_string s) (ty_to_string t))
	  | (TyArr(s1,s2),TyArr(t1,t2)) ->
	      compute_rec ((s1,t1)::(s2,t2)::cs) g
	  | _ -> raise (Exn (Printf.sprintf "Cannot unify %s with %s"
			       (ty_to_string s) (ty_to_string t)))
      end
  in fixed_point (compute_rec cs f);;

(* Global type_inference function
   Arguments  : - a term
   It returns : - a type
                - a fully typed term
                - a list of constraints
                - a renaming function for the constraints *)
let type_infer (t:term) =
  let (ty,_,Cstr c,term) = compute_constraints (Ctxt []) t in
  (* print_endline (term_to_string term); *)
  (* constraints_to_string (Cstr c); *)
  let unif       = solve_constraints (Cstr c) in
  let final_term = apply_rename_term unif term in
  let final_ty   = apply_rename_type unif ty in
  (final_ty, final_term, Cstr c, unif);;

(*************************************************************)
(*                    Parse helpers                          *)
(*************************************************************)
let handle_parse_error lexbuf str exn =
  let curr = lexbuf.Lexing.lex_curr_p in
  let line = curr.Lexing.pos_lnum in
  let cnum = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
  Printf.fprintf stderr "!! Syntax error line %d, col %d\n" line cnum;
  Printf.fprintf stderr "%s\n" str;
  Printf.fprintf stderr "%s^^^\n" (String.make (max (cnum-2) 0) ' ');
  raise exn;;

let parse_term str =
  let lexbuf = Lexing.from_string str in
  try  Type_parser.expr Type_lexer.lex lexbuf
  with exn -> handle_parse_error lexbuf str exn;;

let parse_type str =
  let lexbuf = Lexing.from_string str in
  try  Type_parser.typ  Type_lexer.lex lexbuf
  with exn -> handle_parse_error lexbuf str exn;;

(*************************************************************)
(*             Final diagnostic function                     *)
(*************************************************************)
let display_inference (t:term) =
  print_endline (String.make 50 '-');
  Printf.printf "--- Term : %s\n" (term_to_string t);
  let (final_ty, final_term, Cstr c, unif) = type_infer t in
  (* Printf.printf "--- Free variables : "; *)
  (* display_rename unif (constraint_free_vars (Cstr c)); *)
  (* Printf.printf "--- Assigned variables : "; *)
  (* display_rename unif (constraint_scheme_vars (Cstr c)); *)
  constraints_to_string (Cstr c);
  Printf.printf "--- After unification ";
  constraints_to_string (Cstr (apply_constraints_transform c unif));
  Printf.printf "--- Typed Term : %s\n" (term_to_string final_term);
  Printf.printf "--- Inferred type : %s\n" (ty_to_string final_ty);
  final_ty;
;;

(*********************)
(* Examples of terms *)
(*********************)		    
let rec int_to_term n = if (n == 0) then TmZero
  else TmSucc (int_to_term (n-1));;

let terms = 
  [

    "4";

  ];;

let untypable_terms = 
  [

    "fun x -> (x x)";

  ];;

(*************************************************************)
(*                         Main                              *)
(*************************************************************)
let main =
  let args = (Array.to_list Sys.argv) in
  if (List.length args == 1) then begin
    print_string (bold_string "Tests OK :\n");
    List.iter (fun s -> ignore(display_inference s))
              (List.map parse_term terms);
    print_string (bold_string "\nTests KO :\n");
    List.iter (fun s -> try ignore(display_inference s) with
                          Exn s -> Printf.printf
                                     "!!! Inference failed : %s\n" s)
              (List.map parse_term untypable_terms);
                               end else begin
    ignore (display_inference (parse_term (List.nth args 1)));
                                     end
;;
