(*************************************************************)
(* Simple grammar for types, all beginning with Ty.          *)
(*************************************************************)
type id = string    (* Identifiers *)

type ty =    (* Unquantified types *)
  | TyBool | TyNat
  | TyArr  of ty * ty
  | TyId   of id
  | Unk

type ty_trans = ty -> ty

(*************************************************************)
(* Simple grammar for terms, all beginning with Tm.  Can happily mix
   typed and unyped expression, as in OCaml.  For all typed versions,
   the ty argument is the type of the expression, except for the typed
   let version where the first argument is the type of the "let"
   variable and the second the type of the result expression.

   By default, unknown types are typed by Unk. 
 *)
(*************************************************************)
type term =
  | TmTrue | TmFalse
  | TmZero | TmSucc of term
  | TmIf   of term * term * term * ty    (* Conditional *)
  | TmVar  of id * ty                    (* Variable *)
  | TmAbs  of id * ty * term             (* Abstraction *)
  | TmApp  of term * term                (* Application *)

let rec int_to_term n = if (n == 0) then TmZero
			else TmSucc (int_to_term (n-1));;
