namespace Fos

/-
Abstract syntax tree of the language.
-/
inductive Term : Type where
| t_zero : Term
| t_pred : Term -> Term
| t_succ : Term -> Term
| t_iszero : Term -> Term
| t_if : Term -> Term -> Term -> Term
| t_true : Term
| t_false : Term

/-
Notation for the language.
-/
notation:max "#t" => Term.t_true
notation:max "#f" => Term.t_false
notation:max "#0" => Term.t_zero
notation:40 "succ " t => Term.t_succ t
notation:40 "pred " t => Term.t_pred t
notation:40 "iszero? " t => Term.t_iszero t
notation:50 "#if " c " #then " t1 " #else " t2 => Term.t_if c t1 t2

/-
Check whether a term is a numerical value.
-/
def isNumericalVal : Term -> Bool
  | Term.t_zero => true
  | Term.t_succ t => isNumericalVal t
  | _ => false

/-
Check whether a term is a boolean value.
-/
def isBoolVal : Term -> Bool
  | Term.t_true | Term.t_false => true
  -- TODO: should iszero? be a boolean value?
  | _ => false

/-
Check whether a term is a value.
-/
def isVal (t : Term) : Bool :=
  isNumericalVal t || isBoolVal t

namespace Examples

#check #t
#check succ #0
#check succ succ succ #0
#check iszero? (#if iszero? #0 #then succ #0 #else succ succ #0)
#check succ succ pred pred #0

end Examples

end Fos
