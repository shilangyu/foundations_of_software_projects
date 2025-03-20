import Fos.Term
namespace Fos

/-
A easy-to-write syntax for the language with variables as strings.
-/
inductive Syntax where
| s_var : String -> Syntax
| s_lam : String -> type -> Syntax -> Syntax
| s_app : Syntax -> Syntax -> Syntax
| s_value : Term -> Syntax

/-
A coercion from strings to the syntax, so that you can write `"x"` to mean `Syntax.s_var "x"`.
-/
instance : Coe String Syntax where
  coe s := Syntax.s_var s

notation "λ" n ":" ty " => " t => Syntax.s_lam n ty t
notation t1 "(" t2 ")" => Syntax.s_app t1 t2
notation "{" t "}" => Syntax.s_value t

@[simp]
def lookupName (n : String) : List String -> Option Nat
| [] => none
| x :: xs => if x = n then some 0 else
  match lookupName n xs with
  | some n => some (n + 1)
  | none => none

/-
Elaborate the `Syntax` to the debruijn-indexed `Term` given a context of variable names.
-/
@[simp]
def elaborate' (ctx : List String) : Syntax -> Term
| Syntax.s_var n => Term.t_var (lookupName n ctx).get!
| Syntax.s_lam n ty t =>
  Term.t_abs ty (elaborate' (n :: ctx) t)
| Syntax.s_app t1 t2 =>
  Term.t_app (elaborate' ctx t1) (elaborate' ctx t2)
| Syntax.s_value t =>
  t

@[simp]
def elaborate (s : Syntax) : Term :=
  elaborate' [] s

section Examples

def typeNum := (∘1 ⇒ ∘1) ⇒ ∘1 ⇒ ∘1
def zero : Term := elaborate (λ "s": ∘1 ⇒ ∘1 => λ "z": ∘1 => "z")
def succ : Term :=
  elaborate (λ "n": typeNum => λ "s": (∘1 ⇒ ∘1) => λ "z": ∘1 => "s"("n"("s")("z")))
def one : Term :=
  elaborate ({succ}({zero}))

end Examples

end Fos
