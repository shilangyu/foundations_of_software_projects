namespace Fos

/-
The types present in the language.
-/
inductive type where
  | Base (n: Nat)
  | Arrow: type -> type -> type
deriving DecidableEq

prefix:max "∘" => type.Base
infixr:60 "⇒" => type.Arrow

#check ∘1 ⇒ ∘1 ⇒ ∘2

/-
Abstract syntax tree of the language.
-/
inductive Term : Type where
| t_var : Nat -> Term
| t_abs : type -> Term -> Term
| t_app : Term -> Term -> Term

def Rename : Type := Nat -> Nat
def Subst : Type := Nat -> Term

@[simp]
def Rename.comp (f : Rename) (g : Rename) : Rename := fun x => g (f x)

@[simp]
def Rename.lift (f : Rename) : Rename
| 0 => 0
| n+1 => (f n)+1

@[simp]
def Term.rename (t : Term) (f : Rename) : Term :=
  match t with
  | t_var n => t_var (f n)
  | t_abs ty t => t_abs ty (t.rename f.lift)
  | t_app t1 t2 => t_app (t1.rename f) (t2.rename f)

@[simp]
def Subst.lift (s : Subst) : Subst
| 0 => .t_var 0
| n+1 => (s n).rename Nat.succ

@[simp]
def Term.subst (t : Term) (s : Subst) : Term :=
  match t with
  | t_var n => s n
  | t_abs ty t => t_abs ty (t.subst s.lift)
  | t_app t1 t2 => t_app (t1.subst s) (t2.subst s)

@[simp]
def Subst.subst_zero (t : Term) : Subst
| 0 => t
| n+1 => .t_var n

/-
Substitutes the zero-indexed variable with the given term.
-/
@[simp]
def Term.subst_zero (t : Term) (u : Term) : Term :=
  t.subst (Subst.subst_zero u)

/-
Notation for substitution.
-/
notation:70 t "[" u "]" => Term.subst_zero t u

/-
The typing judgement of the system.
-/
inductive has_ty : (List type) -> Term -> type -> Prop where
  | ty_abs :
      has_ty (T1 :: Γ) t2 T2 ->
      has_ty Γ (Term.t_abs T1 t2) (T1 ⇒ T2)
  | ty_var :
      Γ.idxOf? T = some x ->
      has_ty Γ (Term.t_var x) T
  | ty_app :
      has_ty Γ t1 (T11 ⇒ T12) ->
      has_ty Γ t2 T11 ->
      has_ty Γ (Term.t_app t1 t2) T12

notation:50 env " ⊢ " t " : " ty => has_ty env t ty
