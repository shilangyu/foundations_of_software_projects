import Fos.Term
import Fos.Syntax
import Mathlib.Logic.Relation
import Aesop

namespace Fos

inductive IsValue : Term -> Prop
| value_abs : IsValue (Term.t_abs _ _)

/- Call-by-value single step reduction -/
@[aesop unsafe 50% [constructors, cases]]
inductive Reduce : Term -> Term -> Prop
| beta :
    IsValue u ->
      Reduce (Term.t_app (Term.t_abs _ t) u) (t[u])
| ctx_app1 :
  Reduce t t' ->
  Reduce (Term.t_app t u) (Term.t_app t' u)
| ctx_app2 :
  IsValue t ->
  Reduce u u' ->
  Reduce (Term.t_app t u) (Term.t_app t u')

notation:40 t " ~~> " t' => Reduce t t'

def ReduceMany : Term -> Term -> Prop :=
  Relation.ReflTransGen Reduce

notation:40 t " ~~>* " t' => ReduceMany t t'

instance : Trans ReduceMany Reduce ReduceMany where
  trans :=
    Relation.ReflTransGen.tail

instance : Trans ReduceMany ReduceMany ReduceMany where
  trans := Relation.ReflTransGen.trans

instance : Trans Reduce ReduceMany ReduceMany where
  trans a b := Relation.ReflTransGen.trans (Relation.ReflTransGen.single a) b

instance : Trans Reduce Reduce ReduceMany where
  trans a b := Relation.ReflTransGen.tail (Relation.ReflTransGen.single a) b

@[aesop unsafe 50%]
theorem reduce_many_app1 : (t ~~>* t') -> (elaborate ({t}({a})) ~~>* elaborate ({t'}({a}))) := by
  intro h
  induction h
  . exact Relation.ReflTransGen.refl
  . rename_i b c hb hc ih
    apply Relation.ReflTransGen.tail ih
    exact Reduce.ctx_app1 hc

-- Reduce.ctx_app2, but for ReduceMany
@[aesop unsafe 50%]
theorem reduce_many_app2 : IsValue a -> (t ~~>* t') -> (elaborate ({a}({t})) ~~>* elaborate ({a}({t'}))) := by
  intro iv h
  induction h
  . exact Relation.ReflTransGen.refl
  . rename_i b c hb hc ih
    apply Relation.ReflTransGen.tail ih
    exact Reduce.ctx_app2 iv hc

/- Progress: every typeable term is either a value, or can take a reduction step. -/
theorem progress : ∀ t ty, ([] ⊢ t : ty) -> (IsValue t ∨ (∃ t', t ~~> t')) := by
  intro t ty h
  generalize h' : [] = Γ
  rw [h'] at h
  induction h with
  | ty_var x =>
    subst h'
    contradiction
  | ty_abs h ih =>
    left
    constructor
  | ty_app h1 h2 ih1 ih2 =>
    right
    subst h'
    simp [*] at *
    cases ih1 <;> cases ih2
    · rename_i ht _
      cases ht
      rename_i x _ Tx y
      use y[x]
      constructor
      assumption
    · rename_i t2 _ _ t1 _ ht
      have ⟨ t', ht' ⟩ := ht
      use t2.t_app t'
      constructor
      repeat assumption
    · rename_i t1 _ _ t2 ht _
      have ⟨ t', ht' ⟩ := ht
      use t'.t_app t2
      constructor
      repeat assumption
    · rename_i t1 _ _ t2 ht1 ht2
      have ⟨ t1', ht1' ⟩ := ht1
      use t1'.t_app t2
      constructor
      repeat assumption

/- Preservation: every reduction step preserves the type of the term. -/
-- theorem preservation : ∀ t t' Γ ty, has_ty Γ t ty -> (t ~~> t') -> has_ty Γ t' ty:= by
--   sorry -- Coming in the second part of the lab!

end Fos
