import Fos.Term
import Fos.Substitution
import Fos.Reduce
namespace Fos

/-
# Confluence

A reduction system can have different ways to reduce the same term. For instance, our calculus has the following two ways to reduce the same term:
```
(λ x => x x) (λ y => (λ z => z) y)  ~~>  (λ x => x x) (λ y => y)
(λ x => x x) (λ y => (λ z => z) y)  ~~>  (λ y => (λ z => z) y) (λ y => (λ z => z) y)
```
The first reduction uses the `ctx_app2` rule, while the second reduction uses the `beta` rule.

Therefore, starting from the identical term `t`, the reduction may diverge (`t ~~>* t1` and `t ~~>* t2`). However, if the reduction system is *confluent*, there is always a common term `t'` to which both reduction converges, i.e. `t1 ~~>* t'` and `t2 ~~>* t'`.

The task of this exercise is to show the reduction system of our untyped lambda calculus is confluent, as defined by the following:
-/
def ReduceMany.Confluence : Prop :=
  ∀ t t1 t2,
    (t ~~>* t1) -> (t ~~>* t2) ->
    ∃ t', (t1 ~~>* t') ∧ (t2 ~~>* t')

/-
We first define parallel reduction, `ParReduce`, as an intermediate step in the proof:
-/
inductive ParReduce : Term -> Term -> Prop
| var :
  ParReduce (Term.t_var n) (Term.t_var n)
| beta :
  ParReduce t t' ->
  ParReduce u u' ->
  ParReduce
    (Term.t_app (Term.t_abs t) u)
    (t'[u'])
| ctx_abs :
  ParReduce t t' ->
  ParReduce (Term.t_abs t) (Term.t_abs t')
| ctx_app :
  ParReduce t t' ->
  ParReduce u u' ->
  ParReduce (Term.t_app t u) (Term.t_app t' u')

notation:80 t " ~~>p " t' => ParReduce t t'
/-
The plan is that
(1) we first show that `ParReduce` is confluent, which will be much easier than directly establishing the confluence of the original reduction relation;
(2) then we prove the confluence of `ReduceMany` by establishing the equivalence between `~~>*` and `~~>p*`.

Let's get started!

## `ParReduce` is Confluent

We will do this step-by-step: proving the intermediate results one-by-one which eventually leads to the confluence of `ParReduce`.

The first task is to show that `ParReduce` is reflexive:
-/
theorem ParReduce.refl :
  t ~~>p t := by
  induction t <;> constructor <;> assumption

/-
Next, we define a "normalization" of a term, which applies beta-reductions to the term as much as possible.
-/
def Term.norm : Term -> Term
| t_var n => t_var n
| t_abs t => t_abs (t.norm)
| t_app (t_abs t) u => t.norm[u.norm]
| t_app t u => t_app (t.norm) (u.norm)

/-
The goal is to prove the following *triangle* property of `ParReduce`: if we have `t ~~>p t'`, then `t'` will eventually reduce to the normal form of `t` (i.e. `t.norm`).
-/
def ParReduce.Triangle : Prop := ∀ {t t' : Term} (_ : t ~~>p t'), t' ~~>p t.norm

/-
Hint: the following lemma on substitution will be useful in the proof of the theorems in the rest of this exercise. It shows how beta reduction and substitution commute.
-/
#check Term.subst_zero_subst_commute

/-
To prove `ParReduce.Triangle`, we need a series of lemmas. This is the first one: substitution preserves parallel reduction.
-/
def ParReduce.subst_term
  (h : t ~~>p t') :
  (t.subst s) ~~>p (t'.subst s) := by
  induction h generalizing s
  · exact ParReduce.refl
  · rw [Term.subst_zero_subst_commute]
    rename_i ihs ihu
    constructor
    apply ihs
    apply ihu
  · constructor
    rename_i ih
    apply ih
  · rename_i iht ihu
    constructor
    apply iht
    apply ihu


/-
Next, we show that if there are two substitutions, `s1` and `s2`, and for any `i` in the domain of `s1` and `s2` we have `(s1 i) ~~>p (s2 i)`, then they preserve parallel reduction as well in the sense that any `t1 ~~>* t2` implies `(t1.subst s1) ~~>* (t2.subst s2)`.

Complete the proof of the following two lemmas. The proof of `ParReduce.subst` will require `Subst.lift_reduceTo`.
-/
def Subst.ReduceTo (s1 s2 : Subst) : Prop :=
  ∀ i, s1 i ~~>p s2 i
theorem Subst.lift_reduceTo
  (h : Subst.ReduceTo s1 s2) :
  Subst.ReduceTo (s1.lift) (s2.lift) := by
  intro i
  cases i with
  | zero => exact ParReduce.refl
  | succ n =>
    simp [Subst.lift, Term.rename_toSubst]
    apply ParReduce.subst_term
    exact h n

theorem ParReduce.subst
  (h1 : t ~~>p t')
  (h2 : Subst.ReduceTo s1 s2) :
  (t.subst s1) ~~>p (t'.subst s2) := by
  induction h1 generalizing s1 s2
  · apply h2
  · rw [Term.subst_zero_subst_commute]
    rename_i h1_ih1 h1_ih2
    constructor
    apply h1_ih1
    apply Subst.lift_reduceTo h2
    apply h1_ih2
    assumption
  · rename_i h1_ih
    constructor
    apply h1_ih
    apply Subst.lift_reduceTo h2
  · rename_i h1_ih1 h1_ih2
    constructor
    apply h1_ih1 h2
    apply h1_ih2 h2

/-
Then we obtain the following corollary: beta reduction preserves parallel reduction.
-/
theorem Subst.subst_zero_reduceTo
  (hr : t ~~>p t') :
  Subst.ReduceTo (Subst.subst_zero t) (Subst.subst_zero t') := by
  intro i
  cases i
  case zero => simp [Subst.subst_zero]; apply hr
  case succ i0 => simp [Subst.subst_zero]; apply ParReduce.refl
theorem ParReduce.subst_zero
  (h1 : t ~~>p t')
  (h2 : u ~~>p u') :
  t[u] ~~>p t'[u'] := by
  apply ParReduce.subst
  apply h1
  apply Subst.subst_zero_reduceTo h2

/-
And now we are ready to prove the triangle property of `ParReduce`. Complete the following proof.
-/
theorem ParReduce.triangle'
  (hr : t ~~>p t1) :
  t1 ~~>p t.norm := by
  induction hr
  case var => apply ParReduce.refl
  case beta =>
    apply ParReduce.subst_zero
    repeat assumption
  case ctx_abs =>
    constructor
    assumption
  case ctx_app t t' u u' hr1 ih1 hr2 ih2 =>
    cases hr1 <;> simp [Term.norm] at *
    · constructor <;> assumption
    · constructor <;> assumption
    · constructor
      · cases hr2
        assumption
      · assumption
    · constructor <;> assumption

theorem ParReduce.triangle : ParReduce.Triangle := by
  intro t t' h
  apply ParReduce.triangle' h

/-
Now we are ready to prove the confluence of `ParReduce`.
-/
theorem ParReduce.confluence
  (h1 : t ~~>p t1)
  (h2 : t ~~>p t2) :
  ∃ t', (t1 ~~>p t') ∧ (t2 ~~>p t') := by
  use t.norm
  exact ⟨ParReduce.triangle h1, ParReduce.triangle h2⟩

/-
In the following, we first define the reflexive-transitive closure of `ParReduce`, `ParReduceMany`, and then show that the confluence of `ParReduce` implies the confluence of `ParReduceMany`.
-/
def ParReduceMany : Term -> Term -> Prop :=
  Relation.ReflTransGen ParReduce

notation:80 t " ~~>p* " t' => ParReduceMany t t'

/-
Finish the following two theorems.
-/
def ParReduceMany.confluence_left
  (h1 : t ~~>p* t1)
  (h2 : t ~~>p t2) :
  ∃ u, (t1 ~~>p u) ∧ (t2 ~~>p* u) := by
  induction h1 with
  | refl => exact ⟨t2, h2, Relation.ReflTransGen.refl⟩
  | tail h1 h1' ih =>
    have ⟨u, h1u, h2u⟩ := ih
    have ⟨v, h1v, h2v⟩ := ParReduce.confluence h1' h1u
    use v
    apply And.intro
    · assumption
    · exact Relation.ReflTransGen.tail h2u h2v

def ParReduceMany.confluence
  (h1 : t ~~>p* t1)
  (h2 : t ~~>p* t2) :
  ∃ u, (t1 ~~>p* u) ∧ (t2 ~~>p* u) := by
  induction h2 with
  | refl => exact ⟨t1, Relation.ReflTransGen.refl, h1⟩
  | tail h2 h2' ih =>
    have ⟨v, h1v, h2v⟩ := ih
    have ⟨u, h1u, h2u⟩ := ParReduceMany.confluence_left h2v h2'
    use u
    apply And.intro
    · exact Relation.ReflTransGen.tail h1v h1u
    · assumption

/-
## `~~>*` and `~~>p*` are Equivalent

Now we arrive at the second step of our plan: establishing the equivalence between `~~>*` and `~~>p*`.

First, we can go from `~~>` to `~~>p`.
-/
theorem Reduce.toParReduce
  (h : t ~~> t') :
  t ~~>p t' := by
  induction h <;> constructor <;> repeat (first | assumption | exact ParReduce.refl)

/-
Then, we show that we can go from `~~>` to `~~>p*`.

The following lemmas are useful for the proof.
-/
theorem ReduceMany.ctx_abs
  (h : t ~~>* t') :
  .t_abs t ~~>* .t_abs t' := by
  induction h with
  | refl => constructor
  | tail h ht ih =>
    apply Relation.ReflTransGen.tail ih
    constructor
    assumption

theorem ReduceMany.ctx_app1
  (h1 : t1 ~~>* t1') :
  .t_app t1 t2 ~~>* .t_app t1' t2 := by
  induction h1 with
  | refl => constructor
  | tail h1 ht ih =>
    apply Relation.ReflTransGen.tail ih
    constructor
    assumption

theorem ReduceMany.ctx_app2
  (h2 : t2 ~~>* t2') :
  .t_app t1 t2 ~~>* .t_app t1 t2' := by
  induction h2 with
  | refl => constructor
  | tail h2 ht ih =>
    apply Relation.ReflTransGen.tail ih
    constructor
    assumption

/-
Now, prove that we can go from `~~>p` to `~~>*`.
-/
theorem ParReduce.toReduceMany
  (h : t ~~>p t') :
  t ~~>* t' := by
  induction h with
  | var => constructor
  | beta h1 h2 ih1 ih2 =>
    rename_i t t' u u'
    calc
      _ ~~>* t'.t_abs.t_app u := by simp [ReduceMany.ctx_app1, ReduceMany.ctx_abs, *]
      _ ~~>* t'.t_abs.t_app u' := by simp [ReduceMany.ctx_app2, *]
      _ ~~> t'[u'] := by constructor
  | ctx_abs h ih =>
    exact ReduceMany.ctx_abs ih
  | ctx_app h1 h2 ih1 ih2 =>
    rename_i t t' u u'
    calc
      _ ~~>* t'.t_app u := by simp [ReduceMany.ctx_app1, *]
      _ ~~>* t'.t_app u' := by simp [ReduceMany.ctx_app2, *]

/-
Then, it follows that `~~>*` can be converted to `~~>p*`.
-/
theorem ReduceMany.toParReduceMany
  (h : t ~~>* t') :
  t ~~>p* t' := by
  induction h with
  | refl => constructor
  | tail h ht ih =>
    apply Relation.ReflTransGen.tail ih
    apply Reduce.toParReduce ht

/-
Finally, we can show that `~~>p*` can be converted to `~~>*`, and therefore the equivalence.
-/
theorem ParReduceMany.toReduceMany
  (h : t ~~>p* t') :
  t ~~>* t' := by
  induction h with
  | refl => constructor
  | tail h ht ih =>
    have hp := ParReduce.toReduceMany ht
    exact Relation.ReflTransGen.trans ih hp

/-
## Final Result: `~~>*` is Confluent!

With all the established results, we can finally prove that `~~>*` is confluent. Finish the last piece of this puzzle!
-/
theorem ReduceMany.confluence : Confluence := by
  unfold Confluence
  intro t t1 t2 h1 h2
  have h1' := ReduceMany.toParReduceMany h1
  have h2' := ReduceMany.toParReduceMany h2
  have ⟨t', h1t', h2t'⟩ := ParReduceMany.confluence h1' h2'
  use t'
  exact ⟨ParReduceMany.toReduceMany h1t', ParReduceMany.toReduceMany h2t'⟩

/-
Voila! Starting from zero, and building up intermediate results, we have finally established the confluence of `~~>*`!
-/

end Fos
