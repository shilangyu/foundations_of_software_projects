namespace Fos

-- Question 0: Absurdity Implies False
def False := ∀ (α : Prop), α
def negation := λ (P : Prop) => P -> False

-- Write a lambda-term of the following type
def Q0 : ∀ (P : Prop), P → (negation P) → False :=
  fun _ => fun p => fun np => np p

def True := ∀ (α : Prop), α → α

-- Question 1: Double Negation Introduction
-- Prove that for any proposition P, P implies ¬¬P.
-- Write a lambda term that has the following type:
def Q1 : ∀ (P : Prop), P → (negation (negation P)) :=
  fun _ => fun p => fun np => np p

-- Play with Equality:
-- Definition of Leibniz Equality
def LeibnizEq :=
  λ (α : Type _) (x y : α) =>
  ∀ (P : α → Prop), P x → P y

theorem leibniz_refl : ∀ {α : Type _} {x : α}, LeibnizEq α x x :=
  fun _ => fun hPx => hPx

-- Question 2: Symmetry of Equality
-- Write a lambda-term that has the following type
theorem leibniz_symm : ∀ (α : Type _) (x y : α), LeibnizEq α x y -> LeibnizEq α y x :=
  fun α => fun x => fun _ => fun hXy =>
    hXy (fun z => LeibnizEq α z x) leibniz_refl


-----------------------------------
-- Existentials
---------------------------------

-- We define the following term of the calculus of construction:
def ExistsP := λ (T : Type) (P : T → Prop) =>
  ∀ (α : Prop), (∀ (x : T), P x → α) → α
-- ExistsP T P morally states that there exists a value of type T that verifies predicate P.

-- Question 5: Introduction Rule for Encoded Existential
-- Given a type T, a predicate P : T → Prop, a specific witness w : T, and a proof hPw : P w that P holds for w,
-- it should be the case that ExistsP T P holds.

-- To prove that theorem, write a lambda term that has the following type:
def Q5 : ∀ (T : Type) (P : T → Prop) (w : T), P w → ExistsP T P :=
  fun _ => fun _ => fun w => fun hPw => fun _ => fun h => h w hPw

-- Question 6: Elimination Rule for Encoded Existential
theorem Q6 : ∀ (T : Type) (P : T → Prop) (Q : Prop),
  ExistsP T P → (∀ (x : T), P x → Q) → Q :=
  fun _ => fun _ => fun Q => fun hEx => fun hP =>
    hEx Q (fun x hPx => hP x hPx)

-- Question 7: De Morgan's Law for Encoded Existential (One Direction)
-- Write a lambda-term that prove that if ExistsP T P is false, then for all x : T, P x must be false.
-- In other words, write a lambda term of the following type (Hint: you can use Q5):

theorem Q7 : ∀ (T : Type) (P : T → Prop),
  (negation (ExistsP T P)) →
  (∀ (x₀ : T), negation (P x₀)) :=
  fun T => fun P => fun hnEx =>
    fun x₀ => fun hPx₀ =>
      hnEx (Q5 T P x₀ hPx₀)
