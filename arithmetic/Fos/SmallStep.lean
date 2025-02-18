import Fos.Term
import Fos.Eval
namespace Fos

/-
Inductive definition of `isNumericalVal`.
-/
inductive IsNumericalVal : Term -> Prop where
  | zero_val : IsNumericalVal Term.t_zero
  | succ_val :
    IsNumericalVal t ->
    IsNumericalVal (Term.t_succ t)

/-
Inductive definition of `isBoolVal`.
-/
inductive IsBoolVal : Term -> Prop where
  | true_val : IsBoolVal Term.t_true
  | false_val : IsBoolVal Term.t_false

/-
Inductive definition of `isVal`.
-/
inductive IsVal : Term -> Prop where
  | n_val :
    IsNumericalVal t ->
    IsVal t
  | b_val :
    IsBoolVal t ->
    IsVal t

/-
Inductive definition of small-step reduction.
-/
inductive Smallstep : Term -> Term -> Prop where
  | if_true :
    Smallstep (Term.t_if Term.t_true t1 t2) t1
  | if_false :
    Smallstep (Term.t_if Term.t_false t1 t2) t2
  | iszero_zero :
    Smallstep (Term.t_iszero Term.t_zero) Term.t_true
  | iszero_succ :
    IsNumericalVal t ->
    Smallstep (Term.t_iszero (Term.t_succ t)) Term.t_false
  | pred_zero :
    Smallstep (Term.t_pred Term.t_zero) Term.t_zero
  | pred_succ :
    IsNumericalVal t ->
    Smallstep (Term.t_pred (Term.t_succ t)) t
  | if_step :
    Smallstep t1 t1' ->
    Smallstep (Term.t_if t1 t2 t3) (Term.t_if t1' t2 t3)
  | iszero_step :
    Smallstep t t' ->
    Smallstep (Term.t_iszero t) (Term.t_iszero t')
  | pred_step :
    Smallstep t t' ->
    Smallstep (Term.t_pred t) (Term.t_pred t')
  | succ_step :
    Smallstep t t' ->
    Smallstep (Term.t_succ t) (Term.t_succ t')

notation:50 t " ~~> " t' => Smallstep t t'

/-!
Reflexive and transitive closure of `Smallstep`.
-/
inductive Smallsteps : Term -> Term -> Prop where
| refl :
  Smallsteps t t
| step :
  Smallstep t t' ->
  Smallsteps t' t'' ->
  Smallsteps t t''

notation:50 t " ~~>* " t' => Smallsteps t t'

/-
`IsNumericalVal` implies `isNumericalVal` is true.
-/
theorem num_val_true
  (h : IsNumericalVal t) :
  isNumericalVal t = true := by
  sorry

/-
Evaluating a numerical value yields the same result as the value itself.
-/
theorem num_val_eval
  (h : IsNumericalVal t) :
  eval t = EvalResult.Ok t := by
  sorry

/-
Evaluating a boolean value yields the same result as the value itself.
-/
theorem bool_val_eval
  (h : IsBoolVal t) :
  eval t = EvalResult.Ok t := by
  sorry

/-
Evaluating a value yields the same result as the value itself.
-/
theorem val_eval
  (h : IsVal t) :
  eval t = EvalResult.Ok t := by
  sorry

/-
Reducing a term preserves the result of evaluation.
-/
theorem smallstep_eval
  (hr : t ~~> t') :
  eval t = eval t' := by
  sorry

/-
A numerical value cannot be further reduced.
-/
theorem smallstep_nval_absurd
  (hv : IsNumericalVal t) :
  (t ~~> t') -> False := by
  sorry

/-
A boolean value cannot be further reduced.
-/
theorem smallstep_bval_absurd
  (hv : IsBoolVal t) :
  (t ~~> t') -> False := by
  intro hr
  cases hv
  case b_true => cases hr
  case b_false => cases hr

/-
A value cannot be further reduced.
-/
theorem smallstep_val_absurd
  (hv : IsVal t) :
  (t ~~> t') -> False := by
  sorry

theorem smallsteps_val
  (hv : IsVal t)
  (hr : t ~~>* t') :
  t' = t := by
  sorry

/-
If a term can be reduced to a value, then evaluating the term yields the same result.
-/
theorem smallsteps_eval
  (hr : t ~~>* t')
  (hv : IsVal t') :
  eval t = EvalResult.Ok t' := by
  sorry

end Fos
