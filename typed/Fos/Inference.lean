import Fos.Term
namespace Fos

/- Calculates a given term's type, given an existing environment. -/
@[simp]
def infer (env : List type) (t : Term) : Option type :=
  match t with
  | .t_var x => env[x]?
  | .t_abs ty t => match infer (ty :: env) t with
    | .some ty' => .some (ty ⇒ ty')
    | _ => none
  | .t_app t1 t2 => match infer env t1, infer env t2 with
    | .some (ty1 ⇒ ty2), .some ty1' => if ty1 = ty1' then .some ty2 else none
    | _, _ => none

/- Prove `infer` produces the correct type. -/
theorem infer_is_correct : ∀ t Γ ty, infer Γ t = .some ty -> Γ ⊢ t : ty := by
  intro t Γ ty h
  induction t generalizing Γ ty with
  | t_var x =>
    simp at h
    constructor
    assumption
  | t_abs ty' t ih =>
    simp at h
    cases eq : infer (ty' :: Γ) t with
    | some ty'' =>
      simp [eq] at h
      subst h
      constructor
      apply ih
      assumption
    | none => simp [eq] at h
  | t_app t1 t2 ih1 ih2 =>
    simp at h
    cases eq1 : infer Γ t1 with
    | some ty' =>
      cases eq2 : infer Γ t2 with
      | some ty'' =>
        cases ty' <;> simp [eq1, eq2] at h
        have ⟨ p1, p2 ⟩ := h
        subst p1 p2
        rename_i t_arg t_body
        apply has_ty.ty_app (ih1 _ _ eq1) (ih2 _ _ eq2)
      | none => simp [eq1, eq2] at h
    | none => simp [eq1] at h

/- Prove that every typeable term can be `infer`red. -/
theorem infer_is_complete : ∀ t Γ ty, (Γ ⊢ t : ty) -> infer Γ t = .some ty := by
  intro t Γ ty h
  induction h with
  | ty_var h =>
    assumption
  | ty_abs h ih =>
    simp [ih]
  | ty_app h1 h2 ih1 ih2 =>
    simp [ih1, ih2]

/- Prove that typing judgements always produce the same type for every term. -/
theorem typing_is_unique : (Γ ⊢ t : ty1) -> (Γ ⊢ t : ty2) -> ty1 = ty2 := by
  intro h1 h2
  have eq1 := infer_is_complete _ _ _ h1
  have eq2 := infer_is_complete _ _ _ h2
  rw [eq1] at eq2
  injection eq2

end Fos
