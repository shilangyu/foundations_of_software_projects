import Fos.Term
namespace Fos

def Subst.onTerm (s : Subst) : Term -> Term :=
  fun t => t.subst s

def Subst.comp (s1 : Subst) (s2 : Subst) : Subst :=
  fun i => s2.onTerm (s1 i)

def Subst.id : Subst := fun i => .t_var i

def Subst.shift : Subst := fun i => .t_var (i+1)

def Subst.liftN (s : Subst) : Nat -> Subst
| 0 => s
| n+1 => (s.liftN n).lift

def Rename.liftN (f : Rename) : Nat -> Rename
| 0 => f
| n+1 => (f.liftN n).lift

def Rename.toSubst (f : Rename) : Subst :=
  fun i => .t_var (f i)

def Rename.lift_toSubst {f : Rename} :
  (f.lift.toSubst) = (f.toSubst.lift) := by
  funext i
  cases i <;> rfl

theorem Term.rename_toSubst {t : Term} :
  (t.rename f) = (t.subst f.toSubst) := by
  induction t generalizing f
  case t_var i =>
    simp [Term.rename, Term.subst, Rename.toSubst]
  case t_abs ih =>
    simp [Term.rename, Term.subst, Rename.toSubst]
    simp [<-Rename.lift_toSubst]
    simp [ih]
  case t_app ih1 ih2 =>
    simp [Term.rename, Term.subst, ih1, ih2]

def Rename.lift_id :
  (Rename.lift (fun i => i)) = (fun i => i) := by
  funext i
  cases i
  case zero => simp [Rename.lift]
  case succ i0 => simp [Rename.lift]

def Term.rename_id {t : Term} :
  t.rename (fun i => i) = t := by
  induction t
  case t_var => simp [Term.rename]
  case t_abs t ih => simp [Term.rename, Rename.lift_id, ih]
  case t_app t1 t2 ih1 ih2 => simp [Term.rename, ih1, ih2]

def Rename.comp_lift {f g : Rename} :
  (f.lift.comp g.lift) = (f.comp g).lift := by
  funext i
  cases i
  case zero => simp [Rename.lift, Rename.comp]
  case succ i0 => simp [Rename.lift, Rename.comp]

def Term.comp_rename {t : Term} {f g : Rename} :
  (t.rename f).rename g = t.rename (f.comp g) := by
  induction t generalizing f g
  case t_var => simp [Term.rename, Rename.comp]
  case t_abs t ih => simp [Term.rename, Rename.comp_lift, ih]
  case t_app t1 t2 ih1 ih2 => simp [Term.rename, ih1, ih2]

def Subst.liftN_weaken {s : Subst} {n i : Nat} :
  (s i).rename (fun i => i + n) = (s.liftN n (i+n)) := by
  induction n
  case zero =>
    simp [Term.rename, Subst.liftN]
    simp [Term.rename_id]
  case succ n ih =>
    simp [Subst.liftN]
    rw [<- Nat.add_assoc]
    simp [Subst.lift]
    have h : (fun i => i + (n + 1)) = (Rename.comp (fun i => i + n) (fun i => i + 1)) := by
      funext i
      ac_rfl
    rw [h]
    simp [<- Term.comp_rename]
    simp [ih]

def Subst.liftN_lt {s : Subst} {n : Nat} {i : Nat}
  (hlt : i < n) :
  (s.liftN n i) = .t_var i := by
  induction n generalizing i
  case zero => contradiction
  case succ n ih =>
    cases i
    case zero => simp [Subst.liftN, Subst.lift]
    case succ i0 =>
      simp [Subst.liftN, Subst.lift]
      have h : i0 < n := by
        apply Nat.lt_of_succ_lt_succ hlt
      rw [ih h]
      rfl

def Rename.liftN_lt {f : Rename} {n : Nat} {i : Nat}
  (hlt : i < n) :
  (f.liftN n i) = i := by
  induction n generalizing i
  case zero => contradiction
  case succ n ih =>
    cases i
    case zero => simp [Rename.liftN, Rename.lift]
    case succ i0 =>
      simp [Rename.liftN, Rename.lift]
      have h : i0 < n := by
        apply Nat.lt_of_succ_lt_succ hlt
      rw [ih h]

def Rename.succ_liftN_ge {n i : Nat} (hge : n ≤ i) :
  (Rename.liftN Nat.succ n i) = i.succ := by
  induction n generalizing i
  case zero => simp [Rename.liftN]
  case succ n0 ih =>
    cases i
    case zero => contradiction
    case succ i0 =>
      simp [Rename.liftN]
      simp [Rename.lift]
      have hge' : n0 ≤ i0 := by
        apply Nat.le_of_succ_le_succ hge
      rw [ih hge']

theorem Nat.ge_implies_exists_add {n m : Nat}
  (hge : n ≥ m):
  ∃ k, n = m + k := by
  induction hge
  case refl => exists 0
  case step n0 hle0 ih =>
    rcases ih with ⟨k, hk⟩
    exists k.succ
    rw [hk]
    rfl

theorem Subst.liftN_ge {s : Subst} {n i k : Nat}
  (hge : i = n + k) :
  (s.liftN n i) = (s k).rename (fun i => i + n) := by
  induction n generalizing i k
  case zero =>
    simp [Subst.liftN, Term.rename_id]
    have h : i = k := by
      rw [hge]
      ac_rfl
    simp [h]
  case succ n0 ih =>
    cases i
    case zero =>
      symm at hge
      have h := Nat.eq_zero_of_add_eq_zero_right hge
      contradiction
    case succ i0 =>
      have hge' : i0 = n0 + k := by
        rw [Nat.succ_add] at hge
        cases hge
        rfl
      simp [Subst.liftN, Subst.lift]
      simp [ih hge']
      simp [Term.comp_rename]
      congr

theorem Rename.liftN_succ_ge {n : Nat} {i : Nat} :
  (Rename.liftN Nat.succ n (i + n)) = (i + n).succ := by
  induction n generalizing i
  case zero =>
    simp [Rename.liftN]
  case succ n0 ih =>
    simp [Rename.liftN, Rename.lift]
    rw [ih]
    ac_rfl

theorem Rename.weakenN_liftN_weaken {n : Nat} :
  (Rename.comp (fun i => i + n) (Rename.liftN Nat.succ n)) = (fun i => i + n + 1) := by
  funext i0
  simp [comp]
  rw [Rename.liftN_succ_ge]

theorem Term.subst_weaken_comm' {t : Term} {s : Subst} :
  (t.subst (s.liftN n)).rename (Rename.liftN Nat.succ n) = (t.rename (Rename.liftN Nat.succ n)).subst (s.liftN (n+1)) := by
  induction t generalizing n
  case t_var i =>
    simp [Term.subst, Term.rename, Subst.liftN, Rename.liftN]
    cases Nat.lt_or_ge i n
    case inl h =>
      simp [Subst.liftN_lt h]
      simp [Rename.liftN_lt h]
      simp [Term.rename]
      simp [Rename.liftN_lt h]
      have heq : (s.liftN n).lift i = (s.liftN (n+1)) i := rfl
      rw [heq]
      have h' : i < n + 1 := by
        apply Nat.lt_succ_of_lt h
      simp [Subst.liftN_lt h']
    case inr h =>
      have ⟨k, hge⟩ := Nat.ge_implies_exists_add h
      simp [Rename.succ_liftN_ge h]
      simp [Subst.liftN_ge hge]
      simp [Term.comp_rename]
      simp [Rename.weakenN_liftN_weaken]
      have heq : (s.liftN (n+1)) (i+1) = (s.liftN (n)).lift (i+1) := by rfl
      rw [<-heq]
      have hge' : i + 1 = (n + 1) + k := by
        simp [hge]
        ac_rfl
      simp [Subst.liftN_ge hge']
      rfl
  case t_abs ih =>
    simp [Term.subst, Term.rename]
    have ih := ih (n:=n+1)
    exact ih
  case t_app ih1 ih2 =>
    simp [Term.subst, Term.rename]
    simp [ih1, ih2]

def Term.subst_weaken_comm {t : Term} {s : Subst} :
  (t.subst s).rename Nat.succ = (t.rename Nat.succ).subst s.lift :=
  Term.subst_weaken_comm' (n:=0)

def Subst.comp_lift {s1 s2 : Subst} :
  (s1.comp s2).lift = s1.lift.comp s2.lift := by
  funext i
  cases i
  case zero => simp [Subst.lift, Subst.comp, Subst.onTerm, Term.subst]
  case succ i0 =>
    simp [Subst.lift, Subst.comp, Subst.onTerm, Term.subst]
    simp [Term.subst_weaken_comm]

def Term.comp_subst {t : Term} {s1 s2 : Subst} :
  (t.subst s1).subst s2 = t.subst (s1.comp s2) := by
  induction t generalizing s1 s2
  case t_var =>
    simp [Term.subst, Subst.comp, Subst.onTerm]
  case t_abs t ih =>
    simp [Term.subst]
    rw [ih]
    simp [Subst.comp_lift]
  case t_app t1 t2 ih1 ih2 =>
    simp [Term.subst, Subst.comp, ih1, ih2]

def Subst.shift_open_eq_id {u : Term} :
  Subst.shift.comp (Subst.subst_zero u) = Subst.id := by
  funext i
  cases i <;> rfl

def Rename.succ_toSubst_shift :
  (Rename.toSubst Nat.succ) = Subst.shift := rfl

def Subst.lift_id :
  Subst.id.lift = Subst.id := by
  funext i
  cases i <;> rfl

def Term.subst_id {t : Term} :
  t.subst Subst.id = t := by
  induction t
  case t_var =>
    simp [Term.subst, Subst.id]
  case t_abs t ih =>
    simp [Term.subst, Subst.id]
    simp [Subst.lift_id, ih]
  case t_app t1 t2 ih1 ih2 =>
    simp [Term.subst, Subst.id]
    simp [ih1, ih2]

def Subst.subst_zero_subst {u : Term} {s : Subst} :
  (Subst.subst_zero u).comp s = s.lift.comp (Subst.subst_zero (u.subst s)) := by
  funext i
  cases i
  case zero =>
    simp [Subst.comp, Subst.lift, Subst.subst_zero]
    simp [Subst.onTerm, Term.subst, Subst.subst_zero]
  case succ i0 =>
    simp [Subst.comp, Subst.lift, Subst.subst_zero]
    simp [Subst.onTerm, Term.subst]
    simp [Term.rename_toSubst]
    simp [Term.comp_subst]
    simp [Rename.succ_toSubst_shift]
    simp [Subst.shift_open_eq_id]
    simp [Term.subst_id]

def Term.subst_zero_subst_commute {t u : Term} {s : Subst} :
  (t[u]).subst s = (t.subst s.lift)[u.subst s] := by
  simp [Term.subst_zero]
  simp [Term.comp_subst]
  simp [Subst.subst_zero_subst]

end Fos
