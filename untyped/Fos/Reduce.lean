import Fos.Term
import Fos.Syntax
import Mathlib.Logic.Relation
namespace Fos

inductive Reduce : Term -> Term -> Prop
  | appAbs : Reduce (.t_app (.t_abs t) s) (t[s])
  | app1 : Reduce t1 t1' -> Reduce (.t_app t1 t2) (.t_app t1' t2)
  | app2 : Reduce t2 t2' -> Reduce (.t_app t1 t2) (.t_app t1 t2')
  | abs : Reduce t1 t1' -> Reduce (.t_abs t) (.t_abs t')

inductive Term.IsVal : Term -> Prop
  | abs : Term.IsVal (.t_abs t)

inductive ReduceCBV : Term -> Term -> Prop
  | app1 : ReduceCBV t1 t1' -> ReduceCBV (.t_app t1 t2) (.t_app t1' t2)
  | app2 : Term.IsVal v1 -> ReduceCBV t2 t2' -> ReduceCBV (.t_app v1 t2) (.t_app v1 t2')
  | appAbs : Term.IsVal v -> ReduceCBV (.t_app (.t_abs t) v) (t[v])

notation:40 t " ~~> " t' => Reduce t t'
notation:40 t " ~~>cbv " t' => ReduceCBV t t'

def ReduceMany : Term -> Term -> Prop := Relation.ReflTransGen Reduce

notation:40 t " ~~>* " t' => ReduceMany t t'

instance : Trans ReduceMany Reduce ReduceMany where
  trans := Relation.ReflTransGen.tail

instance : Trans ReduceMany ReduceMany ReduceMany where
  trans := Relation.ReflTransGen.trans

instance : Trans Reduce ReduceMany ReduceMany where
  trans := Relation.ReflTransGen.head

instance : Trans Reduce Reduce ReduceMany where
  trans hab hbc := Relation.ReflTransGen.trans (Relation.ReflTransGen.single hab) (Relation.ReflTransGen.single hbc)

-- Reduce.ctx_abs, but for ReduceMany
theorem reduce_many_abs : (t ~~>* t') -> (elaborate (λ "x" => {t}) ~~>* elaborate (λ "x" => {t'})) := by
  intro h
  simp [elaborate, elaborate']
  induction h
  · constructor
  · rename_i b c _ _ _
    calc
      _ ~~>* b.t_abs := by assumption
      _ ~~> c.t_abs := by apply Reduce.abs; assumption

-- Reduce.ctx_app1, but for ReduceMany
theorem reduce_many_app1 : (t ~~>* t') -> (elaborate ({t}({a})) ~~>* elaborate ({t'}({a}))) := by
  intro h
  simp [elaborate, elaborate']
  induction h
  · constructor
  · rename_i b c _ _ _
    calc
      _ ~~>* b.t_app a := by assumption
      _ ~~> c.t_app a := by apply Reduce.app1; assumption

-- Reduce.ctx_app2, but for ReduceMany
theorem reduce_many_app2 : (t ~~>* t') -> (elaborate ({a}({t})) ~~>* elaborate ({a}({t'}))) := by
  intro h
  simp [elaborate, elaborate']
  induction h
  · constructor
  · rename_i b c _ _ _
    calc
      _ ~~>* a.t_app b := by assumption
      _ ~~> a.t_app c := by apply Reduce.app2; assumption

end Fos
