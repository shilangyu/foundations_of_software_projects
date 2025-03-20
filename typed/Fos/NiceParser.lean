import Fos.Term
import Lean
open Lean Syntax Elab Meta
namespace Fos
namespace NiceParser

declare_syntax_cat fos_type
declare_syntax_cat fos_term
declare_syntax_cat fos_atom

scoped syntax:max "∘" num : fos_type
scoped syntax:50 fos_type "⇒" fos_type : fos_type
scoped syntax:max "(" fos_type ")" : fos_type
scoped syntax:max "{" term "}" : fos_type

scoped syntax:max ident : fos_atom
scoped syntax:50 "λ" ident ":" fos_type " -> " fos_term : fos_atom
scoped syntax:max "(" fos_term ")" : fos_atom
scoped syntax:max "{" term "}" : fos_atom
scoped syntax:60 fos_atom* : fos_term

partial def elabFosType : Syntax -> TermElabM Expr
| `(fos_type| ∘$n:num) =>
  let m := n.getNat
  mkAppM ``type.Base #[mkNatLit m]
| `(fos_type| ($t:fos_type)) => elabFosType t
| `(fos_type| {$t:term}) => do
  let expectedType <- pure (mkConst ``type)
  let expr <- Elab.Term.elabTerm t expectedType
  return expr
| `(fos_type| $t1:fos_type⇒$t2:fos_type) => do
  let tp1 <- elabFosType t1
  let tp2 <- elabFosType t2
  mkAppM ``type.Arrow #[tp1, tp2]
| _ => throwUnsupportedSyntax

def mkVarRef (n : Nat) : MetaM Expr :=
  mkAppM ``Term.t_var #[mkNatLit n]

abbrev Ctx := List String

def lookupName (n : String) : Ctx -> Option Nat
| [] => none
| x :: xs => if x = n then some 0 else
  match lookupName n xs with
  | some n => some (n + 1)
  | none => none

partial def elabFosTerm (ctx : Ctx) : Syntax -> TermElabM Expr
| `(fos_atom| $n:ident) => do
  match lookupName n.getId.toString ctx with
  | some n => mkVarRef n
  | none => throwError "Variable {n} not found"
| `(fos_atom | {$t:term}) => do
  let expectedType <- pure (mkConst ``Term)
  let expr <- Elab.Term.elabTerm t expectedType
  return expr
| `(fos_term | λ $n:ident : $ty:fos_type -> $t:fos_term) => do
  let tp <- elabFosType ty
  let expr <- elabFosTerm (n.getId.toString :: ctx) t
  mkAppM ``Term.t_abs #[tp, expr]
| `(fos_atom| ($t:fos_term)) => elabFosTerm ctx t
| `(fos_term| $atoms:fos_atom*) => do
  if atoms.size < 1 then
    throwError "Expected at least one atom"
  else
    let head := atoms[0]!
    let tail := atoms[1:]
    let mut result <- elabFosTerm ctx head
    for atom in tail do
      let expr <- elabFosTerm ctx atom
      result <- mkAppM ``Term.t_app #[result, expr]
    return result
| _ => throwUnsupportedSyntax

elab "```" term:fos_term "```" : term => elabFosTerm [] term

section Examples

#check ```λx: ∘1 -> x```
#check ```λx:(∘1⇒∘2) -> λy:∘1 -> x y```
#check ```λx:(∘1⇒∘1) -> λy:∘1 -> x(x y)```
#check ```λx:(∘1⇒∘2) -> λy:((∘1⇒∘2)⇒∘1) -> x(y x)```

def zero : Term := ```
λs: ∘1⇒∘1 -> λz: ∘1 -> z
```

def succ : Term := ```
λn: ((∘1⇒∘1) ⇒ ∘1 ⇒ ∘1) -> λs: ∘1⇒∘1 -> λz: ∘1 -> s(n s z)
```

#check ```λx:∘3 -> λy: ∘3⇒((∘1⇒∘1) ⇒ ∘1 ⇒ ∘1) -> {succ} (y x)```

#reduce succ



end Examples

end NiceParser
end Fos
