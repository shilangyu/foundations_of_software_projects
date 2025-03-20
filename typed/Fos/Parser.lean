import Fos.Term
import Lean
open Lean Syntax Elab Meta
namespace Fos

namespace Parser

declare_syntax_cat fos_type
declare_syntax_cat fos_term
declare_syntax_cat fos_atom

scoped syntax:max "∘" num : fos_type
scoped syntax:50 fos_type "⇒" fos_type : fos_type
scoped syntax:max "(" fos_type ")" : fos_type
scoped syntax:max "{" term "}" : fos_type

scoped syntax:max "#" num : fos_atom
scoped syntax:50 "λ" fos_type "." fos_term : fos_atom
scoped syntax:max "(" fos_term ")" : fos_atom
scoped syntax:max "{" term "}" : fos_atom
scoped syntax:60 fos_atom* : fos_term

def mkVarRef (n : Nat) : MetaM Expr :=
  mkAppM ``Term.t_var #[mkNatLit n]

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

partial def elabFosTerm : Syntax -> TermElabM Expr
| `(fos_atom| #$n:num) => mkVarRef n.getNat
| `(fos_atom| {$t:term}) => do
  let expectedType <- pure (mkConst ``Term)
  let expr <- Elab.Term.elabTerm t expectedType
  return expr
| `(fos_atom| λ$ty:fos_type.$t:fos_term) => do
  let tp <- elabFosType ty
  let expr <- elabFosTerm t
  mkAppM ``Term.t_abs #[tp, expr]
| `(fos_atom| ($t:fos_term)) => elabFosTerm t
| `(fos_term| $atoms:fos_atom*) => do
  if atoms.size < 1 then
    throwError "Expected at least one atom"
  else
    let head := atoms[0]!
    let tail := atoms[1:]
    let mut result <- elabFosTerm head
    for atom in tail do
      let expr <- elabFosTerm atom
      result <- mkAppM ``Term.t_app #[result, expr]
    return result
| _ => throwUnsupportedSyntax

elab "```" term:fos_term "```" : term => elabFosTerm term

section Examples

#check ```#0```
#check ```λ∘1 .#0```
#check ```λ∘1 .λ∘1 .#0#1```

private def zero : Term := ```
λ∘1⇒∘1 .λ∘1 .#0
```

private def succ : Term := ```
λ((∘1⇒∘1)⇒∘1⇒∘1).λ(∘1⇒∘1).λ∘1 .#1(#2#1#0)
```

private def one : Term := ```
{succ}{zero}
```

private def two : Term := ```
{succ}{one}
```

private def three : Term := ```
{succ}{two}
```

end Examples

end Parser

end Fos
