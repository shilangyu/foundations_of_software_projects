import Fos.Term
import Fos.Syntax
import Fos.Reduce
import Aesop
-- Or one of the following, use the one you like best
-- import Fos.Parser
import Fos.NiceParser
namespace Fos
namespace NiceParser

def typeBool := ∘1 ⇒ ∘1 ⇒ ∘1

def btrue : Term :=
  ```λt : ∘1 -> λf : ∘1 -> t```

def bfalse : Term :=
  ```λt : ∘1 -> λf : ∘1 -> f```

def or : Term :=
  ```λa : {typeBool} -> λb : {typeBool} -> λt : ∘1 -> λf : ∘1 -> b t (a t f)```

def and : Term :=
  ```λa : {typeBool} -> λb : {typeBool} -> λt : ∘1 -> λf : ∘1 -> b (a t f) f```

def not : Term :=
  elaborate (λ "b": typeBool => λ "t": ∘1 => λ "f": ∘1 => "b"("f")("t"))

-- Fold lists

def typeList := (∘1 ⇒ ∘2 ⇒ ∘2) ⇒ ∘2 ⇒ ∘2

def flist_nil :=
  elaborate (λ "c": (∘1 ⇒ ∘2 ⇒ ∘2) => λ "z": ∘2 => "z")

def flist_cons :=
  ```λh : ∘1 -> λt : {typeList} -> λc : ∘1 ⇒ ∘2 ⇒ ∘2 -> λz : ∘2 -> c h (t c z)```

example : [] ⊢ ```λ x: ∘1 -> x``` : (∘1 ⇒ ∘1) := by
  repeat constructor

example : [] ⊢ ```{not} ({and} {btrue} ({or} {bfalse} {btrue}))``` : typeBool := by
  repeat constructor

example : [] ⊢ ```{zero}``` : ((∘1 ⇒ ∘1) ⇒ ∘1 ⇒ ∘1) := by
  repeat constructor

example : [] ⊢ ```{flist_nil}``` : typeList := by
  repeat constructor

example: [] ⊢ ```{flist_cons}``` : ∘1 ⇒ typeList ⇒ typeList := by
  repeat constructor
