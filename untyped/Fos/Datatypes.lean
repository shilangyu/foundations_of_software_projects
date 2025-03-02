import Fos.Term
import Fos.Syntax
import Fos.Reduce
import Fos.NiceParser
namespace Fos

open Fos.NiceParser

def btrue : Term :=
  ```λt -> λf -> t```

def bfalse : Term :=
  ```λt -> λf -> f```

def or : Term :=
  ```λa -> λb -> a {btrue} b```

def and : Term :=
  ```λa -> λb -> a b {bfalse}```

def not : Term :=
  ```λb -> b {bfalse} {btrue}```

theorem boolean_expr_simple :=
  sorry

-- Arithmetic

def iszero :=
  ```λn -> n (λx -> {bfalse}) {btrue}```

theorem iszero_zero : elaborate ({iszero}({zero})) ~~>* btrue := by
  calc
    _ ~~> ```{zero} (λx -> {bfalse}) {btrue}``` := by constructor
    _ ~~> ```(λz -> z) {btrue}``` := by repeat constructor
    _ ~~> ```{btrue}``` := by constructor

theorem iszero_succ : elaborate (λ "n" => {iszero}({succ}("n"))) ~~>* elaborate (λ "n" => {bfalse}) := by
  apply reduce_many_abs
  calc
    _ ~~> (elaborate' ["n"] (({succ})("n")(λ "x" => {bfalse})({btrue})))  := by constructor
    _ ~~> (elaborate' ["n"] ((λ "s" => λ "z" => "s"("n"("s")("z")))(λ "x" => {bfalse})({btrue})))  := by repeat constructor
    _ ~~> (elaborate' ["n"] ((λ "z" => (λ "x" => {bfalse})("n"(λ "x" => {bfalse})("z")))({btrue})))  := by repeat constructor
    _ ~~> (elaborate' ["n"] ((λ "x" => {bfalse})("n"(λ "x" => {bfalse})({btrue}))))  := by constructor
    _ ~~> bfalse := by constructor

-- Fold lists

def flist_nil :=
  sorry

def flist_cons :=
  sorry

def flist_isnil :=
  sorry

theorem flist_isnil_nil : elaborate ({flist_isnil}({flist_nil})) ~~>* btrue := by
  sorry

theorem flist_isnil_cons :
  elaborate (λ "h" => λ "t" => {flist_isnil}({flist_cons}("h")("t")))
  ~~>* elaborate (λ "h" => λ "t" => {bfalse}) := by
  sorry

def flist_head :=
  sorry

theorem flist_head_cons : elaborate (λ "h" => λ "t" => {flist_head}({flist_cons}("h")("t"))) ~~>* elaborate (λ "h" => λ "t" => "h") := by
  sorry

end Fos
