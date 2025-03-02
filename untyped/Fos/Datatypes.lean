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

theorem boolean_expr_simple : ```{not} ({and} {btrue} {bfalse})``` ~~>* btrue := by
  calc
    _ ~~> ```{and} {btrue} {bfalse} {bfalse} {btrue}``` := by constructor
    _ ~~> ```(λb -> {btrue} b {bfalse}) {bfalse} {bfalse} {btrue}``` := by repeat constructor
    _ ~~> ```{btrue} {bfalse} {bfalse} {bfalse} {btrue}``` := by
      apply Reduce.app1
      apply Reduce.app1
      apply Reduce.appAbs
      -- Q: why does repeat constructor not work here?
    _ ~~> ```(λf -> {bfalse}) {bfalse} {bfalse} {btrue}``` := by repeat constructor
    _ ~~> ```{bfalse} {bfalse} {btrue}``` := by repeat constructor
    _ ~~> ```(λf -> f) {btrue}``` := by repeat constructor
    _ ~~> btrue := by repeat constructor

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

def pair :=
  ```λa -> λb -> λf -> f a b```

def flist_nil :=
  ```λx -> {btrue}```

def flist_cons :=
  ```λe -> λc -> {pair} e c```

def flist_isnil :=
  ```λp -> p (λa -> λb -> {bfalse})```

theorem flist_isnil_nil : elaborate ({flist_isnil}({flist_nil})) ~~>* btrue := by
  calc
    _ ~~> ```{flist_nil} (λa -> λb -> {bfalse})``` := by constructor
    _ ~~> btrue := by constructor

theorem flist_isnil_cons :
  elaborate (λ "h" => λ "t" => {flist_isnil}({flist_cons}("h")("t")))
  ~~>* elaborate (λ "h" => λ "t" => {bfalse}) := by
  apply reduce_many_abs
  apply reduce_many_abs
  calc
    _ ~~> ((elaborate' ["t", "h"] ({flist_cons}("h")("t"))).t_app ```λa -> λb -> {bfalse}```) := by constructor
    _ ~~> ((elaborate' ["t", "h"] ((λ "c" => {pair}("h")("c"))("t"))).t_app ```λa -> λb -> {bfalse}```) := by repeat constructor
    _ ~~> ((elaborate' ["t", "h"] ({pair}("h")("t"))).t_app ```λa -> λb -> {bfalse}```) := by
      apply Reduce.app1
      apply Reduce.appAbs
    _ ~~> ((elaborate' ["t", "h"] ((λ "b" => λ "f" => "f"("h")("b"))("t"))).t_app ```λa -> λb -> {bfalse}```) := by repeat constructor
    _ ~~> ((elaborate' ["t", "h"] ((λ "f" => "f"("h")("t")))).t_app ```λa -> λb -> {bfalse}```) := by repeat constructor
    _ ~~> (elaborate' ["t", "h"] ((λ "a" => λ "b" => {bfalse})("h")("t"))) := by repeat constructor
    _ ~~> (elaborate' ["t", "h"] ((λ "b" => {bfalse})("t"))) := by repeat constructor
    _ ~~> bfalse := by repeat constructor

def flist_head :=
  sorry

theorem flist_head_cons : elaborate (λ "h" => λ "t" => {flist_head}({flist_cons}("h")("t"))) ~~>* elaborate (λ "h" => λ "t" => "h") := by
  sorry

end Fos
