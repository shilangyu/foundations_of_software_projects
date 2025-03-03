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
    _ ~~> ```{btrue} {bfalse} {bfalse} {bfalse} {btrue}``` := by repeat constructor
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
  calc
    _ ~~> ```λn -> ({iszero} (λs -> λz -> s (n s z)))``` := by repeat constructor
    _ ~~> ```λn -> ((λs -> λz -> s (n s z)) (λx -> {bfalse}) {btrue})``` := by repeat constructor
    _ ~~> ```λn -> ((λz -> (λx -> {bfalse}) (n (λx -> {bfalse}) z)) {btrue})``` := by repeat constructor
    _ ~~> ```λn -> ((λz -> {bfalse}) {btrue})``` := by repeat constructor
    _ ~~> ```λn -> {bfalse}``` := by repeat constructor

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
  calc
    _ ~~> ```λh -> λt -> {flist_cons} h t (λa -> λb -> {bfalse})``` := by repeat constructor
    _ ~~> ```λh -> λt -> (λc -> {pair} h c) t (λa -> λb -> {bfalse})``` := by repeat constructor
    _ ~~> ```λh -> λt -> {pair} h t (λa -> λb -> {bfalse})``` := by repeat constructor
    _ ~~> ```λh -> λt -> (λb -> λf -> f h b) t (λa -> λb -> {bfalse})``` := by repeat constructor
    _ ~~> ```λh -> λt -> (λf -> f h t) (λa -> λb -> {bfalse})``` := by repeat constructor
    _ ~~> ```λh -> λt -> (λa -> λb -> {bfalse}) h t``` := by repeat constructor
    _ ~~> ```λh -> λt -> (λb -> {bfalse}) t``` := by repeat constructor
    _ ~~> ```λh -> λt -> {bfalse}``` := by repeat constructor

def flist_head :=
  ```λp -> p {btrue}```

theorem flist_head_cons : elaborate (λ "h" => λ "t" => {flist_head}({flist_cons}("h")("t"))) ~~>* elaborate (λ "h" => λ "t" => "h") := by
  calc
    _ ~~> ```λh -> λt -> {flist_cons} h t {btrue}``` := by repeat constructor
    _ ~~> ```λh -> λt -> (λb -> {pair} h b) t {btrue}``` := by repeat constructor
    _ ~~> ```λh -> λt -> {pair} h t {btrue}``` := by repeat constructor
    _ ~~> ```λh -> λt -> (λb -> λf -> f h b) t {btrue}``` := by repeat constructor
    _ ~~> ```λh -> λt -> (λf -> f h t) {btrue}``` := by repeat constructor
    _ ~~> ```λh -> λt -> {btrue} h t``` := by repeat constructor
    _ ~~> ```λh -> λt -> (λf -> h) t``` := by repeat constructor
    _ ~~> ```λh -> λt -> h``` := by repeat constructor

end Fos
