# Lab 1: The NB language

In this lab, we will implement in Lean the NB (Number and Booleans) language of booleans and numbers,
found in Chapter 3 of the TAPL book.

Some of the terms in NB (in Lean syntax) are shown in the following example:

```
#t
succ #0
succ succ succ #0
iszero? (#if iszero? #0 #then succ #0 #else succ succ #0)
succ succ pred pred #0
```

You can find them in the `Examples` namespace in `Fos/Term.lean`.

## Preparations

You can find the scaffold repository at [`https://gitlab.epfl.ch/fos/arithmetic`](https://gitlab.epfl.ch/fos/arithmetic).
Or, simply clone the repository with:

```sh
git clone git@gitlab.epfl.ch:fos/arithmetic.git
```

It is _required_ that you work on your project _as a Git repo_.
We will require you to provide the _commit hash_ of the commit that contains your submitted code.

You can find the commit hash by running `git show --shortstat`:

```
> git show --shortstat
commit aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
      // ^^-----this is the commit hash------^^
```

### Testing & Submitting your solution

We provide examples in the `Examples` namespace of each file.

As stated, we ask you to submit the commit hash of the submission on Moodle.
At the check-off session, we will grade your solution at the corresponding commit that you have written down.
**Make sure your changes are committed and the `git` repo is clean
before submitting!**

We grade your lab based on your explanations of your Lean code,
so make sure to understand what you are doing! (leaving comments helps)

## Syntax

The syntax of NB is defined as follows

```
t  ::= "#t"                   terms
     | "#f"
     | "#if" t "#then" t "#else" t
     | "succ" t
     | "pred" t
     | "iszero?" t

v  ::= "#t"                   values
     | "#f"
     | nv

nv ::= 0                      numeric values
     | "succ" nv
```

There are three syntactic forms: terms - the most general form - and two kinds of values: numeric and boolean values.
The language is completely defined by the production `t`, for terms. Note that values are a subset of terms.

In Lean, terms are defined as the `Term` inductive type, given in `Fos/Term.lean`:

```lean
inductive Term : Type where
| t_zero : Term
| t_succ : Term -> Term
-- finish the definitions of the term
```

The two given cases define a (constant) term `t_zero`,
and a _constructor_ `t_succ`, which takes a subterm of type `Term` and returns a new `Term`.

**Complete the remaining cases for `Term`.**

In order for Lean to accept NB terms, we also need to define _notations_ - rules for Lean to parse the terms into our defined
`Term` type.

The notations are defined by the `notation` keyword:

```lean
notation:max "#0" => Term.t_zero
notation:40 "succ " t => Term.t_succ t
```

The above declarations define that:

- the string `#0` is to be parsed as the `t_zero` value, and
- the string `succ`, followed by another term `t`, is to be parsed as the expression `t_succ t`.
  This rule has a precedence of "40", which means it will bind tighter than other notations of precedence less than 40.

You can find more details about the `notation` syntax in [Lean documentation](https://leanprover.github.io/theorem_proving_in_lean4/interacting_with_lean.html#notations-and-precedence).

**Complete the remaining notations for the remaining cases of `Term`.**
After writing down all notations, `Fos/Term.lean` should compile successfully.

Finally, we can write functions that takes a `Term` and return whether they are a value.
The `isNumericalVal` function is defined in Lean as follows:

```lean
def isNumericalVal : Term -> Bool
| Term.t_zero => true
| _ => sorry
```

Note that we are using pattern matching on the input `Term`: in the `t_zero` case, this is a numerical value.
For the rest, `sorry` is used, marking that this is an incomplete definition (similar to Scala's `???`).
_Do not leave any `sorry` in your final solution!_ Lean will tell you that `sorry` was used in the program.

**Complete the definition of `isNumericalVal` and `isBoolVal`.**

## Small-step Semantics, as a `reduce` function

The small-step evaluation rules are as follows.

```
         #if #t #then t1 #else t2 → t1

         #if #f #then t1 #else t2 → t2

                iszero? #0 → #t

              iszero? succ nv → #f

                  pred #0 → #0

               pred succ nv → nv

                    t1 → t1'
 ——————————————————————————————————————————————------
 #if t1 #then t2 #else t3 → #if t1' #then t2 #else t3

                     t → t'
             ————————————————————--
             iszero? t → isZero? t'

                     t → t'
                ————————————————
                pred t → pred t'

                     t → t'
                ————————————————
                succ t → succ t'
```

We shall first implement the evaluation rules as a reduction function in Lean.

The `reduce` function, given in `Fos/Reduce.lean`, takes a `Term` and returns a `ReduceResult`:
either a `Reduced t'` value with the reduced term, or `NotReducible`: this is similar to Scala `Option[Term]`.

**Complete the implementation of `reduce`.**

## Big-step semantics

The other style of operational semantics commonly in use is called big-step sematics.
Instead of defining evaluation in terms of a single step reduction,
it formulates the notion of a term that evaluates to a final value, written "t ⇓ v".
Here is how the big step evaluation rules would look for this language:

```
           v ⇓ v               (B-VALUE)

   t1 ⇓ #t     t2 ⇓ v2
---——————————————————————————  (B-IFTRUE)
#if t1 #then t2 #else t3 ⇓ v2

   t1 ⇓ #f     t3 ⇓ v3
---——————————————————————————  (B-IFFALSE)
#if t1 #then t2 #else t3 ⇓ v3

         t1 ⇓ nv1
    ——————————————————         (B-SUCC)
    succ t1 ⇓ succ nv1

         t1 ⇓ #0
       -———————————            (B-PREDZERO)
       pred t1 ⇓ #0

       t1 ⇓ succ nv1
       —————————————           (B-PREDSUCC)
       pred t1 ⇓ nv1

         t1 ⇓ 0
     ———————————————           (B-ISZEROZERO)
     iszero? t1 ⇓ #t

      t1 ⇓ succ nv1
     ———————————————           (B-ISZEROSUCC)
     iszero? t1 ⇓ #f
```

Similarly, we implement the big-step evaluation rules in Lean as the `eval` function in `Fos/Eval.lean`.
`eval` takes a `Term` and return `EvalResult`, which is either `Ok t` with the final value, or `Error` if the
term gets stuck during evaluation.

**Complete the implementation of `eval`.**

## Small-step Semantics, as Propositions

Another way to encode the evaluation rules is to define them as inductive propositions, which acts as compile-time
evidence that are useful in theorem proving.

The `IsNumericalVal` and `IsBoolVal` types define propositions that a `Term` is a numerical or boolean value.

```lean
inductive IsNumericalVal : Term -> Prop where
-- TODO: finish the definition of `isNumericalVal`
```

**Complete the definition of `IsNumericalVal` and `IsBoolVal`.** With both propositions defined, we can simply define
another propositions, `IsVal`, as follows:

```lean
inductive IsVal : Term -> Prop where
| n_val :
  IsNumericalVal t ->
  IsVal t
| b_val :
  IsBoolVal t ->
  IsVal t
```

The `Smallstep` type defines a _relation_ between two terms `t` and `t'` and provides evidence that `t` reduces to `t'`,
or `t ~~> t'`.

```lean
inductive Smallstep : Term -> Term -> Prop where
-- finish the definition of small-step reduction

notation:50 t " ~~> " t' => Smallstep t t'
```

**Complete the definition of `Smallstep`.**

With `Smallstep` defined, we can further define the _reflexive, transitive closure_ of small-step reduction, as the
`Smallsteps` relation (with the `t ~~>* t'` notation):

```lean
inductive Smallsteps : Term -> Term -> Prop where
| refl :
  Smallsteps t t
| step :
  Smallstep t t' ->
  Smallsteps t' t'' ->
  Smallsteps t t''

notation:50 t " ~~>* " t' => Smallsteps t t'
```

### Some properties of NB, with small-step semantics

**Complete the following proofs:**

1. `IsNumericalVal` implies `isNumericalVal` is true.

   ```lean
   theorem num_val_true
     (h : IsNumericalVal t) :
     isNumericalVal t = true := by
     sorry
   ```

1. Evaluating a numerical value yields the same result as the value itself.

   ```lean
   theorem num_val_eval
     (h : IsNumericalVal t) :
     eval t = EvalResult.Ok t := by
     sorry
   ```

1. Evaluating a boolean value yields the same result as the value itself.

   ```lean
   theorem bool_val_eval
     (h : IsBoolVal t) :
     eval t = EvalResult.Ok t := by
     sorry
   ```

1. Evaluating a value yields the same result as the value itself.

   ```lean
   theorem val_eval
     (h : IsVal t) :
     eval t = EvalResult.Ok t := by
     sorry
   ```

1. Reducing a term preserves the result of evaluation.

   ```lean
   theorem smallstep_eval
     (hr : t ~~> t') :
     eval t = eval t' := by
     sorry
   ```

1. A numerical value cannot be further reduced.

   ```lean
   theorem smallstep_nval_absurd
     (hv : IsNumericalVal t) :
     (t ~~> t') -> False := by
     sorry
   ```

1. A value cannot be further reduced.

   ```lean
   theorem smallstep_val_absurd
     (hv : IsVal t) :
     (t ~~> t') -> False := by
     sorry
   ```

   ... and its alternative, using the reflexive, transitive closure relation:

   ```lean
   theorem smallsteps_val
     (hv : IsVal t)
     (hr : t ~~>* t') :
     t' = t := by
     sorry
   ```

1. If a term can be reduced to a value, then evaluating the term yields the same result.
   ```lean
   theorem smallsteps_eval
     (hr : t ~~>* t')
     (hv : IsVal t') :
     eval t = EvalResult.Ok t' := by
     sorry
   ```
