# **Getting familiar with debruijn-indexed simply-typed lambda calculus in `Term.lean`**

Open `Term.lean`.

Note that our calculus structure is slightly different from the untyped lambda calculus. We now have `type`s, and abstraction requires the type of the parameter to be given.
Familiarize yourself with the syntax (as before, you can choose between the syntaxes in `Syntax.lean`, `Parser.lean` or `NiceParser.lean`).

# **Write the definition of typing judgements for STLC**

> _Question 1_: Fill in the typing judgement rules for the `has_ty` inductive defined in `Term.lean`.

Note that while working with DeBrujin-indexed calculi, we represent the typing environment as a list of type assignments. In Lean, we simply directly use the `List` data structure.

> _Question 2_: Fill in the definitions for boolean and list operators in `Datatypes.lean`, now with STLC syntax. Make sure to match the types given in `btrue`, `bfalse` and `flist_nil`.

You might notice that simply annotating the old definitions in untyped lambda calculus might not work. Why?

_Note_: To make Lean accept the examples, make sure your that your typing judgement cases are not _ambiguous_: `constructor` relies on the fact that for each term, there is only one possible rule that could apply.

# **Write a type inference algorithm for STLC**

Not only we can type-check STLC terms, we can also automatically infer their types!

> _Question 3_: Open `Inference.lean` and complete the definition of `infer`: given an expression and an existing type environment, infer the type of the term, if it exists.

> _Question 4_: Complete the proof for `infer_is_correct`.

> _Question 5_: Complete the proof for `infer_is_complete`.

> _Question 6_: Complete the proof for `typing_is_unique`.

# **Metatheory: Progress theorem**

For the first part of the lab, we will prove the first of the two safety theorems.

> _Question 7_: Complete the proof for `progress` in `Term.lean`.

# Curiosity Step (Optional): Extend STLC with primitives

Extend your definition of terms with (you can choose which one!):

- Number and number operations.
- Boolean and if statements.
- Lists of items of the same type.

Update the definition of `IsValue`, types, judgements and the theorems accordingly. You may notice that your terms can get "stuck" now: reduction is not possible, but the term is not a value! Try to give some examples.
