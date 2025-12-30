import Game.Metadata


World "Intermediate"
Level 3

Introduction
"In this problem you will see how to prove a statement involving the existential
quantifier and some inequalities. In the right sidebar you will find some useful
tactics like `constructor` and `use`, together with some new lemmas.
"

Statement : ∃ n : ℕ, 8 < n ∧ n < 10 := by
  use 9
  constructor
  exact Nat.lt_succ_self 8
  exact Nat.lt_succ_self 9


/-- When given a goal that is an `∧` (and) of two propositions, the `constructor` tactic
will produce two goals, one for each side, that can be solved individually.-/
TacticDoc constructor


/-- When the goal is to prove an existential `∃`, we can
supply the witness (an example that has the desired property)
using the tactic `use`.

For example :
If the goal is
```
⊢ ∃ n : ℕ, n + 1 = 1
```
then we have to take `n` to be zero, so we type `use 0`.
The remaining goal will then be that
`0 + 1 = 1`
which is provable with `zero_add`.-/
TacticDoc use

NewTactic constructor use

 /-- A natural number is smaller than its successor. -/
TheoremDoc Nat.lt_succ_self as "Nat.lt_succ_self" in "Inequalities"

NewTheorem Nat.lt_succ_self
