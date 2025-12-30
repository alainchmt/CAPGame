import Game.Metadata

World "Intro"
Level 2

Title ""

lemma Intro.add_zero : ∀ x, x + 0 = x
:= Nat.add_zero

lemma Intro.one_mul : ∀ x, 1 * x = x
:= Nat.one_mul

Introduction "
We can state lemmas assuming hypotheses with similar notation as we made a lemma
dependent on natural numbers before.

The `rewrite` tactic can then be used to rewrite a hypothesis. After all, we can substitute
things we know to be equal in facts we know, as well as substituting into what we are trying to prove.

### Example:
You can use `rewrite` to change a hypothesis as well.
For example, if your goal state looks like this:
```
Objects:
n m : ℕ
Assumptions:
h1 : n + 1 = 7
h2 : m = n + 1
Goal:
m + 2 = 9
```
then `rewrite [h1] at h2` will turn `h2` into `h2 : m = 7`.

Below are two useful results you can use to finish this level.


``` lemma add_zero : ∀ x, x + 0 = x ```

``` lemma one_mul : ∀ x, 1 * x = x ```

"

/-- Adding zero on the right. -/
TheoremDoc Intro.add_zero as "add_zero" in "Arithmetic"

/-- Multiplying by one on the left. -/
TheoremDoc Intro.one_mul as "one_mul" in "Arithmetic"


NewTheorem Intro.add_zero Intro.one_mul

open Intro
Statement (x y : ℕ) (hx : x + 0 = 1 * y) : x + y = y + y := by
  Hint (hidden := true ) "Type `rewrite [add_zero x] at hx` as a first step of the proof.
  In fact, in this situation the `rewrite` tactic can infer that the argument of `add_zero` should be `x`,
  so one could leave out the argument `x`, i.e. simply write `rewrite [add_zero] at hx`."
  rw [add_zero, one_mul] at hx
  rw [hx]



--LemmaDoc add_zero as "add_zero" in "Add"
--"The commutativity of addition"
