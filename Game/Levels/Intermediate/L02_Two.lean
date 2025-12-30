import Game.Metadata
import Mathlib.Topology.ContinuousMap.Polynomial

World "Intermediate"
Level 2

Introduction "
## Using apply
In this problem, you will show that a specific polynomial is continuous. You can do this using
the basic facts in the right sidebar: that adding continuous functions is continuous,
likewise multiplying continuous functions remains continuous, constant functions are continuous,
and the identity function is continuous. The way these lemmas are stated is very general, they work
for any continuous functions on arbitrary topological spaces, but by using `apply` we can let Lean
work out the details automatically.

But, how do we talk about the functions themselves?
The basic method to speak about an unnamed function in Lean makes use of lambda expressions.
In mathematics we might just write $x ^ 3 + 7$ to describe a polynomial function, leaving it
implicit that $x$ is the variable.
In Lean, we use the keyword `fun` to describe a function by placing the name of the variable
after `fun`.
So `fun x => x^3 + 7` defines the function that takes input `x` and outputs `x^3 + 7` in Lean.

Watch out! Some of these lemmas have names with a dot and starting with a capital letter
like `Continuous.add` (these ones prove continuity of a combination of functions)
and some have an underscore and start with a lowercase letter like `continuous_const`
(these ones state that some specific function is continuous). "

open Polynomial

Statement : Continuous (fun (x : ℝ) => 5 * x ^ 2 + x + 6) := by
  Hint (hidden := true) "Start with `apply Continuous.add`, you will notice
  that the goal has split into two goals. Try `apply Continuous.add` again and
  see what happens. "
  apply Continuous.add
  apply Continuous.add
  apply Continuous.mul
  apply continuous_const
  apply Continuous.pow
  apply continuous_id
  apply continuous_id
  apply continuous_const


/-- ## Summary

If `h : P → Q` is a hypothesis and the goal is `⊢ Q`, then
`apply h` changes the goal to `⊢ P`.

## Details

If you have a function `h : P → Q` and your goal is `⊢ Q`
then `apply h` changes the goal to `⊢ P`. The logic is
simple: if you are trying to create a term of type `Q`,
but `h` is a function that turns terms of type `P` into
terms of type `Q`, then it will suffice to construct a
term of type `P`. A mathematician might say: 'We need
to construct an element of $Q$, but we have a function $h:P \\to Q$
so it suffices to construct an element of $P$'. Or alternatively
'we need to prove $Q$, but we have a proof $h$ that $P \\implies Q$
so it suffices to prove $P$'.-/
TacticDoc apply

NewTactic apply

/-- Adding two continuous functions is continuous.-/
TheoremDoc Continuous.add as "Continuous.add" in "Topology"

/-- Multiplying two continuous functions is continuous. -/
TheoremDoc Continuous.mul as "Continuous.mul" in "Topology"

/-- The power of a continuous function is continuous.-/
TheoremDoc Continuous.pow as "Continuous.pow" in "Topology"

/-- A constant function is continuous -/
TheoremDoc continuous_const as "continuous_const" in "Topology"

/-- The identity function is continuous -/
TheoremDoc continuous_id as "continuous_id" in "Topology"


NewTheorem Continuous.add Continuous.mul Continuous.pow continuous_const continuous_id
