import Game.Metadata

World "Intro"
Level 4

Title ""

Introduction "

## Exact

Sometimes after rewriting the hypotheses and goal enough, we reach a point where the goal is
exactly the same as one of the hypotheses.
In this case, we want to tell Lean that we are finished, one of our hypotheses now matches
the conclusion we needed to get to.

The tactic to do this is called `exact`, and to use it we just need to supply the name of
the hypothesis we want to use.

For example, if we were trying to prove that 3 divides some natural number `n` and we
ended up with the goal state:
```
Objects:
n : ℕ
Assumptions:
h : 3 ∣ n
Goal:
3 ∣ n
```
then `exact h` would complete the proof.


We note that binary logical connectives like `∧` and `∨` associate to the right, so
`Q ∧ P ∧ Q` means `Q ∧ (P ∧ Q)`.
"

Statement (P Q : Prop) (h : Q ∧ P ∧ Q) :
  (P ∨ ¬ Q) ∧ Q := by
  rw [or_and_right]
  rw [not_and_self_iff]
  rw [or_false]
  rw [and_comm] at h
  rw [and_assoc] at h
  rw [and_self] at h
  exact h

/-- -/
TheoremDoc or_and_right as "or_and_right" in "Logic"

/-- -/
TheoremDoc not_and_self_iff as "not_and_self_iff" in "Logic"

/-- -/
TheoremDoc or_false as "or_false" in "Logic"

/-- ∧ is commutative -/
TheoremDoc and_comm as "and_comm" in "Logic"

/-- ∧ is associative -/
TheoremDoc and_assoc as "and_assoc" in "Logic"

/-- -/
TheoremDoc and_self as "and_self" in "Logic"

/--
## Summary

If the goal is `⊢ X` then `exact x` will close the goal if
and only if `x` is a term of type `X`.

## Details

Say $P$, $Q$ and $R$ are types (i.e., what a mathematician
might think of as either sets or propositions),
and the local context looks like this:

```
Objects and Assumptions
p : P,
h : P → Q,
j : Q → R
Goal:
R
```

If you can spot how to make a term of type `R`, then you
can just make it and say you're done using the `exact` tactic
together with the formula you have spotted. For example, the
above goal could be solved with

`exact j(h(p)),`

because $j(h(p))$ is easily checked to be a term of type $R$
(i.e., an element of the set $R$, or a proof of the proposition $R$).-/
TacticDoc exact

NewTheorem or_and_right not_and_self_iff or_false and_comm and_assoc and_self
NewTactic exact
