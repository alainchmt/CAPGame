import Game.Metadata

World "Intermediate"
Level 1

Introduction "
  In this level we introduce the tactic `intro`. You will need it to get started.
  Please click on the `intro` tactic in the right sidebar to read an explanation.
  "

variable {X : Type}

Statement (A B : Set X) (x : X) (h : A = B) : x ∈ A → x ∈ B := by
  Hint (hidden := true) "Try something like `intro h1` and go from there."
  intro h1
  rw [← h]
  exact h1

/--
## Summary:

`intro p` will turn a goal `⊢ P → Q` into a hypothesis `p : P`
and goal `⊢ Q`. If `P` and `Q` are sets `intro p` means 'let $p$ be an arbitrary element of $P$'.
If `P` and `Q` are propositions then `intro p` says 'assume $P$ is true'.

## Details

If your goal is a function or an implication `⊢ P → Q` then `intro`
will always make progress. `intro p` turns

`Goal : P → Q`

into

```
Assumptions:
p : P
Goal:
Q
```

The opposite tactic to intro is `revert`; given the situation
just above, `revert p` turns the goal back into `⊢ P → Q`.

## Example

If your goal is an implication $P \implies Q$ then Lean writes
this as `⊢ P → Q`, and `intro p` can be thought of as meaning
'let $p$ be a proof of $P$', or more informally 'let's assume that
$P$ is true'. The goal changes to `⊢ Q` and the hypothesis `p : P`
appears in the local context. -/
TacticDoc intro

NewTactic intro
