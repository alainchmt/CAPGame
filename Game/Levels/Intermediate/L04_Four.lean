import Game.Metadata
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Bracket


World "Intermediate"
Level 4

Introduction "
## The simplifier
Up till now we have been using `rewrite` to manually instruct Lean which steps to take, one at a time.
This is a very useful tool, but after a while you will notice that there are some rewrites that
will always make things easier when substituted.
For example, we almost always want to use the fact that multiplying by 1 or adding 0 doesn't
change things. For this, the `simp` tactic will be very handy.


## Commutator identities

In these exercises we will write the proofs of a couple of the identities in
<https://en.wikipedia.org/wiki/Commutator#Identities_(group_theory)>
in Lean.

First, we will set up the basic definitions. In World 1 we didn't make any new mathematical
definitions, we just made use of the natural numbers, propositions, and some lemmas Lean
already knew about.

```
def commutator {G : Type*} [Group G]
(x y : G) : G := x⁻¹ * y⁻¹ * x * y
```
```
def conjugate {G : Type*} [group G]
(x y : G) : G := y⁻¹ * x * y
```

We denote by `[x ; y]` the commutator of x and y, and by `y ^ x` the conjugate of x by y. 

```
lemma commutator_def {G : Type*} [Group G]
{x y : G} : [x ; y] = x⁻¹ * y⁻¹ * x * y := rfl
```
```
lemma conjugate_def {G : Type*} [Group G]
{x y : G} : y ^ x = x⁻¹ * y * x := rfl
```
 "
def commutator {G : Type*} [Group G] (x y : G) : G := x⁻¹ * y⁻¹ * x * y
instance hasBracket {G : Type*} [Group G] : Bracket G G := ⟨commutator⟩
notation "["x";"y"]" => Bracket.bracket x y

--notation: max "⁅"x" , "y"⁆" => commutator x y

def conjugate  {G : Type*} [Group G] (x y : G) : G := y⁻¹ * x * y
instance Group.has_pow {G : Type*} [Group G] : Pow G G := ⟨conjugate⟩

lemma commutator_def {G : Type*} [Group G] {x y : G} : [x ; y] = x⁻¹ * y⁻¹ * x * y := rfl

lemma conjugate_def {G : Type*} [Group G] {x y : G} : y ^ x = x⁻¹ * y * x := rfl

Statement {G : Type} [Group G] {x : G} : [x ; x] = 1 := by
  rw [commutator_def]
  rw [inv_mul_cancel_right]
  rw [inv_mul_self]


TacticDoc simp "
## Summary

The `simp` tactic is a high-level tactic which tries
to prove equalities using facts in its database.

## Details

The `simp` tactic does basic automation.
For example, some proofs involve a tedious number of rewrites of `add_assoc` and `add_comm`,
the same is true of `mul_assoc` and `mul_comm` in the case of multiplication.
We can use `simp` to do this automatically.
To tell `simp` to use some lemma `h` when simplifying, write `simp[h]`. More generally,
for `simp` to include additional lemmas `h1`, `h2`, ..., `hn` when simplifying, write
`simp[h1, h2, ..., hn]`.

### Example:
If our goal is this:
```
⊢ a + b + c + d + e = a + (b + (c + d) + e)
```

we can solve this with `simp` using `simp[add_assoc]`.
"
NewTactic simp

LemmaDoc commutator_def as "commutator_def" in "Group Theory"
  "The statement echoing the definition of commutator."
LemmaDoc conjugate_def as "conjugate_def" in "Group Theory"
  "The statement echoing the definition of conjugate."
LemmaDoc inv_mul_cancel_right as "inv_mul_cancel_right" in "Group Theory"
  "Cancelling inverses on the right. "
LemmaDoc inv_mul_self as "inv_mul_self" in "Group Theory"
  "Cancelling an element with its own inverse."

NewLemma commutator_def conjugate_def inv_mul_cancel_right inv_mul_self
