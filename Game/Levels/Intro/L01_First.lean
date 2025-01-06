import Game.Metadata

World "Intro"
Level 1

Title ""


lemma Intro.add_comm : ∀ (x : ℕ) (y : ℕ), x + y = y + x := Nat.add_comm

Introduction "
## The setup
We note that the following description applies to the Desktop version of this website.
If you are using a mobile device, the layout may be different.

You should see different windows on this page, they will contain part of using Lean.
Let's go through them one by one.

The middle one is where you tell Lean what steps you want to make in your proof.
You can do this in 'Typewriter mode' or 'Editor mode'.
We suggest you click the `</>` button in the top right corner to switch to 'Editor mode',
which is closer to how Lean actually looks.

By typing statements here in precise language we instruct Lean how we want the proof to go.

At the bottom of the middle window, it reads `Current Goal`.
This panel represents what Lean thinks the current state of your proof is.
It also shows the objects you are working with and the assumptions that you currently have. The statement (or statements) you are trying to show come after
`Goal`.
For example, a valid state might look like
```
Objects:
n : ℕ
Assumptions:
h : Even n
Goal:
Odd (n + 1)
```
which means that we have assumed `n` is a natural number and that `n` is even, and we are trying to show that `n + 1` is
odd (we sometimes write `⊢` as a shorthand notation for `Goal`).
In order to prove this, we will need to use more than what is written here, however. We might need the definition of
an even and an odd number, so in addition to the current hypotheses we also will make use of a library of lemmas that
we have proved so far.

Below this, there will be feedback about any errors in your current proof.
As you move your cursor around by clicking different parts of the proof the goal will update, we can
always step backwards and forwards through the proof using the arrow keys to check what we were
proving before.
If you write some syntax Lean doesn't understand, or a proof step that doesn't make sense, Lean will
return an error, the most common error being `unsolved goals`
which just means that you aren't finished with the proof yet!

On the right of the screen, you will find a list of *Theorems* and *tactics* you can use to prove
results, this is here to remind you of the things we've talked about so far. You can click on them to see more info.

## The language

A lemma in Lean is written using a specific syntax, that is designed to look similar to written
mathematics, but is more restricted in how statements can be constructed.
Here is an example of a lemma statement in Lean:

``` lemma add_comm : ∀ (x : ℕ) (y : ℕ), x + y = y + x ```

This lemma states that for all natural numbers `x` and `y` the addition of `x` and `y` commutes.
Hopefully, you agree that this is a straightforward, but very useful fact!
Note the first word `lemma` is a keyword and means we are stating a new
lemma.
The second word is simply a name we give to the lemma so we can refer to it later, naming lemmas
works much better than numbering lemmas when you need to refer back to many things.
This is especially helpful if you give the lemmas sensible names, so that you can remember them
later, and so that when you use them you can tell what the lemma does from its name.
In this case `add_comm` says that addition is commutative, so it seems like a pretty good choice.

The symbol `:` is used to say that `x` and `y` are natural numbers, this is similar to how we
normally write `x ∈ ℕ`, and you should think of `:` as meaning `∈`.
The symbol `:` is also used after the name of the lemma, and it has the same meaning!
Here within the lemma `x : ℕ` gives a name to a natural number and
`add_comm : ∀ x y, x + y = y + x` gives a name to the proof of the statement saying that addition is commutative.

The lemma `add_comm` is a 'for all' statement, so in order to get the statement that addition
commutes for a _specific_ pair of natural numbers rather than variables `x` and `y`,
we place the naturals we want to refer to after the name,
for instance `add_comm 2 3` means `2 + 3 = 3 + 2`.
Here we used 2 and 3, but we could apply this lemma with variables too by using their names
instead of 2 and 3.


### Rewriting
Rewriting is one of the most basic methods of proof. We substitute one object we know equals another
inside what we want to prove, by doing this we can get closer to something that we already know to
be true,
or get to a point where things cancel out or simplify.

For example, if `h` is a name for the fact that `X = Y`, then `rewrite [h]` will change
all `X`s in the goal to `Y`s.
On the right-hand side in the tactics panel you can find more details about
`rewrite`, you don't need to read it now, but it's there if you ever want to check the syntax
again.

### Reflexivity
A goal of the form `A = A` can be solved using the reflexivity tactic called `rfl`.
For example, if the goal is `x + y = x + y`, then `rfl` will solve it.

Now try to use a sequence of `rewrite` steps to prove the goal in the middle screen by typing these steps into the box
on the right. To finish the proof, you can use `rfl`. We note the convention that `x + y + z` means `(x + y) + z`.

It's worth noting that while this game introduces basic lemmas and tactics for proving
mathematical statements in Lean, Lean does have more advanced
automation tools that can solve certain goals in one go.

 "
/- Hint (hidden := true) " Delete `sorry` and type `rewrite add_comm x y,` (don't forget the comma!).
  That is the first step of the proof, after typing the comma you should see the goal (on the right)
  change so the sides of the equation look closer to each other.
  The next two steps of the proof go on the next lines, and are similar to the first, can you work
  them out?" -/

LemmaDoc Intro.add_comm as "add_comm" in "Arithmetic"
"The commutativity of addition."

NewLemma Intro.add_comm

open Intro
Statement (x y z w : ℕ) : x + y + (z + w) = w + z + (y + x) := by
  Hint (hidden := true) " Start by typing `rewrite [add_comm x y]`.
  That is the first step of the proof. After typing it, you should see the goal (at the bottom)
  change so the sides of the equation look closer to each other.
  The next two steps of the proof go on the next lines, and are similar to the first, can you work
  them out?
  To finish the proof, you may want to use `rfl`.
  "
  rewrite [add_comm]
  rewrite [add_comm z w]
  rewrite [add_comm x y]
  rfl

TacticDoc rfl
" This tactic proves goals of the form `⊢ A = A` "

TacticDoc rewrite
"
## Summary

If `h` is a proof of `X = Y`, then `rewrite [h]` will change
all `X`s in the goal to `Y`s.

As this is such a common proof step we also have a short name, `rw` instead of `rewrite` for this
step, to save us from too much typing.

Variants: `rw [← h]` (type `←` using `\\l` for left) changes
`Y` to `X` and
`rw [h] at h2` changes `X` to `Y` in hypothesis `h2` instead
of the goal.

## Details

The `rw` tactic is a way to do 'substituting in'. 

If `h : A = B` is in your local context (i.e., a proof of `A = B`)
and if your goal contains one or more `A`s, then `rw [h]`
will change them all to `B`'s. This will also work if you have a proof of a if-and-only-if statement `h : A ↔ B`. 

Important note: if `h` is not a proof of the form `A = B`
or `A ↔ B` (for example if `h` is a function, an implication,
or perhaps even a proposition itself rather than its proof),
then `rw` is not the tactic you want to use. For example,
`rw (P = Q)` is never correct: `P = Q` is the true-false
statement itself, not the proof.
If `h : P = Q` is its proof, then `rw [h]` will work.

Pro tip 1: If `h : A = B` and you want to change
`B`s to `A`s instead, try `rw [← h]` (get the arrow with `\\l`,
note that this is a small letter L, not a number 1).

### Example:
If it looks like this in the bottom box:
```
Objects:
A B C : Set X
Assumptions:
h : A = B ∪ C
Goal:
  A ∪ B = B ∪ C
```

then

`rw [h]`

will change the goal into ` ⊢ B ∪ C ∪ B = B ∪ C`.

### Example:
You can use `rw` to change a hypothesis as well.
For example, if your local context looks like this:
```
Objects:
A B C D : Set X
Assumptions:
h1 : A = B ∩ C
h2 : B ∪ A = D
Goal:
  D = B
```
then `rw [h1] at h2` will turn `h2` into `h2 : B ∪ B ∩ C = D` (remember operator precedence).
"

NewTactic rewrite rfl
NewHiddenTactic rw
