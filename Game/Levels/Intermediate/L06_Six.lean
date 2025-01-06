import Game.Metadata
import Mathlib.Topology.Basic

World "Intermediate"
Level 6

Introduction "In this problem you will look at proving that the composition of two continuous maps is
continuous

Some things you should know:
- A subset of a space `X` is an element of the type `Set X` in Lean
- The notation for the preimage of a set `U` along a map `f` is `f ⁻¹' U`

You will need to use the tactics intro, rewrite, and apply for this problem!
And some new lemmas that are in the sidebar for you.

"

Statement (X Y Z : Type*) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  (f : X → Y) (g : Y → Z) (hf : Continuous f) (hg : Continuous g) :
  Continuous (g ∘ f) := by
  rw [continuous_def] at *
  intro S hS
  rw [Set.preimage_comp]
  apply hf
  apply hg
  apply hS


LemmaDoc continuous_def as "continuous_def" in "Topology"
  "The statement echoing the definition of a continuous map."

LemmaDoc Set.preimage_comp as "Set.preimage_comp" in "Topology"
  "The preimage of a set along the composition of maps."

NewLemma continuous_def Set.preimage_comp
