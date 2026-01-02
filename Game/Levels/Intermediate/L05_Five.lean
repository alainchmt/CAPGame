import Game.Metadata
import Game.Levels.Intermediate.L04_Four


World "Intermediate"
Level 5

Introduction "In this level you will prove the more complicated
identity (5) in <https://en.wikipedia.org/wiki/Commutator#Identities_(group_theory)>, called
the Hall-Witt identity.  "

open MyCommutator

Statement {G : Type} [Group G] {x y z : G} :
 [[x ; y⁻¹]; z] ^ y * [[y; z⁻¹]; x] ^ z * [[z; x⁻¹]; y] ^ x = 1 := by
  simp only [commutator_def, inv_inv, mul_assoc, mul_inv_rev, conjugate_def, inv_mul_cancel_left,
    mul_inv_cancel_left, inv_mul_cancel]

/-- The group operation is associative. -/
TheoremDoc mul_assoc as "mul_assoc" in "Group Theory"


NewTheorem mul_assoc
