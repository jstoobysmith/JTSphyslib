/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.Invariants.Averages.BoostAvgProjectorOnMonomials
/-!
# The projected weight-eight monomials lie in the span

Every weight-eight monomial, after averaging over the rotations by `π` and applying the projector
`boostAvgScalarProj`, lands in the span of the four renormalizable invariants. Together with
`boostAvgScalarProj_apply_of_invariant` this is the last input to the classification
theorem.
-/

@[expose] public section

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace LeptonGaugeSector
open TensorProduct StandardModel

namespace JetAlgebra

open scoped minkowskiMatrix PauliMatrix
open Matrix MatrixGroups

/-- The Maxwell term lies in the span of the invariants. -/
lemma maxwellTerm_mem_span :
    maxwellTerm ∈ Submodule.span ℂ massDimFourInvariants :=
  Submodule.subset_span (by simp [massDimFourInvariants])

/-- The theta term lies in the span of the invariants. -/
lemma thetaTerm_mem_span :
    thetaTerm ∈ Submodule.span ℂ massDimFourInvariants :=
  Submodule.subset_span (by simp [massDimFourInvariants])

/-- The fermion kinetic term lies in the span of the invariants. -/
lemma fermionKineticTerm_mem_span :
    fermionKineticTerm ∈ Submodule.span ℂ massDimFourInvariants :=
  Submodule.subset_span (by simp [massDimFourInvariants])

/-- The conjugate fermion kinetic term lies in the span of the invariants. -/
lemma fermionKineticTermBar_mem_span :
    fermionKineticTermBar ∈ Submodule.span ℂ massDimFourInvariants :=
  Submodule.subset_span (by simp [massDimFourInvariants])

/-- Pulling a sign out of a jet-algebra product on the right. The generic
  `mul_neg` does not fire here: the multiplication comes from the tensor-product
  instance, which typeclass search does not connect to `HasDistribNeg`. -/
lemma jetMul_neg (u v : JetAlgebra) : u * -v = -(u * v) := by grind

/-- Pulling a sign out of a jet-algebra product on the left; see `jetMul_neg`. -/
lemma jetNeg_mul (u v : JetAlgebra) : -u * v = -(u * v) := by grind

/-- Projector membership for the ordered square `F01 * F01`. -/
lemma boostAvgScalarProj_FF_c0101_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [boostAvgScalarProj_F01_F01]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered square `F01 * F10`. -/
lemma boostAvgScalarProj_FF_c0110_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [boostAvgScalarProj_F01_F01]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F10 * F01`. -/
lemma boostAvgScalarProj_FF_c1001_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [boostAvgScalarProj_F01_F01]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F10 * F10`. -/
lemma boostAvgScalarProj_FF_c1010_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [boostAvgScalarProj_F01_F01]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered square `F01 * F23`. -/
lemma boostAvgScalarProj_FF_c0123_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [boostAvgScalarProj_F01_F23]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F01 * F32`. -/
lemma boostAvgScalarProj_FF_c0132_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) =
        -(fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [boostAvgScalarProj_F01_F23]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F10 * F23`. -/
lemma boostAvgScalarProj_FF_c1023_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [boostAvgScalarProj_F01_F23]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F10 * F32`. -/
lemma boostAvgScalarProj_FF_c1032_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) from fieldStrengthDeriv_antisymm {} _ _,
    show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) =
        -(fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [boostAvgScalarProj_F01_F23]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F23 * F01`. -/
lemma boostAvgScalarProj_FF_c2301_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_mul_comm]
  rw [boostAvgScalarProj_F01_F23]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F23 * F10`. -/
lemma boostAvgScalarProj_FF_c2310_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [fieldStrengthDeriv_mul_comm]
  rw [boostAvgScalarProj_F01_F23]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F32 * F01`. -/
lemma boostAvgScalarProj_FF_c3201_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) =
        -(fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [fieldStrengthDeriv_mul_comm]
  rw [boostAvgScalarProj_F01_F23]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F32 * F10`. -/
lemma boostAvgScalarProj_FF_c3210_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) =
        -(fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [fieldStrengthDeriv_mul_comm]
  rw [boostAvgScalarProj_F01_F23]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F23 * F23`. -/
lemma boostAvgScalarProj_FF_c2323_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [boostAvgScalarProj_F23_F23]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered square `F23 * F32`. -/
lemma boostAvgScalarProj_FF_c2332_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) =
        -(fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [boostAvgScalarProj_F23_F23]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F32 * F23`. -/
lemma boostAvgScalarProj_FF_c3223_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) =
        -(fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [boostAvgScalarProj_F23_F23]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F32 * F32`. -/
lemma boostAvgScalarProj_FF_c3232_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) =
        -(fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [boostAvgScalarProj_F23_F23]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered square `F02 * F02`. -/
lemma boostAvgScalarProj_FF_c0202_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [boostAvgScalarProj_F02_F02]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered square `F02 * F20`. -/
lemma boostAvgScalarProj_FF_c0220_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [boostAvgScalarProj_F02_F02]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F20 * F02`. -/
lemma boostAvgScalarProj_FF_c2002_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [boostAvgScalarProj_F02_F02]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F20 * F20`. -/
lemma boostAvgScalarProj_FF_c2020_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [boostAvgScalarProj_F02_F02]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered square `F02 * F13`. -/
lemma boostAvgScalarProj_FF_c0213_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [boostAvgScalarProj_F02_F13]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F02 * F31`. -/
lemma boostAvgScalarProj_FF_c0231_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [boostAvgScalarProj_F02_F13]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F20 * F13`. -/
lemma boostAvgScalarProj_FF_c2013_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [boostAvgScalarProj_F02_F13]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F20 * F31`. -/
lemma boostAvgScalarProj_FF_c2031_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [boostAvgScalarProj_F02_F13]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F13 * F02`. -/
lemma boostAvgScalarProj_FF_c1302_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_mul_comm]
  rw [boostAvgScalarProj_F02_F13]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F13 * F20`. -/
lemma boostAvgScalarProj_FF_c1320_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [fieldStrengthDeriv_mul_comm]
  rw [boostAvgScalarProj_F02_F13]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F31 * F02`. -/
lemma boostAvgScalarProj_FF_c3102_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [fieldStrengthDeriv_mul_comm]
  rw [boostAvgScalarProj_F02_F13]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F31 * F20`. -/
lemma boostAvgScalarProj_FF_c3120_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [fieldStrengthDeriv_mul_comm]
  rw [boostAvgScalarProj_F02_F13]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F13 * F13`. -/
lemma boostAvgScalarProj_FF_c1313_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [boostAvgScalarProj_F13_F13]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered square `F13 * F31`. -/
lemma boostAvgScalarProj_FF_c1331_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [boostAvgScalarProj_F13_F13]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F31 * F13`. -/
lemma boostAvgScalarProj_FF_c3113_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [boostAvgScalarProj_F13_F13]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F31 * F31`. -/
lemma boostAvgScalarProj_FF_c3131_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [boostAvgScalarProj_F13_F13]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered square `F03 * F03`. -/
lemma boostAvgScalarProj_FF_c0303_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [boostAvgScalarProj_F03_F03]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered square `F03 * F30`. -/
lemma boostAvgScalarProj_FF_c0330_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [boostAvgScalarProj_F03_F03]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F30 * F03`. -/
lemma boostAvgScalarProj_FF_c3003_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [boostAvgScalarProj_F03_F03]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F30 * F30`. -/
lemma boostAvgScalarProj_FF_c3030_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [boostAvgScalarProj_F03_F03]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered square `F03 * F12`. -/
lemma boostAvgScalarProj_FF_c0312_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [boostAvgScalarProj_F03_F12]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F03 * F21`. -/
lemma boostAvgScalarProj_FF_c0321_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [boostAvgScalarProj_F03_F12]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F30 * F12`. -/
lemma boostAvgScalarProj_FF_c3012_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [boostAvgScalarProj_F03_F12]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F30 * F21`. -/
lemma boostAvgScalarProj_FF_c3021_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [boostAvgScalarProj_F03_F12]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F12 * F03`. -/
lemma boostAvgScalarProj_FF_c1203_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_mul_comm]
  rw [boostAvgScalarProj_F03_F12]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F12 * F30`. -/
lemma boostAvgScalarProj_FF_c1230_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [fieldStrengthDeriv_mul_comm]
  rw [boostAvgScalarProj_F03_F12]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F21 * F03`. -/
lemma boostAvgScalarProj_FF_c2103_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [fieldStrengthDeriv_mul_comm]
  rw [boostAvgScalarProj_F03_F12]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F21 * F30`. -/
lemma boostAvgScalarProj_FF_c2130_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [fieldStrengthDeriv_mul_comm]
  rw [boostAvgScalarProj_F03_F12]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F12 * F12`. -/
lemma boostAvgScalarProj_FF_c1212_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [boostAvgScalarProj_F12_F12]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered square `F12 * F21`. -/
lemma boostAvgScalarProj_FF_c1221_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [boostAvgScalarProj_F12_F12]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F21 * F12`. -/
lemma boostAvgScalarProj_FF_c2112_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [boostAvgScalarProj_F12_F12]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F21 * F21`. -/
lemma boostAvgScalarProj_FF_c2121_mem :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    jetNeg_mul, jetMul_neg, neg_neg, map_neg]
  rw [boostAvgScalarProj_F12_F12]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered derivative monomial `dd01 F01`. -/
lemma boostAvgScalarProj_DDF_c0101_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [boostAvgScalarProj_dd01_F01]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd01 F10`. -/
lemma boostAvgScalarProj_DDF_c0110_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 0) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 0) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) from
            fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 0} _ _]
  rw [map_neg, boostAvgScalarProj_dd01_F01, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd10 F01`. -/
lemma boostAvgScalarProj_DDF_c1001_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 0, Sum.inl 0} (Sum.inl 0) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 0) (Sum.inl 0)]
  rw [boostAvgScalarProj_dd01_F01]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd10 F10`. -/
lemma boostAvgScalarProj_DDF_c1010_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 0, Sum.inl 0} (Sum.inr 0) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 0) (Sum.inl 0)]
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 0) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) from
            fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 0} _ _]
  rw [map_neg, boostAvgScalarProj_dd01_F01, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd01 F23`. -/
lemma boostAvgScalarProj_DDF_c0123_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [boostAvgScalarProj_dd01_F23]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd01 F32`. -/
lemma boostAvgScalarProj_DDF_c0132_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 2) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 2) (Sum.inr 1) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) from
            fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 0} _ _]
  rw [map_neg, boostAvgScalarProj_dd01_F23, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd10 F23`. -/
lemma boostAvgScalarProj_DDF_c1023_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 0, Sum.inl 0} (Sum.inr 1) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 0) (Sum.inl 0)]
  rw [boostAvgScalarProj_dd01_F23]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd10 F32`. -/
lemma boostAvgScalarProj_DDF_c1032_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 0, Sum.inl 0} (Sum.inr 2) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 0) (Sum.inl 0)]
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 2) (Sum.inr 1) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) from
            fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 0} _ _]
  rw [map_neg, boostAvgScalarProj_dd01_F23, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd02 F02`. -/
lemma boostAvgScalarProj_DDF_c0202_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [boostAvgScalarProj_dd02_F02]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd02 F20`. -/
lemma boostAvgScalarProj_DDF_c0220_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 1) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 1) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) from
            fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 1} _ _]
  rw [map_neg, boostAvgScalarProj_dd02_F02, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd20 F02`. -/
lemma boostAvgScalarProj_DDF_c2002_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 1, Sum.inl 0} (Sum.inl 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inl 0)]
  rw [boostAvgScalarProj_dd02_F02]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd20 F20`. -/
lemma boostAvgScalarProj_DDF_c2020_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 1, Sum.inl 0} (Sum.inr 1) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inl 0)]
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 1) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) from
            fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 1} _ _]
  rw [map_neg, boostAvgScalarProj_dd02_F02, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd02 F13`. -/
lemma boostAvgScalarProj_DDF_c0213_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [boostAvgScalarProj_dd02_F13]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd02 F31`. -/
lemma boostAvgScalarProj_DDF_c0231_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 2) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 2) (Sum.inr 0) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) from
            fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 1} _ _]
  rw [map_neg, boostAvgScalarProj_dd02_F13, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd20 F13`. -/
lemma boostAvgScalarProj_DDF_c2013_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 1, Sum.inl 0} (Sum.inr 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inl 0)]
  rw [boostAvgScalarProj_dd02_F13]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd20 F31`. -/
lemma boostAvgScalarProj_DDF_c2031_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 1, Sum.inl 0} (Sum.inr 2) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inl 0)]
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 2) (Sum.inr 0) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) from
            fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 1} _ _]
  rw [map_neg, boostAvgScalarProj_dd02_F13, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd03 F03`. -/
lemma boostAvgScalarProj_DDF_c0303_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [boostAvgScalarProj_dd03_F03]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd03 F30`. -/
lemma boostAvgScalarProj_DDF_c0330_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 2) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 2) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) from
            fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 2} _ _]
  rw [map_neg, boostAvgScalarProj_dd03_F03, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd30 F03`. -/
lemma boostAvgScalarProj_DDF_c3003_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 2, Sum.inl 0} (Sum.inl 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inl 0)]
  rw [boostAvgScalarProj_dd03_F03]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd30 F30`. -/
lemma boostAvgScalarProj_DDF_c3030_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 2, Sum.inl 0} (Sum.inr 2) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inl 0)]
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 2) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) from
            fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 2} _ _]
  rw [map_neg, boostAvgScalarProj_dd03_F03, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd03 F12`. -/
lemma boostAvgScalarProj_DDF_c0312_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [boostAvgScalarProj_dd03_F12]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd03 F21`. -/
lemma boostAvgScalarProj_DDF_c0321_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 1) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 1) (Sum.inr 0) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) from
            fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 2} _ _]
  rw [map_neg, boostAvgScalarProj_dd03_F12, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd30 F12`. -/
lemma boostAvgScalarProj_DDF_c3012_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 2, Sum.inl 0} (Sum.inr 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inl 0)]
  rw [boostAvgScalarProj_dd03_F12]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd30 F21`. -/
lemma boostAvgScalarProj_DDF_c3021_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 2, Sum.inl 0} (Sum.inr 1) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inl 0)]
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 1) (Sum.inr 0) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) from
            fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 2} _ _]
  rw [map_neg, boostAvgScalarProj_dd03_F12, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd12 F03`. -/
lemma boostAvgScalarProj_DDF_c1203_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [boostAvgScalarProj_dd12_F03]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd12 F30`. -/
lemma boostAvgScalarProj_DDF_c1230_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 2) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 2) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) from
            fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 1} _ _]
  rw [map_neg, boostAvgScalarProj_dd12_F03, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd21 F03`. -/
lemma boostAvgScalarProj_DDF_c2103_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 1, Sum.inr 0} (Sum.inl 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inr 0)]
  rw [boostAvgScalarProj_dd12_F03]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd21 F30`. -/
lemma boostAvgScalarProj_DDF_c2130_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 1, Sum.inr 0} (Sum.inr 2) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inr 0)]
  rw [show fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 2) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) from
            fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 1} _ _]
  rw [map_neg, boostAvgScalarProj_dd12_F03, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd12 F12`. -/
lemma boostAvgScalarProj_DDF_c1212_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [boostAvgScalarProj_dd12_F12]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd12 F21`. -/
lemma boostAvgScalarProj_DDF_c1221_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 1) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 1) (Sum.inr 0) =
        -(fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) from
            fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 1} _ _]
  rw [map_neg, boostAvgScalarProj_dd12_F12, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd21 F12`. -/
lemma boostAvgScalarProj_DDF_c2112_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 1, Sum.inr 0} (Sum.inr 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inr 0)]
  rw [boostAvgScalarProj_dd12_F12]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd21 F21`. -/
lemma boostAvgScalarProj_DDF_c2121_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 1, Sum.inr 0} (Sum.inr 1) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inr 0)]
  rw [show fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 1) (Sum.inr 0) =
        -(fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) from
            fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 1} _ _]
  rw [map_neg, boostAvgScalarProj_dd12_F12, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd13 F02`. -/
lemma boostAvgScalarProj_DDF_c1302_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [boostAvgScalarProj_dd13_F02]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd13 F20`. -/
lemma boostAvgScalarProj_DDF_c1320_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 1) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 1) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) from
            fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 2} _ _]
  rw [map_neg, boostAvgScalarProj_dd13_F02, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd31 F02`. -/
lemma boostAvgScalarProj_DDF_c3102_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 2, Sum.inr 0} (Sum.inl 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inr 0)]
  rw [boostAvgScalarProj_dd13_F02]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd31 F20`. -/
lemma boostAvgScalarProj_DDF_c3120_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 2, Sum.inr 0} (Sum.inr 1) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inr 0)]
  rw [show fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 1) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) from
            fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 2} _ _]
  rw [map_neg, boostAvgScalarProj_dd13_F02, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd13 F13`. -/
lemma boostAvgScalarProj_DDF_c1313_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [boostAvgScalarProj_dd13_F13]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd13 F31`. -/
lemma boostAvgScalarProj_DDF_c1331_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 2) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 2) (Sum.inr 0) =
        -(fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) from
            fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 2} _ _]
  rw [map_neg, boostAvgScalarProj_dd13_F13, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd31 F13`. -/
lemma boostAvgScalarProj_DDF_c3113_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 2, Sum.inr 0} (Sum.inr 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inr 0)]
  rw [boostAvgScalarProj_dd13_F13]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd31 F31`. -/
lemma boostAvgScalarProj_DDF_c3131_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 2, Sum.inr 0} (Sum.inr 2) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inr 0)]
  rw [show fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 2) (Sum.inr 0) =
        -(fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) from
            fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 2} _ _]
  rw [map_neg, boostAvgScalarProj_dd13_F13, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd23 F01`. -/
lemma boostAvgScalarProj_DDF_c2301_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [boostAvgScalarProj_dd23_F01]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd23 F10`. -/
lemma boostAvgScalarProj_DDF_c2310_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 0) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 0) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) from
            fieldStrengthDeriv_antisymm {Sum.inr 1, Sum.inr 2} _ _]
  rw [map_neg, boostAvgScalarProj_dd23_F01, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd32 F01`. -/
lemma boostAvgScalarProj_DDF_c3201_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 2, Sum.inr 1} (Sum.inl 0) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inr 1)]
  rw [boostAvgScalarProj_dd23_F01]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd32 F10`. -/
lemma boostAvgScalarProj_DDF_c3210_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 2, Sum.inr 1} (Sum.inr 0) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inr 1)]
  rw [show fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 0) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) from
            fieldStrengthDeriv_antisymm {Sum.inr 1, Sum.inr 2} _ _]
  rw [map_neg, boostAvgScalarProj_dd23_F01, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd23 F23`. -/
lemma boostAvgScalarProj_DDF_c2323_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [boostAvgScalarProj_dd23_F23]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd23 F32`. -/
lemma boostAvgScalarProj_DDF_c2332_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 2) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 2) (Sum.inr 1) =
        -(fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) from
            fieldStrengthDeriv_antisymm {Sum.inr 1, Sum.inr 2} _ _]
  rw [map_neg, boostAvgScalarProj_dd23_F23, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd32 F23`. -/
lemma boostAvgScalarProj_DDF_c3223_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 2, Sum.inr 1} (Sum.inr 1) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inr 1)]
  rw [boostAvgScalarProj_dd23_F23]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd32 F32`. -/
lemma boostAvgScalarProj_DDF_c3232_mem :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 2, Sum.inr 1} (Sum.inr 2) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inr 1)]
  rw [show fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 2) (Sum.inr 1) =
        -(fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) from
            fieldStrengthDeriv_antisymm {Sum.inr 1, Sum.inr 2} _ _]
  rw [map_neg, boostAvgScalarProj_dd23_F23, neg_zero]
  exact Submodule.zero_mem _

/-- Projected rotation average of `e[0,0,0]` (u-family) lies in the span. -/
lemma boostAvgScalarProj_rotationPiAvg_u000_mem :
    boostAvgScalarProj (rotationPiAvg (Dbarψ [] 0 * Dψ [Sum.inl 0] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [rotationPiAvg_u_e000, map_smul, boostAvgScalarProj_u0]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTerm_mem_span)

/-- Projected rotation average of `e[0,0,1]` (u-family) lies in the span. -/
lemma boostAvgScalarProj_rotationPiAvg_u001_mem :
    boostAvgScalarProj (rotationPiAvg (Dbarψ [] 0 * Dψ [Sum.inl 0] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [rotationPiAvg_u_e001, map_zero]
  exact Submodule.zero_mem _

/-- Projected rotation average of `e[0,1,0]` (u-family) lies in the span. -/
lemma boostAvgScalarProj_rotationPiAvg_u010_mem :
    boostAvgScalarProj (rotationPiAvg (Dbarψ [] 1 * Dψ [Sum.inl 0] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [rotationPiAvg_u_e010, map_zero]
  exact Submodule.zero_mem _

/-- Projected rotation average of `e[0,1,1]` (u-family) lies in the span. -/
lemma boostAvgScalarProj_rotationPiAvg_u011_mem :
    boostAvgScalarProj (rotationPiAvg (Dbarψ [] 1 * Dψ [Sum.inl 0] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [rotationPiAvg_u_e011, map_smul, boostAvgScalarProj_u0]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTerm_mem_span)

/-- Projected rotation average of `e[1,0,0]` (u-family) lies in the span. -/
lemma boostAvgScalarProj_rotationPiAvg_u100_mem :
    boostAvgScalarProj (rotationPiAvg (Dbarψ [] 0 * Dψ [Sum.inr 0] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [rotationPiAvg_u_e100, map_zero]
  exact Submodule.zero_mem _

/-- Projected rotation average of `e[1,0,1]` (u-family) lies in the span. -/
lemma boostAvgScalarProj_rotationPiAvg_u101_mem :
    boostAvgScalarProj (rotationPiAvg (Dbarψ [] 0 * Dψ [Sum.inr 0] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [rotationPiAvg_u_e101, map_smul, boostAvgScalarProj_u1]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTerm_mem_span)

/-- Projected rotation average of `e[1,1,0]` (u-family) lies in the span. -/
lemma boostAvgScalarProj_rotationPiAvg_u110_mem :
    boostAvgScalarProj (rotationPiAvg (Dbarψ [] 1 * Dψ [Sum.inr 0] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [rotationPiAvg_u_e110, map_smul, boostAvgScalarProj_u1]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTerm_mem_span)

/-- Projected rotation average of `e[1,1,1]` (u-family) lies in the span. -/
lemma boostAvgScalarProj_rotationPiAvg_u111_mem :
    boostAvgScalarProj (rotationPiAvg (Dbarψ [] 1 * Dψ [Sum.inr 0] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [rotationPiAvg_u_e111, map_zero]
  exact Submodule.zero_mem _

/-- Projected rotation average of `e[2,0,0]` (u-family) lies in the span. -/
lemma boostAvgScalarProj_rotationPiAvg_u200_mem :
    boostAvgScalarProj (rotationPiAvg (Dbarψ [] 0 * Dψ [Sum.inr 1] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [rotationPiAvg_u_e200, map_zero]
  exact Submodule.zero_mem _

/-- Projected rotation average of `e[2,0,1]` (u-family) lies in the span. -/
lemma boostAvgScalarProj_rotationPiAvg_u201_mem :
    boostAvgScalarProj (rotationPiAvg (Dbarψ [] 0 * Dψ [Sum.inr 1] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [rotationPiAvg_u_e201, map_smul, boostAvgScalarProj_u2]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTerm_mem_span)

/-- Projected rotation average of `e[2,1,0]` (u-family) lies in the span. -/
lemma boostAvgScalarProj_rotationPiAvg_u210_mem :
    boostAvgScalarProj (rotationPiAvg (Dbarψ [] 1 * Dψ [Sum.inr 1] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [rotationPiAvg_u_e210, map_smul, boostAvgScalarProj_u2]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTerm_mem_span)

/-- Projected rotation average of `e[2,1,1]` (u-family) lies in the span. -/
lemma boostAvgScalarProj_rotationPiAvg_u211_mem :
    boostAvgScalarProj (rotationPiAvg (Dbarψ [] 1 * Dψ [Sum.inr 1] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [rotationPiAvg_u_e211, map_zero]
  exact Submodule.zero_mem _

/-- Projected rotation average of `e[3,0,0]` (u-family) lies in the span. -/
lemma boostAvgScalarProj_rotationPiAvg_u300_mem :
    boostAvgScalarProj (rotationPiAvg (Dbarψ [] 0 * Dψ [Sum.inr 2] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [rotationPiAvg_u_e300, map_smul, boostAvgScalarProj_u3]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTerm_mem_span)

/-- Projected rotation average of `e[3,0,1]` (u-family) lies in the span. -/
lemma boostAvgScalarProj_rotationPiAvg_u301_mem :
    boostAvgScalarProj (rotationPiAvg (Dbarψ [] 0 * Dψ [Sum.inr 2] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [rotationPiAvg_u_e301, map_zero]
  exact Submodule.zero_mem _

/-- Projected rotation average of `e[3,1,0]` (u-family) lies in the span. -/
lemma boostAvgScalarProj_rotationPiAvg_u310_mem :
    boostAvgScalarProj (rotationPiAvg (Dbarψ [] 1 * Dψ [Sum.inr 2] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [rotationPiAvg_u_e310, map_zero]
  exact Submodule.zero_mem _

/-- Projected rotation average of `e[3,1,1]` (u-family) lies in the span. -/
lemma boostAvgScalarProj_rotationPiAvg_u311_mem :
    boostAvgScalarProj (rotationPiAvg (Dbarψ [] 1 * Dψ [Sum.inr 2] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [rotationPiAvg_u_e311, map_smul, boostAvgScalarProj_u3]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTerm_mem_span)

/-- Projected rotation average of `e[0,0,0]` (ubar-family) lies in the span. -/
lemma boostAvgScalarProj_rotationPiAvg_ubar000_mem :
    boostAvgScalarProj (rotationPiAvg (Dbarψ [Sum.inl 0] 0 * Dψ [] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [rotationPiAvg_ubar_e000, map_smul, boostAvgScalarProj_ubar0]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTermBar_mem_span)

/-- Projected rotation average of `e[0,0,1]` (ubar-family) lies in the span. -/
lemma boostAvgScalarProj_rotationPiAvg_ubar001_mem :
    boostAvgScalarProj (rotationPiAvg (Dbarψ [Sum.inl 0] 0 * Dψ [] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [rotationPiAvg_ubar_e001, map_zero]
  exact Submodule.zero_mem _

/-- Projected rotation average of `e[0,1,0]` (ubar-family) lies in the span. -/
lemma boostAvgScalarProj_rotationPiAvg_ubar010_mem :
    boostAvgScalarProj (rotationPiAvg (Dbarψ [Sum.inl 0] 1 * Dψ [] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [rotationPiAvg_ubar_e010, map_zero]
  exact Submodule.zero_mem _

/-- Projected rotation average of `e[0,1,1]` (ubar-family) lies in the span. -/
lemma boostAvgScalarProj_rotationPiAvg_ubar011_mem :
    boostAvgScalarProj (rotationPiAvg (Dbarψ [Sum.inl 0] 1 * Dψ [] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [rotationPiAvg_ubar_e011, map_smul, boostAvgScalarProj_ubar0]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTermBar_mem_span)

/-- Projected rotation average of `e[1,0,0]` (ubar-family) lies in the span. -/
lemma boostAvgScalarProj_rotationPiAvg_ubar100_mem :
    boostAvgScalarProj (rotationPiAvg (Dbarψ [Sum.inr 0] 0 * Dψ [] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [rotationPiAvg_ubar_e100, map_zero]
  exact Submodule.zero_mem _

/-- Projected rotation average of `e[1,0,1]` (ubar-family) lies in the span. -/
lemma boostAvgScalarProj_rotationPiAvg_ubar101_mem :
    boostAvgScalarProj (rotationPiAvg (Dbarψ [Sum.inr 0] 0 * Dψ [] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [rotationPiAvg_ubar_e101, map_smul, boostAvgScalarProj_ubar1]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTermBar_mem_span)

/-- Projected rotation average of `e[1,1,0]` (ubar-family) lies in the span. -/
lemma boostAvgScalarProj_rotationPiAvg_ubar110_mem :
    boostAvgScalarProj (rotationPiAvg (Dbarψ [Sum.inr 0] 1 * Dψ [] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [rotationPiAvg_ubar_e110, map_smul, boostAvgScalarProj_ubar1]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTermBar_mem_span)

/-- Projected rotation average of `e[1,1,1]` (ubar-family) lies in the span. -/
lemma boostAvgScalarProj_rotationPiAvg_ubar111_mem :
    boostAvgScalarProj (rotationPiAvg (Dbarψ [Sum.inr 0] 1 * Dψ [] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [rotationPiAvg_ubar_e111, map_zero]
  exact Submodule.zero_mem _

/-- Projected rotation average of `e[2,0,0]` (ubar-family) lies in the span. -/
lemma boostAvgScalarProj_rotationPiAvg_ubar200_mem :
    boostAvgScalarProj (rotationPiAvg (Dbarψ [Sum.inr 1] 0 * Dψ [] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [rotationPiAvg_ubar_e200, map_zero]
  exact Submodule.zero_mem _

/-- Projected rotation average of `e[2,0,1]` (ubar-family) lies in the span. -/
lemma boostAvgScalarProj_rotationPiAvg_ubar201_mem :
    boostAvgScalarProj (rotationPiAvg (Dbarψ [Sum.inr 1] 0 * Dψ [] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [rotationPiAvg_ubar_e201, map_smul, boostAvgScalarProj_ubar2]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTermBar_mem_span)

/-- Projected rotation average of `e[2,1,0]` (ubar-family) lies in the span. -/
lemma boostAvgScalarProj_rotationPiAvg_ubar210_mem :
    boostAvgScalarProj (rotationPiAvg (Dbarψ [Sum.inr 1] 1 * Dψ [] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [rotationPiAvg_ubar_e210, map_smul, boostAvgScalarProj_ubar2]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTermBar_mem_span)

/-- Projected rotation average of `e[2,1,1]` (ubar-family) lies in the span. -/
lemma boostAvgScalarProj_rotationPiAvg_ubar211_mem :
    boostAvgScalarProj (rotationPiAvg (Dbarψ [Sum.inr 1] 1 * Dψ [] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [rotationPiAvg_ubar_e211, map_zero]
  exact Submodule.zero_mem _

/-- Projected rotation average of `e[3,0,0]` (ubar-family) lies in the span. -/
lemma boostAvgScalarProj_rotationPiAvg_ubar300_mem :
    boostAvgScalarProj (rotationPiAvg (Dbarψ [Sum.inr 2] 0 * Dψ [] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [rotationPiAvg_ubar_e300, map_smul, boostAvgScalarProj_ubar3]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTermBar_mem_span)

/-- Projected rotation average of `e[3,0,1]` (ubar-family) lies in the span. -/
lemma boostAvgScalarProj_rotationPiAvg_ubar301_mem :
    boostAvgScalarProj (rotationPiAvg (Dbarψ [Sum.inr 2] 0 * Dψ [] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [rotationPiAvg_ubar_e301, map_zero]
  exact Submodule.zero_mem _

/-- Projected rotation average of `e[3,1,0]` (ubar-family) lies in the span. -/
lemma boostAvgScalarProj_rotationPiAvg_ubar310_mem :
    boostAvgScalarProj (rotationPiAvg (Dbarψ [Sum.inr 2] 1 * Dψ [] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [rotationPiAvg_ubar_e310, map_zero]
  exact Submodule.zero_mem _

/-- Projected rotation average of `e[3,1,1]` (ubar-family) lies in the span. -/
lemma boostAvgScalarProj_rotationPiAvg_ubar311_mem :
    boostAvgScalarProj (rotationPiAvg (Dbarψ [Sum.inr 2] 1 * Dψ [] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [rotationPiAvg_ubar_e311, map_smul, boostAvgScalarProj_ubar3]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTermBar_mem_span)

attribute [local irreducible] Dψ Dbarψ fieldStrengthDeriv

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 8192 in
/-- The projected rotation average of any product of two field strengths lies in
  the span of the invariants. -/
lemma boostAvgScalarProj_rotationPiAvg_FF_mem (a b c d : Fin 1 ⊕ Fin 3) :
    boostAvgScalarProj (rotationPiAvg (fieldStrengthDeriv {} a b * fieldStrengthDeriv {} c d)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [rotationPiAvg_fieldStrengthDeriv_nil_mul, map_smul]
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
    rcases d with d | d <;> fin_cases a <;> fin_cases b <;> fin_cases c <;>
    fin_cases d <;>
    (try simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]) <;>
    first
    | (rw [fieldStrengthDeriv_self]
       simp only [zero_mul, mul_zero, map_zero, smul_zero]
       exact Submodule.zero_mem _)
    | (refine Submodule.smul_mem _ _ ?_
       first
       | exact boostAvgScalarProj_FF_c0101_mem
       | exact boostAvgScalarProj_FF_c0110_mem
       | exact boostAvgScalarProj_FF_c1001_mem
       | exact boostAvgScalarProj_FF_c1010_mem
       | exact boostAvgScalarProj_FF_c0123_mem
       | exact boostAvgScalarProj_FF_c0132_mem
       | exact boostAvgScalarProj_FF_c1023_mem
       | exact boostAvgScalarProj_FF_c1032_mem
       | exact boostAvgScalarProj_FF_c2301_mem
       | exact boostAvgScalarProj_FF_c2310_mem
       | exact boostAvgScalarProj_FF_c3201_mem
       | exact boostAvgScalarProj_FF_c3210_mem
       | exact boostAvgScalarProj_FF_c2323_mem
       | exact boostAvgScalarProj_FF_c2332_mem
       | exact boostAvgScalarProj_FF_c3223_mem
       | exact boostAvgScalarProj_FF_c3232_mem
       | exact boostAvgScalarProj_FF_c0202_mem
       | exact boostAvgScalarProj_FF_c0220_mem
       | exact boostAvgScalarProj_FF_c2002_mem
       | exact boostAvgScalarProj_FF_c2020_mem
       | exact boostAvgScalarProj_FF_c0213_mem
       | exact boostAvgScalarProj_FF_c0231_mem
       | exact boostAvgScalarProj_FF_c2013_mem
       | exact boostAvgScalarProj_FF_c2031_mem
       | exact boostAvgScalarProj_FF_c1302_mem
       | exact boostAvgScalarProj_FF_c1320_mem
       | exact boostAvgScalarProj_FF_c3102_mem
       | exact boostAvgScalarProj_FF_c3120_mem
       | exact boostAvgScalarProj_FF_c1313_mem
       | exact boostAvgScalarProj_FF_c1331_mem
       | exact boostAvgScalarProj_FF_c3113_mem
       | exact boostAvgScalarProj_FF_c3131_mem
       | exact boostAvgScalarProj_FF_c0303_mem
       | exact boostAvgScalarProj_FF_c0330_mem
       | exact boostAvgScalarProj_FF_c3003_mem
       | exact boostAvgScalarProj_FF_c3030_mem
       | exact boostAvgScalarProj_FF_c0312_mem
       | exact boostAvgScalarProj_FF_c0321_mem
       | exact boostAvgScalarProj_FF_c3012_mem
       | exact boostAvgScalarProj_FF_c3021_mem
       | exact boostAvgScalarProj_FF_c1203_mem
       | exact boostAvgScalarProj_FF_c1230_mem
       | exact boostAvgScalarProj_FF_c2103_mem
       | exact boostAvgScalarProj_FF_c2130_mem
       | exact boostAvgScalarProj_FF_c1212_mem
       | exact boostAvgScalarProj_FF_c1221_mem
       | exact boostAvgScalarProj_FF_c2112_mem
       | exact boostAvgScalarProj_FF_c2121_mem)
    | (norm_num [rotationPiSignZ, rotationPiSignY, rotationPiSignX]
       first
       | done
       | exact Submodule.zero_mem _)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 8192 in
/-- The projected rotation average of any second-derivative field strength lies
  in the span of the invariants. -/
lemma boostAvgScalarProj_rotationPiAvg_DDF_mem (r t a b : Fin 1 ⊕ Fin 3) :
    boostAvgScalarProj (rotationPiAvg (fieldStrengthDeriv {r, t} a b)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [rotationPiAvg_fieldStrengthDeriv_pair, map_smul]
  rcases r with r | r <;> rcases t with t | t <;> rcases a with a | a <;>
    rcases b with b | b <;> fin_cases r <;> fin_cases t <;> fin_cases a <;>
    fin_cases b <;>
    (try simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]) <;>
    first
    | (rw [fieldStrengthDeriv_self]
       simp only [map_zero, smul_zero]
       exact Submodule.zero_mem _)
    | (refine Submodule.smul_mem _ _ ?_
       first
       | exact boostAvgScalarProj_DDF_c0101_mem
       | exact boostAvgScalarProj_DDF_c0110_mem
       | exact boostAvgScalarProj_DDF_c1001_mem
       | exact boostAvgScalarProj_DDF_c1010_mem
       | exact boostAvgScalarProj_DDF_c0123_mem
       | exact boostAvgScalarProj_DDF_c0132_mem
       | exact boostAvgScalarProj_DDF_c1023_mem
       | exact boostAvgScalarProj_DDF_c1032_mem
       | exact boostAvgScalarProj_DDF_c0202_mem
       | exact boostAvgScalarProj_DDF_c0220_mem
       | exact boostAvgScalarProj_DDF_c2002_mem
       | exact boostAvgScalarProj_DDF_c2020_mem
       | exact boostAvgScalarProj_DDF_c0213_mem
       | exact boostAvgScalarProj_DDF_c0231_mem
       | exact boostAvgScalarProj_DDF_c2013_mem
       | exact boostAvgScalarProj_DDF_c2031_mem
       | exact boostAvgScalarProj_DDF_c0303_mem
       | exact boostAvgScalarProj_DDF_c0330_mem
       | exact boostAvgScalarProj_DDF_c3003_mem
       | exact boostAvgScalarProj_DDF_c3030_mem
       | exact boostAvgScalarProj_DDF_c0312_mem
       | exact boostAvgScalarProj_DDF_c0321_mem
       | exact boostAvgScalarProj_DDF_c3012_mem
       | exact boostAvgScalarProj_DDF_c3021_mem
       | exact boostAvgScalarProj_DDF_c1203_mem
       | exact boostAvgScalarProj_DDF_c1230_mem
       | exact boostAvgScalarProj_DDF_c2103_mem
       | exact boostAvgScalarProj_DDF_c2130_mem
       | exact boostAvgScalarProj_DDF_c1212_mem
       | exact boostAvgScalarProj_DDF_c1221_mem
       | exact boostAvgScalarProj_DDF_c2112_mem
       | exact boostAvgScalarProj_DDF_c2121_mem
       | exact boostAvgScalarProj_DDF_c1302_mem
       | exact boostAvgScalarProj_DDF_c1320_mem
       | exact boostAvgScalarProj_DDF_c3102_mem
       | exact boostAvgScalarProj_DDF_c3120_mem
       | exact boostAvgScalarProj_DDF_c1313_mem
       | exact boostAvgScalarProj_DDF_c1331_mem
       | exact boostAvgScalarProj_DDF_c3113_mem
       | exact boostAvgScalarProj_DDF_c3131_mem
       | exact boostAvgScalarProj_DDF_c2301_mem
       | exact boostAvgScalarProj_DDF_c2310_mem
       | exact boostAvgScalarProj_DDF_c3201_mem
       | exact boostAvgScalarProj_DDF_c3210_mem
       | exact boostAvgScalarProj_DDF_c2323_mem
       | exact boostAvgScalarProj_DDF_c2332_mem
       | exact boostAvgScalarProj_DDF_c3223_mem
       | exact boostAvgScalarProj_DDF_c3232_mem)
    | (norm_num [rotationPiSignZ, rotationPiSignY, rotationPiSignX]
       first
       | done
       | exact Submodule.zero_mem _)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 8192 in
/-- The projected rotation average of any `ψ̄ (Dψ)` pair lies in the span. -/
lemma boostAvgScalarProj_rotationPiAvg_FM1_mem (μ : Fin 1 ⊕ Fin 3) (α β : Fin 2) :
    boostAvgScalarProj (rotationPiAvg (Dbarψ [] α * Dψ [μ] β)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rcases μ with m | m <;> fin_cases m <;> fin_cases α <;> fin_cases β <;>
    (try simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]) <;>
    first
    | exact boostAvgScalarProj_rotationPiAvg_u000_mem
    | exact boostAvgScalarProj_rotationPiAvg_u001_mem
    | exact boostAvgScalarProj_rotationPiAvg_u010_mem
    | exact boostAvgScalarProj_rotationPiAvg_u011_mem
    | exact boostAvgScalarProj_rotationPiAvg_u100_mem
    | exact boostAvgScalarProj_rotationPiAvg_u101_mem
    | exact boostAvgScalarProj_rotationPiAvg_u110_mem
    | exact boostAvgScalarProj_rotationPiAvg_u111_mem
    | exact boostAvgScalarProj_rotationPiAvg_u200_mem
    | exact boostAvgScalarProj_rotationPiAvg_u201_mem
    | exact boostAvgScalarProj_rotationPiAvg_u210_mem
    | exact boostAvgScalarProj_rotationPiAvg_u211_mem
    | exact boostAvgScalarProj_rotationPiAvg_u300_mem
    | exact boostAvgScalarProj_rotationPiAvg_u301_mem
    | exact boostAvgScalarProj_rotationPiAvg_u310_mem
    | exact boostAvgScalarProj_rotationPiAvg_u311_mem

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 8192 in
/-- The projected rotation average of any `(D̄ψ̄) ψ` pair lies in the span. -/
lemma boostAvgScalarProj_rotationPiAvg_FM2_mem (μ : Fin 1 ⊕ Fin 3) (α β : Fin 2) :
    boostAvgScalarProj (rotationPiAvg (Dbarψ [μ] α * Dψ [] β)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rcases μ with m | m <;> fin_cases m <;> fin_cases α <;> fin_cases β <;>
    (try simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]) <;>
    first
    | exact boostAvgScalarProj_rotationPiAvg_ubar000_mem
    | exact boostAvgScalarProj_rotationPiAvg_ubar001_mem
    | exact boostAvgScalarProj_rotationPiAvg_ubar010_mem
    | exact boostAvgScalarProj_rotationPiAvg_ubar011_mem
    | exact boostAvgScalarProj_rotationPiAvg_ubar100_mem
    | exact boostAvgScalarProj_rotationPiAvg_ubar101_mem
    | exact boostAvgScalarProj_rotationPiAvg_ubar110_mem
    | exact boostAvgScalarProj_rotationPiAvg_ubar111_mem
    | exact boostAvgScalarProj_rotationPiAvg_ubar200_mem
    | exact boostAvgScalarProj_rotationPiAvg_ubar201_mem
    | exact boostAvgScalarProj_rotationPiAvg_ubar210_mem
    | exact boostAvgScalarProj_rotationPiAvg_ubar211_mem
    | exact boostAvgScalarProj_rotationPiAvg_ubar300_mem
    | exact boostAvgScalarProj_rotationPiAvg_ubar301_mem
    | exact boostAvgScalarProj_rotationPiAvg_ubar310_mem
    | exact boostAvgScalarProj_rotationPiAvg_ubar311_mem

/-- The reversed pair `(Dψ) ψ̄`, via anticommutation. -/
lemma boostAvgScalarProj_rotationPiAvg_FM1r_mem (μ : Fin 1 ⊕ Fin 3) (α β : Fin 2) :
    boostAvgScalarProj (rotationPiAvg (Dψ [μ] β * Dbarψ [] α)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [Dψ_mul_Dbarψ_anticomm, map_neg, map_neg]
  exact neg_mem (boostAvgScalarProj_rotationPiAvg_FM1_mem μ α β)

/-- The reversed pair `ψ (D̄ψ̄)`, via anticommutation. -/
lemma boostAvgScalarProj_rotationPiAvg_FM2r_mem (μ : Fin 1 ⊕ Fin 3) (α β : Fin 2) :
    boostAvgScalarProj (rotationPiAvg (Dψ [] α * Dbarψ [μ] β)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [Dψ_mul_Dbarψ_anticomm, map_neg, map_neg]
  exact neg_mem (boostAvgScalarProj_rotationPiAvg_FM2_mem μ β α)
end JetAlgebra

end LeptonGaugeSector
