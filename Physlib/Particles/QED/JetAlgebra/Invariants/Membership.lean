/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.QED.JetAlgebra.Invariants.KleinAverage
/-!
# The projected weight-eight monomials lie in the span

Every weight-eight monomial, after Klein-averaging and applying the projector
`opPi`, lands in the span of the four renormalizable invariants. Together with
`opPi_apply_of_invariant` this is the last input to the classification
theorem.
-/

@[expose] public section

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace QED
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

/-- Projector membership for the ordered square `F01 * F01`. -/
lemma opPi_FF_c0101_mem :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_F01_F01]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered square `F01 * F10`. -/
lemma opPi_FF_c0110_mem :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [opPi_F01_F01]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F10 * F01`. -/
lemma opPi_FF_c1001_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [opPi_F01_F01]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F10 * F10`. -/
lemma opPi_FF_c1010_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [opPi_F01_F01]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered square `F01 * F23`. -/
lemma opPi_FF_c0123_mem :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_F01_F23]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F01 * F32`. -/
lemma opPi_FF_c0132_mem :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) =
        -(fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [opPi_F01_F23]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F10 * F23`. -/
lemma opPi_FF_c1023_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [opPi_F01_F23]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F10 * F32`. -/
lemma opPi_FF_c1032_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) from fieldStrengthDeriv_antisymm {} _ _,
    show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) =
        -(fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [opPi_F01_F23]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F23 * F01`. -/
lemma opPi_FF_c2301_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_mul_comm]
  rw [opPi_F01_F23]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F23 * F10`. -/
lemma opPi_FF_c2310_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [fieldStrengthDeriv_mul_comm]
  rw [opPi_F01_F23]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F32 * F01`. -/
lemma opPi_FF_c3201_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) =
        -(fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [fieldStrengthDeriv_mul_comm]
  rw [opPi_F01_F23]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F32 * F10`. -/
lemma opPi_FF_c3210_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) =
        -(fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [fieldStrengthDeriv_mul_comm]
  rw [opPi_F01_F23]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F23 * F23`. -/
lemma opPi_FF_c2323_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_F23_F23]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered square `F23 * F32`. -/
lemma opPi_FF_c2332_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) =
        -(fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [opPi_F23_F23]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F32 * F23`. -/
lemma opPi_FF_c3223_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) =
        -(fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [opPi_F23_F23]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F32 * F32`. -/
lemma opPi_FF_c3232_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) =
        -(fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [opPi_F23_F23]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered square `F02 * F02`. -/
lemma opPi_FF_c0202_mem :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_F02_F02]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered square `F02 * F20`. -/
lemma opPi_FF_c0220_mem :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [opPi_F02_F02]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F20 * F02`. -/
lemma opPi_FF_c2002_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [opPi_F02_F02]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F20 * F20`. -/
lemma opPi_FF_c2020_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [opPi_F02_F02]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered square `F02 * F13`. -/
lemma opPi_FF_c0213_mem :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_F02_F13]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F02 * F31`. -/
lemma opPi_FF_c0231_mem :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [opPi_F02_F13]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F20 * F13`. -/
lemma opPi_FF_c2013_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [opPi_F02_F13]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F20 * F31`. -/
lemma opPi_FF_c2031_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [opPi_F02_F13]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F13 * F02`. -/
lemma opPi_FF_c1302_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_mul_comm]
  rw [opPi_F02_F13]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F13 * F20`. -/
lemma opPi_FF_c1320_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [fieldStrengthDeriv_mul_comm]
  rw [opPi_F02_F13]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F31 * F02`. -/
lemma opPi_FF_c3102_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [fieldStrengthDeriv_mul_comm]
  rw [opPi_F02_F13]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F31 * F20`. -/
lemma opPi_FF_c3120_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [fieldStrengthDeriv_mul_comm]
  rw [opPi_F02_F13]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F13 * F13`. -/
lemma opPi_FF_c1313_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_F13_F13]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered square `F13 * F31`. -/
lemma opPi_FF_c1331_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [opPi_F13_F13]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F31 * F13`. -/
lemma opPi_FF_c3113_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [opPi_F13_F13]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F31 * F31`. -/
lemma opPi_FF_c3131_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [opPi_F13_F13]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered square `F03 * F03`. -/
lemma opPi_FF_c0303_mem :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_F03_F03]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered square `F03 * F30`. -/
lemma opPi_FF_c0330_mem :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [opPi_F03_F03]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F30 * F03`. -/
lemma opPi_FF_c3003_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [opPi_F03_F03]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F30 * F30`. -/
lemma opPi_FF_c3030_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [opPi_F03_F03]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered square `F03 * F12`. -/
lemma opPi_FF_c0312_mem :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_F03_F12]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F03 * F21`. -/
lemma opPi_FF_c0321_mem :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [opPi_F03_F12]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F30 * F12`. -/
lemma opPi_FF_c3012_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [opPi_F03_F12]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F30 * F21`. -/
lemma opPi_FF_c3021_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [opPi_F03_F12]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F12 * F03`. -/
lemma opPi_FF_c1203_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_mul_comm]
  rw [opPi_F03_F12]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F12 * F30`. -/
lemma opPi_FF_c1230_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [fieldStrengthDeriv_mul_comm]
  rw [opPi_F03_F12]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F21 * F03`. -/
lemma opPi_FF_c2103_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [fieldStrengthDeriv_mul_comm]
  rw [opPi_F03_F12]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F21 * F30`. -/
lemma opPi_FF_c2130_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [fieldStrengthDeriv_mul_comm]
  rw [opPi_F03_F12]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F12 * F12`. -/
lemma opPi_FF_c1212_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_F12_F12]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered square `F12 * F21`. -/
lemma opPi_FF_c1221_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [opPi_F12_F12]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F21 * F12`. -/
lemma opPi_FF_c2112_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [opPi_F12_F12]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F21 * F21`. -/
lemma opPi_FF_c2121_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul, mul_neg, neg_neg, map_neg]
  rw [opPi_F12_F12]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered derivative monomial `dd01 F01`. -/
lemma opPi_DDF_c0101_mem :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_dd01_F01]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd01 F10`. -/
lemma opPi_DDF_c0110_mem :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 0) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 0) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) from
            fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 0} _ _]
  rw [map_neg, opPi_dd01_F01, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd10 F01`. -/
lemma opPi_DDF_c1001_mem :
    opPi (fieldStrengthDeriv {Sum.inr 0, Sum.inl 0} (Sum.inl 0) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 0) (Sum.inl 0)]
  rw [opPi_dd01_F01]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd10 F10`. -/
lemma opPi_DDF_c1010_mem :
    opPi (fieldStrengthDeriv {Sum.inr 0, Sum.inl 0} (Sum.inr 0) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 0) (Sum.inl 0)]
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 0) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) from
            fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 0} _ _]
  rw [map_neg, opPi_dd01_F01, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd01 F23`. -/
lemma opPi_DDF_c0123_mem :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_dd01_F23]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd01 F32`. -/
lemma opPi_DDF_c0132_mem :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 2) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 2) (Sum.inr 1) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) from
            fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 0} _ _]
  rw [map_neg, opPi_dd01_F23, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd10 F23`. -/
lemma opPi_DDF_c1023_mem :
    opPi (fieldStrengthDeriv {Sum.inr 0, Sum.inl 0} (Sum.inr 1) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 0) (Sum.inl 0)]
  rw [opPi_dd01_F23]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd10 F32`. -/
lemma opPi_DDF_c1032_mem :
    opPi (fieldStrengthDeriv {Sum.inr 0, Sum.inl 0} (Sum.inr 2) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 0) (Sum.inl 0)]
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 2) (Sum.inr 1) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) from
            fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 0} _ _]
  rw [map_neg, opPi_dd01_F23, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd02 F02`. -/
lemma opPi_DDF_c0202_mem :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_dd02_F02]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd02 F20`. -/
lemma opPi_DDF_c0220_mem :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 1) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 1) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) from
            fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 1} _ _]
  rw [map_neg, opPi_dd02_F02, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd20 F02`. -/
lemma opPi_DDF_c2002_mem :
    opPi (fieldStrengthDeriv {Sum.inr 1, Sum.inl 0} (Sum.inl 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inl 0)]
  rw [opPi_dd02_F02]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd20 F20`. -/
lemma opPi_DDF_c2020_mem :
    opPi (fieldStrengthDeriv {Sum.inr 1, Sum.inl 0} (Sum.inr 1) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inl 0)]
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 1) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) from
            fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 1} _ _]
  rw [map_neg, opPi_dd02_F02, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd02 F13`. -/
lemma opPi_DDF_c0213_mem :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_dd02_F13]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd02 F31`. -/
lemma opPi_DDF_c0231_mem :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 2) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 2) (Sum.inr 0) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) from
            fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 1} _ _]
  rw [map_neg, opPi_dd02_F13, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd20 F13`. -/
lemma opPi_DDF_c2013_mem :
    opPi (fieldStrengthDeriv {Sum.inr 1, Sum.inl 0} (Sum.inr 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inl 0)]
  rw [opPi_dd02_F13]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd20 F31`. -/
lemma opPi_DDF_c2031_mem :
    opPi (fieldStrengthDeriv {Sum.inr 1, Sum.inl 0} (Sum.inr 2) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inl 0)]
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 2) (Sum.inr 0) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) from
            fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 1} _ _]
  rw [map_neg, opPi_dd02_F13, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd03 F03`. -/
lemma opPi_DDF_c0303_mem :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_dd03_F03]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd03 F30`. -/
lemma opPi_DDF_c0330_mem :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 2) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 2) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) from
            fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 2} _ _]
  rw [map_neg, opPi_dd03_F03, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd30 F03`. -/
lemma opPi_DDF_c3003_mem :
    opPi (fieldStrengthDeriv {Sum.inr 2, Sum.inl 0} (Sum.inl 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inl 0)]
  rw [opPi_dd03_F03]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd30 F30`. -/
lemma opPi_DDF_c3030_mem :
    opPi (fieldStrengthDeriv {Sum.inr 2, Sum.inl 0} (Sum.inr 2) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inl 0)]
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 2) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) from
            fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 2} _ _]
  rw [map_neg, opPi_dd03_F03, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd03 F12`. -/
lemma opPi_DDF_c0312_mem :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_dd03_F12]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd03 F21`. -/
lemma opPi_DDF_c0321_mem :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 1) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 1) (Sum.inr 0) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) from
            fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 2} _ _]
  rw [map_neg, opPi_dd03_F12, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd30 F12`. -/
lemma opPi_DDF_c3012_mem :
    opPi (fieldStrengthDeriv {Sum.inr 2, Sum.inl 0} (Sum.inr 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inl 0)]
  rw [opPi_dd03_F12]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd30 F21`. -/
lemma opPi_DDF_c3021_mem :
    opPi (fieldStrengthDeriv {Sum.inr 2, Sum.inl 0} (Sum.inr 1) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inl 0)]
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 1) (Sum.inr 0) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) from
            fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 2} _ _]
  rw [map_neg, opPi_dd03_F12, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd12 F03`. -/
lemma opPi_DDF_c1203_mem :
    opPi (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_dd12_F03]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd12 F30`. -/
lemma opPi_DDF_c1230_mem :
    opPi (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 2) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 2) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) from
            fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 1} _ _]
  rw [map_neg, opPi_dd12_F03, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd21 F03`. -/
lemma opPi_DDF_c2103_mem :
    opPi (fieldStrengthDeriv {Sum.inr 1, Sum.inr 0} (Sum.inl 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inr 0)]
  rw [opPi_dd12_F03]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd21 F30`. -/
lemma opPi_DDF_c2130_mem :
    opPi (fieldStrengthDeriv {Sum.inr 1, Sum.inr 0} (Sum.inr 2) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inr 0)]
  rw [show fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 2) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) from
            fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 1} _ _]
  rw [map_neg, opPi_dd12_F03, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd12 F12`. -/
lemma opPi_DDF_c1212_mem :
    opPi (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_dd12_F12]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd12 F21`. -/
lemma opPi_DDF_c1221_mem :
    opPi (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 1) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 1) (Sum.inr 0) =
        -(fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) from
            fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 1} _ _]
  rw [map_neg, opPi_dd12_F12, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd21 F12`. -/
lemma opPi_DDF_c2112_mem :
    opPi (fieldStrengthDeriv {Sum.inr 1, Sum.inr 0} (Sum.inr 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inr 0)]
  rw [opPi_dd12_F12]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd21 F21`. -/
lemma opPi_DDF_c2121_mem :
    opPi (fieldStrengthDeriv {Sum.inr 1, Sum.inr 0} (Sum.inr 1) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inr 0)]
  rw [show fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 1) (Sum.inr 0) =
        -(fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) from
            fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 1} _ _]
  rw [map_neg, opPi_dd12_F12, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd13 F02`. -/
lemma opPi_DDF_c1302_mem :
    opPi (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_dd13_F02]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd13 F20`. -/
lemma opPi_DDF_c1320_mem :
    opPi (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 1) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 1) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) from
            fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 2} _ _]
  rw [map_neg, opPi_dd13_F02, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd31 F02`. -/
lemma opPi_DDF_c3102_mem :
    opPi (fieldStrengthDeriv {Sum.inr 2, Sum.inr 0} (Sum.inl 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inr 0)]
  rw [opPi_dd13_F02]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd31 F20`. -/
lemma opPi_DDF_c3120_mem :
    opPi (fieldStrengthDeriv {Sum.inr 2, Sum.inr 0} (Sum.inr 1) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inr 0)]
  rw [show fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 1) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) from
            fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 2} _ _]
  rw [map_neg, opPi_dd13_F02, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd13 F13`. -/
lemma opPi_DDF_c1313_mem :
    opPi (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_dd13_F13]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd13 F31`. -/
lemma opPi_DDF_c1331_mem :
    opPi (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 2) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 2) (Sum.inr 0) =
        -(fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) from
            fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 2} _ _]
  rw [map_neg, opPi_dd13_F13, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd31 F13`. -/
lemma opPi_DDF_c3113_mem :
    opPi (fieldStrengthDeriv {Sum.inr 2, Sum.inr 0} (Sum.inr 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inr 0)]
  rw [opPi_dd13_F13]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd31 F31`. -/
lemma opPi_DDF_c3131_mem :
    opPi (fieldStrengthDeriv {Sum.inr 2, Sum.inr 0} (Sum.inr 2) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inr 0)]
  rw [show fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 2) (Sum.inr 0) =
        -(fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) from
            fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 2} _ _]
  rw [map_neg, opPi_dd13_F13, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd23 F01`. -/
lemma opPi_DDF_c2301_mem :
    opPi (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_dd23_F01]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd23 F10`. -/
lemma opPi_DDF_c2310_mem :
    opPi (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 0) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 0) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) from
            fieldStrengthDeriv_antisymm {Sum.inr 1, Sum.inr 2} _ _]
  rw [map_neg, opPi_dd23_F01, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd32 F01`. -/
lemma opPi_DDF_c3201_mem :
    opPi (fieldStrengthDeriv {Sum.inr 2, Sum.inr 1} (Sum.inl 0) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inr 1)]
  rw [opPi_dd23_F01]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd32 F10`. -/
lemma opPi_DDF_c3210_mem :
    opPi (fieldStrengthDeriv {Sum.inr 2, Sum.inr 1} (Sum.inr 0) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inr 1)]
  rw [show fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 0) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) from
            fieldStrengthDeriv_antisymm {Sum.inr 1, Sum.inr 2} _ _]
  rw [map_neg, opPi_dd23_F01, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd23 F23`. -/
lemma opPi_DDF_c2323_mem :
    opPi (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_dd23_F23]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd23 F32`. -/
lemma opPi_DDF_c2332_mem :
    opPi (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 2) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 2) (Sum.inr 1) =
        -(fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) from
            fieldStrengthDeriv_antisymm {Sum.inr 1, Sum.inr 2} _ _]
  rw [map_neg, opPi_dd23_F23, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd32 F23`. -/
lemma opPi_DDF_c3223_mem :
    opPi (fieldStrengthDeriv {Sum.inr 2, Sum.inr 1} (Sum.inr 1) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inr 1)]
  rw [opPi_dd23_F23]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd32 F32`. -/
lemma opPi_DDF_c3232_mem :
    opPi (fieldStrengthDeriv {Sum.inr 2, Sum.inr 1} (Sum.inr 2) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inr 1)]
  rw [show fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 2) (Sum.inr 1) =
        -(fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) from
            fieldStrengthDeriv_antisymm {Sum.inr 1, Sum.inr 2} _ _]
  rw [map_neg, opPi_dd23_F23, neg_zero]
  exact Submodule.zero_mem _

/-- Projected Klein average of `e[0,0,0]` (u-family) lies in the span. -/
lemma opPi_kA_u000_mem :
    opPi (kleinAvg (Dbarψ [] 0 * Dψ [Sum.inl 0] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_u_e000, map_smul, opPi_u0]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTerm_mem_span)

/-- Projected Klein average of `e[0,0,1]` (u-family) lies in the span. -/
lemma opPi_kA_u001_mem :
    opPi (kleinAvg (Dbarψ [] 0 * Dψ [Sum.inl 0] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_u_e001, map_zero]
  exact Submodule.zero_mem _

/-- Projected Klein average of `e[0,1,0]` (u-family) lies in the span. -/
lemma opPi_kA_u010_mem :
    opPi (kleinAvg (Dbarψ [] 1 * Dψ [Sum.inl 0] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_u_e010, map_zero]
  exact Submodule.zero_mem _

/-- Projected Klein average of `e[0,1,1]` (u-family) lies in the span. -/
lemma opPi_kA_u011_mem :
    opPi (kleinAvg (Dbarψ [] 1 * Dψ [Sum.inl 0] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_u_e011, map_smul, opPi_u0]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTerm_mem_span)

/-- Projected Klein average of `e[1,0,0]` (u-family) lies in the span. -/
lemma opPi_kA_u100_mem :
    opPi (kleinAvg (Dbarψ [] 0 * Dψ [Sum.inr 0] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_u_e100, map_zero]
  exact Submodule.zero_mem _

/-- Projected Klein average of `e[1,0,1]` (u-family) lies in the span. -/
lemma opPi_kA_u101_mem :
    opPi (kleinAvg (Dbarψ [] 0 * Dψ [Sum.inr 0] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_u_e101, map_smul, opPi_u1]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTerm_mem_span)

/-- Projected Klein average of `e[1,1,0]` (u-family) lies in the span. -/
lemma opPi_kA_u110_mem :
    opPi (kleinAvg (Dbarψ [] 1 * Dψ [Sum.inr 0] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_u_e110, map_smul, opPi_u1]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTerm_mem_span)

/-- Projected Klein average of `e[1,1,1]` (u-family) lies in the span. -/
lemma opPi_kA_u111_mem :
    opPi (kleinAvg (Dbarψ [] 1 * Dψ [Sum.inr 0] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_u_e111, map_zero]
  exact Submodule.zero_mem _

/-- Projected Klein average of `e[2,0,0]` (u-family) lies in the span. -/
lemma opPi_kA_u200_mem :
    opPi (kleinAvg (Dbarψ [] 0 * Dψ [Sum.inr 1] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_u_e200, map_zero]
  exact Submodule.zero_mem _

/-- Projected Klein average of `e[2,0,1]` (u-family) lies in the span. -/
lemma opPi_kA_u201_mem :
    opPi (kleinAvg (Dbarψ [] 0 * Dψ [Sum.inr 1] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_u_e201, map_smul, opPi_u2]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTerm_mem_span)

/-- Projected Klein average of `e[2,1,0]` (u-family) lies in the span. -/
lemma opPi_kA_u210_mem :
    opPi (kleinAvg (Dbarψ [] 1 * Dψ [Sum.inr 1] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_u_e210, map_smul, opPi_u2]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTerm_mem_span)

/-- Projected Klein average of `e[2,1,1]` (u-family) lies in the span. -/
lemma opPi_kA_u211_mem :
    opPi (kleinAvg (Dbarψ [] 1 * Dψ [Sum.inr 1] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_u_e211, map_zero]
  exact Submodule.zero_mem _

/-- Projected Klein average of `e[3,0,0]` (u-family) lies in the span. -/
lemma opPi_kA_u300_mem :
    opPi (kleinAvg (Dbarψ [] 0 * Dψ [Sum.inr 2] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_u_e300, map_smul, opPi_u3]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTerm_mem_span)

/-- Projected Klein average of `e[3,0,1]` (u-family) lies in the span. -/
lemma opPi_kA_u301_mem :
    opPi (kleinAvg (Dbarψ [] 0 * Dψ [Sum.inr 2] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_u_e301, map_zero]
  exact Submodule.zero_mem _

/-- Projected Klein average of `e[3,1,0]` (u-family) lies in the span. -/
lemma opPi_kA_u310_mem :
    opPi (kleinAvg (Dbarψ [] 1 * Dψ [Sum.inr 2] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_u_e310, map_zero]
  exact Submodule.zero_mem _

/-- Projected Klein average of `e[3,1,1]` (u-family) lies in the span. -/
lemma opPi_kA_u311_mem :
    opPi (kleinAvg (Dbarψ [] 1 * Dψ [Sum.inr 2] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_u_e311, map_smul, opPi_u3]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTerm_mem_span)

/-- Projected Klein average of `e[0,0,0]` (ubar-family) lies in the span. -/
lemma opPi_kA_ubar000_mem :
    opPi (kleinAvg (Dbarψ [Sum.inl 0] 0 * Dψ [] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_ubar_e000, map_smul, opPi_ubar0]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTermBar_mem_span)

/-- Projected Klein average of `e[0,0,1]` (ubar-family) lies in the span. -/
lemma opPi_kA_ubar001_mem :
    opPi (kleinAvg (Dbarψ [Sum.inl 0] 0 * Dψ [] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_ubar_e001, map_zero]
  exact Submodule.zero_mem _

/-- Projected Klein average of `e[0,1,0]` (ubar-family) lies in the span. -/
lemma opPi_kA_ubar010_mem :
    opPi (kleinAvg (Dbarψ [Sum.inl 0] 1 * Dψ [] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_ubar_e010, map_zero]
  exact Submodule.zero_mem _

/-- Projected Klein average of `e[0,1,1]` (ubar-family) lies in the span. -/
lemma opPi_kA_ubar011_mem :
    opPi (kleinAvg (Dbarψ [Sum.inl 0] 1 * Dψ [] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_ubar_e011, map_smul, opPi_ubar0]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTermBar_mem_span)

/-- Projected Klein average of `e[1,0,0]` (ubar-family) lies in the span. -/
lemma opPi_kA_ubar100_mem :
    opPi (kleinAvg (Dbarψ [Sum.inr 0] 0 * Dψ [] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_ubar_e100, map_zero]
  exact Submodule.zero_mem _

/-- Projected Klein average of `e[1,0,1]` (ubar-family) lies in the span. -/
lemma opPi_kA_ubar101_mem :
    opPi (kleinAvg (Dbarψ [Sum.inr 0] 0 * Dψ [] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_ubar_e101, map_smul, opPi_ubar1]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTermBar_mem_span)

/-- Projected Klein average of `e[1,1,0]` (ubar-family) lies in the span. -/
lemma opPi_kA_ubar110_mem :
    opPi (kleinAvg (Dbarψ [Sum.inr 0] 1 * Dψ [] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_ubar_e110, map_smul, opPi_ubar1]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTermBar_mem_span)

/-- Projected Klein average of `e[1,1,1]` (ubar-family) lies in the span. -/
lemma opPi_kA_ubar111_mem :
    opPi (kleinAvg (Dbarψ [Sum.inr 0] 1 * Dψ [] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_ubar_e111, map_zero]
  exact Submodule.zero_mem _

/-- Projected Klein average of `e[2,0,0]` (ubar-family) lies in the span. -/
lemma opPi_kA_ubar200_mem :
    opPi (kleinAvg (Dbarψ [Sum.inr 1] 0 * Dψ [] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_ubar_e200, map_zero]
  exact Submodule.zero_mem _

/-- Projected Klein average of `e[2,0,1]` (ubar-family) lies in the span. -/
lemma opPi_kA_ubar201_mem :
    opPi (kleinAvg (Dbarψ [Sum.inr 1] 0 * Dψ [] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_ubar_e201, map_smul, opPi_ubar2]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTermBar_mem_span)

/-- Projected Klein average of `e[2,1,0]` (ubar-family) lies in the span. -/
lemma opPi_kA_ubar210_mem :
    opPi (kleinAvg (Dbarψ [Sum.inr 1] 1 * Dψ [] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_ubar_e210, map_smul, opPi_ubar2]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTermBar_mem_span)

/-- Projected Klein average of `e[2,1,1]` (ubar-family) lies in the span. -/
lemma opPi_kA_ubar211_mem :
    opPi (kleinAvg (Dbarψ [Sum.inr 1] 1 * Dψ [] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_ubar_e211, map_zero]
  exact Submodule.zero_mem _

/-- Projected Klein average of `e[3,0,0]` (ubar-family) lies in the span. -/
lemma opPi_kA_ubar300_mem :
    opPi (kleinAvg (Dbarψ [Sum.inr 2] 0 * Dψ [] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_ubar_e300, map_smul, opPi_ubar3]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTermBar_mem_span)

/-- Projected Klein average of `e[3,0,1]` (ubar-family) lies in the span. -/
lemma opPi_kA_ubar301_mem :
    opPi (kleinAvg (Dbarψ [Sum.inr 2] 0 * Dψ [] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_ubar_e301, map_zero]
  exact Submodule.zero_mem _

/-- Projected Klein average of `e[3,1,0]` (ubar-family) lies in the span. -/
lemma opPi_kA_ubar310_mem :
    opPi (kleinAvg (Dbarψ [Sum.inr 2] 1 * Dψ [] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_ubar_e310, map_zero]
  exact Submodule.zero_mem _

/-- Projected Klein average of `e[3,1,1]` (ubar-family) lies in the span. -/
lemma opPi_kA_ubar311_mem :
    opPi (kleinAvg (Dbarψ [Sum.inr 2] 1 * Dψ [] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_ubar_e311, map_smul, opPi_ubar3]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTermBar_mem_span)

attribute [local irreducible] Dψ Dbarψ fieldStrengthDeriv

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 8192 in
/-- The projected Klein average of any product of two field strengths lies in
  the span of the invariants. -/
lemma opPi_kleinAvg_FF_mem (a b c d : Fin 1 ⊕ Fin 3) :
    opPi (kleinAvg (fieldStrengthDeriv {} a b * fieldStrengthDeriv {} c d)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_fieldStrengthDeriv_nil_mul, map_smul]
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
       | exact opPi_FF_c0101_mem
       | exact opPi_FF_c0110_mem
       | exact opPi_FF_c1001_mem
       | exact opPi_FF_c1010_mem
       | exact opPi_FF_c0123_mem
       | exact opPi_FF_c0132_mem
       | exact opPi_FF_c1023_mem
       | exact opPi_FF_c1032_mem
       | exact opPi_FF_c2301_mem
       | exact opPi_FF_c2310_mem
       | exact opPi_FF_c3201_mem
       | exact opPi_FF_c3210_mem
       | exact opPi_FF_c2323_mem
       | exact opPi_FF_c2332_mem
       | exact opPi_FF_c3223_mem
       | exact opPi_FF_c3232_mem
       | exact opPi_FF_c0202_mem
       | exact opPi_FF_c0220_mem
       | exact opPi_FF_c2002_mem
       | exact opPi_FF_c2020_mem
       | exact opPi_FF_c0213_mem
       | exact opPi_FF_c0231_mem
       | exact opPi_FF_c2013_mem
       | exact opPi_FF_c2031_mem
       | exact opPi_FF_c1302_mem
       | exact opPi_FF_c1320_mem
       | exact opPi_FF_c3102_mem
       | exact opPi_FF_c3120_mem
       | exact opPi_FF_c1313_mem
       | exact opPi_FF_c1331_mem
       | exact opPi_FF_c3113_mem
       | exact opPi_FF_c3131_mem
       | exact opPi_FF_c0303_mem
       | exact opPi_FF_c0330_mem
       | exact opPi_FF_c3003_mem
       | exact opPi_FF_c3030_mem
       | exact opPi_FF_c0312_mem
       | exact opPi_FF_c0321_mem
       | exact opPi_FF_c3012_mem
       | exact opPi_FF_c3021_mem
       | exact opPi_FF_c1203_mem
       | exact opPi_FF_c1230_mem
       | exact opPi_FF_c2103_mem
       | exact opPi_FF_c2130_mem
       | exact opPi_FF_c1212_mem
       | exact opPi_FF_c1221_mem
       | exact opPi_FF_c2112_mem
       | exact opPi_FF_c2121_mem)
    | (norm_num [paritySignZ, paritySignY, paritySignX]
       first
       | done
       | exact Submodule.zero_mem _)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 8192 in
/-- The projected Klein average of any second-derivative field strength lies
  in the span of the invariants. -/
lemma opPi_kleinAvg_DDF_mem (r t a b : Fin 1 ⊕ Fin 3) :
    opPi (kleinAvg (fieldStrengthDeriv {r, t} a b)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_fieldStrengthDeriv_pair, map_smul]
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
       | exact opPi_DDF_c0101_mem
       | exact opPi_DDF_c0110_mem
       | exact opPi_DDF_c1001_mem
       | exact opPi_DDF_c1010_mem
       | exact opPi_DDF_c0123_mem
       | exact opPi_DDF_c0132_mem
       | exact opPi_DDF_c1023_mem
       | exact opPi_DDF_c1032_mem
       | exact opPi_DDF_c0202_mem
       | exact opPi_DDF_c0220_mem
       | exact opPi_DDF_c2002_mem
       | exact opPi_DDF_c2020_mem
       | exact opPi_DDF_c0213_mem
       | exact opPi_DDF_c0231_mem
       | exact opPi_DDF_c2013_mem
       | exact opPi_DDF_c2031_mem
       | exact opPi_DDF_c0303_mem
       | exact opPi_DDF_c0330_mem
       | exact opPi_DDF_c3003_mem
       | exact opPi_DDF_c3030_mem
       | exact opPi_DDF_c0312_mem
       | exact opPi_DDF_c0321_mem
       | exact opPi_DDF_c3012_mem
       | exact opPi_DDF_c3021_mem
       | exact opPi_DDF_c1203_mem
       | exact opPi_DDF_c1230_mem
       | exact opPi_DDF_c2103_mem
       | exact opPi_DDF_c2130_mem
       | exact opPi_DDF_c1212_mem
       | exact opPi_DDF_c1221_mem
       | exact opPi_DDF_c2112_mem
       | exact opPi_DDF_c2121_mem
       | exact opPi_DDF_c1302_mem
       | exact opPi_DDF_c1320_mem
       | exact opPi_DDF_c3102_mem
       | exact opPi_DDF_c3120_mem
       | exact opPi_DDF_c1313_mem
       | exact opPi_DDF_c1331_mem
       | exact opPi_DDF_c3113_mem
       | exact opPi_DDF_c3131_mem
       | exact opPi_DDF_c2301_mem
       | exact opPi_DDF_c2310_mem
       | exact opPi_DDF_c3201_mem
       | exact opPi_DDF_c3210_mem
       | exact opPi_DDF_c2323_mem
       | exact opPi_DDF_c2332_mem
       | exact opPi_DDF_c3223_mem
       | exact opPi_DDF_c3232_mem)
    | (norm_num [paritySignZ, paritySignY, paritySignX]
       first
       | done
       | exact Submodule.zero_mem _)

set_option maxRecDepth 8192 in
/-- The projected Klein average of any `ψ̄ (Dψ)` pair lies in the span. -/
lemma opPi_kleinAvg_FM1_mem (μ : Fin 1 ⊕ Fin 3) (α β : Fin 2) :
    opPi (kleinAvg (Dbarψ [] α * Dψ [μ] β)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rcases μ with m | m <;> fin_cases m <;> fin_cases α <;> fin_cases β <;>
    (try simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]) <;>
    first
    | exact opPi_kA_u000_mem
    | exact opPi_kA_u001_mem
    | exact opPi_kA_u010_mem
    | exact opPi_kA_u011_mem
    | exact opPi_kA_u100_mem
    | exact opPi_kA_u101_mem
    | exact opPi_kA_u110_mem
    | exact opPi_kA_u111_mem
    | exact opPi_kA_u200_mem
    | exact opPi_kA_u201_mem
    | exact opPi_kA_u210_mem
    | exact opPi_kA_u211_mem
    | exact opPi_kA_u300_mem
    | exact opPi_kA_u301_mem
    | exact opPi_kA_u310_mem
    | exact opPi_kA_u311_mem

set_option maxRecDepth 8192 in
/-- The projected Klein average of any `(D̄ψ̄) ψ` pair lies in the span. -/
lemma opPi_kleinAvg_FM2_mem (μ : Fin 1 ⊕ Fin 3) (α β : Fin 2) :
    opPi (kleinAvg (Dbarψ [μ] α * Dψ [] β)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rcases μ with m | m <;> fin_cases m <;> fin_cases α <;> fin_cases β <;>
    (try simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]) <;>
    first
    | exact opPi_kA_ubar000_mem
    | exact opPi_kA_ubar001_mem
    | exact opPi_kA_ubar010_mem
    | exact opPi_kA_ubar011_mem
    | exact opPi_kA_ubar100_mem
    | exact opPi_kA_ubar101_mem
    | exact opPi_kA_ubar110_mem
    | exact opPi_kA_ubar111_mem
    | exact opPi_kA_ubar200_mem
    | exact opPi_kA_ubar201_mem
    | exact opPi_kA_ubar210_mem
    | exact opPi_kA_ubar211_mem
    | exact opPi_kA_ubar300_mem
    | exact opPi_kA_ubar301_mem
    | exact opPi_kA_ubar310_mem
    | exact opPi_kA_ubar311_mem

/-- The reversed pair `(Dψ) ψ̄`, via anticommutation. -/
lemma opPi_kleinAvg_FM1r_mem (μ : Fin 1 ⊕ Fin 3) (α β : Fin 2) :
    opPi (kleinAvg (Dψ [μ] β * Dbarψ [] α)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [Dψ_mul_Dbarψ_anticomm, map_neg, map_neg]
  exact neg_mem (opPi_kleinAvg_FM1_mem μ α β)

/-- The reversed pair `ψ (D̄ψ̄)`, via anticommutation. -/
lemma opPi_kleinAvg_FM2r_mem (μ : Fin 1 ⊕ Fin 3) (α β : Fin 2) :
    opPi (kleinAvg (Dψ [] α * Dbarψ [μ] β)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [Dψ_mul_Dbarψ_anticomm, map_neg, map_neg]
  exact neg_mem (opPi_kleinAvg_FM2_mem μ β α)
end JetAlgebra

end QED
