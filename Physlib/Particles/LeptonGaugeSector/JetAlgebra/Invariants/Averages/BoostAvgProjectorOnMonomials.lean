/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.Invariants.Averages.BoostAvgProjectorOnDerivativesAndFermions
/-!
# The Lorentz-scalar projector on the weight-eight monomials

The values of `boostAvgScalarProj` on the weight-eight monomials, the entries of the Lorentz
matrices of the rotations by `π`, and the values of the rotation average
`rotationPiAvg` on the weight-eight monomials.
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

set_option maxHeartbeats 2000000 in
/-- The projector `boostAvgScalarProj` on the field-strength square `F01_F01`. -/
lemma boostAvgScalarProj_F01_F01 :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) =
      (-(1/12) : ℂ) • maxwellTerm := by
  rw [boostAvgScalarProj_apply,
    scalarProjFF0 boostAvg boostAvg_F01_F01 boostAvg_F01_F23 boostAvg_F02_F02 boostAvg_F02_F13 boostAvg_F03_F03 boostAvg_F03_F12 boostAvg_F12_F12
        boostAvg_F13_F13 boostAvg_F23_F23,
    ← maxwellTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `boostAvgScalarProj` on the field-strength square `F01_F23`. -/
lemma boostAvgScalarProj_F01_F23 :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) =
      (1/24 : ℂ) • thetaTerm := by
  rw [boostAvgScalarProj_apply,
    scalarProjFF1 boostAvg boostAvg_F01_F01 boostAvg_F01_F23 boostAvg_F02_F02 boostAvg_F02_F13 boostAvg_F03_F03 boostAvg_F03_F12 boostAvg_F12_F12
        boostAvg_F13_F13 boostAvg_F23_F23,
    ← thetaTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `boostAvgScalarProj` on the field-strength square `F02_F02`. -/
lemma boostAvgScalarProj_F02_F02 :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) =
      (-(1/12) : ℂ) • maxwellTerm := by
  rw [boostAvgScalarProj_apply,
    scalarProjFF2 boostAvg boostAvg_F01_F01 boostAvg_F01_F23 boostAvg_F02_F02 boostAvg_F02_F13 boostAvg_F03_F03 boostAvg_F03_F12 boostAvg_F12_F12
        boostAvg_F13_F13 boostAvg_F23_F23,
    ← maxwellTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `boostAvgScalarProj` on the field-strength square `F02_F13`. -/
lemma boostAvgScalarProj_F02_F13 :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) =
      (-(1/24) : ℂ) • thetaTerm := by
  rw [boostAvgScalarProj_apply,
    scalarProjFF3 boostAvg boostAvg_F01_F01 boostAvg_F01_F23 boostAvg_F02_F02 boostAvg_F02_F13 boostAvg_F03_F03 boostAvg_F03_F12 boostAvg_F12_F12
        boostAvg_F13_F13 boostAvg_F23_F23,
    ← thetaTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `boostAvgScalarProj` on the field-strength square `F03_F03`. -/
lemma boostAvgScalarProj_F03_F03 :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) =
      (-(1/12) : ℂ) • maxwellTerm := by
  rw [boostAvgScalarProj_apply,
    scalarProjFF4 boostAvg boostAvg_F01_F01 boostAvg_F01_F23 boostAvg_F02_F02 boostAvg_F02_F13 boostAvg_F03_F03 boostAvg_F03_F12 boostAvg_F12_F12
        boostAvg_F13_F13 boostAvg_F23_F23,
    ← maxwellTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `boostAvgScalarProj` on the field-strength square `F03_F12`. -/
lemma boostAvgScalarProj_F03_F12 :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) =
      (1/24 : ℂ) • thetaTerm := by
  rw [boostAvgScalarProj_apply,
    scalarProjFF5 boostAvg boostAvg_F01_F01 boostAvg_F01_F23 boostAvg_F02_F02 boostAvg_F02_F13 boostAvg_F03_F03 boostAvg_F03_F12 boostAvg_F12_F12
        boostAvg_F13_F13 boostAvg_F23_F23,
    ← thetaTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `boostAvgScalarProj` on the field-strength square `F12_F12`. -/
lemma boostAvgScalarProj_F12_F12 :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) =
      (1/12 : ℂ) • maxwellTerm := by
  rw [boostAvgScalarProj_apply,
    scalarProjFF6 boostAvg boostAvg_F01_F01 boostAvg_F01_F23 boostAvg_F02_F02 boostAvg_F02_F13 boostAvg_F03_F03 boostAvg_F03_F12 boostAvg_F12_F12
        boostAvg_F13_F13 boostAvg_F23_F23,
    ← maxwellTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `boostAvgScalarProj` on the field-strength square `F13_F13`. -/
lemma boostAvgScalarProj_F13_F13 :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) =
      (1/12 : ℂ) • maxwellTerm := by
  rw [boostAvgScalarProj_apply,
    scalarProjFF7 boostAvg boostAvg_F01_F01 boostAvg_F01_F23 boostAvg_F02_F02 boostAvg_F02_F13 boostAvg_F03_F03 boostAvg_F03_F12 boostAvg_F12_F12
        boostAvg_F13_F13 boostAvg_F23_F23,
    ← maxwellTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `boostAvgScalarProj` on the field-strength square `F23_F23`. -/
lemma boostAvgScalarProj_F23_F23 :
    boostAvgScalarProj (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) =
      (1/12 : ℂ) • maxwellTerm := by
  rw [boostAvgScalarProj_apply,
    scalarProjFF8 boostAvg boostAvg_F01_F01 boostAvg_F01_F23 boostAvg_F02_F02 boostAvg_F02_F13 boostAvg_F03_F03 boostAvg_F03_F12 boostAvg_F12_F12
        boostAvg_F13_F13 boostAvg_F23_F23,
    ← maxwellTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `boostAvgScalarProj` annihilates the derivative monomial `dd01_F01`. -/
lemma boostAvgScalarProj_dd01_F01 :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) =
      (0 : JetAlgebra) := by
  rw [boostAvgScalarProj_apply,
    scalarProjDDF0 boostAvg boostAvg_dd01_F01 boostAvg_dd01_F23 boostAvg_dd02_F02 boostAvg_dd02_F13 boostAvg_dd03_F03 boostAvg_dd03_F12
        boostAvg_dd12_F03 boostAvg_dd12_F12 boostAvg_dd13_F02 boostAvg_dd13_F13 boostAvg_dd23_F01 boostAvg_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `boostAvgScalarProj` annihilates the derivative monomial `dd01_F23`. -/
lemma boostAvgScalarProj_dd01_F23 :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) =
      (0 : JetAlgebra) := by
  rw [boostAvgScalarProj_apply,
    scalarProjDDF1 boostAvg boostAvg_dd01_F01 boostAvg_dd01_F23 boostAvg_dd02_F02 boostAvg_dd02_F13 boostAvg_dd03_F03 boostAvg_dd03_F12
        boostAvg_dd12_F03 boostAvg_dd12_F12 boostAvg_dd13_F02 boostAvg_dd13_F13 boostAvg_dd23_F01 boostAvg_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `boostAvgScalarProj` annihilates the derivative monomial `dd02_F02`. -/
lemma boostAvgScalarProj_dd02_F02 :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) =
      (0 : JetAlgebra) := by
  rw [boostAvgScalarProj_apply,
    scalarProjDDF2 boostAvg boostAvg_dd01_F01 boostAvg_dd01_F23 boostAvg_dd02_F02 boostAvg_dd02_F13 boostAvg_dd03_F03 boostAvg_dd03_F12
        boostAvg_dd12_F03 boostAvg_dd12_F12 boostAvg_dd13_F02 boostAvg_dd13_F13 boostAvg_dd23_F01 boostAvg_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `boostAvgScalarProj` annihilates the derivative monomial `dd02_F13`. -/
lemma boostAvgScalarProj_dd02_F13 :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) =
      (0 : JetAlgebra) := by
  rw [boostAvgScalarProj_apply,
    scalarProjDDF3 boostAvg boostAvg_dd01_F01 boostAvg_dd01_F23 boostAvg_dd02_F02 boostAvg_dd02_F13 boostAvg_dd03_F03 boostAvg_dd03_F12
        boostAvg_dd12_F03 boostAvg_dd12_F12 boostAvg_dd13_F02 boostAvg_dd13_F13 boostAvg_dd23_F01 boostAvg_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `boostAvgScalarProj` annihilates the derivative monomial `dd03_F03`. -/
lemma boostAvgScalarProj_dd03_F03 :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) =
      (0 : JetAlgebra) := by
  rw [boostAvgScalarProj_apply,
    scalarProjDDF4 boostAvg boostAvg_dd01_F01 boostAvg_dd01_F23 boostAvg_dd02_F02 boostAvg_dd02_F13 boostAvg_dd03_F03 boostAvg_dd03_F12
        boostAvg_dd12_F03 boostAvg_dd12_F12 boostAvg_dd13_F02 boostAvg_dd13_F13 boostAvg_dd23_F01 boostAvg_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `boostAvgScalarProj` annihilates the derivative monomial `dd03_F12`. -/
lemma boostAvgScalarProj_dd03_F12 :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) =
      (0 : JetAlgebra) := by
  rw [boostAvgScalarProj_apply,
    scalarProjDDF5 boostAvg boostAvg_dd01_F01 boostAvg_dd01_F23 boostAvg_dd02_F02 boostAvg_dd02_F13 boostAvg_dd03_F03 boostAvg_dd03_F12
        boostAvg_dd12_F03 boostAvg_dd12_F12 boostAvg_dd13_F02 boostAvg_dd13_F13 boostAvg_dd23_F01 boostAvg_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `boostAvgScalarProj` annihilates the derivative monomial `dd12_F03`. -/
lemma boostAvgScalarProj_dd12_F03 :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) =
      (0 : JetAlgebra) := by
  rw [boostAvgScalarProj_apply,
    scalarProjDDF6 boostAvg boostAvg_dd01_F01 boostAvg_dd01_F23 boostAvg_dd02_F02 boostAvg_dd02_F13 boostAvg_dd03_F03 boostAvg_dd03_F12
        boostAvg_dd12_F03 boostAvg_dd12_F12 boostAvg_dd13_F02 boostAvg_dd13_F13 boostAvg_dd23_F01 boostAvg_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `boostAvgScalarProj` annihilates the derivative monomial `dd12_F12`. -/
lemma boostAvgScalarProj_dd12_F12 :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) =
      (0 : JetAlgebra) := by
  rw [boostAvgScalarProj_apply,
    scalarProjDDF7 boostAvg boostAvg_dd01_F01 boostAvg_dd01_F23 boostAvg_dd02_F02 boostAvg_dd02_F13 boostAvg_dd03_F03 boostAvg_dd03_F12
        boostAvg_dd12_F03 boostAvg_dd12_F12 boostAvg_dd13_F02 boostAvg_dd13_F13 boostAvg_dd23_F01 boostAvg_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `boostAvgScalarProj` annihilates the derivative monomial `dd13_F02`. -/
lemma boostAvgScalarProj_dd13_F02 :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) =
      (0 : JetAlgebra) := by
  rw [boostAvgScalarProj_apply,
    scalarProjDDF8 boostAvg boostAvg_dd01_F01 boostAvg_dd01_F23 boostAvg_dd02_F02 boostAvg_dd02_F13 boostAvg_dd03_F03 boostAvg_dd03_F12
        boostAvg_dd12_F03 boostAvg_dd12_F12 boostAvg_dd13_F02 boostAvg_dd13_F13 boostAvg_dd23_F01 boostAvg_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `boostAvgScalarProj` annihilates the derivative monomial `dd13_F13`. -/
lemma boostAvgScalarProj_dd13_F13 :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) =
      (0 : JetAlgebra) := by
  rw [boostAvgScalarProj_apply,
    scalarProjDDF9 boostAvg boostAvg_dd01_F01 boostAvg_dd01_F23 boostAvg_dd02_F02 boostAvg_dd02_F13 boostAvg_dd03_F03 boostAvg_dd03_F12
        boostAvg_dd12_F03 boostAvg_dd12_F12 boostAvg_dd13_F02 boostAvg_dd13_F13 boostAvg_dd23_F01 boostAvg_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `boostAvgScalarProj` annihilates the derivative monomial `dd23_F01`. -/
lemma boostAvgScalarProj_dd23_F01 :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) =
      (0 : JetAlgebra) := by
  rw [boostAvgScalarProj_apply,
    scalarProjDDF10 boostAvg boostAvg_dd01_F01 boostAvg_dd01_F23 boostAvg_dd02_F02 boostAvg_dd02_F13 boostAvg_dd03_F03 boostAvg_dd03_F12
        boostAvg_dd12_F03 boostAvg_dd12_F12 boostAvg_dd13_F02 boostAvg_dd13_F13 boostAvg_dd23_F01 boostAvg_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `boostAvgScalarProj` annihilates the derivative monomial `dd23_F23`. -/
lemma boostAvgScalarProj_dd23_F23 :
    boostAvgScalarProj (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) =
      (0 : JetAlgebra) := by
  rw [boostAvgScalarProj_apply,
    scalarProjDDF11 boostAvg boostAvg_dd01_F01 boostAvg_dd01_F23 boostAvg_dd02_F02 boostAvg_dd02_F13 boostAvg_dd03_F03 boostAvg_dd03_F12
        boostAvg_dd12_F03 boostAvg_dd12_F12 boostAvg_dd13_F02 boostAvg_dd13_F13 boostAvg_dd23_F01 boostAvg_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `boostAvgScalarProj` on the σ-contracted fermion pair `u0`. -/
lemma boostAvgScalarProj_u0 :
    boostAvgScalarProj (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) =
      (-(Complex.I/4)) • fermionKineticTerm := by
  rw [boostAvgScalarProj_apply,
    scalarProjFMu0 boostAvg boostAvg_u0 boostAvg_u1 boostAvg_u2 boostAvg_u3,
    ← fermionKineticTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `boostAvgScalarProj` on the σ-contracted fermion pair `u1`. -/
lemma boostAvgScalarProj_u1 :
    boostAvgScalarProj (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0) =
      (Complex.I/4) • fermionKineticTerm := by
  rw [boostAvgScalarProj_apply,
    scalarProjFMu1 boostAvg boostAvg_u0 boostAvg_u1 boostAvg_u2 boostAvg_u3,
    ← fermionKineticTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `boostAvgScalarProj` on the σ-contracted fermion pair `u2`. -/
lemma boostAvgScalarProj_u2 :
    boostAvgScalarProj (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0) =
      (1/4 : ℂ) • fermionKineticTerm := by
  rw [boostAvgScalarProj_apply,
    scalarProjFMu2 boostAvg boostAvg_u0 boostAvg_u1 boostAvg_u2 boostAvg_u3,
    ← fermionKineticTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `boostAvgScalarProj` on the σ-contracted fermion pair `u3`. -/
lemma boostAvgScalarProj_u3 :
    boostAvgScalarProj (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) =
      (Complex.I/4) • fermionKineticTerm := by
  rw [boostAvgScalarProj_apply,
    scalarProjFMu3 boostAvg boostAvg_u0 boostAvg_u1 boostAvg_u2 boostAvg_u3,
    ← fermionKineticTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `boostAvgScalarProj` on the σ-contracted fermion pair `ubar0`. -/
lemma boostAvgScalarProj_ubar0 :
    boostAvgScalarProj (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) =
      (Complex.I/4) • fermionKineticTermBar := by
  rw [boostAvgScalarProj_apply,
    scalarProjFMubar0 boostAvg boostAvg_ubar0 boostAvg_ubar1 boostAvg_ubar2 boostAvg_ubar3,
    ← fermionKineticTermBar_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `boostAvgScalarProj` on the σ-contracted fermion pair `ubar1`. -/
lemma boostAvgScalarProj_ubar1 :
    boostAvgScalarProj (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0) =
      (-(Complex.I/4)) • fermionKineticTermBar := by
  rw [boostAvgScalarProj_apply,
    scalarProjFMubar1 boostAvg boostAvg_ubar0 boostAvg_ubar1 boostAvg_ubar2 boostAvg_ubar3,
    ← fermionKineticTermBar_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `boostAvgScalarProj` on the σ-contracted fermion pair `ubar2`. -/
lemma boostAvgScalarProj_ubar2 :
    boostAvgScalarProj (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0) =
      (-(1/4) : ℂ) • fermionKineticTermBar := by
  rw [boostAvgScalarProj_apply,
    scalarProjFMubar2 boostAvg boostAvg_ubar0 boostAvg_ubar1 boostAvg_ubar2 boostAvg_ubar3,
    ← fermionKineticTermBar_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `boostAvgScalarProj` on the σ-contracted fermion pair `ubar3`. -/
lemma boostAvgScalarProj_ubar3 :
    boostAvgScalarProj (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) =
      (-(Complex.I/4)) • fermionKineticTermBar := by
  rw [boostAvgScalarProj_apply,
    scalarProjFMubar3 boostAvg boostAvg_ubar0 boostAvg_ubar1 boostAvg_ubar2 boostAvg_ubar3,
    ← fermionKineticTermBar_eq]
end JetAlgebra

end LeptonGaugeSector
