/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.QED.JetAlgebra.Invariants.ProjectorsDerivative
/-!
# Values of the projector and of the Klein average

The values of `opPi` on the weight-eight monomials, the entries of the Lorentz
matrices of the parity rotations, and the values of the Klein average
`kleinAvg` on the weight-eight monomials.
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

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` on the field-strength square `F01_F01`. -/
lemma opPi_F01_F01 :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) =
      (-(1/12) : ℂ) • maxwellTerm := by
  rw [opPi_apply,
    projFF0 opS opS_F01_F01 opS_F01_F23 opS_F02_F02 opS_F02_F13 opS_F03_F03 opS_F03_F12 opS_F12_F12
        opS_F13_F13 opS_F23_F23,
    ← maxwellTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` on the field-strength square `F01_F23`. -/
lemma opPi_F01_F23 :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) =
      (1/24 : ℂ) • thetaTerm := by
  rw [opPi_apply,
    projFF1 opS opS_F01_F01 opS_F01_F23 opS_F02_F02 opS_F02_F13 opS_F03_F03 opS_F03_F12 opS_F12_F12
        opS_F13_F13 opS_F23_F23,
    ← thetaTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` on the field-strength square `F02_F02`. -/
lemma opPi_F02_F02 :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) =
      (-(1/12) : ℂ) • maxwellTerm := by
  rw [opPi_apply,
    projFF2 opS opS_F01_F01 opS_F01_F23 opS_F02_F02 opS_F02_F13 opS_F03_F03 opS_F03_F12 opS_F12_F12
        opS_F13_F13 opS_F23_F23,
    ← maxwellTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` on the field-strength square `F02_F13`. -/
lemma opPi_F02_F13 :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) =
      (-(1/24) : ℂ) • thetaTerm := by
  rw [opPi_apply,
    projFF3 opS opS_F01_F01 opS_F01_F23 opS_F02_F02 opS_F02_F13 opS_F03_F03 opS_F03_F12 opS_F12_F12
        opS_F13_F13 opS_F23_F23,
    ← thetaTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` on the field-strength square `F03_F03`. -/
lemma opPi_F03_F03 :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) =
      (-(1/12) : ℂ) • maxwellTerm := by
  rw [opPi_apply,
    projFF4 opS opS_F01_F01 opS_F01_F23 opS_F02_F02 opS_F02_F13 opS_F03_F03 opS_F03_F12 opS_F12_F12
        opS_F13_F13 opS_F23_F23,
    ← maxwellTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` on the field-strength square `F03_F12`. -/
lemma opPi_F03_F12 :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) =
      (1/24 : ℂ) • thetaTerm := by
  rw [opPi_apply,
    projFF5 opS opS_F01_F01 opS_F01_F23 opS_F02_F02 opS_F02_F13 opS_F03_F03 opS_F03_F12 opS_F12_F12
        opS_F13_F13 opS_F23_F23,
    ← thetaTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` on the field-strength square `F12_F12`. -/
lemma opPi_F12_F12 :
    opPi (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) =
      (1/12 : ℂ) • maxwellTerm := by
  rw [opPi_apply,
    projFF6 opS opS_F01_F01 opS_F01_F23 opS_F02_F02 opS_F02_F13 opS_F03_F03 opS_F03_F12 opS_F12_F12
        opS_F13_F13 opS_F23_F23,
    ← maxwellTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` on the field-strength square `F13_F13`. -/
lemma opPi_F13_F13 :
    opPi (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) =
      (1/12 : ℂ) • maxwellTerm := by
  rw [opPi_apply,
    projFF7 opS opS_F01_F01 opS_F01_F23 opS_F02_F02 opS_F02_F13 opS_F03_F03 opS_F03_F12 opS_F12_F12
        opS_F13_F13 opS_F23_F23,
    ← maxwellTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` on the field-strength square `F23_F23`. -/
lemma opPi_F23_F23 :
    opPi (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) =
      (1/12 : ℂ) • maxwellTerm := by
  rw [opPi_apply,
    projFF8 opS opS_F01_F01 opS_F01_F23 opS_F02_F02 opS_F02_F13 opS_F03_F03 opS_F03_F12 opS_F12_F12
        opS_F13_F13 opS_F23_F23,
    ← maxwellTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` annihilates the derivative monomial `dd01_F01`. -/
lemma opPi_dd01_F01 :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) =
      (0 : JetAlgebra) := by
  rw [opPi_apply,
    projDDF0 opS opS_dd01_F01 opS_dd01_F23 opS_dd02_F02 opS_dd02_F13 opS_dd03_F03 opS_dd03_F12
        opS_dd12_F03 opS_dd12_F12 opS_dd13_F02 opS_dd13_F13 opS_dd23_F01 opS_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` annihilates the derivative monomial `dd01_F23`. -/
lemma opPi_dd01_F23 :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) =
      (0 : JetAlgebra) := by
  rw [opPi_apply,
    projDDF1 opS opS_dd01_F01 opS_dd01_F23 opS_dd02_F02 opS_dd02_F13 opS_dd03_F03 opS_dd03_F12
        opS_dd12_F03 opS_dd12_F12 opS_dd13_F02 opS_dd13_F13 opS_dd23_F01 opS_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` annihilates the derivative monomial `dd02_F02`. -/
lemma opPi_dd02_F02 :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) =
      (0 : JetAlgebra) := by
  rw [opPi_apply,
    projDDF2 opS opS_dd01_F01 opS_dd01_F23 opS_dd02_F02 opS_dd02_F13 opS_dd03_F03 opS_dd03_F12
        opS_dd12_F03 opS_dd12_F12 opS_dd13_F02 opS_dd13_F13 opS_dd23_F01 opS_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` annihilates the derivative monomial `dd02_F13`. -/
lemma opPi_dd02_F13 :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) =
      (0 : JetAlgebra) := by
  rw [opPi_apply,
    projDDF3 opS opS_dd01_F01 opS_dd01_F23 opS_dd02_F02 opS_dd02_F13 opS_dd03_F03 opS_dd03_F12
        opS_dd12_F03 opS_dd12_F12 opS_dd13_F02 opS_dd13_F13 opS_dd23_F01 opS_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` annihilates the derivative monomial `dd03_F03`. -/
lemma opPi_dd03_F03 :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) =
      (0 : JetAlgebra) := by
  rw [opPi_apply,
    projDDF4 opS opS_dd01_F01 opS_dd01_F23 opS_dd02_F02 opS_dd02_F13 opS_dd03_F03 opS_dd03_F12
        opS_dd12_F03 opS_dd12_F12 opS_dd13_F02 opS_dd13_F13 opS_dd23_F01 opS_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` annihilates the derivative monomial `dd03_F12`. -/
lemma opPi_dd03_F12 :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) =
      (0 : JetAlgebra) := by
  rw [opPi_apply,
    projDDF5 opS opS_dd01_F01 opS_dd01_F23 opS_dd02_F02 opS_dd02_F13 opS_dd03_F03 opS_dd03_F12
        opS_dd12_F03 opS_dd12_F12 opS_dd13_F02 opS_dd13_F13 opS_dd23_F01 opS_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` annihilates the derivative monomial `dd12_F03`. -/
lemma opPi_dd12_F03 :
    opPi (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) =
      (0 : JetAlgebra) := by
  rw [opPi_apply,
    projDDF6 opS opS_dd01_F01 opS_dd01_F23 opS_dd02_F02 opS_dd02_F13 opS_dd03_F03 opS_dd03_F12
        opS_dd12_F03 opS_dd12_F12 opS_dd13_F02 opS_dd13_F13 opS_dd23_F01 opS_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` annihilates the derivative monomial `dd12_F12`. -/
lemma opPi_dd12_F12 :
    opPi (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) =
      (0 : JetAlgebra) := by
  rw [opPi_apply,
    projDDF7 opS opS_dd01_F01 opS_dd01_F23 opS_dd02_F02 opS_dd02_F13 opS_dd03_F03 opS_dd03_F12
        opS_dd12_F03 opS_dd12_F12 opS_dd13_F02 opS_dd13_F13 opS_dd23_F01 opS_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` annihilates the derivative monomial `dd13_F02`. -/
lemma opPi_dd13_F02 :
    opPi (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) =
      (0 : JetAlgebra) := by
  rw [opPi_apply,
    projDDF8 opS opS_dd01_F01 opS_dd01_F23 opS_dd02_F02 opS_dd02_F13 opS_dd03_F03 opS_dd03_F12
        opS_dd12_F03 opS_dd12_F12 opS_dd13_F02 opS_dd13_F13 opS_dd23_F01 opS_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` annihilates the derivative monomial `dd13_F13`. -/
lemma opPi_dd13_F13 :
    opPi (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) =
      (0 : JetAlgebra) := by
  rw [opPi_apply,
    projDDF9 opS opS_dd01_F01 opS_dd01_F23 opS_dd02_F02 opS_dd02_F13 opS_dd03_F03 opS_dd03_F12
        opS_dd12_F03 opS_dd12_F12 opS_dd13_F02 opS_dd13_F13 opS_dd23_F01 opS_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` annihilates the derivative monomial `dd23_F01`. -/
lemma opPi_dd23_F01 :
    opPi (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) =
      (0 : JetAlgebra) := by
  rw [opPi_apply,
    projDDF10 opS opS_dd01_F01 opS_dd01_F23 opS_dd02_F02 opS_dd02_F13 opS_dd03_F03 opS_dd03_F12
        opS_dd12_F03 opS_dd12_F12 opS_dd13_F02 opS_dd13_F13 opS_dd23_F01 opS_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` annihilates the derivative monomial `dd23_F23`. -/
lemma opPi_dd23_F23 :
    opPi (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) =
      (0 : JetAlgebra) := by
  rw [opPi_apply,
    projDDF11 opS opS_dd01_F01 opS_dd01_F23 opS_dd02_F02 opS_dd02_F13 opS_dd03_F03 opS_dd03_F12
        opS_dd12_F03 opS_dd12_F12 opS_dd13_F02 opS_dd13_F13 opS_dd23_F01 opS_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` on the σ-contracted fermion pair `u0`. -/
lemma opPi_u0 :
    opPi (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) =
      (-(Complex.I/4)) • fermionKineticTerm := by
  rw [opPi_apply,
    projFMu0 opS opS_u0 opS_u1 opS_u2 opS_u3,
    ← fermionKineticTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` on the σ-contracted fermion pair `u1`. -/
lemma opPi_u1 :
    opPi (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0) =
      (Complex.I/4) • fermionKineticTerm := by
  rw [opPi_apply,
    projFMu1 opS opS_u0 opS_u1 opS_u2 opS_u3,
    ← fermionKineticTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` on the σ-contracted fermion pair `u2`. -/
lemma opPi_u2 :
    opPi (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0) =
      (1/4 : ℂ) • fermionKineticTerm := by
  rw [opPi_apply,
    projFMu2 opS opS_u0 opS_u1 opS_u2 opS_u3,
    ← fermionKineticTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` on the σ-contracted fermion pair `u3`. -/
lemma opPi_u3 :
    opPi (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) =
      (Complex.I/4) • fermionKineticTerm := by
  rw [opPi_apply,
    projFMu3 opS opS_u0 opS_u1 opS_u2 opS_u3,
    ← fermionKineticTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` on the σ-contracted fermion pair `ubar0`. -/
lemma opPi_ubar0 :
    opPi (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) =
      (Complex.I/4) • fermionKineticTermBar := by
  rw [opPi_apply,
    projFMubar0 opS opS_ubar0 opS_ubar1 opS_ubar2 opS_ubar3,
    ← fermionKineticTermBar_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` on the σ-contracted fermion pair `ubar1`. -/
lemma opPi_ubar1 :
    opPi (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0) =
      (-(Complex.I/4)) • fermionKineticTermBar := by
  rw [opPi_apply,
    projFMubar1 opS opS_ubar0 opS_ubar1 opS_ubar2 opS_ubar3,
    ← fermionKineticTermBar_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` on the σ-contracted fermion pair `ubar2`. -/
lemma opPi_ubar2 :
    opPi (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0) =
      (-(1/4) : ℂ) • fermionKineticTermBar := by
  rw [opPi_apply,
    projFMubar2 opS opS_ubar0 opS_ubar1 opS_ubar2 opS_ubar3,
    ← fermionKineticTermBar_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` on the σ-contracted fermion pair `ubar3`. -/
lemma opPi_ubar3 :
    opPi (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) =
      (-(Complex.I/4)) • fermionKineticTermBar := by
  rw [opPi_apply,
    projFMubar3 opS opS_ubar0 opS_ubar1 opS_ubar2 opS_ubar3,
    ← fermionKineticTermBar_eq]
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
end JetAlgebra

end QED
