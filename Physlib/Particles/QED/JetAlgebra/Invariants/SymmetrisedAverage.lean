/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.QED.JetAlgebra.Invariants.BoostFermionPairs
/-!
# The symmetrised boost average

A rational combination of the paired boosts at `t = 2, 3, 4` together with the
identity (`boostProjZ`, `boostProjX`, `boostProjY`) realises the single-axis
boost averages, and their mean `opS` fixes every Lorentz-invariant vector
while acting on the weight-eight monomials by an explicit rational matrix (the
`opS_*` lemmas).
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

/-- The `Z`-axis boost-weighted average: the identity together with the
  paired boosts at `t = 2, 3, 4`, with weights chosen so that the operator
  fixes invariant vectors and acts as the Klein-restricted single-axis
  average on the weight-eight sector. -/
noncomputable def boostProjZ : Module.End ℂ JetAlgebra :=
  (65359/21600 : ℂ) • LinearMap.id
  + (-133264/99225 : ℂ) • (repLorentzGroup (boostZel 2 (by norm_num)) +
      repLorentzGroup ((boostZel 2 (by norm_num))⁻¹))
  + (384183/1019200 : ℂ) • (repLorentzGroup (boostZel 3 (by norm_num)) +
      repLorentzGroup ((boostZel 3 (by norm_num))⁻¹))
  + (-60416/1289925 : ℂ) • (repLorentzGroup (boostZel 4 (by norm_num)) +
      repLorentzGroup ((boostZel 4 (by norm_num))⁻¹))

/-- The `X`-axis boost-weighted average: the identity together with the
  paired boosts at `t = 2, 3, 4`, with weights chosen so that the operator
  fixes invariant vectors and acts as the Klein-restricted single-axis
  average on the weight-eight sector. -/
noncomputable def boostProjX : Module.End ℂ JetAlgebra :=
  (65359/21600 : ℂ) • LinearMap.id
  + (-133264/99225 : ℂ) • (repLorentzGroup (boostXel 2 (by norm_num)) +
      repLorentzGroup ((boostXel 2 (by norm_num))⁻¹))
  + (384183/1019200 : ℂ) • (repLorentzGroup (boostXel 3 (by norm_num)) +
      repLorentzGroup ((boostXel 3 (by norm_num))⁻¹))
  + (-60416/1289925 : ℂ) • (repLorentzGroup (boostXel 4 (by norm_num)) +
      repLorentzGroup ((boostXel 4 (by norm_num))⁻¹))

/-- The `Y`-axis boost-weighted average: the identity together with the
  paired boosts at `t = 2, 3, 4`, with weights chosen so that the operator
  fixes invariant vectors and acts as the Klein-restricted single-axis
  average on the weight-eight sector. -/
noncomputable def boostProjY : Module.End ℂ JetAlgebra :=
  (65359/21600 : ℂ) • LinearMap.id
  + (-133264/99225 : ℂ) • (repLorentzGroup (boostYel 2 (by norm_num)) +
      repLorentzGroup ((boostYel 2 (by norm_num))⁻¹))
  + (384183/1019200 : ℂ) • (repLorentzGroup (boostYel 3 (by norm_num)) +
      repLorentzGroup ((boostYel 3 (by norm_num))⁻¹))
  + (-60416/1289925 : ℂ) • (repLorentzGroup (boostYel 4 (by norm_num)) +
      repLorentzGroup ((boostYel 4 (by norm_num))⁻¹))

/-- The symmetrised boost average over the three axes. -/
noncomputable def opS : Module.End ℂ JetAlgebra :=
  (3⁻¹ : ℂ) • (boostProjZ + boostProjX + boostProjY)

/-- The operator `opS` fixes every Lorentz-invariant vector: each boost term
  fixes it and the weights sum to one. -/
lemma opS_apply_of_invariant {y : JetAlgebra}
    (hinv : ∀ Λ : SL(2,ℂ), repLorentzGroup Λ y = y) : opS y = y := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply, hinv]
  match_scalars
  norm_num

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `F01 * F01`. -/
lemma opS_F01_F01 :
    opS (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_F01_F01 2 (by norm_num),
    pairZ_F01_F01 3 (by norm_num),
    pairZ_F01_F01 4 (by norm_num),
    pairX_F01_F01 2 (by norm_num),
    pairX_F01_F01 3 (by norm_num),
    pairX_F01_F01 4 (by norm_num),
    pairY_F01_F01 2 (by norm_num),
    pairY_F01_F01 3 (by norm_num),
    pairY_F01_F01 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `F01 * F23`. -/
lemma opS_F01_F23 :
    opS (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2))
      + (1/6 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_F01_F23 2 (by norm_num),
    pairZ_F01_F23 3 (by norm_num),
    pairZ_F01_F23 4 (by norm_num),
    pairX_F01_F23 2 (by norm_num),
    pairX_F01_F23 3 (by norm_num),
    pairX_F01_F23 4 (by norm_num),
    pairY_F01_F23 2 (by norm_num),
    pairY_F01_F23 3 (by norm_num),
    pairY_F01_F23 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `F02 * F02`. -/
lemma opS_F02_F02 :
    opS (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_F02_F02 2 (by norm_num),
    pairZ_F02_F02 3 (by norm_num),
    pairZ_F02_F02 4 (by norm_num),
    pairX_F02_F02 2 (by norm_num),
    pairX_F02_F02 3 (by norm_num),
    pairX_F02_F02 4 (by norm_num),
    pairY_F02_F02 2 (by norm_num),
    pairY_F02_F02 3 (by norm_num),
    pairY_F02_F02 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `F02 * F13`. -/
lemma opS_F02_F13 :
    opS (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_F02_F13 2 (by norm_num),
    pairZ_F02_F13 3 (by norm_num),
    pairZ_F02_F13 4 (by norm_num),
    pairX_F02_F13 2 (by norm_num),
    pairX_F02_F13 3 (by norm_num),
    pairX_F02_F13 4 (by norm_num),
    pairY_F02_F13 2 (by norm_num),
    pairY_F02_F13 3 (by norm_num),
    pairY_F02_F13 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `F03 * F03`. -/
lemma opS_F03_F03 :
    opS (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_F03_F03 2 (by norm_num),
    pairZ_F03_F03 3 (by norm_num),
    pairZ_F03_F03 4 (by norm_num),
    pairX_F03_F03 2 (by norm_num),
    pairX_F03_F03 3 (by norm_num),
    pairX_F03_F03 4 (by norm_num),
    pairY_F03_F03 2 (by norm_num),
    pairY_F03_F03 3 (by norm_num),
    pairY_F03_F03 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `F03 * F12`. -/
lemma opS_F03_F12 :
    opS (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1))
      + (1/6 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_F03_F12 2 (by norm_num),
    pairZ_F03_F12 3 (by norm_num),
    pairZ_F03_F12 4 (by norm_num),
    pairX_F03_F12 2 (by norm_num),
    pairX_F03_F12 3 (by norm_num),
    pairX_F03_F12 4 (by norm_num),
    pairY_F03_F12 2 (by norm_num),
    pairY_F03_F12 3 (by norm_num),
    pairY_F03_F12 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `F12 * F12`. -/
lemma opS_F12_F12 :
    opS (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_F12_F12 2 (by norm_num),
    pairZ_F12_F12 3 (by norm_num),
    pairZ_F12_F12 4 (by norm_num),
    pairX_F12_F12 2 (by norm_num),
    pairX_F12_F12 3 (by norm_num),
    pairX_F12_F12 4 (by norm_num),
    pairY_F12_F12 2 (by norm_num),
    pairY_F12_F12 3 (by norm_num),
    pairY_F12_F12 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `F13 * F13`. -/
lemma opS_F13_F13 :
    opS (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_F13_F13 2 (by norm_num),
    pairZ_F13_F13 3 (by norm_num),
    pairZ_F13_F13 4 (by norm_num),
    pairX_F13_F13 2 (by norm_num),
    pairX_F13_F13 3 (by norm_num),
    pairX_F13_F13 4 (by norm_num),
    pairY_F13_F13 2 (by norm_num),
    pairY_F13_F13 3 (by norm_num),
    pairY_F13_F13 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `F23 * F23`. -/
lemma opS_F23_F23 :
    opS (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_F23_F23 2 (by norm_num),
    pairZ_F23_F23 3 (by norm_num),
    pairZ_F23_F23 4 (by norm_num),
    pairX_F23_F23 2 (by norm_num),
    pairX_F23_F23 3 (by norm_num),
    pairX_F23_F23 4 (by norm_num),
    pairY_F23_F23 2 (by norm_num),
    pairY_F23_F23 3 (by norm_num),
    pairY_F23_F23 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `∂∂F01` with derivative indices `(0, 1)`. -/
lemma opS_dd01_F01 :
    opS (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) =
      (1/3 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_dd01_F01 2 (by norm_num),
    pairZ_dd01_F01 3 (by norm_num),
    pairZ_dd01_F01 4 (by norm_num),
    pairX_dd01_F01 2 (by norm_num),
    pairX_dd01_F01 3 (by norm_num),
    pairX_dd01_F01 4 (by norm_num),
    pairY_dd01_F01 2 (by norm_num),
    pairY_dd01_F01 3 (by norm_num),
    pairY_dd01_F01 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `∂∂F23` with derivative indices `(0, 1)`. -/
lemma opS_dd01_F23 :
    opS (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) =
      (1/3 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_dd01_F23 2 (by norm_num),
    pairZ_dd01_F23 3 (by norm_num),
    pairZ_dd01_F23 4 (by norm_num),
    pairX_dd01_F23 2 (by norm_num),
    pairX_dd01_F23 3 (by norm_num),
    pairX_dd01_F23 4 (by norm_num),
    pairY_dd01_F23 2 (by norm_num),
    pairY_dd01_F23 3 (by norm_num),
    pairY_dd01_F23 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `∂∂F02` with derivative indices `(0, 2)`. -/
lemma opS_dd02_F02 :
    opS (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) =
      (1/3 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_dd02_F02 2 (by norm_num),
    pairZ_dd02_F02 3 (by norm_num),
    pairZ_dd02_F02 4 (by norm_num),
    pairX_dd02_F02 2 (by norm_num),
    pairX_dd02_F02 3 (by norm_num),
    pairX_dd02_F02 4 (by norm_num),
    pairY_dd02_F02 2 (by norm_num),
    pairY_dd02_F02 3 (by norm_num),
    pairY_dd02_F02 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `∂∂F13` with derivative indices `(0, 2)`. -/
lemma opS_dd02_F13 :
    opS (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) =
      (1/3 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_dd02_F13 2 (by norm_num),
    pairZ_dd02_F13 3 (by norm_num),
    pairZ_dd02_F13 4 (by norm_num),
    pairX_dd02_F13 2 (by norm_num),
    pairX_dd02_F13 3 (by norm_num),
    pairX_dd02_F13 4 (by norm_num),
    pairY_dd02_F13 2 (by norm_num),
    pairY_dd02_F13 3 (by norm_num),
    pairY_dd02_F13 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `∂∂F03` with derivative indices `(0, 3)`. -/
lemma opS_dd03_F03 :
    opS (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) =
      (1/3 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_dd03_F03 2 (by norm_num),
    pairZ_dd03_F03 3 (by norm_num),
    pairZ_dd03_F03 4 (by norm_num),
    pairX_dd03_F03 2 (by norm_num),
    pairX_dd03_F03 3 (by norm_num),
    pairX_dd03_F03 4 (by norm_num),
    pairY_dd03_F03 2 (by norm_num),
    pairY_dd03_F03 3 (by norm_num),
    pairY_dd03_F03 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `∂∂F12` with derivative indices `(0, 3)`. -/
lemma opS_dd03_F12 :
    opS (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) =
      (1/3 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_dd03_F12 2 (by norm_num),
    pairZ_dd03_F12 3 (by norm_num),
    pairZ_dd03_F12 4 (by norm_num),
    pairX_dd03_F12 2 (by norm_num),
    pairX_dd03_F12 3 (by norm_num),
    pairX_dd03_F12 4 (by norm_num),
    pairY_dd03_F12 2 (by norm_num),
    pairY_dd03_F12 3 (by norm_num),
    pairY_dd03_F12 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `∂∂F03` with derivative indices `(1, 2)`. -/
lemma opS_dd12_F03 :
    opS (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_dd12_F03 2 (by norm_num),
    pairZ_dd12_F03 3 (by norm_num),
    pairZ_dd12_F03 4 (by norm_num),
    pairX_dd12_F03 2 (by norm_num),
    pairX_dd12_F03 3 (by norm_num),
    pairX_dd12_F03 4 (by norm_num),
    pairY_dd12_F03 2 (by norm_num),
    pairY_dd12_F03 3 (by norm_num),
    pairY_dd12_F03 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `∂∂F12` with derivative indices `(1, 2)`. -/
lemma opS_dd12_F12 :
    opS (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_dd12_F12 2 (by norm_num),
    pairZ_dd12_F12 3 (by norm_num),
    pairZ_dd12_F12 4 (by norm_num),
    pairX_dd12_F12 2 (by norm_num),
    pairX_dd12_F12 3 (by norm_num),
    pairX_dd12_F12 4 (by norm_num),
    pairY_dd12_F12 2 (by norm_num),
    pairY_dd12_F12 3 (by norm_num),
    pairY_dd12_F12 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `∂∂F02` with derivative indices `(1, 3)`. -/
lemma opS_dd13_F02 :
    opS (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_dd13_F02 2 (by norm_num),
    pairZ_dd13_F02 3 (by norm_num),
    pairZ_dd13_F02 4 (by norm_num),
    pairX_dd13_F02 2 (by norm_num),
    pairX_dd13_F02 3 (by norm_num),
    pairX_dd13_F02 4 (by norm_num),
    pairY_dd13_F02 2 (by norm_num),
    pairY_dd13_F02 3 (by norm_num),
    pairY_dd13_F02 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `∂∂F13` with derivative indices `(1, 3)`. -/
lemma opS_dd13_F13 :
    opS (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_dd13_F13 2 (by norm_num),
    pairZ_dd13_F13 3 (by norm_num),
    pairZ_dd13_F13 4 (by norm_num),
    pairX_dd13_F13 2 (by norm_num),
    pairX_dd13_F13 3 (by norm_num),
    pairX_dd13_F13 4 (by norm_num),
    pairY_dd13_F13 2 (by norm_num),
    pairY_dd13_F13 3 (by norm_num),
    pairY_dd13_F13 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `∂∂F01` with derivative indices `(2, 3)`. -/
lemma opS_dd23_F01 :
    opS (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_dd23_F01 2 (by norm_num),
    pairZ_dd23_F01 3 (by norm_num),
    pairZ_dd23_F01 4 (by norm_num),
    pairX_dd23_F01 2 (by norm_num),
    pairX_dd23_F01 3 (by norm_num),
    pairX_dd23_F01 4 (by norm_num),
    pairY_dd23_F01 2 (by norm_num),
    pairY_dd23_F01 3 (by norm_num),
    pairY_dd23_F01 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `∂∂F23` with derivative indices `(2, 3)`. -/
lemma opS_dd23_F23 :
    opS (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_dd23_F23 2 (by norm_num),
    pairZ_dd23_F23 3 (by norm_num),
    pairZ_dd23_F23 4 (by norm_num),
    pairX_dd23_F23 2 (by norm_num),
    pairX_dd23_F23 3 (by norm_num),
    pairX_dd23_F23 4 (by norm_num),
    pairY_dd23_F23 2 (by norm_num),
    pairY_dd23_F23 3 (by norm_num),
    pairY_dd23_F23 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on the σ-contracted fermion pair `u0`. -/
lemma opS_u0 :
    opS (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) =
      (1/2 : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1)
      + (-(1/6) : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0)
      + (-(Complex.I/6)) • (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0)
      + (-(1/6) : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_u0 2 (by norm_num),
    pairZ_u0 3 (by norm_num),
    pairZ_u0 4 (by norm_num),
    pairX_u0 2 (by norm_num),
    pairX_u0 3 (by norm_num),
    pairX_u0 4 (by norm_num),
    pairY_u0 2 (by norm_num),
    pairY_u0 3 (by norm_num),
    pairY_u0 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on the σ-contracted fermion pair `u1`. -/
lemma opS_u1 :
    opS (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0) =
      (5/6 : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0)
      + (-(1/6) : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_u1 2 (by norm_num),
    pairZ_u1 3 (by norm_num),
    pairZ_u1 4 (by norm_num),
    pairX_u1 2 (by norm_num),
    pairX_u1 3 (by norm_num),
    pairX_u1 4 (by norm_num),
    pairY_u1 2 (by norm_num),
    pairY_u1 3 (by norm_num),
    pairY_u1 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on the σ-contracted fermion pair `u2`. -/
lemma opS_u2 :
    opS (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0) =
      (5/6 : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0)
      + (Complex.I/6) • (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_u2 2 (by norm_num),
    pairZ_u2 3 (by norm_num),
    pairZ_u2 4 (by norm_num),
    pairX_u2 2 (by norm_num),
    pairX_u2 3 (by norm_num),
    pairX_u2 4 (by norm_num),
    pairY_u2 2 (by norm_num),
    pairY_u2 3 (by norm_num),
    pairY_u2 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on the σ-contracted fermion pair `u3`. -/
lemma opS_u3 :
    opS (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) =
      (5/6 : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1)
      + (-(1/6) : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_u3 2 (by norm_num),
    pairZ_u3 3 (by norm_num),
    pairZ_u3 4 (by norm_num),
    pairX_u3 2 (by norm_num),
    pairX_u3 3 (by norm_num),
    pairX_u3 4 (by norm_num),
    pairY_u3 2 (by norm_num),
    pairY_u3 3 (by norm_num),
    pairY_u3 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on the σ-contracted fermion pair `ubar0`. -/
lemma opS_ubar0 :
    opS (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) =
      (1/2 : ℂ) • (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1)
      + (-(1/6) : ℂ) • (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0)
      + (-(Complex.I/6)) • (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0)
      + (-(1/6) : ℂ) • (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_ubar0 2 (by norm_num),
    pairZ_ubar0 3 (by norm_num),
    pairZ_ubar0 4 (by norm_num),
    pairX_ubar0 2 (by norm_num),
    pairX_ubar0 3 (by norm_num),
    pairX_ubar0 4 (by norm_num),
    pairY_ubar0 2 (by norm_num),
    pairY_ubar0 3 (by norm_num),
    pairY_ubar0 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on the σ-contracted fermion pair `ubar1`. -/
lemma opS_ubar1 :
    opS (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0) =
      (5/6 : ℂ) • (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0)
      + (-(1/6) : ℂ) • (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_ubar1 2 (by norm_num),
    pairZ_ubar1 3 (by norm_num),
    pairZ_ubar1 4 (by norm_num),
    pairX_ubar1 2 (by norm_num),
    pairX_ubar1 3 (by norm_num),
    pairX_ubar1 4 (by norm_num),
    pairY_ubar1 2 (by norm_num),
    pairY_ubar1 3 (by norm_num),
    pairY_ubar1 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on the σ-contracted fermion pair `ubar2`. -/
lemma opS_ubar2 :
    opS (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0) =
      (5/6 : ℂ) • (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0)
      + (Complex.I/6) • (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_ubar2 2 (by norm_num),
    pairZ_ubar2 3 (by norm_num),
    pairZ_ubar2 4 (by norm_num),
    pairX_ubar2 2 (by norm_num),
    pairX_ubar2 3 (by norm_num),
    pairX_ubar2 4 (by norm_num),
    pairY_ubar2 2 (by norm_num),
    pairY_ubar2 3 (by norm_num),
    pairY_ubar2 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on the σ-contracted fermion pair `ubar3`. -/
lemma opS_ubar3 :
    opS (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) =
      (5/6 : ℂ) • (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1)
      + (-(1/6) : ℂ) • (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_ubar3 2 (by norm_num),
    pairZ_ubar3 3 (by norm_num),
    pairZ_ubar3 4 (by norm_num),
    pairX_ubar3 2 (by norm_num),
    pairX_ubar3 3 (by norm_num),
    pairX_ubar3 4 (by norm_num),
    pairY_ubar3 2 (by norm_num),
    pairY_ubar3 3 (by norm_num),
    pairY_ubar3 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

/-!

### The projector polynomial and the weight-eight endgame

-/
/-- The quintic projector polynomial in the symmetrised boost average `opS`:
  the unique degree-five polynomial with value one at the invariant eigenvalue
  and vanishing on the remaining boost eigenvalues of the weight-eight Klein
  sector. -/
noncomputable def opPi : Module.End ℂ JetAlgebra :=
  (-1 : ℂ) • (1 : Module.End ℂ JetAlgebra) + (137/10 : ℂ) • opS
    + (-(135/2) : ℂ) • (opS * opS) + (153 : ℂ) • (opS * opS * opS)
    + (-162 : ℂ) • (opS * opS * opS * opS)
    + (324/5 : ℂ) • (opS * opS * opS * opS * opS)

/-- The projector polynomial, termwise. -/
lemma opPi_apply (v : JetAlgebra) :
    opPi v = (-1 : ℂ) • v + (137/10 : ℂ) • opS v
      + (-(135/2) : ℂ) • opS (opS v) + (153 : ℂ) • opS (opS (opS v))
      + (-162 : ℂ) • opS (opS (opS (opS v)))
      + (324/5 : ℂ) • opS (opS (opS (opS (opS v)))) := by
  simp only [opPi, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    Module.End.mul_apply]

/-- The projector fixes every Lorentz-invariant vector: `opS` fixes it and the
  coefficients sum to one. -/
lemma opPi_apply_of_invariant {y : JetAlgebra}
    (hinv : ∀ Λ : SL(2,ℂ), repLorentzGroup Λ y = y) : opPi y = y := by
  have hS : opS y = y := opS_apply_of_invariant hinv
  rw [opPi_apply]
  simp only [hS]
  match_scalars
  norm_num
end JetAlgebra

end QED
