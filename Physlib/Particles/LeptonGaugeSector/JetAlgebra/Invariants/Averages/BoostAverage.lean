/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.Invariants.Averages.RotationPiBoostAverage
/-!
# The average over the boosts

The average over the boosts of `Subgroups/AxisBoosts`, whose action on the
weight-eight monomials is tabulated in the `Subgroups/BoostsOn*` files.

A boost subgroup is non-compact, so it carries no invariant average. In its
place a rational combination of the boosts at `t = 2, 3, 4` paired with their
inverses, together with the identity (`boostAvgZ`, `boostAvgX`, `boostAvgY`),
has weights summing to one — so it still fixes every Lorentz-invariant vector —
while annihilating the unwanted boost eigenvalues. Their mean over the three
axes is `boostAvg`, which acts on the weight-eight monomials by an explicit rational
matrix (the `boostAvg_*` lemmas).
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

/-- The `Z`-axis boost-weighted average: the identity together with the
  paired boosts at `t = 2, 3, 4`, with weights chosen so that the operator
  fixes invariant vectors and acts as the rotation-averaged single-axis
  average on the weight-eight sector. -/
noncomputable def boostAvgZ : Module.End ℂ JetAlgebra :=
  (65359/21600 : ℂ) • LinearMap.id
  + (-133264/99225 : ℂ) • (repLorentzGroup (boostZel 2 (by norm_num)) +
      repLorentzGroup ((boostZel 2 (by norm_num))⁻¹))
  + (384183/1019200 : ℂ) • (repLorentzGroup (boostZel 3 (by norm_num)) +
      repLorentzGroup ((boostZel 3 (by norm_num))⁻¹))
  + (-60416/1289925 : ℂ) • (repLorentzGroup (boostZel 4 (by norm_num)) +
      repLorentzGroup ((boostZel 4 (by norm_num))⁻¹))

/-- The `X`-axis boost-weighted average: the identity together with the
  paired boosts at `t = 2, 3, 4`, with weights chosen so that the operator
  fixes invariant vectors and acts as the rotation-averaged single-axis
  average on the weight-eight sector. -/
noncomputable def boostAvgX : Module.End ℂ JetAlgebra :=
  (65359/21600 : ℂ) • LinearMap.id
  + (-133264/99225 : ℂ) • (repLorentzGroup (boostXel 2 (by norm_num)) +
      repLorentzGroup ((boostXel 2 (by norm_num))⁻¹))
  + (384183/1019200 : ℂ) • (repLorentzGroup (boostXel 3 (by norm_num)) +
      repLorentzGroup ((boostXel 3 (by norm_num))⁻¹))
  + (-60416/1289925 : ℂ) • (repLorentzGroup (boostXel 4 (by norm_num)) +
      repLorentzGroup ((boostXel 4 (by norm_num))⁻¹))

/-- The `Y`-axis boost-weighted average: the identity together with the
  paired boosts at `t = 2, 3, 4`, with weights chosen so that the operator
  fixes invariant vectors and acts as the rotation-averaged single-axis
  average on the weight-eight sector. -/
noncomputable def boostAvgY : Module.End ℂ JetAlgebra :=
  (65359/21600 : ℂ) • LinearMap.id
  + (-133264/99225 : ℂ) • (repLorentzGroup (boostYel 2 (by norm_num)) +
      repLorentzGroup ((boostYel 2 (by norm_num))⁻¹))
  + (384183/1019200 : ℂ) • (repLorentzGroup (boostYel 3 (by norm_num)) +
      repLorentzGroup ((boostYel 3 (by norm_num))⁻¹))
  + (-60416/1289925 : ℂ) • (repLorentzGroup (boostYel 4 (by norm_num)) +
      repLorentzGroup ((boostYel 4 (by norm_num))⁻¹))

/-- The symmetrised boost average over the three axes. -/
noncomputable def boostAvg : Module.End ℂ JetAlgebra :=
  (3⁻¹ : ℂ) • (boostAvgZ + boostAvgX + boostAvgY)

/-- The operator `boostAvg` fixes every Lorentz-invariant vector: each boost term
  fixes it and the weights sum to one. -/
lemma boostAvg_apply_of_invariant {y : JetAlgebra}
    (hinv : ∀ Λ : SL(2,ℂ), repLorentzGroup Λ y = y) : boostAvg y = y := by
  simp only [boostAvg, boostAvgZ, boostAvgX, boostAvgY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply, hinv]
  match_scalars
  norm_num

set_option maxHeartbeats 4000000 in
/-- The boost average `boostAvg` on `F01 * F01`. -/
lemma boostAvg_F01_F01 :
    boostAvg (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) := by
  simp only [boostAvg, boostAvgZ, boostAvgX, boostAvgY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [boostPairZ_F01_F01 2 (by norm_num),
    boostPairZ_F01_F01 3 (by norm_num),
    boostPairZ_F01_F01 4 (by norm_num),
    boostPairX_F01_F01 2 (by norm_num),
    boostPairX_F01_F01 3 (by norm_num),
    boostPairX_F01_F01 4 (by norm_num),
    boostPairY_F01_F01 2 (by norm_num),
    boostPairY_F01_F01 3 (by norm_num),
    boostPairY_F01_F01 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `boostAvg` on `F01 * F23`. -/
lemma boostAvg_F01_F23 :
    boostAvg (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2))
      + (1/6 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) := by
  simp only [boostAvg, boostAvgZ, boostAvgX, boostAvgY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [boostPairZ_F01_F23 2 (by norm_num),
    boostPairZ_F01_F23 3 (by norm_num),
    boostPairZ_F01_F23 4 (by norm_num),
    boostPairX_F01_F23 2 (by norm_num),
    boostPairX_F01_F23 3 (by norm_num),
    boostPairX_F01_F23 4 (by norm_num),
    boostPairY_F01_F23 2 (by norm_num),
    boostPairY_F01_F23 3 (by norm_num),
    boostPairY_F01_F23 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `boostAvg` on `F02 * F02`. -/
lemma boostAvg_F02_F02 :
    boostAvg (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) := by
  simp only [boostAvg, boostAvgZ, boostAvgX, boostAvgY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [boostPairZ_F02_F02 2 (by norm_num),
    boostPairZ_F02_F02 3 (by norm_num),
    boostPairZ_F02_F02 4 (by norm_num),
    boostPairX_F02_F02 2 (by norm_num),
    boostPairX_F02_F02 3 (by norm_num),
    boostPairX_F02_F02 4 (by norm_num),
    boostPairY_F02_F02 2 (by norm_num),
    boostPairY_F02_F02 3 (by norm_num),
    boostPairY_F02_F02 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `boostAvg` on `F02 * F13`. -/
lemma boostAvg_F02_F13 :
    boostAvg (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) := by
  simp only [boostAvg, boostAvgZ, boostAvgX, boostAvgY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [boostPairZ_F02_F13 2 (by norm_num),
    boostPairZ_F02_F13 3 (by norm_num),
    boostPairZ_F02_F13 4 (by norm_num),
    boostPairX_F02_F13 2 (by norm_num),
    boostPairX_F02_F13 3 (by norm_num),
    boostPairX_F02_F13 4 (by norm_num),
    boostPairY_F02_F13 2 (by norm_num),
    boostPairY_F02_F13 3 (by norm_num),
    boostPairY_F02_F13 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `boostAvg` on `F03 * F03`. -/
lemma boostAvg_F03_F03 :
    boostAvg (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) := by
  simp only [boostAvg, boostAvgZ, boostAvgX, boostAvgY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [boostPairZ_F03_F03 2 (by norm_num),
    boostPairZ_F03_F03 3 (by norm_num),
    boostPairZ_F03_F03 4 (by norm_num),
    boostPairX_F03_F03 2 (by norm_num),
    boostPairX_F03_F03 3 (by norm_num),
    boostPairX_F03_F03 4 (by norm_num),
    boostPairY_F03_F03 2 (by norm_num),
    boostPairY_F03_F03 3 (by norm_num),
    boostPairY_F03_F03 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `boostAvg` on `F03 * F12`. -/
lemma boostAvg_F03_F12 :
    boostAvg (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1))
      + (1/6 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) := by
  simp only [boostAvg, boostAvgZ, boostAvgX, boostAvgY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [boostPairZ_F03_F12 2 (by norm_num),
    boostPairZ_F03_F12 3 (by norm_num),
    boostPairZ_F03_F12 4 (by norm_num),
    boostPairX_F03_F12 2 (by norm_num),
    boostPairX_F03_F12 3 (by norm_num),
    boostPairX_F03_F12 4 (by norm_num),
    boostPairY_F03_F12 2 (by norm_num),
    boostPairY_F03_F12 3 (by norm_num),
    boostPairY_F03_F12 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `boostAvg` on `F12 * F12`. -/
lemma boostAvg_F12_F12 :
    boostAvg (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) := by
  simp only [boostAvg, boostAvgZ, boostAvgX, boostAvgY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [boostPairZ_F12_F12 2 (by norm_num),
    boostPairZ_F12_F12 3 (by norm_num),
    boostPairZ_F12_F12 4 (by norm_num),
    boostPairX_F12_F12 2 (by norm_num),
    boostPairX_F12_F12 3 (by norm_num),
    boostPairX_F12_F12 4 (by norm_num),
    boostPairY_F12_F12 2 (by norm_num),
    boostPairY_F12_F12 3 (by norm_num),
    boostPairY_F12_F12 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `boostAvg` on `F13 * F13`. -/
lemma boostAvg_F13_F13 :
    boostAvg (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) := by
  simp only [boostAvg, boostAvgZ, boostAvgX, boostAvgY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [boostPairZ_F13_F13 2 (by norm_num),
    boostPairZ_F13_F13 3 (by norm_num),
    boostPairZ_F13_F13 4 (by norm_num),
    boostPairX_F13_F13 2 (by norm_num),
    boostPairX_F13_F13 3 (by norm_num),
    boostPairX_F13_F13 4 (by norm_num),
    boostPairY_F13_F13 2 (by norm_num),
    boostPairY_F13_F13 3 (by norm_num),
    boostPairY_F13_F13 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `boostAvg` on `F23 * F23`. -/
lemma boostAvg_F23_F23 :
    boostAvg (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) := by
  simp only [boostAvg, boostAvgZ, boostAvgX, boostAvgY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [boostPairZ_F23_F23 2 (by norm_num),
    boostPairZ_F23_F23 3 (by norm_num),
    boostPairZ_F23_F23 4 (by norm_num),
    boostPairX_F23_F23 2 (by norm_num),
    boostPairX_F23_F23 3 (by norm_num),
    boostPairX_F23_F23 4 (by norm_num),
    boostPairY_F23_F23 2 (by norm_num),
    boostPairY_F23_F23 3 (by norm_num),
    boostPairY_F23_F23 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `boostAvg` on `∂∂F01` with derivative indices `(0, 1)`. -/
lemma boostAvg_dd01_F01 :
    boostAvg (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) =
      (1/3 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) := by
  simp only [boostAvg, boostAvgZ, boostAvgX, boostAvgY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [boostPairZ_dd01_F01 2 (by norm_num),
    boostPairZ_dd01_F01 3 (by norm_num),
    boostPairZ_dd01_F01 4 (by norm_num),
    boostPairX_dd01_F01 2 (by norm_num),
    boostPairX_dd01_F01 3 (by norm_num),
    boostPairX_dd01_F01 4 (by norm_num),
    boostPairY_dd01_F01 2 (by norm_num),
    boostPairY_dd01_F01 3 (by norm_num),
    boostPairY_dd01_F01 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `boostAvg` on `∂∂F23` with derivative indices `(0, 1)`. -/
lemma boostAvg_dd01_F23 :
    boostAvg (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) =
      (1/3 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) := by
  simp only [boostAvg, boostAvgZ, boostAvgX, boostAvgY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [boostPairZ_dd01_F23 2 (by norm_num),
    boostPairZ_dd01_F23 3 (by norm_num),
    boostPairZ_dd01_F23 4 (by norm_num),
    boostPairX_dd01_F23 2 (by norm_num),
    boostPairX_dd01_F23 3 (by norm_num),
    boostPairX_dd01_F23 4 (by norm_num),
    boostPairY_dd01_F23 2 (by norm_num),
    boostPairY_dd01_F23 3 (by norm_num),
    boostPairY_dd01_F23 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `boostAvg` on `∂∂F02` with derivative indices `(0, 2)`. -/
lemma boostAvg_dd02_F02 :
    boostAvg (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) =
      (1/3 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) := by
  simp only [boostAvg, boostAvgZ, boostAvgX, boostAvgY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [boostPairZ_dd02_F02 2 (by norm_num),
    boostPairZ_dd02_F02 3 (by norm_num),
    boostPairZ_dd02_F02 4 (by norm_num),
    boostPairX_dd02_F02 2 (by norm_num),
    boostPairX_dd02_F02 3 (by norm_num),
    boostPairX_dd02_F02 4 (by norm_num),
    boostPairY_dd02_F02 2 (by norm_num),
    boostPairY_dd02_F02 3 (by norm_num),
    boostPairY_dd02_F02 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `boostAvg` on `∂∂F13` with derivative indices `(0, 2)`. -/
lemma boostAvg_dd02_F13 :
    boostAvg (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) =
      (1/3 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) := by
  simp only [boostAvg, boostAvgZ, boostAvgX, boostAvgY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [boostPairZ_dd02_F13 2 (by norm_num),
    boostPairZ_dd02_F13 3 (by norm_num),
    boostPairZ_dd02_F13 4 (by norm_num),
    boostPairX_dd02_F13 2 (by norm_num),
    boostPairX_dd02_F13 3 (by norm_num),
    boostPairX_dd02_F13 4 (by norm_num),
    boostPairY_dd02_F13 2 (by norm_num),
    boostPairY_dd02_F13 3 (by norm_num),
    boostPairY_dd02_F13 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `boostAvg` on `∂∂F03` with derivative indices `(0, 3)`. -/
lemma boostAvg_dd03_F03 :
    boostAvg (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) =
      (1/3 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) := by
  simp only [boostAvg, boostAvgZ, boostAvgX, boostAvgY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [boostPairZ_dd03_F03 2 (by norm_num),
    boostPairZ_dd03_F03 3 (by norm_num),
    boostPairZ_dd03_F03 4 (by norm_num),
    boostPairX_dd03_F03 2 (by norm_num),
    boostPairX_dd03_F03 3 (by norm_num),
    boostPairX_dd03_F03 4 (by norm_num),
    boostPairY_dd03_F03 2 (by norm_num),
    boostPairY_dd03_F03 3 (by norm_num),
    boostPairY_dd03_F03 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `boostAvg` on `∂∂F12` with derivative indices `(0, 3)`. -/
lemma boostAvg_dd03_F12 :
    boostAvg (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) =
      (1/3 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) := by
  simp only [boostAvg, boostAvgZ, boostAvgX, boostAvgY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [boostPairZ_dd03_F12 2 (by norm_num),
    boostPairZ_dd03_F12 3 (by norm_num),
    boostPairZ_dd03_F12 4 (by norm_num),
    boostPairX_dd03_F12 2 (by norm_num),
    boostPairX_dd03_F12 3 (by norm_num),
    boostPairX_dd03_F12 4 (by norm_num),
    boostPairY_dd03_F12 2 (by norm_num),
    boostPairY_dd03_F12 3 (by norm_num),
    boostPairY_dd03_F12 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `boostAvg` on `∂∂F03` with derivative indices `(1, 2)`. -/
lemma boostAvg_dd12_F03 :
    boostAvg (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) := by
  simp only [boostAvg, boostAvgZ, boostAvgX, boostAvgY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [boostPairZ_dd12_F03 2 (by norm_num),
    boostPairZ_dd12_F03 3 (by norm_num),
    boostPairZ_dd12_F03 4 (by norm_num),
    boostPairX_dd12_F03 2 (by norm_num),
    boostPairX_dd12_F03 3 (by norm_num),
    boostPairX_dd12_F03 4 (by norm_num),
    boostPairY_dd12_F03 2 (by norm_num),
    boostPairY_dd12_F03 3 (by norm_num),
    boostPairY_dd12_F03 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `boostAvg` on `∂∂F12` with derivative indices `(1, 2)`. -/
lemma boostAvg_dd12_F12 :
    boostAvg (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) := by
  simp only [boostAvg, boostAvgZ, boostAvgX, boostAvgY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [boostPairZ_dd12_F12 2 (by norm_num),
    boostPairZ_dd12_F12 3 (by norm_num),
    boostPairZ_dd12_F12 4 (by norm_num),
    boostPairX_dd12_F12 2 (by norm_num),
    boostPairX_dd12_F12 3 (by norm_num),
    boostPairX_dd12_F12 4 (by norm_num),
    boostPairY_dd12_F12 2 (by norm_num),
    boostPairY_dd12_F12 3 (by norm_num),
    boostPairY_dd12_F12 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `boostAvg` on `∂∂F02` with derivative indices `(1, 3)`. -/
lemma boostAvg_dd13_F02 :
    boostAvg (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) := by
  simp only [boostAvg, boostAvgZ, boostAvgX, boostAvgY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [boostPairZ_dd13_F02 2 (by norm_num),
    boostPairZ_dd13_F02 3 (by norm_num),
    boostPairZ_dd13_F02 4 (by norm_num),
    boostPairX_dd13_F02 2 (by norm_num),
    boostPairX_dd13_F02 3 (by norm_num),
    boostPairX_dd13_F02 4 (by norm_num),
    boostPairY_dd13_F02 2 (by norm_num),
    boostPairY_dd13_F02 3 (by norm_num),
    boostPairY_dd13_F02 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `boostAvg` on `∂∂F13` with derivative indices `(1, 3)`. -/
lemma boostAvg_dd13_F13 :
    boostAvg (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) := by
  simp only [boostAvg, boostAvgZ, boostAvgX, boostAvgY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [boostPairZ_dd13_F13 2 (by norm_num),
    boostPairZ_dd13_F13 3 (by norm_num),
    boostPairZ_dd13_F13 4 (by norm_num),
    boostPairX_dd13_F13 2 (by norm_num),
    boostPairX_dd13_F13 3 (by norm_num),
    boostPairX_dd13_F13 4 (by norm_num),
    boostPairY_dd13_F13 2 (by norm_num),
    boostPairY_dd13_F13 3 (by norm_num),
    boostPairY_dd13_F13 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `boostAvg` on `∂∂F01` with derivative indices `(2, 3)`. -/
lemma boostAvg_dd23_F01 :
    boostAvg (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) := by
  simp only [boostAvg, boostAvgZ, boostAvgX, boostAvgY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [boostPairZ_dd23_F01 2 (by norm_num),
    boostPairZ_dd23_F01 3 (by norm_num),
    boostPairZ_dd23_F01 4 (by norm_num),
    boostPairX_dd23_F01 2 (by norm_num),
    boostPairX_dd23_F01 3 (by norm_num),
    boostPairX_dd23_F01 4 (by norm_num),
    boostPairY_dd23_F01 2 (by norm_num),
    boostPairY_dd23_F01 3 (by norm_num),
    boostPairY_dd23_F01 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `boostAvg` on `∂∂F23` with derivative indices `(2, 3)`. -/
lemma boostAvg_dd23_F23 :
    boostAvg (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) := by
  simp only [boostAvg, boostAvgZ, boostAvgX, boostAvgY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [boostPairZ_dd23_F23 2 (by norm_num),
    boostPairZ_dd23_F23 3 (by norm_num),
    boostPairZ_dd23_F23 4 (by norm_num),
    boostPairX_dd23_F23 2 (by norm_num),
    boostPairX_dd23_F23 3 (by norm_num),
    boostPairX_dd23_F23 4 (by norm_num),
    boostPairY_dd23_F23 2 (by norm_num),
    boostPairY_dd23_F23 3 (by norm_num),
    boostPairY_dd23_F23 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `boostAvg` on the σ-contracted fermion pair `u0`. -/
lemma boostAvg_u0 :
    boostAvg (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) =
      (1/2 : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1)
      + (-(1/6) : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0)
      + (-(Complex.I/6)) • (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0)
      + (-(1/6) : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) := by
  simp only [boostAvg, boostAvgZ, boostAvgX, boostAvgY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [boostPairZ_u0 2 (by norm_num),
    boostPairZ_u0 3 (by norm_num),
    boostPairZ_u0 4 (by norm_num),
    boostPairX_u0 2 (by norm_num),
    boostPairX_u0 3 (by norm_num),
    boostPairX_u0 4 (by norm_num),
    boostPairY_u0 2 (by norm_num),
    boostPairY_u0 3 (by norm_num),
    boostPairY_u0 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `boostAvg` on the σ-contracted fermion pair `u1`. -/
lemma boostAvg_u1 :
    boostAvg (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0) =
      (5/6 : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0)
      + (-(1/6) : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) := by
  simp only [boostAvg, boostAvgZ, boostAvgX, boostAvgY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [boostPairZ_u1 2 (by norm_num),
    boostPairZ_u1 3 (by norm_num),
    boostPairZ_u1 4 (by norm_num),
    boostPairX_u1 2 (by norm_num),
    boostPairX_u1 3 (by norm_num),
    boostPairX_u1 4 (by norm_num),
    boostPairY_u1 2 (by norm_num),
    boostPairY_u1 3 (by norm_num),
    boostPairY_u1 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `boostAvg` on the σ-contracted fermion pair `u2`. -/
lemma boostAvg_u2 :
    boostAvg (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0) =
      (5/6 : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0)
      + (Complex.I/6) • (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) := by
  simp only [boostAvg, boostAvgZ, boostAvgX, boostAvgY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [boostPairZ_u2 2 (by norm_num),
    boostPairZ_u2 3 (by norm_num),
    boostPairZ_u2 4 (by norm_num),
    boostPairX_u2 2 (by norm_num),
    boostPairX_u2 3 (by norm_num),
    boostPairX_u2 4 (by norm_num),
    boostPairY_u2 2 (by norm_num),
    boostPairY_u2 3 (by norm_num),
    boostPairY_u2 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `boostAvg` on the σ-contracted fermion pair `u3`. -/
lemma boostAvg_u3 :
    boostAvg (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) =
      (5/6 : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1)
      + (-(1/6) : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) := by
  simp only [boostAvg, boostAvgZ, boostAvgX, boostAvgY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [boostPairZ_u3 2 (by norm_num),
    boostPairZ_u3 3 (by norm_num),
    boostPairZ_u3 4 (by norm_num),
    boostPairX_u3 2 (by norm_num),
    boostPairX_u3 3 (by norm_num),
    boostPairX_u3 4 (by norm_num),
    boostPairY_u3 2 (by norm_num),
    boostPairY_u3 3 (by norm_num),
    boostPairY_u3 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `boostAvg` on the σ-contracted fermion pair `ubar0`. -/
lemma boostAvg_ubar0 :
    boostAvg (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) =
      (1/2 : ℂ) • (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1)
      + (-(1/6) : ℂ) • (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0)
      + (-(Complex.I/6)) • (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0)
      + (-(1/6) : ℂ) • (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) := by
  simp only [boostAvg, boostAvgZ, boostAvgX, boostAvgY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [boostPairZ_ubar0 2 (by norm_num),
    boostPairZ_ubar0 3 (by norm_num),
    boostPairZ_ubar0 4 (by norm_num),
    boostPairX_ubar0 2 (by norm_num),
    boostPairX_ubar0 3 (by norm_num),
    boostPairX_ubar0 4 (by norm_num),
    boostPairY_ubar0 2 (by norm_num),
    boostPairY_ubar0 3 (by norm_num),
    boostPairY_ubar0 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `boostAvg` on the σ-contracted fermion pair `ubar1`. -/
lemma boostAvg_ubar1 :
    boostAvg (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0) =
      (5/6 : ℂ) • (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0)
      + (-(1/6) : ℂ) • (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) := by
  simp only [boostAvg, boostAvgZ, boostAvgX, boostAvgY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [boostPairZ_ubar1 2 (by norm_num),
    boostPairZ_ubar1 3 (by norm_num),
    boostPairZ_ubar1 4 (by norm_num),
    boostPairX_ubar1 2 (by norm_num),
    boostPairX_ubar1 3 (by norm_num),
    boostPairX_ubar1 4 (by norm_num),
    boostPairY_ubar1 2 (by norm_num),
    boostPairY_ubar1 3 (by norm_num),
    boostPairY_ubar1 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `boostAvg` on the σ-contracted fermion pair `ubar2`. -/
lemma boostAvg_ubar2 :
    boostAvg (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0) =
      (5/6 : ℂ) • (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0)
      + (Complex.I/6) • (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) := by
  simp only [boostAvg, boostAvgZ, boostAvgX, boostAvgY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [boostPairZ_ubar2 2 (by norm_num),
    boostPairZ_ubar2 3 (by norm_num),
    boostPairZ_ubar2 4 (by norm_num),
    boostPairX_ubar2 2 (by norm_num),
    boostPairX_ubar2 3 (by norm_num),
    boostPairX_ubar2 4 (by norm_num),
    boostPairY_ubar2 2 (by norm_num),
    boostPairY_ubar2 3 (by norm_num),
    boostPairY_ubar2 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `boostAvg` on the σ-contracted fermion pair `ubar3`. -/
lemma boostAvg_ubar3 :
    boostAvg (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) =
      (5/6 : ℂ) • (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1)
      + (-(1/6) : ℂ) • (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) := by
  simp only [boostAvg, boostAvgZ, boostAvgX, boostAvgY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [boostPairZ_ubar3 2 (by norm_num),
    boostPairZ_ubar3 3 (by norm_num),
    boostPairZ_ubar3 4 (by norm_num),
    boostPairX_ubar3 2 (by norm_num),
    boostPairX_ubar3 3 (by norm_num),
    boostPairX_ubar3 4 (by norm_num),
    boostPairY_ubar3 2 (by norm_num),
    boostPairY_ubar3 3 (by norm_num),
    boostPairY_ubar3 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

end JetAlgebra

end LeptonGaugeSector
