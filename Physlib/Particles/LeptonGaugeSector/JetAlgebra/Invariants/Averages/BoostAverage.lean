/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.Invariants.Averages.RotationPiBoostAverage
/-!
# The average over the boosts

The average over the boosts of `Subgroups/AxisBoosts`. Their action on the weight-eight
monomials is not tabulated: the tactic `boostAvg_calculator` below computes it on demand from
the Lorentz transformation laws of `LorentzAction` and the boost matrices of `AxisBoosts`.

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

/-!

## The boost-average calculator

The values of `boostAvg` on the weight-eight monomials below are not separate facts: they are
what the Lorentz transformation laws of `LorentzAction` give when the boost matrices of
`Subgroups/AxisBoosts` are substituted and the index sums expanded. The tactic
`boostAvg_calculator` performs exactly that, so each of the lemmas is proved by a single
invocation and nothing has to be tabulated in advance.

The only step that is not mechanical is fixing a basis: a field strength is antisymmetric, so
the expansion produces both `F_{ab}` and `F_{ba}` and the two have to be identified. The three
lemmas below orient the spatial index pairs; `fieldStrengthDeriv_inr_inl` orients the mixed
ones and `fieldStrengthDeriv_self` kills the diagonal. All four are oriented, so they terminate.

-/

/-- Orientation of the `yx` field-strength component. -/
lemma fieldStrengthDeriv_yx (s : Multiset (Fin 1 ⊕ Fin 3)) :
    fieldStrengthDeriv s (Sum.inr 1) (Sum.inr 0) =
      -fieldStrengthDeriv s (Sum.inr 0) (Sum.inr 1) := fieldStrengthDeriv_antisymm ..

/-- Orientation of the `zx` field-strength component. -/
lemma fieldStrengthDeriv_zx (s : Multiset (Fin 1 ⊕ Fin 3)) :
    fieldStrengthDeriv s (Sum.inr 2) (Sum.inr 0) =
      -fieldStrengthDeriv s (Sum.inr 0) (Sum.inr 2) := fieldStrengthDeriv_antisymm ..

/-- Orientation of the `zy` field-strength component. -/
lemma fieldStrengthDeriv_zy (s : Multiset (Fin 1 ⊕ Fin 3)) :
    fieldStrengthDeriv s (Sum.inr 2) (Sum.inr 1) =
      -fieldStrengthDeriv s (Sum.inr 1) (Sum.inr 2) := fieldStrengthDeriv_antisymm ..

/-- Compute the boost average on an explicit weight-eight monomial, directly from the Lorentz
  transformation laws: unfold the average, push the representation through the products, expand
  each generator into its index sum, substitute the boost matrices, orient the basis, and
  compare coefficients. -/
scoped syntax "boostAvg_calculator" : tactic

scoped macro_rules
  | `(tactic| boostAvg_calculator) =>
    `(tactic|
      (simp only [boostAvg, boostAvgZ, boostAvgX, boostAvgY,
          LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
          repLorentzGroup_apply_mul, repLorentzGroup_apply_one,
          repLorentzGroup_fieldStrengthDeriv_nil,
          repLorentzGroup_fieldStrengthDeriv_singleton,
          repLorentzGroup_fieldStrengthDeriv_pair,
          repLorentzGroup_Dψ_nil, repLorentzGroup_Dψ_singleton,
          repLorentzGroup_Dbarψ_nil, repLorentzGroup_Dbarψ_singleton,
          repLorentzGroup_Dbarψ_nil_mul_Dψ_nil, repLorentzGroup_Dψ_nil_mul_Dbarψ_nil,
          repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
          repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
          map_add, map_sub, inv_inv,
          boostZel_coe, boostXel_coe, boostYel_coe,
          boostZel_inv_coe, boostXel_inv_coe, boostYel_inv_coe,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
          Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
          Complex.star_def, map_mul, map_div₀, map_inv₀, map_ofNat,
          map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
          star_zero, star_one, neg_neg, neg_zero, Complex.ofReal_neg,
          toLorentzGroup_boostZel, toLorentzGroup_boostZel_inv,
          toLorentzGroup_boostXel, toLorentzGroup_boostXel_inv,
          toLorentzGroup_boostYel, toLorentzGroup_boostYel_inv,
          Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_two, Fin.sum_univ_three,
          boostMatZ, boostMatX, boostMatY,
          fieldStrengthDeriv_self, fieldStrengthDeriv_inr_inl,
          fieldStrengthDeriv_yx, fieldStrengthDeriv_zx, fieldStrengthDeriv_zy,
          fieldStrengthDeriv_mul_comm, fieldStrengthDeriv_pair_swap,
          mul_zero, zero_mul, mul_one, one_mul,
          Complex.ofReal_zero, Complex.ofReal_one,
          zero_smul, smul_zero, add_zero, zero_add, neg_mul, mul_neg, smul_neg, neg_smul,
          add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul]
       push_cast
       match_scalars <;>
         (push_cast
          first
          | (norm_num; done)
          | (ring_nf; simp only [Complex.I_sq]; ring_nf; done)
          | (ring_nf; simp only [Complex.I_sq]; norm_num; done)
          | (field_simp; ring))))

/-- The operator `boostAvg` fixes every Lorentz-invariant vector: each boost term
  fixes it and the weights sum to one. -/
lemma boostAvg_apply_of_invariant {y : JetAlgebra}
    (hinv : ∀ Λ : SL(2,ℂ), repLorentzGroup Λ y = y) : boostAvg y = y := by
  simp only [boostAvg, boostAvgZ, boostAvgX, boostAvgY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply, hinv]
  match_scalars
  norm_num

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
  boostAvg_calculator

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
  boostAvg_calculator

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
  boostAvg_calculator

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
  boostAvg_calculator

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
  boostAvg_calculator

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
  boostAvg_calculator

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
  boostAvg_calculator

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
  boostAvg_calculator

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
  boostAvg_calculator

/-- The boost average `boostAvg` on `∂∂F01` with derivative indices `(0, 1)`. -/
lemma boostAvg_dd01_F01 :
    boostAvg (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) =
      (1/3 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) := by
  boostAvg_calculator

/-- The boost average `boostAvg` on `∂∂F23` with derivative indices `(0, 1)`. -/
lemma boostAvg_dd01_F23 :
    boostAvg (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) =
      (1/3 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) := by
  boostAvg_calculator

/-- The boost average `boostAvg` on `∂∂F02` with derivative indices `(0, 2)`. -/
lemma boostAvg_dd02_F02 :
    boostAvg (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) =
      (1/3 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) := by
  boostAvg_calculator

/-- The boost average `boostAvg` on `∂∂F13` with derivative indices `(0, 2)`. -/
lemma boostAvg_dd02_F13 :
    boostAvg (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) =
      (1/3 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) := by
  boostAvg_calculator

/-- The boost average `boostAvg` on `∂∂F03` with derivative indices `(0, 3)`. -/
lemma boostAvg_dd03_F03 :
    boostAvg (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) =
      (1/3 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) := by
  boostAvg_calculator

/-- The boost average `boostAvg` on `∂∂F12` with derivative indices `(0, 3)`. -/
lemma boostAvg_dd03_F12 :
    boostAvg (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) =
      (1/3 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) := by
  boostAvg_calculator

/-- The boost average `boostAvg` on `∂∂F03` with derivative indices `(1, 2)`. -/
lemma boostAvg_dd12_F03 :
    boostAvg (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) := by
  boostAvg_calculator

/-- The boost average `boostAvg` on `∂∂F12` with derivative indices `(1, 2)`. -/
lemma boostAvg_dd12_F12 :
    boostAvg (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) := by
  boostAvg_calculator

/-- The boost average `boostAvg` on `∂∂F02` with derivative indices `(1, 3)`. -/
lemma boostAvg_dd13_F02 :
    boostAvg (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) := by
  boostAvg_calculator

/-- The boost average `boostAvg` on `∂∂F13` with derivative indices `(1, 3)`. -/
lemma boostAvg_dd13_F13 :
    boostAvg (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) := by
  boostAvg_calculator

/-- The boost average `boostAvg` on `∂∂F01` with derivative indices `(2, 3)`. -/
lemma boostAvg_dd23_F01 :
    boostAvg (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) := by
  boostAvg_calculator

/-- The boost average `boostAvg` on `∂∂F23` with derivative indices `(2, 3)`. -/
lemma boostAvg_dd23_F23 :
    boostAvg (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) := by
  boostAvg_calculator

/-- The boost average `boostAvg` on the σ-contracted fermion pair `u0`. -/
lemma boostAvg_u0 :
    boostAvg (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) =
      (1/2 : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1)
      + (-(1/6) : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0)
      + (-(Complex.I/6)) • (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0)
      + (-(1/6) : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) := by
  boostAvg_calculator

/-- The boost average `boostAvg` on the σ-contracted fermion pair `u1`. -/
lemma boostAvg_u1 :
    boostAvg (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0) =
      (5/6 : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0)
      + (-(1/6) : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) := by
  boostAvg_calculator

/-- The boost average `boostAvg` on the σ-contracted fermion pair `u2`. -/
lemma boostAvg_u2 :
    boostAvg (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0) =
      (5/6 : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0)
      + (Complex.I/6) • (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) := by
  boostAvg_calculator

/-- The boost average `boostAvg` on the σ-contracted fermion pair `u3`. -/
lemma boostAvg_u3 :
    boostAvg (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) =
      (5/6 : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1)
      + (-(1/6) : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) := by
  boostAvg_calculator

/-- The boost average `boostAvg` on the σ-contracted fermion pair `ubar0`. -/
lemma boostAvg_ubar0 :
    boostAvg (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) =
      (1/2 : ℂ) • (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1)
      + (-(1/6) : ℂ) • (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0)
      + (-(Complex.I/6)) • (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0)
      + (-(1/6) : ℂ) • (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) := by
  boostAvg_calculator

/-- The boost average `boostAvg` on the σ-contracted fermion pair `ubar1`. -/
lemma boostAvg_ubar1 :
    boostAvg (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0) =
      (5/6 : ℂ) • (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0)
      + (-(1/6) : ℂ) • (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) := by
  boostAvg_calculator

/-- The boost average `boostAvg` on the σ-contracted fermion pair `ubar2`. -/
lemma boostAvg_ubar2 :
    boostAvg (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0) =
      (5/6 : ℂ) • (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0)
      + (Complex.I/6) • (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) := by
  boostAvg_calculator

/-- The boost average `boostAvg` on the σ-contracted fermion pair `ubar3`. -/
lemma boostAvg_ubar3 :
    boostAvg (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) =
      (5/6 : ℂ) • (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1)
      + (-(1/6) : ℂ) • (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) := by
  boostAvg_calculator

end JetAlgebra

end LeptonGaugeSector
