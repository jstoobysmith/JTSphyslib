/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.IsInvariant
/-!
# The boosts along the coordinate axes

## i. Overview

The one-parameter boosts `boostZel t`, `boostXel t`, `boostYel t` along the three coordinate
axes, their Lorentz matrices, their inverses, and the weighted averages `boostAvgZ`, `boostAvgX`,
`boostAvgY` over finitely many of them.

## ii. What they are for

These are the boosts the boost-weight grading of `Grading/BoostWeight` is defined by: an element
has boost weight `k` along an axis when the corresponding one-parameter family acts on it by
`t ^ k`. The three averages are fixed rational combinations of the identity and the boosts at
`t = 2, 3, 4` paired with their inverses; `Grading/BoostWeight` shows that each acts on an
element of boost weight `k` by an explicit scalar, which is one at `k = 0` and zero at
`k = ± 2, ± 4, ± 6`, so that on the covariant subalgebra in mass weight eight they are the
projections onto boost weight zero.

Being non-compact, the boosts admit no invariant average, which is why the weights have to be
chosen by hand rather than obtained by integration.

## iii. Key results

- `JetAlgebra.boostZel`, `JetAlgebra.boostXel`, `JetAlgebra.boostYel` : the one-parameter boosts.
- `JetAlgebra.toLorentzGroup_boostZel` and its two companions : their Lorentz matrices.
- `JetAlgebra.boostAvgZ`, `JetAlgebra.boostAvgX`, `JetAlgebra.boostAvgY` : the weighted averages.

## iv. Table of contents

- A. The boosts along the three axes
- B. Their Lorentz matrices
- C. Their inverses
- D. The weighted boost averages

-/

@[expose] public section

set_option maxHeartbeats 1000000

namespace LeptonGaugeSector
open TensorProduct StandardModel

namespace JetAlgebra

open scoped minkowskiMatrix PauliMatrix
open Matrix MatrixGroups

/-!

## A. The boosts along the three axes

The one-parameter families of boosts `diag(t, t⁻¹)` (along `z`) and their conjugates along `x`
and `y`.

-/


/-- The lift `diag(t, t⁻¹)` of the boost along the `z`-axis with rapidity
  `2 log t`. -/
noncomputable def boostZel (t : ℝ) (ht : t ≠ 0) : SL(2,ℂ) :=
  ⟨!![(t : ℂ), 0; 0, (t : ℂ)⁻¹], by
    have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
    rw [Matrix.det_fin_two_of]
    simp [mul_inv_cancel₀ htc]⟩

/-- The lift of the boost along the `x`-axis with rapidity `2 log t`. -/
noncomputable def boostXel (t : ℝ) (ht : t ≠ 0) : SL(2,ℂ) :=
  ⟨!![((t : ℂ) + (t : ℂ)⁻¹)/2, ((t : ℂ) - (t : ℂ)⁻¹)/2;
      ((t : ℂ) - (t : ℂ)⁻¹)/2, ((t : ℂ) + (t : ℂ)⁻¹)/2], by
    have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
    rw [Matrix.det_fin_two_of]
    field_simp
    ring⟩

/-- The lift of the boost along the `y`-axis with rapidity `2 log t`. -/
noncomputable def boostYel (t : ℝ) (ht : t ≠ 0) : SL(2,ℂ) :=
  ⟨!![((t : ℂ) + (t : ℂ)⁻¹)/2, -Complex.I * ((t : ℂ) - (t : ℂ)⁻¹)/2;
      Complex.I * ((t : ℂ) - (t : ℂ)⁻¹)/2, ((t : ℂ) + (t : ℂ)⁻¹)/2], by
    have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
    have h2 : -Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2 *
        (Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2) =
        ((t : ℂ) - (t : ℂ)⁻¹) / 2 * (((t : ℂ) - (t : ℂ)⁻¹) / 2) := by
      have hI : -Complex.I * Complex.I = 1 := by
        rw [neg_mul, Complex.I_mul_I, neg_neg]
      calc -Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2 *
            (Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2)
          = (-Complex.I * Complex.I) *
              (((t : ℂ) - (t : ℂ)⁻¹) / 2 * (((t : ℂ) - (t : ℂ)⁻¹) / 2)) := by
            ring
        _ = ((t : ℂ) - (t : ℂ)⁻¹) / 2 * (((t : ℂ) - (t : ℂ)⁻¹) / 2) := by
            rw [hI, one_mul]
    rw [Matrix.det_fin_two_of, h2]
    field_simp
    ring⟩

/-!

## B. Their Lorentz matrices

-/

/-- The Lorentz matrix of `boostZel t`: `ch = (t² + t⁻²)/2` on the time-time
  and `zz` entries, `-sh = -(t² - t⁻²)/2` on the mixed entries. -/
noncomputable def boostMatZ (t : ℝ) : (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → ℝ
  | Sum.inl _, Sum.inl _ => (t^2 + (t⁻¹)^2)/2
  | Sum.inl _, Sum.inr 2 => -((t^2 - (t⁻¹)^2)/2)
  | Sum.inr 2, Sum.inl _ => -((t^2 - (t⁻¹)^2)/2)
  | Sum.inr 0, Sum.inr 0 => 1
  | Sum.inr 1, Sum.inr 1 => 1
  | Sum.inr 2, Sum.inr 2 => (t^2 + (t⁻¹)^2)/2
  | _, _ => 0

/-- The Lorentz matrix of `boostXel t`. -/
noncomputable def boostMatX (t : ℝ) : (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → ℝ
  | Sum.inl _, Sum.inl _ => (t^2 + (t⁻¹)^2)/2
  | Sum.inl _, Sum.inr 0 => -((t^2 - (t⁻¹)^2)/2)
  | Sum.inr 0, Sum.inl _ => -((t^2 - (t⁻¹)^2)/2)
  | Sum.inr 0, Sum.inr 0 => (t^2 + (t⁻¹)^2)/2
  | Sum.inr 1, Sum.inr 1 => 1
  | Sum.inr 2, Sum.inr 2 => 1
  | _, _ => 0

/-- The Lorentz matrix of `boostYel t`. -/
noncomputable def boostMatY (t : ℝ) : (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → ℝ
  | Sum.inl _, Sum.inl _ => (t^2 + (t⁻¹)^2)/2
  | Sum.inl _, Sum.inr 1 => -((t^2 - (t⁻¹)^2)/2)
  | Sum.inr 1, Sum.inl _ => -((t^2 - (t⁻¹)^2)/2)
  | Sum.inr 0, Sum.inr 0 => 1
  | Sum.inr 1, Sum.inr 1 => (t^2 + (t⁻¹)^2)/2
  | Sum.inr 2, Sum.inr 2 => 1
  | _, _ => 0

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- The Lorentz matrix of the parametric `z`-boost. -/
lemma toLorentzGroup_boostZel (t : ℝ) (ht : t ≠ 0) (a b : Fin 1 ⊕ Fin 3) :
    (Lorentz.SL2C.toLorentzGroup (boostZel t ht)).1 a b = boostMatZ t a b := by
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  refine Complex.ofReal_injective ?_
  rw [Lorentz.SL2C.toLorentzGroup_eq_trace]
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    · try simp [boostZel, boostMatZ, PauliMatrix.pauliSelfAdjoint',
        PauliMatrix.pauliMatrix, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose, Matrix.diag, Complex.conj_ofNat,
        Complex.conj_ofReal, Complex.conj_I, Complex.I_sq]
      try simp [Matrix.vecMul, Matrix.vecHead, Matrix.vecTail]
      try push_cast
      try field_simp
      try ring_nf
      try norm_num [Complex.I_sq, Complex.conj_ofNat]
      try ring

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- The Lorentz matrix of the parametric `x`-boost. -/
lemma toLorentzGroup_boostXel (t : ℝ) (ht : t ≠ 0) (a b : Fin 1 ⊕ Fin 3) :
    (Lorentz.SL2C.toLorentzGroup (boostXel t ht)).1 a b = boostMatX t a b := by
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  refine Complex.ofReal_injective ?_
  rw [Lorentz.SL2C.toLorentzGroup_eq_trace]
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    · try simp [boostXel, boostMatX, PauliMatrix.pauliSelfAdjoint',
        PauliMatrix.pauliMatrix, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose, Matrix.diag, Complex.conj_ofNat,
        Complex.conj_ofReal, Complex.conj_I, Complex.I_sq]
      try simp [Matrix.vecMul, Matrix.vecHead, Matrix.vecTail]
      try push_cast
      try field_simp
      try ring_nf
      try norm_num [Complex.I_sq, Complex.conj_ofNat]
      try ring

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- The Lorentz matrix of the parametric `y`-boost. -/
lemma toLorentzGroup_boostYel (t : ℝ) (ht : t ≠ 0) (a b : Fin 1 ⊕ Fin 3) :
    (Lorentz.SL2C.toLorentzGroup (boostYel t ht)).1 a b = boostMatY t a b := by
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  refine Complex.ofReal_injective ?_
  rw [Lorentz.SL2C.toLorentzGroup_eq_trace]
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    · try simp [boostYel, boostMatY, PauliMatrix.pauliSelfAdjoint',
        PauliMatrix.pauliMatrix, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose, Matrix.diag, Complex.conj_ofNat,
        Complex.conj_ofReal, Complex.conj_I, Complex.I_sq]
      try simp [Matrix.vecMul, Matrix.vecHead, Matrix.vecTail]
      try push_cast
      try field_simp
      try ring_nf
      try norm_num [Complex.I_sq, Complex.conj_ofNat]
      try ring


/-!

## C. Their inverses

-/

/-- The inverse of the parametric `z`-boost is the boost at the inverse
  parameter. -/
lemma boostZel_inv (t : ℝ) (ht : t ≠ 0) :
    (boostZel t ht)⁻¹ = boostZel t⁻¹ (inv_ne_zero ht) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  fin_cases i <;> fin_cases j <;>
    simp [boostZel, Complex.ofReal_inv, inv_inv]

/-- The inverse of the parametric `x`-boost is the boost at the inverse
  parameter. -/
lemma boostXel_inv (t : ℝ) (ht : t ≠ 0) :
    (boostXel t ht)⁻¹ = boostXel t⁻¹ (inv_ne_zero ht) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  fin_cases i <;> fin_cases j <;>
    · simp [boostXel, Complex.ofReal_inv, inv_inv]
      try ring

/-- The inverse of the parametric `y`-boost is the boost at the inverse
  parameter. -/
lemma boostYel_inv (t : ℝ) (ht : t ≠ 0) :
    (boostYel t ht)⁻¹ = boostYel t⁻¹ (inv_ne_zero ht) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  fin_cases i <;> fin_cases j <;>
    · simp [boostYel, Complex.ofReal_inv, inv_inv]
      try ring


/-- The inverse of the parametric `z`-boost, entrywise, with real entries. -/
lemma boostZel_inv_coe (t : ℝ) (ht : t ≠ 0) :
    ((boostZel t ht)⁻¹ : SL(2,ℂ)).1 =
      !![(((t⁻¹ : ℝ)) : ℂ), 0; 0, ((t : ℝ) : ℂ)] := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boostZel]

/-- The inverse of the parametric `x`-boost, entrywise. -/
lemma boostXel_inv_coe (t : ℝ) (ht : t ≠ 0) :
    ((boostXel t ht)⁻¹ : SL(2,ℂ)).1 =
      !![((t : ℂ) + (t : ℂ)⁻¹)/2, -(((t : ℂ) - (t : ℂ)⁻¹)/2);
         -(((t : ℂ) - (t : ℂ)⁻¹)/2), ((t : ℂ) + (t : ℂ)⁻¹)/2] := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boostXel]

/-- The inverse of the parametric `y`-boost, entrywise. -/
lemma boostYel_inv_coe (t : ℝ) (ht : t ≠ 0) :
    ((boostYel t ht)⁻¹ : SL(2,ℂ)).1 =
      !![((t : ℂ) + (t : ℂ)⁻¹)/2, Complex.I * ((t : ℂ) - (t : ℂ)⁻¹)/2;
         -(Complex.I * ((t : ℂ) - (t : ℂ)⁻¹)/2), ((t : ℂ) + (t : ℂ)⁻¹)/2] := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;> · simp [boostYel]; try ring

/-!

## D. The weighted boost averages

Each average is the identity together with the paired boosts at `t = 2, 3, 4`, with weights
chosen so that the operator fixes the invariants and annihilates the boost weights
`± 2, ± 4, ± 6`. See `Grading/BoostWeight` for the scalar it acts by, `boostAvgZWeight`.

-/


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

end JetAlgebra

end LeptonGaugeSector

end
