/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.SL2C.AxisRotations
public import Physlib.Relativity.PauliMatrices.Basic
public import Physlib.Relativity.MinkowskiMatrix
/-!
# The boosts along the coordinate axes

## i. Overview

The one-parameter boosts `boostZel t`, `boostXel t`, `boostYel t` along the three coordinate
axes as elements of `SL(2,ℂ)`, their Lorentz matrices, their inverses, the uniform
parametrisation `boostAxis`, and the rotations conjugating the `z`-boost into the `x`- and
`y`-boosts.

## ii. What they are for

These are the boosts boost-weight gradings are defined by: an element of a representation has
boost weight `k` along an axis when the corresponding one-parameter family acts on it by
`t ^ k`. The conjugations `boostXel_eq_conj`, `boostYel_eq_conj` let facts proved for the
`z`-axis be transported to the other two.

## iii. Key results

- `Lorentz.boostZel`, `Lorentz.boostXel`, `Lorentz.boostYel` : the one-parameter boosts.
- `Lorentz.toLorentzGroup_boostZel` and its two companions : their Lorentz matrices.
- `Lorentz.boostAxis` : the boost along the `i`-th axis.
- `Lorentz.exists_conj_boostAxis` : every axis boost is a rotation of the `z`-boost.

## iv. Table of contents

- A. The boosts along the three axes
- B. Their Lorentz matrices
- C. Their inverses
- D. The uniform parametrisation and the conjugations

-/

@[expose] public section

open scoped minkowskiMatrix PauliMatrix
open Matrix MatrixGroups

namespace Lorentz.SL2C

/-- The `SL(2,ℂ)` lift of the boost along spatial axis `i`, with `0 = x`, `1 = y`, and
`2 = z`. The parameter `t` is multiplicative, and for `t > 0` the rapidity is `2 * log t`. -/
noncomputable def boostAxis : Fin 3 → (t : ℝ) → t ≠ 0 → SL(2,ℂ)
  | 0, t, ht =>
      ⟨!![((t : ℂ) + (t : ℂ)⁻¹) / 2, ((t : ℂ) - (t : ℂ)⁻¹) / 2;
          ((t : ℂ) - (t : ℂ)⁻¹) / 2, ((t : ℂ) + (t : ℂ)⁻¹) / 2], by
        have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
        rw [Matrix.det_fin_two_of]
        field_simp
        ring⟩
  | 1, t, ht =>
      ⟨!![((t : ℂ) + (t : ℂ)⁻¹) / 2, -Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2;
          Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2, ((t : ℂ) + (t : ℂ)⁻¹) / 2], by
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
  | 2, t, ht =>
      ⟨!![(t : ℂ), 0; 0, (t : ℂ)⁻¹], by
        have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
        rw [Matrix.det_fin_two_of]
        simp [mul_inv_cancel₀ htc]⟩

/-- The matrix entries of the `SL(2,ℂ)` boost lift along the `x`-axis. -/
@[simp] lemma boostAxis_zero_apply (t : ℝ) (ht : t ≠ 0) (j k : Fin 2) :
    (boostAxis 0 t ht).1 j k =
      (!![((t : ℂ) + (t : ℂ)⁻¹) / 2, ((t : ℂ) - (t : ℂ)⁻¹) / 2;
        ((t : ℂ) - (t : ℂ)⁻¹) / 2, ((t : ℂ) + (t : ℂ)⁻¹) / 2]) j k := rfl

/-- The matrix entries of the `SL(2,ℂ)` boost lift along the `y`-axis. -/
@[simp] lemma boostAxis_one_apply (t : ℝ) (ht : t ≠ 0) (j k : Fin 2) :
    (boostAxis 1 t ht).1 j k =
      (!![((t : ℂ) + (t : ℂ)⁻¹) / 2,
        -Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2;
        Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2,
        ((t : ℂ) + (t : ℂ)⁻¹) / 2]) j k := rfl

/-- The matrix entries of the diagonal `SL(2,ℂ)` boost lift along the `z`-axis. -/
@[simp] lemma boostAxis_two_apply (t : ℝ) (ht : t ≠ 0) (j k : Fin 2) :
    (boostAxis 2 t ht).1 j k = (!![(t : ℂ), 0; 0, (t : ℂ)⁻¹]) j k := rfl

/-- Inverting an axis boost replaces its multiplicative parameter `t` by `t⁻¹`. -/
lemma boostAxis_inv (i : Fin 3) (t : ℝ) (ht : t ≠ 0) :
    (boostAxis i t ht)⁻¹ = boostAxis i t⁻¹ (inv_ne_zero ht) := by
  fin_cases i
  · ext j k
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    fin_cases j <;> fin_cases k <;>
      simp [boostAxis, Complex.ofReal_inv, inv_inv] <;>
      ring
  · ext j k
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    fin_cases j <;> fin_cases k <;>
      simp [boostAxis, Complex.ofReal_inv, inv_inv] <;>
      ring
  · ext j k
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    fin_cases j <;> fin_cases k <;>
      simp [boostAxis, Complex.ofReal_inv, inv_inv]

/-- The matrix underlying an axis-boost lift is Hermitian. -/
lemma boostAxis_conjTranspose (i : Fin 3) (t : ℝ) (ht : t ≠ 0) :
    (boostAxis i t ht).1ᴴ = (boostAxis i t ht).1 := by
  fin_cases i <;> ext j k <;> fin_cases j <;> fin_cases k <;> simp [boostAxis]

/-- Every axis boost is obtained by conjugating the `z`-axis boost by `rotationZToAxis`. -/
lemma boostAxis_eq_conj (i : Fin 3) (t : ℝ) (ht : t ≠ 0) :
    boostAxis i t ht =
      rotationZToAxis i * boostAxis 2 t ht * (rotationZToAxis i)⁻¹ := by
  fin_cases i
  · refine Subtype.ext ?_
    change !![((t : ℂ) + (t : ℂ)⁻¹) / 2, ((t : ℂ) - (t : ℂ)⁻¹) / 2;
        ((t : ℂ) - (t : ℂ)⁻¹) / 2, ((t : ℂ) + (t : ℂ)⁻¹) / 2] =
      (rotationZToAxis 0).1 * !![(t : ℂ), 0; 0, (t : ℂ)⁻¹] *
        ((rotationZToAxis 0)⁻¹).1
    rw [rotationZToAxis_zero_mul_diagonal_mul_inv]
  · refine Subtype.ext ?_
    change !![((t : ℂ) + (t : ℂ)⁻¹) / 2,
        -Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2;
        Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2,
        ((t : ℂ) + (t : ℂ)⁻¹) / 2] =
      (rotationZToAxis 1).1 * !![(t : ℂ), 0; 0, (t : ℂ)⁻¹] *
        ((rotationZToAxis 1)⁻¹).1
    rw [rotationZToAxis_one_mul_diagonal_mul_inv]
  · refine Subtype.ext ?_
    change !![(t : ℂ), 0; 0, (t : ℂ)⁻¹] =
      (rotationZToAxis 2).1 * !![(t : ℂ), 0; 0, (t : ℂ)⁻¹] *
        ((rotationZToAxis 2)⁻¹).1
    rw [rotationZToAxis_two_mul_diagonal_mul_inv]

/-- Every coordinate-axis boost is conjugate to the `z`-axis boost. -/
lemma exists_conj_boostAxis (i : Fin 3) :
    ∃ R : SL(2,ℂ), ∀ (t : ℝ) (ht : t ≠ 0),
      boostAxis i t ht = R * boostAxis 2 t ht * R⁻¹ := by
  exact ⟨rotationZToAxis i, fun t ht => boostAxis_eq_conj i t ht⟩

end Lorentz.SL2C

namespace LorentzGroup

/-- The Lorentz transformation induced by the multiplicatively parameterized `SL(2,ℂ)` boost
along spatial axis `i`. -/
noncomputable def boostAxis (i : Fin 3) (t : ℝ) (ht : t ≠ 0) : LorentzGroup 3 :=
  Lorentz.SL2C.toLorentzGroup (Lorentz.SL2C.boostAxis i t ht)

/-- The entries of an axis boost in the Lorentz group. -/
lemma boostAxis_apply (i : Fin 3) (t : ℝ) (ht : t ≠ 0) (a b : Fin 1 ⊕ Fin 3) :
    (boostAxis i t ht).1 a b =
      if a = Sum.inl 0 ∧ b = Sum.inl 0 then (t ^ 2 + (t⁻¹) ^ 2) / 2
      else if a = Sum.inl 0 ∧ b = Sum.inr i then -((t ^ 2 - (t⁻¹) ^ 2) / 2)
      else if a = Sum.inr i ∧ b = Sum.inl 0 then -((t ^ 2 - (t⁻¹) ^ 2) / 2)
      else if a = Sum.inr i ∧ b = Sum.inr i then (t ^ 2 + (t⁻¹) ^ 2) / 2
      else if a = b then 1 else 0 := by
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  refine Complex.ofReal_injective ?_
  rw [boostAxis, Lorentz.SL2C.toLorentzGroup_eq_trace,
    PauliMatrix.trace_pauliSelfAdjoint'_mul_apply, Lorentz.SL2C.boostAxis_conjTranspose]
  fin_cases i
  all_goals
    rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
      simp [Lorentz.SL2C.boostAxis, PauliMatrix.pauliSelfAdjoint', PauliMatrix.pauliMatrix,
        Matrix.mul_apply, Fin.sum_univ_two] <;>
      field_simp <;>
      ring_nf
  all_goals simp only [Complex.I_sq, Complex.I_pow_four]
  all_goals ring

end LorentzGroup

set_option maxHeartbeats 1000000

namespace Lorentz

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

## D. The uniform parametrisation and the conjugations

The three axis boosts are conjugate: a rotation by `π/2` carries the `z`-boost to the `x`- and
`y`-boosts, so facts about the `z`-boost transport to the other axes.

-/

/-- The boost along the `i`-th spatial axis. -/
noncomputable def boostAxis : Fin 3 → (t : ℝ) → t ≠ 0 → SL(2,ℂ)
  | 0, t, ht => boostXel t ht
  | 1, t, ht => boostYel t ht
  | 2, t, ht => boostZel t ht

@[simp] lemma boostAxis_zero (t : ℝ) (ht : t ≠ 0) : boostAxis 0 t ht = boostXel t ht := rfl
@[simp] lemma boostAxis_one (t : ℝ) (ht : t ≠ 0) : boostAxis 1 t ht = boostYel t ht := rfl
@[simp] lemma boostAxis_two (t : ℝ) (ht : t ≠ 0) : boostAxis 2 t ht = boostZel t ht := rfl

lemma boostAxis_inv (i : Fin 3) (t : ℝ) (ht : t ≠ 0) :
    (boostAxis i t ht)⁻¹ = boostAxis i t⁻¹ (inv_ne_zero ht) := by
  fin_cases i
  · exact boostXel_inv t ht
  · exact boostYel_inv t ht
  · exact boostZel_inv t ht

private lemma sqrtTwo_sq : (((Real.sqrt 2 : ℝ) : ℂ)) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

private lemma sqrtTwo_ne_zero : (((Real.sqrt 2 : ℝ) : ℂ)) ≠ 0 := by
  simp []

private lemma sqrtTwo_inv_mul :
    ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹) * ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹) = 2⁻¹ := by
  rw [← mul_inv, ← sq, sqrtTwo_sq]

/-- The rotation by `π/2` about the `y`-axis, carrying the `z`-boost to the `x`-boost. -/
noncomputable def rotZX : SL(2,ℂ) :=
  ⟨(((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • !![1, -1; 1, 1], by
    rw [Matrix.det_smul, Matrix.det_fin_two_of, Fintype.card_fin, inv_pow, sqrtTwo_sq]
    norm_num⟩

/-- The rotation by `π/2` about the `x`-axis, carrying the `z`-boost to the `y`-boost. -/
noncomputable def rotZY : SL(2,ℂ) :=
  ⟨(((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • !![1, Complex.I; Complex.I, 1], by
    rw [Matrix.det_smul, Matrix.det_fin_two_of, Fintype.card_fin, inv_pow, sqrtTwo_sq,
      Complex.I_mul_I]
    norm_num⟩

lemma boostXel_eq_conj (t : ℝ) (ht : t ≠ 0) :
    boostXel t ht = rotZX * boostZel t ht * rotZX⁻¹ := by
  have h0 := sqrtTwo_ne_zero
  have hc := sqrtTwo_inv_mul
  have htc : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [Matrix.SpecialLinearGroup.coe_mul, rotZX, boostZel, boostXel,
        Matrix.mul_apply, Fin.sum_univ_two]
      field_simp
      simp only [sqrtTwo_sq]
      try ring

lemma boostYel_eq_conj (t : ℝ) (ht : t ≠ 0) :
    boostYel t ht = rotZY * boostZel t ht * rotZY⁻¹ := by
  have h0 := sqrtTwo_ne_zero
  have hc := sqrtTwo_inv_mul
  have htc : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [Matrix.SpecialLinearGroup.coe_mul, rotZY, boostZel, boostYel,
        Matrix.mul_apply, Fin.sum_univ_two]
      field_simp
      simp only [sqrtTwo_sq, Complex.I_sq]
      try ring

/-- Every axis boost is a rotation of the `z`-boost. -/
lemma exists_conj_boostAxis (i : Fin 3) :
    ∃ R : SL(2,ℂ), ∀ (t : ℝ) (ht : t ≠ 0),
      boostAxis i t ht = R * boostAxis 2 t ht * R⁻¹ := by
  fin_cases i
  · exact ⟨rotZX, fun t ht => boostXel_eq_conj t ht⟩
  · exact ⟨rotZY, fun t ht => boostYel_eq_conj t ht⟩
  · exact ⟨1, fun t ht => by simp⟩

end Lorentz

end
