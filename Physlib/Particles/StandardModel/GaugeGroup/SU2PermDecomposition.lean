/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
/-!
# The `SU(2)` Weyl element and other test elements

## i. Overview

The Weyl reflection of `SU(2)`,

  `su2Perm = !![0, -1; 1, 0]`,

sends a doublet `(a, b)` to `(-b, a)`, exchanging the two isospin components and so
exchanging the isospin weights `+1` and `-1` that the third coordinate of a `GaugeWeight`
records. `gaugeSU2Perm` is its image in the gauge group.

`su2Perm` squares to `-1`, so it has order four in `SU(2)`, and its spectrum is contained in
the fourth roots of unity: `su2PermSign` is the character `k ↦ i ^ k` on `ZMod 4` attaching
the eigenvalue to each grade.

Two further families of elements serve as test elements for the gauge invariant
classifications: the half turns `su2Flip k = i σ_k` about the three isospin axes, and the
third of a turn `su2Cyc = (1 + i(σ₁ + σ₂ + σ₃))/2` about the diagonal axis.

## ii. Key results

- `su2Perm` : the `SU(2)` Weyl element `!![0, -1; 1, 0]`, and `gaugeSU2Perm` its image in
  the gauge group.
- `su2PermSign` : the character `k ↦ i ^ k` on `ZMod 4`, injective and multiplicative.
- `su2Flip`, `su2Cyc` : the half turns about the isospin axes and a third of a turn.

## iii. Table of contents

- A. The `SU(2)` Weyl element
- B. The sign character of `ZMod 4`
- C. Half turns and a third of a turn

-/

@[expose] public section

namespace StandardModel

open Matrix

/-!

## A. The `SU(2)` Weyl element

-/

/-- The `SU(2)` Weyl element `!![0, -1; 1, 0]`. On a doublet it sends `(a, b)` to `(-b, a)`,
  exchanging the two isospin components; it squares to `-1`, so it has order four in
  `SU(2)`. -/
noncomputable def su2Perm : specialUnitaryGroup (Fin 2) ℂ :=
  ⟨!![0, -1; 1, 0], by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff]
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, star_eq_conjTranspose,
          Matrix.conjTranspose_apply]
    · simp [Matrix.det_fin_two_of]⟩

lemma su2Perm_coe : (su2Perm : specialUnitaryGroup (Fin 2) ℂ).1 = !![0, -1; 1, 0] := rfl

/-- The inverse Weyl element is `!![0, 1; -1, 0]`. -/
lemma su2Perm_inv_coe :
    (su2Perm⁻¹ : specialUnitaryGroup (Fin 2) ℂ).1 = !![0, 1; -1, 0] := by
  rw [← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star, su2Perm_coe]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

/-- The Weyl element as a gauge transformation: trivial on colour and hypercharge. -/
noncomputable def gaugeSU2Perm : GaugeGroupI := ⟨1, su2Perm, 1⟩

/-!

## B. The sign character of `ZMod 4`

-/

/-- The fourth root of unity `i ^ k` attached to a grade `k : ZMod 4`: the eigenvalue of the
  Weyl element on the `k` piece of a decomposition. -/
noncomputable def su2PermSign (k : ZMod 4) : ℂ :=
  if k = 0 then 1 else if k = 1 then Complex.I else if k = 2 then -1 else -Complex.I

@[simp] lemma su2PermSign_zero : su2PermSign 0 = 1 := rfl

@[simp] lemma su2PermSign_one : su2PermSign 1 = Complex.I := rfl

@[simp] lemma su2PermSign_two : su2PermSign 2 = -1 := rfl

@[simp] lemma su2PermSign_three : su2PermSign 3 = -Complex.I := rfl

/-- The sign is a character: grades **add** under multiplication because the fourth roots of
  unity multiply. -/
lemma su2PermSign_add (k l : ZMod 4) :
    su2PermSign (k + l) = su2PermSign k * su2PermSign l := by
  have hcases : ∀ j : ZMod 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
  rcases hcases k with rfl | rfl | rfl | rfl <;> rcases hcases l with rfl | rfl | rfl | rfl <;>
    simp [show (1 + 1 : ZMod 4) = 2 from by decide,
      show (1 + 2 : ZMod 4) = 3 from by decide, show (1 + 3 : ZMod 4) = 0 from by decide,
      show (2 + 1 : ZMod 4) = 3 from by decide, show (2 + 2 : ZMod 4) = 0 from by decide,
      show (2 + 3 : ZMod 4) = 1 from by decide, show (3 + 1 : ZMod 4) = 0 from by decide,
      show (3 + 2 : ZMod 4) = 1 from by decide, show (3 + 3 : ZMod 4) = 2 from by decide,
      Complex.I_mul_I]

lemma su2PermSign_ne_zero (k : ZMod 4) : su2PermSign k ≠ 0 := by
  have hcases : ∀ j : ZMod 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
  rcases hcases k with rfl | rfl | rfl | rfl <;> simp

/-- The four fourth roots of unity are distinct, so the pieces of a decomposition sit in
  eigenspaces at distinct eigenvalues and are automatically independent. -/
lemma su2PermSign_injective : Function.Injective su2PermSign := by
  have hcases : ∀ j : ZMod 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
  intro k l hkl
  rcases hcases k with rfl | rfl | rfl | rfl <;> rcases hcases l with rfl | rfl | rfl | rfl <;>
    simp_all [Complex.ext_iff] <;> norm_num at hkl

/-!

## C. Half turns and a third of a turn

-/

/-- The matrix of the `k`-th isospin flip, the half turn `i σ_k` about the `k`-th isospin
  axis. It is unitary, and its determinant is `1` because `i ^ 2` cancels the determinant
  `-1` of a Pauli matrix. -/
noncomputable def su2FlipMatrix : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![0, Complex.I; Complex.I, 0]
  | 1 => !![0, 1; -1, 0]
  | 2 => !![Complex.I, 0; 0, -Complex.I]

/-- The conjugate transpose of the `k`-th isospin flip, which is its inverse and its
  negative, the Pauli matrices being self-adjoint. -/
noncomputable def su2FlipStarMatrix : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![0, -Complex.I; -Complex.I, 0]
  | 1 => !![0, -1; 1, 0]
  | 2 => !![-Complex.I, 0; 0, Complex.I]

/-- The `k`-th isospin flip as an element of `SU(2)`. -/
noncomputable def su2Flip (k : Fin 3) : specialUnitaryGroup (Fin 2) ℂ :=
  ⟨su2FlipMatrix k, by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff]
      fin_cases k <;> ext a b <;> fin_cases a <;> fin_cases b <;>
        simp [su2FlipMatrix, Matrix.mul_apply, Fin.sum_univ_two]
    · fin_cases k <;> simp [su2FlipMatrix, Matrix.det_fin_two_of]⟩

/-- The underlying matrix of an isospin flip. -/
lemma su2Flip_coe (k : Fin 3) : (su2Flip k).1 = su2FlipMatrix k := rfl

/-- The conjugate transpose of an isospin flip. -/
lemma star_su2FlipMatrix (k : Fin 3) :
    star (su2FlipMatrix k) = su2FlipStarMatrix k := by
  fin_cases k <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [su2FlipMatrix, su2FlipStarMatrix]

/-- The `SU(2)` element `(1 + i(σ₁ + σ₂ + σ₃))/2`, a third of a turn about the diagonal
  axis of the three Pauli directions. -/
noncomputable def su2Cyc : specialUnitaryGroup (Fin 2) ℂ :=
  ⟨!![(1 + Complex.I) / 2, (1 + Complex.I) / 2;
      (-1 + Complex.I) / 2, (1 - Complex.I) / 2], by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff]
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, star_eq_conjTranspose,
          Matrix.conjTranspose_apply, map_div₀, Complex.conj_I, map_ofNat] <;>
        ring_nf <;>
        simp [Complex.I_sq] <;>
        ring
    · simp [Matrix.det_fin_two, Complex.ext_iff]
      norm_num⟩

/-- The underlying matrix of the third of a turn. -/
lemma su2Cyc_coe :
    (su2Cyc : specialUnitaryGroup (Fin 2) ℂ).1
      = !![(1 + Complex.I) / 2, (1 + Complex.I) / 2;
          (-1 + Complex.I) / 2, (1 - Complex.I) / 2] := rfl

/-- The conjugate transpose of the third of a turn. -/
lemma star_su2Cyc_coe :
    star (su2Cyc : specialUnitaryGroup (Fin 2) ℂ).1
      = !![(1 - Complex.I) / 2, (-1 - Complex.I) / 2;
          (1 - Complex.I) / 2, (1 + Complex.I) / 2] := by
  rw [su2Cyc_coe]
  ext a b
  fin_cases a <;> fin_cases b <;> simp <;> ring

end StandardModel
