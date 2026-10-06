/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Mathematics.Groups.SpecialUnitary.LieAlgebra.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.RepresentationTheory.Intertwining
/-!

# The adjoint representation of `SU(n)`

## i. Overview

We define the adjont representation of `SU(n)` on its Lie algebra `su(n)` and its complexification.
The adjoint is defined by conjugation, `x ↦ g x g†`.

The contraction `adjointContr` of two real adjoint indices is the trace form `x ⊗ y ↦ tr (x y)` on
`su(n)`, which is real since `x` and `y` are hermitian, and invariant under the adjoint action by
the cyclicity of the trace. It is symmetric, and nondegenerate since `tr (x x†) = 0` forces
`x = 0` (B.1). The contraction `adjointℂContr` of two complex adjoint indices is its
complexification. On the underlying matrices it is the trace form `A ⊗ B ↦ tr (A B)`, and it is
again symmetric and nondegenerate (B.2).

## ii. Key results

- `SULieAlgebra.adjoint` : the adjoint representation on `su(n)`.
- `SULieAlgebra.adjoint_lie` : the adjoint representation preserves the bracket.
- `SULieAlgebra.adjointℂ` : the adjoint representation on the complexification.
- `SULieAlgebra.adjointℂ_lie` : the complex adjoint representation preserves the bracket.
- `SULieAlgebra.adjointContr` : the contraction of two real adjoint indices.
- `SULieAlgebra.adjointContr_flip_injective` : the real contraction is nondegenerate.
- `SULieAlgebra.adjointℂContr` : the contraction of two complex adjoint indices.
- `SULieAlgebra.toMatrixℂ_adjointℂ` : on matrices the adjoint action is conjugation.
- `SULieAlgebra.adjointℂContr_tmul` : the contraction is the trace form on matrices.
- `SULieAlgebra.adjointℂContr_flip_injective` : the complex contraction is nondegenerate.

## iii. Table of contents

- A. The adjoint representation
  - A.1. The real adjoint representation
  - A.2. The complex adjoint representation
- B. The contraction of adjoint indices
  - B.1. The real case
  - B.2. The complex case

## iv. References

* None.

-/

@[expose] public section

open Matrix TensorProduct ComplexStarModule
open scoped ComplexOrder

namespace SULieAlgebra

/-!

## A. The adjoint representation

-/

/-!

### A.1. The real adjoint representation

-/

/-- The adjoint representation `x ↦ g x g†` of `SU(n)` on its real Lie algebra `su(n)`. -/
noncomputable def adjoint {n : ℕ} :
    Representation ℝ (specialUnitaryGroup (Fin n) ℂ) (SULieAlgebra n ℂ) :=
  conj.comp (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup)

/-- The underlying matrix of `adjoint g x` is `g x g†`. -/
@[simp]
lemma adjoint_val {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ) (x : SULieAlgebra n ℂ) :
    (adjoint g x).1 = g.1 * x.1 * star g.1 := rfl

/-- The adjoint representation preserves the bracket, so `SU(n)` acts on `su(n)` by Lie algebra
  automorphisms. -/
lemma adjoint_lie {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ) (x y : SULieAlgebra n ℂ) :
    adjoint g ⁅x, y⁆ = ⁅adjoint g x, adjoint g y⁆ :=
  conj_lie _ x y

/-!

### A.2. The complex adjoint representation

-/

/-- The adjoint representation of `SU(n)` on the complexification `ℂ ⊗[ℝ] su(n)`: the
  complexification of the adjoint representation `adjoint` on `su(n)`. -/
noncomputable def adjointℂ {n : ℕ} :
    Representation ℂ (specialUnitaryGroup (Fin n) ℂ) (Complexification n) :=
  (Module.End.baseChangeHom ℝ ℂ (SULieAlgebra n ℂ) : Module.End ℝ _ →* Module.End ℂ _).comp
    adjoint

@[simp]
lemma adjointℂ_tmul {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ) (z : ℂ) (x : SULieAlgebra n ℂ) :
    adjointℂ g (z ⊗ₜ x) = z ⊗ₜ adjoint g x := rfl

/-- The complex adjoint representation preserves the bracket of the complexification, so `SU(n)`
  acts on `ℂ ⊗[ℝ] su(n)` by Lie algebra automorphisms. -/
lemma adjointℂ_lie {n : ℕ} (g : specialUnitaryGroup (Fin n) ℂ) (A B : Complexification n) :
    adjointℂ g ⁅A, B⁆ = ⁅adjointℂ g A, adjointℂ g B⁆ := by
  induction A using TensorProduct.inductionOn with
  | tmul z x =>
    induction B using TensorProduct.inductionOn with
    | tmul w y =>
      rw [LieAlgebra.ExtendScalars.bracket_tmul, adjointℂ_tmul, adjointℂ_tmul, adjointℂ_tmul,
        LieAlgebra.ExtendScalars.bracket_tmul, adjoint_lie]
    | add B B' hB hB' =>
      rw [lie_add (L := Complexification n), map_add, hB, hB', map_add,
        lie_add (L := Complexification n)]
  | add A A' hA hA' =>
    rw [add_lie (L := Complexification n), map_add, hA, hA', map_add,
      add_lie (L := Complexification n)]

/-- The adjoint representation conjugates the matrix, `M ↦ g M g†`. -/
@[simp]
lemma toMatrixℂ_adjointℂ {n} (g : specialUnitaryGroup (Fin n) ℂ) (A : Complexification n) :
    toMatrixℂ (adjointℂ g A) = g.1 * toMatrixℂ A * star g.1 := by
  induction A using TensorProduct.inductionOn with
  | tmul z x =>
    rw [adjointℂ_tmul, toMatrixℂ_tmul, toMatrixℂ_tmul, adjoint_val, Matrix.mul_smul,
      Matrix.smul_mul]
  | add A B hA hB => rw [map_add, map_add, hA, hB, map_add, Matrix.mul_add, Matrix.add_mul]

lemma toMatrixℂ_adjointℂ_trace {n} (g : specialUnitaryGroup (Fin n) ℂ) (A : Complexification n) :
    (toMatrixℂ (adjointℂ g A)).trace = (toMatrixℂ A).trace := by
  rw [toMatrixℂ_adjointℂ, Matrix.trace_mul_cycle, Matrix.trace_mul_cycle, Matrix.mul_assoc,
    (mem_specialUnitaryGroup_iff.mp g.2).1.1, Matrix.mul_one]

/-!

## B. The contraction of adjoint indices

### B.1. The real case

-/

/-- The contraction of two real adjoint indices: the trace form `x ⊗ y ↦ tr (x y)` on `su(n)`,
  which is real since `x` and `y` are hermitian. -/
noncomputable def adjointContr {n : ℕ} : ((adjoint (n := n)).tprod adjoint).IntertwiningMap
    (Representation.trivial ℝ (specialUnitaryGroup (Fin n) ℂ) ℝ) where
  toLinearMap := TensorProduct.lift <|
    LinearMap.mk₂ ℝ (fun x y : SULieAlgebra n ℂ => (x.1 * y.1).trace.re)
      (fun x x' y => by simp [add_mul, trace_add])
      (fun r x y => by simp)
      (fun x y y' => by simp [mul_add, trace_add])
      (fun r x y => by simp)
  isIntertwining' g := TensorProduct.ext' fun x y => by
    have hg : star g.1 * g.1 = 1 := (mem_specialUnitaryGroup_iff.mp g.2).1.1
    simp only [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul,
      Representation.trivial_apply, lift.tmul, LinearMap.mk₂_apply, adjoint_val]
    rw [show g.1 * x.1 * star g.1 * (g.1 * y.1 * star g.1) = g.1 * (x.1 * y.1) * star g.1 by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star g.1), hg, Matrix.one_mul],
      Matrix.trace_mul_cycle, hg, Matrix.one_mul]

/-- The real contraction is the real part of the trace, `x ⊗ y ↦ re tr (x y)`. -/
@[simp]
lemma adjointContr_tmul {n : ℕ} (x y : SULieAlgebra n ℂ) :
    adjointContr (x ⊗ₜ y) = (x.1 * y.1).trace.re := rfl

/-- The trace `tr (x y)` of two elements of `su(n)` is real, equal to their contraction. -/
lemma ofReal_adjointContr_tmul {n : ℕ} (x y : SULieAlgebra n ℂ) :
    (adjointContr (x ⊗ₜ y) : ℂ) = (x.1 * y.1).trace := by
  rw [adjointContr_tmul]
  refine Complex.conj_eq_iff_re.1 ?_
  change star (x.1 * y.1).trace = _
  rw [← trace_conjTranspose, conjTranspose_mul, ← star_eq_conjTranspose,
    ← star_eq_conjTranspose, x.star_val_eq, y.star_val_eq, trace_mul_comm]

lemma adjointContr_symm {n : ℕ} (x y : SULieAlgebra n ℂ) :
    adjointContr (x ⊗ₜ y) = adjointContr (y ⊗ₜ x) := by
  rw [adjointContr_tmul, adjointContr_tmul, trace_mul_comm]

lemma adjointContr_separating_left {n : ℕ} (x : SULieAlgebra n ℂ)
    (hx : ∀ y, adjointContr (x ⊗ₜ y) = 0) : x = 0 := by
  have h : (x.1 * x.1ᴴ).trace = 0 := by
    rw [← star_eq_conjTranspose, x.star_val_eq, ← ofReal_adjointContr_tmul, hx,
      Complex.ofReal_zero]
  exact Subtype.ext (trace_mul_conjTranspose_self_eq_zero_iff.mp h)

lemma adjointContr_separating_right {n : ℕ} (y : SULieAlgebra n ℂ)
    (hy : ∀ x, adjointContr (x ⊗ₜ y) = 0) : y = 0 :=
  adjointContr_separating_left y fun x => by rw [adjointContr_symm, hy]

/-- The real contraction separates `su(n)`: `y ↦ (x ↦ re tr (x y))` is injective. -/
lemma adjointContr_flip_injective {n : ℕ} :
    Function.Injective (TensorProduct.curry (adjointContr (n := n)).toLinearMap).flip := by
  intro w w' h
  refine sub_eq_zero.1 (adjointContr_separating_right _ fun x => ?_)
  have hx := LinearMap.congr_fun h x
  simp only [LinearMap.flip_apply, TensorProduct.curry_apply] at hx
  rw [tmul_sub, map_sub, sub_eq_zero]
  exact hx

/-!

### B.2. The complex case

-/

/-- The contraction of two complex adjoint indices: the complexification of the real contraction
  `adjointContr`. -/
noncomputable def adjointℂContr {n : ℕ} : ((adjointℂ (n := n)).tprod adjointℂ).IntertwiningMap
    (Representation.trivial ℂ (specialUnitaryGroup (Fin n) ℂ) ℂ) where
  toLinearMap := TensorProduct.lift <| LinearMap.BilinForm.baseChange ℂ <|
    TensorProduct.curry (adjointContr (n := n)).toLinearMap
  isIntertwining' g := TensorProduct.ext' fun A B => by
    simp only [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul,
      Representation.trivial_apply]
    induction A using TensorProduct.inductionOn with
    | tmul z x =>
      induction B using TensorProduct.inductionOn with
      | tmul w y =>
        have h := Representation.IntertwiningMap.isIntertwining _ _ (adjointContr (n := n)) g
          (x ⊗ₜ y)
        simp only [Representation.tprod_apply, TensorProduct.map_tmul,
          Representation.trivial_apply] at h
        simp only [adjointℂ_tmul, lift.tmul, LinearMap.BilinForm.baseChange_tmul,
          TensorProduct.curry_apply, Representation.IntertwiningMap.toLinearMap_apply, h]
      | add B B' hB hB' => rw [map_add, tmul_add, map_add, hB, hB', tmul_add, map_add]
    | add A A' hA hA' => rw [map_add, add_tmul, map_add, hA, hA', add_tmul, map_add]

/-- The contraction is the trace form, `A ⊗ B ↦ tr (A B)`. -/
lemma adjointℂContr_tmul (A B : Complexification n) :
    adjointℂContr (A ⊗ₜ B) = (toMatrixℂ A * toMatrixℂ B).trace := by
  induction A using TensorProduct.inductionOn with
  | tmul z x =>
    induction B using TensorProduct.inductionOn with
    | tmul w y =>
      change TensorProduct.lift _ ((z ⊗ₜ x) ⊗ₜ (w ⊗ₜ y)) = _
      rw [lift.tmul, LinearMap.BilinForm.baseChange_tmul, TensorProduct.curry_apply,
        Representation.IntertwiningMap.toLinearMap_apply, Complex.real_smul,
        ofReal_adjointContr_tmul, toMatrixℂ_tmul, toMatrixℂ_tmul, Matrix.smul_mul,
        Matrix.mul_smul, trace_smul, trace_smul, smul_eq_mul, smul_eq_mul]
      ring
    | add B B' hB hB' => rw [tmul_add, map_add, hB, hB', map_add, Matrix.mul_add, trace_add]
  | add A A' hA hA' => rw [add_tmul, map_add, hA, hA', map_add, Matrix.add_mul, trace_add]

lemma adjointℂContr_symm {n} (A B : Complexification n) :
    adjointℂContr (A ⊗ₜ B) = adjointℂContr (B ⊗ₜ A) := by
  rw [adjointℂContr_tmul, adjointℂContr_tmul, Matrix.trace_mul_comm]

lemma adjointℂContr_separating_left {n} (A : Complexification n)
    (hA : ∀ B, adjointℂContr (A ⊗ₜ B) = 0) : A = 0 := by
  have h := hA (ofTracelessℂ (toMatrixℂ A)ᴴ
    (by rw [trace_conjTranspose, trace_toMatrixℂ, star_zero]))
  rw [adjointℂContr_tmul, toMatrixℂ_ofTracelessℂ, trace_mul_conjTranspose_self_eq_zero_iff] at h
  exact toMatrixℂ_injective (h.trans (map_zero _).symm)

lemma adjointℂContr_separating_right {n} (B : Complexification n)
    (hB : ∀ A, adjointℂContr (A ⊗ₜ B) = 0) : B = 0 :=
  adjointℂContr_separating_left B fun A => by rw [adjointℂContr_symm, hB]

/-- The contraction separates the complexification: `B ↦ (A ↦ tr (A B))` is injective. -/
lemma adjointℂContr_flip_injective :
    Function.Injective (TensorProduct.curry (adjointℂContr (n := n)).toLinearMap).flip := by
  intro w w' h
  refine sub_eq_zero.1 (adjointℂContr_separating_right _ fun A => ?_)
  have hA := LinearMap.congr_fun h A
  simp only [LinearMap.flip_apply, TensorProduct.curry_apply] at hA
  rw [tmul_sub, map_sub, sub_eq_zero]
  exact hA

end SULieAlgebra
