/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Complex.Module
/-!

# The Lie algebra `su(n)` in the hermitian presentation

## i. Overview

In physics, `su(n)` is described through generators `T^a`, `a = 1, …, n² - 1`, a basis of the
traceless hermitian `n × n` complex matrices, satisfying `[T^a, T^b] = i f_{abc} T^c` with real
structure constants `f_{abc}`. Here `i` is the imaginary unit and the repeated index `c` is summed.
This file makes the traceless hermitian matrices into a real Lie algebra with the bracket
`⁅x, y⁆ = i (x y - y x)`, on which the unitary group acts by conjugation. The construction allows
entries in any commutative `*`-ring `R` that is both a real and a complex `*`-algebra, as
`SULieAlgebra n R`; the Lie algebra `su(n)` itself is `SULieAlgebra n ℂ`.

Sending `z ⊗ x` to the matrix `z x` identifies the complexification `ℂ ⊗[ℝ] su(n)` with the
traceless complex matrices. The inverse writes a traceless matrix `M` as `ℜ M + i ℑ M`, its real
and imaginary parts `ℜ M` and `ℑ M` being traceless hermitian.

## ii. Key results

- `SULieAlgebra n R` : traceless hermitian `n × n` matrices over `R`, as a real Lie algebra.
- `SULieAlgebra.conj` : the representation `x ↦ U x U†` of the unitary group.
- `SULieAlgebra.conj_lie` : conjugation by a unitary matrix preserves the bracket.
- `SULieAlgebra.Complexification n` : the complexification `ℂ ⊗[ℝ] su(n)`.
- `SULieAlgebra.toMatrixℂ` : the underlying matrix of an element of the complexification.
- `SULieAlgebra.toMatrixℂ_injective`, `SULieAlgebra.range_toMatrixℂ` : the complexification is
  the traceless complex matrices.

## iii. Table of contents

- A. Traceless hermitian matrices
- B. The conjugation representation
- C. The bracket
- D. Conjugation preserves the bracket
- E. The complexification
  - E.1. The underlying matrix of the complexification
  - E.2. The element with a given traceless matrix
  - E.3. The injectivity and surjectivity of the matrix map

## iv. References

* None.

-/

@[expose] public section

open Matrix TensorProduct ComplexStarModule

/-!

## A. Traceless hermitian matrices

Since `i A` is skew-hermitian when `A` is hermitian, the traceless hermitian matrices form a real
vector space.

-/

/-- The traceless hermitian `n × n` matrices with entries in `R`, as a real subspace. -/
abbrev SULieAlgebra.submodule (n : ℕ) (R : Type*) [CommRing R] [StarRing R] [Algebra ℝ R]
    [StarModule ℝ R] : Submodule ℝ (Matrix (Fin n) (Fin n) R) :=
  selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) R) ⊓
    LinearMap.ker (Matrix.traceLinearMap (Fin n) ℝ R)

/-- Traceless hermitian `n × n` matrices with entries in `R`, as a real Lie algebra;
  `SULieAlgebra n ℂ` is `su(n)`. -/
abbrev SULieAlgebra (n : ℕ) (R : Type*) [CommRing R] [StarRing R] [Algebra ℝ R]
    [StarModule ℝ R] : Type _ :=
  ↥(SULieAlgebra.submodule n R)

namespace SULieAlgebra

variable {n : ℕ} {R : Type*} [CommRing R] [StarRing R] [Algebra ℝ R] [StarModule ℝ R]

/-- The element given by a traceless hermitian matrix. -/
def ofMatrix (A : Matrix (Fin n) (Fin n) R) (hA : star A = A) (hT : A.trace = 0) :
    SULieAlgebra n R := ⟨A, hA, hT⟩

/-- The underlying matrix of `ofMatrix A hA hT` is `A`. -/
@[simp]
lemma val_ofMatrix (A : Matrix (Fin n) (Fin n) R) (hA : star A = A) (hT : A.trace = 0) :
    (ofMatrix A hA hT).1 = A := rfl

/-- The underlying matrix of an element is hermitian. -/
lemma star_val_eq (x : SULieAlgebra n R) : star x.1 = x.1 := x.2.1

/-- The underlying matrix of an element is traceless. -/
lemma trace_val_eq_zero (x : SULieAlgebra n R) : x.1.trace = 0 := x.2.2

/-!

## B. The conjugation representation

Conjugation `x ↦ U x U†` by a unitary matrix `U` preserves traceless hermitian matrices, by
`U† U = 1` and cyclicity of the trace, and defines a representation of the unitary group.

-/

/-- The conjugation representation of the unitary group on `SULieAlgebra n R`: `x ↦ U x U†`. -/
noncomputable def conj : Representation ℝ (unitaryGroup (Fin n) R) (SULieAlgebra n R) where
  toFun U :=
    { toFun x := ofMatrix (U.1 * x.1 * star U.1)
        (by rw [star_mul, star_mul, star_star, x.star_val_eq, mul_assoc])
        (by
          rw [Matrix.trace_mul_comm, ← mul_assoc, UnitaryGroup.star_mul_self U, one_mul,
            x.trace_val_eq_zero])
      map_add' x y := Subtype.ext (by simp [mul_add, add_mul])
      map_smul' r x := Subtype.ext (by simp) }
  map_one' := LinearMap.ext fun x => Subtype.ext (by simp)
  map_mul' U V := LinearMap.ext fun x => Subtype.ext (by simp [star_mul, mul_assoc])

/-- The underlying matrix of `conj U x` is `U x U†`. -/
@[simp]
lemma val_conj_apply (U : unitaryGroup (Fin n) R) (x : SULieAlgebra n R) :
    (conj U x).1 = U.1 * x.1 * star U.1 := rfl

/-!

## C. The bracket

From here on `R` is also a complex `*`-algebra, so that matrices can be multiplied by `i`. The
commutator of two hermitian matrices is skew-hermitian, and multiplying it by `i` makes it
hermitian again, giving the bracket `⁅x, y⁆ = i (x y - y x)`. Being `i` times the commutator, it
is a Lie bracket.

Since `[i x, i y] = i ⁅x, y⁆`, multiplication by `i` turns this bracket into the commutator of
traceless skew-hermitian matrices, the usual mathematical presentation of `su(n)`.

The factor `i` flips the sign of the structure constants; if `[T^a, T^b] = i f_{abc} T^c`, then
`⁅T^a, T^b⁆ = -f_{abc} T^c`.

-/

variable [Algebra ℂ R] [StarModule ℂ R]

/-- The bracket `⁅x, y⁆ = i (x y - y x)`. -/
noncomputable instance : Bracket (SULieAlgebra n R) (SULieAlgebra n R) where
  bracket x y := ofMatrix (Complex.I • (x.1 * y.1 - y.1 * x.1))
    (by
      rw [star_smul, star_sub, star_mul, star_mul, x.star_val_eq, y.star_val_eq,
        Complex.star_def, Complex.conj_I, neg_smul, ← smul_neg, neg_sub])
    (by rw [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self, smul_zero])

/-- The underlying matrix of `⁅x, y⁆` is `i (x y - y x)`. -/
@[simp]
lemma val_bracket (x y : SULieAlgebra n R) :
    ⁅x, y⁆.1 = Complex.I • (x.1 * y.1 - y.1 * x.1) := rfl

/-- `⁅x, y⁆ = i (x y - y x)` makes `SULieAlgebra n R` a Lie ring. -/
noncomputable instance : LieRing (SULieAlgebra n R) where
  add_lie x y z := Subtype.ext (by
    simp only [val_bracket, Submodule.coe_add, add_mul, mul_add, smul_add, smul_sub]
    abel)
  lie_add x y z := Subtype.ext (by
    simp only [val_bracket, Submodule.coe_add, add_mul, mul_add, smul_add, smul_sub]
    abel)
  lie_self x := Subtype.ext (by simp)
  leibniz_lie x y z := Subtype.ext (by
    simp only [val_bracket, Submodule.coe_add, mul_smul_comm, smul_mul_assoc, smul_smul,
      Complex.I_mul_I, smul_sub, mul_sub, sub_mul, mul_assoc]
    module)

/-- The bracket is `ℝ`-bilinear, so `SULieAlgebra n R` is a real Lie algebra. -/
noncomputable instance : LieAlgebra ℝ (SULieAlgebra n R) where
  lie_smul r x y := Subtype.ext (by
    ext i j
    simp only [val_bracket, Submodule.coe_smul, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.mul_apply]
    simp only [Algebra.smul_def, mul_sub, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun k _ => by ring)

/-!

## D. Conjugation preserves the bracket

-/

/-- Conjugation by a unitary matrix preserves the bracket, so `conj` acts by Lie algebra
  automorphisms. -/
lemma conj_lie (U : unitaryGroup (Fin n) R) (x y : SULieAlgebra n R) :
    conj U ⁅x, y⁆ = ⁅conj U x, conj U y⁆ := by
  ext1
  simp only [val_conj_apply, val_bracket, Matrix.mul_smul, Matrix.smul_mul, mul_sub, sub_mul]
  congr 2 <;> simp only [mul_assoc, ← mul_assoc (star U.1) U.1, UnitaryGroup.star_mul_self,
    one_mul]

/-!

## E. The complexification

-/

/-- The complexification `ℂ ⊗[ℝ] su(n)` of `su(n)`, a complex Lie algebra. -/
abbrev Complexification (n : ℕ) : Type := ℂ ⊗[ℝ] SULieAlgebra n ℂ

/-!

### E.1. The underlying matrix of the complexification

-/

/-- The underlying matrix of an element of the complexification, `z ⊗ x ↦ z x`. -/
noncomputable def toMatrixℂ : Complexification n →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  (SULieAlgebra.submodule n ℂ).subtype.liftBaseChange ℂ

@[simp]
lemma toMatrixℂ_tmul (z : ℂ) (x : SULieAlgebra n ℂ) : toMatrixℂ (z ⊗ₜ x) = z • x.1 := rfl

/-- The underlying matrix of an element of the complexification is traceless. -/
lemma trace_toMatrixℂ (A : Complexification n) : (toMatrixℂ A).trace = 0 := by
  induction A using TensorProduct.inductionOn with
  | tmul z x => rw [toMatrixℂ_tmul, Matrix.trace_smul, x.trace_val_eq_zero, smul_zero]
  | add A B hA hB => rw [map_add, Matrix.trace_add, hA, hB, add_zero]

/-!

### E.2. The element with a given traceless matrix

-/

/-- The element `1 ⊗ ℜ M + i ⊗ ℑ M` of the complexification with the traceless matrix `M`. -/
noncomputable def ofTracelessℂ (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.trace = 0) :
    Complexification n :=
  1 ⊗ₜ ofMatrix (ℜ M) (selfAdjoint.mem_iff.mp (ℜ M).2) (by
      simp [realPart_apply_coe, trace_smul, trace_add, star_eq_conjTranspose,
        trace_conjTranspose, hM]) +
    Complex.I ⊗ₜ ofMatrix (ℑ M) (selfAdjoint.mem_iff.mp (ℑ M).2) (by
      simp [imaginaryPart_apply_coe, trace_smul, trace_sub, star_eq_conjTranspose,
        trace_conjTranspose, hM])

/-- The matrix of `ofTracelessℂ M` is `M = ℜ M + i ℑ M`. -/
@[simp]
lemma toMatrixℂ_ofTracelessℂ (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.trace = 0) :
    toMatrixℂ (ofTracelessℂ M hM) = M := by
  rw [ofTracelessℂ, map_add, toMatrixℂ_tmul, toMatrixℂ_tmul, one_smul, val_ofMatrix,
    val_ofMatrix, realPart_add_I_smul_imaginaryPart]

/-- `ofTracelessℂ` is additive. -/
lemma ofTracelessℂ_add (M N : Matrix (Fin n) (Fin n) ℂ) (hM : M.trace = 0) (hN : N.trace = 0)
    (hMN : (M + N).trace = 0) :
    ofTracelessℂ (M + N) hMN = ofTracelessℂ M hM + ofTracelessℂ N hN := by
  rw [ofTracelessℂ, ofTracelessℂ, ofTracelessℂ, add_add_add_comm, ← tmul_add, ← tmul_add]
  congr 2 <;> exact Subtype.ext (by simp)

/-- An element of the complexification is recovered from its matrix. -/
@[simp]
lemma ofTracelessℂ_toMatrixℂ (A : Complexification n) :
    ofTracelessℂ (toMatrixℂ A) (trace_toMatrixℂ A) = A := by
  induction A using TensorProduct.inductionOn with
  | tmul z x =>
    have hre : ∀ h₁ h₂, ofMatrix (ℜ (z • x.1)) h₁ h₂ = z.re • x := fun _ _ => Subtype.ext (by
      simp [realPart_smul, IsSelfAdjoint.coe_realPart x.star_val_eq,
        IsSelfAdjoint.imaginaryPart x.star_val_eq])
    have him : ∀ h₁ h₂, ofMatrix (ℑ (z • x.1)) h₁ h₂ = z.im • x := fun _ _ => Subtype.ext (by
      simp [imaginaryPart_smul, IsSelfAdjoint.coe_realPart x.star_val_eq,
        IsSelfAdjoint.imaginaryPart x.star_val_eq])
    rw [ofTracelessℂ]
    simp only [toMatrixℂ_tmul, hre, him]
    rw [← smul_tmul, ← smul_tmul, ← add_tmul, Complex.real_smul, Complex.real_smul, mul_one,
      Complex.re_add_im]
  | add A B hA hB =>
    calc _ = ofTracelessℂ (toMatrixℂ A + toMatrixℂ B)
          (by rw [← map_add]; exact trace_toMatrixℂ _) := by
          congr 1
          exact map_add _ _ _
      _ = A + B := by rw [ofTracelessℂ_add _ _ (trace_toMatrixℂ A) (trace_toMatrixℂ B), hA, hB]

/-!

### E.3. The injectivity and surjectivity of the matrix map

-/

/-- An element of the complexification is determined by its matrix. -/
lemma toMatrixℂ_injective : Function.Injective (toMatrixℂ (n := n)) := fun A B h => by
  rw [← ofTracelessℂ_toMatrixℂ A, ← ofTracelessℂ_toMatrixℂ B]
  congr 1

/-- The matrices of elements of the complexification are exactly the traceless matrices. -/
lemma range_toMatrixℂ :
    LinearMap.range (toMatrixℂ (n := n)) = LinearMap.ker (Matrix.traceLinearMap (Fin n) ℂ ℂ) := by
  ext M
  rw [LinearMap.mem_range, LinearMap.mem_ker, Matrix.traceLinearMap_apply]
  exact ⟨fun ⟨A, hA⟩ => hA ▸ trace_toMatrixℂ A,
    fun hM => ⟨ofTracelessℂ M hM, toMatrixℂ_ofTracelessℂ M hM⟩⟩

end SULieAlgebra
