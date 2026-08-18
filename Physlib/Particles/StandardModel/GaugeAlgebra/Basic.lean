/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.Jet
public import Physlib.Relativity.Tensors.ComplexTensor.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Representation
public import Physlib.Relativity.SL2C.Basic
public import Physlib.Mathematics.ConjModule
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Physlib.Particles.LagrangianTheory.Basic
public import Physlib.Mathematics.MvPowerSeriesDerivative
public import Physlib.Mathematics.MvPolynomialTranslation
public import Mathlib.Algebra.MvPolynomial.Derivation
/-!
# The gauge algebra of the Standard Model

The gauge algebra of the Standard Model is the Lie algebra of
`GaugeGroupI`, which is the direct sum of the Lie algebras of `SU(3)`, `SU(2)` and `U(1)`.
This is a matrix Lie algebra, so the bracket is given by the commutator of matrices.

-/

@[expose] public section

namespace StandardModel
open MvPowerSeries Matrix

/-- The gauge algebra of the Standard Model: the Lie algebra of `GaugeGroupI`, with one
  factor per gauge group factor — traceless self-adjoint `3 × 3` and `2 × 2` complex
  matrices and a self-adjoint (i.e. real) scalar. This is the constant-coefficient
  analogue of `JetGaugeAlgebra`, and the value at the base point of the jets it contains. -/
abbrev GaugeAlgebra :=
  ↥(selfAdjoint.submodule ℝ (Matrix (Fin 3) (Fin 3) ℂ) ⊓
    LinearMap.ker (Matrix.traceLinearMap (Fin 3) ℝ ℂ)) ×
  ↥(selfAdjoint.submodule ℝ (Matrix (Fin 2) (Fin 2) ℂ) ⊓
    LinearMap.ker (Matrix.traceLinearMap (Fin 2) ℝ ℂ)) ×
  selfAdjoint ℂ

namespace GaugeAlgebra

/-!

## Basic projections

-/

/-- The `su(3)`-factor component of an element of the gauge algebra. -/
def toSU3Matrix (a : GaugeAlgebra) : Matrix (Fin 3) (Fin 3) ℂ := a.1

/-- The `su(2)`-factor component of an element of the gauge algebra. -/
def toSU2Matrix (a : GaugeAlgebra) : Matrix (Fin 2) (Fin 2) ℂ := a.2.1

/-- The `u(1)`-factor component of an element of the gauge algebra. -/
def toU1Value (a : GaugeAlgebra) : ℂ := a.2.2

@[ext]
lemma ext_of_matrix {a b : GaugeAlgebra} (h1 : a.toSU3Matrix = b.toSU3Matrix)
    (h2 : a.toSU2Matrix = b.toSU2Matrix) (h3 : a.toU1Value = b.toU1Value) : a = b := by
  cases a; cases b
  simp only [toSU3Matrix, toSU2Matrix, toU1Value] at h1 h2 h3
  grind

/-!

## Constructor from a product of matrices

-/

/-- The element of the gauge algebra constructed from a triple of matrices satisfying
  the relevant hermiticity and tracelessness conditions. -/
def ofMatrixProd (A : Matrix (Fin 3) (Fin 3) ℂ ×
    Matrix (Fin 2) (Fin 2) ℂ × ℂ) (hA : star A.1 = A.1 ∧ A.1.trace = 0)
    (hB : star A.2.1 = A.2.1 ∧ A.2.1.trace = 0) (hC : star A.2.2 = A.2.2) : GaugeAlgebra :=
  ⟨⟨A.1, hA⟩, ⟨A.2.1, hB⟩, ⟨A.2.2, hC⟩⟩

@[simp]
lemma ofMatrixProd_toSU3Matrix (A : Matrix (Fin 3) (Fin 3) ℂ ×
    Matrix (Fin 2) (Fin 2) ℂ × ℂ) (hA : star A.1 = A.1 ∧ A.1.trace = 0)
    (hB : star A.2.1 = A.2.1 ∧ A.2.1.trace = 0) (hC : star A.2.2 = A.2.2) :
    (ofMatrixProd A hA hB hC).toSU3Matrix = A.1 := by rfl

@[simp]
lemma ofMatrixProd_toSU2Matrix (A : Matrix (Fin 3) (Fin 3) ℂ ×
    Matrix (Fin 2) (Fin 2) ℂ × ℂ) (hA : star A.1 = A.1 ∧ A.1.trace = 0)
    (hB : star A.2.1 = A.2.1 ∧ A.2.1.trace = 0) (hC : star A.2.2 = A.2.2) :
    (ofMatrixProd A hA hB hC).toSU2Matrix = A.2.1 := by rfl

@[simp]
lemma ofMatrixProd_toU1Value (A : Matrix (Fin 3) (Fin 3) ℂ ×
    Matrix (Fin 2) (Fin 2) ℂ × ℂ) (hA : star A.1 = A.1 ∧ A.1.trace = 0)
    (hB : star A.2.1 = A.2.1 ∧ A.2.1.trace = 0) (hC : star A.2.2 = A.2.2) :
    (ofMatrixProd A hA hB hC).toU1Value = A.2.2 := by rfl

/-!

## The Lie algebra instance

-/

@[simp]
lemma add_toSU3Matrix (a b : GaugeAlgebra) :
    (a + b).toSU3Matrix = a.toSU3Matrix + b.toSU3Matrix := by rfl

@[simp]
lemma add_toSU2Matrix (a b : GaugeAlgebra) :
    (a + b).toSU2Matrix = a.toSU2Matrix + b.toSU2Matrix := by rfl

@[simp]
lemma add_toU1Value (a b : GaugeAlgebra) :
    (a + b).toU1Value = a.toU1Value + b.toU1Value := by rfl

@[simp]
lemma zero_toSU3Matrix : (0 : GaugeAlgebra).toSU3Matrix = 0 := by rfl

@[simp]
lemma zero_toSU2Matrix : (0 : GaugeAlgebra).toSU2Matrix = 0 := by rfl

@[simp]
lemma zero_toU1Value : (0 : GaugeAlgebra).toU1Value = 0 := by rfl

@[simp]
lemma smul_toSU3Matrix (r : ℝ) (a : GaugeAlgebra) :
    (r • a).toSU3Matrix = r • a.toSU3Matrix := by rfl

@[simp]
lemma smul_toSU2Matrix (r : ℝ) (a : GaugeAlgebra) :
    (r • a).toSU2Matrix = r • a.toSU2Matrix := by rfl

@[simp]
lemma smul_toU1Value (r : ℝ) (a : GaugeAlgebra) :
    (r • a).toU1Value = r • a.toU1Value := by rfl

/-- The bracket on the gauge algebra: `I` times the matrix commutator on the
  `su(3)` and `su(2)` factors, and zero on the (commutative) `u(1)` factor. The
  factor of `I` is what makes the bracket of two hermitian matrices hermitian
  again; it is also why the bracket is only `ℝ`-bilinear, not `ℂ`-bilinear. -/
noncomputable instance : Bracket GaugeAlgebra GaugeAlgebra where
  bracket a b := ofMatrixProd
      (Complex.I • (a.toSU3Matrix * b.toSU3Matrix - b.toSU3Matrix * a.toSU3Matrix),
        Complex.I • (a.toSU2Matrix * b.toSU2Matrix - b.toSU2Matrix * a.toSU2Matrix),
        0)
      ⟨by
        rw [star_smul, star_sub, star_mul, star_mul,
          show star a.toSU3Matrix = a.toSU3Matrix from a.1.2.1,
          show star b.toSU3Matrix = b.toSU3Matrix from b.1.2.1,
          Complex.star_def, Complex.conj_I, neg_smul, ← smul_neg, neg_sub],
        by rw [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self, smul_zero]⟩
      ⟨by
        rw [star_smul, star_sub, star_mul, star_mul,
          show star a.toSU2Matrix = a.toSU2Matrix from a.2.1.2.1,
          show star b.toSU2Matrix = b.toSU2Matrix from b.2.1.2.1,
          Complex.star_def, Complex.conj_I, neg_smul, ← smul_neg, neg_sub],
        by rw [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self, smul_zero]⟩
      (star_zero _)

@[simp]
lemma bracket_toSU3Matrix (a b : GaugeAlgebra) :
    ⁅a, b⁆.toSU3Matrix =
      Complex.I • (a.toSU3Matrix * b.toSU3Matrix - b.toSU3Matrix * a.toSU3Matrix) := rfl

@[simp]
lemma bracket_toSU2Matrix (a b : GaugeAlgebra) :
    ⁅a, b⁆.toSU2Matrix =
      Complex.I • (a.toSU2Matrix * b.toSU2Matrix - b.toSU2Matrix * a.toSU2Matrix) := rfl

@[simp]
lemma bracket_toU1Value (a b : GaugeAlgebra) :
    ⁅a, b⁆.toU1Value = 0 := rfl

noncomputable instance : LieRing GaugeAlgebra where
  add_lie a b c := by
    ext <;> simp [add_mul, mul_add, smul_sub] <;> ring
  lie_add a b c := by
    ext <;> simp [add_mul, mul_add, smul_sub] <;> ring
  lie_self a := by
    ext <;> simp
  leibniz_lie a b c := by
    refine ext_of_matrix ?_ ?_ ?_ <;>
      simp only [bracket_toSU3Matrix, bracket_toSU2Matrix, bracket_toU1Value,
        add_toSU3Matrix, add_toSU2Matrix, add_toU1Value, mul_smul_comm, smul_mul_assoc,
        smul_smul, Complex.I_mul_I, smul_sub, mul_sub, sub_mul, mul_assoc, add_zero] <;>
      module

noncomputable instance : LieAlgebra ℝ GaugeAlgebra where
  lie_smul t a b := by
    ext <;> simp [smul_sub] <;> ring

end GaugeAlgebra

end StandardModel
