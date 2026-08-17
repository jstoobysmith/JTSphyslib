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
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.RingTheory.MvPowerSeries.PiTopology
public import Mathlib.Topology.Instances.Matrix
/-!
# The jet gauge algebra

We define `JetGaugeAlgebra` as the Lie algebra of `JetGaugeGroupI`,
defined explicitly as traceless self-adjoint matrices, and giving it an instance `LieAlgebra`.
This is a matrix Lie algebra, so the bracket is given by the commutator of matrices.

Note here that `JetGaugeAlgebra` is a module over `ℝ` not `ℂ` or `JetRing`.

On this Lie algebra define a prefered basis, `basis`, indexed by
`basisIndex × Multiset (Fin 1 ⊕ Fin 3)`.
Here `basisIndex` is the sum `Fin 8 ⊕ Fin 3 ⊕ Fin 1`. The first factor
corresponds to the Gell-Mann matrices which form a basis of `su(3)`,
the second factor corresponds to the Pauli matrices which form a basis of `su(2)`,
and the third factor corresponds to the identity matrix which forms a basis of `u(1)`.

We let `structuralConstant` (typically called `f`) be the structure constants of the Lie algebra
with respect to this prefered basis, so that
```
  [basis i, basis j] = i * ∑ k, structuralConstant i j k • basis k
```

On `JetGaugeAlgebra` we define the adjoint representation of `JetGaugeGroupI`,
`adjointRep`, which acts via `x ↦ g * x * g⁻¹`.

There is also a derivative `deriv : Fin 1 ⊕ Fin 3 → JetLieAlgebra →ₗ[ℝ] JetLieAlgebra`
whose action can be defined componentwise in terms of the basis.

The derivative acts on brackets via the Leibniz rule:
```
  deriv μ [x, y] = [deriv μ x, y] + [x, deriv μ y]
```

-/

@[expose] public section
TODO "Make the API here match what is in the doc-string."
TODO "Add discussion about the basis."
namespace StandardModel
open MvPowerSeries Matrix

/-- The jet gauge algebra: the Lie-algebra analogue of `JetGaugeGroupI`, with one factor per
  gauge group factor — traceless self-adjoint `3 × 3` and `2 × 2` matrices and a self-adjoint
  scalar, all with coefficients in the ring `JetRing` of formal power series in the spacetime
  coordinates. The Maurer–Cartan forms of the jet gauge group are valued here, hermiticity
  being `star_maurerCartanSU3` and its companions. -/
def JetGaugeAlgebra :=
  { A : Matrix (Fin 3) (Fin 3) JetRing // star A = A ∧ A.trace = 0 } ×
  { A : Matrix (Fin 2) (Fin 2) JetRing // star A = A ∧ A.trace = 0 } ×
  selfAdjoint JetRing

namespace JetGaugeAlgebra

/-!

## Basic projections

-/

/-- The `su(3)`-factor component of an element of the jet gauge algebra. -/
def toSU3Matrix (a : JetGaugeAlgebra) : Matrix (Fin 3) (Fin 3) JetRing := a.1

/-- The `su(2)`-factor component of an element of the jet gauge algebra. -/
def toSU2Matrix (a : JetGaugeAlgebra) : Matrix (Fin 2) (Fin 2) JetRing  := a.2.1

/-- The `u(1)`-factor component of an element of the jet gauge algebra. -/
def toU1Value (a : JetGaugeAlgebra) :  JetRing := a.2.2

@[ext]
lemma ext_of_matrix {a b : JetGaugeAlgebra} (h1 : a.toSU3Matrix = b.toSU3Matrix)
    (h2 : a.toSU2Matrix = b.toSU2Matrix) (h3 : a.toU1Value = b.toU1Value) : a = b := by
  cases a; cases b
  simp only [toSU3Matrix, toSU2Matrix, toU1Value] at h1 h2 h3
  grind

/-!

## Constructor from a product of matrices

-/

def ofMatrixProd (A : Matrix (Fin 3) (Fin 3) JetRing ×
    Matrix (Fin 2) (Fin 2) JetRing × JetRing) (hA : star A.1 = A.1 ∧ A.1.trace = 0)
    (hB : star A.2.1 = A.2.1 ∧ A.2.1.trace = 0) (hC : star A.2.2 = A.2.2) : JetGaugeAlgebra :=
  ⟨⟨A.1, hA⟩, ⟨A.2.1, hB⟩, ⟨A.2.2, hC⟩⟩

@[simp]
lemma ofMatrixProd_toSU3Matrix (A : Matrix (Fin 3) (Fin 3) JetRing ×
    Matrix (Fin 2) (Fin 2) JetRing × JetRing) (hA : star A.1 = A.1 ∧ A.1.trace = 0)
    (hB : star A.2.1 = A.2.1 ∧ A.2.1.trace = 0) (hC : star A.2.2 = A.2.2) :
    (ofMatrixProd A hA hB hC).toSU3Matrix = A.1 := by rfl

@[simp]
lemma ofMatrixProd_toSU2Matrix (A : Matrix (Fin 3) (Fin 3) JetRing ×
    Matrix (Fin 2) (Fin 2) JetRing × JetRing) (hA : star A.1 = A.1 ∧ A.1.trace = 0)
    (hB : star A.2.1 = A.2.1 ∧ A.2.1.trace = 0) (hC : star A.2.2 = A.2.2) :
    (ofMatrixProd A hA hB hC).toSU2Matrix = A.2.1 := by rfl

@[simp]
lemma ofMatrixProd_toU1Value (A : Matrix (Fin 3) (Fin 3) JetRing ×
    Matrix (Fin 2) (Fin 2) JetRing × JetRing) (hA : star A.1 = A.1 ∧ A.1.trace = 0)
    (hB : star A.2.1 = A.2.1 ∧ A.2.1.trace = 0) (hC : star A.2.2 = A.2.2) :
    (ofMatrixProd A hA hB hC).toU1Value = A.2.2 := by rfl

/-!

## The Lie algebra instance

-/

noncomputable instance : Add JetGaugeAlgebra where
  add a b :=
    ⟨⟨a.1.1 + b.1.1,
      by rw [star_add, a.1.2.1, b.1.2.1],
      by rw [trace_add, a.1.2.2, b.1.2.2, add_zero]⟩,
    ⟨a.2.1.1 + b.2.1.1,
      by rw [star_add, a.2.1.2.1, b.2.1.2.1],
      by rw [trace_add, a.2.1.2.2, b.2.1.2.2, add_zero]⟩,
    a.2.2 + b.2.2⟩

@[simp]
lemma add_toSU3Matrix (a b : JetGaugeAlgebra) :
    (a + b).toSU3Matrix = a.toSU3Matrix + b.toSU3Matrix := by rfl

@[simp]
lemma add_toSU2Matrix (a b : JetGaugeAlgebra) :
    (a + b).toSU2Matrix = a.toSU2Matrix + b.toSU2Matrix := by rfl

@[simp]
lemma add_toU1Value (a b : JetGaugeAlgebra) :
    (a + b).toU1Value = a.toU1Value + b.toU1Value := by rfl

noncomputable instance : Zero JetGaugeAlgebra where
  zero := ⟨⟨0, by simp, by simp⟩, ⟨0, by simp, by simp⟩, 0⟩

@[simp]
lemma zero_toSU3Matrix : (0 : JetGaugeAlgebra).toSU3Matrix = 0 := by rfl

@[simp]
lemma zero_toSU2Matrix : (0 : JetGaugeAlgebra).toSU2Matrix = 0 := by rfl

@[simp]
lemma zero_toU1Value : (0 : JetGaugeAlgebra).toU1Value = 0 := by rfl

noncomputable instance : SMul ℝ JetGaugeAlgebra where
  smul r a :=
    ⟨⟨r • a.1.1,
      by rw [star_smul, star_trivial, a.1.2.1],
      by rw [trace_smul, a.1.2.2, smul_zero]⟩,
    ⟨r • a.2.1.1,
      by rw [star_smul, star_trivial, a.2.1.2.1],
      by rw [trace_smul, a.2.1.2.2, smul_zero]⟩,
    r • a.2.2⟩

@[simp]
lemma smul_toSU3Matrix (r : ℝ) (a : JetGaugeAlgebra) :
    (r • a).toSU3Matrix = r • a.toSU3Matrix := by rfl

@[simp]
lemma smul_toSU2Matrix (r : ℝ) (a : JetGaugeAlgebra) :
    (r • a).toSU2Matrix = r • a.toSU2Matrix := by rfl

@[simp]
lemma smul_toU1Value (r : ℝ) (a : JetGaugeAlgebra) :
    (r • a).toU1Value = r • a.toU1Value := by rfl


/-!

## The basis

-/

TODO "Define the basis of the jet gauge algebra."


/-!

## The adjoint representation of Jet Gauge group

-/

TODO "Define the adjoint representation of the jet gauge group on the jet gauge algebra."

end JetGaugeAlgebra

end StandardModel
