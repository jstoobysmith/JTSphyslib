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
abbrev JetGaugeAlgebra :=
  ↥(selfAdjoint.submodule ℝ (Matrix (Fin 3) (Fin 3) JetRing) ⊓
    LinearMap.ker (Matrix.traceLinearMap (Fin 3) ℝ JetRing)) ×
  ↥(selfAdjoint.submodule ℝ (Matrix (Fin 2) (Fin 2) JetRing) ⊓
    LinearMap.ker (Matrix.traceLinearMap (Fin 2) ℝ JetRing)) ×
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

@[simp]
lemma add_toSU3Matrix (a b : JetGaugeAlgebra) :
    (a + b).toSU3Matrix = a.toSU3Matrix + b.toSU3Matrix := by rfl

@[simp]
lemma add_toSU2Matrix (a b : JetGaugeAlgebra) :
    (a + b).toSU2Matrix = a.toSU2Matrix + b.toSU2Matrix := by rfl

@[simp]
lemma add_toU1Value (a b : JetGaugeAlgebra) :
    (a + b).toU1Value = a.toU1Value + b.toU1Value := by rfl

@[simp]
lemma zero_toSU3Matrix : (0 : JetGaugeAlgebra).toSU3Matrix = 0 := by rfl

@[simp]
lemma zero_toSU2Matrix : (0 : JetGaugeAlgebra).toSU2Matrix = 0 := by rfl

@[simp]
lemma zero_toU1Value : (0 : JetGaugeAlgebra).toU1Value = 0 := by rfl

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

## The derivative on the jet gauge algebra

-/

/-- The formal derivative in the direction `μ` on the jet gauge algebra, acting
  entrywise on each factor. It preserves hermiticity since `star` commutes with
  `pderiv`, and tracelessness since the trace of the entrywise derivative is the
  derivative of the trace. -/
noncomputable def deriv (μ : Fin 1 ⊕ Fin 3) : JetGaugeAlgebra →ₗ[ℝ] JetGaugeAlgebra where
  toFun a := ofMatrixProd
      (a.toSU3Matrix.map (pderiv ℂ μ), a.toSU2Matrix.map (pderiv ℂ μ),
        pderiv ℂ μ a.toU1Value)
      ⟨by
        ext i j : 1
        simpa [Matrix.star_apply, Matrix.map_apply, ← JetRing.pderiv_star] using
          congrArg (fun M => pderiv ℂ μ (M i j))
            (show star a.toSU3Matrix = a.toSU3Matrix from a.1.2.1),
        by rw [← AddMonoidHom.map_trace, show a.toSU3Matrix.trace = 0 from a.1.2.2, map_zero]⟩
      ⟨by
        ext i j : 1
        simpa [Matrix.star_apply, Matrix.map_apply, ← JetRing.pderiv_star] using
          congrArg (fun M => pderiv ℂ μ (M i j))
            (show star a.toSU2Matrix = a.toSU2Matrix from a.2.1.2.1),
        by rw [← AddMonoidHom.map_trace, show a.toSU2Matrix.trace = 0 from a.2.1.2.2, map_zero]⟩
      (by rw [← JetRing.pderiv_star, show star a.toU1Value = a.toU1Value from a.2.2.2])
  map_add' a b := by
    ext <;> simp [Matrix.map_apply]
  map_smul' r a := by
    refine ext_of_matrix ?_ ?_ ?_ <;>
      simp only [ofMatrixProd_toSU3Matrix, ofMatrixProd_toSU2Matrix, ofMatrixProd_toU1Value,
        smul_toSU3Matrix, smul_toSU2Matrix, smul_toU1Value, RingHom.id_apply]
    · ext i j : 1
      simp only [Matrix.map_apply, Matrix.smul_apply]
      rw [← algebraMap_smul ℂ r, Derivation.map_smul, algebraMap_smul]
    · ext i j : 1
      simp only [Matrix.map_apply, Matrix.smul_apply]
      rw [← algebraMap_smul ℂ r, Derivation.map_smul, algebraMap_smul]
    · rw [← algebraMap_smul ℂ r, Derivation.map_smul, algebraMap_smul]

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
