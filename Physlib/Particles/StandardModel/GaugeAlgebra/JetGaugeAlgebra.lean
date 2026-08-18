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

/-- The bracket on the jet gauge algebra: `I` times the matrix commutator on the
  `su(3)` and `su(2)` factors, and zero on the (commutative) `u(1)` factor. The
  factor of `I` is what makes the bracket of two hermitian matrices hermitian
  again; it is also why the bracket is only `ℝ`-bilinear, not `ℂ`-bilinear. -/
noncomputable instance : Bracket JetGaugeAlgebra JetGaugeAlgebra where
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
lemma bracket_toSU3Matrix (a b : JetGaugeAlgebra) :
    ⁅a, b⁆.toSU3Matrix =
      Complex.I • (a.toSU3Matrix * b.toSU3Matrix - b.toSU3Matrix * a.toSU3Matrix) := rfl

@[simp]
lemma bracket_toSU2Matrix (a b : JetGaugeAlgebra) :
    ⁅a, b⁆.toSU2Matrix =
      Complex.I • (a.toSU2Matrix * b.toSU2Matrix - b.toSU2Matrix * a.toSU2Matrix) := rfl

@[simp]
lemma bracket_toU1Value (a b : JetGaugeAlgebra) :
    ⁅a, b⁆.toU1Value = 0 := rfl

noncomputable instance : LieRing JetGaugeAlgebra where
  add_lie a b c := by
    ext <;> simp [add_mul, mul_add, smul_add, smul_sub] <;> abel
  lie_add a b c := by
    ext <;> simp [add_mul, mul_add, smul_add, smul_sub] <;> abel
  lie_self a := by
    ext <;> simp
  leibniz_lie a b c := by
    refine ext_of_matrix ?_ ?_ ?_ <;>
      simp only [bracket_toSU3Matrix, bracket_toSU2Matrix, bracket_toU1Value,
        add_toSU3Matrix, add_toSU2Matrix, add_toU1Value, mul_smul_comm, smul_mul_assoc,
        smul_smul, Complex.I_mul_I, smul_sub, mul_sub, sub_mul, mul_assoc, add_zero] <;>
      module

noncomputable instance : LieAlgebra ℝ JetGaugeAlgebra where
  lie_smul r a b := by refine ext_of_matrix ?_ ?_ ?_ <;> simp <;> module

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

@[simp]
lemma deriv_toSU3Matrix (μ : Fin 1 ⊕ Fin 3) (a : JetGaugeAlgebra) :
    (deriv μ a).toSU3Matrix = a.toSU3Matrix.map (pderiv ℂ μ) := rfl

@[simp]
lemma deriv_toSU2Matrix (μ : Fin 1 ⊕ Fin 3) (a : JetGaugeAlgebra) :
    (deriv μ a).toSU2Matrix = a.toSU2Matrix.map (pderiv ℂ μ) := rfl

@[simp]
lemma deriv_toU1Value (μ : Fin 1 ⊕ Fin 3) (a : JetGaugeAlgebra) :
    (deriv μ a).toU1Value = pderiv ℂ μ a.toU1Value := rfl

/-- Formal derivatives on the jet gauge algebra commute. -/
lemma deriv_comm (μ ν : Fin 1 ⊕ Fin 3) (a : JetGaugeAlgebra) :
    deriv μ (deriv ν a) = deriv ν (deriv μ a) := by
  refine ext_of_matrix ?_ ?_ ?_
  · ext i j : 1
    simp [Matrix.map_apply, JetRing.pderiv_comm μ ν]
  · ext i j : 1
    simp [Matrix.map_apply, JetRing.pderiv_comm μ ν]
  · exact JetRing.pderiv_comm μ ν _

/-- Post-composition with `deriv` is right-commutative, since formal derivatives
  commute (`deriv_comm`). This is what allows iterated derivatives to be indexed by a
  `Multiset` of directions. -/
instance : RightCommutative
    (fun (D : JetGaugeAlgebra →ₗ[ℝ] JetGaugeAlgebra) (μ : Fin 1 ⊕ Fin 3) => D.comp (deriv μ)) where
  right_comm D μ ν := by
    refine LinearMap.ext fun a => ?_
    exact congrArg D (deriv_comm μ ν a)

/-- The iterated formal derivative on the jet gauge algebra, in the (unordered, since
  derivatives commute) directions given by the multiset `μs`. -/
noncomputable def iteratedDeriv (μs : Multiset (Fin 1 ⊕ Fin 3)) :
    JetGaugeAlgebra →ₗ[ℝ] JetGaugeAlgebra :=
  μs.foldl (fun D μ => D.comp (deriv μ)) LinearMap.id

@[simp]
lemma iteratedDeriv_zero : iteratedDeriv 0 = LinearMap.id := by
  simp [iteratedDeriv]

/-!

## The basis

-/

TODO "Define the basis of the jet gauge algebra."


/-!

## The adjoint representation of Jet Gauge group

-/

/-- The adjoint action of an element `U` of the jet gauge group on the jet gauge algebra,
  acting on the `su(3)` and `su(2)` factors by `a ↦ U a U⁻¹`, with `U⁻¹ = star U` by
  unitarity, and trivially on the `u(1)` factor since `JetRing` is commutative.
  Hermiticity is preserved since `star (U a (star U)) = U (star a) (star U)`, and
  tracelessness since the trace is invariant under conjugation. -/
noncomputable def adjointMap (U : JetGaugeGroupI) : JetGaugeAlgebra →ₗ[ℝ] JetGaugeAlgebra where
  toFun a := ofMatrixProd
      (U.1.1 * a.toSU3Matrix * star U.1.1,
        U.2.1.1 * a.toSU2Matrix * star U.2.1.1,
        a.toU1Value)
      ⟨by
        rw [star_mul, star_mul, star_star,
          show star a.toSU3Matrix = a.toSU3Matrix from a.1.2.1, mul_assoc],
        by
        rw [Matrix.trace_mul_comm, ← mul_assoc,
          show star U.1.1 * U.1.1 = 1 from mem_unitaryGroup_iff'.mp
            (mem_specialUnitaryGroup_iff.mp U.1.2).1,
          one_mul, show a.toSU3Matrix.trace = 0 from a.1.2.2]⟩
      ⟨by
        rw [star_mul, star_mul, star_star,
          show star a.toSU2Matrix = a.toSU2Matrix from a.2.1.2.1]
        exact (mul_assoc _ _ _).symm,
        by
        rw [Matrix.trace_mul_comm, ← mul_assoc,
          show star U.2.1.1 * U.2.1.1 = 1 from mem_unitaryGroup_iff'.mp
            (mem_specialUnitaryGroup_iff.mp U.2.1.2).1,
          one_mul, show a.toSU2Matrix.trace = 0 from a.2.1.2.2]⟩
      (show star a.toU1Value = a.toU1Value from a.2.2.2)
  map_add' a b := by
    ext <;> simp [mul_add, add_mul]
  map_smul' r a := by
    ext <;> simp

@[simp]
lemma adjointMap_toSU3Matrix (U : JetGaugeGroupI) (a : JetGaugeAlgebra) :
    (adjointMap U a).toSU3Matrix = U.1.1 * a.toSU3Matrix * star U.1.1 := rfl

@[simp]
lemma adjointMap_toSU2Matrix (U : JetGaugeGroupI) (a : JetGaugeAlgebra) :
    (adjointMap U a).toSU2Matrix = U.2.1.1 * a.toSU2Matrix * star U.2.1.1 := rfl

@[simp]
lemma adjointMap_toU1Value (U : JetGaugeGroupI) (a : JetGaugeAlgebra) :
    (adjointMap U a).toU1Value = a.toU1Value := rfl

/-- The adjoint representation of the jet gauge group on the jet gauge algebra,
  `U ↦ (a ↦ U a U⁻¹)` factorwise. -/
noncomputable def adjoint : Representation ℝ JetGaugeGroupI JetGaugeAlgebra where
  toFun := adjointMap
  map_one' := by
    refine LinearMap.ext fun a => ?_
    ext <;> simp
  map_mul' U V := by
    refine LinearMap.ext fun a => ?_
    ext <;> simp [star_mul, mul_assoc]

end JetGaugeAlgebra

end StandardModel
