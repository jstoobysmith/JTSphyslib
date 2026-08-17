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
  gauge group factor — self-adjoint `3 × 3` and `2 × 2` matrices and a self-adjoint scalar,
  all with coefficients in the ring `JetRing` of formal power series in the spacetime
  coordinates. The Maurer–Cartan forms of the jet gauge group are valued here, hermiticity
  being `star_maurerCartanSU3` and its companions. -/
abbrev JetGaugeAlgebra :=
  selfAdjoint (Matrix (Fin 3) (Fin 3) JetRing) ×
  selfAdjoint (Matrix (Fin 2) (Fin 2) JetRing) × selfAdjoint JetRing

namespace JetGaugeAlgebra

/-!

## Basic projections

-/

/-- The `su(3)`-factor component of an element of the jet gauge algebra. -/
def toSU3 (a : JetGaugeAlgebra) : selfAdjoint (Matrix (Fin 3) (Fin 3) JetRing) := a.1

/-- The `su(2)`-factor component of an element of the jet gauge algebra. -/
def toSU2 (a : JetGaugeAlgebra) : selfAdjoint (Matrix (Fin 2) (Fin 2) JetRing) := a.2.1

/-- The `u(1)`-factor component of an element of the jet gauge algebra. -/
def toU1 (a : JetGaugeAlgebra) : selfAdjoint JetRing := a.2.2

/-!

## The Lie algebra instance

-/

TODO "Define the Lie algebra instance on `JetGaugeAlgebra`."

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
