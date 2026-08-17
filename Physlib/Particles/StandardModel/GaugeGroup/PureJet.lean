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
# The pure Jet gauge group

Within `JetGaugeGroupI` there is a subgroup for which `U₀ = 1`,
that is those elements whose constant part is the identity. We call this
the pure Jet gauge group, and denote it `PureJetGaugeGroup`.
This is simply the kernel of the map `JetGaugeGroupI → GaugeGroupI` given by `U ↦ U₀`,
and therefore is a normal subgroup of `JetGaugeGroupI`.

Every element `U ∈ PureJetGaugeGroup` uniquely factors as `U = (U U₀⁻¹) · U₀` with
`U U₀⁻¹ : PureJetGaugeGroup`. This gives a splitting of `JetGaugeGroupI` as
a semi-direct product of `PureJetGaugeGroup` and `GaugeGroupI`.

There exists a map:
```
 maurerCartanCoeff : PureJetGaugeGroup → { r : Multiset (Fin 1 ⊕ Fin 3) // r ≠ 0 } → JetLieAlgebra
```
Defined through the symmetrised Maurer-Cartan form, as
```
  U, r ↦ 1/|r| ∑_{ν ∈ r} ∂_{r − ν}| ω_ν(U).
```
This map is a bijection, i.e. `Function.Bijective maurerCartanCoeff`.
This is the uncurried version i.e. `U ↦ (r ↦ maurerCartanCoeff U r)`.

-/

@[expose] public section
