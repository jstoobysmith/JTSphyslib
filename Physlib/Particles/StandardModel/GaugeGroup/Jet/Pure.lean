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
 maurerCartanCoeff : PureJetGaugeGroup → { r : Multiset (Fin 1 ⊕ Fin 3) // r ≠ 0 } → LieAlgebra
```
Defined through the symmetrised Maurer-Cartan form, as
```
  U, r ↦ 1/|r| ∑_{ν ∈ r} ∂_{r − ν}| ω_ν(U).
```
This map is a bijection, i.e. `Function.Bijective maurerCartanCoeff`.
This is the uncurried version i.e. `U ↦ (r ↦ maurerCartanCoeff U r)`.

-/

@[expose] public section

namespace StandardModel

namespace JetGaugeGroup

/-- The subgroup of `JetGaugeGroupI` consisting of those gauge transformations
  where the constant part is unity: the kernel of evaluation at the base
  point, `JetGaugeGroupI.eval`. -/
noncomputable def PureSubgroup : Subgroup JetGaugeGroupI := JetGaugeGroupI.eval.ker

namespace PureSubgroup

instance : Subgroup.Normal (PureSubgroup) :=
  inferInstanceAs (Subgroup.Normal (JetGaugeGroupI.eval.ker))

lemma mem_iff {U : JetGaugeGroupI} : U ∈ PureSubgroup ↔ U.eval = 1 := by
  rw [PureSubgroup]
  rfl

@[simp]
lemma eval_ceo_mem (U : PureSubgroup) : U.1.eval = 1 := by
  rcases U with ⟨U, hU⟩
  rw [mem_iff] at hU
  exact hU

lemma self_mul_ofConstant_eval_mem (U : JetGaugeGroupI) :
    U * (JetGaugeGroupI.ofConstant U.eval)⁻¹ ∈ PureSubgroup := by
  rw [mem_iff]
  simp

/-!

## The projection from `JetGaugeGroupI` onto `PureSubgroup`

-/

/-- The projection from `JetGaugeGroupI` onto `PureSubgroup`. This is
  not a group homomorphism. -/
noncomputable def proj (U : JetGaugeGroupI) : PureSubgroup :=
  ⟨U * (JetGaugeGroupI.ofConstant U.eval)⁻¹ , self_mul_ofConstant_eval_mem U⟩

lemma proj_surjective : Function.Surjective proj := by
  intro U
  use (U : JetGaugeGroupI)
  simp [proj]

lemma proj_eq_one_iff_constant {U : JetGaugeGroupI} :
    proj U = 1 ↔ ∃ c, U = .ofConstant c := by
  constructor
  · intro h
    refine ⟨U.eval, ?_⟩
    have h1 : U * (JetGaugeGroupI.ofConstant U.eval)⁻¹ = 1 := congrArg Subtype.val h
    exact mul_inv_eq_one.mp h1
  · rintro ⟨c, rfl⟩
    apply Subtype.ext
    simp [proj]

lemma proj_ofConstant (c : GaugeGroupI) : proj (JetGaugeGroupI.ofConstant c) = 1 := by
  rw [proj_eq_one_iff_constant]
  exact ⟨c, rfl⟩

lemma eq_proj_mul_ofConstant (U : JetGaugeGroupI) :
    U = proj U * JetGaugeGroupI.ofConstant U.eval := by
  simp [proj]

end PureSubgroup

end JetGaugeGroup
end StandardModel
