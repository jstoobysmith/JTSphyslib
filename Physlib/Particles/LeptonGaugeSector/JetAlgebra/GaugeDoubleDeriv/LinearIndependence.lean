/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.GaugeKineticTerm.LinearIndependence
/-!
# A dual family for the second derivatives of the field strength

The monomials `∂_ρ ∂_τ F_{μν}` are not linearly independent — the Bianchi identity
`∂_ρ F_{μν} + ∂_μ F_{νρ} + ∂_ν F_{ρμ} = 0` holds identically, `F` being built from `B` — but the
coefficients of a combination of them, read in the gauge-field generators `∂_s B_μ`, can still
be extracted one by one. This file constructs the functionals that extract them.

*The construction is the first polarization.* A field-strength derivative is linear, not
quadratic, in the gauge-field generators, so where `GaugeKineticTerm.LinearIndependence` needs a
second difference of `symEval` this file needs only the first: `symEval φ - symEval 0` is linear,
kills the constants and sends a degree-one monomial `ι v` to `φ v`. Tensored with the
augmentation of the lepton factor it gives `gaugeDerivDual`, dual to a single gauge-field
generator, and `gaugeDerivDual_fieldStrengthDeriv` evaluates it on a field-strength derivative of
any order.

The second polarization of the same construction — the dual family of the photon pairs — is
recorded here to vanish on the field-strength derivatives
(`gaugePairDual_fieldStrengthDeriv`): a second difference is blind to a linear term. This is
what separates this sector from the photon pairs.

## Key results

- `gaugeDerivDual_fieldStrengthDeriv` : the value of the dual on `∂_s F_{μν}`.
- `gaugePairDual_fieldStrengthDeriv` : the photon-pair duals vanish on a single field-strength
  derivative.

-/

@[expose] public section

namespace LeptonGaugeSector
open TensorProduct StandardModel

namespace JetAlgebra

/-!

## A. The first polarization

-/

/-- The first difference of `symEval`: the functional on the B-boson factor dual to the
  degree-one monomial `φ`. It kills the constants, where the first difference of an affine
  function is blind. -/
noncomputable def symLinDual (φ : BBoson.JetComponentSpace →ₗ[ℝ] ℂ) :
    (ℂ ⊗[ℝ] BBoson.JetAlgebra) →ₗ[ℂ] ℂ :=
  (symEval φ).toLinearMap - (symEval 0).toLinearMap

lemma symLinDual_tmul_ofGenerator (φ : BBoson.JetComponentSpace →ₗ[ℝ] ℂ)
    (g : BBoson.JetGenerators) :
    symLinDual φ (1 ⊗ₜ[ℝ] BBoson.JetAlgebra.ofGenerator g) =
      φ (BBoson.JetComponentSpace.basis g) := by
  simp only [symLinDual, LinearMap.sub_apply, AlgHom.toLinearMap_apply, symEval_tmul_ofGenerator,
    LinearMap.zero_apply, sub_zero]

/-- The functional on the jet algebra dual to a single gauge-field generator: the first
  polarization on the B-boson factor tensored with the augmentation on the lepton factor. -/
noncomputable def gaugeLinDual (φ : BBoson.JetComponentSpace →ₗ[ℝ] ℂ) : JetAlgebra →ₗ[ℂ] ℂ :=
  TensorProduct.lift (((LinearMap.mul ℂ ℂ).comp (symLinDual φ)).compl₂ augL.toLinearMap)

@[simp]
lemma gaugeLinDual_tmul (φ : BBoson.JetComponentSpace →ₗ[ℝ] ℂ)
    (a : ℂ ⊗[ℝ] BBoson.JetAlgebra) (b : LeptonSinglet.JetAlgebra) :
    gaugeLinDual φ (a ⊗ⱼ b) = symLinDual φ a * augL b := rfl

lemma gaugeLinDual_ofGenerator (φ : BBoson.JetComponentSpace →ₗ[ℝ] ℂ)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) :
    gaugeLinDual φ (ofGenerator (JetGenerators.dB s μ)) =
      φ (BBoson.JetComponentSpace.basis (BBoson.JetGenerators.dB s μ)) := by
  rw [ofGenerator_B_eq, gaugeLinDual_tmul, symLinDual_tmul_ofGenerator, map_one, mul_one]

/-!

## B. The dual family for the field-strength derivatives

-/

/-- The coefficient with which the field-strength derivative `∂_s F_{μ ν}` contains the
  gauge-field generator `∂_{p.1} B_{p.2}`. -/
noncomputable def fsDerivCoeff (p : Multiset (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3))
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) : ℂ :=
  (if s + {μ} = p.1 ∧ ν = p.2 then 1 else 0) - (if s + {ν} = p.1 ∧ μ = p.2 then 1 else 0)

/-- The functional dual to the gauge-field generator indexed by `p`. -/
noncomputable def gaugeDerivDual (p : Multiset (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)) :
    JetAlgebra →ₗ[ℂ] ℂ :=
  gaugeLinDual ((BBoson.JetComponentSpace.basis.coord
    (BBoson.JetGenerators.dB p.1 p.2)).smulRight (1 : ℂ))

/-- A field-strength derivative written out on the generators. -/
lemma fieldStrengthDeriv_eq_sub (s : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) :
    fieldStrengthDeriv s μ ν =
      ofGenerator (JetGenerators.dB (s + {μ}) ν) - ofGenerator (JetGenerators.dB (s + {ν}) μ) := by
  rw [fieldStrengthDeriv, BBoson.JetAlgebra.fieldStrengthDeriv, TensorProduct.tmul_sub, sub_tmul]
  rfl

/-- **`gaugeDerivDual` is dual to the gauge-field generators.** Its value on a field-strength
  derivative of any order is the antisymmetric coefficient `fsDerivCoeff`. -/
@[simp]
lemma gaugeDerivDual_fieldStrengthDeriv (p : Multiset (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3))
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) :
    gaugeDerivDual p (fieldStrengthDeriv s μ ν) = fsDerivCoeff p s μ ν := by
  simp only [fieldStrengthDeriv_eq_sub, map_sub, gaugeDerivDual, gaugeLinDual_ofGenerator,
    Module.Basis.coord_apply, Module.Basis.repr_self, LinearMap.smulRight_apply,
    Finsupp.single_apply, BBoson.JetGenerators.dB.injEq, fsDerivCoeff, ite_smul, one_smul,
    zero_smul]

/-!

## C. The photon-pair duals are blind to a single field strength

-/

/-- A second difference vanishes on a degree-one monomial. -/
lemma symPairDual_tmul_ofGenerator_eq_zero (φ ψ : BBoson.JetComponentSpace →ₗ[ℝ] ℂ)
    (g : BBoson.JetGenerators) :
    symPairDual φ ψ (1 ⊗ₜ[ℝ] BBoson.JetAlgebra.ofGenerator g) = 0 := by
  simp only [symPairDual, LinearMap.add_apply, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
    symEval_tmul_ofGenerator, LinearMap.add_apply, LinearMap.zero_apply]
  ring

/-- **The photon-pair duals vanish on a field-strength derivative.** The dual family of
  `GaugeKineticTerm` reads a quadratic coefficient, and a field-strength derivative is linear in
  the gauge-field generators. -/
@[simp]
lemma gaugePairDual_fieldStrengthDeriv (φ ψ : BBoson.JetComponentSpace →ₗ[ℝ] ℂ)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) :
    gaugePairDual φ ψ (fieldStrengthDeriv s μ ν) = 0 := by
  simp only [fieldStrengthDeriv_eq_sub, map_sub, ofGenerator_B_eq, gaugePairDual_tmul,
    symPairDual_tmul_ofGenerator_eq_zero, zero_mul, sub_zero, sub_self]

@[simp]
lemma gaugeDual_fieldStrengthDeriv (p q : (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3))
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) :
    gaugeDual p q (fieldStrengthDeriv s μ ν) = 0 :=
  gaugePairDual_fieldStrengthDeriv _ _ s μ ν

end JetAlgebra

end LeptonGaugeSector

end
