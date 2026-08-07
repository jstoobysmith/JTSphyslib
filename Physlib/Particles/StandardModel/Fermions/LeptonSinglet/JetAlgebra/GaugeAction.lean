/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.Particles.StandardModel.Fermions.LeptonSinglet.JetAlgebra.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.MaurerCartan
/-!
# The jet gauge action on the charged-lepton jet algebra

## i. Overview

The jet gauge group acts on the jet algebra of the charged-lepton singlet by the
exterior-algebra functor applied to its action on the jet component space. On a
derivative generator `∂_s ψ_α` the action is the all-orders Leibniz rule for the
contragredient hypercharge character `u ^ 6`: each splitting of the derivative
multi-index contributes a Taylor coefficient of the character against a lower
generator.

## ii. Key results

- `JetAlgebra.repJetGaugeGroupI` : the jet gauge action on the jet algebra.
- `JetAlgebra.repJetGaugeGroupI_ofGenerator_ψ` : the all-orders Leibniz rule.
- `JetAlgebra.repJetGaugeGroupIAlgHom` : the action as an algebra homomorphism.

## iii. Table of contents

- A. The action of the jet gauge group

-/

@[expose] public section

namespace StandardModel

namespace LeptonSinglet

namespace JetAlgebra

open TensorProduct LagrangianTheory

/-!

## A. The action of the jet gauge group

-/

/-- The action of the (jet) gauge group on the jet algebra of the lepton singlets. -/
noncomputable def repJetGaugeGroupI : Representation ℂ JetGaugeGroupI JetAlgebra where
  toFun g := (ExteriorAlgebra.map (JetComponentSpace.repJetGaugeGroupI g)).toLinearMap
  map_one' := by
    simp only [map_one, Module.End.one_eq_id, ExteriorAlgebra.map_id,
      AlgHom.toLinearMap_id]
  map_mul' g1 g2 := by
    simp only [map_mul, Module.End.mul_eq_comp, ← ExteriorAlgebra.map_comp_map,
      AlgHom.comp_toLinearMap]

lemma repJetGaugeGroupI_apply (g : JetGaugeGroupI) (x : JetAlgebra) :
    repJetGaugeGroupI g x =
      ExteriorAlgebra.map (JetComponentSpace.repJetGaugeGroupI g) x := rfl

lemma repJetGaugeGroupI_apply_one (g : JetGaugeGroupI) :
    repJetGaugeGroupI g (1 : JetAlgebra) = 1 := by
  simp [repJetGaugeGroupI_apply]

lemma repJetGaugeGroupI_apply_mul (g : JetGaugeGroupI) (x y : JetAlgebra) :
    repJetGaugeGroupI g (x * y) =
      repJetGaugeGroupI g x * repJetGaugeGroupI g y := by
  simp [repJetGaugeGroupI_apply]

/-- The value of the jet of gauge transformations at the base point acts by the
  contragredient hypercharge scalar on the zeroth-order singlet generator, with
  no derivative contributions. -/
lemma repJetGaugeGroupI_ofGenerator_ψ_nil (g : JetGaugeGroupI) (α : Fin 2) :
    repJetGaugeGroupI g (ofGenerator (.dψ {} α)) =  g.eval.2.2 ^ 6 • ofGenerator (.dψ {} α) := by
  rw [ofGenerator, repJetGaugeGroupI_apply, ExteriorAlgebra.map_apply_ι,
    JetComponentSpace.basis_dψ_nil, Submonoid.smul_def]
  simp only [JetComponentSpace.repJetGaugeGroupI, Representation.prod_apply_apply,
    Representation.tprod_apply, dualJetAlgebraRepJetGaugeGroupI_apply,
    Representation.trivial_apply, map_zero, TensorProduct.map_tmul,
    DerivAlgebraComplex.jetRingAction_apply_one, map_pow, ← TensorProduct.smul_tmul',
    SubmonoidClass.coe_pow, ← map_smul, Prod.smul_mk, smul_zero]
  rfl


/-- The action of the gauge group on ∂_μ ψ takes it to
  g • (∂_μ ψ + 6 i (maurerCartanU1Coeff g μ 0) • ψ)-/
lemma repJetGaugeGroupI_ofGenerator_ψ_singleton (g : JetGaugeGroupI)
      (μ : (Fin 1 ⊕ Fin 3)) (α : Fin 2) :
    repJetGaugeGroupI g (ofGenerator (.dψ {μ} α)) =
      g.eval.2.2 ^ 6 • ofGenerator (.dψ {μ} α) -
        ((6 : ℂ) * Complex.I * (maurerCartanU1Coeff g μ 0 : ℂ) * (g.eval.2.2 : ℂ) ^ 6) •
          ofGenerator (.dψ {} α) := by
  have hval : ((g.eval.2.2 : unitary ℂ) : ℂ) =
      MvPowerSeries.constantCoeff ((g.2.2 : unitary JetRing) : JetRing) := rfl
  have hcoeff : MvPowerSeries.coeff (Finsupp.single μ 1)
      (((g.2.2 : unitary JetRing) : JetRing) ^ 6) =
      -((6 : ℂ) * Complex.I * (maurerCartanU1Coeff g μ 0 : ℂ) *
        MvPowerSeries.constantCoeff ((g.2.2 : unitary JetRing) : JetRing) ^ 6) := by
    have h := congrArg (MvPowerSeries.coeff (0 : (Fin 1 ⊕ Fin 3) →₀ ℕ))
      (pderiv_pow_unitary g μ 6)
    rw [MvPowerSeries.coeff_pderiv] at h
    simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_pow,
      MvPowerSeries.constantCoeff_C, Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero,
      zero_add, mul_one] at h
    rw [show ((maurerCartanU1Coeff g μ 0 : selfAdjoint ℂ) : ℂ) =
        MvPowerSeries.constantCoeff (maurerCartanU1 g μ) from
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply _, h]
    push_cast
    ring
  have hinl : ∀ x : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
      Module.Dual ℂ LeptonSinglet,
      (x, (0 : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
        Module.Dual ℂ (ConjModule LeptonSinglet))) =
      LinearMap.inl ℂ _ _ x := fun x => rfl
  simp only [ofGenerator, repJetGaugeGroupI_apply, ExteriorAlgebra.map_apply_ι,
    JetComponentSpace.basis_dψ_singleton, JetComponentSpace.basis_dψ_nil,
    JetComponentSpace.repJetGaugeGroupI, Representation.prod_apply_apply,
    Representation.tprod_apply, dualJetAlgebraRepJetGaugeGroupI_apply,
    Representation.trivial_apply, map_zero, TensorProduct.map_tmul,
    DerivAlgebraComplex.jetRingAction_apply_ι, hcoeff, TensorProduct.add_tmul,
    ← TensorProduct.smul_tmul', Submonoid.smul_def, SubmonoidClass.coe_pow,
    hval, map_pow, sub_eq_add_neg, neg_smul]
  simp only [hinl, TensorProduct.neg_tmul, ← TensorProduct.smul_tmul',
    map_add, map_neg, map_smul]

/-- The jet gauge action on a general singlet generator: the all-orders Leibniz
  rule. A jet of gauge transformations acts on the derivative generator
  `∂_s ψ_α` through the Taylor coefficients of its contragredient hypercharge
  power series `u ^ 6`: each splitting `s = p.1 + p.2` contributes the `p.1`-th
  Taylor coefficient, with the divided-power multiplicity, times the lower
  generator `∂_{p.2} ψ_α`. The zeroth- and first-order cases are
  `repJetGaugeGroupI_ofGenerator_ψ_nil` and
  `repJetGaugeGroupI_ofGenerator_ψ_singleton`. -/
lemma repJetGaugeGroupI_ofGenerator_ψ (g : JetGaugeGroupI)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (α : Fin 2) :
    repJetGaugeGroupI g (ofGenerator (.dψ s α)) =
      ∑ p ∈ Finset.antidiagonal (Multiset.toFinsupp s),
        ((∏ μ, (Multiset.toFinsupp s μ).descFactorial (p.1 μ) : ℕ) : ℂ) •
          MvPowerSeries.coeff p.1 (((g.2.2 : unitary JetRing) : JetRing) ^ 6) •
            ofGenerator (.dψ (Finsupp.toMultiset p.2) α) := by
  have hinl : ∀ x : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
      Module.Dual ℂ LeptonSinglet,
      (x, (0 : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
        Module.Dual ℂ (ConjModule LeptonSinglet))) =
      LinearMap.inl ℂ _ _ x := fun x => rfl
  simp only [ofGenerator, repJetGaugeGroupI_apply, ExteriorAlgebra.map_apply_ι,
    JetComponentSpace.basis_dψ, DerivAlgebraComplex.basis_apply, Finsupp.toMultiset_toFinsupp,
    JetComponentSpace.repJetGaugeGroupI, Representation.prod_apply_apply,
    Representation.tprod_apply, dualJetAlgebraRepJetGaugeGroupI_apply,
    Representation.trivial_apply, map_zero, TensorProduct.map_tmul,
    DerivAlgebraComplex.jetRingAction_basis]
  simp only [hinl, TensorProduct.sum_tmul, ← TensorProduct.smul_tmul', map_sum, map_smul]

noncomputable def repJetGaugeGroupIAlgHom (g : JetGaugeGroupI) :
    AlgHom ℂ JetAlgebra JetAlgebra where
  toFun := repJetGaugeGroupI g
  map_one' := repJetGaugeGroupI_apply_one g
  map_mul' := repJetGaugeGroupI_apply_mul g
  map_add' := LinearMap.map_add _
  map_zero' := LinearMap.map_zero _
  commutes' := fun r => by simp [repJetGaugeGroupI_apply]

end JetAlgebra

end LeptonSinglet

end StandardModel
