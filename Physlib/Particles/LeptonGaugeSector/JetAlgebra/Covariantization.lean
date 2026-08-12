/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.Terms.KineticTerms
/-!
# Covariantization of charged-lepton jets

This file provides compatibility properties of `covExtHom` (defined in `CovariantAlgebra.lean`),
which sends ordinary charged-lepton jets to ordered covariant derivatives in the mixed
lepton–gauge-sector jet algebra.

The map is distinct from `covSubst` as `covExtHom` acts only on the matter algebra, while `covSubst`
extends it over the B-boson factor as a coordinate equivalence of the whole mixed algebra.

At derivative order two and above, `covExtHom` uses `sortList` to choose an ordering of covariant
derivatives. Consequently, the Lorentz compatibility API in this file is restricted to derivative
orders zero and one.
-/

@[expose] public section

namespace LeptonGaugeSector
open TensorProduct StandardModel

namespace JetAlgebra

open Matrix MatrixGroups

/-!

## A. Gauge compatibility

-/

/-- Applying a jet gauge transformation after covariantization is the same as first applying its
value at the base point to the ordinary lepton jets and then covariantizing the result. -/
lemma repJetGaugeGroupI_covExtHom (U : JetGaugeGroupI)
    (x : LeptonSinglet.JetAlgebra) :
    repJetGaugeGroupI U (covExtHom x) =
      covExtHom (LeptonSinglet.JetAlgebra.repGaugeGroupI U.eval x) := by
  have hhom : (repAlgHom U).comp covExtHom =
      covExtHom.comp (LeptonSinglet.JetAlgebra.repJetGaugeGroupIAlgHom
        (JetGaugeGroupI.ofConstant U.eval)) := by
    refine ExteriorAlgebra.hom_ext (LinearMap.ext fun m => ?_)
    simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, Function.comp_apply,
      AlgHom.toLinearMap_apply, covExtHom_ι]
    have hlin : (repAlgHom U).toLinearMap ∘ₗ covMap =
        covExtHom.toLinearMap ∘ₗ
          (LeptonSinglet.JetAlgebra.repGaugeGroupI U.eval ∘ₗ ExteriorAlgebra.ι ℂ) := by
      refine LeptonSinglet.JetComponentSpace.basis.ext fun g => ?_
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, covMap_basis,
        AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply,
        ← repJetGaugeGroupI_eq_repAlgHom]
      cases g with
      | dψ s α =>
          rw [show covGenerator (.dψ s α) = Dψ (sortList s) α from rfl,
            repJetGaugeGroupI_Dψ]
          rw [show ExteriorAlgebra.ι ℂ
              (LeptonSinglet.JetComponentSpace.basis (.dψ s α)) =
            LeptonSinglet.JetAlgebra.ofGenerator (.dψ s α) from rfl,
            LeptonSinglet.JetAlgebra.repGaugeGroupI_ofGenerator_ψ, map_smul]
          rw [show LeptonSinglet.JetAlgebra.ofGenerator (.dψ s α) =
              ExteriorAlgebra.ι ℂ
                (LeptonSinglet.JetComponentSpace.basis (.dψ s α)) from rfl,
            covExtHom_ι, covMap_basis]
          rfl
      | dbarψ s α =>
          rw [show covGenerator (.dbarψ s α) = Dbarψ (sortList s) α from rfl,
            repJetGaugeGroupI_Dbarψ]
          rw [show ExteriorAlgebra.ι ℂ
              (LeptonSinglet.JetComponentSpace.basis (.dbarψ s α)) =
            LeptonSinglet.JetAlgebra.ofGenerator (.dbarψ s α) from rfl,
            LeptonSinglet.JetAlgebra.repGaugeGroupI_ofGenerator_barψ, map_smul]
          rw [show LeptonSinglet.JetAlgebra.ofGenerator (.dbarψ s α) =
              ExteriorAlgebra.ι ℂ
                (LeptonSinglet.JetComponentSpace.basis (.dbarψ s α)) from rfl,
            covExtHom_ι, covMap_basis]
          rfl
    exact LinearMap.congr_fun hlin m
  rw [repJetGaugeGroupI_eq_repAlgHom]
  exact AlgHom.congr_fun hhom x

/-- A gauge jet whose value at the base point is the identity fixes every covariantized
charged-lepton expression. -/
lemma repJetGaugeGroupI_covExtHom_of_eval_eq_one (U : JetGaugeGroupI)
    (hU : U.eval = 1) (x : LeptonSinglet.JetAlgebra) :
    repJetGaugeGroupI U (covExtHom x) = covExtHom x := by
  rw [repJetGaugeGroupI_covExtHom, hU, map_one, Module.End.one_apply]

/-- An ordinary charged-lepton expression invariant under constant gauge transformations becomes
invariant under all jet gauge transformations after covariantization. -/
lemma repJetGaugeGroupI_covExtHom_eq_self (x : LeptonSinglet.JetAlgebra)
    (hx : ∀ g : GaugeGroupI, LeptonSinglet.JetAlgebra.repGaugeGroupI g x = x)
    (U : JetGaugeGroupI) :
    repJetGaugeGroupI U (covExtHom x) = covExtHom x := by
  rw [repJetGaugeGroupI_covExtHom, hx U.eval]

/-!

## B. Mass-weight compatibility

-/

/-- Covariantization preserves the mass-weight polynomial. -/
lemma massWeightPoly_covExtHom (x : LeptonSinglet.JetAlgebra) :
    massWeightPoly (covExtHom x) =
      Polynomial.mapAlgHom covExtHom (LeptonSinglet.JetAlgebra.massWeightPoly x) := by
  have hhom : massWeightPoly.comp covExtHom =
      (Polynomial.mapAlgHom covExtHom).comp LeptonSinglet.JetAlgebra.massWeightPoly := by
    refine ExteriorAlgebra.hom_ext (LinearMap.ext fun m => ?_)
    simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, Function.comp_apply,
      AlgHom.toLinearMap_apply, covExtHom_ι]
    have hlin : massWeightPoly.toLinearMap ∘ₗ covMap =
        (Polynomial.mapAlgHom covExtHom).toLinearMap ∘ₗ
          (LeptonSinglet.JetAlgebra.massWeightPoly.toLinearMap ∘ₗ ExteriorAlgebra.ι ℂ) := by
      refine LeptonSinglet.JetComponentSpace.basis.ext fun g => ?_
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, covMap_basis]
      cases g with
      | dψ s α =>
          rw [show covGenerator (.dψ s α) = Dψ (sortList s) α from rfl]
          rw [show ExteriorAlgebra.ι ℂ
              (LeptonSinglet.JetComponentSpace.basis (.dψ s α)) =
              LeptonSinglet.JetAlgebra.ofGenerator (.dψ s α) from rfl,
            LeptonSinglet.JetAlgebra.massWeightPoly_ofGenerator,
            Polynomial.mapAlgHom_monomial]
          rw [show covExtHom (LeptonSinglet.JetAlgebra.ofGenerator (.dψ s α)) =
              Dψ (sortList s) α from by
            rw [show LeptonSinglet.JetAlgebra.ofGenerator (.dψ s α) =
              ExteriorAlgebra.ι ℂ
                  (LeptonSinglet.JetComponentSpace.basis (.dψ s α)) from rfl,
              covExtHom_ι, covMap_basis]
            rfl]
          have h := Dψ_mem_massWeightSubmodule (sortList s) α
          rw [mem_massWeightSubmodule] at h
          simpa [LeptonSinglet.JetGenerators.massWeight, length_sortList] using h
      | dbarψ s α =>
          rw [show covGenerator (.dbarψ s α) = Dbarψ (sortList s) α from rfl]
          rw [show ExteriorAlgebra.ι ℂ
              (LeptonSinglet.JetComponentSpace.basis (.dbarψ s α)) =
              LeptonSinglet.JetAlgebra.ofGenerator (.dbarψ s α) from rfl,
            LeptonSinglet.JetAlgebra.massWeightPoly_ofGenerator,
            Polynomial.mapAlgHom_monomial]
          rw [show covExtHom (LeptonSinglet.JetAlgebra.ofGenerator (.dbarψ s α)) =
              Dbarψ (sortList s) α from by
            rw [show LeptonSinglet.JetAlgebra.ofGenerator (.dbarψ s α) =
              ExteriorAlgebra.ι ℂ
                  (LeptonSinglet.JetComponentSpace.basis (.dbarψ s α)) from rfl,
              covExtHom_ι, covMap_basis]
            rfl]
          have h := Dbarψ_mem_massWeightSubmodule (sortList s) α
          rw [mem_massWeightSubmodule] at h
          simpa [LeptonSinglet.JetGenerators.massWeight, length_sortList] using h
    exact LinearMap.congr_fun hlin m
  exact AlgHom.congr_fun hhom x

/-!

## C. Lorentz compatibility at derivative orders zero and one

-/

/-- Covariantization is compatible with Lorentz transformations on a zeroth-order lepton
generator. -/
lemma repLorentzGroup_covExtHom_ofGenerator_ψ_nil (Λ : SL(2,ℂ)) (α : Fin 2) :
    repLorentzGroup Λ
        (covExtHom (LeptonSinglet.JetAlgebra.ofGenerator (.dψ {} α))) =
      covExtHom (LeptonSinglet.JetAlgebra.repLorentzGroup Λ
        (LeptonSinglet.JetAlgebra.ofGenerator (.dψ {} α))) := by
  rw [show covExtHom (LeptonSinglet.JetAlgebra.ofGenerator (.dψ {} α)) = Dψ [] α from by
    rw [show LeptonSinglet.JetAlgebra.ofGenerator (.dψ {} α) = ExteriorAlgebra.ι ℂ
        (LeptonSinglet.JetComponentSpace.basis (.dψ {} α)) from rfl,
      covExtHom_ι, covMap_basis]
    simp [covGenerator, sortList]]
  rw [repLorentzGroup_Dψ_nil,
    LeptonSinglet.JetAlgebra.repLorentzGroup_ofGenerator_ψ_nil, map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul]
  congr 1
  rw [show LeptonSinglet.JetAlgebra.ofGenerator (.dψ {} β) = ExteriorAlgebra.ι ℂ
      (LeptonSinglet.JetComponentSpace.basis (.dψ {} β)) from rfl,
    covExtHom_ι, covMap_basis]
  simp [covGenerator, sortList]

/-- Covariantization is compatible with Lorentz transformations on a first-order lepton
generator. -/
lemma repLorentzGroup_covExtHom_ofGenerator_ψ_singleton (Λ : SL(2,ℂ))
    (μ : Fin 1 ⊕ Fin 3) (α : Fin 2) :
    repLorentzGroup Λ
        (covExtHom (LeptonSinglet.JetAlgebra.ofGenerator (.dψ {μ} α))) =
      covExtHom (LeptonSinglet.JetAlgebra.repLorentzGroup Λ
        (LeptonSinglet.JetAlgebra.ofGenerator (.dψ {μ} α))) := by
  rw [show covExtHom (LeptonSinglet.JetAlgebra.ofGenerator (.dψ {μ} α)) = Dψ [μ] α from by
    rw [show LeptonSinglet.JetAlgebra.ofGenerator (.dψ {μ} α) = ExteriorAlgebra.ι ℂ
        (LeptonSinglet.JetComponentSpace.basis (.dψ {μ} α)) from rfl,
      covExtHom_ι, covMap_basis]
    simp [covGenerator, sortList]]
  rw [repLorentzGroup_Dψ_singleton,
    LeptonSinglet.JetAlgebra.repLorentzGroup_ofGenerator_ψ_singleton, map_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul]
  congr 1
  rw [show LeptonSinglet.JetAlgebra.ofGenerator (.dψ {ν} β) = ExteriorAlgebra.ι ℂ
      (LeptonSinglet.JetComponentSpace.basis (.dψ {ν} β)) from rfl,
    covExtHom_ι, covMap_basis]
  simp [covGenerator, sortList]

/-- Covariantization is compatible with Lorentz transformations on a zeroth-order conjugate
lepton generator. -/
lemma repLorentzGroup_covExtHom_ofGenerator_barψ_nil (Λ : SL(2,ℂ)) (α : Fin 2) :
    repLorentzGroup Λ
        (covExtHom (LeptonSinglet.JetAlgebra.ofGenerator (.dbarψ {} α))) =
      covExtHom (LeptonSinglet.JetAlgebra.repLorentzGroup Λ
        (LeptonSinglet.JetAlgebra.ofGenerator (.dbarψ {} α))) := by
  rw [show covExtHom (LeptonSinglet.JetAlgebra.ofGenerator (.dbarψ {} α)) =
      Dbarψ [] α from by
    rw [show LeptonSinglet.JetAlgebra.ofGenerator (.dbarψ {} α) = ExteriorAlgebra.ι ℂ
        (LeptonSinglet.JetComponentSpace.basis (.dbarψ {} α)) from rfl,
      covExtHom_ι, covMap_basis]
    simp [covGenerator, sortList]]
  rw [repLorentzGroup_Dbarψ_nil,
    LeptonSinglet.JetAlgebra.repLorentzGroup_ofGenerator_barψ_nil, map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul]
  congr 1
  rw [show LeptonSinglet.JetAlgebra.ofGenerator (.dbarψ {} β) = ExteriorAlgebra.ι ℂ
      (LeptonSinglet.JetComponentSpace.basis (.dbarψ {} β)) from rfl,
    covExtHom_ι, covMap_basis]
  simp [covGenerator, sortList]

/-- Covariantization is compatible with Lorentz transformations on a first-order conjugate
lepton generator. -/
lemma repLorentzGroup_covExtHom_ofGenerator_barψ_singleton (Λ : SL(2,ℂ))
    (μ : Fin 1 ⊕ Fin 3) (α : Fin 2) :
    repLorentzGroup Λ
        (covExtHom (LeptonSinglet.JetAlgebra.ofGenerator (.dbarψ {μ} α))) =
      covExtHom (LeptonSinglet.JetAlgebra.repLorentzGroup Λ
        (LeptonSinglet.JetAlgebra.ofGenerator (.dbarψ {μ} α))) := by
  rw [show covExtHom (LeptonSinglet.JetAlgebra.ofGenerator (.dbarψ {μ} α)) =
      Dbarψ [μ] α from by
    rw [show LeptonSinglet.JetAlgebra.ofGenerator (.dbarψ {μ} α) = ExteriorAlgebra.ι ℂ
        (LeptonSinglet.JetComponentSpace.basis (.dbarψ {μ} α)) from rfl,
      covExtHom_ι, covMap_basis]
    simp [covGenerator, sortList]]
  rw [repLorentzGroup_Dbarψ_singleton,
    LeptonSinglet.JetAlgebra.repLorentzGroup_ofGenerator_barψ_singleton, map_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul]
  congr 1
  rw [show LeptonSinglet.JetAlgebra.ofGenerator (.dbarψ {ν} β) = ExteriorAlgebra.ι ℂ
      (LeptonSinglet.JetComponentSpace.basis (.dbarψ {ν} β)) from rfl,
    covExtHom_ι, covMap_basis]
  simp [covGenerator, sortList]

end JetAlgebra

end LeptonGaugeSector

namespace StandardModel

namespace LeptonSinglet

namespace JetAlgebra

open Matrix MatrixGroups

/-!

## D. The fermion kinetic term

-/

/-- The ordinary-jet charged-lepton kinetic expression. Covariantization sends this expression to
`LeptonGaugeSector.JetAlgebra.fermionKineticTerm`. -/
noncomputable def fermionKineticTerm : LeptonSinglet.JetAlgebra :=
  Complex.I • ∑ μ, ∑ α, ∑ β, LeptonGaugeSector.JetAlgebra.kineticPauli μ α β •
    (ofGenerator (.dbarψ {} α) * ofGenerator (.dψ {μ} β))

/-- The hypercharge factors of an ordinary conjugate-lepton/lepton generator pair cancel. -/
lemma repGaugeGroupI_barψ_mul_ψ
    (g : GaugeGroupI) (s t : Multiset (Fin 1 ⊕ Fin 3)) (α β : Fin 2) :
    repGaugeGroupI g (ofGenerator (.dbarψ s α) * ofGenerator (.dψ t β)) =
      ofGenerator (.dbarψ s α) * ofGenerator (.dψ t β) := by
  have hz : star ((g.toU1 : unitary ℂ) : ℂ) * ((g.toU1 : unitary ℂ) : ℂ) = 1 :=
    (Unitary.mem_iff.mp g.toU1.2).1
  rw [repGaugeGroupI_apply_mul, repGaugeGroupI_ofGenerator_barψ,
    repGaugeGroupI_ofGenerator_ψ, smul_mul_smul_comm, ← mul_pow, hz, one_pow, one_smul]

/-- Constant-gauge invariance of the ordinary-jet charged-lepton kinetic expression. -/
lemma repGaugeGroupI_fermionKineticTerm
    (g : GaugeGroupI) :
    repGaugeGroupI g fermionKineticTerm = fermionKineticTerm := by
  rw [fermionKineticTerm, map_smul]
  congr 1
  rw [map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul, repGaugeGroupI_barψ_mul_ψ]

/-- Lorentz invariance of the ordinary-jet charged-lepton kinetic expression. -/
lemma repLorentzGroup_fermionKineticTerm
    (Λ : SL(2,ℂ)) :
    repLorentzGroup Λ fermionKineticTerm = fermionKineticTerm := by
  have hsmF : ∀ (f : Fin 2 → LeptonSinglet.JetAlgebra) (y : LeptonSinglet.JetAlgebra),
      (∑ x, f x) * y = ∑ x, f x * y := fun f y => by
    rw [show (∑ x, f x) * y = LinearMap.mulRight ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hmsS : ∀ (f : (Fin 1 ⊕ Fin 3) → LeptonSinglet.JetAlgebra)
      (y : LeptonSinglet.JetAlgebra), y * (∑ x, f x) = ∑ x, y * f x := fun f y => by
    rw [show y * (∑ x, f x) = LinearMap.mulLeft ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hmsF : ∀ (f : Fin 2 → LeptonSinglet.JetAlgebra) (y : LeptonSinglet.JetAlgebra),
      y * (∑ x, f x) = ∑ x, y * f x := fun f y => by
    rw [show y * (∑ x, f x) = LinearMap.mulLeft ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hsmul : ∀ (c d : ℂ) (x y : LeptonSinglet.JetAlgebra),
      (c • x) * (d • y) = (c * d) • (x * y) := fun c d x y => by
    rw [smul_mul_smul_comm]
  rw [fermionKineticTerm, map_smul]
  congr 1
  rw [map_sum]
  conv_lhs => enter [2, μ]; rw [map_sum]
  conv_lhs => enter [2, μ, 2, α]; rw [map_sum]
  conv_lhs =>
    enter [2, μ, 2, α, 2, β]
    rw [map_smul, repLorentzGroup_apply_mul, repLorentzGroup_ofGenerator_barψ_nil,
      repLorentzGroup_ofGenerator_ψ_singleton]
  simp only [hsmF, hmsS, hmsF, hsmul, Finset.smul_sum, smul_smul]
  -- Move the transformed indices outside the original contraction sums.
  conv_lhs => enter [2, μ, 2, α]; rw [Finset.sum_comm]
  conv_lhs => enter [2, μ, 2, α, 2, α']; rw [Finset.sum_comm]
  conv_lhs => enter [2, μ, 2, α, 2, α', 2, ν]; rw [Finset.sum_comm]
  conv_lhs => enter [2, μ]; rw [Finset.sum_comm]
  conv_lhs => enter [2, μ, 2, α']; rw [Finset.sum_comm]
  conv_lhs => enter [2, μ, 2, α', 2, ν]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, α']; rw [Finset.sum_comm]
  conv_lhs => enter [2, α', 2, ν]; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α' _ => Finset.sum_congr rfl fun ν _ =>
    Finset.sum_congr rfl fun β' _ => ?_
  conv_lhs => enter [2, μ, 2, α]; rw [← Finset.sum_smul]
  conv_lhs => enter [2, μ]; rw [← Finset.sum_smul]
  rw [← Finset.sum_smul]
  -- The remaining scalar coefficient is the existing Pauli-matrix contraction identity.
  rw [show (∑ μ, ∑ α, ∑ β, LeptonGaugeSector.JetAlgebra.kineticPauli μ α β *
      ((Λ⁻¹).1 α α' * ((((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) *
        star ((Λ⁻¹).1 β β')))) =
      LeptonGaugeSector.JetAlgebra.kineticPauli ν α' β' from
    LeptonGaugeSector.JetAlgebra.sum_kineticPauli_contraction Λ ν α' β']

end JetAlgebra

end LeptonSinglet

end StandardModel

namespace LeptonGaugeSector
open TensorProduct StandardModel

namespace JetAlgebra

open Matrix MatrixGroups

/-- Covariantization maps the ordinary-jet kinetic expression to the existing covariant kinetic
term in the mixed algebra. -/
lemma covExtHom_fermionKineticTerm :
    covExtHom LeptonSinglet.JetAlgebra.fermionKineticTerm = fermionKineticTerm := by
  rw [LeptonSinglet.JetAlgebra.fermionKineticTerm, fermionKineticTerm, map_smul]
  congr 1
  rw [map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul, map_mul]
  have hbar : covExtHom (LeptonSinglet.JetAlgebra.ofGenerator (.dbarψ {} α)) =
      Dbarψ [] α := by
    rw [show LeptonSinglet.JetAlgebra.ofGenerator (.dbarψ {} α) = ExteriorAlgebra.ι ℂ
        (LeptonSinglet.JetComponentSpace.basis (.dbarψ {} α)) from rfl,
      covExtHom_ι, covMap_basis]
    simp [covGenerator, sortList]
  have hψ : covExtHom (LeptonSinglet.JetAlgebra.ofGenerator (.dψ {μ} β)) = Dψ [μ] β := by
    rw [show LeptonSinglet.JetAlgebra.ofGenerator (.dψ {μ} β) = ExteriorAlgebra.ι ℂ
        (LeptonSinglet.JetComponentSpace.basis (.dψ {μ} β)) from rfl,
      covExtHom_ι, covMap_basis]
    simp [covGenerator, sortList]
  rw [hbar, hψ]

/-- Lorentz compatibility of covariantization on the ordinary-jet kinetic expression, obtained
from the order-zero and order-one generator compatibility lemmas. -/
lemma repLorentzGroup_covExtHom_fermionKineticTerm (Λ : SL(2,ℂ)) :
    repLorentzGroup Λ (covExtHom LeptonSinglet.JetAlgebra.fermionKineticTerm) =
      covExtHom (LeptonSinglet.JetAlgebra.repLorentzGroup Λ
        LeptonSinglet.JetAlgebra.fermionKineticTerm) := by
  rw [LeptonSinglet.JetAlgebra.fermionKineticTerm]
  simp only [map_smul]
  congr 1
  conv_lhs => rw [map_sum, map_sum]
  conv_rhs => rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  conv_lhs => rw [map_sum, map_sum]
  conv_rhs => rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  conv_lhs => rw [map_sum, map_sum]
  conv_rhs => rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  simp only [map_smul]
  congr 1
  rw [map_mul, repLorentzGroup_apply_mul,
    LeptonSinglet.JetAlgebra.repLorentzGroup_apply_mul, map_mul,
    repLorentzGroup_covExtHom_ofGenerator_barψ_nil,
    repLorentzGroup_covExtHom_ofGenerator_ψ_singleton]

/-- A modular gauge-invariance proof of the existing covariant kinetic term through
`covExtHom`. The existing direct proof remains available. -/
lemma repJetGaugeGroupI_fermionKineticTerm_via_covExtHom (U : JetGaugeGroupI) :
    repJetGaugeGroupI U fermionKineticTerm = fermionKineticTerm := by
  rw [← covExtHom_fermionKineticTerm, repJetGaugeGroupI_covExtHom,
    LeptonSinglet.JetAlgebra.repGaugeGroupI_fermionKineticTerm]

/-- A modular Lorentz-invariance proof of the existing covariant kinetic term through
`covExtHom`. The existing direct proof remains available. -/
lemma repLorentzGroup_fermionKineticTerm_via_covExtHom (Λ : SL(2,ℂ)) :
    repLorentzGroup Λ fermionKineticTerm = fermionKineticTerm := by
  rw [← covExtHom_fermionKineticTerm, repLorentzGroup_covExtHom_fermionKineticTerm,
    LeptonSinglet.JetAlgebra.repLorentzGroup_fermionKineticTerm]

end JetAlgebra

end LeptonGaugeSector
