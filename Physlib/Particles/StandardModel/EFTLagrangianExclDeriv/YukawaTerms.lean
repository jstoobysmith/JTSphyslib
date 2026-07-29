/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Jinzheng Li, Nathaneal Sajan
-/
module

public import Physlib.Particles.StandardModel.EFTLagrangianExclDeriv.Basic
/-!

# The Yukawa terms in the EFT lagrangian

-/

@[expose] public section

namespace StandardModel
noncomputable section

open Module Matrix
open MatrixGroups
open Complex
open TensorProduct
open CategoryTheory.MonoidalCategory
open Fermion

/-!

## The action of the representations on the basis of the target spaces

-/

namespace LeptonDoublet

lemma repLorentzGroup_apply_basis (Λ : SL(2,ℂ)) (α a : Fin 2) :
    repLorentzGroup Λ (basis (α, a)) = ∑ β, Λ.1 β α • basis (β, a) := by
  simp only [basis, Basis.map_apply, Basis.tensorProduct_apply, repLorentzGroup,
    MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, LinearEquiv.apply_symm_apply, TensorProduct.map_tmul,
    Fermion.LeftHandedWeyl.rep_apply_basis, Representation.trivial_apply,
    TensorProduct.sum_tmul, ← TensorProduct.smul_tmul', map_sum, map_smul]

lemma repGaugeGroupI_apply_basis (g : GaugeGroupI) (α a : Fin 2) :
    repGaugeGroupI g (basis (α, a)) =
      ∑ b, (star (g.toU1.1 : ℂ) ^ 3 * g.toSU2.1 b a) • basis (α, b) := by
  have h := repGaugeGroupI_tmul_basis_eq_sum g α a
  simpa [basis, Basis.map_apply, Basis.tensorProduct_apply, valLinEquiv_symm_apply,
    EuclideanSpace.basisFun_apply] using h

end LeptonDoublet

namespace LeptonSinglet

lemma repLorentzGroup_apply_basis (Λ : SL(2,ℂ)) (α : Fin 2) :
    repLorentzGroup Λ (basis α) = ∑ β, star (Λ.1 β α) • basis β := by
  simp only [basis, Basis.map_apply, repLorentzGroup, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.apply_symm_apply,
    Fermion.RightHandedWeyl.rep_apply_basis, Matrix.map_apply, map_sum, map_smul]

lemma repGaugeGroupI_apply_basis (g : GaugeGroupI) (α : Fin 2) :
    repGaugeGroupI g (basis α) = (star (g.toU1.1 : ℂ) ^ 6) • basis α := by
  simpa [basis, Basis.map_apply, valLinEquiv_symm_apply] using repGaugeGroupI_basis g α

end LeptonSinglet

namespace HiggsVec

lemma repGaugeGroupI_apply_basis (g : GaugeGroupI) (a : Fin 2) :
    repGaugeGroupI g (orthonormBasis.toBasis a) =
      ∑ b, ((g.toU1.1 : ℂ) ^ 3 * g.toSU2.1 b a) • orthonormBasis.toBasis b := by
  ext c
  simp [repGaugeGroupI, gaugeGroupI_smul_eq, orthonormBasis, EuclideanSpace.basisFun_apply,
    PiLp.ofLp_single, Submonoid.smul_def, Fin.sum_univ_two, mul_comm]
  fin_cases c <;> simp

end HiggsVec

/-!

## The action of the representations on the fermionic component space

-/

lemma FermionicComponentSpace.repLorentzGroup_apply_basis_of (Λ : SL(2,ℂ))
    (φ : FermionIrrep) (α : FermionIrrep.components φ) :
    FermionicComponentSpace.repLorentzGroup Λ (fermionicComponentBasis (.of φ α)) =
    ∑ β : FermionIrrep.components φ,
      ((FermionIrrep.basis φ).repr (FermionIrrep.repLorentzGroup φ Λ⁻¹
        (FermionIrrep.basis φ β)) α) • fermionicComponentBasis (.of φ β) := by
  refine ((Pi.basis (fun φ => FermionIrrep.basis φ)).prod
    ((Pi.basis (fun φ => FermionIrrep.basis φ)).conj)).ext fun w => ?_
  obtain (⟨φ', γ⟩ | ⟨φ', γ⟩) := w
  · simp only [FermionicComponentSpace.repLorentzGroup, Representation.dual_apply,
      Module.Dual.transpose_apply, fermionicComponentBasis, Basis.reindex_apply,
      fermionicGeneratorEquiv, Basis.prod_apply,
      FermionicTargetSpaceWithComplex.repLorentzGroup, FermionicTargetSpace.repLorentzGroup]
    simp
    by_cases h : φ' = φ
    · subst h
      simp [Finsupp.single_apply, Sigma.mk.injEq]
    · simp [Sigma.mk.injEq, h]
  · simp [FermionicComponentSpace.repLorentzGroup, Representation.dual_apply,
      Module.Dual.transpose_apply, fermionicComponentBasis, Basis.reindex_apply,
      fermionicGeneratorEquiv, Basis.prod_apply,
      FermionicTargetSpaceWithComplex.repLorentzGroup, FermionicTargetSpace.repLorentzGroup]

lemma FermionicComponentSpace.repLorentzGroup_apply_basis_bar (Λ : SL(2,ℂ))
    (φ : FermionIrrep) (α : FermionIrrep.components φ) :
    FermionicComponentSpace.repLorentzGroup Λ (fermionicComponentBasis (.bar φ α)) =
    ∑ β : FermionIrrep.components φ,
      star ((FermionIrrep.basis φ).repr (FermionIrrep.repLorentzGroup φ Λ⁻¹
        (FermionIrrep.basis φ β)) α) • fermionicComponentBasis (.bar φ β) := by
  refine ((Pi.basis (fun φ => FermionIrrep.basis φ)).prod
    ((Pi.basis (fun φ => FermionIrrep.basis φ)).conj)).ext fun w => ?_
  obtain (⟨φ', γ⟩ | ⟨φ', γ⟩) := w
  · simp [FermionicComponentSpace.repLorentzGroup, Representation.dual_apply,
      Module.Dual.transpose_apply, fermionicComponentBasis, Basis.reindex_apply,
      fermionicGeneratorEquiv, Basis.prod_apply,
      FermionicTargetSpaceWithComplex.repLorentzGroup, FermionicTargetSpace.repLorentzGroup]
  · simp only [FermionicComponentSpace.repLorentzGroup, Representation.dual_apply,
      Module.Dual.transpose_apply, fermionicComponentBasis, Basis.reindex_apply,
      fermionicGeneratorEquiv, Basis.prod_apply,
      FermionicTargetSpaceWithComplex.repLorentzGroup, FermionicTargetSpace.repLorentzGroup]
    simp [Representation.conj_apply]
    by_cases h : φ' = φ
    · subst h
      simp [Finsupp.single_apply, Sigma.mk.injEq]
    · simp [Sigma.mk.injEq, h]

lemma FermionicComponentSpace.repGaugeGroupI_apply_basis_of (g : GaugeGroupI)
    (φ : FermionIrrep) (α : FermionIrrep.components φ) :
    FermionicComponentSpace.repGaugeGroupI g (fermionicComponentBasis (.of φ α)) =
    ∑ β : FermionIrrep.components φ,
      ((FermionIrrep.basis φ).repr (FermionIrrep.repGaugeGroupI φ g⁻¹
        (FermionIrrep.basis φ β)) α) • fermionicComponentBasis (.of φ β) := by
  refine ((Pi.basis (fun φ => FermionIrrep.basis φ)).prod
    ((Pi.basis (fun φ => FermionIrrep.basis φ)).conj)).ext fun w => ?_
  obtain (⟨φ', γ⟩ | ⟨φ', γ⟩) := w
  · simp only [FermionicComponentSpace.repGaugeGroupI, Representation.dual_apply,
      Module.Dual.transpose_apply, fermionicComponentBasis, Basis.reindex_apply,
      fermionicGeneratorEquiv, Basis.prod_apply,
      FermionicTargetSpaceWithComplex.repGaugeGroupI, FermionicTargetSpace.repGaugeGroupI]
    simp
    by_cases h : φ' = φ
    · subst h
      simp [Finsupp.single_apply, Sigma.mk.injEq]
    · simp [Sigma.mk.injEq, h]
  · simp [FermionicComponentSpace.repGaugeGroupI, Representation.dual_apply,
      Module.Dual.transpose_apply, fermionicComponentBasis, Basis.reindex_apply,
      fermionicGeneratorEquiv, Basis.prod_apply,
      FermionicTargetSpaceWithComplex.repGaugeGroupI, FermionicTargetSpace.repGaugeGroupI]

lemma FermionicComponentSpace.repGaugeGroupI_apply_basis_bar (g : GaugeGroupI)
    (φ : FermionIrrep) (α : FermionIrrep.components φ) :
    FermionicComponentSpace.repGaugeGroupI g (fermionicComponentBasis (.bar φ α)) =
    ∑ β : FermionIrrep.components φ,
      star ((FermionIrrep.basis φ).repr (FermionIrrep.repGaugeGroupI φ g⁻¹
        (FermionIrrep.basis φ β)) α) • fermionicComponentBasis (.bar φ β) := by
  refine ((Pi.basis (fun φ => FermionIrrep.basis φ)).prod
    ((Pi.basis (fun φ => FermionIrrep.basis φ)).conj)).ext fun w => ?_
  obtain (⟨φ', γ⟩ | ⟨φ', γ⟩) := w
  · simp [FermionicComponentSpace.repGaugeGroupI, Representation.dual_apply,
      Module.Dual.transpose_apply, fermionicComponentBasis, Basis.reindex_apply,
      fermionicGeneratorEquiv, Basis.prod_apply,
      FermionicTargetSpaceWithComplex.repGaugeGroupI, FermionicTargetSpace.repGaugeGroupI]
  · simp only [FermionicComponentSpace.repGaugeGroupI, Representation.dual_apply,
      Module.Dual.transpose_apply, fermionicComponentBasis, Basis.reindex_apply,
      fermionicGeneratorEquiv, Basis.prod_apply,
      FermionicTargetSpaceWithComplex.repGaugeGroupI, FermionicTargetSpace.repGaugeGroupI]
    simp [Representation.conj_apply]
    by_cases h : φ' = φ
    · subst h
      simp [Finsupp.single_apply, Sigma.mk.injEq]
    · simp [Sigma.mk.injEq, h]

/-!

## The action of the representations on the complex scalar component space

-/

lemma ComplexScalarComponentSpace.repLorentzGroup_apply (Λ : SL(2,ℂ))
    (v : ComplexScalarComponentSpace) :
    ComplexScalarComponentSpace.repLorentzGroup Λ v = v := by
  have h1 : ∀ w : ComplexScalarTargetSpaceWithComplex,
      ComplexScalarTargetSpaceWithComplex.repLorentzGroup Λ⁻¹ w = w := by
    intro w
    apply Prod.ext
    · funext φ
      simp [ComplexScalarTargetSpaceWithComplex.repLorentzGroup,
        ComplexScalarTargetSpace.repLorentzGroup]
      cases φ
      simp [ComplexScalarIrrep.repLorentzGroup]
      rfl
    · funext φ
      simp [ComplexScalarTargetSpaceWithComplex.repLorentzGroup,
        ComplexScalarTargetSpace.repLorentzGroup, Representation.conj_apply]
      cases φ
      simp [ComplexScalarIrrep.repLorentzGroup, conjEquiv]
      rfl
  refine LinearMap.ext fun w => ?_
  simp [ComplexScalarComponentSpace.repLorentzGroup, Representation.dual_apply,
    Module.Dual.transpose_apply, h1]

lemma ComplexScalarComponentSpace.repGaugeGroupI_apply_basis_of (g : GaugeGroupI)
    (φ : ComplexScalarIrrep) (α : ComplexScalarIrrep.components φ) :
    ComplexScalarComponentSpace.repGaugeGroupI g (complexScalarComponentBasis (.of φ α)) =
    ∑ β : ComplexScalarIrrep.components φ,
      ((ComplexScalarIrrep.basis φ).repr (ComplexScalarIrrep.repGaugeGroupI φ g⁻¹
        (ComplexScalarIrrep.basis φ β)) α) • complexScalarComponentBasis (.of φ β) := by
  refine ((Pi.basis (fun φ => ComplexScalarIrrep.basis φ)).prod
    ((Pi.basis (fun φ => ComplexScalarIrrep.basis φ)).conj)).ext fun w => ?_
  obtain (⟨φ', γ⟩ | ⟨φ', γ⟩) := w
  · simp only [ComplexScalarComponentSpace.repGaugeGroupI, Representation.dual_apply,
      Module.Dual.transpose_apply, complexScalarComponentBasis, Basis.reindex_apply,
      complexScalarGeneratorEquiv, Basis.prod_apply,
      ComplexScalarTargetSpaceWithComplex.repGaugeGroupI,
      ComplexScalarTargetSpace.repGaugeGroupI]
    simp
    by_cases h : φ' = φ
    · subst h
      simp [Finsupp.single_apply, Sigma.mk.injEq]
    · simp [Finsupp.single_apply, Sigma.mk.injEq]
  · simp [ComplexScalarComponentSpace.repGaugeGroupI, Representation.dual_apply,
      Module.Dual.transpose_apply, complexScalarComponentBasis, Basis.reindex_apply,
      complexScalarGeneratorEquiv, Basis.prod_apply,
      ComplexScalarTargetSpaceWithComplex.repGaugeGroupI,
      ComplexScalarTargetSpace.repGaugeGroupI]

namespace EFTLagrangianExclDeriv

/-!

## The action of the representations on the field generators

-/

lemma repLorentzGroup_apply_fermion (Λ : SL(2,ℂ)) (ψ : FermionicGenerator) :
    repLorentzGroup Λ [ψ]ₑ = 1 ⊗ₜ[ℂ] ExteriorAlgebra.ι ℂ
      (FermionicComponentSpace.repLorentzGroup Λ (fermionicComponentBasis ψ)) := by
  simp [repLorentzGroup, Representation.tprod_apply, ofFieldGenerators,
    FermionicEFTExclDeriv.repLorentzGroup, ComplexScalarEFTExclDeriv.repLorentzGroup,
    ExteriorAlgebra.map_apply_ι]

lemma repGaugeGroupI_apply_fermion (g : GaugeGroupI) (ψ : FermionicGenerator) :
    repGaugeGroupI g [ψ]ₑ = 1 ⊗ₜ[ℂ] ExteriorAlgebra.ι ℂ
      (FermionicComponentSpace.repGaugeGroupI g (fermionicComponentBasis ψ)) := by
  simp [repGaugeGroupI, Representation.tprod_apply, ofFieldGenerators,
    FermionicEFTExclDeriv.repGaugeGroupI, ComplexScalarEFTExclDeriv.repGaugeGroupI,
    ExteriorAlgebra.map_apply_ι]

lemma repLorentzGroup_apply_cScalar (Λ : SL(2,ℂ)) (ϕ : ComplexScalarGenerator) :
    repLorentzGroup Λ [ϕ]ₛ = SymmetricAlgebra.ι ℂ _
      (ComplexScalarComponentSpace.repLorentzGroup Λ (complexScalarComponentBasis ϕ)) ⊗ₜ[ℂ] 1 := by
  simp [repLorentzGroup, Representation.tprod_apply, ofFieldGenerators,
    FermionicEFTExclDeriv.repLorentzGroup, ComplexScalarEFTExclDeriv.repLorentzGroup]

lemma repGaugeGroupI_apply_cScalar (g : GaugeGroupI) (ϕ : ComplexScalarGenerator) :
    repGaugeGroupI g [ϕ]ₛ = SymmetricAlgebra.ι ℂ _
      (ComplexScalarComponentSpace.repGaugeGroupI g (complexScalarComponentBasis ϕ)) ⊗ₜ[ℂ] 1 := by
  simp [repGaugeGroupI, Representation.tprod_apply, ofFieldGenerators,
    FermionicEFTExclDeriv.repGaugeGroupI, ComplexScalarEFTExclDeriv.repGaugeGroupI]

/-!

## The action of the representations on the generators appearing in the
## `L`, `e`, `H` Yukawa term

-/

lemma repLorentzGroup_apply_bar_L (Λ : SL(2,ℂ)) (i : Fin 3) (α a : Fin 2) :
    repLorentzGroup Λ [FermionicGenerator.bar (.L i) (α, a)]ₑ =
      ∑ β, star (Λ⁻¹.1 α β) • [FermionicGenerator.bar (.L i) (β, a)]ₑ := by
  rw [repLorentzGroup_apply_fermion, FermionicComponentSpace.repLorentzGroup_apply_basis_bar]
  show (1 : ComplexScalarEFTExclDeriv) ⊗ₜ[ℂ] (ExteriorAlgebra.ι ℂ)
      (∑ β : Fin 2 × Fin 2,
        star ((LeptonDoublet.basis.repr ((LeptonDoublet.repLorentzGroup Λ⁻¹)
          (LeptonDoublet.basis β))) (α, a)) •
          fermionicComponentBasis (FermionicGenerator.bar (FermionIrrep.L i) β)) = _
  rw [Fintype.sum_prod_type]
  simp [LeptonDoublet.repLorentzGroup_apply_basis, Basis.repr_self, Finsupp.single_apply,
    Prod.mk.injEq, ofFieldGenerators]
  fin_cases α <;> fin_cases a <;>
    simp [TensorProduct.tmul_add, TensorProduct.tmul_smul]

lemma repLorentzGroup_apply_of_e (Λ : SL(2,ℂ)) (j : Fin 3) (α : Fin 2) :
    repLorentzGroup Λ [FermionicGenerator.of (.e j) α]ₑ =
      ∑ β, star (Λ⁻¹.1 α β) • [FermionicGenerator.of (.e j) β]ₑ := by
  rw [repLorentzGroup_apply_fermion, FermionicComponentSpace.repLorentzGroup_apply_basis_of]
  show (1 : ComplexScalarEFTExclDeriv) ⊗ₜ[ℂ] (ExteriorAlgebra.ι ℂ)
      (∑ β : Fin 2,
        ((LeptonSinglet.basis.repr ((LeptonSinglet.repLorentzGroup Λ⁻¹)
          (LeptonSinglet.basis β))) α) •
          fermionicComponentBasis (FermionicGenerator.of (FermionIrrep.e j) β)) = _
  simp [LeptonSinglet.repLorentzGroup_apply_basis, Basis.repr_self, Finsupp.single_apply,
    ofFieldGenerators]
  fin_cases α <;> simp [TensorProduct.tmul_add, TensorProduct.tmul_smul]

lemma repLorentzGroup_apply_of_H (Λ : SL(2,ℂ)) (a : Fin 2) :
    repLorentzGroup Λ [ComplexScalarGenerator.of .H a]ₛ = [ComplexScalarGenerator.of .H a]ₛ := by
  rw [repLorentzGroup_apply_cScalar, ComplexScalarComponentSpace.repLorentzGroup_apply]
  rfl

lemma repGaugeGroupI_apply_bar_L (g : GaugeGroupI) (i : Fin 3) (α a : Fin 2) :
    repGaugeGroupI g [FermionicGenerator.bar (.L i) (α, a)]ₑ =
      ∑ b, (star (g.toU1.1 : ℂ) ^ 3 * g.toSU2.1 b a) • [FermionicGenerator.bar (.L i) (α, b)]ₑ := by
  rw [repGaugeGroupI_apply_fermion, FermionicComponentSpace.repGaugeGroupI_apply_basis_bar]
  show (1 : ComplexScalarEFTExclDeriv) ⊗ₜ[ℂ] (ExteriorAlgebra.ι ℂ)
      (∑ β : Fin 2 × Fin 2,
        star ((LeptonDoublet.basis.repr ((LeptonDoublet.repGaugeGroupI g⁻¹)
          (LeptonDoublet.basis β))) (α, a)) •
          fermionicComponentBasis (FermionicGenerator.bar (FermionIrrep.L i) β)) = _
  rw [Fintype.sum_prod_type]
  simp [LeptonDoublet.repGaugeGroupI_apply_basis, Basis.repr_self, Finsupp.single_apply,
    Prod.mk.injEq, ofFieldGenerators, map_inv, ← Unitary.star_eq_inv, ← Matrix.star_eq_inv,
    Matrix.star_apply]
  fin_cases α <;> fin_cases a <;>
    simp [TensorProduct.tmul_add, TensorProduct.tmul_smul]

lemma repGaugeGroupI_apply_of_e (g : GaugeGroupI) (j : Fin 3) (α : Fin 2) :
    repGaugeGroupI g [FermionicGenerator.of (.e j) α]ₑ =
      ((g.toU1.1 : ℂ) ^ 6) • [FermionicGenerator.of (.e j) α]ₑ := by
  rw [repGaugeGroupI_apply_fermion, FermionicComponentSpace.repGaugeGroupI_apply_basis_of]
  show (1 : ComplexScalarEFTExclDeriv) ⊗ₜ[ℂ] (ExteriorAlgebra.ι ℂ)
      (∑ β : Fin 2,
        ((LeptonSinglet.basis.repr ((LeptonSinglet.repGaugeGroupI g⁻¹)
          (LeptonSinglet.basis β))) α) •
          fermionicComponentBasis (FermionicGenerator.of (FermionIrrep.e j) β)) = _
  simp [LeptonSinglet.repGaugeGroupI_apply_basis, Basis.repr_self, Finsupp.single_apply,
    ofFieldGenerators, map_inv, ← Unitary.star_eq_inv, TensorProduct.tmul_smul]

lemma repGaugeGroupI_apply_of_H (g : GaugeGroupI) (a : Fin 2) :
    repGaugeGroupI g [ComplexScalarGenerator.of .H a]ₛ =
      ∑ b, (star (g.toU1.1 : ℂ) ^ 3 * star (g.toSU2.1 b a)) • [ComplexScalarGenerator.of .H b]ₛ := by
  rw [repGaugeGroupI_apply_cScalar, ComplexScalarComponentSpace.repGaugeGroupI_apply_basis_of]
  show (SymmetricAlgebra.ι ℂ _)
      (∑ β : Fin 2,
        ((HiggsVec.orthonormBasis.toBasis.repr ((HiggsVec.repGaugeGroupI g⁻¹)
          (HiggsVec.orthonormBasis.toBasis β))) a) •
          complexScalarComponentBasis (ComplexScalarGenerator.of ComplexScalarIrrep.H β))
      ⊗ₜ[ℂ] 1 = _
  simp only [HiggsVec.repGaugeGroupI_apply_basis, map_sum, map_smul, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, Basis.repr_self, smul_eq_mul,
    Finsupp.single_apply]
  simp [map_inv, ← Unitary.star_eq_inv, ← Matrix.star_eq_inv, Matrix.star_apply,
    mul_ite, Finset.sum_ite_eq', ofFieldGenerators]
  fin_cases a <;> simp [TensorProduct.add_tmul, ← TensorProduct.smul_tmul']

/-!

## The Yukawa term for the lepton doublet, lepton singlet and Higgs field

-/

/-- The Yukawa term coupling the lepton doublet `L i`, the charged lepton
  singlet `e j` and the Higgs field: `ε^{α β} (bar L i)_{α a} (e j)_β H_a`,
  with the Lorentz indices of `bar L` and `e` contracted with the Weyl metric
  and the weak isospin indices of `bar L` and `H` contracted directly. -/
def yukawaTermLeH (i j : Fin 3) : EFTLagrangianExclDeriv :=
  ∑ α, ∑ β, ∑ a, metricRaw α β •
    ([FermionicGenerator.bar (.L i) (α, a)]ₑ * [FermionicGenerator.of (.e j) β]ₑ *
      [ComplexScalarGenerator.of .H a]ₛ)

lemma yukawaTermLeH_invariant (i j : Fin 3) : IsInvariant (yukawaTermLeH i j) := by
  constructor
  · intro Λ
    have hdet : (starRingEnd ℂ) ((Λ⁻¹).1 0 0) * (starRingEnd ℂ) ((Λ⁻¹).1 1 1) -
        (starRingEnd ℂ) ((Λ⁻¹).1 0 1) * (starRingEnd ℂ) ((Λ⁻¹).1 1 0) = 1 := by
      have h : ((Λ⁻¹).1).det = 1 := Matrix.SpecialLinearGroup.det_coe Λ⁻¹
      rw [Matrix.det_fin_two] at h
      simpa using congrArg (starRingEnd ℂ) h
    simp only [yukawaTermLeH, metricRaw, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      zero_smul, one_smul, zero_add, add_zero, map_add, map_smul,
      repLorentzGroup_mul, repLorentzGroup_apply_bar_L, repLorentzGroup_apply_of_e,
      repLorentzGroup_apply_of_H, Fin.sum_univ_two, add_mul, mul_add, smul_mul_assoc,
      mul_smul_comm, RCLike.star_def]
    match_scalars
    all_goals first
      | linear_combination hdet
      | linear_combination -hdet
      | linear_combination (2 : ℂ) * hdet
      | linear_combination -(2 : ℂ) * hdet
      | ring
  · intro g
    have hz6 : (g.toU1.1 : ℂ) ^ 6 * (starRingEnd ℂ) (g.toU1.1 : ℂ) ^ 6 = 1 := by
      have hz : (g.toU1.1 : ℂ) * star (g.toU1.1 : ℂ) = 1 := (Unitary.mem_iff.mp g.toU1.2).2
      calc (g.toU1.1 : ℂ) ^ 6 * (starRingEnd ℂ) (g.toU1.1 : ℂ) ^ 6
          = ((g.toU1.1 : ℂ) * star (g.toU1.1 : ℂ)) ^ 6 := by rw [RCLike.star_def]; ring
        _ = 1 := by rw [hz]; norm_num
    have hE : ∀ b b' : Fin 2,
        g.toSU2.1 b 0 * (starRingEnd ℂ) (g.toSU2.1 b' 0) +
          g.toSU2.1 b 1 * (starRingEnd ℂ) (g.toSU2.1 b' 1) = if b = b' then 1 else 0 := by
      intro b b'
      have hh := Matrix.mem_unitaryGroup_iff.mp g.toSU2.2.1
      have h2 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M b b') hh
      simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, Fin.sum_univ_two,
        RCLike.star_def] using h2
    have hK : ∀ b b' : Fin 2,
        (g.toU1.1 : ℂ) ^ 6 * (starRingEnd ℂ) (g.toU1.1 : ℂ) ^ 6 *
          (g.toSU2.1 b 0 * (starRingEnd ℂ) (g.toSU2.1 b' 0) +
            g.toSU2.1 b 1 * (starRingEnd ℂ) (g.toSU2.1 b' 1)) = if b = b' then 1 else 0 := by
      intro b b'
      rw [hz6, one_mul, hE]
    have hK00 := hK 0 0
    have hK01 := hK 0 1
    have hK10 := hK 1 0
    have hK11 := hK 1 1
    rw [if_pos rfl] at hK00 hK11
    rw [if_neg (by decide)] at hK01
    rw [if_neg (by decide)] at hK10
    simp only [yukawaTermLeH, metricRaw, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      zero_smul, one_smul, zero_add, add_zero, map_add, map_smul,
      repGaugeGroupI_mul, repGaugeGroupI_apply_bar_L, repGaugeGroupI_apply_of_e,
      repGaugeGroupI_apply_of_H, Fin.sum_univ_two, add_mul, mul_add, smul_mul_assoc,
      mul_smul_comm, smul_smul, RCLike.star_def]
    match_scalars
    · linear_combination hK00
    · linear_combination hK10
    · linear_combination hK01
    · linear_combination hK11
    · linear_combination -hK00
    · linear_combination -hK10
    · linear_combination -hK01
    · linear_combination -hK11

end EFTLagrangianExclDeriv

end
end StandardModel
