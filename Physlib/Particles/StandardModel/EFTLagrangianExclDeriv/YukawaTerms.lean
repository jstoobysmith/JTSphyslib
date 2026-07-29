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

/-!

## Exclusivity of the `L`, `e`, `H` Yukawa term

The submodule of the EFT lagrangian spanned by the terms with irrep content
`{bar L i, e j, H}` is spanned by the sixteen monomials
`[bar L i (α, a)]ₑ * [e j β]ₑ * [H c]ₛ`. We construct linear functionals
extracting the coefficient of each monomial, and use invariance under specific
group elements to show that any invariant element of this submodule is
proportional to `yukawaTermLeH`.

-/

/-- The index of a monomial in the `L`, `e`, `H` sector: the components
  `(α, a)` of `bar L`, `β` of `e` and `c` of `H`. -/
abbrev LEHIndex : Type := (Fin 2 × Fin 2) × Fin 2 × Fin 2

/-- The monomial `[bar L i (α, a)]ₑ * [e j β]ₑ * [H c]ₛ` of the `L`, `e`, `H`
  sector associated with an index `((α, a), β, c)`. -/
def lehMonomial (i j : Fin 3) (m : LEHIndex) : EFTLagrangianExclDeriv :=
  [FermionicGenerator.bar (.L i) m.1]ₑ * [FermionicGenerator.of (.e j) m.2.1]ₑ *
    [ComplexScalarGenerator.of .H m.2.2]ₛ

lemma yukawaTermLeH_eq_sum_lehMonomial (i j : Fin 3) :
    yukawaTermLeH i j = ∑ α, ∑ β, ∑ a, metricRaw α β • lehMonomial i j ((α, a), β, a) := rfl

lemma lehMonomial_eq_tmul (i j : Fin 3) (m : LEHIndex) :
    lehMonomial i j m =
      SymmetricAlgebra.ι ℂ _ (complexScalarComponentBasis (.of .H m.2.2)) ⊗ₜ[ℂ]
        (ExteriorAlgebra.ι ℂ (fermionicComponentBasis (.bar (.L i) m.1)) *
          ExteriorAlgebra.ι ℂ (fermionicComponentBasis (.of (.e j) m.2.1))) := by
  simp [lehMonomial, ofFieldGenerators, Algebra.TensorProduct.tmul_mul_tmul]

/-- The linear functional on the bosonic factor extracting the coefficient of
  the degree-one monomial `SymmetricAlgebra.ι (complexScalarComponentBasis (.of .H c))`,
  through the identification of the symmetric algebra with multivariate polynomials. -/
def lehCoeffS (c : Fin 2) : ComplexScalarEFTExclDeriv →ₗ[ℂ] ℂ :=
  MvPolynomial.lcoeff ℂ (Finsupp.single (ComplexScalarGenerator.of .H c) 1) ∘ₗ
    (SymmetricAlgebra.equivMvPolynomial complexScalarComponentBasis).toLinearMap

lemma lehCoeffS_apply_ι (c c' : Fin 2) :
    lehCoeffS c (SymmetricAlgebra.ι ℂ _ (complexScalarComponentBasis (.of .H c'))) =
      if c' = c then 1 else 0 := by
  simp only [lehCoeffS, LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply,
    SymmetricAlgebra.equivMvPolynomial_ι_apply, MvPolynomial.lcoeff_apply, MvPolynomial.coeff_X]
  simp only [Finsupp.single_eq_single_iff, ComplexScalarGenerator.of.injEq, one_ne_zero,
    and_false, or_false, true_and]
  split_ifs <;> simp_all

/-- The linear functional on the fermionic factor extracting the coefficient of the
  quadratic monomial `ι (bar L i (α, a)) * ι (e j β)`, built from the degree-two
  alternating map given by the determinant of the pair of coordinate functionals. -/
def lehCoeffE (i j : Fin 3) (α a β : Fin 2) : FermionicEFTExclDeriv →ₗ[ℂ] ℂ :=
  ExteriorAlgebra.liftAlternating fun n =>
    match n with
    | 2 => (Matrix.detRowAlternating (n := Fin 2) (R := ℂ)).compLinearMap
        (LinearMap.pi ![fermionicComponentBasis.coord (.bar (.L i) (α, a)),
          fermionicComponentBasis.coord (.of (.e j) β)])
    | _ => 0

lemma lehCoeffE_apply_ι_mul_ι (i j : Fin 3) (α a β α' a' β' : Fin 2) :
    lehCoeffE i j α a β (ExteriorAlgebra.ι ℂ (fermionicComponentBasis (.bar (.L i) (α', a'))) *
      ExteriorAlgebra.ι ℂ (fermionicComponentBasis (.of (.e j) β'))) =
      if (α', a') = (α, a) ∧ β' = β then 1 else 0 := by
  have h2 : ExteriorAlgebra.ι ℂ (fermionicComponentBasis (.bar (.L i) (α', a'))) *
      ExteriorAlgebra.ι ℂ (fermionicComponentBasis (.of (.e j) β')) =
      ExteriorAlgebra.ιMulti ℂ 2 ![fermionicComponentBasis (.bar (.L i) (α', a')),
        fermionicComponentBasis (.of (.e j) β')] := by
    simp [ExteriorAlgebra.ιMulti_apply]
  rw [h2, lehCoeffE, ExteriorAlgebra.liftAlternating_apply_ιMulti]
  simp only [AlternatingMap.compLinearMap_apply]
  show Matrix.det _ = _
  rw [Matrix.det_fin_two]
  simp only [LinearMap.pi_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Basis.coord_apply,
    Basis.repr_self, Finsupp.single_apply, Fin.isValue]
  simp only [FermionicGenerator.bar.injEq, FermionicGenerator.of.injEq, heq_eq_eq,
    reduceCtorEq, if_false, mul_zero, sub_zero, true_and]
  split_ifs <;> simp_all

/-- The linear functional on `EFTLagrangianExclDeriv` extracting the coefficient of
  the monomial `lehMonomial i j m`. -/
def lehCoeff (i j : Fin 3) (m : LEHIndex) : EFTLagrangianExclDeriv →ₗ[ℂ] ℂ :=
  (TensorProduct.lid ℂ ℂ).toLinearMap ∘ₗ
    TensorProduct.map (lehCoeffS m.2.2) (lehCoeffE i j m.1.1 m.1.2 m.2.1)

lemma lehCoeff_apply_lehMonomial (i j : Fin 3) (m m' : LEHIndex) :
    lehCoeff i j m (lehMonomial i j m') = if m' = m then 1 else 0 := by
  obtain ⟨⟨α, a⟩, β, c⟩ := m
  obtain ⟨⟨α', a'⟩, β', c'⟩ := m'
  rw [lehMonomial_eq_tmul]
  simp only [lehCoeff, LinearMap.coe_comp, Function.comp_apply, TensorProduct.map_tmul,
    LinearEquiv.coe_coe, TensorProduct.lid_tmul, lehCoeffS_apply_ι, lehCoeffE_apply_ι_mul_ι,
    smul_eq_mul, Prod.mk.injEq]
  split_ifs <;> simp_all

lemma lehCoeff_apply_sum (i j : Fin 3) (f : LEHIndex → ℂ) (m : LEHIndex) :
    lehCoeff i j m (∑ m', f m' • lehMonomial i j m') = f m := by
  rw [map_sum]
  simp [lehCoeff_apply_lehMonomial, mul_ite]

lemma eq_sum_lehCoeff_of_mem_span (i j : Fin 3) (V : EFTLagrangianExclDeriv)
    (hV : V ∈ Submodule.span ℂ (Set.range (lehMonomial i j))) :
    V = ∑ m, lehCoeff i j m V • lehMonomial i j m := by
  induction hV using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m', rfl⟩ := hx
    simp [lehCoeff_apply_lehMonomial, ite_smul, Finset.sum_ite_eq]
  | zero => simp
  | add x y hx hy ihx ihy =>
    conv_lhs => rw [ihx, ihy]
    simp [map_add, add_smul, Finset.sum_add_distrib]
  | smul c x hx ih =>
    conv_lhs => rw [ih]
    simp [map_smul, smul_smul, Finset.smul_sum]

def LEHSubModule (i j : Fin 3) : Submodule ℂ EFTLagrangianExclDeriv :=
  Submodule.span ℂ (termOfList '' {l | (Multiset.ofList l).map FieldGenerators.toIrrep =
  [Irrep.barFermion (FermionIrrep.L i), Irrep.fermion (FermionIrrep.e j),
  Irrep.cScalar ComplexScalarIrrep.H]})

lemma toIrrep_eq_barFermion_iff (g : FieldGenerators) (φ : FermionIrrep) :
    g.toIrrep = Irrep.barFermion φ ↔ ∃ p, g = FieldGenerators.fermion (.bar φ p) := by
  match g with
  | .cScalar (.of φ' p) => simp [FieldGenerators.toIrrep]
  | .cScalar (.bar φ' p) => simp [FieldGenerators.toIrrep]
  | .fermion (.of φ' p) => simp [FieldGenerators.toIrrep]
  | .fermion (.bar φ' p) =>
    simp only [FieldGenerators.toIrrep, Irrep.barFermion.injEq]
    constructor
    · intro h
      subst h
      exact ⟨p, rfl⟩
    · rintro ⟨p', h⟩
      simp only [FieldGenerators.fermion.injEq, FermionicGenerator.bar.injEq] at h
      exact h.1

lemma toIrrep_eq_fermion_iff (g : FieldGenerators) (φ : FermionIrrep) :
    g.toIrrep = Irrep.fermion φ ↔ ∃ p, g = FieldGenerators.fermion (.of φ p) := by
  match g with
  | .cScalar (.of φ' p) => simp [FieldGenerators.toIrrep]
  | .cScalar (.bar φ' p) => simp [FieldGenerators.toIrrep]
  | .fermion (.bar φ' p) => simp [FieldGenerators.toIrrep]
  | .fermion (.of φ' p) =>
    simp only [FieldGenerators.toIrrep, Irrep.fermion.injEq]
    constructor
    · intro h
      subst h
      exact ⟨p, rfl⟩
    · rintro ⟨p', h⟩
      simp only [FieldGenerators.fermion.injEq, FermionicGenerator.of.injEq] at h
      exact h.1

lemma toIrrep_eq_cScalar_iff (g : FieldGenerators) (φ : ComplexScalarIrrep) :
    g.toIrrep = Irrep.cScalar φ ↔ ∃ p, g = FieldGenerators.cScalar (.of φ p) := by
  match g with
  | .cScalar (.bar φ' p) => simp [FieldGenerators.toIrrep]
  | .fermion (.of φ' p) => simp [FieldGenerators.toIrrep]
  | .fermion (.bar φ' p) => simp [FieldGenerators.toIrrep]
  | .cScalar (.of φ' p) =>
    cases φ
    cases φ'
    simp only [FieldGenerators.toIrrep]
    exact ⟨fun _ => ⟨p, rfl⟩, fun _ => trivial⟩

lemma exists_perm_of_mem_LEH_set (i j : Fin 3) (l : List FieldGenerators)
    (hl : (Multiset.ofList l).map FieldGenerators.toIrrep =
      ([Irrep.barFermion (FermionIrrep.L i), Irrep.fermion (FermionIrrep.e j),
        Irrep.cScalar ComplexScalarIrrep.H] : Multiset Irrep)) :
    ∃ m : LEHIndex, l.Perm [.fermion (.bar (.L i) m.1), .fermion (.of (.e j) m.2.1),
      .cScalar (.of .H m.2.2)] := by
  rw [show ([Irrep.barFermion (FermionIrrep.L i), Irrep.fermion (FermionIrrep.e j),
      Irrep.cScalar ComplexScalarIrrep.H] : Multiset Irrep) =
    Irrep.barFermion (FermionIrrep.L i) ::ₘ Irrep.fermion (FermionIrrep.e j) ::ₘ
      {Irrep.cScalar ComplexScalarIrrep.H} from rfl] at hl
  obtain ⟨g1, hg1m, hg1, h2⟩ := (Multiset.map_eq_cons _ _ _ _).mpr hl
  obtain ⟨g2, hg2m, hg2, h3⟩ := (Multiset.map_eq_cons _ _ _ _).mpr h2
  obtain ⟨g3, h4, hg3⟩ := Multiset.map_eq_singleton.mp h3
  obtain ⟨p, rfl⟩ := (toIrrep_eq_barFermion_iff g1 _).mp hg1
  obtain ⟨q, rfl⟩ := (toIrrep_eq_fermion_iff g2 _).mp hg2
  obtain ⟨r, rfl⟩ := (toIrrep_eq_cScalar_iff g3 _).mp hg3
  refine ⟨(p, q, r), Multiset.coe_eq_coe.mp ?_⟩
  rw [← Multiset.cons_erase hg1m, ← Multiset.cons_erase hg2m, h4]
  rfl

lemma termOfList_canonical (i j : Fin 3) (m : LEHIndex) :
    termOfList [.fermion (.bar (.L i) m.1), .fermion (.of (.e j) m.2.1),
      .cScalar (.of .H m.2.2)] = lehMonomial i j m := by
  simp [termOfList, lehMonomial, mul_assoc]

lemma LEHSubModule_le_span (i j : Fin 3) :
    LEHSubModule i j ≤ Submodule.span ℂ (Set.range (lehMonomial i j)) := by
  rw [LEHSubModule]
  refine Submodule.span_le.mpr ?_
  rintro x ⟨l, hl, rfl⟩
  obtain ⟨m, hperm⟩ := exists_perm_of_mem_LEH_set i j l hl
  obtain ⟨c, hc, _⟩ := termOfList_perm hperm
  rw [hc, termOfList_canonical]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)

/-!

### Specific group elements used to constrain the coefficients

-/

/-- The diagonal Lorentz transformation `diag (2, 2⁻¹)`. -/
def lorentzDiag : SL(2,ℂ) := ⟨!![2, 0; 0, 2⁻¹], by simp [Matrix.det_fin_two_of]⟩

/-- The off-diagonal Lorentz transformation `!![0, 1; -1, 0]`. -/
def lorentzSwap : SL(2,ℂ) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two_of]⟩

lemma lorentzDiag_inv_coe : (lorentzDiag⁻¹).1 = !![2⁻¹, 0; 0, 2] := by
  rw [Matrix.SpecialLinearGroup.coe_inv]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [lorentzDiag, Matrix.adjugate_fin_two]

lemma lorentzSwap_inv_coe : (lorentzSwap⁻¹).1 = !![0, -1; 1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_inv]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [lorentzSwap, Matrix.adjugate_fin_two]

/-- The gauge transformation with `SU(2)` part `diag (I, -I)`. -/
def gaugeDiag : GaugeGroupI :=
  (1, ⟨!![I, 0; 0, -I], by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    constructor
    · rw [Matrix.mem_unitaryGroup_iff]
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, star_eq_conjTranspose,
          Matrix.conjTranspose_apply]
    · simp [Matrix.det_fin_two_of]⟩, 1)

/-- The gauge transformation with `SU(2)` part `!![0, 1; -1, 0]`. -/
def gaugeSwap : GaugeGroupI :=
  (1, ⟨!![0, 1; -1, 0], by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    constructor
    · rw [Matrix.mem_unitaryGroup_iff]
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, star_eq_conjTranspose,
          Matrix.conjTranspose_apply]
    · simp [Matrix.det_fin_two_of]⟩, 1)

lemma repLorentzGroup_lorentzDiag_lehMonomial (i j : Fin 3) (m : LEHIndex) :
    repLorentzGroup lorentzDiag (lehMonomial i j m) =
      ((![2⁻¹, 2] : Fin 2 → ℂ) m.1.1 * ![2⁻¹, 2] m.2.1) • lehMonomial i j m := by
  obtain ⟨⟨α, a⟩, β, c⟩ := m
  simp only [lehMonomial, repLorentzGroup_mul, repLorentzGroup_apply_bar_L,
    repLorentzGroup_apply_of_e, repLorentzGroup_apply_of_H, lorentzDiag_inv_coe]
  fin_cases α <;> fin_cases β <;>
    simp [Fin.sum_univ_two, smul_mul_assoc, mul_smul_comm,
      smul_smul, Complex.conj_ofNat, one_smul]

lemma repLorentzGroup_lorentzSwap_lehMonomial (i j : Fin 3) (m : LEHIndex) :
    repLorentzGroup lorentzSwap (lehMonomial i j m) =
      ((![-1, 1] : Fin 2 → ℂ) m.1.1 * ![-1, 1] m.2.1) •
        lehMonomial i j ((![1, 0] m.1.1, m.1.2), ![1, 0] m.2.1, m.2.2) := by
  obtain ⟨⟨α, a⟩, β, c⟩ := m
  simp only [lehMonomial, repLorentzGroup_mul, repLorentzGroup_apply_bar_L,
    repLorentzGroup_apply_of_e, repLorentzGroup_apply_of_H, lorentzSwap_inv_coe]
  fin_cases α <;> fin_cases β <;>
    simp [Fin.sum_univ_two, smul_mul_assoc, mul_smul_comm,
      smul_smul, mul_comm, one_smul]

lemma repGaugeGroupI_gaugeDiag_lehMonomial (i j : Fin 3) (m : LEHIndex) :
    repGaugeGroupI gaugeDiag (lehMonomial i j m) =
      ((![I, -I] : Fin 2 → ℂ) m.1.2 * ![-I, I] m.2.2) • lehMonomial i j m := by
  obtain ⟨⟨α, a⟩, β, c⟩ := m
  simp only [lehMonomial, repGaugeGroupI_mul, repGaugeGroupI_apply_bar_L,
    repGaugeGroupI_apply_of_e, repGaugeGroupI_apply_of_H]
  have hU1 : (GaugeGroupI.toU1 gaugeDiag).1 = 1 := rfl
  have hSU2 : (GaugeGroupI.toSU2 gaugeDiag).1 = !![I, 0; 0, -I] := rfl
  rw [hU1, hSU2]
  fin_cases a <;> fin_cases c <;>
    simp [Fin.sum_univ_two, smul_mul_assoc, mul_smul_comm,
      smul_smul, mul_comm, neg_smul, one_smul] <;>
    module

lemma repGaugeGroupI_gaugeSwap_lehMonomial (i j : Fin 3) (m : LEHIndex) :
    repGaugeGroupI gaugeSwap (lehMonomial i j m) =
      ((![-1, 1] : Fin 2 → ℂ) m.1.2 * ![-1, 1] m.2.2) •
        lehMonomial i j ((m.1.1, ![1, 0] m.1.2), m.2.1, ![1, 0] m.2.2) := by
  obtain ⟨⟨α, a⟩, β, c⟩ := m
  simp only [lehMonomial, repGaugeGroupI_mul, repGaugeGroupI_apply_bar_L,
    repGaugeGroupI_apply_of_e, repGaugeGroupI_apply_of_H]
  have hU1 : (GaugeGroupI.toU1 gaugeSwap).1 = 1 := rfl
  have hSU2 : (GaugeGroupI.toSU2 gaugeSwap).1 = !![0, 1; -1, 0] := rfl
  rw [hU1, hSU2]
  fin_cases a <;> fin_cases c <;>
    simp [Fin.sum_univ_two, smul_mul_assoc, mul_smul_comm,
      smul_smul, mul_comm, one_smul]

lemma yukawaTermLeH_exclusive (i j : Fin 3)
    (V : EFTLagrangianExclDeriv) (hV : V ∈ LEHSubModule i j)
    (hI : IsInvariant V) : ∃ (c : ℂ), V = c • yukawaTermLeH i j := by
  have hVexp : V = ∑ m, lehCoeff i j m V • lehMonomial i j m :=
    eq_sum_lehCoeff_of_mem_span i j V (LEHSubModule_le_span i j hV)
  -- The diagonal Lorentz transformation scales each monomial.
  have hLD : ∀ m : LEHIndex,
      lehCoeff i j m V * ((![2⁻¹, 2] : Fin 2 → ℂ) m.1.1 * ![2⁻¹, 2] m.2.1) =
        lehCoeff i j m V := by
    intro m
    have h := congrArg (lehCoeff i j m) (hI.1 lorentzDiag)
    conv at h => lhs; rw [hVexp]
    simpa only [map_sum, map_smul, repLorentzGroup_lorentzDiag_lehMonomial, smul_smul,
      lehCoeff_apply_lehMonomial, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true] using h
  -- The diagonal gauge transformation scales each monomial.
  have hGD : ∀ m : LEHIndex,
      lehCoeff i j m V * ((![I, -I] : Fin 2 → ℂ) m.1.2 * ![-I, I] m.2.2) =
        lehCoeff i j m V := by
    intro m
    have h := congrArg (lehCoeff i j m) (hI.2 gaugeDiag)
    conv at h => lhs; rw [hVexp]
    simpa only [map_sum, map_smul, repGaugeGroupI_gaugeDiag_lehMonomial, smul_smul,
      lehCoeff_apply_lehMonomial, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true] using h
  -- Coefficients with equal Lorentz indices vanish.
  have hz00 : ∀ a c : Fin 2, lehCoeff i j ((0, a), 0, c) V = 0 := by
    intro a c
    have h := hLD ((0, a), 0, c)
    simp only [Matrix.cons_val_zero] at h
    linear_combination (-(4 : ℂ)/3) * h
  have hz11 : ∀ a c : Fin 2, lehCoeff i j ((1, a), 1, c) V = 0 := by
    intro a c
    have h := hLD ((1, a), 1, c)
    simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
    linear_combination ((1 : ℂ)/3) * h
  -- Coefficients with different weak isospin indices vanish.
  have hza01 : ∀ α β : Fin 2, lehCoeff i j ((α, 0), β, 1) V = 0 := by
    intro α β
    have h := hGD ((α, 0), β, 1)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Complex.I_mul_I] at h
    linear_combination (-(1 : ℂ)/2) * h
  have hza10 : ∀ α β : Fin 2, lehCoeff i j ((α, 1), β, 0) V = 0 := by
    intro α β
    have h := hGD ((α, 1), β, 0)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, neg_mul_neg, Complex.I_mul_I] at h
    linear_combination (-(1 : ℂ)/2) * h
  -- The off-diagonal Lorentz transformation relates the two `ε` components.
  have hr1 : lehCoeff i j ((1, 0), 0, 0) V = -lehCoeff i j ((0, 0), 1, 0) V := by
    have h := congrArg (lehCoeff i j ((1, 0), 0, 0)) (hI.1 lorentzSwap)
    conv at h => lhs; rw [hVexp]
    simp only [map_sum, map_smul, repLorentzGroup_lorentzSwap_lehMonomial, smul_smul,
      lehCoeff_apply_lehMonomial, smul_eq_mul, mul_ite, mul_one, mul_zero] at h
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
    simp at h
    linear_combination -h
  have hr2 : lehCoeff i j ((1, 1), 0, 1) V = -lehCoeff i j ((0, 1), 1, 1) V := by
    have h := congrArg (lehCoeff i j ((1, 1), 0, 1)) (hI.1 lorentzSwap)
    conv at h => lhs; rw [hVexp]
    simp only [map_sum, map_smul, repLorentzGroup_lorentzSwap_lehMonomial, smul_smul,
      lehCoeff_apply_lehMonomial, smul_eq_mul, mul_ite, mul_one, mul_zero] at h
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
    simp at h
    linear_combination -h
  -- The off-diagonal gauge transformation relates the two isospin components.
  have hr3 : lehCoeff i j ((0, 1), 1, 1) V = lehCoeff i j ((0, 0), 1, 0) V := by
    have h := congrArg (lehCoeff i j ((0, 1), 1, 1)) (hI.2 gaugeSwap)
    conv at h => lhs; rw [hVexp]
    simp only [map_sum, map_smul, repGaugeGroupI_gaugeSwap_lehMonomial, smul_smul,
      lehCoeff_apply_lehMonomial, smul_eq_mul, mul_ite, mul_one, mul_zero] at h
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
    simp at h
    linear_combination -h
  -- Assemble.
  refine ⟨lehCoeff i j ((0, 0), 1, 0) V, ?_⟩
  conv_lhs => rw [hVexp]
  rw [yukawaTermLeH_eq_sum_lehMonomial]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  rw [hr1, hr2, hr3]
  simp only [hz00, hz11, hza01, hza10, zero_smul, add_zero, zero_add]
  simp only [metricRaw, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    zero_smul, one_smul, add_zero, zero_add]
  module
end EFTLagrangianExclDeriv

end
end StandardModel
