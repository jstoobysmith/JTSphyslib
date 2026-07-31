/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Jinzheng Li, Nathaneal Sajan
-/
module

public import Physlib.Particles.LagrangianTheory.Basic

/-!

# The EFT Lagrangian with free derivatives

## i. Overview

For a Lagrangian theory, this file defines the algebra of complex-scalar, real-boson, and
fermionic expressions with arbitrarily many derivatives. It also bundles the Lorentz and gauge
actions as algebra homomorphisms and proves that the existing tensor-product representations
preserve multiplication and the unit.

-/

@[expose] public section

namespace LagrangianTheory

open TensorProduct Matrix MatrixGroups

noncomputable section

variable {G : Type} [Group G]
variable {L : LagrangianTheory G}

/-- The algebra of Lagrangian expressions whose derivative-decorated fields remain freely
generated. -/
abbrev EFTLagrangianFreeDeriv (L : LagrangianTheory G) : Type :=
  L.ComplexScalarEFTFreeDeriv ⊗[ℂ]
    L.RealBosonEFTFreeDerivComplex ⊗[ℂ] L.FermionicEFTFreeDeriv

namespace EFTLagrangianFreeDeriv

set_option maxSynthPendingDepth 4 in
noncomputable instance : Ring L.EFTLagrangianFreeDeriv := inferInstanceAs <|
  Ring (L.ComplexScalarEFTFreeDeriv ⊗[ℂ]
    L.RealBosonEFTFreeDerivComplex ⊗[ℂ] L.FermionicEFTFreeDeriv)

set_option maxSynthPendingDepth 4 in
noncomputable instance : Algebra ℂ L.EFTLagrangianFreeDeriv := inferInstanceAs <|
  Algebra ℂ (L.ComplexScalarEFTFreeDeriv ⊗[ℂ]
    L.RealBosonEFTFreeDerivComplex ⊗[ℂ] L.FermionicEFTFreeDeriv)

/-!

## A. Lorentz-group action

### A.1. Algebra homomorphisms

-/

/-- The Lorentz action on the complex-scalar factor as an algebra homomorphism. -/
noncomputable def complexScalarLorentzAlgHom (Λ : SL(2,ℂ)) :
    L.ComplexScalarEFTFreeDeriv →ₐ[ℂ] L.ComplexScalarEFTFreeDeriv :=
  SymmetricAlgebra.lift
    (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarComponentSpaceWithDeriv.repLorentzGroup Λ)

/-- The Lorentz action on the fermionic factor as an algebra homomorphism. -/
noncomputable def fermionicLorentzAlgHom (Λ : SL(2,ℂ)) :
    L.FermionicEFTFreeDeriv →ₐ[ℂ] L.FermionicEFTFreeDeriv :=
  ExteriorAlgebra.map (FermionicComponentSpaceWithDeriv.repLorentzGroup Λ)

/-- The Lorentz action on the real-boson factor as a real algebra homomorphism. -/
noncomputable def realBosonLorentzAlgHom (Λ : SL(2,ℂ)) :
    L.RealBosonEFTFreeDeriv →ₐ[ℝ] L.RealBosonEFTFreeDeriv :=
  SymmetricAlgebra.lift
    (SymmetricAlgebra.ι ℝ _ ∘ₗ RealBosonComponentSpaceWithDeriv.repLorentzGroup Λ)

/-- The scalar extension of the real-boson Lorentz action as a complex algebra homomorphism. -/
noncomputable def realBosonComplexLorentzAlgHom (Λ : SL(2,ℂ)) :
    L.RealBosonEFTFreeDerivComplex →ₐ[ℂ] L.RealBosonEFTFreeDerivComplex :=
  (AlgHom.liftEquiv ℝ ℂ L.RealBosonEFTFreeDeriv L.RealBosonEFTFreeDerivComplex)
    ((Algebra.TensorProduct.includeRight :
      L.RealBosonEFTFreeDeriv →ₐ[ℝ] L.RealBosonEFTFreeDerivComplex).comp
      (realBosonLorentzAlgHom Λ))

/-- The Lorentz action on the bosonic factors as an algebra homomorphism. -/
noncomputable def bosonicLorentzAlgHom (Λ : SL(2,ℂ)) :
    L.ComplexScalarEFTFreeDeriv ⊗[ℂ] L.RealBosonEFTFreeDerivComplex →ₐ[ℂ]
      L.ComplexScalarEFTFreeDeriv ⊗[ℂ] L.RealBosonEFTFreeDerivComplex :=
  Algebra.TensorProduct.map (complexScalarLorentzAlgHom Λ) (realBosonComplexLorentzAlgHom Λ)

/-- The Lorentz action on the free-derivative Lagrangian as an algebra homomorphism. -/
noncomputable def lorentzAlgHom (Λ : SL(2,ℂ)) :
    L.EFTLagrangianFreeDeriv →ₐ[ℂ] L.EFTLagrangianFreeDeriv :=
  Algebra.TensorProduct.map (bosonicLorentzAlgHom Λ) (fermionicLorentzAlgHom Λ)

/-!

### A.2. Representation and compatibility

-/

/-- The representation of the Lorentz group on the free-derivative Lagrangian. -/
noncomputable def repLorentzGroup :
    Representation ℂ SL(2,ℂ) L.EFTLagrangianFreeDeriv :=
  ((ComplexScalarEFTFreeDeriv.repLorentzGroup (L := L)).tprod
    (RealBosonEFTFreeDerivComplex.repLorentzGroup (L := L))).tprod
    (FermionicEFTFreeDeriv.repLorentzGroup (L := L))

private lemma complexScalar_repLorentzGroup_apply (Λ : SL(2,ℂ))
    (x : L.ComplexScalarEFTFreeDeriv) :
    ComplexScalarEFTFreeDeriv.repLorentzGroup Λ x = complexScalarLorentzAlgHom Λ x := rfl

private lemma fermionic_repLorentzGroup_apply (Λ : SL(2,ℂ))
    (x : L.FermionicEFTFreeDeriv) :
    FermionicEFTFreeDeriv.repLorentzGroup Λ x = fermionicLorentzAlgHom Λ x := rfl

private lemma realBosonComplex_repLorentzGroup_apply (Λ : SL(2,ℂ))
    (x : L.RealBosonEFTFreeDerivComplex) :
    RealBosonEFTFreeDerivComplex.repLorentzGroup Λ x =
      realBosonComplexLorentzAlgHom Λ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c x =>
      change c ⊗ₜ[ℝ] realBosonLorentzAlgHom Λ x =
        c • (1 ⊗ₜ[ℝ] realBosonLorentzAlgHom Λ x)
      exact TensorProduct.tmul_eq_smul_one_tmul c _
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

private lemma bosonic_repLorentzGroup_apply (Λ : SL(2,ℂ))
    (x : L.ComplexScalarEFTFreeDeriv ⊗[ℂ] L.RealBosonEFTFreeDerivComplex) :
    ((ComplexScalarEFTFreeDeriv.repLorentzGroup (L := L)).tprod
      (RealBosonEFTFreeDerivComplex.repLorentzGroup (L := L))) Λ x =
      bosonicLorentzAlgHom Λ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      simp only [Representation.tprod_apply, TensorProduct.map_tmul]
      rw [complexScalar_repLorentzGroup_apply, realBosonComplex_repLorentzGroup_apply]
      simp [bosonicLorentzAlgHom]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- The tensor-product Lorentz representation agrees with its algebra homomorphism. -/
lemma repLorentzGroup_apply (Λ : SL(2,ℂ)) (x : L.EFTLagrangianFreeDeriv) :
    repLorentzGroup Λ x = lorentzAlgHom Λ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      simp only [repLorentzGroup, Representation.tprod_apply, TensorProduct.map_tmul]
      have hx := bosonic_repLorentzGroup_apply (L := L) Λ x
      simp only [Representation.tprod_apply] at hx
      rw [hx, fermionic_repLorentzGroup_apply]
      simp [lorentzAlgHom]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- The Lorentz representation preserves multiplication. -/
lemma repLorentzGroup_mul (Λ : SL(2,ℂ)) (V W : L.EFTLagrangianFreeDeriv) :
    repLorentzGroup Λ (V * W) = repLorentzGroup Λ V * repLorentzGroup Λ W := by
  calc
    repLorentzGroup Λ (V * W) = lorentzAlgHom Λ (V * W) := repLorentzGroup_apply Λ _
    _ = lorentzAlgHom Λ V * lorentzAlgHom Λ W := map_mul _ _ _
    _ = repLorentzGroup Λ V * repLorentzGroup Λ W :=
      congrArg₂ (· * ·) (repLorentzGroup_apply Λ V).symm
        (repLorentzGroup_apply Λ W).symm

/-- The Lorentz representation preserves the unit. -/
@[simp]
lemma repLorentzGroup_one (Λ : SL(2,ℂ)) :
    repLorentzGroup (L := L) Λ 1 = 1 := by
  calc
    repLorentzGroup (L := L) Λ 1 = lorentzAlgHom Λ 1 := repLorentzGroup_apply Λ _
    _ = 1 := map_one _

/-!

## B. Gauge-group action

### B.1. Algebra homomorphisms

-/

/-- The gauge action on the complex-scalar factor as an algebra homomorphism. -/
noncomputable def complexScalarGaugeAlgHom (g : G) :
    L.ComplexScalarEFTFreeDeriv →ₐ[ℂ] L.ComplexScalarEFTFreeDeriv :=
  SymmetricAlgebra.lift
    (SymmetricAlgebra.ι ℂ _ ∘ₗ ComplexScalarComponentSpaceWithDeriv.repGaugeGroup g)

/-- The gauge action on the fermionic factor as an algebra homomorphism. -/
noncomputable def fermionicGaugeAlgHom (g : G) :
    L.FermionicEFTFreeDeriv →ₐ[ℂ] L.FermionicEFTFreeDeriv :=
  ExteriorAlgebra.map (FermionicComponentSpaceWithDeriv.repGaugeGroup g)

/-- The gauge action on the real-boson factor as a real algebra homomorphism. -/
noncomputable def realBosonGaugeAlgHom (g : G) :
    L.RealBosonEFTFreeDeriv →ₐ[ℝ] L.RealBosonEFTFreeDeriv :=
  SymmetricAlgebra.lift
    (SymmetricAlgebra.ι ℝ _ ∘ₗ RealBosonComponentSpaceWithDeriv.repGaugeGroup g)

/-- The scalar extension of the real-boson gauge action as a complex algebra homomorphism. -/
noncomputable def realBosonComplexGaugeAlgHom (g : G) :
    L.RealBosonEFTFreeDerivComplex →ₐ[ℂ] L.RealBosonEFTFreeDerivComplex :=
  (AlgHom.liftEquiv ℝ ℂ L.RealBosonEFTFreeDeriv L.RealBosonEFTFreeDerivComplex)
    ((Algebra.TensorProduct.includeRight :
      L.RealBosonEFTFreeDeriv →ₐ[ℝ] L.RealBosonEFTFreeDerivComplex).comp
      (realBosonGaugeAlgHom g))

/-- The gauge action on the bosonic factors as an algebra homomorphism. -/
noncomputable def bosonicGaugeAlgHom (g : G) :
    L.ComplexScalarEFTFreeDeriv ⊗[ℂ] L.RealBosonEFTFreeDerivComplex →ₐ[ℂ]
      L.ComplexScalarEFTFreeDeriv ⊗[ℂ] L.RealBosonEFTFreeDerivComplex :=
  Algebra.TensorProduct.map (complexScalarGaugeAlgHom g) (realBosonComplexGaugeAlgHom g)

/-- The gauge action on the free-derivative Lagrangian as an algebra homomorphism. -/
noncomputable def gaugeAlgHom (g : G) :
    L.EFTLagrangianFreeDeriv →ₐ[ℂ] L.EFTLagrangianFreeDeriv :=
  Algebra.TensorProduct.map (bosonicGaugeAlgHom g) (fermionicGaugeAlgHom g)

/-!

### B.2. Representation and compatibility

-/

/-- The representation of the gauge group on the free-derivative Lagrangian. -/
noncomputable def repGaugeGroup : Representation ℂ G L.EFTLagrangianFreeDeriv :=
  ((ComplexScalarEFTFreeDeriv.repGaugeGroup (L := L)).tprod
    (RealBosonEFTFreeDerivComplex.repGaugeGroup (L := L))).tprod
    (FermionicEFTFreeDeriv.repGaugeGroup (L := L))

private lemma complexScalar_repGaugeGroup_apply (g : G)
    (x : L.ComplexScalarEFTFreeDeriv) :
    ComplexScalarEFTFreeDeriv.repGaugeGroup g x = complexScalarGaugeAlgHom g x := rfl

private lemma fermionic_repGaugeGroup_apply (g : G) (x : L.FermionicEFTFreeDeriv) :
    FermionicEFTFreeDeriv.repGaugeGroup g x = fermionicGaugeAlgHom g x := rfl

private lemma realBosonComplex_repGaugeGroup_apply (g : G)
    (x : L.RealBosonEFTFreeDerivComplex) :
    RealBosonEFTFreeDerivComplex.repGaugeGroup g x =
      realBosonComplexGaugeAlgHom g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c x =>
      change c ⊗ₜ[ℝ] realBosonGaugeAlgHom g x =
        c • (1 ⊗ₜ[ℝ] realBosonGaugeAlgHom g x)
      exact TensorProduct.tmul_eq_smul_one_tmul c _
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

private lemma bosonic_repGaugeGroup_apply (g : G)
    (x : L.ComplexScalarEFTFreeDeriv ⊗[ℂ] L.RealBosonEFTFreeDerivComplex) :
    ((ComplexScalarEFTFreeDeriv.repGaugeGroup (L := L)).tprod
      (RealBosonEFTFreeDerivComplex.repGaugeGroup (L := L))) g x =
      bosonicGaugeAlgHom g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      simp only [Representation.tprod_apply, TensorProduct.map_tmul]
      rw [complexScalar_repGaugeGroup_apply, realBosonComplex_repGaugeGroup_apply]
      simp [bosonicGaugeAlgHom]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- The tensor-product gauge representation agrees with its algebra homomorphism. -/
lemma repGaugeGroup_apply (g : G) (x : L.EFTLagrangianFreeDeriv) :
    repGaugeGroup g x = gaugeAlgHom g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      simp only [repGaugeGroup, Representation.tprod_apply, TensorProduct.map_tmul]
      have hx := bosonic_repGaugeGroup_apply (L := L) g x
      simp only [Representation.tprod_apply] at hx
      rw [hx, fermionic_repGaugeGroup_apply]
      simp [gaugeAlgHom]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- The gauge representation preserves multiplication. -/
lemma repGaugeGroup_mul (g : G) (V W : L.EFTLagrangianFreeDeriv) :
    repGaugeGroup g (V * W) = repGaugeGroup g V * repGaugeGroup g W := by
  calc
    repGaugeGroup g (V * W) = gaugeAlgHom g (V * W) := repGaugeGroup_apply g _
    _ = gaugeAlgHom g V * gaugeAlgHom g W := map_mul _ _ _
    _ = repGaugeGroup g V * repGaugeGroup g W :=
      congrArg₂ (· * ·) (repGaugeGroup_apply g V).symm
        (repGaugeGroup_apply g W).symm

/-- The gauge representation preserves the unit. -/
@[simp]
lemma repGaugeGroup_one (g : G) : repGaugeGroup (L := L) g 1 = 1 := by
  calc
    repGaugeGroup (L := L) g 1 = gaugeAlgHom g 1 := repGaugeGroup_apply g _
    _ = 1 := map_one _

/-!

## C. The `IsInvariant` condition

This section is reserved for the predicate expressing simultaneous Lorentz and gauge invariance.

-/

end EFTLagrangianFreeDeriv

end

end LagrangianTheory
