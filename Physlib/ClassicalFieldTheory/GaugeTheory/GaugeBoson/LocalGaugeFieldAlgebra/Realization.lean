/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeBoson.LocalGaugeFieldAlgebra.FieldStrength
public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeBoson.Realization.Basic
public import Physlib.Mathematics.AlgebraRepresentation
/-!
# Realizations of the local gauge field algebra

## i. Overview

A real algebra `B` carries the gauge bosons when the local gauge field algebra maps into it
by a real algebra map equivariant for the jet gauge group and the Lorentz group, both acting
on `B` by algebra endomorphisms: `LocalGaugeFieldAlgebra.Realization`. The derivative
symbols of `B` are the images of the algebra's own symbols `∂_s A_μ^φ` (`Realization.A`);
no derivative operator on `B` is involved.

`GaugeAlgebraRealization` is the same notion with complex scalars, out of the
complexification `ℂ ⊗[ℝ] LocalGaugeFieldAlgebra 𝔤`. For a complex target the two agree by
the universal property of base change `AlgHom.liftEquiv` (section D); the real algebra is
never identified with its complexification.

## ii. Key results

- `LocalGaugeFieldAlgebra.Realization` : an algebra carrying the gauge bosons over `ℝ`.
- `LocalGaugeFieldAlgebra.Realization.A` : the derivative symbols of a realization, with the
  laws `gauge_apply_deriv` and `lorentz_apply` and the extensionality `ext_A`.
- `LocalGaugeFieldAlgebra.Realization.toAlgHom_covDerivFieldStrength` : the map carries the
  covariant derivatives of the field strength to those of the symbols of `B`.
- `LocalGaugeFieldAlgebra.Realization.equivGaugeAlgebraRealization` : for a complex target,
  real realizations are the complex realizations.

## iii. Table of contents

- A. Realizations
- B. The derivative symbols of a realization
- C. The field strength of a realization
- D. Comparison with the complex realizations

-/

@[expose] public section

set_option linter.unusedSectionVars false

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
variable {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
variable {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J}

open TensorProduct Matrix MatrixGroups Lorentz

namespace LocalGaugeFieldAlgebra

/-!

## A. Realizations

-/

/-- A real algebra `B` carrying the gauge bosons of the package `jets`: a real algebra map
  out of the local gauge field algebra, equivariant for the jet gauge group and the Lorentz
  group, both acting on the whole of `B` by algebra endomorphisms. -/
@[ext]
structure Realization (jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J) (B : Type) [Ring B] [Algebra ℝ B]
    (repJet : Representation ℝ GJ B) (repLorentz : Representation ℝ SL(2,ℂ) B) where
  /-- The algebra map out of the local gauge field algebra. -/
  toAlgHom : LocalGaugeFieldAlgebra 𝔤 →ₐ[ℝ] B
  /-- The map is equivariant for the jet gauge group. -/
  map_repJet : ∀ (U : GJ) (x : LocalGaugeFieldAlgebra 𝔤),
    toAlgHom (LocalGaugeFieldAlgebra.repJet jets U x) = repJet U (toAlgHom x)
  /-- The map is equivariant for the Lorentz group. -/
  map_repLorentz : ∀ (Λ : SL(2,ℂ)) (x : LocalGaugeFieldAlgebra 𝔤),
    toAlgHom (LocalGaugeFieldAlgebra.repLorentzGroup 𝔤 Λ x) = repLorentz Λ (toAlgHom x)
  /-- The jet gauge group acts on the whole of `B` by algebra endomorphisms. -/
  repJet_mul : ∀ (U : GJ) (b₁ b₂ : B), repJet U (b₁ * b₂) = repJet U b₁ * repJet U b₂
  /-- The Lorentz group acts on the whole of `B` by algebra endomorphisms. -/
  repLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂

namespace Realization

section RealTarget

variable {B : Type} [Ring B] [Algebra ℝ B] {repJet : Representation ℝ GJ B}
  {repLorentz : Representation ℝ SL(2,ℂ) B}

variable (jets) in
/-- The local gauge field algebra realized in itself, by the identity. -/
noncomputable def id : Realization jets (LocalGaugeFieldAlgebra 𝔤)
    (LocalGaugeFieldAlgebra.repJet jets) (repLorentzGroup 𝔤) where
  toAlgHom := AlgHom.id ℝ _
  map_repJet _ _ := rfl
  map_repLorentz _ _ := rfl
  repJet_mul := repJet_apply_mul
  repLorentz_mul := repLorentzGroup_apply_mul

@[simp]
lemma id_toAlgHom : (id jets).toAlgHom = AlgHom.id ℝ (LocalGaugeFieldAlgebra 𝔤) := rfl

variable (h : Realization jets B repJet repLorentz)

/-!

## B. The derivative symbols of a realization

-/

/-- The derivative symbols `∂_s A_μ^φ` of a realization: the images of the algebra's own
  symbols `derivA`. -/
noncomputable def A (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) :
    Module.Dual ℝ 𝔤 →ₗ[ℝ] B :=
  h.toAlgHom.toLinearMap ∘ₗ derivA 𝔤 s μ

lemma A_apply (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    h.A s μ φ = h.toAlgHom (derivA 𝔤 s μ φ) := rfl

@[simp]
lemma id_A : (id jets).A = derivA 𝔤 := rfl

lemma commute_A (p q : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ ψ : Module.Dual ℝ 𝔤) : Commute (h.A p μ φ) (h.A q ν ψ) :=
  (Commute.all _ _).map h.toAlgHom

/-- Two realizations with the same derivative symbols are equal. -/
lemma ext_A {h₁ h₂ : Realization jets B repJet repLorentz}
    (hA : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤),
      h₁.A s μ φ = h₂.A s μ φ) : h₁ = h₂ :=
  Realization.ext (algHom_ext hA)

/-- The gauge law: a jet `U` acts on `∂_s A_μ^φ` by the Leibniz convolution of the dual
  adjoint Taylor coefficients of `U⁻¹` against lower symbols, plus the base-point value of
  the `s`-th derivative of the Maurer–Cartan form of `U⁻¹`. -/
lemma gauge_apply_deriv (U : GJ) (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ 𝔤) :
    repJet U (h.A s μ φ) =
      (s.antidiagonal.map fun p => h.A p.2 μ (jets.adjointDualCoeff U⁻¹ p.1 φ)).sum
      + algebraMap ℝ B (φ (jets.evalLie (jets.iteratedDeriv s (jets.maurerCartan U⁻¹ μ)))) := by
  rw [A_apply, ← h.map_repJet, derivA_apply, repJet_iteratedJetDeriv_ofA, map_add,
    map_multiset_sum, Multiset.map_map, AlgHom.commutes]
  rfl

/-- The Lorentz law: the symbol carries one covector index, and each derivative slot
  transforms as a covector. -/
lemma lorentz_apply (Λ : SL(2,ℂ)) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ 𝔤) :
    repLorentz Λ (h.A (List.ofFn l) μ φ) =
      ∑ p : Fin n → (Fin 1 ⊕ Fin 3), (∏ i, ((SL2C.toLorentzGroup Λ).1 (p i) (l i) : ℝ)) •
        ∑ a, ((SL2C.toLorentzGroup Λ).1 a μ : ℝ) • h.A (List.ofFn p) a φ := by
  rw [A_apply, ← h.map_repLorentz, repLorentzGroup_derivA, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul, map_sum]
  exact congrArg _ (Finset.sum_congr rfl fun a _ => map_smul h.toAlgHom _ _)

/-!

## C. The field strength of a realization

-/

/-- The map of a realization carries the covariant derivatives of the field strength to
  those of its symbols. -/
lemma toAlgHom_covDerivFieldStrength (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ 𝔤) :
    h.toAlgHom (covDerivFieldStrength 𝔤 l μ ν φ)
      = GaugeAlgebraRealization.iteratedCovDerivAdjoint h.A l
        (GaugeAlgebraRealization.fieldStrength h.A μ ν) 0 φ := by
  have key := congrFun (GaugeAlgebraRealization.iteratedCovDerivAdjoint_map
    h.toAlgHom.toLinearMap (map_mul h.toAlgHom) (derivA 𝔤) l
    (GaugeAlgebraRealization.fieldStrength (derivA 𝔤) μ ν)) 0
  rw [show (fun p => h.toAlgHom.toLinearMap ∘ₗ
        GaugeAlgebraRealization.fieldStrength (derivA 𝔤) μ ν p)
      = GaugeAlgebraRealization.fieldStrength h.A μ ν from
      funext fun p => (GaugeAlgebraRealization.fieldStrength_map _ (map_mul h.toAlgHom) _ μ ν
        p).symm] at key
  exact (LinearMap.congr_fun key φ).symm

lemma toAlgHom_fieldStrength (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    h.toAlgHom (fieldStrength 𝔤 μ ν φ) = GaugeAlgebraRealization.fieldStrength h.A μ ν 0 φ :=
  h.toAlgHom_covDerivFieldStrength [] μ ν φ

end RealTarget

/-!

## D. Comparison with the complex realizations

-/

section ComplexTarget

variable {B : Type} [Ring B] [Algebra ℂ B] {repJet : Representation ℂ GJ B}
  {repLorentz : Representation ℂ SL(2,ℂ) B}

/-- The complexification of a jet-equivariant real algebra map is equivariant for the
  complexified jet action. -/
lemma liftEquiv_complexRepJet (f : LocalGaugeFieldAlgebra 𝔤 →ₐ[ℝ] B)
    (hf : ∀ (U : GJ) (x : LocalGaugeFieldAlgebra 𝔤),
      f (LocalGaugeFieldAlgebra.repJet jets U x) = repJet U (f x))
    (U : GJ) (x : ℂ ⊗[ℝ] LocalGaugeFieldAlgebra 𝔤) :
    AlgHom.liftEquiv ℝ ℂ (LocalGaugeFieldAlgebra 𝔤) B f (complexRepJet jets U x)
      = repJet U (AlgHom.liftEquiv ℝ ℂ (LocalGaugeFieldAlgebra 𝔤) B f x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul z a =>
    rw [complexRepJet_tmul, AlgHom.liftEquiv_tmul, AlgHom.liftEquiv_tmul, map_smul (repJet U),
      hf]

/-- The complexification of a Lorentz-equivariant real algebra map is equivariant for the
  complexified Lorentz action. -/
lemma liftEquiv_complexRepLorentzGroup (f : LocalGaugeFieldAlgebra 𝔤 →ₐ[ℝ] B)
    (hf : ∀ (Λ : SL(2,ℂ)) (x : LocalGaugeFieldAlgebra 𝔤),
      f (LocalGaugeFieldAlgebra.repLorentzGroup 𝔤 Λ x) = repLorentz Λ (f x))
    (Λ : SL(2,ℂ)) (x : ℂ ⊗[ℝ] LocalGaugeFieldAlgebra 𝔤) :
    AlgHom.liftEquiv ℝ ℂ (LocalGaugeFieldAlgebra 𝔤) B f (complexRepLorentzGroup 𝔤 Λ x)
      = repLorentz Λ (AlgHom.liftEquiv ℝ ℂ (LocalGaugeFieldAlgebra 𝔤) B f x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul z a =>
    rw [complexRepLorentzGroup_tmul, AlgHom.liftEquiv_tmul, AlgHom.liftEquiv_tmul,
      map_smul (repLorentz Λ), hf]

/-- The complexification of a real realization in a complex algebra, by `AlgHom.liftEquiv`;
  the symbols are unchanged. -/
noncomputable def toGaugeAlgebraRealization
    (h : Realization jets B (repJet.restrictScalars ℝ) (repLorentz.restrictScalars ℝ)) :
    GaugeAlgebraRealization jets B repJet repLorentz where
  toAlgHom := AlgHom.liftEquiv ℝ ℂ (LocalGaugeFieldAlgebra 𝔤) B h.toAlgHom
  A := h.A
  A_eq s μ φ := by
    rw [gaugeField_eq_one_tmul_derivA, AlgHom.liftEquiv_tmul, one_smul]
    rfl
  map_repJet := liftEquiv_complexRepJet h.toAlgHom h.map_repJet
  map_repLorentz := liftEquiv_complexRepLorentzGroup h.toAlgHom h.map_repLorentz
  repJet_mul := h.repJet_mul
  repLorentz_mul := h.repLorentz_mul

@[simp]
lemma toGaugeAlgebraRealization_A
    (h : Realization jets B (repJet.restrictScalars ℝ) (repLorentz.restrictScalars ℝ)) :
    h.toGaugeAlgebraRealization.A = h.A := rfl

lemma toGaugeAlgebraRealization_toAlgHom_one_tmul
    (h : Realization jets B (repJet.restrictScalars ℝ) (repLorentz.restrictScalars ℝ))
    (x : LocalGaugeFieldAlgebra 𝔤) :
    h.toGaugeAlgebraRealization.toAlgHom ((1 : ℂ) ⊗ₜ[ℝ] x) = h.toAlgHom x := by
  rw [toGaugeAlgebraRealization, AlgHom.liftEquiv_tmul, one_smul]

/-- The restriction of scalars of a complex realization: the algebra map precomposed with
  `x ↦ 1 ⊗ₜ x`. -/
noncomputable def _root_.GaugeAlgebraRealization.toRealization
    (h : GaugeAlgebraRealization jets B repJet repLorentz) :
    Realization jets B (repJet.restrictScalars ℝ) (repLorentz.restrictScalars ℝ) where
  toAlgHom := (AlgHom.liftEquiv ℝ ℂ (LocalGaugeFieldAlgebra 𝔤) B).symm h.toAlgHom
  map_repJet U x := by
    show h.toAlgHom ((1 : ℂ) ⊗ₜ[ℝ] LocalGaugeFieldAlgebra.repJet jets U x)
      = repJet U (h.toAlgHom ((1 : ℂ) ⊗ₜ[ℝ] x))
    rw [← complexRepJet_tmul, h.map_repJet]
  map_repLorentz Λ x := by
    show h.toAlgHom ((1 : ℂ) ⊗ₜ[ℝ] LocalGaugeFieldAlgebra.repLorentzGroup 𝔤 Λ x)
      = repLorentz Λ (h.toAlgHom ((1 : ℂ) ⊗ₜ[ℝ] x))
    rw [← complexRepLorentzGroup_tmul, h.map_repLorentz]
  repJet_mul := h.repJet_mul
  repLorentz_mul := h.repLorentz_mul

@[simp]
lemma _root_.GaugeAlgebraRealization.toRealization_toAlgHom_apply
    (h : GaugeAlgebraRealization jets B repJet repLorentz) (x : LocalGaugeFieldAlgebra 𝔤) :
    h.toRealization.toAlgHom x = h.toAlgHom ((1 : ℂ) ⊗ₜ[ℝ] x) := rfl

@[simp]
lemma _root_.GaugeAlgebraRealization.toRealization_A
    (h : GaugeAlgebraRealization jets B repJet repLorentz) : h.toRealization.A = h.A := by
  funext s μ
  refine LinearMap.ext fun φ => ?_
  rw [h.A_apply, gaugeField_eq_one_tmul_derivA]
  rfl

lemma _root_.GaugeAlgebraRealization.toRealization_id_toAlgHom :
    (GaugeAlgebraRealization.id jets).toRealization.toAlgHom
      = (Algebra.TensorProduct.includeRight :
          LocalGaugeFieldAlgebra 𝔤 →ₐ[ℝ] ℂ ⊗[ℝ] LocalGaugeFieldAlgebra 𝔤) :=
  AlgHom.ext fun _ => rfl

/-- For a complex target, real realizations are the complex realizations. -/
noncomputable def equivGaugeAlgebraRealization :
    Realization jets B (repJet.restrictScalars ℝ) (repLorentz.restrictScalars ℝ)
      ≃ GaugeAlgebraRealization jets B repJet repLorentz where
  toFun := toGaugeAlgebraRealization
  invFun := GaugeAlgebraRealization.toRealization
  left_inv h := Realization.ext
    ((AlgHom.liftEquiv ℝ ℂ (LocalGaugeFieldAlgebra 𝔤) B).symm_apply_apply h.toAlgHom)
  right_inv h := GaugeAlgebraRealization.ext
    ((AlgHom.liftEquiv ℝ ℂ (LocalGaugeFieldAlgebra 𝔤) B).apply_symm_apply h.toAlgHom)

end ComplexTarget

end Realization

end LocalGaugeFieldAlgebra
