/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeBoson.GaugeJetAlgebra.LorentzAction
public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeBoson.GaugeJetAlgebra.GaugeAction
public import Physlib.ClassicalFieldTheory.GaugeTheory.GaugeBoson.Realization.Symmetrized
/-!
# Realizations of the gauge-boson jet algebra

## i. Overview

An algebra `B` carries the gauge bosons of a gauge theory when the gauge-boson jet algebra,
the universal algebra on the symbols `∂_s A_μ^φ`, maps into it compatibly with the actions
of the jet gauge group and of the Lorentz group. That is the structure
`GaugeAlgebraRealization`: an algebra map `ℂ ⊗[ℝ] GaugeJetAlgebra 𝔤 →ₐ[ℂ] B` equivariant for
the two groups, together with the demands that both groups act on the whole of `B` by
algebra endomorphisms. It is the gauge-boson part of the Standard Model's
`AlgebraRealization`, for any local-gauge-data package `jets`.

The gauge-field symbols of a realization are the jet algebra's own symbols pushed along
the map, `GaugeAlgebraRealization.A`, and their transformation laws are the jet algebra's
own laws pushed along it, `GaugeAlgebraRealization.isGaugeField`. The base case is the jet
algebra realized in itself: its symbols satisfy the laws `IsGaugeField` because the Lorentz
law is that of a Lorentz derivative and the gauge law is the substitution action of the jet
gauge group constructed in `GaugeJetAlgebra.GaugeAction`.

Everything the theory of the laws derives, the covariant derivative, the field strength and
the classification of invariants, then applies to every realization through its predicate
`IsGaugeField`, which is the form of the laws the theorems consume; the classification for
a realization is in `Invariants.lean`.

## ii. Key results

- `GaugeJetAlgebra.gaugeField` : the gauge-field symbols of the jet algebra.
- `GaugeJetAlgebra.isGaugeField` : the jet algebra is a gauge field.
- `GaugeAlgebraRealization` : an algebra carrying the gauge bosons, as an equivariant
  algebra map out of the jet algebra.
- `GaugeAlgebraRealization.id` : the jet algebra realized in itself.
- `GaugeAlgebraRealization.A`, `GaugeAlgebraRealization.isGaugeField` : the gauge-field
  symbols of a realization and their laws.

## iii. Table of contents

- A. The gauge-field structure of the jet algebra
- B. Realizations

-/

@[expose] public section

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
variable {G₀ : Type} [Group G₀] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
variable {jets : LocalGaugeData G 𝔤 G₀ 𝔤J}

set_option maxHeartbeats 1000000


namespace GaugeJetAlgebra

open TensorProduct Matrix MatrixGroups

/-!

## A. The gauge-field structure of the jet algebra

-/

/-!

### A.1. The gauge-field derivative symbols

-/

variable (𝔤) in
/-- The gauge-field derivative symbols of the complexified gauge-boson jet algebra, as a
  family over the derivative multiset, the spacetime index and the dual of the gauge
  algebra — the form consumed by the abstract covariance machinery. -/
noncomputable def gaugeField (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) :
    Module.Dual ℝ 𝔤 →ₗ[ℝ] ℂ ⊗[ℝ] (GaugeJetAlgebra 𝔤) :=
  (Lorentz.iteratedD (complexJetDeriv 𝔤) complexJetDeriv_comm s).restrictScalars ℝ ∘ₗ
    (TensorProduct.mk ℝ ℂ (GaugeJetAlgebra 𝔤) 1).comp ((ofA 𝔤) μ)

@[simp]
lemma gaugeField_apply (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ 𝔤) :
    (gaugeField 𝔤) s μ φ = Lorentz.iteratedD (complexJetDeriv 𝔤) complexJetDeriv_comm s
      ((1 : ℂ) ⊗ₜ[ℝ] (ofA 𝔤) μ φ) := rfl

/-!

### A.2. The laws

-/

variable (jets) in
/-- The complexified gauge-boson jet algebra is a gauge field: its derivative symbols
  are those of a Lorentz covector, transform under the jet gauge group by the all-orders
  Leibniz convolution of the adjoint Taylor coefficients plus the Maurer–Cartan shift, and
  the gauge action is multiplicative. -/
theorem isGaugeField :
    IsGaugeField jets (complexRepLorentzGroup 𝔤) (complexRepJet jets) (gaugeField 𝔤) where
  lorentz_apply Λ n l μ φ := by
    calc (complexRepLorentzGroup 𝔤) Λ ((gaugeField 𝔤) (List.ofFn l) μ φ)
        = ∑ p : Fin n → (Fin 1 ⊕ Fin 3),
            (∏ i, (((Lorentz.SL2C.toLorentzGroup Λ).1 (p i) (l i) : ℝ) : ℂ)) •
            Lorentz.iteratedD (complexJetDeriv 𝔤) complexJetDeriv_comm (List.ofFn p)
              ((complexRepLorentzGroup 𝔤) Λ ((1 : ℂ) ⊗ₜ[ℝ] (ofA 𝔤) μ φ)) :=
          Lorentz.IsLorentzDeriv.rep_iteratedD_ofFn complexJetDeriv_comm Λ l
            ((1 : ℂ) ⊗ₜ[ℝ] (ofA 𝔤) μ φ)
      _ = _ := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [complexRepLorentzGroup_one_tmul_ofA, map_sum]
          refine congrArg (HSMul.hSMul _) (Finset.sum_congr rfl fun a _ => ?_)
          rw [map_smul]
          rfl
  gauge_apply_deriv U s μ φ := complexRepJet_iteratedD_one_tmul_ofA U s μ φ
  gauge_mul U b₁ b₂ := complexRepJet_apply_mul U b₁ b₂

end GaugeJetAlgebra

/-!

## B. Realizations

-/

open TensorProduct Matrix MatrixGroups

/-- An algebra `B` carrying the gauge bosons of the package `jets`: an algebra map out of
  the complexified gauge-boson jet algebra, equivariant for the jet gauge group and the
  Lorentz group, with both groups acting on the whole of `B` by algebra endomorphisms.
  The gauge-field symbols of `B` are the images of the jet algebra's symbols,
  `GaugeAlgebraRealization.A`, and they satisfy the laws `IsGaugeField` by transport. -/
structure GaugeAlgebraRealization (jets : LocalGaugeData G 𝔤 G₀ 𝔤J) (B : Type) [Ring B]
    [Algebra ℂ B] (repJet : Representation ℂ G B) (repLorentz : Representation ℂ SL(2,ℂ) B)
    where
  /-- The algebra map out of the gauge-boson jet algebra: it places the gauge-boson
    symbols, and every polynomial expression in them, inside `B`. -/
  toAlgHom : ℂ ⊗[ℝ] GaugeJetAlgebra 𝔤 →ₐ[ℂ] B
  /-- The map is equivariant for the jet gauge group. -/
  map_repJet : ∀ (U : G) (x : ℂ ⊗[ℝ] GaugeJetAlgebra 𝔤),
    toAlgHom (GaugeJetAlgebra.complexRepJet jets U x) = repJet U (toAlgHom x)
  /-- The map is equivariant for the Lorentz group. -/
  map_repLorentz : ∀ (Λ : SL(2,ℂ)) (x : ℂ ⊗[ℝ] GaugeJetAlgebra 𝔤),
    toAlgHom (GaugeJetAlgebra.complexRepLorentzGroup 𝔤 Λ x) = repLorentz Λ (toAlgHom x)
  /-- The jet gauge group acts on the whole of `B` by algebra endomorphisms. -/
  repJet_mul : ∀ (U : G) (b₁ b₂ : B), repJet U (b₁ * b₂) = repJet U b₁ * repJet U b₂
  /-- The Lorentz group acts on the whole of `B` by algebra endomorphisms. -/
  repLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂

namespace GaugeAlgebraRealization

open GaugeJetAlgebra

variable {B : Type} [Ring B] [Algebra ℂ B] {repJet : Representation ℂ G B}
  {repLorentz : Representation ℂ SL(2,ℂ) B}

variable (jets) in
/-- The gauge-boson jet algebra realized in itself, by the identity. -/
noncomputable def id : GaugeAlgebraRealization jets (ℂ ⊗[ℝ] GaugeJetAlgebra 𝔤)
    (complexRepJet jets) (complexRepLorentzGroup 𝔤) where
  toAlgHom := AlgHom.id ℂ _
  map_repJet _ _ := rfl
  map_repLorentz _ _ := rfl
  repJet_mul := complexRepJet_apply_mul
  repLorentz_mul := complexRepLorentzGroup_apply_mul

variable (h : GaugeAlgebraRealization jets B repJet repLorentz)

/-- The gauge-field symbols `∂_s A_μ^φ` of a realization: the jet algebra's symbols pushed
  along the map. -/
noncomputable def A (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) :
    Module.Dual ℝ 𝔤 →ₗ[ℝ] B :=
  h.toAlgHom.toLinearMap.restrictScalars ℝ ∘ₗ gaugeField 𝔤 s μ

@[simp]
lemma A_apply (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    h.A s μ φ = h.toAlgHom (gaugeField 𝔤 s μ φ) := rfl

/-- The gauge-field symbols of a realization commute, being images of a commutative
  algebra. -/
lemma commute_A (p q : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ ψ : Module.Dual ℝ 𝔤) : Commute (h.A p μ φ) (h.A q ν ψ) :=
  (Commute.all _ _).map h.toAlgHom

/-- The gauge-field laws of a realization, obtained from the laws of the jet algebra by
  pushing them along the defining algebra map. -/
theorem isGaugeField : IsGaugeField jets repLorentz repJet h.A where
  lorentz_apply Λ n l μ φ := by
    have key := congrArg h.toAlgHom ((GaugeJetAlgebra.isGaugeField jets).lorentz_apply Λ n l μ φ)
    rw [h.map_repLorentz] at key
    refine key.trans ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_smul, map_sum]
    exact congrArg _ (Finset.sum_congr rfl fun a _ => map_smul h.toAlgHom _ _)
  gauge_apply_deriv U s μ φ := by
    have key := congrArg h.toAlgHom ((GaugeJetAlgebra.isGaugeField jets).gauge_apply_deriv U s μ φ)
    rw [h.map_repJet] at key
    refine key.trans ?_
    rw [map_add, map_multiset_sum, Multiset.map_map, AlgHom.commutes]
    rfl
  gauge_mul := h.repJet_mul

end GaugeAlgebraRealization
