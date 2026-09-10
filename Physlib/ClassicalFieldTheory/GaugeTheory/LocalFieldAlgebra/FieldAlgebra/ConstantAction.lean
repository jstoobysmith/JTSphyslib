/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalFieldAlgebra.FieldAlgebra.GaugeAction
/-!
# Constant gauge transformations on a field algebra

## i. Overview

A jet gauge group `G` contains the constant — that is, global — gauge transformations as
the image of a homomorphism `ι : G₀ →* G` from the value group `G₀` (for the Standard Model,
`JetGaugeGroupI.ofConstant`). Restricting the jet gauge action `FieldAlgebra.repJet` along
`ι` gives the action of the global gauge group on the field algebra, which is diagonal in
the derivative label: it is the action whose invariants the classification theorems
describe.

## ii. Key results

- `FieldAlgebra.repConstant` : the action of the constant gauge transformations.
- `FieldAlgebra.repConstant_ofField`, `FieldAlgebra.repConstant_ofConjField` : on the
  undifferentiated field it is the contragredient of the value.

-/

@[expose] public section

namespace FieldAlgebra

open TensorProduct

variable {G : Type} [Group G] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {G₀ : Type} [Group G₀] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G 𝔤 G₀ 𝔤J} (M : MatterField jets)
variable {A : Type} [Ring A] [Algebra ℂ A] [IsFieldAlgebra (JetComponentSpace M) A]
variable (ι : G₀ →* G)

/-- The action of the constant — that is, global — gauge transformations on the field
  algebra: the restriction of the jet gauge action along the inclusion `ι : G₀ →* G` of the
  constant jets. -/
noncomputable def repConstant :
    Representation ℂ G₀ A :=
  (repJet M).comp ι

lemma repConstant_apply
    (g : G₀) (x : A) :
    repConstant M ι g x =
      repJet M (ι g) x := rfl

@[simp]
lemma repConstant_apply_one
    (g : G₀) :
    repConstant M ι g (1 : A) = 1 :=
  repJet_apply_one M _

lemma repConstant_apply_mul
    (g : G₀) (x y : A) :
    repConstant M ι g (x * y) =
      repConstant M ι g x * repConstant M ι g y :=
  repJet_apply_mul M _ x y

/-- A constant gauge transformation acts on the undifferentiated field by the
  contragredient of its value — which for a constant jet is the transformation itself. -/
lemma repConstant_ofField
    (g : G₀) (φ : Module.Dual ℂ M.V) :
    repConstant M ι g (ofField A φ) =
      ofField A (Module.Dual.transpose
        (jetEval ∘ₗ (M.repJet (ι g⁻¹)).comp jetOfConstant) φ) := by
  have h : (ι g)⁻¹ = ι g⁻¹ :=
    (map_inv ι g).symm
  rw [repConstant_apply, repJet_ofField, h]

/-- A constant gauge transformation acts on the undifferentiated conjugate field by the
  conjugate contragredient of its value. -/
lemma repConstant_ofConjField
    (g : G₀) (φ : Module.Dual ℂ (ConjModule M.V)) :
    repConstant M ι g (ofConjField A φ) =
      ofConjField A (Module.Dual.transpose
        (jetEval ∘ₗ (JetComponentSpace.repConj M.repJet (ι g⁻¹)).comp
          jetOfConstant) φ) := by
  have h : (ι g)⁻¹ = ι g⁻¹ :=
    (map_inv ι g).symm
  rw [repConstant_apply, repJet_ofConjField, h]

end FieldAlgebra
