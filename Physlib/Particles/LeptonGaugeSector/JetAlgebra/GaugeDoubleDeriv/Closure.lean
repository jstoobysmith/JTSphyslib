/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.LorentzAction
/-!
# The second derivatives of the field strength span a subrepresentation

The span of the monomials `∂_ρ ∂_τ F_{μν}` is carried to itself by both group actions on the jet
algebra. Statements proved for the span may therefore be combined with any operator built from
the group elements, an average or a projector among them, without leaving the span.

*Both closures are the covariance of the field strength.* Under the Lorentz group each of the
four indices of `∂_ρ ∂_τ F_{μν}` is rotated into the others and nothing else
(`repLorentzGroup_fieldStrengthDeriv_pair`). Under the gauge group the field strength and its
derivatives are fixed outright (`repJetGaugeGroupI_fieldStrengthDeriv`), so the span is fixed
pointwise.

## Key results

- `JetAlgebra.repLorentzGroup_mem_span_fieldStrengthDeriv_pair` : the span is closed under the
  Lorentz action, and `map_repLorentzGroup_span_fieldStrengthDeriv_pair` states this as an
  equality of submodules.
- `JetAlgebra.repJetGaugeGroupI_apply_of_mem_span_fieldStrengthDeriv_pair` : the gauge group
  fixes the span pointwise, whence `map_repJetGaugeGroupI_span_fieldStrengthDeriv_pair`.

-/

@[expose] public section

namespace LeptonGaugeSector
open TensorProduct StandardModel

namespace JetAlgebra

open scoped minkowskiMatrix PauliMatrix
open Matrix MatrixGroups

/-!

## A. The generators

-/

/-- A second derivative of a field strength lies in their span. -/
lemma fieldStrengthDeriv_pair_mem_span (ρ τ μ ν : Fin 1 ⊕ Fin 3) :
    fieldStrengthDeriv {ρ, τ} μ ν ∈
      Submodule.span ℂ {y : JetAlgebra | ∃ ρ τ μ ν, y = fieldStrengthDeriv {ρ, τ} μ ν} :=
  Submodule.subset_span ⟨ρ, τ, μ, ν, rfl⟩

/-- The Lorentz action carries a second derivative of a field strength into their span: each of
  the four indices is rotated into the others. -/
lemma repLorentzGroup_fieldStrengthDeriv_pair_mem_span (Λ : SL(2,ℂ)) (ρ τ μ ν : Fin 1 ⊕ Fin 3) :
    repLorentzGroup Λ (fieldStrengthDeriv {ρ, τ} μ ν) ∈
      Submodule.span ℂ {y : JetAlgebra | ∃ ρ τ μ ν, y = fieldStrengthDeriv {ρ, τ} μ ν} := by
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  exact Submodule.sum_mem _ fun r _ => Submodule.sum_mem _ fun s _ =>
    Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
      Submodule.smul_mem _ _ (fieldStrengthDeriv_pair_mem_span r s a b)

/-!

## B. Closure under the Lorentz group

-/

/-- **The span of the second derivatives of the field strength is closed under the Lorentz
  action.** -/
lemma repLorentzGroup_mem_span_fieldStrengthDeriv_pair (Λ : SL(2,ℂ)) {x : JetAlgebra}
    (hx : x ∈ Submodule.span ℂ {y : JetAlgebra | ∃ ρ τ μ ν, y = fieldStrengthDeriv {ρ, τ} μ ν}) :
    repLorentzGroup Λ x ∈
      Submodule.span ℂ {y : JetAlgebra | ∃ ρ τ μ ν, y = fieldStrengthDeriv {ρ, τ} μ ν} := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨ρ, τ, μ, ν, rfl⟩ := hy
    exact repLorentzGroup_fieldStrengthDeriv_pair_mem_span Λ ρ τ μ ν
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u v _ _ hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv
  | smul c u _ hu => rw [map_smul]; exact Submodule.smul_mem _ _ hu

/-- **The span of the second derivatives of the field strength is a subrepresentation of the
  Lorentz group.** -/
lemma map_repLorentzGroup_span_fieldStrengthDeriv_pair (Λ : SL(2,ℂ)) :
    Submodule.map (repLorentzGroup Λ)
        (Submodule.span ℂ {y : JetAlgebra | ∃ ρ τ μ ν, y = fieldStrengthDeriv {ρ, τ} μ ν}) =
      Submodule.span ℂ {y : JetAlgebra | ∃ ρ τ μ ν, y = fieldStrengthDeriv {ρ, τ} μ ν} := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro x ⟨u, hu, rfl⟩
    exact repLorentzGroup_mem_span_fieldStrengthDeriv_pair Λ hu
  · exact ⟨repLorentzGroup Λ⁻¹ x, repLorentzGroup_mem_span_fieldStrengthDeriv_pair Λ⁻¹ hx,
      repLorentzGroup.self_inv_apply Λ x⟩

/-!

## C. Closure under the gauge group

-/

/-- **The gauge group fixes the span of the second derivatives of the field strength
  pointwise.** -/
lemma repJetGaugeGroupI_apply_of_mem_span_fieldStrengthDeriv_pair (U : JetGaugeGroupI)
    {x : JetAlgebra}
    (hx : x ∈ Submodule.span ℂ {y : JetAlgebra | ∃ ρ τ μ ν, y = fieldStrengthDeriv {ρ, τ} μ ν}) :
    repJetGaugeGroupI U x = x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨ρ, τ, μ, ν, rfl⟩ := hy
    exact repJetGaugeGroupI_fieldStrengthDeriv U {ρ, τ} μ ν
  | zero => rw [map_zero]
  | add u v _ _ hu hv => rw [map_add, hu, hv]
  | smul c u _ hu => rw [map_smul, hu]

/-- **The span of the second derivatives of the field strength is closed under the gauge
  action.** -/
lemma repJetGaugeGroupI_mem_span_fieldStrengthDeriv_pair (U : JetGaugeGroupI) {x : JetAlgebra}
    (hx : x ∈ Submodule.span ℂ {y : JetAlgebra | ∃ ρ τ μ ν, y = fieldStrengthDeriv {ρ, τ} μ ν}) :
    repJetGaugeGroupI U x ∈
      Submodule.span ℂ {y : JetAlgebra | ∃ ρ τ μ ν, y = fieldStrengthDeriv {ρ, τ} μ ν} := by
  rw [repJetGaugeGroupI_apply_of_mem_span_fieldStrengthDeriv_pair U hx]
  exact hx

/-- **The span of the second derivatives of the field strength is a subrepresentation of the
  gauge group.** -/
lemma map_repJetGaugeGroupI_span_fieldStrengthDeriv_pair (U : JetGaugeGroupI) :
    Submodule.map (repJetGaugeGroupI U)
        (Submodule.span ℂ {y : JetAlgebra | ∃ ρ τ μ ν, y = fieldStrengthDeriv {ρ, τ} μ ν}) =
      Submodule.span ℂ {y : JetAlgebra | ∃ ρ τ μ ν, y = fieldStrengthDeriv {ρ, τ} μ ν} := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro x ⟨u, hu, rfl⟩
    exact repJetGaugeGroupI_mem_span_fieldStrengthDeriv_pair U hu
  · exact ⟨x, hx, repJetGaugeGroupI_apply_of_mem_span_fieldStrengthDeriv_pair U hx⟩

end JetAlgebra

end LeptonGaugeSector

end
