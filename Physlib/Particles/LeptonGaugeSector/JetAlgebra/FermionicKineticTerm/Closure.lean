/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.Terms.KineticTerms
/-!
# The fermion kinetic bilinears span a subrepresentation

The span of the sixteen bilinears `ψ̄_α D_μ ψ_β` is carried to itself by both group actions on
the jet algebra. Statements proved for the span — that its boost-weight-zero part is the fermion
kinetic term, say — may therefore be combined with any operator built from the group elements,
an average or a projector among them, without leaving the span.

*Both closures are covariance of the covariant derivative.* Under the Lorentz group `ψ̄_α` mixes
only with the `ψ̄_γ`, and `D_μ ψ_β` only with the `D_ν ψ_δ` — the `- 6 i B_μ ψ_β` tail of the
covariant derivative transforms along with the derivative, which is the content of
`repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton` — so a bilinear goes to a combination of bilinears.
Under the gauge group each bilinear is not merely carried into the span but fixed: the
hypercharge characters of the lepton and of its conjugate cancel by unitarity
(`repJetGaugeGroupI_Dbarψ_mul_Dψ`), so the span is fixed pointwise.

## Key results

- `JetAlgebra.repLorentzGroup_mem_span_Dbarψ_mul_Dψ` : the span is closed under the Lorentz
  action, and `map_repLorentzGroup_span_Dbarψ_mul_Dψ` states this as an equality of submodules.
- `JetAlgebra.repJetGaugeGroupI_apply_of_mem_span_Dbarψ_mul_Dψ` : the gauge group fixes the span
  pointwise, whence `map_repJetGaugeGroupI_span_Dbarψ_mul_Dψ`.

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

/-- A fermion kinetic bilinear lies in their span. -/
lemma Dbarψ_mul_Dψ_mem_span (α : Fin 2) (μ : Fin 1 ⊕ Fin 3) (β : Fin 2) :
    Dbarψ [] α * Dψ [μ] β ∈
      Submodule.span ℂ {y : JetAlgebra | ∃ α μ β, y = Dbarψ [] α * Dψ [μ] β} :=
  Submodule.subset_span ⟨α, μ, β, rfl⟩

/-- The Lorentz action carries a fermion kinetic bilinear into the span of the bilinears: the
  spinor indices are rotated among themselves and the derivative index along with them. -/
lemma repLorentzGroup_Dbarψ_mul_Dψ_mem_span (Λ : SL(2,ℂ)) (α : Fin 2) (μ : Fin 1 ⊕ Fin 3)
    (β : Fin 2) :
    repLorentzGroup Λ (Dbarψ [] α * Dψ [μ] β) ∈
      Submodule.span ℂ {y : JetAlgebra | ∃ α μ β, y = Dbarψ [] α * Dψ [μ] β} := by
  rw [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton]
  exact Submodule.sum_mem _ fun γ _ => Submodule.sum_mem _ fun ν _ =>
    Submodule.sum_mem _ fun δ _ => Submodule.smul_mem _ _ (Dbarψ_mul_Dψ_mem_span γ ν δ)

/-!

## B. Closure under the Lorentz group

-/

/-- **The span of the fermion kinetic bilinears is closed under the Lorentz action.** -/
lemma repLorentzGroup_mem_span_Dbarψ_mul_Dψ (Λ : SL(2,ℂ)) {x : JetAlgebra}
    (hx : x ∈ Submodule.span ℂ {y : JetAlgebra | ∃ α μ β, y = Dbarψ [] α * Dψ [μ] β}) :
    repLorentzGroup Λ x ∈
      Submodule.span ℂ {y : JetAlgebra | ∃ α μ β, y = Dbarψ [] α * Dψ [μ] β} := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨α, μ, β, rfl⟩ := hy
    exact repLorentzGroup_Dbarψ_mul_Dψ_mem_span Λ α μ β
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u v _ _ hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv
  | smul c u _ hu => rw [map_smul]; exact Submodule.smul_mem _ _ hu

/-- **The span of the fermion kinetic bilinears is a subrepresentation of the Lorentz group.**
  Closure under every element and its inverse upgrades `repLorentzGroup_mem_span_Dbarψ_mul_Dψ`
  to an equality. -/
lemma map_repLorentzGroup_span_Dbarψ_mul_Dψ (Λ : SL(2,ℂ)) :
    Submodule.map (repLorentzGroup Λ)
        (Submodule.span ℂ {y : JetAlgebra | ∃ α μ β, y = Dbarψ [] α * Dψ [μ] β}) =
      Submodule.span ℂ {y : JetAlgebra | ∃ α μ β, y = Dbarψ [] α * Dψ [μ] β} := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro x ⟨u, hu, rfl⟩
    exact repLorentzGroup_mem_span_Dbarψ_mul_Dψ Λ hu
  · exact ⟨repLorentzGroup Λ⁻¹ x, repLorentzGroup_mem_span_Dbarψ_mul_Dψ Λ⁻¹ hx,
      repLorentzGroup.self_inv_apply Λ x⟩

/-!

## C. Closure under the gauge group

-/

/-- **The gauge group fixes the span of the fermion kinetic bilinears pointwise.** Each bilinear
  pairs the lepton with its conjugate, and their hypercharge characters cancel. -/
lemma repJetGaugeGroupI_apply_of_mem_span_Dbarψ_mul_Dψ (U : JetGaugeGroupI) {x : JetAlgebra}
    (hx : x ∈ Submodule.span ℂ {y : JetAlgebra | ∃ α μ β, y = Dbarψ [] α * Dψ [μ] β}) :
    repJetGaugeGroupI U x = x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨α, μ, β, rfl⟩ := hy
    exact repJetGaugeGroupI_Dbarψ_mul_Dψ U [] [μ] α β
  | zero => rw [map_zero]
  | add u v _ _ hu hv => rw [map_add, hu, hv]
  | smul c u _ hu => rw [map_smul, hu]

/-- **The span of the fermion kinetic bilinears is closed under the gauge action.** -/
lemma repJetGaugeGroupI_mem_span_Dbarψ_mul_Dψ (U : JetGaugeGroupI) {x : JetAlgebra}
    (hx : x ∈ Submodule.span ℂ {y : JetAlgebra | ∃ α μ β, y = Dbarψ [] α * Dψ [μ] β}) :
    repJetGaugeGroupI U x ∈
      Submodule.span ℂ {y : JetAlgebra | ∃ α μ β, y = Dbarψ [] α * Dψ [μ] β} := by
  rw [repJetGaugeGroupI_apply_of_mem_span_Dbarψ_mul_Dψ U hx]
  exact hx

/-- **The span of the fermion kinetic bilinears is a subrepresentation of the gauge group.** -/
lemma map_repJetGaugeGroupI_span_Dbarψ_mul_Dψ (U : JetGaugeGroupI) :
    Submodule.map (repJetGaugeGroupI U)
        (Submodule.span ℂ {y : JetAlgebra | ∃ α μ β, y = Dbarψ [] α * Dψ [μ] β}) =
      Submodule.span ℂ {y : JetAlgebra | ∃ α μ β, y = Dbarψ [] α * Dψ [μ] β} := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro x ⟨u, hu, rfl⟩
    exact repJetGaugeGroupI_mem_span_Dbarψ_mul_Dψ U hu
  · exact ⟨x, hx, repJetGaugeGroupI_apply_of_mem_span_Dbarψ_mul_Dψ U hx⟩

end JetAlgebra

end LeptonGaugeSector

end
