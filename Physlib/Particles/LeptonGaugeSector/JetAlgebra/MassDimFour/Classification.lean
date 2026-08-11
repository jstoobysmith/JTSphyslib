/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.MassDimFour.Basic
public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.MassDimFour.LinearIndependence
public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.FermionicKineticTerm.BoostWeight
public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.FermionicKineticTerm.Closure
public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.FermionicBarKineticTerm.BoostWeight
public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.FermionicBarKineticTerm.Closure
public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.GaugeKineticTerm.Invariance
public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.GaugeKineticTerm.Closure
public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.GaugeDoubleDeriv.Invariance
/-!
# The renormalizable Lagrangian densities of the lepton–gauge sector

## i. Overview

**An invariant of mass dimension four is a combination of the two fermion kinetic terms, the
Maxwell term and the theta term** — `mem_span_renormalizableTerms_of_isInvariant`. This is the
classification theorem for the lepton–gauge sector, and it is the last step: everything it uses
is proved elsewhere.

## ii. The argument

`mem_massDimFour_neutral_sectors_of_isInvariant` puts an invariant of mass weight eight in the
join of four sector spans, and each sector has already been cut down to its invariants:

| sector | invariants | proved in |
|---|---|---|
| `D̄_μ ψ̄_α ψ_β` | `fermionKineticTermBar` | `FermionicBarKineticTerm.BoostWeight` |
| `ψ̄_α D_μ ψ_β` | `fermionKineticTerm` | `FermionicKineticTerm.BoostWeight` |
| `∂_ρ ∂_τ F_{μν}` | none | `GaugeDoubleDeriv.Invariance` |
| `F_{μν} F_{μ'ν'}` | `maxwellTerm`, `thetaTerm` | `GaugeKineticTerm.Invariance` |

Those four results are about a single sector at a time, so they apply to the four summands of
`x = a + b + c + d` only once each summand is known to be invariant, which is what section A
establishes. Two ingredients go into it. Each sector is carried to itself by the Lorentz action
and fixed pointwise by the gauge action (the `Closure` files), so `ρ(Λ) a - a` lies in the first
sector again and the four such differences sum to `ρ(Λ) x - x = 0`. And the four sectors are
independent (`MassDimFour.LinearIndependence`), so those four differences are individually zero.

## iii. Key results

- `JetAlgebra.isInvariant_of_massDimFour_decomp` : the sector components of an invariant are
  themselves invariant.
- `JetAlgebra.mem_span_renormalizableTerms_of_isInvariant` : **the classification** — an
  invariant of mass weight eight lies in
  `span ℂ {fermionKineticTerm, fermionKineticTermBar, maxwellTerm, thetaTerm}`.

## iv. Table of contents

- A. The sector components of an invariant are invariant
- B. The classification

-/

@[expose] public section

namespace LeptonGaugeSector
open TensorProduct StandardModel

namespace JetAlgebra

open Matrix MatrixGroups

/-!

## A. The sector components of an invariant are invariant

The gauge half is immediate: each sector is fixed pointwise by the gauge action, so every
element of it — the components included — is gauge invariant. The Lorentz half is where the
independence of the sectors is spent: `ρ(Λ) a - a` lies in the first sector again, and likewise
for the other three, and the four differences sum to `ρ(Λ) x - x = 0`.

-/

/-- **The sector components of an invariant are themselves invariant.** -/
lemma isInvariant_of_massDimFour_decomp {x a b c d : JetAlgebra} (hx : IsInvariant x)
    (ha : a ∈ Submodule.span ℂ {y : JetAlgebra | ∃ α μ β, y = Dbarψ [μ] α * Dψ [] β})
    (hb : b ∈ Submodule.span ℂ {y : JetAlgebra | ∃ α μ β, y = Dbarψ [] α * Dψ [μ] β})
    (hc : c ∈ Submodule.span ℂ {y : JetAlgebra | ∃ ρ τ μ ν, y = fieldStrengthDeriv {ρ, τ} μ ν})
    (hd : d ∈ Submodule.span ℂ {y : JetAlgebra | ∃ μ ν μ' ν',
      y = fieldStrengthDeriv {} μ ν * fieldStrengthDeriv {} μ' ν'})
    (hsum : a + b + c + d = x) :
    IsInvariant a ∧ IsInvariant b ∧ IsInvariant c ∧ IsInvariant d := by
  have hlor : ∀ Λ : SL(2,ℂ), repLorentzGroup Λ a = a ∧ repLorentzGroup Λ b = b ∧
      repLorentzGroup Λ c = c ∧ repLorentzGroup Λ d = d := by
    intro Λ
    have hzero : (repLorentzGroup Λ a - a) + (repLorentzGroup Λ b - b) +
        (repLorentzGroup Λ c - c) + (repLorentzGroup Λ d - d) = 0 := by
      have h1 : repLorentzGroup Λ a + repLorentzGroup Λ b + repLorentzGroup Λ c +
          repLorentzGroup Λ d = x := by
        rw [← map_add, ← map_add, ← map_add, hsum, hx.2 Λ]
      rw [show (repLorentzGroup Λ a - a) + (repLorentzGroup Λ b - b) +
          (repLorentzGroup Λ c - c) + (repLorentzGroup Λ d - d) =
          (repLorentzGroup Λ a + repLorentzGroup Λ b + repLorentzGroup Λ c +
            repLorentzGroup Λ d) - (a + b + c + d) from by abel,
        h1, hsum, sub_self]
    obtain ⟨e1, e2, e3, e4⟩ := eq_zero_of_massDimFour_sum_eq_zero
      (sub_mem (repLorentzGroup_mem_span_Dbarψ_singleton_mul_Dψ_nil Λ ha) ha)
      (sub_mem (repLorentzGroup_mem_span_Dbarψ_mul_Dψ Λ hb) hb)
      (sub_mem (repLorentzGroup_mem_span_fieldStrengthDeriv_pair Λ hc) hc)
      (sub_mem (repLorentzGroup_mem_span_fieldStrength_mul Λ hd) hd) hzero
    exact ⟨sub_eq_zero.mp e1, sub_eq_zero.mp e2, sub_eq_zero.mp e3, sub_eq_zero.mp e4⟩
  exact ⟨⟨fun U => repJetGaugeGroupI_apply_of_mem_span_Dbarψ_singleton_mul_Dψ_nil U ha,
      fun Λ => (hlor Λ).1⟩,
    ⟨fun U => repJetGaugeGroupI_apply_of_mem_span_Dbarψ_mul_Dψ U hb, fun Λ => (hlor Λ).2.1⟩,
    ⟨fun U => repJetGaugeGroupI_apply_of_mem_span_fieldStrengthDeriv_pair U hc,
      fun Λ => (hlor Λ).2.2.1⟩,
    ⟨fun U => repJetGaugeGroupI_apply_of_mem_span_fieldStrength_mul U hd,
      fun Λ => (hlor Λ).2.2.2⟩⟩

/-!

## B. The classification

-/

/-- **The renormalizable Lagrangian densities of the lepton–gauge sector.** An invariant of mass
  weight eight — mass dimension four — is a linear combination of the fermion kinetic term, the
  conjugate fermion kinetic term, the Maxwell term and the theta term.

  Every ingredient is proved elsewhere: `mem_massDimFour_neutral_sectors_of_isInvariant` for the
  decomposition into sectors, `MassDimFour.LinearIndependence` and the four `Closure` files for
  the invariance of the components, and the four sector theorems for what each sector
  contributes. The second derivatives of the field strength contribute nothing. -/
theorem mem_span_renormalizableTerms_of_isInvariant {x : JetAlgebra} (hx : IsInvariant x)
    (h8 : x ∈ massWeightSubmodule 8) :
    x ∈ Submodule.span ℂ
      {fermionKineticTerm, fermionKineticTermBar, maxwellTerm, thetaTerm} := by
  obtain ⟨u, hu, d, hd, rfl⟩ := Submodule.mem_sup.mp
    (mem_massDimFour_neutral_sectors_of_isInvariant hx h8)
  obtain ⟨v, hv, c, hc, rfl⟩ := Submodule.mem_sup.mp hu
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨hai, hbi, hci, hdi⟩ := isInvariant_of_massDimFour_decomp hx ha hb hc hd rfl
  have hmono : ∀ S : Set JetAlgebra,
      S ⊆ {fermionKineticTerm, fermionKineticTermBar, maxwellTerm, thetaTerm} →
      Submodule.span ℂ S ≤ Submodule.span ℂ
        {fermionKineticTerm, fermionKineticTermBar, maxwellTerm, thetaTerm} :=
    fun _ hS => Submodule.span_mono hS
  refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_
  · exact hmono _ (by simp) (mem_fermionic_bar_kinetic_span_eq_kineticTermBar_of_isInvariant
      hai ha)
  · exact hmono _ (by simp) (mem_fermionic_kinetic_span_eq_kineticTerm_of_isInvariant hbi hb)
  · rw [eq_zero_of_isInvariant_of_mem_span_fieldStrengthDeriv_pair hci hc]
    exact zero_mem _
  · refine hmono _ (fun y hy => ?_)
      (mem_gauge_kinetic_span_eq_maxwell_theta_of_isInvariant hdi hd)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
    tauto

end JetAlgebra

end LeptonGaugeSector

end
