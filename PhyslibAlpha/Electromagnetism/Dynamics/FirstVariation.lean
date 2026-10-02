/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Electromagnetism.Dynamics.Lagrangian

/-!

# The first variation of the electromagnetic lagrangian

For a potential `A` which is differentiable, but not necessarily smooth, and a variation `δA`,
the lagrangian density along `A + s • δA` is a quadratic polynomial in `s`. Its derivative at
`s = 0` is the first variation of the lagrangian density,
`-(1/μ₀) Σ (η_μμ η_νν ∂_μ A_ν ∂_μ δA_ν - ∂_μ A_ν ∂_ν δA_μ) - ⟪δA, J⟫`.
This is the integrand of the first variation of the action which defines `IsWeakExtrema`.

## Main results

- `deriv_add_smul_apply` : the coordinate derivatives of a variation of a potential.
- `lagrangian_add_smul_eq` : the lagrangian along a variation as a polynomial in `s`.
- `deriv_lagrangian_add_smul` : the first variation of the lagrangian density.

## Contents

- A. Derivatives of a variation
- B. The lagrangian along a variation
- C. The first variation

-/

@[expose] public section

namespace Electromagnetism
namespace ElectromagneticPotential
open SpaceTime minkowskiMatrix Lorentz.Vector

/-!

## A. Derivatives of a variation

-/

/-- The coordinate derivatives of a variation `A + s • δA` of a potential. -/
lemma deriv_add_smul_apply {d} (A : ElectromagneticPotential d)
    (δA : SpaceTime d → Lorentz.Vector d) (hA : Differentiable ℝ A) (hδA : Differentiable ℝ δA)
    (s : ℝ) (μ ν : Fin 1 ⊕ Fin d) (x : SpaceTime d) :
    ∂_ μ (fun x' => A x' + s • δA x') x ν = ∂_ μ A x ν + s * ∂_ μ δA x ν := by
  rw [SpaceTime.deriv_eq, SpaceTime.deriv_eq, SpaceTime.deriv_eq,
    fderiv_fun_add (hA x) (by fun_prop), fderiv_fun_const_smul (hδA x)]
  simp

/-!

## B. The lagrangian along a variation

-/

/-- The lagrangian along a variation `A + s • δA` is a quadratic polynomial in `s`. -/
lemma lagrangian_add_smul_eq {d} {𝓕 : FreeSpace} (A : ElectromagneticPotential d)
    (J : LorentzCurrentDensity d) (δA : SpaceTime d → Lorentz.Vector d)
    (hA : Differentiable ℝ A) (hδA : Differentiable ℝ δA) (x : SpaceTime d) (s : ℝ) :
    lagrangian 𝓕 ⟨fun x' => A x' + s • δA x'⟩ J x =
      - 1 / (2 * 𝓕.μ₀) * (∑ μ, ∑ ν, (η μ μ * η ν ν * ∂_ μ A x ν ^ 2 - ∂_ μ A x ν * ∂_ ν A x μ)
        + s * ∑ μ, ∑ ν, (2 * η μ μ * η ν ν * ∂_ μ A x ν * ∂_ μ δA x ν
          - (∂_ μ A x ν * ∂_ ν δA x μ + ∂_ μ δA x ν * ∂_ ν A x μ))
        + s ^ 2 * ∑ μ, ∑ ν, (η μ μ * η ν ν * ∂_ μ δA x ν ^ 2 - ∂_ μ δA x ν * ∂_ ν δA x μ))
      - (⟪A x, J x⟫ₘ + s * ⟪δA x, J x⟫ₘ) := by
  rw [lagrangian, kineticTerm_eq_sum_potential, freeCurrentPotential]
  change - 1 / (2 * 𝓕.μ₀) * ∑ μ, ∑ ν, (η μ μ * η ν ν *
    (∂_ μ (fun x' => A x' + s • δA x') x ν) ^ 2 -
    ∂_ μ (fun x' => A x' + s • δA x') x ν * ∂_ ν (fun x' => A x' + s • δA x') x μ)
    - ⟪A x + s • δA x, J x⟫ₘ = _
  simp only [deriv_add_smul_apply A δA hA hδA s, map_add, map_smul, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul]
  congr 2
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  ring

/-!

## C. The first variation

-/

/-- The first variation of the lagrangian density. -/
lemma deriv_lagrangian_add_smul {d} {𝓕 : FreeSpace} (A : ElectromagneticPotential d)
    (J : LorentzCurrentDensity d) (δA : SpaceTime d → Lorentz.Vector d)
    (hA : Differentiable ℝ A) (hδA : Differentiable ℝ δA) (x : SpaceTime d) :
    _root_.deriv (fun s : ℝ => lagrangian 𝓕 ⟨fun x' => A x' + s • δA x'⟩ J x) 0 =
      - 1 / 𝓕.μ₀ * ∑ μ, ∑ ν, (η μ μ * η ν ν * ∂_ μ A x ν * ∂_ μ δA x ν
        - ∂_ μ A x ν * ∂_ ν δA x μ) - ⟪δA x, J x⟫ₘ := by
  simp only [lagrangian_add_smul_eq A J δA hA hδA x]
  have hS1 : ∑ μ, ∑ ν, (2 * η μ μ * η ν ν * ∂_ μ A x ν * ∂_ μ δA x ν
      - (∂_ μ A x ν * ∂_ ν δA x μ + ∂_ μ δA x ν * ∂_ ν A x μ)) =
      2 * ∑ μ, ∑ ν, (η μ μ * η ν ν * ∂_ μ A x ν * ∂_ μ δA x ν - ∂_ μ A x ν * ∂_ ν δA x μ) := by
    have h1 : ∑ μ, ∑ ν, (2 * η μ μ * η ν ν * ∂_ μ A x ν * ∂_ μ δA x ν
        - (∂_ μ A x ν * ∂_ ν δA x μ + ∂_ μ δA x ν * ∂_ ν A x μ)) =
        ∑ μ, ∑ ν, (2 * (η μ μ * η ν ν * ∂_ μ A x ν * ∂_ μ δA x ν - ∂_ μ A x ν * ∂_ ν δA x μ)
          + (∂_ μ A x ν * ∂_ ν δA x μ - ∂_ μ δA x ν * ∂_ ν A x μ)) :=
      Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by ring
    have h2 : ∑ μ, ∑ ν, (∂_ μ A x ν * ∂_ ν δA x μ - ∂_ μ δA x ν * ∂_ ν A x μ) = 0 := by
      simp only [Finset.sum_sub_distrib]
      rw [Finset.sum_comm (f := fun μ ν => ∂_ μ δA x ν * ∂_ ν A x μ), sub_eq_zero]
      exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => mul_comm _ _
    rw [h1]
    simp only [Finset.sum_add_distrib, h2, add_zero, ← Finset.mul_sum]
  rw [hS1]
  generalize ∑ μ, ∑ ν, (η μ μ * η ν ν * ∂_ μ A x ν * ∂_ μ δA x ν - ∂_ μ A x ν * ∂_ ν δA x μ) = T
  generalize ∑ μ, ∑ ν, (η μ μ * η ν ν * ∂_ μ A x ν ^ 2 - ∂_ μ A x ν * ∂_ ν A x μ) = S0
  generalize ∑ μ, ∑ ν, (η μ μ * η ν ν * ∂_ μ δA x ν ^ 2 - ∂_ μ δA x ν * ∂_ ν δA x μ) = S2
  generalize ⟪A x, J x⟫ₘ = m0
  generalize ⟪δA x, J x⟫ₘ = m1
  have h : HasDerivAt (fun s : ℝ => - 1 / (2 * 𝓕.μ₀) * (S0 + s * (2 * T) + s ^ 2 * S2)
      - (m0 + s * m1))
      (- 1 / (2 * 𝓕.μ₀) * (0 + 1 * (2 * T) + (2 * 0 ^ 1) * S2) - (0 + 1 * m1)) 0 := by
    refine HasDerivAt.sub (HasDerivAt.const_mul _ ?_) ?_
    · exact ((hasDerivAt_const _ _).add ((hasDerivAt_id 0).mul_const (2 * T))).add
        ((hasDerivAt_pow 2 0).mul_const S2)
    · exact (hasDerivAt_const _ _).add ((hasDerivAt_id 0).mul_const m1)
  rw [h.deriv]
  field_simp
  ring

end ElectromagneticPotential
end Electromagnetism
