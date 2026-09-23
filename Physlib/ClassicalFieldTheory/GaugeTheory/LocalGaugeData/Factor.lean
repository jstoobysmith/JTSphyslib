/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.Basic
/-!
# The factors of a gauge group

## i. Overview

A gauge group is presented, as in a model-building table, by its factors: `U(1)` factors
and `SU(n)` factors. This file says what a factor of a local gauge data package is, without
reference to matter:

* `LocalGaugeData.U1Factor` : a unitary jet `u U` attached to each gauge jet, with the
  matching components `φ`, `φJ` of the gauge algebra and its jets, related by the
  Maurer–Cartan form `φJ (ω_μ U) = i (∂_μ u) u⁻¹` and invariant under the adjoint action;
* `LocalGaugeData.SUFactor` : a unitary matrix of jets `u U` attached to each gauge jet,
  with the matching matrix components `φ`, `φJ`, related by the Maurer–Cartan form
  `φJ (ω_μ U) = i (∂_μ u) u⁻¹` and transforming by conjugation under the adjoint action;
* `LocalGaugeData.Factor`, `Factors` : a factor of either kind, and a gauge group as a
  list of factors.

The canonical factors of the concrete packages are `LocalGaugeData.u1Factor` and
`LocalGaugeData.suFactor`, the lifts of factors along a product are in
`Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.Prod`, and the representations
a factor names (the charge twist, the fundamental) are built in
`Physlib.ClassicalFieldTheory.GaugeTheory.MatterField.MatrixRep.Factors`.

## ii. Key results

- `LocalGaugeData.U1Factor` : a `U(1)` factor of the local gauge data.
- `LocalGaugeData.SUFactor` : an `SU(n)` factor of the local gauge data.
- `LocalGaugeData.Factor`, `LocalGaugeData.Factors` : a gauge group presented by its factors.

## iii. Table of contents

- A. `U(1)` factors
- B. `SU(n)` factors
- C. A gauge group as a list of factors

-/

@[expose] public section

open MvPowerSeries

namespace LocalGaugeData

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]

/-!

## A. `U(1)` factors

-/

/-- **A `U(1)` factor** of the local gauge data: a unitary jet `u U` attached to each gauge
  jet, with the corresponding components `φ c` of the gauge algebra and `φJ a` of its jets,
  related by the Maurer–Cartan form `φJ (ω_μ U) = i (∂_μ u) u⁻¹` and invariant under the
  adjoint action. -/
structure U1Factor (jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J) where
  /-- The unitary jet of a gauge jet. -/
  u : GJ →* unitary JetRing
  /-- The `u(1)` component of a gauge algebra element. -/
  φ : 𝔤 →ₗ[ℝ] ℂ
  /-- The `u(1)` component of a jet of gauge algebra elements. -/
  φJ : 𝔤J → JetRing
  φJ_ofConstantLie : ∀ c, φJ (jets.ofConstantLie c) = C (φ c)
  φJ_cc_foldl : ∀ (p : Multiset (Fin 1 ⊕ Fin 3)) (a : 𝔤J),
    constantCoeff (p.foldl (fun h ρ => pderiv ρ h) (φJ a))
      = φ (jets.evalLie (jets.iteratedDeriv p a))
  φJ_maurerCartan : ∀ (U : GJ) (μ : Fin 1 ⊕ Fin 3),
    φJ (jets.maurerCartan U μ)
      = Complex.I • (pderiv μ (u U : JetRing) * star (u U : JetRing))
  φJ_adjoint : ∀ (U : GJ) (c : 𝔤),
    φJ (jets.adjoint U (jets.ofConstantLie c)) = φJ (jets.ofConstantLie c)

/-!

## B. `SU(n)` factors

-/

/-- **An `SU(n)` factor** of the local gauge data: a unitary matrix of jets `u U` attached
  to each gauge jet, with the corresponding matrix components `φ c` of the gauge algebra
  and `φJ a` of its jets, related by the Maurer–Cartan form `φJ (ω_μ U) = i (∂_μ u) u⁻¹`
  and transforming by conjugation under the adjoint action. -/
structure SUFactor (jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J) (n : Type) [Fintype n] [DecidableEq n]
    where
  /-- The unitary matrix of jets of a gauge jet. -/
  u : GJ → Matrix n n JetRing
  u_one : u 1 = 1
  u_mul : ∀ U V, u (U * V) = u U * u V
  u_unitary : ∀ U, star (u U) * u U = 1
  /-- The matrix component of a gauge algebra element. -/
  φ : 𝔤 →ₗ[ℝ] Matrix n n ℂ
  /-- The matrix component of a jet of gauge algebra elements. -/
  φJ : 𝔤J → Matrix n n JetRing
  φJ_ofConstantLie : ∀ c, φJ (jets.ofConstantLie c) = (φ c).map (C : ℂ → JetRing)
  φJ_cc_foldl : ∀ (p : Multiset (Fin 1 ⊕ Fin 3)) (a : 𝔤J),
    ((φJ a).map fun f => constantCoeff (p.foldl (fun h ρ => pderiv ρ h) f))
      = φ (jets.evalLie (jets.iteratedDeriv p a))
  φJ_maurerCartan : ∀ (U : GJ) (μ : Fin 1 ⊕ Fin 3),
    φJ (jets.maurerCartan U μ)
      = Complex.I • (((u U).map fun f => pderiv μ f) * star (u U))
  φJ_adjoint : ∀ (U : GJ) (c : 𝔤),
    φJ (jets.adjoint U (jets.ofConstantLie c)) = u U * φJ (jets.ofConstantLie c) * star (u U)

/-!

## C. A gauge group as a list of factors

-/

/-- **A factor of the gauge group**, presented in the local gauge data: a `U(1)` factor or
  an `SU(n)` factor. -/
inductive Factor (jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J)
  /-- A `U(1)` factor. -/
  | U1 (F : U1Factor jets)
  /-- An `SU(n)` factor. -/
  | SU {n : ℕ} (F : SUFactor jets (Fin n))

/-- **A gauge group presented by its factors.** -/
abbrev Factors (jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J) : Type := List (Factor jets)

end LocalGaugeData
