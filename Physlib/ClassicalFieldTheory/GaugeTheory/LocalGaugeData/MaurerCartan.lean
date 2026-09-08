/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.Basic
/-!
# The Maurer–Cartan form of a local gauge data package

## i. Overview

The Maurer–Cartan form `ω_μ(U) = i (∂_μ U) U⁻¹` of a package
`jets : LocalGaugeData G 𝔤 G₀ 𝔤J` is the field `jets.maurerCartan`, subject to the cocycle
law `maurerCartan_cocycle`, its value `maurerCartan_one` on the identity and
`maurerCartan_ofConstant` on constants, and the flatness (structural) equation
`maurerCartan_structure`. This file develops what follows from those laws alone, for any
package: nothing here mentions a particular gauge group.

The main construction is the *symmetrized* Maurer–Cartan form

  `ω̄_r(U) = (1 / |r|) ∑_{μ ∈ r} ∂_{r − {μ}} ω_μ(U)`,

the average over which direction of the multiset `r` is carried by the form itself rather
than by a derivative. Its point is `iteratedDeriv_maurerCartan_eq_symmetrized_add`: an
iterated
derivative `∂_s ω_μ(U)` is the symmetrized form at `μ ::ₘ s` plus an average of iterated
derivatives of *brackets* of Maurer–Cartan forms in strictly fewer directions — the
structural equation used to trade an antisymmetric part for lower-order data. Iterating
that gives `evalLie_iteratedDeriv_maurerCartan_eq_of_symmetrized_eq`: the base-point Taylor
data of `ω` is determined by the base-point symmetrized data.

## ii. Key results

- `LocalGaugeData.maurerCartan_inv` : `ω_μ(U⁻¹) = − Ad_{U⁻¹} ω_μ(U)`.
- `LocalGaugeData.symmetrizedMaurerCartanForm` : the symmetrized Maurer–Cartan form, with
  `symmetrizedMaurerCartanForm_singleton` and the recursion
  `symmetrizedMaurerCartanForm_cons`.
- `LocalGaugeData.iteratedDeriv_maurerCartan_eq_symmetrized_add` : the symmetrization
  defect is an average of brackets in fewer directions.
- `LocalGaugeData.evalLie_iteratedDeriv_maurerCartan_eq_of_symmetrized_eq` : the base-point
  symmetrized data determines the base-point Taylor data of `ω`.

## iii. Table of contents

- A. The Maurer–Cartan form on inverses
- B. The symmetrized Maurer–Cartan form
- C. Determination of the Maurer–Cartan form by its symmetrized coefficients

-/

@[expose] public section

namespace LocalGaugeData

variable {G : Type} [Group G] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {G₀ : Type} [Group G₀] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  (jets : LocalGaugeData G 𝔤 G₀ 𝔤J)

/-!

## A. The Maurer–Cartan form on inverses

-/

/-- **The Maurer–Cartan form of an inverse**: `ω_μ(U⁻¹) = − Ad_{U⁻¹} ω_μ(U)`, the cocycle
  law applied to `U⁻¹ U = 1`. -/
lemma maurerCartan_inv (U : G) (μ : Fin 1 ⊕ Fin 3) :
    jets.maurerCartan U⁻¹ μ = - jets.adjoint U⁻¹ (jets.maurerCartan U μ) := by
  have h := jets.maurerCartan_cocycle U⁻¹ U μ
  rw [inv_mul_cancel, jets.maurerCartan_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-!

## B. The symmetrized Maurer–Cartan form

-/

/-- **The symmetrized Maurer–Cartan form** `ω̄_r(U) = (1/|r|) ∑_{μ ∈ r} ∂_{r − {μ}} ω_μ(U)`:
  the average, over the directions of `r`, of the Maurer–Cartan form in one direction
  differentiated along the remaining ones. -/
noncomputable def symmetrizedMaurerCartanForm (U : G) (r : Multiset (Fin 1 ⊕ Fin 3)) : 𝔤J :=
  ((1/(r.card : ℝ) : ℝ) • (r.map fun μ =>
    (jets.iteratedDeriv (r - {μ}) (jets.maurerCartan U μ))).sum)

@[simp]
lemma symmetrizedMaurerCartanForm_apply_zero (U : G) :
    jets.symmetrizedMaurerCartanForm U 0 = 0 := by
  simp [symmetrizedMaurerCartanForm]

@[simp]
lemma symmetrizedMaurerCartanForm_one : jets.symmetrizedMaurerCartanForm 1 = 0 := by
  funext r
  simp [symmetrizedMaurerCartanForm, jets.maurerCartan_one]

@[simp]
lemma symmetrizedMaurerCartanForm_ofConstant (g : G₀) :
    jets.symmetrizedMaurerCartanForm (jets.ofConstant g) = 0 := by
  funext r
  simp [symmetrizedMaurerCartanForm, jets.maurerCartan_ofConstant]

@[simp]
lemma symmetrizedMaurerCartanForm_singleton (U : G) (μ : Fin 1 ⊕ Fin 3) :
    jets.symmetrizedMaurerCartanForm U {μ} = jets.maurerCartan U μ := by
  simp [symmetrizedMaurerCartanForm, iteratedDeriv_zero]

/-- The recursion for the symmetrized Maurer–Cartan form: peeling one direction off the
  multiset. -/
lemma symmetrizedMaurerCartanForm_cons (U : G) (μ : Fin 1 ⊕ Fin 3)
    (r : Multiset (Fin 1 ⊕ Fin 3)) : jets.symmetrizedMaurerCartanForm U (μ ::ₘ r) =
    (1/(r.card + 1 : ℝ) : ℝ) • (jets.iteratedDeriv r (jets.maurerCartan U μ))
    + ((r.card : ℝ)/(r.card + 1 : ℝ)) •
      jets.deriv μ (jets.symmetrizedMaurerCartanForm U r) := by
  by_cases hr : r = 0
  · subst hr
    simp
  · have hn : (r.card : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr fun h => hr (Multiset.card_eq_zero.mp h)
    have herase : ∀ ν ∈ r, (μ ::ₘ r).erase ν = μ ::ₘ r.erase ν := by
      intro ν hν
      rcases eq_or_ne ν μ with rfl | h
      · rw [Multiset.erase_cons_head, Multiset.cons_erase hν]
      · rw [Multiset.erase_cons_tail _ h.symm]
    rw [symmetrizedMaurerCartanForm, symmetrizedMaurerCartanForm, Multiset.map_cons,
      Multiset.sum_cons, Multiset.card_cons, Multiset.sub_singleton, Multiset.erase_cons_head,
      Multiset.map_congr rfl fun ν hν => by
        rw [Multiset.sub_singleton, herase ν hν, iteratedDeriv_cons, LinearMap.comp_apply,
          ← Multiset.sub_singleton],
      show (r.map fun ν =>
            jets.deriv μ (jets.iteratedDeriv (r - {ν}) (jets.maurerCartan U ν))) =
          (r.map fun ν =>
            jets.iteratedDeriv (r - {ν}) (jets.maurerCartan U ν)).map (jets.deriv μ) from
        (Multiset.map_map _ _ _).symm,
      ← map_multiset_sum, smul_add, map_smul, smul_smul,
      show ((r.card + 1 : ℕ) : ℝ) = (r.card : ℝ) + 1 by push_cast; ring,
      show (r.card : ℝ)/((r.card : ℝ) + 1) * (1/(r.card : ℝ)) = 1/((r.card : ℝ) + 1) by
        field_simp]

/-!

## C. Determination of the Maurer–Cartan form by its symmetrized coefficients

-/

/-- The symmetrization defect of the Maurer–Cartan form: an iterated derivative of
  `ω` is the corresponding symmetrized form plus an average of iterated derivatives
  of brackets of `ω` in strictly fewer directions. This is the structural equation
  `maurerCartan_structure` used to trade the antisymmetric part for lower-order data. -/
lemma iteratedDeriv_maurerCartan_eq_symmetrized_add (U : G)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) :
    jets.iteratedDeriv s (jets.maurerCartan U μ) =
      jets.symmetrizedMaurerCartanForm U (μ ::ₘ s) +
      (1/(s.card + 1 : ℝ)) • (s.map fun ν =>
        jets.iteratedDeriv (s.erase ν)
          ⁅jets.maurerCartan U μ, jets.maurerCartan U ν⁆).sum := by
  -- each bracket term is a difference of two iterated derivatives of `ω`
  have hswap : ∀ ν ∈ s,
      jets.iteratedDeriv (s.erase ν) ⁅jets.maurerCartan U μ, jets.maurerCartan U ν⁆ =
        jets.iteratedDeriv s (jets.maurerCartan U μ) -
          jets.iteratedDeriv (μ ::ₘ s.erase ν) (jets.maurerCartan U ν) := by
    intro ν hν
    have hb : ⁅jets.maurerCartan U μ, jets.maurerCartan U ν⁆ =
        jets.deriv ν (jets.maurerCartan U μ) - jets.deriv μ (jets.maurerCartan U ν) := by
      have h1 : jets.deriv μ (jets.maurerCartan U ν) - jets.deriv ν (jets.maurerCartan U μ) =
          -⁅jets.maurerCartan U μ, jets.maurerCartan U ν⁆ :=
        eq_neg_of_add_eq_zero_left (jets.maurerCartan_structure U μ ν)
      rw [← neg_sub, h1, neg_neg]
    rw [hb, map_sub]
    congr 1
    · conv_rhs => rw [← Multiset.cons_erase hν]
      rw [show (ν ::ₘ s.erase ν : Multiset (Fin 1 ⊕ Fin 3)) = s.erase ν + {ν} from by
          rw [add_comm, Multiset.singleton_add],
        iteratedDeriv_add, LinearMap.comp_apply, iteratedDeriv_singleton]
    · rw [show (μ ::ₘ s.erase ν : Multiset (Fin 1 ⊕ Fin 3)) = s.erase ν + {μ} from by
          rw [add_comm, Multiset.singleton_add],
        iteratedDeriv_add, LinearMap.comp_apply, iteratedDeriv_singleton]
  have herase : ∀ ν ∈ s, (μ ::ₘ s).erase ν = μ ::ₘ s.erase ν := by
    intro ν hν
    rcases eq_or_ne ν μ with rfl | hne
    · rw [Multiset.erase_cons_head, Multiset.cons_erase hν]
    · rw [Multiset.erase_cons_tail _ hne.symm]
  rw [symmetrizedMaurerCartanForm, Multiset.map_cons, Multiset.sum_cons,
    Multiset.card_cons, Multiset.sub_singleton, Multiset.erase_cons_head,
    Multiset.map_congr rfl fun ν hν => by rw [Multiset.sub_singleton, herase ν hν],
    Multiset.map_congr rfl hswap, Multiset.sum_map_sub, Multiset.map_const',
    Multiset.sum_replicate, ← Nat.cast_smul_eq_nsmul ℝ]
  push_cast
  match_scalars <;> field_simp <;> ring

/-- **Determination step**: if the base-point symmetrized Maurer–Cartan data of `U` and
  `V` agree, and their Maurer–Cartan Taylor data agree in fewer than `n` directions,
  then they agree in `n` directions. -/
lemma evalLie_iteratedDeriv_maurerCartan_eq_of_symmetrized_eq (U V : G) (n : ℕ)
    (hsym : ∀ r, jets.evalLie (jets.symmetrizedMaurerCartanForm U r) =
      jets.evalLie (jets.symmetrizedMaurerCartanForm V r))
    (ih : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3), s.card < n →
      jets.evalLie (jets.iteratedDeriv s (jets.maurerCartan U μ)) =
        jets.evalLie (jets.iteratedDeriv s (jets.maurerCartan V μ)))
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (hs : s.card = n) :
    jets.evalLie (jets.iteratedDeriv s (jets.maurerCartan U μ)) =
      jets.evalLie (jets.iteratedDeriv s (jets.maurerCartan V μ)) := by
  rw [iteratedDeriv_maurerCartan_eq_symmetrized_add jets U s μ,
    iteratedDeriv_maurerCartan_eq_symmetrized_add jets V s μ,
    map_add, map_add, map_smul, map_smul, hsym]
  refine congrArg (fun z => jets.evalLie (jets.symmetrizedMaurerCartanForm V (μ ::ₘ s)) +
    (1/(s.card + 1 : ℝ)) • z) ?_
  rw [map_multiset_sum, map_multiset_sum, Multiset.map_map, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun ν hν => ?_)
  have hlt : ∀ p : Multiset (Fin 1 ⊕ Fin 3), p ≤ s.erase ν → p.card < n := by
    intro p hp
    have h1 := Multiset.card_le_card hp
    have h2 := Multiset.card_erase_add_one hν
    omega
  exact jets.evalLie_iteratedDeriv_bracket_congr (s.erase ν) _ _ _ _
    (fun p hp => ih p μ (hlt p hp)) (fun p hp => ih p ν (hlt p hp))

end LocalGaugeData
