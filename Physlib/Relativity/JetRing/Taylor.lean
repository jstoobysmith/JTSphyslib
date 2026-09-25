/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Relativity.JetRing.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
/-!
# Taylor determinacy and completeness of jets

## i. Overview

A jet is determined by the base-point values of its iterated derivatives, and a jet all of
whose first derivatives vanish is the constant jet of its value. These are the two facts
that make the jets of a matrix gauge group a faithful package of local gauge data, in the
sense of `LocalGaugeData.Faithful`. Conversely every family of base-point Taylor data is
realized by a jet, `taylorSeries`, and entrywise by a matrix of jets, `taylorMatrix`: this
is the Taylor completeness half of `LocalGaugeData.Free`.

## ii. Key results

- `JetRing.ext_of_constantCoeff_foldl_pderiv` : Taylor determinacy.
- `JetRing.eq_C_of_pderiv_eq_zero` : a jet with vanishing derivatives is constant.
- `JetRing.taylorSeries`, `JetRing.constantCoeff_foldl_pderiv_taylorSeries` : Taylor
  completeness.
- `JetRing.taylorMatrix` : Taylor completeness for matrices of jets.

## iii. Table of contents

- A. Taylor determinacy
- B. Taylor completeness

-/

@[expose] public section

namespace JetRing

open MvPowerSeries

/-!

## A. Taylor determinacy

-/

/-- **Taylor determinacy**: two jets with the same base-point values of all iterated
  derivatives are equal. -/
lemma ext_of_constantCoeff_foldl_pderiv {f g : JetRing}
    (h : ∀ s : Multiset (Fin 1 ⊕ Fin 3),
      constantCoeff (s.foldl (fun h ρ => pderiv ρ h) f)
        = constantCoeff (s.foldl (fun h ρ => pderiv ρ h) g)) : f = g := by
  ext m
  obtain ⟨s, rfl⟩ : ∃ s : Multiset (Fin 1 ⊕ Fin 3), s.toFinsupp = m :=
    ⟨Multiset.toFinsupp.symm m, Multiset.toFinsupp.apply_symm_apply m⟩
  have hs := h s
  rw [constantCoeff_foldl_pderiv, constantCoeff_foldl_pderiv] at hs
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr
    (Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.factorial_ne_zero _)) hs

/-- A jet all of whose first derivatives vanish is the constant jet of its value. -/
lemma eq_C_of_pderiv_eq_zero {f : JetRing} (hf : ∀ μ, pderiv μ f = 0) :
    f = C (constantCoeff f) :=
  pderiv.ext (fun i => by rw [hf i, pderiv_C]) (by rw [constantCoeff_C])

/-!

## B. Taylor completeness

-/

/-- The power series with prescribed base-point Taylor data `f`: the coefficient at the
  monomial `m` is `f` at the multiset of `m`, divided by the factorials of `m`. -/
noncomputable def taylorSeries (f : Multiset (Fin 1 ⊕ Fin 3) → ℂ) : JetRing :=
  fun m => ((∏ ν, Nat.factorial (m ν) : ℕ) : ℂ)⁻¹ * f (Finsupp.toMultiset m)

lemma coeff_taylorSeries (f : Multiset (Fin 1 ⊕ Fin 3) → ℂ) (m : (Fin 1 ⊕ Fin 3) →₀ ℕ) :
    coeff m (taylorSeries f) = ((∏ ν, Nat.factorial (m ν) : ℕ) : ℂ)⁻¹ * f (Finsupp.toMultiset m) :=
  rfl

lemma star_taylorSeries (f : Multiset (Fin 1 ⊕ Fin 3) → ℂ) :
    star (taylorSeries f) = taylorSeries fun s => star (f s) := by
  ext m
  rw [coeff_star, coeff_taylorSeries, coeff_taylorSeries, star_mul', star_inv₀,
    star_natCast]

lemma taylorSeries_sum {ι : Type} (t : Finset ι) (f : ι → Multiset (Fin 1 ⊕ Fin 3) → ℂ) :
    taylorSeries (fun s => ∑ i ∈ t, f i s) = ∑ i ∈ t, taylorSeries (f i) := by
  ext m
  simp only [coeff_taylorSeries, map_sum, Finset.mul_sum]

/-- The base-point Taylor data of `taylorSeries f` are `f`. -/
lemma constantCoeff_foldl_pderiv_taylorSeries (f : Multiset (Fin 1 ⊕ Fin 3) → ℂ)
    (s : Multiset (Fin 1 ⊕ Fin 3)) :
    constantCoeff (s.foldl (fun h ρ => pderiv ρ h) (taylorSeries f)) = f s := by
  have hfac : ((∏ ν, Nat.factorial (s.count ν) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun ν _ => Nat.factorial_ne_zero _)
  rw [constantCoeff_foldl_pderiv, coeff_taylorSeries, Multiset.toFinsupp_toMultiset,
    show (∏ ν, Nat.factorial (s.toFinsupp ν)) = ∏ ν, Nat.factorial (s.count ν) from
      Finset.prod_congr rfl fun ν _ => by rw [Multiset.toFinsupp_apply],
    ← mul_assoc, mul_inv_cancel₀ hfac, one_mul]

/-- The matrix of jets with prescribed base-point Taylor data `M`, entrywise. -/
noncomputable def taylorMatrix {κ : Type} (M : Multiset (Fin 1 ⊕ Fin 3) → Matrix κ κ ℂ) :
    Matrix κ κ JetRing :=
  Matrix.of fun i j => taylorSeries fun s => M s i j

lemma taylorMatrix_apply {κ : Type} (M : Multiset (Fin 1 ⊕ Fin 3) → Matrix κ κ ℂ) (i j : κ) :
    taylorMatrix M i j = taylorSeries fun s => M s i j :=
  rfl

lemma star_taylorMatrix {κ : Type} {M : Multiset (Fin 1 ⊕ Fin 3) → Matrix κ κ ℂ}
    (hM : ∀ s, star (M s) = M s) : star (taylorMatrix M) = taylorMatrix M := by
  ext i j : 1
  rw [Matrix.star_apply, taylorMatrix_apply, taylorMatrix_apply, star_taylorSeries]
  exact congrArg taylorSeries (funext fun s => by rw [← Matrix.star_apply, hM s])

lemma trace_taylorMatrix {κ : Type} [Fintype κ] {M : Multiset (Fin 1 ⊕ Fin 3) → Matrix κ κ ℂ}
    (hM : ∀ s, (M s).trace = 0) : (taylorMatrix M).trace = 0 := by
  have h : ∀ s, ∑ i, M s i i = 0 := fun s => hM s
  simp only [Matrix.trace, Matrix.diag_apply, taylorMatrix_apply, ← taylorSeries_sum, h]
  ext m
  simp [coeff_taylorSeries]

/-- The base-point Taylor data of `taylorMatrix M` are `M`, entrywise. -/
lemma map_constantCoeff_foldl_pderiv_taylorMatrix {κ : Type}
    (M : Multiset (Fin 1 ⊕ Fin 3) → Matrix κ κ ℂ) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    (taylorMatrix M).map (fun f => constantCoeff (s.foldl (fun h ρ => pderiv ρ h) f)) = M s := by
  ext i j
  rw [Matrix.map_apply, taylorMatrix_apply, constantCoeff_foldl_pderiv_taylorSeries]

end JetRing
