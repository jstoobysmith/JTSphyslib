/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.Grading.BoostWeight
public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.JetDerivLorentz
public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.GaugeDoubleDeriv.Closure
public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.GaugeDoubleDeriv.LinearIndependence
/-!
# The boost weight of the second derivatives of the field strength

The span of the monomials `∂_ρ ∂_τ F_{μν}` is analysed as the photon pairs are in
`GaugeKineticTerm.BoostWeight`, with one difference: there the two factors of a product carry
the weights and multiplication adds them, here the two derivatives carry the weights and the
light-cone derivative operators shift them.

*The derivatives are Lorentz vectors.* `JetDerivLorentz` proves
`ρ(Λ) (∂_μ x) = ∑ a, Λ_{aμ} • ∂_a (ρ(Λ) x)` on the bosonic part of the jet algebra, which is
where these monomials live. For the boost along an axis the four derivative directions
diagonalise exactly as the field-strength indices do: the light-cone combinations `∂_0 ∓ ∂_i`
shift the weight by `±2` and the two transverse derivatives leave it alone. Composing the
shifts with the weights of the field strengths themselves gives the weight of every
`∂_a ∂_b F_c` without a separate computation for each.

## Key results

- `JetAlgebra.lcp_mem_boostWeight`, `lcn_mem_boostWeight`, `jetDeriv_transverse_mem` : the
  light-cone derivatives shift the boost weight of their axis by `±2`, the transverse
  derivatives preserve it.
- `JetAlgebra.boostWeight_inter_fieldStrengthDeriv_pair_le` and its `_x`, `_y` partners : along
  each axis the boost weight zero part of the span of the monomials `∂_ρ ∂_τ F_{μν}` lies in
  the span of sixteen explicit second derivatives.
- `JetAlgebra.boostWeight_inter_fieldStrengthDeriv_pair_full` : the three axes together leave
  nothing — the intersection is `⊥`.

-/

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace LeptonGaugeSector
open TensorProduct StandardModel
open scoped minkowskiMatrix PauliMatrix Pointwise
open Matrix MatrixGroups

namespace JetAlgebra

private lemma algebraMap_real_complex (t : ℝ) :
    (algebraMap ℝ ℂ) t = ((t : ℝ) : ℂ) := rfl

/-!

## A. The light-cone derivatives shift the `z`-boost weight

-/

/-- **The light-cone derivative `∂_0 - ∂_z` raises the `z`-boost weight by two.** -/
lemma jetDeriv_lightConeZ_pos_mem {k : ℤ} {x : JetAlgebra} (hb : x ∈ bosonic)
    (hx : x ∈ boostWeightSubmodule 2 k) :
    jetDeriv (Sum.inl 0) x - jetDeriv (Sum.inr 2) x ∈ boostWeightSubmodule 2 (k + 2) := by
  intro t ht
  have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [map_sub, repLorentzGroup_jetDeriv_of_mem_bosonic _ _ hb,
    repLorentzGroup_jetDeriv_of_mem_bosonic _ _ hb, hx t ht]
  rw [algebraMap_real_complex, zpow_add₀ ht']
  simp only [boostAxis_two, toLorentzGroup_boostZel, boostMatZ, Fintype.sum_sum_type,
    Fin.sum_univ_one, Fin.sum_univ_three, map_smul, Complex.ofReal_zero, zero_smul,
    Complex.ofReal_one, one_smul, add_zero, zero_add, Complex.ofReal_div, Complex.ofReal_add,
    Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_neg,
    Complex.ofReal_ofNat]
  match_scalars <;> (field_simp; ring)

/-- **The light-cone derivative `∂_0 + ∂_z` lowers the `z`-boost weight by two.** -/
lemma jetDeriv_lightConeZ_neg_mem {k : ℤ} {x : JetAlgebra} (hb : x ∈ bosonic)
    (hx : x ∈ boostWeightSubmodule 2 k) :
    jetDeriv (Sum.inl 0) x + jetDeriv (Sum.inr 2) x ∈ boostWeightSubmodule 2 (k - 2) := by
  intro t ht
  have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [map_add, repLorentzGroup_jetDeriv_of_mem_bosonic _ _ hb,
    repLorentzGroup_jetDeriv_of_mem_bosonic _ _ hb, hx t ht]
  rw [algebraMap_real_complex, zpow_sub₀ ht']
  simp only [boostAxis_two, toLorentzGroup_boostZel, boostMatZ, Fintype.sum_sum_type,
    Fin.sum_univ_one, Fin.sum_univ_three, map_smul, Complex.ofReal_zero, zero_smul,
    Complex.ofReal_one, one_smul, add_zero, zero_add, Complex.ofReal_div, Complex.ofReal_add,
    Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_neg,
    Complex.ofReal_ofNat]
  match_scalars <;> (field_simp; ring)

/-- **A transverse derivative leaves the `z`-boost weight alone.** -/
lemma jetDeriv_transverseZ_mem {k : ℤ} {x : JetAlgebra} {i : Fin 3} (hi : i ≠ 2)
    (hb : x ∈ bosonic) (hx : x ∈ boostWeightSubmodule 2 k) :
    jetDeriv (Sum.inr i) x ∈ boostWeightSubmodule 2 k := by
  intro t ht
  have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_jetDeriv_of_mem_bosonic _ _ hb, hx t ht, algebraMap_real_complex]
  fin_cases i
  ·
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    simp only [boostAxis_two, toLorentzGroup_boostZel, boostMatZ, Fintype.sum_sum_type,
      Fin.sum_univ_one, Fin.sum_univ_three, map_smul, Complex.ofReal_zero, zero_smul,
      Complex.ofReal_one, one_smul, add_zero, zero_add]
  ·
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    simp only [boostAxis_two, toLorentzGroup_boostZel, boostMatZ, Fintype.sum_sum_type,
      Fin.sum_univ_one, Fin.sum_univ_three, map_smul, Complex.ofReal_zero, zero_smul,
      Complex.ofReal_one, one_smul, add_zero, zero_add]
  · exact absurd rfl hi

/-!

## B. The same shifts along the `x`- and `y`-axes

-/

/-- **The light-cone derivative `∂_0 - ∂_x` raises the `x`-boost weight by two.** -/
lemma jetDeriv_lightConeX_pos_mem {k : ℤ} {x : JetAlgebra} (hb : x ∈ bosonic)
    (hx : x ∈ boostWeightSubmodule 0 k) :
    jetDeriv (Sum.inl 0) x - jetDeriv (Sum.inr 0) x ∈ boostWeightSubmodule 0 (k + 2) := by
  intro t ht
  have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [map_sub, repLorentzGroup_jetDeriv_of_mem_bosonic _ _ hb,
    repLorentzGroup_jetDeriv_of_mem_bosonic _ _ hb, hx t ht]
  rw [algebraMap_real_complex, zpow_add₀ ht']
  simp only [boostAxis_zero, toLorentzGroup_boostXel, boostMatX, Fintype.sum_sum_type,
    Fin.sum_univ_one, Fin.sum_univ_three, map_smul, Complex.ofReal_zero, zero_smul,
    Complex.ofReal_one, one_smul, add_zero, zero_add, Complex.ofReal_div, Complex.ofReal_add,
    Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_neg,
    Complex.ofReal_ofNat]
  match_scalars <;> (field_simp; ring)

/-- **The light-cone derivative `∂_0 + ∂_x` lowers the `x`-boost weight by two.** -/
lemma jetDeriv_lightConeX_neg_mem {k : ℤ} {x : JetAlgebra} (hb : x ∈ bosonic)
    (hx : x ∈ boostWeightSubmodule 0 k) :
    jetDeriv (Sum.inl 0) x + jetDeriv (Sum.inr 0) x ∈ boostWeightSubmodule 0 (k - 2) := by
  intro t ht
  have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [map_add, repLorentzGroup_jetDeriv_of_mem_bosonic _ _ hb,
    repLorentzGroup_jetDeriv_of_mem_bosonic _ _ hb, hx t ht]
  rw [algebraMap_real_complex, zpow_sub₀ ht']
  simp only [boostAxis_zero, toLorentzGroup_boostXel, boostMatX, Fintype.sum_sum_type,
    Fin.sum_univ_one, Fin.sum_univ_three, map_smul, Complex.ofReal_zero, zero_smul,
    Complex.ofReal_one, one_smul, add_zero, zero_add, Complex.ofReal_div, Complex.ofReal_add,
    Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_neg,
    Complex.ofReal_ofNat]
  match_scalars <;> (field_simp; ring)

/-- **A transverse derivative leaves the `x`-boost weight alone.** -/
lemma jetDeriv_transverseX_mem {k : ℤ} {x : JetAlgebra} {i : Fin 3} (hi : i ≠ 0)
    (hb : x ∈ bosonic) (hx : x ∈ boostWeightSubmodule 0 k) :
    jetDeriv (Sum.inr i) x ∈ boostWeightSubmodule 0 k := by
  intro t ht
  have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_jetDeriv_of_mem_bosonic _ _ hb, hx t ht, algebraMap_real_complex]
  fin_cases i
  · exact absurd rfl hi
  ·
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    simp only [boostAxis_zero, toLorentzGroup_boostXel, boostMatX, Fintype.sum_sum_type,
      Fin.sum_univ_one, Fin.sum_univ_three, map_smul, Complex.ofReal_zero, zero_smul,
      Complex.ofReal_one, one_smul, add_zero, zero_add, Complex.ofReal_div, Complex.ofReal_add,
      Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_neg,
      Complex.ofReal_ofNat]
  ·
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    simp only [boostAxis_zero, toLorentzGroup_boostXel, boostMatX, Fintype.sum_sum_type,
      Fin.sum_univ_one, Fin.sum_univ_three, map_smul, Complex.ofReal_zero, zero_smul,
      Complex.ofReal_one, one_smul, add_zero, zero_add, Complex.ofReal_div, Complex.ofReal_add,
      Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_neg,
      Complex.ofReal_ofNat]

/-- **The light-cone derivative `∂_0 - ∂_y` raises the `y`-boost weight by two.** -/
lemma jetDeriv_lightConeY_pos_mem {k : ℤ} {x : JetAlgebra} (hb : x ∈ bosonic)
    (hx : x ∈ boostWeightSubmodule 1 k) :
    jetDeriv (Sum.inl 0) x - jetDeriv (Sum.inr 1) x ∈ boostWeightSubmodule 1 (k + 2) := by
  intro t ht
  have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [map_sub, repLorentzGroup_jetDeriv_of_mem_bosonic _ _ hb,
    repLorentzGroup_jetDeriv_of_mem_bosonic _ _ hb, hx t ht]
  rw [algebraMap_real_complex, zpow_add₀ ht']
  simp only [boostAxis_one, toLorentzGroup_boostYel, boostMatY, Fintype.sum_sum_type,
    Fin.sum_univ_one, Fin.sum_univ_three, map_smul, Complex.ofReal_zero, zero_smul,
    Complex.ofReal_one, one_smul, add_zero, zero_add, Complex.ofReal_div, Complex.ofReal_add,
    Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_neg,
    Complex.ofReal_ofNat]
  match_scalars <;> (field_simp; ring)

/-- **The light-cone derivative `∂_0 + ∂_y` lowers the `y`-boost weight by two.** -/
lemma jetDeriv_lightConeY_neg_mem {k : ℤ} {x : JetAlgebra} (hb : x ∈ bosonic)
    (hx : x ∈ boostWeightSubmodule 1 k) :
    jetDeriv (Sum.inl 0) x + jetDeriv (Sum.inr 1) x ∈ boostWeightSubmodule 1 (k - 2) := by
  intro t ht
  have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [map_add, repLorentzGroup_jetDeriv_of_mem_bosonic _ _ hb,
    repLorentzGroup_jetDeriv_of_mem_bosonic _ _ hb, hx t ht]
  rw [algebraMap_real_complex, zpow_sub₀ ht']
  simp only [boostAxis_one, toLorentzGroup_boostYel, boostMatY, Fintype.sum_sum_type,
    Fin.sum_univ_one, Fin.sum_univ_three, map_smul, Complex.ofReal_zero, zero_smul,
    Complex.ofReal_one, one_smul, add_zero, zero_add, Complex.ofReal_div, Complex.ofReal_add,
    Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_neg,
    Complex.ofReal_ofNat]
  match_scalars <;> (field_simp; ring)

/-- **A transverse derivative leaves the `y`-boost weight alone.** -/
lemma jetDeriv_transverseY_mem {k : ℤ} {x : JetAlgebra} {i : Fin 3} (hi : i ≠ 1)
    (hb : x ∈ bosonic) (hx : x ∈ boostWeightSubmodule 1 k) :
    jetDeriv (Sum.inr i) x ∈ boostWeightSubmodule 1 k := by
  intro t ht
  have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_jetDeriv_of_mem_bosonic _ _ hb, hx t ht, algebraMap_real_complex]
  fin_cases i
  ·
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    simp only [boostAxis_one, toLorentzGroup_boostYel, boostMatY, Fintype.sum_sum_type,
      Fin.sum_univ_one, Fin.sum_univ_three, map_smul, Complex.ofReal_zero, zero_smul,
      Complex.ofReal_one, one_smul, add_zero, zero_add, Complex.ofReal_div, Complex.ofReal_add,
      Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_neg,
      Complex.ofReal_ofNat]
  · exact absurd rfl hi
  ·
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    simp only [boostAxis_one, toLorentzGroup_boostYel, boostMatY, Fintype.sum_sum_type,
      Fin.sum_univ_one, Fin.sum_univ_three, map_smul, Complex.ofReal_zero, zero_smul,
      Complex.ofReal_one, one_smul, add_zero, zero_add, Complex.ofReal_div, Complex.ofReal_add,
      Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_neg,
      Complex.ofReal_ofNat]

/-!

## D. The light-cone derivative operators

Along the axis `i` the four derivative directions regroup into the two light-cone combinations
`∂_0 ∓ ∂_i`, which shift the `i`-boost weight by `±2`, and the two transverse derivatives, which
preserve it. The three axes differ only through the shift lemmas of sections A and B, so the
operators, and everything algebraic about them, are set up once, parametrised by the axis.

-/

/-- The light-cone derivative `∂_0 - ∂_i`, as an operator. -/
noncomputable def lcp (i : Fin 3) : JetAlgebra →ₗ[ℂ] JetAlgebra :=
  jetDeriv (Sum.inl 0) - jetDeriv (Sum.inr i)

/-- The light-cone derivative `∂_0 + ∂_i`, as an operator. -/
noncomputable def lcn (i : Fin 3) : JetAlgebra →ₗ[ℂ] JetAlgebra :=
  jetDeriv (Sum.inl 0) + jetDeriv (Sum.inr i)

lemma lcp_apply (i : Fin 3) (x : JetAlgebra) :
    lcp i x = jetDeriv (Sum.inl 0) x - jetDeriv (Sum.inr i) x := rfl

lemma lcn_apply (i : Fin 3) (x : JetAlgebra) :
    lcn i x = jetDeriv (Sum.inl 0) x + jetDeriv (Sum.inr i) x := rfl

/-- `∂_0 - ∂_i` raises the `i`-boost weight of a bosonic element by two. -/
lemma lcp_mem_boostWeight {i : Fin 3} {k : ℤ} {x : JetAlgebra} (hb : x ∈ bosonic)
    (hx : x ∈ boostWeightSubmodule i k) : lcp i x ∈ boostWeightSubmodule i (k + 2) := by
  fin_cases i
  · exact jetDeriv_lightConeX_pos_mem hb hx
  · exact jetDeriv_lightConeY_pos_mem hb hx
  · exact jetDeriv_lightConeZ_pos_mem hb hx

/-- `∂_0 + ∂_i` lowers the `i`-boost weight of a bosonic element by two. -/
lemma lcn_mem_boostWeight {i : Fin 3} {k : ℤ} {x : JetAlgebra} (hb : x ∈ bosonic)
    (hx : x ∈ boostWeightSubmodule i k) : lcn i x ∈ boostWeightSubmodule i (k - 2) := by
  fin_cases i
  · exact jetDeriv_lightConeX_neg_mem hb hx
  · exact jetDeriv_lightConeY_neg_mem hb hx
  · exact jetDeriv_lightConeZ_neg_mem hb hx

/-- A transverse derivative preserves the `i`-boost weight of a bosonic element. -/
lemma jetDeriv_transverse_mem {i j : Fin 3} (hj : j ≠ i) {k : ℤ} {x : JetAlgebra}
    (hb : x ∈ bosonic) (hx : x ∈ boostWeightSubmodule i k) :
    jetDeriv (Sum.inr j) x ∈ boostWeightSubmodule i k := by
  fin_cases i
  · exact jetDeriv_transverseX_mem hj hb hx
  · exact jetDeriv_transverseY_mem hj hb hx
  · exact jetDeriv_transverseZ_mem hj hb hx

/-- The light-cone operators keep the bosonic part bosonic. -/
lemma lcp_mem_bosonic {i : Fin 3} {x : JetAlgebra} (hx : x ∈ bosonic) : lcp i x ∈ bosonic :=
  sub_mem (jetDeriv_mem_bosonic _ hx) (jetDeriv_mem_bosonic _ hx)

lemma lcn_mem_bosonic {i : Fin 3} {x : JetAlgebra} (hx : x ∈ bosonic) : lcn i x ∈ bosonic :=
  add_mem (jetDeriv_mem_bosonic _ hx) (jetDeriv_mem_bosonic _ hx)

/-- A bosonic submodule of pure `i`-boost weight is carried by `∂_0 - ∂_i` to one of weight two
  higher. -/
lemma map_lcp_le {i : Fin 3} {k : ℤ} {P : Submodule ℂ JetAlgebra} (hb : P ≤ bosonic)
    (hw : P ≤ boostWeightSubmodule i k) :
    Submodule.map (lcp i) P ≤ boostWeightSubmodule i (k + 2) := by
  rintro y ⟨u, hu, rfl⟩
  exact lcp_mem_boostWeight (hb hu) (hw hu)

/-- The partner of `map_lcp_le`: `∂_0 + ∂_i` lowers the weight by two. -/
lemma map_lcn_le {i : Fin 3} {k : ℤ} {P : Submodule ℂ JetAlgebra} (hb : P ≤ bosonic)
    (hw : P ≤ boostWeightSubmodule i k) :
    Submodule.map (lcn i) P ≤ boostWeightSubmodule i (k - 2) := by
  rintro y ⟨u, hu, rfl⟩
  exact lcn_mem_boostWeight (hb hu) (hw hu)

/-- A transverse derivative preserves the `i`-boost weight of a bosonic submodule. -/
lemma map_jetDeriv_transverse_le {i j : Fin 3} (hj : j ≠ i) {k : ℤ}
    {P : Submodule ℂ JetAlgebra} (hb : P ≤ bosonic) (hw : P ≤ boostWeightSubmodule i k) :
    Submodule.map (jetDeriv (Sum.inr j)) P ≤ boostWeightSubmodule i k := by
  rintro y ⟨u, hu, rfl⟩
  exact jetDeriv_transverse_mem hj (hb hu) (hw hu)

lemma map_lcp_le_bosonic {i : Fin 3} {P : Submodule ℂ JetAlgebra} (hb : P ≤ bosonic) :
    Submodule.map (lcp i) P ≤ bosonic := by
  rintro y ⟨u, hu, rfl⟩
  exact lcp_mem_bosonic (hb hu)

lemma map_lcn_le_bosonic {i : Fin 3} {P : Submodule ℂ JetAlgebra} (hb : P ≤ bosonic) :
    Submodule.map (lcn i) P ≤ bosonic := by
  rintro y ⟨u, hu, rfl⟩
  exact lcn_mem_bosonic (hb hu)

lemma map_jetDeriv_le_bosonic (μ : Fin 1 ⊕ Fin 3) {P : Submodule ℂ JetAlgebra}
    (hb : P ≤ bosonic) : Submodule.map (jetDeriv μ) P ≤ bosonic := by
  rintro y ⟨u, hu, rfl⟩
  exact jetDeriv_mem_bosonic _ (hb hu)

/-!

## E. Every second derivative is a light-cone second derivative

-/

private lemma eq_or_eq_of_ne : ∀ {i t₁ t₂ j : Fin 3}, t₁ ≠ i → t₂ ≠ i → t₁ ≠ t₂ → j ≠ i →
    j = t₁ ∨ j = t₂ := by decide

/-- The four light-cone directions of the axis `i` span the derivatives: every `∂_μ` is a
  combination of `∂_0 ∓ ∂_i` and the two transverse derivatives. -/
lemma jetDeriv_mem_span_lightCone {i t₁ t₂ : Fin 3} (h₁ : t₁ ≠ i) (h₂ : t₂ ≠ i)
    (h₁₂ : t₁ ≠ t₂) (μ : Fin 1 ⊕ Fin 3) (x : JetAlgebra) :
    jetDeriv μ x ∈ Submodule.span ℂ
      {lcp i x, lcn i x, jetDeriv (Sum.inr t₁) x, jetDeriv (Sum.inr t₂) x} := by
  have hp : lcp i x ∈ Submodule.span ℂ
      {lcp i x, lcn i x, jetDeriv (Sum.inr t₁) x, jetDeriv (Sum.inr t₂) x} :=
    Submodule.subset_span (by simp)
  have hm : lcn i x ∈ Submodule.span ℂ
      {lcp i x, lcn i x, jetDeriv (Sum.inr t₁) x, jetDeriv (Sum.inr t₂) x} :=
    Submodule.subset_span (by simp)
  match μ with
  | Sum.inl 0 =>
    rw [show jetDeriv (Sum.inl 0) x = (2⁻¹ : ℂ) • lcp i x + (2⁻¹ : ℂ) • lcn i x from by
      rw [lcp_apply, lcn_apply]; module]
    exact add_mem (Submodule.smul_mem _ _ hp) (Submodule.smul_mem _ _ hm)
  | Sum.inr j =>
    by_cases hj : j = i
    · subst hj
      rw [show jetDeriv (Sum.inr j) x = (-2⁻¹ : ℂ) • lcp j x + (2⁻¹ : ℂ) • lcn j x from by
        rw [lcp_apply, lcn_apply]; module]
      exact add_mem (Submodule.smul_mem _ _ hp) (Submodule.smul_mem _ _ hm)
    · rcases eq_or_eq_of_ne h₁ h₂ h₁₂ hj with rfl | rfl
      · exact Submodule.subset_span (by simp)
      · exact Submodule.subset_span (by simp)

/-- The light-cone derivatives commute with every jet derivative. -/
lemma lcp_jetDeriv_comm (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) (x : JetAlgebra) :
    lcp i (jetDeriv μ x) = jetDeriv μ (lcp i x) := by
  rw [lcp_apply, lcp_apply, map_sub, jetDeriv_comm, jetDeriv_comm (Sum.inr i)]

lemma lcn_jetDeriv_comm (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) (x : JetAlgebra) :
    lcn i (jetDeriv μ x) = jetDeriv μ (lcn i x) := by
  rw [lcn_apply, lcn_apply, map_add, jetDeriv_comm, jetDeriv_comm (Sum.inr i)]

/-- The two light-cone derivatives commute with each other. -/
lemma lcn_lcp_comm (i : Fin 3) (x : JetAlgebra) : lcn i (lcp i x) = lcp i (lcn i x) := by
  simp only [lcp_apply, lcn_apply, map_sub, map_add, jetDeriv_comm (Sum.inl 0) (Sum.inr i)]
  abel

/-- One step of the light-cone derivative expansion along the axis `i` with transverse
  directions `t₁`, `t₂`: the four derivative directions applied to a submodule. -/
noncomputable def stepAxis (i t₁ t₂ : Fin 3) (P : Submodule ℂ JetAlgebra) :
    Submodule ℂ JetAlgebra :=
  Submodule.map (lcp i) P ⊔ Submodule.map (lcn i) P ⊔
    Submodule.map (jetDeriv (Sum.inr t₁)) P ⊔ Submodule.map (jetDeriv (Sum.inr t₂)) P

lemma stepAxis_mono {i t₁ t₂ : Fin 3} {P Q : Submodule ℂ JetAlgebra} (h : P ≤ Q) :
    stepAxis i t₁ t₂ P ≤ stepAxis i t₁ t₂ Q :=
  sup_le_sup (sup_le_sup (sup_le_sup (Submodule.map_mono h) (Submodule.map_mono h))
    (Submodule.map_mono h)) (Submodule.map_mono h)

/-- Every jet derivative of an element of `P` lies in `stepAxis i t₁ t₂ P`. -/
lemma jetDeriv_mem_stepAxis {i t₁ t₂ : Fin 3} (h₁ : t₁ ≠ i) (h₂ : t₂ ≠ i) (h₁₂ : t₁ ≠ t₂)
    {P : Submodule ℂ JetAlgebra} {x : JetAlgebra} (hx : x ∈ P) (μ : Fin 1 ⊕ Fin 3) :
    jetDeriv μ x ∈ stepAxis i t₁ t₂ P := by
  refine Submodule.span_le.2 ?_ (jetDeriv_mem_span_lightCone h₁ h₂ h₁₂ μ x)
  rintro y (rfl | rfl | rfl | rfl)
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left ⟨x, hx, rfl⟩))
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right ⟨x, hx, rfl⟩))
  · exact Submodule.mem_sup_left (Submodule.mem_sup_right ⟨x, hx, rfl⟩)
  · exact Submodule.mem_sup_right ⟨x, hx, rfl⟩

/-!

## F. The boost weight zero part of the second derivatives

-/

/-- **The boost weight zero part of the second derivatives of the field strength.** An element
  of the span of the monomials `∂_ρ ∂_τ F_{μν}` of `z`-boost weight zero is a combination of the
  sixteen listed second derivatives: the derivative pair and the field strength each carry a
  weight, and the two must cancel. Only this inclusion feeds the three-axis theorem, so the
  converse is not recorded. -/
lemma boostWeight_inter_fieldStrengthDeriv_pair_le :
    boostWeightSubmodule 2 0 ⊓ Submodule.span ℂ
        {x | ∃ ρ τ μ ν, x = fieldStrengthDeriv {ρ, τ} μ ν} ≤
      Submodule.span ℂ
        {lcp 2 (lcn 2 (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1))),
        lcp 2 (lcn 2 (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2))),
        jetDeriv (Sum.inr 0) (jetDeriv (Sum.inr 0) (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1))),
        jetDeriv (Sum.inr 0) (jetDeriv (Sum.inr 0) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2))),
        jetDeriv (Sum.inr 0) (jetDeriv (Sum.inr 1) (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1))),
        jetDeriv (Sum.inr 0) (jetDeriv (Sum.inr 1) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2))),
        jetDeriv (Sum.inr 1) (jetDeriv (Sum.inr 1) (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1))),
        jetDeriv (Sum.inr 1) (jetDeriv (Sum.inr 1) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2))),
        lcp 2 (jetDeriv (Sum.inr 0) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) + fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0))),
        lcp 2 (jetDeriv (Sum.inr 0) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) + fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1))),
        lcp 2 (jetDeriv (Sum.inr 1) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) + fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0))),
        lcp 2 (jetDeriv (Sum.inr 1) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) + fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1))),
        lcn 2 (jetDeriv (Sum.inr 0) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) - fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0))),
        lcn 2 (jetDeriv (Sum.inr 0) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) - fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1))),
        lcn 2 (jetDeriv (Sum.inr 1) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) - fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0))),
        lcn 2 (jetDeriv (Sum.inr 1) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) - fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1)))} := by
  set PX := fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) -
    fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) with hPX
  set PY := fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) -
    fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) with hPY
  set MX := fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) +
    fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) with hMX
  set MY := fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) +
    fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) with hMY
  set T := fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) with hT
  set L := fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) with hL
  obtain ⟨hPXw, hPYw, hMXw, hMYw, hTw, hLw⟩ :
      PX ∈ boostWeightSubmodule 2 2 ∧ PY ∈ boostWeightSubmodule 2 2 ∧
      MX ∈ boostWeightSubmodule 2 (-2) ∧ MY ∈ boostWeightSubmodule 2 (-2) ∧
      T ∈ boostWeightSubmodule 2 0 ∧ L ∈ boostWeightSubmodule 2 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro t ht
    all_goals
      have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
      simp only [hPX, hPY, hMX, hMY, hT, hL, map_sub, map_add, boostAxis_two,
        repLorentzGroup_fieldStrengthDeriv_nil, algebraMap_real_complex,
        toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three,
        boostMatZ, fieldStrengthDeriv_self, mul_zero, zero_mul, mul_one, Complex.ofReal_zero,
        zero_smul, smul_zero, add_zero, zero_add]
      try rw [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) =
        -fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) from
        fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 2)]
      push_cast
      match_scalars <;> (field_simp; try ring)
  -- ### B. Every field strength is a combination of the eigenvectors
  -- On the light-cone pairs this is `F_{0x} = ((F_{0x} - F_{zx}) + (F_{0x} + F_{zx}))/2` and its
  -- partners; the remaining components are zero, `±F_{xy}`, or `±F_{0z}` by antisymmetry.
  set A := Submodule.span ℂ {PX, PY} with hA
  set B := Submodule.span ℂ {T, L} with hB
  set C := Submodule.span ℂ {MX, MY} with hC
  set V := Submodule.span ℂ {x | ∃ μ ν, x = fieldStrengthDeriv {} μ ν} with hV
  have hAle : A ≤ boostWeightSubmodule 2 2 := by
    rw [hA]; exact Submodule.span_le.2 (by rintro x (rfl | rfl); exacts [hPXw, hPYw])
  have hBle : B ≤ boostWeightSubmodule 2 0 := by
    rw [hB]; exact Submodule.span_le.2 (by rintro x (rfl | rfl); exacts [hTw, hLw])
  have hCle : C ≤ boostWeightSubmodule 2 (-2) := by
    rw [hC]; exact Submodule.span_le.2 (by rintro x (rfl | rfl); exacts [hMXw, hMYw])
  have hAV : A ≤ A ⊔ B ⊔ C := le_sup_left.trans le_sup_left
  have hBV : B ≤ A ⊔ B ⊔ C := le_sup_right.trans le_sup_left
  have hCV : C ≤ A ⊔ B ⊔ C := le_sup_right
  have hPXV : PX ∈ A ⊔ B ⊔ C := hAV (Submodule.subset_span (Set.mem_insert _ _))
  have hPYV : PY ∈ A ⊔ B ⊔ C := hAV (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  have hTV : T ∈ A ⊔ B ⊔ C := hBV (Submodule.subset_span (Set.mem_insert _ _))
  have hLV : L ∈ A ⊔ B ⊔ C := hBV (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  have hMXV : MX ∈ A ⊔ B ⊔ C := hCV (Submodule.subset_span (Set.mem_insert _ _))
  have hMYV : MY ∈ A ⊔ B ⊔ C := hCV (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  have key : ∀ {u v x : JetAlgebra} (c d : ℂ), u ∈ A ⊔ B ⊔ C → v ∈ A ⊔ B ⊔ C →
      x = c • u + d • v → x ∈ A ⊔ B ⊔ C := by
    rintro u v x c d hu hv rfl
    exact add_mem (Submodule.smul_mem _ c hu) (Submodule.smul_mem _ d hv)
  have keyn : ∀ {u v : JetAlgebra} (c d : ℂ) {μ ν : Fin 1 ⊕ Fin 3}, u ∈ A ⊔ B ⊔ C →
      v ∈ A ⊔ B ⊔ C → fieldStrengthDeriv {} μ ν = c • u + d • v →
      fieldStrengthDeriv {} ν μ ∈ A ⊔ B ⊔ C := by
    intro u v c d μ ν hu hv h
    rw [fieldStrengthDeriv_antisymm, h]
    exact neg_mem (add_mem (Submodule.smul_mem _ c hu) (Submodule.smul_mem _ d hv))
  have hVle : V ≤ A ⊔ B ⊔ C := by
    rw [hV]
    refine Submodule.span_le.2 ?_
    rintro x ⟨μ, ν, rfl⟩
    match μ, ν with
    | Sum.inl 0, Sum.inl 0 | Sum.inr 0, Sum.inr 0 | Sum.inr 1, Sum.inr 1
    | Sum.inr 2, Sum.inr 2 => rw [fieldStrengthDeriv_self]; exact zero_mem _
    | Sum.inl 0, Sum.inr 0 => exact key 2⁻¹ 2⁻¹ hPXV hMXV (by rw [hPX, hMX]; module)
    | Sum.inr 0, Sum.inl 0 => exact keyn 2⁻¹ 2⁻¹ hPXV hMXV (by rw [hPX, hMX]; module)
    | Sum.inl 0, Sum.inr 1 => exact key 2⁻¹ 2⁻¹ hPYV hMYV (by rw [hPY, hMY]; module)
    | Sum.inr 1, Sum.inl 0 => exact keyn 2⁻¹ 2⁻¹ hPYV hMYV (by rw [hPY, hMY]; module)
    | Sum.inr 2, Sum.inr 0 => exact key (-2⁻¹) 2⁻¹ hPXV hMXV (by rw [hPX, hMX]; module)
    | Sum.inr 0, Sum.inr 2 => exact keyn (-2⁻¹) 2⁻¹ hPXV hMXV (by rw [hPX, hMX]; module)
    | Sum.inr 2, Sum.inr 1 => exact key (-2⁻¹) 2⁻¹ hPYV hMYV (by rw [hPY, hMY]; module)
    | Sum.inr 1, Sum.inr 2 => exact keyn (-2⁻¹) 2⁻¹ hPYV hMYV (by rw [hPY, hMY]; module)
    | Sum.inr 0, Sum.inr 1 => exact hTV
    | Sum.inr 1, Sum.inr 0 => rw [fieldStrengthDeriv_antisymm]; exact neg_mem hTV
    | Sum.inl 0, Sum.inr 2 => exact hLV
    | Sum.inr 2, Sum.inl 0 => rw [fieldStrengthDeriv_antisymm]; exact neg_mem hLV
  set FF : Set JetAlgebra := {x | ∃ ρ τ μ ν, x = fieldStrengthDeriv {ρ, τ} μ ν} with hFF
  set S : Set JetAlgebra :=
    {lcp 2 (lcn 2 T),
      lcp 2 (lcn 2 L),
      (jetDeriv (Sum.inr 0)) ((jetDeriv (Sum.inr 0)) T),
      (jetDeriv (Sum.inr 0)) ((jetDeriv (Sum.inr 0)) L),
      (jetDeriv (Sum.inr 0)) ((jetDeriv (Sum.inr 1)) T),
      (jetDeriv (Sum.inr 0)) ((jetDeriv (Sum.inr 1)) L),
      (jetDeriv (Sum.inr 1)) ((jetDeriv (Sum.inr 1)) T),
      (jetDeriv (Sum.inr 1)) ((jetDeriv (Sum.inr 1)) L),
      lcp 2 ((jetDeriv (Sum.inr 0)) MX),
      lcp 2 ((jetDeriv (Sum.inr 0)) MY),
      lcp 2 ((jetDeriv (Sum.inr 1)) MX),
      lcp 2 ((jetDeriv (Sum.inr 1)) MY),
      lcn 2 ((jetDeriv (Sum.inr 0)) PX),
      lcn 2 ((jetDeriv (Sum.inr 0)) PY),
      lcn 2 ((jetDeriv (Sum.inr 1)) PX),
      lcn 2 ((jetDeriv (Sum.inr 1)) PY)} with hS
  set W := Submodule.span ℂ S ⊔ ⨆ (j : ℤ) (_ : j ≠ 0), boostWeightSubmodule 2 j with hW
  -- the three weight spaces are bosonic
  have hFb : ∀ μ ν, fieldStrengthDeriv {} μ ν ∈ bosonic := fun μ ν =>
    fieldStrengthDeriv_mem_bosonic _ _ _
  have hAb : A ≤ bosonic := by
    rw [hA]
    refine Submodule.span_le.2 ?_
    rintro x (rfl | rfl)
    · rw [hPX]; exact sub_mem (hFb _ _) (hFb _ _)
    · rw [hPY]; exact sub_mem (hFb _ _) (hFb _ _)
  have hBb : B ≤ bosonic := by
    rw [hB]
    refine Submodule.span_le.2 ?_
    rintro x (rfl | rfl)
    · rw [hT]; exact hFb _ _
    · rw [hL]; exact hFb _ _
  have hCb : C ≤ bosonic := by
    rw [hC]
    refine Submodule.span_le.2 ?_
    rintro x (rfl | rfl)
    · rw [hMX]; exact add_mem (hFb _ _) (hFb _ _)
    · rw [hMY]; exact add_mem (hFb _ _) (hFb _ _)
  have hN : ∀ {j : ℤ} {P : Submodule ℂ JetAlgebra}, j ≠ 0 →
      P ≤ boostWeightSubmodule 2 j → P ≤ W := fun hj hP =>
    le_trans hP (le_sup_of_le_right (le_iSup_of_le _ (le_iSup_of_le hj le_rfl)))
  have bpA : Submodule.map (lcp 2) A ≤ bosonic := map_lcp_le_bosonic hAb
  have wpA : Submodule.map (lcp 2) A ≤
      boostWeightSubmodule 2 (2 + 2) := map_lcp_le hAb hAle
  have bpB : Submodule.map (lcp 2) B ≤ bosonic := map_lcp_le_bosonic hBb
  have wpB : Submodule.map (lcp 2) B ≤
      boostWeightSubmodule 2 (0 + 2) := map_lcp_le hBb hBle
  have bpC : Submodule.map (lcp 2) C ≤ bosonic := map_lcp_le_bosonic hCb
  have wpC : Submodule.map (lcp 2) C ≤
      boostWeightSubmodule 2 (-2 + 2) := map_lcp_le hCb hCle
  have bmA : Submodule.map (lcn 2) A ≤ bosonic := map_lcn_le_bosonic hAb
  have wmA : Submodule.map (lcn 2) A ≤
      boostWeightSubmodule 2 (2 - 2) := map_lcn_le hAb hAle
  have bmB : Submodule.map (lcn 2) B ≤ bosonic := map_lcn_le_bosonic hBb
  have wmB : Submodule.map (lcn 2) B ≤
      boostWeightSubmodule 2 (0 - 2) := map_lcn_le hBb hBle
  have bmC : Submodule.map (lcn 2) C ≤ bosonic := map_lcn_le_bosonic hCb
  have wmC : Submodule.map (lcn 2) C ≤
      boostWeightSubmodule 2 (-2 - 2) := map_lcn_le hCb hCle
  have bxA : Submodule.map (jetDeriv (Sum.inr 0)) A ≤ bosonic := map_jetDeriv_le_bosonic (Sum.inr 0) hAb
  have wxA : Submodule.map (jetDeriv (Sum.inr 0)) A ≤
      boostWeightSubmodule 2 (2) := map_jetDeriv_transverse_le (by decide) hAb hAle
  have bxB : Submodule.map (jetDeriv (Sum.inr 0)) B ≤ bosonic := map_jetDeriv_le_bosonic (Sum.inr 0) hBb
  have wxB : Submodule.map (jetDeriv (Sum.inr 0)) B ≤
      boostWeightSubmodule 2 (0) := map_jetDeriv_transverse_le (by decide) hBb hBle
  have bxC : Submodule.map (jetDeriv (Sum.inr 0)) C ≤ bosonic := map_jetDeriv_le_bosonic (Sum.inr 0) hCb
  have wxC : Submodule.map (jetDeriv (Sum.inr 0)) C ≤
      boostWeightSubmodule 2 (-2) := map_jetDeriv_transverse_le (by decide) hCb hCle
  have byA : Submodule.map (jetDeriv (Sum.inr 1)) A ≤ bosonic := map_jetDeriv_le_bosonic (Sum.inr 1) hAb
  have wyA : Submodule.map (jetDeriv (Sum.inr 1)) A ≤
      boostWeightSubmodule 2 (2) := map_jetDeriv_transverse_le (by decide) hAb hAle
  have byB : Submodule.map (jetDeriv (Sum.inr 1)) B ≤ bosonic := map_jetDeriv_le_bosonic (Sum.inr 1) hBb
  have wyB : Submodule.map (jetDeriv (Sum.inr 1)) B ≤
      boostWeightSubmodule 2 (0) := map_jetDeriv_transverse_le (by decide) hBb hBle
  have byC : Submodule.map (jetDeriv (Sum.inr 1)) C ≤ bosonic := map_jetDeriv_le_bosonic (Sum.inr 1) hCb
  have wyC : Submodule.map (jetDeriv (Sum.inr 1)) C ≤
      boostWeightSubmodule 2 (-2) := map_jetDeriv_transverse_le (by decide) hCb hCle
  have eppA : Submodule.map (lcp 2) (Submodule.map (lcp 2) A) ≤ W :=
    hN (by norm_num) (map_lcp_le bpA wpA)
  have eppB : Submodule.map (lcp 2) (Submodule.map (lcp 2) B) ≤ W :=
    hN (by norm_num) (map_lcp_le bpB wpB)
  have eppC : Submodule.map (lcp 2) (Submodule.map (lcp 2) C) ≤ W :=
    hN (by norm_num) (map_lcp_le bpC wpC)
  have epmA : Submodule.map (lcp 2) (Submodule.map (lcn 2) A) ≤ W :=
    hN (by norm_num) (map_lcp_le bmA wmA)
  have epmB : Submodule.map (lcp 2) (Submodule.map (lcn 2) B) ≤ W := by
    simp only [hB, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have epmC : Submodule.map (lcp 2) (Submodule.map (lcn 2) C) ≤ W :=
    hN (by norm_num) (map_lcp_le bmC wmC)
  have epxA : Submodule.map (lcp 2) (Submodule.map (jetDeriv (Sum.inr 0)) A) ≤ W :=
    hN (by norm_num) (map_lcp_le bxA wxA)
  have epxB : Submodule.map (lcp 2) (Submodule.map (jetDeriv (Sum.inr 0)) B) ≤ W :=
    hN (by norm_num) (map_lcp_le bxB wxB)
  have epxC : Submodule.map (lcp 2) (Submodule.map (jetDeriv (Sum.inr 0)) C) ≤ W := by
    simp only [hC, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have epyA : Submodule.map (lcp 2) (Submodule.map (jetDeriv (Sum.inr 1)) A) ≤ W :=
    hN (by norm_num) (map_lcp_le byA wyA)
  have epyB : Submodule.map (lcp 2) (Submodule.map (jetDeriv (Sum.inr 1)) B) ≤ W :=
    hN (by norm_num) (map_lcp_le byB wyB)
  have epyC : Submodule.map (lcp 2) (Submodule.map (jetDeriv (Sum.inr 1)) C) ≤ W := by
    simp only [hC, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have empA : Submodule.map (lcn 2) (Submodule.map (lcp 2) A) ≤ W :=
    hN (by norm_num) (map_lcn_le bpA wpA)
  have empB : Submodule.map (lcn 2) (Submodule.map (lcp 2) B) ≤ W := by
    simp only [hB, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> rw [lcn_lcp_comm] <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have empC : Submodule.map (lcn 2) (Submodule.map (lcp 2) C) ≤ W :=
    hN (by norm_num) (map_lcn_le bpC wpC)
  have emmA : Submodule.map (lcn 2) (Submodule.map (lcn 2) A) ≤ W :=
    hN (by norm_num) (map_lcn_le bmA wmA)
  have emmB : Submodule.map (lcn 2) (Submodule.map (lcn 2) B) ≤ W :=
    hN (by norm_num) (map_lcn_le bmB wmB)
  have emmC : Submodule.map (lcn 2) (Submodule.map (lcn 2) C) ≤ W :=
    hN (by norm_num) (map_lcn_le bmC wmC)
  have emxA : Submodule.map (lcn 2) (Submodule.map (jetDeriv (Sum.inr 0)) A) ≤ W := by
    simp only [hA, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have emxB : Submodule.map (lcn 2) (Submodule.map (jetDeriv (Sum.inr 0)) B) ≤ W :=
    hN (by norm_num) (map_lcn_le bxB wxB)
  have emxC : Submodule.map (lcn 2) (Submodule.map (jetDeriv (Sum.inr 0)) C) ≤ W :=
    hN (by norm_num) (map_lcn_le bxC wxC)
  have emyA : Submodule.map (lcn 2) (Submodule.map (jetDeriv (Sum.inr 1)) A) ≤ W := by
    simp only [hA, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have emyB : Submodule.map (lcn 2) (Submodule.map (jetDeriv (Sum.inr 1)) B) ≤ W :=
    hN (by norm_num) (map_lcn_le byB wyB)
  have emyC : Submodule.map (lcn 2) (Submodule.map (jetDeriv (Sum.inr 1)) C) ≤ W :=
    hN (by norm_num) (map_lcn_le byC wyC)
  have expA : Submodule.map (jetDeriv (Sum.inr 0)) (Submodule.map (lcp 2) A) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bpA wpA)
  have expB : Submodule.map (jetDeriv (Sum.inr 0)) (Submodule.map (lcp 2) B) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bpB wpB)
  have expC : Submodule.map (jetDeriv (Sum.inr 0)) (Submodule.map (lcp 2) C) ≤ W := by
    simp only [hC, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> rw [← lcp_jetDeriv_comm] <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have exmA : Submodule.map (jetDeriv (Sum.inr 0)) (Submodule.map (lcn 2) A) ≤ W := by
    simp only [hA, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> rw [← lcn_jetDeriv_comm] <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have exmB : Submodule.map (jetDeriv (Sum.inr 0)) (Submodule.map (lcn 2) B) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bmB wmB)
  have exmC : Submodule.map (jetDeriv (Sum.inr 0)) (Submodule.map (lcn 2) C) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bmC wmC)
  have exxA : Submodule.map (jetDeriv (Sum.inr 0)) (Submodule.map (jetDeriv (Sum.inr 0)) A) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bxA wxA)
  have exxB : Submodule.map (jetDeriv (Sum.inr 0)) (Submodule.map (jetDeriv (Sum.inr 0)) B) ≤ W := by
    simp only [hB, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have exxC : Submodule.map (jetDeriv (Sum.inr 0)) (Submodule.map (jetDeriv (Sum.inr 0)) C) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bxC wxC)
  have exyA : Submodule.map (jetDeriv (Sum.inr 0)) (Submodule.map (jetDeriv (Sum.inr 1)) A) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) byA wyA)
  have exyB : Submodule.map (jetDeriv (Sum.inr 0)) (Submodule.map (jetDeriv (Sum.inr 1)) B) ≤ W := by
    simp only [hB, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have exyC : Submodule.map (jetDeriv (Sum.inr 0)) (Submodule.map (jetDeriv (Sum.inr 1)) C) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) byC wyC)
  have eypA : Submodule.map (jetDeriv (Sum.inr 1)) (Submodule.map (lcp 2) A) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bpA wpA)
  have eypB : Submodule.map (jetDeriv (Sum.inr 1)) (Submodule.map (lcp 2) B) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bpB wpB)
  have eypC : Submodule.map (jetDeriv (Sum.inr 1)) (Submodule.map (lcp 2) C) ≤ W := by
    simp only [hC, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> rw [← lcp_jetDeriv_comm] <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have eymA : Submodule.map (jetDeriv (Sum.inr 1)) (Submodule.map (lcn 2) A) ≤ W := by
    simp only [hA, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> rw [← lcn_jetDeriv_comm] <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have eymB : Submodule.map (jetDeriv (Sum.inr 1)) (Submodule.map (lcn 2) B) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bmB wmB)
  have eymC : Submodule.map (jetDeriv (Sum.inr 1)) (Submodule.map (lcn 2) C) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bmC wmC)
  have eyxA : Submodule.map (jetDeriv (Sum.inr 1)) (Submodule.map (jetDeriv (Sum.inr 0)) A) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bxA wxA)
  have eyxB : Submodule.map (jetDeriv (Sum.inr 1)) (Submodule.map (jetDeriv (Sum.inr 0)) B) ≤ W := by
    simp only [hB, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> rw [jetDeriv_comm (Sum.inr 1) (Sum.inr 0)] <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have eyxC : Submodule.map (jetDeriv (Sum.inr 1)) (Submodule.map (jetDeriv (Sum.inr 0)) C) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bxC wxC)
  have eyyA : Submodule.map (jetDeriv (Sum.inr 1)) (Submodule.map (jetDeriv (Sum.inr 1)) A) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) byA wyA)
  have eyyB : Submodule.map (jetDeriv (Sum.inr 1)) (Submodule.map (jetDeriv (Sum.inr 1)) B) ≤ W := by
    simp only [hB, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have eyyC : Submodule.map (jetDeriv (Sum.inr 1)) (Submodule.map (jetDeriv (Sum.inr 1)) C) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) byC wyC)
  -- every monomial is a second light-cone derivative of a field strength
  have hFFle : Submodule.span ℂ FF ≤ stepAxis 2 0 1 (stepAxis 2 0 1 V) := by
    rw [hFF]
    refine Submodule.span_le.2 ?_
    rintro x ⟨ρ, τ, μ, ν, rfl⟩
    rw [fieldStrengthDeriv_pair_eq_jetDeriv]
    exact jetDeriv_mem_stepAxis (by decide) (by decide) (by decide)
      (jetDeriv_mem_stepAxis (by decide) (by decide) (by decide)
        (by rw [hV]; exact Submodule.subset_span ⟨μ, ν, rfl⟩) τ) ρ
  have hmap4 : ∀ (f : JetAlgebra →ₗ[ℂ] JetAlgebra) (P Q R T : Submodule ℂ JetAlgebra),
      Submodule.map f P ≤ W → Submodule.map f Q ≤ W → Submodule.map f R ≤ W →
      Submodule.map f T ≤ W → Submodule.map f (P ⊔ Q ⊔ R ⊔ T) ≤ W := by
    intro f P Q R T h1 h2 h3 h4
    simp only [Submodule.map_sup]
    exact sup_le (sup_le (sup_le h1 h2) h3) h4
  have hin3 : ∀ (f g : JetAlgebra →ₗ[ℂ] JetAlgebra),
      Submodule.map f (Submodule.map g A) ≤ W → Submodule.map f (Submodule.map g B) ≤ W →
      Submodule.map f (Submodule.map g C) ≤ W →
      Submodule.map f (Submodule.map g (A ⊔ B ⊔ C)) ≤ W := by
    intro f g h1 h2 h3
    simp only [Submodule.map_sup]
    exact sup_le (sup_le h1 h2) h3
  have hfin : stepAxis 2 0 1 (stepAxis 2 0 1 (A ⊔ B ⊔ C)) ≤ W := by
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · exact hmap4 _ _ _ _ _ (hin3 _ _ eppA eppB eppC) (hin3 _ _ epmA epmB epmC)
        (hin3 _ _ epxA epxB epxC) (hin3 _ _ epyA epyB epyC)
    · exact hmap4 _ _ _ _ _ (hin3 _ _ empA empB empC) (hin3 _ _ emmA emmB emmC)
        (hin3 _ _ emxA emxB emxC) (hin3 _ _ emyA emyB emyC)
    · exact hmap4 _ _ _ _ _ (hin3 _ _ expA expB expC) (hin3 _ _ exmA exmB exmC)
        (hin3 _ _ exxA exxB exxC) (hin3 _ _ exyA exyB exyC)
    · exact hmap4 _ _ _ _ _ (hin3 _ _ eypA eypB eypC) (hin3 _ _ eymA eymB eymC)
        (hin3 _ _ eyxA eyxB eyxC) (hin3 _ _ eyyA eyyB eyyC)
  have hkey : Submodule.span ℂ FF ≤ W :=
    le_trans hFFle (le_trans (stepAxis_mono (stepAxis_mono hVle)) hfin)
  -- the sixteen generators have weight zero
  have hwz : ∀ {j : ℤ} {y : JetAlgebra}, j = 0 → y ∈ boostWeightSubmodule 2 j →
      y ∈ boostWeightSubmodule 2 0 := by rintro j y rfl h; exact h
  have hTb : T ∈ bosonic := by rw [hT]; exact hFb _ _
  have hLb : L ∈ bosonic := by rw [hL]; exact hFb _ _
  have hPXb : PX ∈ bosonic := by rw [hPX]; exact sub_mem (hFb _ _) (hFb _ _)
  have hPYb : PY ∈ bosonic := by rw [hPY]; exact sub_mem (hFb _ _) (hFb _ _)
  have hMXb : MX ∈ bosonic := by rw [hMX]; exact add_mem (hFb _ _) (hFb _ _)
  have hMYb : MY ∈ bosonic := by rw [hMY]; exact add_mem (hFb _ _) (hFb _ _)
  have hSw : Submodule.span ℂ S ≤ boostWeightSubmodule 2 0 := by
    rw [hS]
    refine Submodule.span_le.2 ?_
    rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl)
    exacts [
    hwz (by norm_num) (lcp_mem_boostWeight (lcn_mem_bosonic hTb)
      (lcn_mem_boostWeight hTb hTw)),
    hwz (by norm_num) (lcp_mem_boostWeight (lcn_mem_bosonic hLb)
      (lcn_mem_boostWeight hLb hLw)),
    jetDeriv_transverse_mem (by decide) (jetDeriv_mem_bosonic (Sum.inr 0) hTb) (jetDeriv_transverse_mem (by decide) hTb hTw),
    jetDeriv_transverse_mem (by decide) (jetDeriv_mem_bosonic (Sum.inr 0) hLb) (jetDeriv_transverse_mem (by decide) hLb hLw),
    jetDeriv_transverse_mem (by decide) (jetDeriv_mem_bosonic (Sum.inr 1) hTb) (jetDeriv_transverse_mem (by decide) hTb hTw),
    jetDeriv_transverse_mem (by decide) (jetDeriv_mem_bosonic (Sum.inr 1) hLb) (jetDeriv_transverse_mem (by decide) hLb hLw),
    jetDeriv_transverse_mem (by decide) (jetDeriv_mem_bosonic (Sum.inr 1) hTb) (jetDeriv_transverse_mem (by decide) hTb hTw),
    jetDeriv_transverse_mem (by decide) (jetDeriv_mem_bosonic (Sum.inr 1) hLb) (jetDeriv_transverse_mem (by decide) hLb hLw),
    hwz (by norm_num) (lcp_mem_boostWeight (jetDeriv_mem_bosonic (Sum.inr 0) hMXb) (jetDeriv_transverse_mem (by decide) hMXb hMXw)),
    hwz (by norm_num) (lcp_mem_boostWeight (jetDeriv_mem_bosonic (Sum.inr 0) hMYb) (jetDeriv_transverse_mem (by decide) hMYb hMYw)),
    hwz (by norm_num) (lcp_mem_boostWeight (jetDeriv_mem_bosonic (Sum.inr 1) hMXb) (jetDeriv_transverse_mem (by decide) hMXb hMXw)),
    hwz (by norm_num) (lcp_mem_boostWeight (jetDeriv_mem_bosonic (Sum.inr 1) hMYb) (jetDeriv_transverse_mem (by decide) hMYb hMYw)),
    hwz (by norm_num) (lcn_mem_boostWeight (jetDeriv_mem_bosonic (Sum.inr 0) hPXb) (jetDeriv_transverse_mem (by decide) hPXb hPXw)),
    hwz (by norm_num) (lcn_mem_boostWeight (jetDeriv_mem_bosonic (Sum.inr 0) hPYb) (jetDeriv_transverse_mem (by decide) hPYb hPYw)),
    hwz (by norm_num) (lcn_mem_boostWeight (jetDeriv_mem_bosonic (Sum.inr 1) hPXb) (jetDeriv_transverse_mem (by decide) hPXb hPXw)),
    hwz (by norm_num) (lcn_mem_boostWeight (jetDeriv_mem_bosonic (Sum.inr 1) hPYb) (jetDeriv_transverse_mem (by decide) hPYb hPYw))]
  refine le_trans (inf_le_inf_left _ hkey) ?_
  rw [hW, inf_comm, sup_inf_assoc_of_le _ hSw,
    disjoint_iff.mp (boostWeightSubmodule_iSupIndep (i := 2) 0).symm, sup_bot_eq]
/-!

## G. The boost weight zero part, `x`-direction

-/

/-- **The boost weight zero part of the second derivatives of the field strength.** An element
  of the span of the monomials `∂_ρ ∂_τ F_{μν}` of `x`-boost weight zero is a combination of the
  sixteen listed second derivatives: the derivative pair and the field strength each carry a
  weight, and the two must cancel. Only this inclusion feeds the three-axis theorem, so the
  converse is not recorded. -/
lemma boostWeight_inter_fieldStrengthDeriv_pair_x_le :
    boostWeightSubmodule 0 0 ⊓ Submodule.span ℂ
        {x | ∃ ρ τ μ ν, x = fieldStrengthDeriv {ρ, τ} μ ν} ≤
      Submodule.span ℂ
        {lcp 0 (lcn 0 (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2))),
        lcp 0 (lcn 0 (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0))),
        jetDeriv (Sum.inr 1) (jetDeriv (Sum.inr 1) (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2))),
        jetDeriv (Sum.inr 1) (jetDeriv (Sum.inr 1) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0))),
        jetDeriv (Sum.inr 1) (jetDeriv (Sum.inr 2) (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2))),
        jetDeriv (Sum.inr 1) (jetDeriv (Sum.inr 2) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0))),
        jetDeriv (Sum.inr 2) (jetDeriv (Sum.inr 2) (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2))),
        jetDeriv (Sum.inr 2) (jetDeriv (Sum.inr 2) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0))),
        lcp 0 (jetDeriv (Sum.inr 1) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) + fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1))),
        lcp 0 (jetDeriv (Sum.inr 1) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) + fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2))),
        lcp 0 (jetDeriv (Sum.inr 2) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) + fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1))),
        lcp 0 (jetDeriv (Sum.inr 2) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) + fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2))),
        lcn 0 (jetDeriv (Sum.inr 1) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) - fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1))),
        lcn 0 (jetDeriv (Sum.inr 1) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) - fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2))),
        lcn 0 (jetDeriv (Sum.inr 2) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) - fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1))),
        lcn 0 (jetDeriv (Sum.inr 2) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) - fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)))} := by
  set PX := fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) -
    fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) with hPX
  set PY := fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) -
    fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) with hPY
  set MX := fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) +
    fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) with hMX
  set MY := fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) +
    fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) with hMY
  set T := fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) with hT
  set L := fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) with hL
  obtain ⟨hPXw, hPYw, hMXw, hMYw, hTw, hLw⟩ :
      PX ∈ boostWeightSubmodule 0 2 ∧ PY ∈ boostWeightSubmodule 0 2 ∧
      MX ∈ boostWeightSubmodule 0 (-2) ∧ MY ∈ boostWeightSubmodule 0 (-2) ∧
      T ∈ boostWeightSubmodule 0 0 ∧ L ∈ boostWeightSubmodule 0 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro t ht
    all_goals
      have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
      simp only [hPX, hPY, hMX, hMY, hT, hL, map_sub, map_add, boostAxis_zero,
        repLorentzGroup_fieldStrengthDeriv_nil, algebraMap_real_complex,
        toLorentzGroup_boostXel, Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three,
        boostMatX, fieldStrengthDeriv_self, mul_zero, zero_mul, mul_one, Complex.ofReal_zero,
        zero_smul, smul_zero, add_zero, zero_add]
      try rw [show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) =
        -fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) from
        fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 0)]
      push_cast
      match_scalars <;> (field_simp; try ring)
  -- ### B. Every field strength is a combination of the eigenvectors
  -- On the light-cone pairs this is `F_{0x} = ((F_{0x} - F_{zx}) + (F_{0x} + F_{zx}))/2` and its
  -- partners; the remaining components are zero, `±F_{xy}`, or `±F_{0z}` by antisymmetry.
  set A := Submodule.span ℂ {PX, PY} with hA
  set B := Submodule.span ℂ {T, L} with hB
  set C := Submodule.span ℂ {MX, MY} with hC
  set V := Submodule.span ℂ {x | ∃ μ ν, x = fieldStrengthDeriv {} μ ν} with hV
  have hAle : A ≤ boostWeightSubmodule 0 2 := by
    rw [hA]; exact Submodule.span_le.2 (by rintro x (rfl | rfl); exacts [hPXw, hPYw])
  have hBle : B ≤ boostWeightSubmodule 0 0 := by
    rw [hB]; exact Submodule.span_le.2 (by rintro x (rfl | rfl); exacts [hTw, hLw])
  have hCle : C ≤ boostWeightSubmodule 0 (-2) := by
    rw [hC]; exact Submodule.span_le.2 (by rintro x (rfl | rfl); exacts [hMXw, hMYw])
  have hAV : A ≤ A ⊔ B ⊔ C := le_sup_left.trans le_sup_left
  have hBV : B ≤ A ⊔ B ⊔ C := le_sup_right.trans le_sup_left
  have hCV : C ≤ A ⊔ B ⊔ C := le_sup_right
  have hPXV : PX ∈ A ⊔ B ⊔ C := hAV (Submodule.subset_span (Set.mem_insert _ _))
  have hPYV : PY ∈ A ⊔ B ⊔ C := hAV (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  have hTV : T ∈ A ⊔ B ⊔ C := hBV (Submodule.subset_span (Set.mem_insert _ _))
  have hLV : L ∈ A ⊔ B ⊔ C := hBV (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  have hMXV : MX ∈ A ⊔ B ⊔ C := hCV (Submodule.subset_span (Set.mem_insert _ _))
  have hMYV : MY ∈ A ⊔ B ⊔ C := hCV (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  have key : ∀ {u v x : JetAlgebra} (c d : ℂ), u ∈ A ⊔ B ⊔ C → v ∈ A ⊔ B ⊔ C →
      x = c • u + d • v → x ∈ A ⊔ B ⊔ C := by
    rintro u v x c d hu hv rfl
    exact add_mem (Submodule.smul_mem _ c hu) (Submodule.smul_mem _ d hv)
  have keyn : ∀ {u v : JetAlgebra} (c d : ℂ) {μ ν : Fin 1 ⊕ Fin 3}, u ∈ A ⊔ B ⊔ C →
      v ∈ A ⊔ B ⊔ C → fieldStrengthDeriv {} μ ν = c • u + d • v →
      fieldStrengthDeriv {} ν μ ∈ A ⊔ B ⊔ C := by
    intro u v c d μ ν hu hv h
    rw [fieldStrengthDeriv_antisymm, h]
    exact neg_mem (add_mem (Submodule.smul_mem _ c hu) (Submodule.smul_mem _ d hv))
  have hVle : V ≤ A ⊔ B ⊔ C := by
    rw [hV]
    refine Submodule.span_le.2 ?_
    rintro x ⟨μ, ν, rfl⟩
    match μ, ν with
    | Sum.inl 0, Sum.inl 0 | Sum.inr 1, Sum.inr 1 | Sum.inr 2, Sum.inr 2
    | Sum.inr 0, Sum.inr 0 => rw [fieldStrengthDeriv_self]; exact zero_mem _
    | Sum.inl 0, Sum.inr 1 => exact key 2⁻¹ 2⁻¹ hPXV hMXV (by rw [hPX, hMX]; module)
    | Sum.inr 1, Sum.inl 0 => exact keyn 2⁻¹ 2⁻¹ hPXV hMXV (by rw [hPX, hMX]; module)
    | Sum.inl 0, Sum.inr 2 => exact key 2⁻¹ 2⁻¹ hPYV hMYV (by rw [hPY, hMY]; module)
    | Sum.inr 2, Sum.inl 0 => exact keyn 2⁻¹ 2⁻¹ hPYV hMYV (by rw [hPY, hMY]; module)
    | Sum.inr 0, Sum.inr 1 => exact key (-2⁻¹) 2⁻¹ hPXV hMXV (by rw [hPX, hMX]; module)
    | Sum.inr 1, Sum.inr 0 => exact keyn (-2⁻¹) 2⁻¹ hPXV hMXV (by rw [hPX, hMX]; module)
    | Sum.inr 0, Sum.inr 2 => exact key (-2⁻¹) 2⁻¹ hPYV hMYV (by rw [hPY, hMY]; module)
    | Sum.inr 2, Sum.inr 0 => exact keyn (-2⁻¹) 2⁻¹ hPYV hMYV (by rw [hPY, hMY]; module)
    | Sum.inr 1, Sum.inr 2 => exact hTV
    | Sum.inr 2, Sum.inr 1 => rw [fieldStrengthDeriv_antisymm]; exact neg_mem hTV
    | Sum.inl 0, Sum.inr 0 => exact hLV
    | Sum.inr 0, Sum.inl 0 => rw [fieldStrengthDeriv_antisymm]; exact neg_mem hLV
  set FF : Set JetAlgebra := {x | ∃ ρ τ μ ν, x = fieldStrengthDeriv {ρ, τ} μ ν} with hFF
  set S : Set JetAlgebra :=
    {lcp 0 (lcn 0 T),
      lcp 0 (lcn 0 L),
      (jetDeriv (Sum.inr 1)) ((jetDeriv (Sum.inr 1)) T),
      (jetDeriv (Sum.inr 1)) ((jetDeriv (Sum.inr 1)) L),
      (jetDeriv (Sum.inr 1)) ((jetDeriv (Sum.inr 2)) T),
      (jetDeriv (Sum.inr 1)) ((jetDeriv (Sum.inr 2)) L),
      (jetDeriv (Sum.inr 2)) ((jetDeriv (Sum.inr 2)) T),
      (jetDeriv (Sum.inr 2)) ((jetDeriv (Sum.inr 2)) L),
      lcp 0 ((jetDeriv (Sum.inr 1)) MX),
      lcp 0 ((jetDeriv (Sum.inr 1)) MY),
      lcp 0 ((jetDeriv (Sum.inr 2)) MX),
      lcp 0 ((jetDeriv (Sum.inr 2)) MY),
      lcn 0 ((jetDeriv (Sum.inr 1)) PX),
      lcn 0 ((jetDeriv (Sum.inr 1)) PY),
      lcn 0 ((jetDeriv (Sum.inr 2)) PX),
      lcn 0 ((jetDeriv (Sum.inr 2)) PY)} with hS
  set W := Submodule.span ℂ S ⊔ ⨆ (j : ℤ) (_ : j ≠ 0), boostWeightSubmodule 0 j with hW
  -- the three weight spaces are bosonic
  have hFb : ∀ μ ν, fieldStrengthDeriv {} μ ν ∈ bosonic := fun μ ν =>
    fieldStrengthDeriv_mem_bosonic _ _ _
  have hAb : A ≤ bosonic := by
    rw [hA]
    refine Submodule.span_le.2 ?_
    rintro x (rfl | rfl)
    · rw [hPX]; exact sub_mem (hFb _ _) (hFb _ _)
    · rw [hPY]; exact sub_mem (hFb _ _) (hFb _ _)
  have hBb : B ≤ bosonic := by
    rw [hB]
    refine Submodule.span_le.2 ?_
    rintro x (rfl | rfl)
    · rw [hT]; exact hFb _ _
    · rw [hL]; exact hFb _ _
  have hCb : C ≤ bosonic := by
    rw [hC]
    refine Submodule.span_le.2 ?_
    rintro x (rfl | rfl)
    · rw [hMX]; exact add_mem (hFb _ _) (hFb _ _)
    · rw [hMY]; exact add_mem (hFb _ _) (hFb _ _)
  have hN : ∀ {j : ℤ} {P : Submodule ℂ JetAlgebra}, j ≠ 0 →
      P ≤ boostWeightSubmodule 0 j → P ≤ W := fun hj hP =>
    le_trans hP (le_sup_of_le_right (le_iSup_of_le _ (le_iSup_of_le hj le_rfl)))
  have bpA : Submodule.map (lcp 0) A ≤ bosonic := map_lcp_le_bosonic hAb
  have wpA : Submodule.map (lcp 0) A ≤
      boostWeightSubmodule 0 (2 + 2) := map_lcp_le hAb hAle
  have bpB : Submodule.map (lcp 0) B ≤ bosonic := map_lcp_le_bosonic hBb
  have wpB : Submodule.map (lcp 0) B ≤
      boostWeightSubmodule 0 (0 + 2) := map_lcp_le hBb hBle
  have bpC : Submodule.map (lcp 0) C ≤ bosonic := map_lcp_le_bosonic hCb
  have wpC : Submodule.map (lcp 0) C ≤
      boostWeightSubmodule 0 (-2 + 2) := map_lcp_le hCb hCle
  have bmA : Submodule.map (lcn 0) A ≤ bosonic := map_lcn_le_bosonic hAb
  have wmA : Submodule.map (lcn 0) A ≤
      boostWeightSubmodule 0 (2 - 2) := map_lcn_le hAb hAle
  have bmB : Submodule.map (lcn 0) B ≤ bosonic := map_lcn_le_bosonic hBb
  have wmB : Submodule.map (lcn 0) B ≤
      boostWeightSubmodule 0 (0 - 2) := map_lcn_le hBb hBle
  have bmC : Submodule.map (lcn 0) C ≤ bosonic := map_lcn_le_bosonic hCb
  have wmC : Submodule.map (lcn 0) C ≤
      boostWeightSubmodule 0 (-2 - 2) := map_lcn_le hCb hCle
  have bxA : Submodule.map (jetDeriv (Sum.inr 1)) A ≤ bosonic := map_jetDeriv_le_bosonic (Sum.inr 1) hAb
  have wxA : Submodule.map (jetDeriv (Sum.inr 1)) A ≤
      boostWeightSubmodule 0 (2) := map_jetDeriv_transverse_le (by decide) hAb hAle
  have bxB : Submodule.map (jetDeriv (Sum.inr 1)) B ≤ bosonic := map_jetDeriv_le_bosonic (Sum.inr 1) hBb
  have wxB : Submodule.map (jetDeriv (Sum.inr 1)) B ≤
      boostWeightSubmodule 0 (0) := map_jetDeriv_transverse_le (by decide) hBb hBle
  have bxC : Submodule.map (jetDeriv (Sum.inr 1)) C ≤ bosonic := map_jetDeriv_le_bosonic (Sum.inr 1) hCb
  have wxC : Submodule.map (jetDeriv (Sum.inr 1)) C ≤
      boostWeightSubmodule 0 (-2) := map_jetDeriv_transverse_le (by decide) hCb hCle
  have byA : Submodule.map (jetDeriv (Sum.inr 2)) A ≤ bosonic := map_jetDeriv_le_bosonic (Sum.inr 2) hAb
  have wyA : Submodule.map (jetDeriv (Sum.inr 2)) A ≤
      boostWeightSubmodule 0 (2) := map_jetDeriv_transverse_le (by decide) hAb hAle
  have byB : Submodule.map (jetDeriv (Sum.inr 2)) B ≤ bosonic := map_jetDeriv_le_bosonic (Sum.inr 2) hBb
  have wyB : Submodule.map (jetDeriv (Sum.inr 2)) B ≤
      boostWeightSubmodule 0 (0) := map_jetDeriv_transverse_le (by decide) hBb hBle
  have byC : Submodule.map (jetDeriv (Sum.inr 2)) C ≤ bosonic := map_jetDeriv_le_bosonic (Sum.inr 2) hCb
  have wyC : Submodule.map (jetDeriv (Sum.inr 2)) C ≤
      boostWeightSubmodule 0 (-2) := map_jetDeriv_transverse_le (by decide) hCb hCle
  have eppA : Submodule.map (lcp 0) (Submodule.map (lcp 0) A) ≤ W :=
    hN (by norm_num) (map_lcp_le bpA wpA)
  have eppB : Submodule.map (lcp 0) (Submodule.map (lcp 0) B) ≤ W :=
    hN (by norm_num) (map_lcp_le bpB wpB)
  have eppC : Submodule.map (lcp 0) (Submodule.map (lcp 0) C) ≤ W :=
    hN (by norm_num) (map_lcp_le bpC wpC)
  have epmA : Submodule.map (lcp 0) (Submodule.map (lcn 0) A) ≤ W :=
    hN (by norm_num) (map_lcp_le bmA wmA)
  have epmB : Submodule.map (lcp 0) (Submodule.map (lcn 0) B) ≤ W := by
    simp only [hB, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have epmC : Submodule.map (lcp 0) (Submodule.map (lcn 0) C) ≤ W :=
    hN (by norm_num) (map_lcp_le bmC wmC)
  have epxA : Submodule.map (lcp 0) (Submodule.map (jetDeriv (Sum.inr 1)) A) ≤ W :=
    hN (by norm_num) (map_lcp_le bxA wxA)
  have epxB : Submodule.map (lcp 0) (Submodule.map (jetDeriv (Sum.inr 1)) B) ≤ W :=
    hN (by norm_num) (map_lcp_le bxB wxB)
  have epxC : Submodule.map (lcp 0) (Submodule.map (jetDeriv (Sum.inr 1)) C) ≤ W := by
    simp only [hC, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have epyA : Submodule.map (lcp 0) (Submodule.map (jetDeriv (Sum.inr 2)) A) ≤ W :=
    hN (by norm_num) (map_lcp_le byA wyA)
  have epyB : Submodule.map (lcp 0) (Submodule.map (jetDeriv (Sum.inr 2)) B) ≤ W :=
    hN (by norm_num) (map_lcp_le byB wyB)
  have epyC : Submodule.map (lcp 0) (Submodule.map (jetDeriv (Sum.inr 2)) C) ≤ W := by
    simp only [hC, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have empA : Submodule.map (lcn 0) (Submodule.map (lcp 0) A) ≤ W :=
    hN (by norm_num) (map_lcn_le bpA wpA)
  have empB : Submodule.map (lcn 0) (Submodule.map (lcp 0) B) ≤ W := by
    simp only [hB, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> rw [lcn_lcp_comm] <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have empC : Submodule.map (lcn 0) (Submodule.map (lcp 0) C) ≤ W :=
    hN (by norm_num) (map_lcn_le bpC wpC)
  have emmA : Submodule.map (lcn 0) (Submodule.map (lcn 0) A) ≤ W :=
    hN (by norm_num) (map_lcn_le bmA wmA)
  have emmB : Submodule.map (lcn 0) (Submodule.map (lcn 0) B) ≤ W :=
    hN (by norm_num) (map_lcn_le bmB wmB)
  have emmC : Submodule.map (lcn 0) (Submodule.map (lcn 0) C) ≤ W :=
    hN (by norm_num) (map_lcn_le bmC wmC)
  have emxA : Submodule.map (lcn 0) (Submodule.map (jetDeriv (Sum.inr 1)) A) ≤ W := by
    simp only [hA, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have emxB : Submodule.map (lcn 0) (Submodule.map (jetDeriv (Sum.inr 1)) B) ≤ W :=
    hN (by norm_num) (map_lcn_le bxB wxB)
  have emxC : Submodule.map (lcn 0) (Submodule.map (jetDeriv (Sum.inr 1)) C) ≤ W :=
    hN (by norm_num) (map_lcn_le bxC wxC)
  have emyA : Submodule.map (lcn 0) (Submodule.map (jetDeriv (Sum.inr 2)) A) ≤ W := by
    simp only [hA, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have emyB : Submodule.map (lcn 0) (Submodule.map (jetDeriv (Sum.inr 2)) B) ≤ W :=
    hN (by norm_num) (map_lcn_le byB wyB)
  have emyC : Submodule.map (lcn 0) (Submodule.map (jetDeriv (Sum.inr 2)) C) ≤ W :=
    hN (by norm_num) (map_lcn_le byC wyC)
  have expA : Submodule.map (jetDeriv (Sum.inr 1)) (Submodule.map (lcp 0) A) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bpA wpA)
  have expB : Submodule.map (jetDeriv (Sum.inr 1)) (Submodule.map (lcp 0) B) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bpB wpB)
  have expC : Submodule.map (jetDeriv (Sum.inr 1)) (Submodule.map (lcp 0) C) ≤ W := by
    simp only [hC, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> rw [← lcp_jetDeriv_comm] <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have exmA : Submodule.map (jetDeriv (Sum.inr 1)) (Submodule.map (lcn 0) A) ≤ W := by
    simp only [hA, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> rw [← lcn_jetDeriv_comm] <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have exmB : Submodule.map (jetDeriv (Sum.inr 1)) (Submodule.map (lcn 0) B) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bmB wmB)
  have exmC : Submodule.map (jetDeriv (Sum.inr 1)) (Submodule.map (lcn 0) C) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bmC wmC)
  have exxA : Submodule.map (jetDeriv (Sum.inr 1)) (Submodule.map (jetDeriv (Sum.inr 1)) A) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bxA wxA)
  have exxB : Submodule.map (jetDeriv (Sum.inr 1)) (Submodule.map (jetDeriv (Sum.inr 1)) B) ≤ W := by
    simp only [hB, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have exxC : Submodule.map (jetDeriv (Sum.inr 1)) (Submodule.map (jetDeriv (Sum.inr 1)) C) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bxC wxC)
  have exyA : Submodule.map (jetDeriv (Sum.inr 1)) (Submodule.map (jetDeriv (Sum.inr 2)) A) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) byA wyA)
  have exyB : Submodule.map (jetDeriv (Sum.inr 1)) (Submodule.map (jetDeriv (Sum.inr 2)) B) ≤ W := by
    simp only [hB, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have exyC : Submodule.map (jetDeriv (Sum.inr 1)) (Submodule.map (jetDeriv (Sum.inr 2)) C) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) byC wyC)
  have eypA : Submodule.map (jetDeriv (Sum.inr 2)) (Submodule.map (lcp 0) A) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bpA wpA)
  have eypB : Submodule.map (jetDeriv (Sum.inr 2)) (Submodule.map (lcp 0) B) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bpB wpB)
  have eypC : Submodule.map (jetDeriv (Sum.inr 2)) (Submodule.map (lcp 0) C) ≤ W := by
    simp only [hC, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> rw [← lcp_jetDeriv_comm] <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have eymA : Submodule.map (jetDeriv (Sum.inr 2)) (Submodule.map (lcn 0) A) ≤ W := by
    simp only [hA, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> rw [← lcn_jetDeriv_comm] <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have eymB : Submodule.map (jetDeriv (Sum.inr 2)) (Submodule.map (lcn 0) B) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bmB wmB)
  have eymC : Submodule.map (jetDeriv (Sum.inr 2)) (Submodule.map (lcn 0) C) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bmC wmC)
  have eyxA : Submodule.map (jetDeriv (Sum.inr 2)) (Submodule.map (jetDeriv (Sum.inr 1)) A) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bxA wxA)
  have eyxB : Submodule.map (jetDeriv (Sum.inr 2)) (Submodule.map (jetDeriv (Sum.inr 1)) B) ≤ W := by
    simp only [hB, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> rw [jetDeriv_comm (Sum.inr 2) (Sum.inr 1)] <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have eyxC : Submodule.map (jetDeriv (Sum.inr 2)) (Submodule.map (jetDeriv (Sum.inr 1)) C) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bxC wxC)
  have eyyA : Submodule.map (jetDeriv (Sum.inr 2)) (Submodule.map (jetDeriv (Sum.inr 2)) A) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) byA wyA)
  have eyyB : Submodule.map (jetDeriv (Sum.inr 2)) (Submodule.map (jetDeriv (Sum.inr 2)) B) ≤ W := by
    simp only [hB, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have eyyC : Submodule.map (jetDeriv (Sum.inr 2)) (Submodule.map (jetDeriv (Sum.inr 2)) C) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) byC wyC)
  -- every monomial is a second light-cone derivative of a field strength
  have hFFle : Submodule.span ℂ FF ≤ stepAxis 0 1 2 (stepAxis 0 1 2 V) := by
    rw [hFF]
    refine Submodule.span_le.2 ?_
    rintro x ⟨ρ, τ, μ, ν, rfl⟩
    rw [fieldStrengthDeriv_pair_eq_jetDeriv]
    exact jetDeriv_mem_stepAxis (by decide) (by decide) (by decide)
      (jetDeriv_mem_stepAxis (by decide) (by decide) (by decide)
        (by rw [hV]; exact Submodule.subset_span ⟨μ, ν, rfl⟩) τ) ρ
  have hmap4 : ∀ (f : JetAlgebra →ₗ[ℂ] JetAlgebra) (P Q R T : Submodule ℂ JetAlgebra),
      Submodule.map f P ≤ W → Submodule.map f Q ≤ W → Submodule.map f R ≤ W →
      Submodule.map f T ≤ W → Submodule.map f (P ⊔ Q ⊔ R ⊔ T) ≤ W := by
    intro f P Q R T h1 h2 h3 h4
    simp only [Submodule.map_sup]
    exact sup_le (sup_le (sup_le h1 h2) h3) h4
  have hin3 : ∀ (f g : JetAlgebra →ₗ[ℂ] JetAlgebra),
      Submodule.map f (Submodule.map g A) ≤ W → Submodule.map f (Submodule.map g B) ≤ W →
      Submodule.map f (Submodule.map g C) ≤ W →
      Submodule.map f (Submodule.map g (A ⊔ B ⊔ C)) ≤ W := by
    intro f g h1 h2 h3
    simp only [Submodule.map_sup]
    exact sup_le (sup_le h1 h2) h3
  have hfin : stepAxis 0 1 2 (stepAxis 0 1 2 (A ⊔ B ⊔ C)) ≤ W := by
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · exact hmap4 _ _ _ _ _ (hin3 _ _ eppA eppB eppC) (hin3 _ _ epmA epmB epmC)
        (hin3 _ _ epxA epxB epxC) (hin3 _ _ epyA epyB epyC)
    · exact hmap4 _ _ _ _ _ (hin3 _ _ empA empB empC) (hin3 _ _ emmA emmB emmC)
        (hin3 _ _ emxA emxB emxC) (hin3 _ _ emyA emyB emyC)
    · exact hmap4 _ _ _ _ _ (hin3 _ _ expA expB expC) (hin3 _ _ exmA exmB exmC)
        (hin3 _ _ exxA exxB exxC) (hin3 _ _ exyA exyB exyC)
    · exact hmap4 _ _ _ _ _ (hin3 _ _ eypA eypB eypC) (hin3 _ _ eymA eymB eymC)
        (hin3 _ _ eyxA eyxB eyxC) (hin3 _ _ eyyA eyyB eyyC)
  have hkey : Submodule.span ℂ FF ≤ W :=
    le_trans hFFle (le_trans (stepAxis_mono (stepAxis_mono hVle)) hfin)
  -- the sixteen generators have weight zero
  have hwz : ∀ {j : ℤ} {y : JetAlgebra}, j = 0 → y ∈ boostWeightSubmodule 0 j →
      y ∈ boostWeightSubmodule 0 0 := by rintro j y rfl h; exact h
  have hTb : T ∈ bosonic := by rw [hT]; exact hFb _ _
  have hLb : L ∈ bosonic := by rw [hL]; exact hFb _ _
  have hPXb : PX ∈ bosonic := by rw [hPX]; exact sub_mem (hFb _ _) (hFb _ _)
  have hPYb : PY ∈ bosonic := by rw [hPY]; exact sub_mem (hFb _ _) (hFb _ _)
  have hMXb : MX ∈ bosonic := by rw [hMX]; exact add_mem (hFb _ _) (hFb _ _)
  have hMYb : MY ∈ bosonic := by rw [hMY]; exact add_mem (hFb _ _) (hFb _ _)
  have hSw : Submodule.span ℂ S ≤ boostWeightSubmodule 0 0 := by
    rw [hS]
    refine Submodule.span_le.2 ?_
    rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl)
    exacts [
    hwz (by norm_num) (lcp_mem_boostWeight (lcn_mem_bosonic hTb)
      (lcn_mem_boostWeight hTb hTw)),
    hwz (by norm_num) (lcp_mem_boostWeight (lcn_mem_bosonic hLb)
      (lcn_mem_boostWeight hLb hLw)),
    jetDeriv_transverse_mem (by decide) (jetDeriv_mem_bosonic (Sum.inr 1) hTb) (jetDeriv_transverse_mem (by decide) hTb hTw),
    jetDeriv_transverse_mem (by decide) (jetDeriv_mem_bosonic (Sum.inr 1) hLb) (jetDeriv_transverse_mem (by decide) hLb hLw),
    jetDeriv_transverse_mem (by decide) (jetDeriv_mem_bosonic (Sum.inr 2) hTb) (jetDeriv_transverse_mem (by decide) hTb hTw),
    jetDeriv_transverse_mem (by decide) (jetDeriv_mem_bosonic (Sum.inr 2) hLb) (jetDeriv_transverse_mem (by decide) hLb hLw),
    jetDeriv_transverse_mem (by decide) (jetDeriv_mem_bosonic (Sum.inr 2) hTb) (jetDeriv_transverse_mem (by decide) hTb hTw),
    jetDeriv_transverse_mem (by decide) (jetDeriv_mem_bosonic (Sum.inr 2) hLb) (jetDeriv_transverse_mem (by decide) hLb hLw),
    hwz (by norm_num) (lcp_mem_boostWeight (jetDeriv_mem_bosonic (Sum.inr 1) hMXb) (jetDeriv_transverse_mem (by decide) hMXb hMXw)),
    hwz (by norm_num) (lcp_mem_boostWeight (jetDeriv_mem_bosonic (Sum.inr 1) hMYb) (jetDeriv_transverse_mem (by decide) hMYb hMYw)),
    hwz (by norm_num) (lcp_mem_boostWeight (jetDeriv_mem_bosonic (Sum.inr 2) hMXb) (jetDeriv_transverse_mem (by decide) hMXb hMXw)),
    hwz (by norm_num) (lcp_mem_boostWeight (jetDeriv_mem_bosonic (Sum.inr 2) hMYb) (jetDeriv_transverse_mem (by decide) hMYb hMYw)),
    hwz (by norm_num) (lcn_mem_boostWeight (jetDeriv_mem_bosonic (Sum.inr 1) hPXb) (jetDeriv_transverse_mem (by decide) hPXb hPXw)),
    hwz (by norm_num) (lcn_mem_boostWeight (jetDeriv_mem_bosonic (Sum.inr 1) hPYb) (jetDeriv_transverse_mem (by decide) hPYb hPYw)),
    hwz (by norm_num) (lcn_mem_boostWeight (jetDeriv_mem_bosonic (Sum.inr 2) hPXb) (jetDeriv_transverse_mem (by decide) hPXb hPXw)),
    hwz (by norm_num) (lcn_mem_boostWeight (jetDeriv_mem_bosonic (Sum.inr 2) hPYb) (jetDeriv_transverse_mem (by decide) hPYb hPYw))]
  refine le_trans (inf_le_inf_left _ hkey) ?_
  rw [hW, inf_comm, sup_inf_assoc_of_le _ hSw,
    disjoint_iff.mp (boostWeightSubmodule_iSupIndep (i := 0) 0).symm, sup_bot_eq]
/-!

## H. The boost weight zero part, `y`-direction

-/

/-- **The boost weight zero part of the second derivatives of the field strength.** An element
  of the span of the monomials `∂_ρ ∂_τ F_{μν}` of `y`-boost weight zero is a combination of the
  sixteen listed second derivatives: the derivative pair and the field strength each carry a
  weight, and the two must cancel. Only this inclusion feeds the three-axis theorem, so the
  converse is not recorded. -/
lemma boostWeight_inter_fieldStrengthDeriv_pair_y_le :
    boostWeightSubmodule 1 0 ⊓ Submodule.span ℂ
        {x | ∃ ρ τ μ ν, x = fieldStrengthDeriv {ρ, τ} μ ν} ≤
      Submodule.span ℂ
        {lcp 1 (lcn 1 (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0))),
        lcp 1 (lcn 1 (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1))),
        jetDeriv (Sum.inr 2) (jetDeriv (Sum.inr 2) (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0))),
        jetDeriv (Sum.inr 2) (jetDeriv (Sum.inr 2) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1))),
        jetDeriv (Sum.inr 2) (jetDeriv (Sum.inr 0) (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0))),
        jetDeriv (Sum.inr 2) (jetDeriv (Sum.inr 0) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1))),
        jetDeriv (Sum.inr 0) (jetDeriv (Sum.inr 0) (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0))),
        jetDeriv (Sum.inr 0) (jetDeriv (Sum.inr 0) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1))),
        lcp 1 (jetDeriv (Sum.inr 2) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) + fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2))),
        lcp 1 (jetDeriv (Sum.inr 2) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) + fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0))),
        lcp 1 (jetDeriv (Sum.inr 0) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) + fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2))),
        lcp 1 (jetDeriv (Sum.inr 0) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) + fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0))),
        lcn 1 (jetDeriv (Sum.inr 2) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) - fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2))),
        lcn 1 (jetDeriv (Sum.inr 2) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) - fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0))),
        lcn 1 (jetDeriv (Sum.inr 0) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) - fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2))),
        lcn 1 (jetDeriv (Sum.inr 0) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) - fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0)))} := by
  set PX := fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) -
    fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) with hPX
  set PY := fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) -
    fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) with hPY
  set MX := fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) +
    fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) with hMX
  set MY := fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) +
    fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) with hMY
  set T := fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) with hT
  set L := fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) with hL
  obtain ⟨hPXw, hPYw, hMXw, hMYw, hTw, hLw⟩ :
      PX ∈ boostWeightSubmodule 1 2 ∧ PY ∈ boostWeightSubmodule 1 2 ∧
      MX ∈ boostWeightSubmodule 1 (-2) ∧ MY ∈ boostWeightSubmodule 1 (-2) ∧
      T ∈ boostWeightSubmodule 1 0 ∧ L ∈ boostWeightSubmodule 1 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro t ht
    all_goals
      have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
      simp only [hPX, hPY, hMX, hMY, hT, hL, map_sub, map_add, boostAxis_one,
        repLorentzGroup_fieldStrengthDeriv_nil, algebraMap_real_complex,
        toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three,
        boostMatY, fieldStrengthDeriv_self, mul_zero, zero_mul, mul_one, Complex.ofReal_zero,
        zero_smul, smul_zero, add_zero, zero_add]
      try rw [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) =
        -fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) from
        fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 1)]
      push_cast
      match_scalars <;> (field_simp; try ring)
  -- ### B. Every field strength is a combination of the eigenvectors
  -- On the light-cone pairs this is `F_{0x} = ((F_{0x} - F_{zx}) + (F_{0x} + F_{zx}))/2` and its
  -- partners; the remaining components are zero, `±F_{xy}`, or `±F_{0z}` by antisymmetry.
  set A := Submodule.span ℂ {PX, PY} with hA
  set B := Submodule.span ℂ {T, L} with hB
  set C := Submodule.span ℂ {MX, MY} with hC
  set V := Submodule.span ℂ {x | ∃ μ ν, x = fieldStrengthDeriv {} μ ν} with hV
  have hAle : A ≤ boostWeightSubmodule 1 2 := by
    rw [hA]; exact Submodule.span_le.2 (by rintro x (rfl | rfl); exacts [hPXw, hPYw])
  have hBle : B ≤ boostWeightSubmodule 1 0 := by
    rw [hB]; exact Submodule.span_le.2 (by rintro x (rfl | rfl); exacts [hTw, hLw])
  have hCle : C ≤ boostWeightSubmodule 1 (-2) := by
    rw [hC]; exact Submodule.span_le.2 (by rintro x (rfl | rfl); exacts [hMXw, hMYw])
  have hAV : A ≤ A ⊔ B ⊔ C := le_sup_left.trans le_sup_left
  have hBV : B ≤ A ⊔ B ⊔ C := le_sup_right.trans le_sup_left
  have hCV : C ≤ A ⊔ B ⊔ C := le_sup_right
  have hPXV : PX ∈ A ⊔ B ⊔ C := hAV (Submodule.subset_span (Set.mem_insert _ _))
  have hPYV : PY ∈ A ⊔ B ⊔ C := hAV (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  have hTV : T ∈ A ⊔ B ⊔ C := hBV (Submodule.subset_span (Set.mem_insert _ _))
  have hLV : L ∈ A ⊔ B ⊔ C := hBV (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  have hMXV : MX ∈ A ⊔ B ⊔ C := hCV (Submodule.subset_span (Set.mem_insert _ _))
  have hMYV : MY ∈ A ⊔ B ⊔ C := hCV (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  have key : ∀ {u v x : JetAlgebra} (c d : ℂ), u ∈ A ⊔ B ⊔ C → v ∈ A ⊔ B ⊔ C →
      x = c • u + d • v → x ∈ A ⊔ B ⊔ C := by
    rintro u v x c d hu hv rfl
    exact add_mem (Submodule.smul_mem _ c hu) (Submodule.smul_mem _ d hv)
  have keyn : ∀ {u v : JetAlgebra} (c d : ℂ) {μ ν : Fin 1 ⊕ Fin 3}, u ∈ A ⊔ B ⊔ C →
      v ∈ A ⊔ B ⊔ C → fieldStrengthDeriv {} μ ν = c • u + d • v →
      fieldStrengthDeriv {} ν μ ∈ A ⊔ B ⊔ C := by
    intro u v c d μ ν hu hv h
    rw [fieldStrengthDeriv_antisymm, h]
    exact neg_mem (add_mem (Submodule.smul_mem _ c hu) (Submodule.smul_mem _ d hv))
  have hVle : V ≤ A ⊔ B ⊔ C := by
    rw [hV]
    refine Submodule.span_le.2 ?_
    rintro x ⟨μ, ν, rfl⟩
    match μ, ν with
    | Sum.inl 0, Sum.inl 0 | Sum.inr 2, Sum.inr 2 | Sum.inr 0, Sum.inr 0
    | Sum.inr 1, Sum.inr 1 => rw [fieldStrengthDeriv_self]; exact zero_mem _
    | Sum.inl 0, Sum.inr 2 => exact key 2⁻¹ 2⁻¹ hPXV hMXV (by rw [hPX, hMX]; module)
    | Sum.inr 2, Sum.inl 0 => exact keyn 2⁻¹ 2⁻¹ hPXV hMXV (by rw [hPX, hMX]; module)
    | Sum.inl 0, Sum.inr 0 => exact key 2⁻¹ 2⁻¹ hPYV hMYV (by rw [hPY, hMY]; module)
    | Sum.inr 0, Sum.inl 0 => exact keyn 2⁻¹ 2⁻¹ hPYV hMYV (by rw [hPY, hMY]; module)
    | Sum.inr 1, Sum.inr 2 => exact key (-2⁻¹) 2⁻¹ hPXV hMXV (by rw [hPX, hMX]; module)
    | Sum.inr 2, Sum.inr 1 => exact keyn (-2⁻¹) 2⁻¹ hPXV hMXV (by rw [hPX, hMX]; module)
    | Sum.inr 1, Sum.inr 0 => exact key (-2⁻¹) 2⁻¹ hPYV hMYV (by rw [hPY, hMY]; module)
    | Sum.inr 0, Sum.inr 1 => exact keyn (-2⁻¹) 2⁻¹ hPYV hMYV (by rw [hPY, hMY]; module)
    | Sum.inr 2, Sum.inr 0 => exact hTV
    | Sum.inr 0, Sum.inr 2 => rw [fieldStrengthDeriv_antisymm]; exact neg_mem hTV
    | Sum.inl 0, Sum.inr 1 => exact hLV
    | Sum.inr 1, Sum.inl 0 => rw [fieldStrengthDeriv_antisymm]; exact neg_mem hLV
  set FF : Set JetAlgebra := {x | ∃ ρ τ μ ν, x = fieldStrengthDeriv {ρ, τ} μ ν} with hFF
  set S : Set JetAlgebra :=
    {lcp 1 (lcn 1 T),
      lcp 1 (lcn 1 L),
      (jetDeriv (Sum.inr 2)) ((jetDeriv (Sum.inr 2)) T),
      (jetDeriv (Sum.inr 2)) ((jetDeriv (Sum.inr 2)) L),
      (jetDeriv (Sum.inr 2)) ((jetDeriv (Sum.inr 0)) T),
      (jetDeriv (Sum.inr 2)) ((jetDeriv (Sum.inr 0)) L),
      (jetDeriv (Sum.inr 0)) ((jetDeriv (Sum.inr 0)) T),
      (jetDeriv (Sum.inr 0)) ((jetDeriv (Sum.inr 0)) L),
      lcp 1 ((jetDeriv (Sum.inr 2)) MX),
      lcp 1 ((jetDeriv (Sum.inr 2)) MY),
      lcp 1 ((jetDeriv (Sum.inr 0)) MX),
      lcp 1 ((jetDeriv (Sum.inr 0)) MY),
      lcn 1 ((jetDeriv (Sum.inr 2)) PX),
      lcn 1 ((jetDeriv (Sum.inr 2)) PY),
      lcn 1 ((jetDeriv (Sum.inr 0)) PX),
      lcn 1 ((jetDeriv (Sum.inr 0)) PY)} with hS
  set W := Submodule.span ℂ S ⊔ ⨆ (j : ℤ) (_ : j ≠ 0), boostWeightSubmodule 1 j with hW
  -- the three weight spaces are bosonic
  have hFb : ∀ μ ν, fieldStrengthDeriv {} μ ν ∈ bosonic := fun μ ν =>
    fieldStrengthDeriv_mem_bosonic _ _ _
  have hAb : A ≤ bosonic := by
    rw [hA]
    refine Submodule.span_le.2 ?_
    rintro x (rfl | rfl)
    · rw [hPX]; exact sub_mem (hFb _ _) (hFb _ _)
    · rw [hPY]; exact sub_mem (hFb _ _) (hFb _ _)
  have hBb : B ≤ bosonic := by
    rw [hB]
    refine Submodule.span_le.2 ?_
    rintro x (rfl | rfl)
    · rw [hT]; exact hFb _ _
    · rw [hL]; exact hFb _ _
  have hCb : C ≤ bosonic := by
    rw [hC]
    refine Submodule.span_le.2 ?_
    rintro x (rfl | rfl)
    · rw [hMX]; exact add_mem (hFb _ _) (hFb _ _)
    · rw [hMY]; exact add_mem (hFb _ _) (hFb _ _)
  have hN : ∀ {j : ℤ} {P : Submodule ℂ JetAlgebra}, j ≠ 0 →
      P ≤ boostWeightSubmodule 1 j → P ≤ W := fun hj hP =>
    le_trans hP (le_sup_of_le_right (le_iSup_of_le _ (le_iSup_of_le hj le_rfl)))
  have bpA : Submodule.map (lcp 1) A ≤ bosonic := map_lcp_le_bosonic hAb
  have wpA : Submodule.map (lcp 1) A ≤
      boostWeightSubmodule 1 (2 + 2) := map_lcp_le hAb hAle
  have bpB : Submodule.map (lcp 1) B ≤ bosonic := map_lcp_le_bosonic hBb
  have wpB : Submodule.map (lcp 1) B ≤
      boostWeightSubmodule 1 (0 + 2) := map_lcp_le hBb hBle
  have bpC : Submodule.map (lcp 1) C ≤ bosonic := map_lcp_le_bosonic hCb
  have wpC : Submodule.map (lcp 1) C ≤
      boostWeightSubmodule 1 (-2 + 2) := map_lcp_le hCb hCle
  have bmA : Submodule.map (lcn 1) A ≤ bosonic := map_lcn_le_bosonic hAb
  have wmA : Submodule.map (lcn 1) A ≤
      boostWeightSubmodule 1 (2 - 2) := map_lcn_le hAb hAle
  have bmB : Submodule.map (lcn 1) B ≤ bosonic := map_lcn_le_bosonic hBb
  have wmB : Submodule.map (lcn 1) B ≤
      boostWeightSubmodule 1 (0 - 2) := map_lcn_le hBb hBle
  have bmC : Submodule.map (lcn 1) C ≤ bosonic := map_lcn_le_bosonic hCb
  have wmC : Submodule.map (lcn 1) C ≤
      boostWeightSubmodule 1 (-2 - 2) := map_lcn_le hCb hCle
  have bxA : Submodule.map (jetDeriv (Sum.inr 2)) A ≤ bosonic := map_jetDeriv_le_bosonic (Sum.inr 2) hAb
  have wxA : Submodule.map (jetDeriv (Sum.inr 2)) A ≤
      boostWeightSubmodule 1 (2) := map_jetDeriv_transverse_le (by decide) hAb hAle
  have bxB : Submodule.map (jetDeriv (Sum.inr 2)) B ≤ bosonic := map_jetDeriv_le_bosonic (Sum.inr 2) hBb
  have wxB : Submodule.map (jetDeriv (Sum.inr 2)) B ≤
      boostWeightSubmodule 1 (0) := map_jetDeriv_transverse_le (by decide) hBb hBle
  have bxC : Submodule.map (jetDeriv (Sum.inr 2)) C ≤ bosonic := map_jetDeriv_le_bosonic (Sum.inr 2) hCb
  have wxC : Submodule.map (jetDeriv (Sum.inr 2)) C ≤
      boostWeightSubmodule 1 (-2) := map_jetDeriv_transverse_le (by decide) hCb hCle
  have byA : Submodule.map (jetDeriv (Sum.inr 0)) A ≤ bosonic := map_jetDeriv_le_bosonic (Sum.inr 0) hAb
  have wyA : Submodule.map (jetDeriv (Sum.inr 0)) A ≤
      boostWeightSubmodule 1 (2) := map_jetDeriv_transverse_le (by decide) hAb hAle
  have byB : Submodule.map (jetDeriv (Sum.inr 0)) B ≤ bosonic := map_jetDeriv_le_bosonic (Sum.inr 0) hBb
  have wyB : Submodule.map (jetDeriv (Sum.inr 0)) B ≤
      boostWeightSubmodule 1 (0) := map_jetDeriv_transverse_le (by decide) hBb hBle
  have byC : Submodule.map (jetDeriv (Sum.inr 0)) C ≤ bosonic := map_jetDeriv_le_bosonic (Sum.inr 0) hCb
  have wyC : Submodule.map (jetDeriv (Sum.inr 0)) C ≤
      boostWeightSubmodule 1 (-2) := map_jetDeriv_transverse_le (by decide) hCb hCle
  have eppA : Submodule.map (lcp 1) (Submodule.map (lcp 1) A) ≤ W :=
    hN (by norm_num) (map_lcp_le bpA wpA)
  have eppB : Submodule.map (lcp 1) (Submodule.map (lcp 1) B) ≤ W :=
    hN (by norm_num) (map_lcp_le bpB wpB)
  have eppC : Submodule.map (lcp 1) (Submodule.map (lcp 1) C) ≤ W :=
    hN (by norm_num) (map_lcp_le bpC wpC)
  have epmA : Submodule.map (lcp 1) (Submodule.map (lcn 1) A) ≤ W :=
    hN (by norm_num) (map_lcp_le bmA wmA)
  have epmB : Submodule.map (lcp 1) (Submodule.map (lcn 1) B) ≤ W := by
    simp only [hB, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have epmC : Submodule.map (lcp 1) (Submodule.map (lcn 1) C) ≤ W :=
    hN (by norm_num) (map_lcp_le bmC wmC)
  have epxA : Submodule.map (lcp 1) (Submodule.map (jetDeriv (Sum.inr 2)) A) ≤ W :=
    hN (by norm_num) (map_lcp_le bxA wxA)
  have epxB : Submodule.map (lcp 1) (Submodule.map (jetDeriv (Sum.inr 2)) B) ≤ W :=
    hN (by norm_num) (map_lcp_le bxB wxB)
  have epxC : Submodule.map (lcp 1) (Submodule.map (jetDeriv (Sum.inr 2)) C) ≤ W := by
    simp only [hC, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have epyA : Submodule.map (lcp 1) (Submodule.map (jetDeriv (Sum.inr 0)) A) ≤ W :=
    hN (by norm_num) (map_lcp_le byA wyA)
  have epyB : Submodule.map (lcp 1) (Submodule.map (jetDeriv (Sum.inr 0)) B) ≤ W :=
    hN (by norm_num) (map_lcp_le byB wyB)
  have epyC : Submodule.map (lcp 1) (Submodule.map (jetDeriv (Sum.inr 0)) C) ≤ W := by
    simp only [hC, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have empA : Submodule.map (lcn 1) (Submodule.map (lcp 1) A) ≤ W :=
    hN (by norm_num) (map_lcn_le bpA wpA)
  have empB : Submodule.map (lcn 1) (Submodule.map (lcp 1) B) ≤ W := by
    simp only [hB, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> rw [lcn_lcp_comm] <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have empC : Submodule.map (lcn 1) (Submodule.map (lcp 1) C) ≤ W :=
    hN (by norm_num) (map_lcn_le bpC wpC)
  have emmA : Submodule.map (lcn 1) (Submodule.map (lcn 1) A) ≤ W :=
    hN (by norm_num) (map_lcn_le bmA wmA)
  have emmB : Submodule.map (lcn 1) (Submodule.map (lcn 1) B) ≤ W :=
    hN (by norm_num) (map_lcn_le bmB wmB)
  have emmC : Submodule.map (lcn 1) (Submodule.map (lcn 1) C) ≤ W :=
    hN (by norm_num) (map_lcn_le bmC wmC)
  have emxA : Submodule.map (lcn 1) (Submodule.map (jetDeriv (Sum.inr 2)) A) ≤ W := by
    simp only [hA, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have emxB : Submodule.map (lcn 1) (Submodule.map (jetDeriv (Sum.inr 2)) B) ≤ W :=
    hN (by norm_num) (map_lcn_le bxB wxB)
  have emxC : Submodule.map (lcn 1) (Submodule.map (jetDeriv (Sum.inr 2)) C) ≤ W :=
    hN (by norm_num) (map_lcn_le bxC wxC)
  have emyA : Submodule.map (lcn 1) (Submodule.map (jetDeriv (Sum.inr 0)) A) ≤ W := by
    simp only [hA, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have emyB : Submodule.map (lcn 1) (Submodule.map (jetDeriv (Sum.inr 0)) B) ≤ W :=
    hN (by norm_num) (map_lcn_le byB wyB)
  have emyC : Submodule.map (lcn 1) (Submodule.map (jetDeriv (Sum.inr 0)) C) ≤ W :=
    hN (by norm_num) (map_lcn_le byC wyC)
  have expA : Submodule.map (jetDeriv (Sum.inr 2)) (Submodule.map (lcp 1) A) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bpA wpA)
  have expB : Submodule.map (jetDeriv (Sum.inr 2)) (Submodule.map (lcp 1) B) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bpB wpB)
  have expC : Submodule.map (jetDeriv (Sum.inr 2)) (Submodule.map (lcp 1) C) ≤ W := by
    simp only [hC, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> rw [← lcp_jetDeriv_comm] <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have exmA : Submodule.map (jetDeriv (Sum.inr 2)) (Submodule.map (lcn 1) A) ≤ W := by
    simp only [hA, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> rw [← lcn_jetDeriv_comm] <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have exmB : Submodule.map (jetDeriv (Sum.inr 2)) (Submodule.map (lcn 1) B) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bmB wmB)
  have exmC : Submodule.map (jetDeriv (Sum.inr 2)) (Submodule.map (lcn 1) C) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bmC wmC)
  have exxA : Submodule.map (jetDeriv (Sum.inr 2)) (Submodule.map (jetDeriv (Sum.inr 2)) A) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bxA wxA)
  have exxB : Submodule.map (jetDeriv (Sum.inr 2)) (Submodule.map (jetDeriv (Sum.inr 2)) B) ≤ W := by
    simp only [hB, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have exxC : Submodule.map (jetDeriv (Sum.inr 2)) (Submodule.map (jetDeriv (Sum.inr 2)) C) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bxC wxC)
  have exyA : Submodule.map (jetDeriv (Sum.inr 2)) (Submodule.map (jetDeriv (Sum.inr 0)) A) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) byA wyA)
  have exyB : Submodule.map (jetDeriv (Sum.inr 2)) (Submodule.map (jetDeriv (Sum.inr 0)) B) ≤ W := by
    simp only [hB, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have exyC : Submodule.map (jetDeriv (Sum.inr 2)) (Submodule.map (jetDeriv (Sum.inr 0)) C) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) byC wyC)
  have eypA : Submodule.map (jetDeriv (Sum.inr 0)) (Submodule.map (lcp 1) A) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bpA wpA)
  have eypB : Submodule.map (jetDeriv (Sum.inr 0)) (Submodule.map (lcp 1) B) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bpB wpB)
  have eypC : Submodule.map (jetDeriv (Sum.inr 0)) (Submodule.map (lcp 1) C) ≤ W := by
    simp only [hC, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> rw [← lcp_jetDeriv_comm] <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have eymA : Submodule.map (jetDeriv (Sum.inr 0)) (Submodule.map (lcn 1) A) ≤ W := by
    simp only [hA, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> rw [← lcn_jetDeriv_comm] <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have eymB : Submodule.map (jetDeriv (Sum.inr 0)) (Submodule.map (lcn 1) B) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bmB wmB)
  have eymC : Submodule.map (jetDeriv (Sum.inr 0)) (Submodule.map (lcn 1) C) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bmC wmC)
  have eyxA : Submodule.map (jetDeriv (Sum.inr 0)) (Submodule.map (jetDeriv (Sum.inr 2)) A) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bxA wxA)
  have eyxB : Submodule.map (jetDeriv (Sum.inr 0)) (Submodule.map (jetDeriv (Sum.inr 2)) B) ≤ W := by
    simp only [hB, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> rw [jetDeriv_comm (Sum.inr 0) (Sum.inr 2)] <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have eyxC : Submodule.map (jetDeriv (Sum.inr 0)) (Submodule.map (jetDeriv (Sum.inr 2)) C) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) bxC wxC)
  have eyyA : Submodule.map (jetDeriv (Sum.inr 0)) (Submodule.map (jetDeriv (Sum.inr 0)) A) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) byA wyA)
  have eyyB : Submodule.map (jetDeriv (Sum.inr 0)) (Submodule.map (jetDeriv (Sum.inr 0)) B) ≤ W := by
    simp only [hB, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    refine le_trans (Submodule.span_le.2 ?_) le_sup_left
    rintro y (rfl | rfl) <;> exact Submodule.subset_span (by
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
        eq_self_iff_true])
  have eyyC : Submodule.map (jetDeriv (Sum.inr 0)) (Submodule.map (jetDeriv (Sum.inr 0)) C) ≤ W :=
    hN (by norm_num) (map_jetDeriv_transverse_le (by decide) byC wyC)
  -- every monomial is a second light-cone derivative of a field strength
  have hFFle : Submodule.span ℂ FF ≤ stepAxis 1 2 0 (stepAxis 1 2 0 V) := by
    rw [hFF]
    refine Submodule.span_le.2 ?_
    rintro x ⟨ρ, τ, μ, ν, rfl⟩
    rw [fieldStrengthDeriv_pair_eq_jetDeriv]
    exact jetDeriv_mem_stepAxis (by decide) (by decide) (by decide)
      (jetDeriv_mem_stepAxis (by decide) (by decide) (by decide)
        (by rw [hV]; exact Submodule.subset_span ⟨μ, ν, rfl⟩) τ) ρ
  have hmap4 : ∀ (f : JetAlgebra →ₗ[ℂ] JetAlgebra) (P Q R T : Submodule ℂ JetAlgebra),
      Submodule.map f P ≤ W → Submodule.map f Q ≤ W → Submodule.map f R ≤ W →
      Submodule.map f T ≤ W → Submodule.map f (P ⊔ Q ⊔ R ⊔ T) ≤ W := by
    intro f P Q R T h1 h2 h3 h4
    simp only [Submodule.map_sup]
    exact sup_le (sup_le (sup_le h1 h2) h3) h4
  have hin3 : ∀ (f g : JetAlgebra →ₗ[ℂ] JetAlgebra),
      Submodule.map f (Submodule.map g A) ≤ W → Submodule.map f (Submodule.map g B) ≤ W →
      Submodule.map f (Submodule.map g C) ≤ W →
      Submodule.map f (Submodule.map g (A ⊔ B ⊔ C)) ≤ W := by
    intro f g h1 h2 h3
    simp only [Submodule.map_sup]
    exact sup_le (sup_le h1 h2) h3
  have hfin : stepAxis 1 2 0 (stepAxis 1 2 0 (A ⊔ B ⊔ C)) ≤ W := by
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · exact hmap4 _ _ _ _ _ (hin3 _ _ eppA eppB eppC) (hin3 _ _ epmA epmB epmC)
        (hin3 _ _ epxA epxB epxC) (hin3 _ _ epyA epyB epyC)
    · exact hmap4 _ _ _ _ _ (hin3 _ _ empA empB empC) (hin3 _ _ emmA emmB emmC)
        (hin3 _ _ emxA emxB emxC) (hin3 _ _ emyA emyB emyC)
    · exact hmap4 _ _ _ _ _ (hin3 _ _ expA expB expC) (hin3 _ _ exmA exmB exmC)
        (hin3 _ _ exxA exxB exxC) (hin3 _ _ exyA exyB exyC)
    · exact hmap4 _ _ _ _ _ (hin3 _ _ eypA eypB eypC) (hin3 _ _ eymA eymB eymC)
        (hin3 _ _ eyxA eyxB eyxC) (hin3 _ _ eyyA eyyB eyyC)
  have hkey : Submodule.span ℂ FF ≤ W :=
    le_trans hFFle (le_trans (stepAxis_mono (stepAxis_mono hVle)) hfin)
  -- the sixteen generators have weight zero
  have hwz : ∀ {j : ℤ} {y : JetAlgebra}, j = 0 → y ∈ boostWeightSubmodule 1 j →
      y ∈ boostWeightSubmodule 1 0 := by rintro j y rfl h; exact h
  have hTb : T ∈ bosonic := by rw [hT]; exact hFb _ _
  have hLb : L ∈ bosonic := by rw [hL]; exact hFb _ _
  have hPXb : PX ∈ bosonic := by rw [hPX]; exact sub_mem (hFb _ _) (hFb _ _)
  have hPYb : PY ∈ bosonic := by rw [hPY]; exact sub_mem (hFb _ _) (hFb _ _)
  have hMXb : MX ∈ bosonic := by rw [hMX]; exact add_mem (hFb _ _) (hFb _ _)
  have hMYb : MY ∈ bosonic := by rw [hMY]; exact add_mem (hFb _ _) (hFb _ _)
  have hSw : Submodule.span ℂ S ≤ boostWeightSubmodule 1 0 := by
    rw [hS]
    refine Submodule.span_le.2 ?_
    rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl)
    exacts [
    hwz (by norm_num) (lcp_mem_boostWeight (lcn_mem_bosonic hTb)
      (lcn_mem_boostWeight hTb hTw)),
    hwz (by norm_num) (lcp_mem_boostWeight (lcn_mem_bosonic hLb)
      (lcn_mem_boostWeight hLb hLw)),
    jetDeriv_transverse_mem (by decide) (jetDeriv_mem_bosonic (Sum.inr 2) hTb) (jetDeriv_transverse_mem (by decide) hTb hTw),
    jetDeriv_transverse_mem (by decide) (jetDeriv_mem_bosonic (Sum.inr 2) hLb) (jetDeriv_transverse_mem (by decide) hLb hLw),
    jetDeriv_transverse_mem (by decide) (jetDeriv_mem_bosonic (Sum.inr 0) hTb) (jetDeriv_transverse_mem (by decide) hTb hTw),
    jetDeriv_transverse_mem (by decide) (jetDeriv_mem_bosonic (Sum.inr 0) hLb) (jetDeriv_transverse_mem (by decide) hLb hLw),
    jetDeriv_transverse_mem (by decide) (jetDeriv_mem_bosonic (Sum.inr 0) hTb) (jetDeriv_transverse_mem (by decide) hTb hTw),
    jetDeriv_transverse_mem (by decide) (jetDeriv_mem_bosonic (Sum.inr 0) hLb) (jetDeriv_transverse_mem (by decide) hLb hLw),
    hwz (by norm_num) (lcp_mem_boostWeight (jetDeriv_mem_bosonic (Sum.inr 2) hMXb) (jetDeriv_transverse_mem (by decide) hMXb hMXw)),
    hwz (by norm_num) (lcp_mem_boostWeight (jetDeriv_mem_bosonic (Sum.inr 2) hMYb) (jetDeriv_transverse_mem (by decide) hMYb hMYw)),
    hwz (by norm_num) (lcp_mem_boostWeight (jetDeriv_mem_bosonic (Sum.inr 0) hMXb) (jetDeriv_transverse_mem (by decide) hMXb hMXw)),
    hwz (by norm_num) (lcp_mem_boostWeight (jetDeriv_mem_bosonic (Sum.inr 0) hMYb) (jetDeriv_transverse_mem (by decide) hMYb hMYw)),
    hwz (by norm_num) (lcn_mem_boostWeight (jetDeriv_mem_bosonic (Sum.inr 2) hPXb) (jetDeriv_transverse_mem (by decide) hPXb hPXw)),
    hwz (by norm_num) (lcn_mem_boostWeight (jetDeriv_mem_bosonic (Sum.inr 2) hPYb) (jetDeriv_transverse_mem (by decide) hPYb hPYw)),
    hwz (by norm_num) (lcn_mem_boostWeight (jetDeriv_mem_bosonic (Sum.inr 0) hPXb) (jetDeriv_transverse_mem (by decide) hPXb hPXw)),
    hwz (by norm_num) (lcn_mem_boostWeight (jetDeriv_mem_bosonic (Sum.inr 0) hPYb) (jetDeriv_transverse_mem (by decide) hPYb hPYw))]
  refine le_trans (inf_le_inf_left _ hkey) ?_
  rw [hW, inf_comm, sup_inf_assoc_of_le _ hSw,
    disjoint_iff.mp (boostWeightSubmodule_iSupIndep (i := 1) 0).symm, sup_bot_eq]
/-!

## I. The Bianchi identity and the three-axis intersection

-/


lemma lcn_T_eq : lcn 2 (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) =
    jetDeriv (Sum.inr 0) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) +
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1)) -
      jetDeriv (Sum.inr 1) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) +
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0)) := by
  simp only [lcn_apply, map_add]
  rw [jetDeriv_fieldStrengthDeriv_bianchi (Sum.inl 0) (Sum.inr 0) (Sum.inr 1),
    jetDeriv_fieldStrengthDeriv_bianchi (Sum.inr 2) (Sum.inr 0) (Sum.inr 1)]
  abel

lemma lcn_PX_eq : lcn 2 (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) -
      fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0)) =
    (2 : ℂ) • jetDeriv (Sum.inr 0) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) +
      lcp 2 (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) +
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0)) := by
  simp only [lcn_apply, lcp_apply, map_add, map_sub]
  rw [jetDeriv_fieldStrengthDeriv_bianchi (Sum.inr 2) (Sum.inl 0) (Sum.inr 0),
    fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 2)]
  simp only [map_neg]
  module

lemma lcn_PY_eq : lcn 2 (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) -
      fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1)) =
    (2 : ℂ) • jetDeriv (Sum.inr 1) (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) +
      lcp 2 (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) +
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1)) := by
  simp only [lcn_apply, lcp_apply, map_add, map_sub]
  rw [jetDeriv_fieldStrengthDeriv_bianchi (Sum.inr 2) (Sum.inl 0) (Sum.inr 1),
    fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 2)]
  simp only [map_neg]
  module

theorem boostWeight_inter_fieldStrengthDeriv_pair_full :
    boostWeightSubmodule 0 0 ⊓ boostWeightSubmodule 1 0 ⊓ boostWeightSubmodule 2 0 ⊓
      Submodule.span ℂ {x | ∃ ρ τ μ ν, x = fieldStrengthDeriv {ρ, τ} μ ν} = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  rw [Submodule.mem_inf, Submodule.mem_inf, Submodule.mem_inf] at hx
  obtain ⟨⟨⟨hx0, hx1⟩, hx2⟩, hxF⟩ := hx
  have hz := boostWeight_inter_fieldStrengthDeriv_pair_le (Submodule.mem_inf.2 ⟨hx2, hxF⟩)
  have hbx := boostWeight_inter_fieldStrengthDeriv_pair_x_le (Submodule.mem_inf.2 ⟨hx0, hxF⟩)
  have hby := boostWeight_inter_fieldStrengthDeriv_pair_y_le (Submodule.mem_inf.2 ⟨hx1, hxF⟩)
  have hann : ∀ (φ : JetAlgebra →ₗ[ℂ] ℂ) {T : Set JetAlgebra}, (∀ s ∈ T, φ s = 0) →
      ∀ y ∈ Submodule.span ℂ T, φ y = 0 := by
    intro φ T hT y hy
    induction hy using Submodule.span_induction with
    | mem s hs => exact hT s hs
    | zero => simp
    | add u v _ _ hu hv => rw [map_add, hu, hv, add_zero]
    | smul c u _ hu => rw [map_smul, hu, smul_zero]
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ :
      gaugeDerivDual ({Sum.inl 0, Sum.inl 0, Sum.inl 0}, Sum.inr 2) x = 0 ∧
      gaugeDerivDual ({Sum.inl 0, Sum.inl 0, Sum.inr 0}, Sum.inr 0) x = 0 ∧
      gaugeDerivDual ({Sum.inl 0, Sum.inl 0, Sum.inr 0}, Sum.inr 1) x = 0 ∧
      gaugeDerivDual ({Sum.inl 0, Sum.inl 0, Sum.inr 1}, Sum.inr 0) x = 0 ∧
      gaugeDerivDual ({Sum.inl 0, Sum.inl 0, Sum.inr 1}, Sum.inr 1) x = 0 ∧
      gaugeDerivDual ({Sum.inl 0, Sum.inr 0, Sum.inr 0}, Sum.inr 2) x = 0 ∧
      gaugeDerivDual ({Sum.inl 0, Sum.inr 0, Sum.inr 1}, Sum.inr 2) x = 0 ∧
      gaugeDerivDual ({Sum.inl 0, Sum.inr 1, Sum.inr 1}, Sum.inr 2) x = 0 ∧
      gaugeDerivDual ({Sum.inr 0, Sum.inr 0, Sum.inr 0}, Sum.inr 1) x = 0 ∧
      gaugeDerivDual ({Sum.inr 0, Sum.inr 1, Sum.inr 1}, Sum.inr 1) x = 0 ∧
      (gaugeDerivDual ({Sum.inl 0, Sum.inl 0, Sum.inr 1}, Sum.inr 1) +
        gaugeDerivDual ({Sum.inr 0, Sum.inr 0, Sum.inr 1}, Sum.inr 1)) x = 0 := by
    refine ⟨hann _ ?_ x hbx, hann _ ?_ x hbx, hann _ ?_ x hbx, hann _ ?_ x hbx, hann _ ?_ x hby, hann _ ?_ x hbx, hann _ ?_ x hbx, hann _ ?_ x hbx, hann _ ?_ x hbx, hann _ ?_ x hbx, hann _ ?_ x hbx⟩ <;>
      intro s hs <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs <;>
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp +decide only [lcp_apply, lcn_apply, map_add, map_sub,
        LinearMap.add_apply, ← fieldStrengthDeriv_pair_eq_jetDeriv,
        gaugeDerivDual_fieldStrengthDeriv, fsDerivCoeff, add_zero, zero_add, sub_zero,
        zero_sub, sub_self, add_neg_cancel, neg_add_cancel]
  rw [Submodule.mem_bot]
  obtain ⟨a1, y1, hy1, rfl⟩ := Submodule.mem_span_insert.1 hz
  obtain ⟨a2, y2, hy2, rfl⟩ := Submodule.mem_span_insert.1 hy1
  obtain ⟨a3, y3, hy3, rfl⟩ := Submodule.mem_span_insert.1 hy2
  obtain ⟨a4, y4, hy4, rfl⟩ := Submodule.mem_span_insert.1 hy3
  obtain ⟨a5, y5, hy5, rfl⟩ := Submodule.mem_span_insert.1 hy4
  obtain ⟨a6, y6, hy6, rfl⟩ := Submodule.mem_span_insert.1 hy5
  obtain ⟨a7, y7, hy7, rfl⟩ := Submodule.mem_span_insert.1 hy6
  obtain ⟨a8, y8, hy8, rfl⟩ := Submodule.mem_span_insert.1 hy7
  obtain ⟨a9, y9, hy9, rfl⟩ := Submodule.mem_span_insert.1 hy8
  obtain ⟨a10, y10, hy10, rfl⟩ := Submodule.mem_span_insert.1 hy9
  obtain ⟨a11, y11, hy11, rfl⟩ := Submodule.mem_span_insert.1 hy10
  obtain ⟨a12, y12, hy12, rfl⟩ := Submodule.mem_span_insert.1 hy11
  obtain ⟨a13, y13, hy13, rfl⟩ := Submodule.mem_span_insert.1 hy12
  obtain ⟨a14, y14, hy14, rfl⟩ := Submodule.mem_span_insert.1 hy13
  obtain ⟨a15, y15, hy15, rfl⟩ := Submodule.mem_span_insert.1 hy14
  obtain ⟨a16, rfl⟩ := Submodule.mem_span_singleton.1 hy15
  simp +decide only [map_add, map_smul, smul_eq_mul, LinearMap.add_apply, lcp_apply,
    lcn_apply, map_sub, ← fieldStrengthDeriv_pair_eq_jetDeriv,
    gaugeDerivDual_fieldStrengthDeriv, fsDerivCoeff, if_true, if_false, mul_zero, mul_one,
    add_zero, zero_add, sub_zero, zero_sub, sub_self] at e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
  ring_nf at e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
  simp only [lcp_jetDeriv_comm, lcn_jetDeriv_comm]
  simp only [lcn_T_eq, lcn_PX_eq, lcn_PY_eq]
  simp only [map_add, map_sub, map_smul, lcp_jetDeriv_comm, lcn_jetDeriv_comm,
    jetDeriv_comm (Sum.inr 1) (Sum.inr 0)]
  match_scalars
  · linear_combination e3
  · linear_combination e3
  · linear_combination e4
  · linear_combination e4
  · linear_combination e1
  · linear_combination e9
  · linear_combination e6 + e2
  · linear_combination e11 - e5
  · linear_combination e7 + e3 + e4
  · linear_combination e10
  · linear_combination e8 + e5
  · linear_combination e2
  · linear_combination e2
  · linear_combination e5
  · linear_combination e5

end JetAlgebra

end LeptonGaugeSector






end
