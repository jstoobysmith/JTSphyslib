/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Boosts.WeightGrading
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
/-!
# Class IsLorentzDeriv

A family of operators indexed by the four spacetime directions is a **Lorentz derivative**
when the representation of `SL(2,ℂ)` intertwines it through the columns of the Lorentz
matrix, as the jet derivatives on a jet algebra do.

Along the `i`-th spatial axis the four operators regroup into the two light-cone
combinations `lightConePlus D i = D_0 - D_i` and `lightConeMinus D i = D_0 + D_i`, which
shift every boost weight by `+2` and `-2` respectively, and the two transverse operators,
which preserve it. Consequently the weight-`k` part of the span of all derivative images of
a submodule redistributes onto the shifted weight projections
(`boostProj_map_submodule_x/y/z`).

-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups TensorProduct
open scoped Pointwise

variable {A : Type} [Ring A] [Algebra ℂ A]

class IsLorentzDeriv (rep : Representation ℂ SL(2,ℂ) A) (D : (Fin 1 ⊕ Fin 3) → A →ₗ[ℂ] A) where
  rep_deriv {Λ μ x} : rep Λ (D μ x) =
    ∑ a, (((SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) • D a (rep Λ x)

namespace IsLorentzDeriv

variable {rep : Representation ℂ SL(2,ℂ) A} {D : (Fin 1 ⊕ Fin 3) → A →ₗ[ℂ] A}

/-- The scalar action of a real parameter, in the form the weight condition presents it. -/
private lemma algebraMap_real_complex (t : ℝ) : (algebraMap ℝ ℂ) t = ((t : ℝ) : ℂ) := rfl

/-!

## A. Light cone derivatives

-/

/-- The light-cone combination `D_0 - D_i`, raising every boost weight along the `i`-th
  axis by two (`lightConePlus_mem`). -/
def lightConePlus (D : (Fin 1 ⊕ Fin 3) → A →ₗ[ℂ] A) (i : Fin 3) : A →ₗ[ℂ] A :=
  D (Sum.inl 0) - D (Sum.inr i)

/-- The light-cone combination `D_0 + D_i`, lowering every boost weight along the `i`-th
  axis by two (`lightConeMinus_mem`). -/
def lightConeMinus (D : (Fin 1 ⊕ Fin 3) → A →ₗ[ℂ] A) (i : Fin 3) : A →ₗ[ℂ] A :=
  D (Sum.inl 0) + D (Sum.inr i)

/-!

## B. Relationship to boost weights

-/

section

set_option linter.unusedSimpArgs false

/-- A transverse Lorentz derivative leaves the boost weight along the `i`-th axis alone. -/
lemma transverse_mem [IsLorentzDeriv rep D] {i j : Fin 3} (hij : j ≠ i) {k : ℤ} {x : A}
    (hx : x ∈ BoostWeight.boostWeightSubmodule rep i k) :
    D (Sum.inr j) x ∈ BoostWeight.boostWeightSubmodule rep i k := by
  intro t ht
  rw [rep_deriv, hx t ht, algebraMap_real_complex]
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl hij
      | simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
          boostAxis_zero, toLorentzGroup_boostXel, boostMatX,
          boostAxis_one, toLorentzGroup_boostYel, boostMatY,
          boostAxis_two, toLorentzGroup_boostZel, boostMatZ,
          Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, map_smul,
          Complex.ofReal_zero, zero_smul, Complex.ofReal_one, one_smul, add_zero, zero_add]

/-- The light-cone combination `D_0 - D_i` raises the boost weight along the `i`-th axis
  by two. -/
lemma lightConePlus_mem [IsLorentzDeriv rep D] {i : Fin 3} {k : ℤ} {x : A}
    (hx : x ∈ BoostWeight.boostWeightSubmodule rep i k) :
    lightConePlus D i x ∈ BoostWeight.boostWeightSubmodule rep i (k + 2) := by
  intro t ht
  have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  simp only [lightConePlus, LinearMap.sub_apply]
  rw [map_sub, rep_deriv, rep_deriv, hx t ht]
  rw [algebraMap_real_complex, zpow_add₀ ht']
  fin_cases i
  · simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    simp only [boostAxis_zero, toLorentzGroup_boostXel, boostMatX, Fintype.sum_sum_type,
      Fin.sum_univ_one, Fin.sum_univ_three, map_smul, Complex.ofReal_zero, zero_smul,
      Complex.ofReal_one, one_smul, add_zero, zero_add, Complex.ofReal_div, Complex.ofReal_add,
      Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_neg,
      Complex.ofReal_ofNat]
    match_scalars <;> (field_simp; ring)
  · simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    simp only [boostAxis_one, toLorentzGroup_boostYel, boostMatY, Fintype.sum_sum_type,
      Fin.sum_univ_one, Fin.sum_univ_three, map_smul, Complex.ofReal_zero, zero_smul,
      Complex.ofReal_one, one_smul, add_zero, zero_add, Complex.ofReal_div, Complex.ofReal_add,
      Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_neg,
      Complex.ofReal_ofNat]
    match_scalars <;> (field_simp; ring)
  · simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    simp only [boostAxis_two, toLorentzGroup_boostZel, boostMatZ, Fintype.sum_sum_type,
      Fin.sum_univ_one, Fin.sum_univ_three, map_smul, Complex.ofReal_zero, zero_smul,
      Complex.ofReal_one, one_smul, add_zero, zero_add, Complex.ofReal_div, Complex.ofReal_add,
      Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_neg,
      Complex.ofReal_ofNat]
    match_scalars <;> (field_simp; ring)

/-- The light-cone combination `D_0 + D_i` lowers the boost weight along the `i`-th axis
  by two. -/
lemma lightConeMinus_mem [IsLorentzDeriv rep D] {i : Fin 3} {k : ℤ} {x : A}
    (hx : x ∈ BoostWeight.boostWeightSubmodule rep i k) :
    lightConeMinus D i x ∈ BoostWeight.boostWeightSubmodule rep i (k - 2) := by
  intro t ht
  have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  simp only [lightConeMinus, LinearMap.add_apply]
  rw [map_add, rep_deriv, rep_deriv, hx t ht]
  rw [algebraMap_real_complex, zpow_sub₀ ht']
  fin_cases i
  · simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    simp only [boostAxis_zero, toLorentzGroup_boostXel, boostMatX, Fintype.sum_sum_type,
      Fin.sum_univ_one, Fin.sum_univ_three, map_smul, Complex.ofReal_zero, zero_smul,
      Complex.ofReal_one, one_smul, add_zero, zero_add, Complex.ofReal_div, Complex.ofReal_add,
      Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_neg,
      Complex.ofReal_ofNat]
    match_scalars <;> (field_simp; ring)
  · simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    simp only [boostAxis_one, toLorentzGroup_boostYel, boostMatY, Fintype.sum_sum_type,
      Fin.sum_univ_one, Fin.sum_univ_three, map_smul, Complex.ofReal_zero, zero_smul,
      Complex.ofReal_one, one_smul, add_zero, zero_add, Complex.ofReal_div, Complex.ofReal_add,
      Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_neg,
      Complex.ofReal_ofNat]
    match_scalars <;> (field_simp; ring)
  · simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    simp only [boostAxis_two, toLorentzGroup_boostZel, boostMatZ, Fintype.sum_sum_type,
      Fin.sum_univ_one, Fin.sum_univ_three, map_smul, Complex.ofReal_zero, zero_smul,
      Complex.ofReal_one, one_smul, add_zero, zero_add, Complex.ofReal_div, Complex.ofReal_add,
      Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_neg,
      Complex.ofReal_ofNat]
    match_scalars <;> (field_simp; ring)

end

/-!

## The boost projections of the span of the derivative images

-/

/-- Two composites agreeing on a submodule have the same double image. -/
private lemma map_map_eq_of_forall_mem {f g f' g' : A →ₗ[ℂ] A}
    {V : Submodule ℂ A} (h : ∀ x ∈ V, g (f x) = g' (f' x)) :
    (V.map f).map g = (V.map f').map g' := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨f' v, ⟨v, hv, rfl⟩, (h v hv).symm⟩
  · rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨f v, ⟨v, hv, rfl⟩, h v hv⟩

/-- The images under `D_0` and `D_i` span the same submodule as the images under the two
  light-cone combinations. -/
lemma map_pair_eq_lightCone (D : (Fin 1 ⊕ Fin 3) → A →ₗ[ℂ] A) (i : Fin 3)
    (V : Submodule ℂ A) :
    V.map (D (Sum.inl 0)) + V.map (D (Sum.inr i)) =
      V.map (lightConePlus D i) + V.map (lightConeMinus D i) := by
  rw [Submodule.add_eq_sup, Submodule.add_eq_sup]
  refine le_antisymm (sup_le ?_ ?_) (sup_le ?_ ?_)
  · rintro _ ⟨v, hv, rfl⟩
    rw [show D (Sum.inl 0) v =
        (2⁻¹ : ℂ) • lightConePlus D i v + (2⁻¹ : ℂ) • lightConeMinus D i v from by
      simp only [lightConePlus, lightConeMinus, LinearMap.sub_apply, LinearMap.add_apply]
      module]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.mem_sup_left ⟨v, hv, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.mem_sup_right ⟨v, hv, rfl⟩))
  · rintro _ ⟨v, hv, rfl⟩
    rw [show D (Sum.inr i) v =
        (-2⁻¹ : ℂ) • lightConePlus D i v + (2⁻¹ : ℂ) • lightConeMinus D i v from by
      simp only [lightConePlus, lightConeMinus, LinearMap.sub_apply, LinearMap.add_apply]
      module]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.mem_sup_left ⟨v, hv, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.mem_sup_right ⟨v, hv, rfl⟩))
  · rintro _ ⟨v, hv, rfl⟩
    simp only [lightConePlus, LinearMap.sub_apply]
    exact sub_mem (Submodule.mem_sup_left ⟨v, hv, rfl⟩)
      (Submodule.mem_sup_right ⟨v, hv, rfl⟩)
  · rintro _ ⟨v, hv, rfl⟩
    simp only [lightConeMinus, LinearMap.add_apply]
    exact add_mem (Submodule.mem_sup_left ⟨v, hv, rfl⟩)
      (Submodule.mem_sup_right ⟨v, hv, rfl⟩)

/-- The engine behind the three axis lemmas: the projection of the four derivative images
  redistributes onto the shifted projections of `V`. -/
private lemma boostProj_map_submodule_aux [BoostWeight.IsBoostGraded rep]
    [IsLorentzDeriv rep D] {i t₁ t₂ : Fin 3} (ht₁ : t₁ ≠ i) (ht₂ : t₂ ≠ i) (k : ℤ)
    (V : Submodule ℂ A) :
    (V.map (D (Sum.inl 0)) + V.map (D (Sum.inr i)) + V.map (D (Sum.inr t₁)) +
        V.map (D (Sum.inr t₂))).map (BoostWeight.boostProj rep i k) =
      (V.map (BoostWeight.boostProj rep i (k - 2))).map (lightConePlus D i) +
      (V.map (BoostWeight.boostProj rep i (k + 2))).map (lightConeMinus D i) +
      (V.map (BoostWeight.boostProj rep i k)).map (D (Sum.inr t₁)) +
      (V.map (BoostWeight.boostProj rep i k)).map (D (Sum.inr t₂)) := by
  have hlcp : (V.map (lightConePlus D i)).map (BoostWeight.boostProj rep i k) =
      (V.map (BoostWeight.boostProj rep i (k - 2))).map (lightConePlus D i) := by
    refine map_map_eq_of_forall_mem fun v _ => ?_
    refine BoostWeight.boostProj_comm rep k (k - 2) (fun {w} {y} hyw => ?_) v
    rw [show w + k - (k - 2) = w + 2 from by ring]
    exact lightConePlus_mem hyw
  have hlcn : (V.map (lightConeMinus D i)).map (BoostWeight.boostProj rep i k) =
      (V.map (BoostWeight.boostProj rep i (k + 2))).map (lightConeMinus D i) := by
    refine map_map_eq_of_forall_mem fun v _ => ?_
    refine BoostWeight.boostProj_comm rep k (k + 2) (fun {w} {y} hyw => ?_) v
    rw [show w + k - (k + 2) = w - 2 from by ring]
    exact lightConeMinus_mem hyw
  have hd₁ : (V.map (D (Sum.inr t₁))).map (BoostWeight.boostProj rep i k) =
      (V.map (BoostWeight.boostProj rep i k)).map (D (Sum.inr t₁)) := by
    refine map_map_eq_of_forall_mem fun v _ => ?_
    refine BoostWeight.boostProj_comm rep k k (fun {w} {y} hyw => ?_) v
    rw [show w + k - k = w from by ring]
    exact transverse_mem ht₁ hyw
  have hd₂ : (V.map (D (Sum.inr t₂))).map (BoostWeight.boostProj rep i k) =
      (V.map (BoostWeight.boostProj rep i k)).map (D (Sum.inr t₂)) := by
    refine map_map_eq_of_forall_mem fun v _ => ?_
    refine BoostWeight.boostProj_comm rep k k (fun {w} {y} hyw => ?_) v
    rw [show w + k - k = w from by ring]
    exact transverse_mem ht₂ hyw
  rw [map_pair_eq_lightCone]
  simp only [Submodule.add_eq_sup, Submodule.map_sup, hlcp, hlcn, hd₁, hd₂]

/-- **The boost projections of the span of Lorentz derivatives, along any axis.** The
  weight-`k` part of the span of the four derivative images of `V` is spanned by the
  light-cone combinations applied to the weight-`(k ∓ 2)` parts of `V` together with the two
  transverse derivatives, at directions `i + 1` and `i + 2`, of its weight-`k` part. -/
lemma boostProj_map_deriv_map_submodule [BoostWeight.IsBoostGraded rep]
    [IsLorentzDeriv rep D] (k : ℤ) (V : Submodule ℂ A) (i : Fin 3) :
    (∑ α, V.map (D α)).map (BoostWeight.boostProj rep i k) =
    (V.map (BoostWeight.boostProj rep i (k - 2))).map (lightConePlus D i)
    + (V.map (BoostWeight.boostProj rep i (k + 2))).map (lightConeMinus D i)
    + (V.map (BoostWeight.boostProj rep i k)).map (D (Sum.inr (i + 1)))
    + (V.map (BoostWeight.boostProj rep i k)).map (D (Sum.inr (i + 2))) := by
  have hsum : (∑ α, V.map (D α)) =
      V.map (D (Sum.inl 0)) + V.map (D (Sum.inr i)) + V.map (D (Sum.inr (i + 1))) +
        V.map (D (Sum.inr (i + 2))) := by
    rw [Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three]
    fin_cases i <;>
      (simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.reduceAdd]; abel)
  rw [hsum]
  exact boostProj_map_submodule_aux (by fin_cases i <;> decide) (by fin_cases i <;> decide) k V

/-- **Two derivative layers.** The weight-`k` part of the span of all second derivative
  images of `V` redistributes onto the weight `k - 4, …, k + 4` parts of `V`, hit by the
  light-cone and transverse operators twice over: `boostProj_map_deriv_map_submodule`
  applied at the outer layer and then to each of the three inner projected spans. -/
lemma boostProj_map_deriv_map_deriv_map [BoostWeight.IsBoostGraded rep] [IsLorentzDeriv rep D]
    (k : ℤ) (V : Submodule ℂ A) (i : Fin 3) :
    (∑ β, (∑ α, V.map (D α)).map (D β)).map (BoostWeight.boostProj rep i k) =
    ((V.map (BoostWeight.boostProj rep i (k - 4))).map (lightConePlus D i)
      + (V.map (BoostWeight.boostProj rep i k)).map (lightConeMinus D i)
      + (V.map (BoostWeight.boostProj rep i (k - 2))).map (D (Sum.inr (i + 1)))
      + (V.map (BoostWeight.boostProj rep i (k - 2))).map (D (Sum.inr (i + 2)))).map
        (lightConePlus D i)
    + ((V.map (BoostWeight.boostProj rep i k)).map (lightConePlus D i)
      + (V.map (BoostWeight.boostProj rep i (k + 4))).map (lightConeMinus D i)
      + (V.map (BoostWeight.boostProj rep i (k + 2))).map (D (Sum.inr (i + 1)))
      + (V.map (BoostWeight.boostProj rep i (k + 2))).map (D (Sum.inr (i + 2)))).map
        (lightConeMinus D i)
    + ((V.map (BoostWeight.boostProj rep i (k - 2))).map (lightConePlus D i)
      + (V.map (BoostWeight.boostProj rep i (k + 2))).map (lightConeMinus D i)
      + (V.map (BoostWeight.boostProj rep i k)).map (D (Sum.inr (i + 1)))
      + (V.map (BoostWeight.boostProj rep i k)).map (D (Sum.inr (i + 2)))).map
        (D (Sum.inr (i + 1)))
    + ((V.map (BoostWeight.boostProj rep i (k - 2))).map (lightConePlus D i)
      + (V.map (BoostWeight.boostProj rep i (k + 2))).map (lightConeMinus D i)
      + (V.map (BoostWeight.boostProj rep i k)).map (D (Sum.inr (i + 1)))
      + (V.map (BoostWeight.boostProj rep i k)).map (D (Sum.inr (i + 2)))).map
        (D (Sum.inr (i + 2))) := by
  rw [boostProj_map_deriv_map_submodule k _ i, boostProj_map_deriv_map_submodule (k - 2) V i,
    boostProj_map_deriv_map_submodule (k + 2) V i, boostProj_map_deriv_map_submodule k V i,
    show k - 2 - 2 = k - 4 from by ring, show k - 2 + 2 = k from by ring,
    show k + 2 - 2 = k from by ring, show k + 2 + 2 = k + 4 from by ring]

/-- The span of the derivative images of a weight-decomposed submodule is weight decomposed:
  the projections stay inside it and the support widens by the light-cone shifts `±2`. -/
noncomputable def _root_.Lorentz.BoostWeight.WeightDecomposition.deriv
    [BoostWeight.IsBoostGraded rep] {i : Fin 3} {V : Submodule ℂ A}
    (d : BoostWeight.WeightDecomposition rep i V)
    (D : (Fin 1 ⊕ Fin 3) → A →ₗ[ℂ] A) [IsLorentzDeriv rep D] :
    BoostWeight.WeightDecomposition rep i (∑ α, V.map (D α)) := by
  classical
  have hV : ∀ μ, V.map (D μ) ≤ ∑ α, V.map (D α) := fun μ =>
    Finset.single_le_sum (f := fun α => V.map (D α))
      (fun _ _ => by rw [Submodule.zero_eq_bot]; exact bot_le) (Finset.mem_univ μ)
  have hsub : ∀ f g : A →ₗ[ℂ] A, V.map (f - g) ≤ V.map f ⊔ V.map g := by
    rintro f g _ ⟨v, hv, rfl⟩
    rw [LinearMap.sub_apply]
    exact sub_mem (Submodule.mem_sup_left ⟨v, hv, rfl⟩)
      (Submodule.mem_sup_right ⟨v, hv, rfl⟩)
  have hadd : ∀ f g : A →ₗ[ℂ] A, V.map (f + g) ≤ V.map f ⊔ V.map g := by
    rintro f g _ ⟨v, hv, rfl⟩
    rw [LinearMap.add_apply]
    exact add_mem (Submodule.mem_sup_left ⟨v, hv, rfl⟩)
      (Submodule.mem_sup_right ⟨v, hv, rfl⟩)
  refine BoostWeight.WeightDecomposition.ofMapClosed rep (d.supp + ({-2, 0, 2} : Finset ℤ))
    (fun k => ?_) (fun k hk => ?_)
  · rw [boostProj_map_deriv_map_submodule k V i]
    simp only [Submodule.add_eq_sup]
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · exact (Submodule.map_mono (d.map_boostProj_le _)).trans
        ((hsub _ _).trans (sup_le (hV _) (hV _)))
    · exact (Submodule.map_mono (d.map_boostProj_le _)).trans
        ((hadd _ _).trans (sup_le (hV _) (hV _)))
    · exact (Submodule.map_mono (d.map_boostProj_le _)).trans (hV _)
    · exact (Submodule.map_mono (d.map_boostProj_le _)).trans (hV _)
  · have h₁ : k - 2 ∉ d.supp := fun h => hk (by
      simpa using Finset.add_mem_add h (show (2 : ℤ) ∈ ({-2, 0, 2} : Finset ℤ) by decide))
    have h₂ : k + 2 ∉ d.supp := fun h => hk (by
      simpa using Finset.add_mem_add h (show (-2 : ℤ) ∈ ({-2, 0, 2} : Finset ℤ) by decide))
    have h₀ : k ∉ d.supp := fun h => hk (by
      simpa using Finset.add_mem_add h (show (0 : ℤ) ∈ ({-2, 0, 2} : Finset ℤ) by decide))
    rw [boostProj_map_deriv_map_submodule k V i, d.map_boostProj_of_notMem h₁,
      d.map_boostProj_of_notMem h₂, d.map_boostProj_of_notMem h₀]
    simp

end IsLorentzDeriv

end Lorentz

end
