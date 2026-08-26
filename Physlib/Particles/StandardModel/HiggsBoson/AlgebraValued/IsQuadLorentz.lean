/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.HiggsBoson.Basic
public import Physlib.Relativity.IsLorentzDeriv
public import Physlib.Particles.StandardModel.GaugeGroup.Jet.Basic
public import Physlib.Relativity.LorentzGroup.Boosts.WeightGrading
public import Physlib.Particles.StandardModel.GaugeGroup.SU2PermDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.GaugeWeightDecomposition
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.JetDeriv
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.LorentzAction
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.GaugeAction
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.MassDim
public import Physlib.Particles.StandardModel.HiggsBoson.AlgebraValued.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Analysis.Normed.Lp.Matrix
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RepresentationTheory.Invariants
public meta import Mathlib.Data.Fintype.Sum
public meta import Mathlib.Data.Fintype.Pi
/-!
# Invariants under the Lorentz group with four-vector indices
-/

@[expose] public section

namespace Lorentz

open TensorProduct Matrix MatrixGroups Lorentz


structure IsQuadLorentz (B : Type*) [Semiring B] [Algebra ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B)
    (T : (Fin 4 → (Fin 1 ⊕ Fin 3)) → B) : Prop where
  repLorentz_T : ∀ (g : SL(2,ℂ)) l,
    repLorentz g (T l) = ∑ (a : Fin 4 → Fin 1 ⊕ Fin 3),
    (∏ (i : Fin 4), (((SL2C.toLorentzGroup g).1 (a i) (l i) : ℝ) : ℂ)) • T a

namespace IsQuadLorentz
set_option linter.unusedVariables false

variable {B : Type*} [Ring B] [Algebra ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {T : (Fin 4 → (Fin 1 ⊕ Fin 3)) → B}
  (hT : IsQuadLorentz B repLorentz T)

/-- The span of all the components. -/
def span (hT : IsQuadLorentz B repLorentz T) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

lemma mem_span_iff (x : B) :
    x ∈ hT.span ↔ ∃ (c : (Fin 4 → (Fin 1 ⊕ Fin 3)) → ℂ), x = ∑ d, c d • T d := by
  constructor
  · intro hx
    rw [span] at hx
    refine Submodule.iSup_induction
      (motive := fun y => ∃ c : (Fin 4 → (Fin 1 ⊕ Fin 3)) → ℂ, y = ∑ d, c d • T d)
      (fun d => ℂ ∙ T d) hx ?_ ?_ ?_
    · intro d y hy
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
      refine ⟨fun e => if e = d then a else 0, ?_⟩
      simp [ite_smul, Finset.sum_ite_eq']
    · exact ⟨0, by simp⟩
    · rintro y z ⟨c₁, rfl⟩ ⟨c₂, rfl⟩
      exact ⟨c₁ + c₂, by simp [add_smul, Finset.sum_add_distrib]⟩
  · rintro ⟨c, rfl⟩
    exact sum_mem fun d _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem d (Submodule.mem_span_singleton_self _))

/-!

## A. Light cone directions

-/

open StandardModel.IsHiggsAlgebraValued StandardModel.IsHiggsAlgebraValued.IsDerivativeCollection
  BoostWeight

noncomputable def lightCone  (hT : IsQuadLorentz B repLorentz T) (i : Fin 3) (c : Fin 4 → Fin 4) :  B :=
  ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, (∏ j, lightConeCoeff i (c j) (d j)) • T d

/-- Each light-cone component lies in the span of the coordinate components. -/
lemma lightCone_mem_span (i : Fin 3) (c : Fin 4 → Fin 4) : hT.lightCone i c ∈ hT.span :=
  sum_mem fun d _ => Submodule.smul_mem _ _
    (Submodule.mem_iSup_of_mem d (Submodule.mem_span_singleton_self _))

lemma eq_sum_lightCone (i : Fin 3) (d : Fin 4 → Fin 1 ⊕ Fin 3) :
    T d = ∑ c : Fin 4 → Fin 4,
      (∏ j, lightConeCoeffInv i (d j) (c j)) • hT.lightCone i c := by
  calc T d = ∑ e : Fin 4 → Fin 1 ⊕ Fin 3,
        (∑ c : Fin 4 → Fin 4, (∏ j, lightConeCoeffInv i (d j) (c j)) *
          (∏ j, lightConeCoeff i (c j) (e j))) • T e := by
        simp only [sum_prod_lightConeCoeffInv, ite_smul, one_smul, zero_smul,
          Finset.sum_ite_eq, Finset.mem_univ, if_true]
    _ = _ := by
        simp only [lightCone, Finset.smul_sum, smul_smul, Finset.sum_smul]
        rw [Finset.sum_comm]

lemma span_eq_lightCone (hT : IsQuadLorentz B repLorentz T) (i : Fin 3) :
    hT.span = ⨆ c, ℂ ∙ hT.lightCone i c := by
  rw [span]
  refine le_antisymm (iSup_le fun d => ?_) (iSup_le fun c => ?_)
  · rw [Submodule.span_singleton_le_iff_mem, hT.eq_sum_lightCone i d]
    exact sum_mem fun c _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem c (Submodule.mem_span_singleton_self _))
  · rw [Submodule.span_singleton_le_iff_mem]
    exact hT.lightCone_mem_span i c


lemma lightCone_mem_boostWeightSubmodule (i : Fin 3) (c : Fin 4 → Fin 4) :
    hT.lightCone i c ∈ boostWeightSubmodule repLorentz i (∑ j, lightConeWeight (c j)) := by
  refine mem_boostWeightSubmodule.2 fun t ht => ?_
  have hstep : ∀ x : Fin 4 → Fin 1 ⊕ Fin 3,
      (∏ j, lightConeCoeff i (c j) (x j)) •
          repLorentz (SL2C.boostAxis i t ht) (T x)
        = ∑ a : Fin 4 → Fin 1 ⊕ Fin 3,
            ((∏ j, lightConeCoeff i (c j) (x j)) *
              (∏ j, (((SL2C.toLorentzGroup (SL2C.boostAxis i t ht)).1 (a j)
                (x j) : ℝ) : ℂ))) • T a := by
    intro x
    rw [hT.repLorentz_T, Finset.smul_sum]
    exact Finset.sum_congr rfl fun a _ => smul_smul _ _ _
  calc repLorentz (SL2C.boostAxis i t ht) (hT.lightCone i c)
      = ∑ x : Fin 4 → Fin 1 ⊕ Fin 3, (∏ j, lightConeCoeff i (c j) (x j)) •
          repLorentz (SL2C.boostAxis i t ht) (T x) := by
        simp only [lightCone, map_sum, map_smul]
    _ = ∑ a : Fin 4 → Fin 1 ⊕ Fin 3,
          (∑ x : Fin 4 → Fin 1 ⊕ Fin 3, (∏ j, lightConeCoeff i (c j) (x j)) *
            (∏ j, (((SL2C.toLorentzGroup (SL2C.boostAxis i t ht)).1 (a j)
              (x j) : ℝ) : ℂ))) • T a := by
        simp only [hstep]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => (Finset.sum_smul).symm
    _ = ∑ a : Fin 4 → Fin 1 ⊕ Fin 3, (((t : ℝ) : ℂ) ^ (∑ j, lightConeWeight (c j)) *
          (∏ j, lightConeCoeff i (c j) (a j))) • T a := by
        refine Finset.sum_congr rfl fun a _ => ?_
        congr 1
        exact sum_prod_lightConeCoeff i c a ht
    _ = (algebraMap ℝ ℂ) t ^ (∑ j, lightConeWeight (c j)) • hT.lightCone i c := by
        rw [show (algebraMap ℝ ℂ) t = ((t : ℝ) : ℂ) from rfl, lightCone, Finset.smul_sum]
        exact Finset.sum_congr rfl fun a _ => (smul_smul _ _ _).symm

/-- Integer mirror of `IsDerivativeCollection.lightConeCoeff`. -/
def lightConeCoeffZ (i : Fin 3) (κ : Fin 4) (μ : Fin 1 ⊕ Fin 3) : ℤ :=
  if κ = 0 then (if μ = Sum.inl 0 then 1 else if μ = Sum.inr i then -1 else 0)
  else if κ = 1 then (if μ = Sum.inl 0 then 1 else if μ = Sum.inr i then 1 else 0)
  else if κ = 2 then (if μ = Sum.inr (i + 1) then 1 else 0)
  else (if μ = Sum.inr (i + 2) then 1 else 0)

/-- The integer mirror casts to the light-cone coefficients. -/
lemma coe_lightConeCoeffZ (i : Fin 3) (κ : Fin 4) (μ : Fin 1 ⊕ Fin 3) :
    ((lightConeCoeffZ i κ μ : ℤ) : ℂ) = lightConeCoeff i κ μ := by
  rw [lightConeCoeffZ, lightConeCoeff]
  split_ifs <;> norm_num

/-- Rational mirror of `IsDerivativeCollection.lightConeCoeffInv`: entries `0`, `±2⁻¹`
  and `1`, so ℚ-valued (like `lightConeTransition`) rather than integer. -/
def lightConeCoeffInvQ (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) (κ : Fin 4) : ℚ :=
  if μ = Sum.inl 0 then (if κ = 0 then 2⁻¹ else if κ = 1 then 2⁻¹ else 0)
  else if μ = Sum.inr i then (if κ = 0 then -2⁻¹ else if κ = 1 then 2⁻¹ else 0)
  else if μ = Sum.inr (i + 1) then (if κ = 2 then 1 else 0)
  else (if κ = 3 then 1 else 0)

/-- The rational mirror casts to the inverse light-cone coefficients. -/
lemma coe_lightConeCoeffInvQ (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) (κ : Fin 4) :
    ((lightConeCoeffInvQ i μ κ : ℚ) : ℂ) = lightConeCoeffInv i μ κ := by
  rw [lightConeCoeffInvQ, lightConeCoeffInv]
  split_ifs <;> norm_num

/-- Where the integer mirror vanishes, the inverse coefficient vanishes too: the zero
  pattern of `lightConeCoeffInv` is the transpose of that of `lightConeCoeffZ`. -/
lemma lightConeCoeffInv_eq_zero_of_coeffZ_eq_zero (i : Fin 3) (κ : Fin 4)
    (μ : Fin 1 ⊕ Fin 3) (h : lightConeCoeffZ i κ μ = 0) : lightConeCoeffInv i μ κ = 0 := by
  rcases μ with a | j
  · rw [Subsingleton.elim a 0] at h ⊢
    fin_cases i <;> fin_cases κ <;> simp_all [lightConeCoeffZ, lightConeCoeffInv]
  · fin_cases i <;> fin_cases j <;> fin_cases κ <;>
      simp_all [lightConeCoeffZ, lightConeCoeffInv]

/-!

## Vanishing of homogeneous components

A finite sum of homogeneous boost-weight components vanishes only if every component
does: the weight spaces are independent. Consequently a weight-zero element written as
such a sum equals its weight-zero component alone.

These are pure weight-grading statements (no `T` involved) generalizing
`eq_zero_and_eq_zero_of_add_add_mem_boostWeightSubmodule` from two weights to finitely
many; they will eventually move next to `boostWeightSubmodule_iSupIndep`.

-/

/-- **Components of a vanishing homogeneous sum vanish**: the boost-weight spaces are
  independent. -/
lemma eq_zero_of_sum_mem_boostWeightSubmodule
    {K : Type*} [Field K] [Algebra ℝ K] {A : Type*} [Ring A] [Algebra K A]
    {rep : Representation K SL(2,ℂ) A} {i : Fin 3} {s : Finset ℤ} {w : ℤ → A}
    (hw : ∀ m ∈ s, w m ∈ boostWeightSubmodule rep i m)
    (hsum : ∑ m ∈ s, w m = 0) :
    ∀ m ∈ s, w m = 0 := by
  intro m₀ hm₀
  refine Submodule.disjoint_def.1
    (iSupIndep_def.1 (boostWeightSubmodule_iSupIndep rep) m₀) (w m₀) (hw m₀ hm₀) ?_
  have h : w m₀ = -∑ m ∈ s.erase m₀, w m :=
    eq_neg_of_add_eq_zero_left (by rw [Finset.add_sum_erase s w hm₀]; exact hsum)
  rw [h]
  exact neg_mem (sum_mem fun m hm => Submodule.mem_iSup_of_mem m
    (Submodule.mem_iSup_of_mem (Finset.ne_of_mem_erase hm)
      (hw m (Finset.mem_of_mem_erase hm))))

/-- **A weight-zero element of a homogeneous sum is its weight-zero component**: all the
  other components must vanish. -/
lemma eq_component_zero_of_mem_boostWeightSubmodule
    {K : Type*} [Field K] [Algebra ℝ K] {A : Type*} [Ring A] [Algebra K A]
    {rep : Representation K SL(2,ℂ) A} {i : Fin 3} {s : Finset ℤ} {w : ℤ → A} {x : A}
    (hx : x ∈ boostWeightSubmodule rep i 0)
    (hw : ∀ m ∈ s, w m ∈ boostWeightSubmodule rep i m)
    (h0 : (0 : ℤ) ∈ s) (hsum : x = ∑ m ∈ s, w m) :
    x = w 0 := by
  have hv : ∀ m ∈ s, Function.update w 0 (w 0 - x) m ∈ boostWeightSubmodule rep i m := by
    intro m hm
    by_cases h : m = 0
    · subst h
      rw [Function.update_self]
      exact sub_mem (hw 0 h0) hx
    · rw [Function.update_of_ne h]
      exact hw m hm
  have hsum0 : ∑ m ∈ s, Function.update w 0 (w 0 - x) m = 0 := by
    rw [Finset.sum_update_of_mem h0, hsum, ← Finset.add_sum_erase s w h0, Finset.erase_eq]
    abel
  have h := eq_zero_of_sum_mem_boostWeightSubmodule hv hsum0 0 h0
  rw [Function.update_self] at h
  exact (sub_eq_zero.1 h).symm

/-!

## B. Decomposing generators

We want to give the decomposition of
`T d` into peices along the three axis.
-/

/-- The axis-i weight-zero component of a component, as in `boostComponent`
    but one level down: the weight-m partial sum of `eq_sum_lightCone`. -/
noncomputable def monoComponent (i : Fin 3) (e : Fin 4 → Fin 1 ⊕ Fin 3) (m : ℤ) : B :=
  ∑ c ∈ Finset.univ.filter (fun c : Fin 4 → Fin 4 => (∑ s, lightConeWeight (c s)) = m),
    (∏ s, lightConeCoeffInv i (e s) (c s)) • hT.lightCone i c

lemma monoComponent_mem_boostWeightSubmodule (i : Fin 3) (e : Fin 4 → Fin 1 ⊕ Fin 3) (m : ℤ) :
    hT.monoComponent i e m ∈ boostWeightSubmodule repLorentz i m := by
  refine sum_mem fun c hc => Submodule.smul_mem _ _ ?_
  exact (show (∑ s, lightConeWeight (c s)) = m from (Finset.mem_filter.1 hc).2) ▸
    hT.lightCone_mem_boostWeightSubmodule i c

/-- **The possible axis-`i` boost weights of a component**: the total light-cone weights
  of the axis-`i` light-cone monomials appearing in `eq_sum_lightCone` with a nonzero
  coefficient — those reachable through slots where the integer mirror `lightConeCoeffZ`
  does not vanish. Computable, so membership can be settled by `decide`. -/
def boostSupport (i : Fin 3) (e : Fin 4 → Fin 1 ⊕ Fin 3) : Finset ℤ :=
  (Finset.univ.filter fun c : Fin 4 → Fin 4 =>
      ∀ s, lightConeCoeffZ i (c s) (e s) ≠ 0).image
    fun c => ∑ s, lightConeWeight (c s)

lemma eq_sum_monoComponent (i : Fin 3) (e : Fin 4 → Fin 1 ⊕ Fin 3) :
    T e = ∑ m ∈ boostSupport i e, hT.monoComponent i e m := by
  have hne : ∀ c : Fin 4 → Fin 4,
      ((∏ s, lightConeCoeffInv i (e s) (c s)) • hT.lightCone i c ≠ 0) →
      ∀ s, lightConeCoeffZ i (c s) (e s) ≠ 0 := fun c hc s hs =>
    absurd (by rw [Finset.prod_eq_zero (Finset.mem_univ s)
      (lightConeCoeffInv_eq_zero_of_coeffZ_eq_zero i (c s) (e s) hs), zero_smul]) hc
  calc T e
      = ∑ c : Fin 4 → Fin 4,
          (∏ s, lightConeCoeffInv i (e s) (c s)) • hT.lightCone i c :=
        hT.eq_sum_lightCone i e
    _ = ∑ c ∈ Finset.univ.filter (fun c : Fin 4 → Fin 4 =>
            ∀ s, lightConeCoeffZ i (c s) (e s) ≠ 0),
          (∏ s, lightConeCoeffInv i (e s) (c s)) • hT.lightCone i c :=
        (Finset.sum_filter_of_ne (fun c _ => hne c)).symm
    _ = ∑ m ∈ boostSupport i e,
          ∑ c ∈ (Finset.univ.filter (fun c : Fin 4 → Fin 4 =>
              ∀ s, lightConeCoeffZ i (c s) (e s) ≠ 0)).filter
            (fun c => (∑ s, lightConeWeight (c s)) = m),
          (∏ s, lightConeCoeffInv i (e s) (c s)) • hT.lightCone i c :=
        (Finset.sum_fiberwise_of_maps_to
          (fun c hc => Finset.mem_image_of_mem _ hc) _).symm
    _ = ∑ m ∈ boostSupport i e, hT.monoComponent i e m := by
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [Finset.filter_comm, monoComponent]
        exact Finset.sum_filter_of_ne fun c _ => hne c

set_option maxRecDepth 10000 in
/-- **A component is the sum of its weight components over the full weight set**: as
  `eq_sum_monoComponent` but over the fixed weight set common to all components. -/
lemma eq_sum_monoComponent_univ (i : Fin 3) (e : Fin 4 → Fin 1 ⊕ Fin 3) :
    T e = ∑ m ∈ ({-8, -6, -4, -2, 0, 2, 4, 6, 8} : Finset ℤ), hT.monoComponent i e m := by
  have hall : ∀ c : Fin 4 → Fin 4,
      (∑ s, lightConeWeight (c s)) ∈ ({-8, -6, -4, -2, 0, 2, 4, 6, 8} : Finset ℤ) := by
    decide
  rw [hT.eq_sum_lightCone i e]
  exact (Finset.sum_fiberwise_of_maps_to (fun c _ => hall c) _).symm

/-- **The matrix of the axis-`i` weight-zero projection in the `T`-basis**: the
  coefficient of `T d` in the re-expansion of `monoComponent i e 0` through the
  light-cone basis. Rational-valued and computable, built from the two mirrors. -/
def weightZeroTransition (i : Fin 3) (d e : Fin 4 → Fin 1 ⊕ Fin 3) : ℚ :=
  ∑ c ∈ Finset.univ.filter (fun c : Fin 4 → Fin 4 => (∑ s, lightConeWeight (c s)) = 0),
    ∏ s, lightConeCoeffInvQ i (e s) (c s) * (lightConeCoeffZ i (c s) (d s) : ℚ)

/-- **The weight-zero component re-expanded in the `T`-basis**: `monoComponent i e 0`
  is the `e`-th column of `weightZeroTransition` applied to the generators. -/
lemma monoComponent_zero_eq (i : Fin 3) (e : Fin 4 → Fin 1 ⊕ Fin 3) :
    hT.monoComponent i e 0
      = ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, ((weightZeroTransition i d e : ℚ) : ℂ) • T d := by
  rw [monoComponent]
  simp only [lightCone, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  rw [weightZeroTransition]
  push_cast
  simp only [coe_lightConeCoeffInvQ, coe_lightConeCoeffZ, Finset.prod_mul_distrib]

/-- **The boost-average matrix `M`**: the matrix of `3⁻¹(π₀⁰ + π₁⁰ + π₂⁰)` in the
  `T`-basis — the average over the three axes of the weight-zero transition matrices.
  Its powers drive the endgame recursion, and the certificate is a fixed rational
  combination of them. -/
def boostAverageTransition :
    Matrix (Fin 4 → Fin 1 ⊕ Fin 3) (Fin 4 → Fin 1 ⊕ Fin 3) ℚ :=
  Matrix.of fun d e => (3⁻¹ : ℚ) * ∑ i : Fin 3, weightZeroTransition i d e

include hT in
/-- **One round of the recursion along one axis**: an element of weight zero along axis
  `i` expanded in the generators re-expands with the weight-zero transition matrix
  applied to its coefficients — the nonzero-weight components of the expansion must
  vanish, and the surviving weight-zero part is `weightZeroTransition` acting on `c`. -/
lemma eq_sum_weightZeroTransition_smul (i : Fin 3) {x : B}
    (c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ) (hx : x = ∑ e, c e • T e)
    (hw : x ∈ boostWeightSubmodule repLorentz i 0) :
    x = ∑ d, (∑ e, ((weightZeroTransition i d e : ℚ) : ℂ) * c e) • T d := by
  have hsum : x = ∑ m ∈ ({-8, -6, -4, -2, 0, 2, 4, 6, 8} : Finset ℤ),
      ∑ e, c e • hT.monoComponent i e m := by
    rw [hx]
    calc ∑ e, c e • T e
        = ∑ e, c e • ∑ m ∈ ({-8, -6, -4, -2, 0, 2, 4, 6, 8} : Finset ℤ),
            hT.monoComponent i e m :=
          Finset.sum_congr rfl fun e _ => by rw [← hT.eq_sum_monoComponent_univ i e]
      _ = _ := by
          simp only [Finset.smul_sum]
          exact Finset.sum_comm
  have hx0 : x = ∑ e, c e • hT.monoComponent i e 0 :=
    eq_component_zero_of_mem_boostWeightSubmodule
      (w := fun m => ∑ e, c e • hT.monoComponent i e m) hw
      (fun m _ => sum_mem fun e _ => Submodule.smul_mem _ _
        (hT.monoComponent_mem_boostWeightSubmodule i e m))
      (by decide) hsum
  calc x = ∑ e, c e • hT.monoComponent i e 0 := hx0
    _ = ∑ e, c e • ∑ d, ((weightZeroTransition i d e : ℚ) : ℂ) • T d :=
        Finset.sum_congr rfl fun e _ => by rw [hT.monoComponent_zero_eq i e]
    _ = ∑ d, (∑ e, ((weightZeroTransition i d e : ℚ) : ℂ) * c e) • T d := by
        simp only [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [← Finset.sum_smul]
        congr 1
        exact Finset.sum_congr rfl fun e _ => mul_comm _ _

include hT in
/-- **One averaged round of the recursion**: an element of weight zero along all three
  axes re-expands with the boost-average matrix `M` applied to its coefficients — the
  average over the axes of `eq_sum_weightZeroTransition_smul`. -/
lemma eq_sum_boostAverageTransition_smul {x : B}
    (c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ) (hx : x = ∑ e, c e • T e)
    (hw : ∀ i : Fin 3, x ∈ boostWeightSubmodule repLorentz i 0) :
    x = ∑ d, (∑ e, ((boostAverageTransition d e : ℚ) : ℂ) * c e) • T d := by
  have hround : ∀ i : Fin 3,
      x = ∑ d, (∑ e, ((weightZeroTransition i d e : ℚ) : ℂ) * c e) • T d :=
    fun i => hT.eq_sum_weightZeroTransition_smul i c hx (hw i)
  have h3 : (3 : ℂ) • x = ∑ i : Fin 3, x := by
    rw [Fin.sum_univ_three, show (3 : ℂ) = 1 + 1 + 1 from by norm_num,
      add_smul, add_smul, one_smul]
  calc x = (3⁻¹ : ℂ) • ((3 : ℂ) • x) := by rw [smul_smul]; norm_num
    _ = (3⁻¹ : ℂ) • ∑ i : Fin 3, x := by rw [h3]
    _ = (3⁻¹ : ℂ) • ∑ i : Fin 3, ∑ d,
          (∑ e, ((weightZeroTransition i d e : ℚ) : ℂ) * c e) • T d :=
        congrArg (fun y => (3⁻¹ : ℂ) • y) (Finset.sum_congr rfl fun i _ => hround i)
    _ = ∑ d, (∑ e, ((boostAverageTransition d e : ℚ) : ℂ) * c e) • T d := by
        rw [Finset.sum_comm, Finset.smul_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [← Finset.sum_smul, smul_smul]
        congr 1
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        simp only [boostAverageTransition, Matrix.of_apply]
        push_cast
        rw [mul_assoc, Finset.sum_mul]

include hT in
/-- **Iterated averaged rounds**: an element of weight zero along all three axes
  re-expands through every power of the boost-average matrix applied to its
  coefficients. -/
lemma eq_sum_pow_boostAverageTransition_smul {x : B}
    (c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ) (hx : x = ∑ e, c e • T e)
    (hw : ∀ i : Fin 3, x ∈ boostWeightSubmodule repLorentz i 0) (n : ℕ) :
    x = ∑ d, (∑ e, (((boostAverageTransition ^ n) d e : ℚ) : ℂ) * c e) • T d := by
  induction n with
  | zero =>
    rw [hx]
    refine Finset.sum_congr rfl fun d _ => ?_
    congr 1
    rw [pow_zero]
    simp [Matrix.one_apply, apply_ite (fun q : ℚ => (q : ℂ)), ite_mul, Finset.sum_ite_eq]
  | succ n ih =>
    rw [hT.eq_sum_boostAverageTransition_smul
      (fun d => ∑ e, (((boostAverageTransition ^ n) d e : ℚ) : ℂ) * c e) ih hw]
    refine Finset.sum_congr rfl fun d _ => ?_
    congr 1
    rw [pow_succ']
    calc ∑ e, ((boostAverageTransition d e : ℚ) : ℂ)
          * ∑ f, (((boostAverageTransition ^ n) e f : ℚ) : ℂ) * c f
        = ∑ e, ∑ f, ((boostAverageTransition d e : ℚ) : ℂ)
            * ((((boostAverageTransition ^ n) e f : ℚ) : ℂ) * c f) :=
          Finset.sum_congr rfl fun e _ => by rw [Finset.mul_sum]
      _ = ∑ f, (∑ e, ((boostAverageTransition d e : ℚ) : ℂ)
            * (((boostAverageTransition ^ n) e f : ℚ) : ℂ)) * c f := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun f _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun e _ => (mul_assoc _ _ _).symm
      _ = ∑ e, (((boostAverageTransition * boostAverageTransition ^ n) d e : ℚ) : ℂ)
            * c e := by
          refine Finset.sum_congr rfl fun f _ => ?_
          congr 1
          rw [Matrix.mul_apply]
          push_cast
          rfl

/-!

## B. Pieces along one axis

-/

def boostPiece (i : Fin 3) (n : ℤ) : Submodule ℂ B :=
  ⨆ c ∈ {c : Fin 4 → Fin 4 | (∑ j, lightConeWeight (c j)) = n}, ℂ ∙ hT.lightCone i c

lemma boostPiece_le_boostWeightSubmodule (i : Fin 3) (n : ℤ) :
    hT.boostPiece i n ≤ boostWeightSubmodule repLorentz i n := by
  refine iSup₂_le fun c hc => ?_
  rw [Submodule.span_singleton_le_iff_mem]
  exact (show (∑ j, lightConeWeight (c j)) = n from hc) ▸
    hT.lightCone_mem_boostWeightSubmodule i c

/-- **The span regrouped by boost weight**: the light-cone components sorted by their
  total weight along the axis. -/
lemma span_eq_iSup_boostPiece (i : Fin 3) :
    hT.span = ⨆ n : ℤ, hT.boostPiece i n := by
  rw [hT.span_eq_lightCone i]
  refine le_antisymm (iSup_le fun c => ?_) (iSup_le fun n => iSup₂_le fun c _ => ?_)
  · exact le_iSup_of_le (∑ s, lightConeWeight (c s)) (le_iSup₂_of_le c rfl le_rfl)
  · exact le_iSup_of_le c le_rfl

/-!

## C. Pieces along a second axis

The axis-`i` and axis-`j` light-cone bases are related slot by slot by an invertible
`4 × 4` transition matrix. An axis-`i` piece is therefore covered by axis-`j` pieces
spanned by the light-cone components reachable through nonzero transition coefficients.

-/

/-- **The one-slot transition matrix between two light-cone bases**: the axis-`i`
  light-cone direction `κ` expanded in the axis-`j` light-cone basis. Rational-valued —
  the entries are `0`, `±2⁻¹` and `±1` — so that vanishing of entries is decidable;
  `coe_lightConeTransition` identifies it with the composite change of basis over `ℂ`. -/
def lightConeTransition (i j : Fin 3) (κ κ' : Fin 4) : ℚ :=
  if j = i then (if κ = κ' then 1 else 0)
  else if j = i + 1 then
    if κ = 0 then (if κ' = 0 ∨ κ' = 1 then 2⁻¹ else if κ' = 3 then -1 else 0)
    else if κ = 1 then (if κ' = 0 ∨ κ' = 1 then 2⁻¹ else if κ' = 3 then 1 else 0)
    else if κ = 2 then (if κ' = 0 then -2⁻¹ else if κ' = 1 then 2⁻¹ else 0)
    else (if κ' = 2 then 1 else 0)
  else
    if κ = 0 then (if κ' = 0 ∨ κ' = 1 then 2⁻¹ else if κ' = 2 then -1 else 0)
    else if κ = 1 then (if κ' = 0 ∨ κ' = 1 then 2⁻¹ else if κ' = 2 then 1 else 0)
    else if κ = 2 then (if κ' = 3 then 1 else 0)
    else (if κ' = 0 then -2⁻¹ else if κ' = 1 then 2⁻¹ else 0)

/-- **The transition matrix is the composite change of basis**: the axis-`i` light-cone
  coefficients composed with the inverse axis-`j` coefficients. -/
lemma coe_lightConeTransition (i j : Fin 3) (κ κ' : Fin 4) :
    (lightConeTransition i j κ κ' : ℂ)
      = ∑ μ : Fin 1 ⊕ Fin 3, lightConeCoeff i κ μ * lightConeCoeffInv j μ κ' := by
  fin_cases i <;> fin_cases j <;> fin_cases κ <;> fin_cases κ' <;>
    simp [lightConeTransition, lightConeCoeff, lightConeCoeffInv, Fintype.sum_sum_type,
      Fin.sum_univ_three] <;>
    norm_num

/-- Integer mirror of twice the transition matrix: the entries are `0`, `±1` and `±2`. -/
def lightConeTransitionZ (i j : Fin 3) (κ κ' : Fin 4) : ℤ :=
  if j = i then (if κ = κ' then 2 else 0)
  else if j = i + 1 then
    if κ = 0 then (if κ' = 0 ∨ κ' = 1 then 1 else if κ' = 3 then -2 else 0)
    else if κ = 1 then (if κ' = 0 ∨ κ' = 1 then 1 else if κ' = 3 then 2 else 0)
    else if κ = 2 then (if κ' = 0 then -1 else if κ' = 1 then 1 else 0)
    else (if κ' = 2 then 2 else 0)
  else
    if κ = 0 then (if κ' = 0 ∨ κ' = 1 then 1 else if κ' = 2 then -2 else 0)
    else if κ = 1 then (if κ' = 0 ∨ κ' = 1 then 1 else if κ' = 2 then 2 else 0)
    else if κ = 2 then (if κ' = 3 then 2 else 0)
    else (if κ' = 0 then -1 else if κ' = 1 then 1 else 0)

/-- The transition matrix is half its integer mirror. -/
lemma coe_lightConeTransition_eq (i j : Fin 3) (κ κ' : Fin 4) :
    ((lightConeTransition i j κ κ' : ℚ) : ℂ)
      = 2⁻¹ * ((lightConeTransitionZ i j κ κ' : ℤ) : ℂ) := by
  rw [lightConeTransition, lightConeTransitionZ]
  split_ifs <;> norm_num

/-- The transition coefficients of a multi-index factor slot by slot. -/
lemma sum_prod_lightConeTransition (i j : Fin 3) (c c' : Fin 4 → Fin 4) :
    ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, (∏ s, lightConeCoeff i (c s) (d s)) *
        (∏ s, lightConeCoeffInv j (d s) (c' s))
      = ∏ s, (lightConeTransition i j (c s) (c' s) : ℂ) := by
  calc ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, (∏ s, lightConeCoeff i (c s) (d s)) *
        (∏ s, lightConeCoeffInv j (d s) (c' s))
      = ∑ d : Fin 4 → Fin 1 ⊕ Fin 3,
          ∏ s, (lightConeCoeff i (c s) (d s) * lightConeCoeffInv j (d s) (c' s)) :=
        Finset.sum_congr rfl fun d _ => (Finset.prod_mul_distrib).symm
    _ = ∏ s, ∑ μ : Fin 1 ⊕ Fin 3,
          (lightConeCoeff i (c s) μ * lightConeCoeffInv j μ (c' s)) := by
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    _ = ∏ s, (lightConeTransition i j (c s) (c' s) : ℂ) :=
        Finset.prod_congr rfl fun s _ => (coe_lightConeTransition i j (c s) (c' s)).symm

/-- **The change-of-axis identity**: an axis-`i` light-cone component expanded in the
  axis-`j` light-cone basis, with slot-wise transition coefficients. -/
lemma lightCone_eq_sum_lightCone (i j : Fin 3) (c : Fin 4 → Fin 4) :
    hT.lightCone i c = ∑ c' : Fin 4 → Fin 4,
      (∏ s, (lightConeTransition i j (c s) (c' s) : ℂ)) • hT.lightCone j c' := by
  calc hT.lightCone i c
      = ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, (∏ s, lightConeCoeff i (c s) (d s)) • T d := by
        rw [lightCone]
    _ = ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, (∏ s, lightConeCoeff i (c s) (d s)) •
          ∑ c' : Fin 4 → Fin 4,
            (∏ s, lightConeCoeffInv j (d s) (c' s)) • hT.lightCone j c' :=
        Finset.sum_congr rfl fun d _ => by rw [← hT.eq_sum_lightCone j d]
    _ = ∑ c' : Fin 4 → Fin 4, (∑ d : Fin 4 → Fin 1 ⊕ Fin 3,
          (∏ s, lightConeCoeff i (c s) (d s)) *
            (∏ s, lightConeCoeffInv j (d s) (c' s))) • hT.lightCone j c' := by
        simp only [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c' _ => (Finset.sum_smul).symm
    _ = _ := Finset.sum_congr rfl fun c' _ => by rw [sum_prod_lightConeTransition]

/-- **The second-level pieces**: the axis-`j` light-cone components of weight `m` which
  are reachable, slot by slot, from an axis-`i` multi-index of weight `n`. -/
def boostPiece₂ (i j : Fin 3) (n m : ℤ) : Submodule ℂ B :=
  ⨆ c' ∈ {c' : Fin 4 → Fin 4 | (∑ s, lightConeWeight (c' s)) = m ∧
    ∃ c : Fin 4 → Fin 4, (∑ s, lightConeWeight (c s)) = n ∧
      ∀ s, lightConeTransition i j (c s) (c' s) ≠ 0}, ℂ ∙ hT.lightCone j c'

/-- Each second-level piece is contained in the boost-weight space of its weight along
  the second axis. -/
lemma boostPiece₂_le_boostWeightSubmodule (i j : Fin 3) (n m : ℤ) :
    hT.boostPiece₂ i j n m ≤ boostWeightSubmodule repLorentz j m := by
  refine iSup₂_le fun c' hc' => ?_
  rw [Submodule.span_singleton_le_iff_mem]
  exact (show (∑ s, lightConeWeight (c' s)) = m from hc'.1) ▸
    hT.lightCone_mem_boostWeightSubmodule j c'

/-- **The second-axis covering**: each axis-`i` piece is covered by the second-level
  pieces along the axis `j` — the change-of-axis coefficients vanish on unreachable
  multi-indices. -/
lemma boostPiece_le_iSup_boostPiece₂ (i j : Fin 3) (n : ℤ) :
    hT.boostPiece i n ≤ ⨆ m : ℤ, hT.boostPiece₂ i j n m := by
  refine iSup₂_le fun c hc => ?_
  rw [Submodule.span_singleton_le_iff_mem, hT.lightCone_eq_sum_lightCone i j c]
  refine sum_mem fun c' _ => ?_
  by_cases hz : ∀ s, lightConeTransition i j (c s) (c' s) ≠ 0
  · refine Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem (∑ s, lightConeWeight (c' s)) ?_)
    rw [boostPiece₂]
    exact Submodule.mem_iSup_of_mem c' (Submodule.mem_iSup_of_mem ⟨rfl, c, hc, hz⟩
      (Submodule.mem_span_singleton_self _))
  · push Not at hz
    obtain ⟨s, hs⟩ := hz
    rw [Finset.prod_eq_zero (Finset.mem_univ s) (by rw [hs, Rat.cast_zero]), zero_smul]
    exact Submodule.zero_mem _

/-!

## D. Tied pieces along the third axis

Covering the doubly-weight-zero part by spans of whole light-cone components stabilises:
no new multi-index is excluded along the third axis. The third round instead splits each
generator into its boost-weight components along the last axis — the tied combinations —
and takes the pieces spanned by those components.

-/

/-- **The axis-`j` weight-`m` component of an axis-`i` light-cone component**: the partial
  sum of its change-of-axis expansion over the axis-`j` multi-indices of weight `m`. -/
noncomputable def boostComponent (i j : Fin 3) (c : Fin 4 → Fin 4) (m : ℤ) : B :=
  ∑ c' ∈ Finset.univ.filter (fun c' : Fin 4 → Fin 4 => (∑ s, lightConeWeight (c' s)) = m),
    (∏ s, (lightConeTransition i j (c s) (c' s) : ℂ)) • hT.lightCone j c'

/-- Each component is a boost eigenvector of its weight: it is a combination of
  light-cone components of that weight. -/
lemma boostComponent_mem_boostWeightSubmodule (i j : Fin 3) (c : Fin 4 → Fin 4) (m : ℤ) :
    hT.boostComponent i j c m ∈ boostWeightSubmodule repLorentz j m := by
  refine sum_mem fun c' hc' => Submodule.smul_mem _ _ ?_
  exact (Finset.mem_filter.1 hc').2 ▸ hT.lightCone_mem_boostWeightSubmodule j c'

set_option maxRecDepth 10000 in
/-- **A light-cone component is the sum of its boost-weight components along any other
  axis**: the change-of-axis expansion regrouped by weight. -/
lemma lightCone_eq_sum_boostComponent (i j : Fin 3) (c : Fin 4 → Fin 4) :
    hT.lightCone i c
      = ∑ m ∈ ({-8, -6, -4, -2, 0, 2, 4, 6, 8} : Finset ℤ), hT.boostComponent i j c m := by
  have hall : ∀ c' : Fin 4 → Fin 4,
      (∑ s, lightConeWeight (c' s)) ∈ ({-8, -6, -4, -2, 0, 2, 4, 6, 8} : Finset ℤ) := by decide
  rw [hT.lightCone_eq_sum_lightCone i j c]
  exact (Finset.sum_fiberwise_of_maps_to (fun c' _ => hall c') _).symm

/-- **The tied pieces along the third axis**: for each generator of the doubly-weight-zero
  part, the span of its weight-`m` component along the last axis. -/
noncomputable def boostPiece₃ (m : ℤ) : Submodule ℂ B :=
  ⨆ c' ∈ {c' : Fin 4 → Fin 4 | (∑ s, lightConeWeight (c' s)) = 0 ∧
    ∃ c : Fin 4 → Fin 4, (∑ s, lightConeWeight (c s)) = 0 ∧
      ∀ s, lightConeTransition 0 1 (c s) (c' s) ≠ 0},
    ℂ ∙ hT.boostComponent 1 2 c' m

/-- Each tied piece is contained in the boost-weight space of its weight along the last
  axis. -/
lemma boostPiece₃_le_boostWeightSubmodule (m : ℤ) :
    hT.boostPiece₃ m ≤ boostWeightSubmodule repLorentz 2 m := by
  refine iSup₂_le fun c' _ => ?_
  rw [Submodule.span_singleton_le_iff_mem]
  exact hT.boostComponent_mem_boostWeightSubmodule 1 2 c' m

/-- **The third-axis covering**: the doubly-weight-zero part is covered by the tied
  pieces along the last axis. -/
lemma boostPiece₂_le_iSup_boostPiece₃ :
    hT.boostPiece₂ 0 1 0 0 ≤ ⨆ m : ℤ, hT.boostPiece₃ m := by
  refine iSup₂_le fun c' hc' => ?_
  rw [Submodule.span_singleton_le_iff_mem, hT.lightCone_eq_sum_boostComponent 1 2 c']
  refine sum_mem fun m _ => ?_
  refine Submodule.mem_iSup_of_mem m ?_
  rw [boostPiece₃]
  exact Submodule.mem_iSup_of_mem c' (Submodule.mem_iSup_of_mem hc'
    (Submodule.mem_span_singleton_self _))


/-!

## E. The support of the weight-zero tied piece

The weight-zero tied piece only involves components `T d` whose four indices either form
two identical pairs or are all different: the one-pair and three-of-a-kind monomials
cancel out of every tied generator. The cancellation is established by a sign involution:
swapping the two null directions in every slot of the inner light-cone index negates each
contributing term whenever a parity condition on the generator holds; the remaining cases
vanish slot by slot — a slot whose factor vanishes identically, or an odd null-sector
count, which no weight-zero inner index can accommodate. The finite checks are performed
by `decide` on the integer mirrors.

-/

/-- **The index vectors surviving the three boost sieves**: the four indices either split
  into two pairs of identical indices, or are all different. -/
def IsPairedOrDistinct (d : Fin 4 → Fin 1 ⊕ Fin 3) : Prop :=
  (d 0 = d 1 ∧ d 2 = d 3) ∨ (d 0 = d 2 ∧ d 1 = d 3) ∨ (d 0 = d 3 ∧ d 1 = d 2) ∨
    Function.Injective d

instance : DecidablePred IsPairedOrDistinct := fun d =>
  inferInstanceAs (Decidable ((d 0 = d 1 ∧ d 2 = d 3) ∨ (d 0 = d 2 ∧ d 1 = d 3) ∨
    (d 0 = d 3 ∧ d 1 = d 2) ∨ Function.Injective d))

/-- The swap of the two null light-cone directions. -/
def swap01 : Fin 4 → Fin 4 := fun κ => if κ = 0 then 1 else if κ = 1 then 0 else κ

/-- The sign by which the null swap changes a slot: `-1` exactly on the null-sector
  mismatches. -/
def nuZ (a : Fin 4) (μ : Fin 1 ⊕ Fin 3) : ℤ :=
  if μ = Sum.inl 0 then (if a = 2 then -1 else 1)
  else if μ = Sum.inr 2 then (if a = 0 ∨ a = 1 then -1 else 1)
  else 1

/-- The null swap is an involution. -/
lemma swap01_swap01 (κ : Fin 4) : swap01 (swap01 κ) = κ := by
  fin_cases κ <;> rfl

/-- The null swap negates the light-cone weight. -/
lemma lightConeWeight_swap01 (κ : Fin 4) :
    lightConeWeight (swap01 κ) = -lightConeWeight κ := by
  fin_cases κ <;> rfl

/-- **The slot identity of the sign involution**: swapping the null directions of the
  inner index multiplies the slot factor by the sign `nuZ`. -/
lemma transitionZ_swap01_mul_coeffZ :
    ∀ (a κ : Fin 4) (μ : Fin 1 ⊕ Fin 3),
      lightConeTransitionZ 1 2 a (swap01 κ) * lightConeCoeffZ 2 (swap01 κ) μ
        = nuZ a μ * (lightConeTransitionZ 1 2 a κ * lightConeCoeffZ 2 κ μ) := by
  decide

set_option maxRecDepth 40000 in
/-- **The odd-count case**: if the number of null-sector indices of `d` is odd, every
  weight-zero inner index hits a vanishing coefficient. -/
lemma exists_coeffZ_eq_zero_of_odd :
    ∀ d : Fin 4 → Fin 1 ⊕ Fin 3,
      Odd (Finset.univ.filter fun s => d s = Sum.inl 0 ∨ d s = Sum.inr 2).card →
      ∀ c'' : Fin 4 → Fin 4, (∑ s, lightConeWeight (c'' s)) = 0 →
      ∃ s, lightConeCoeffZ 2 (c'' s) (d s) = 0 := by
  decide

set_option maxRecDepth 40000 in
/-- **The parity of the sign involution**: over a weight-zero generator, a component that
  is neither two pairs nor all distinct, with no identically-vanishing slot and an even
  null-sector count, carries total sign `-1`. -/
lemma prod_nuZ_eq_neg_one :
    ∀ c' : Fin 4 → Fin 4, (∑ s, lightConeWeight (c' s)) = 0 →
    ∀ d : Fin 4 → Fin 1 ⊕ Fin 3, ¬IsPairedOrDistinct d →
    ¬(∃ s, ∀ κ, lightConeTransitionZ 1 2 (c' s) κ * lightConeCoeffZ 2 κ (d s) = 0) →
    ¬Odd (Finset.univ.filter fun s => d s = Sum.inl 0 ∨ d s = Sum.inr 2).card →
    (∏ s, nuZ (c' s) (d s)) = -1 := by
  suffices h1 : ∀ c' ∈ {c : Fin 4 → Fin 4 | (∑ s, lightConeWeight (c s)) = 0},
      ∀ d ∈  {d : Fin 4 → Fin 1 ⊕ Fin 3 | ¬IsPairedOrDistinct d
      ∧  ¬Odd (Finset.univ.filter fun s => d s = Sum.inl 0 ∨ d s = Sum.inr 2).card } ,
      ¬(∃ s, ∀ κ, lightConeTransitionZ 1 2 (c' s) κ * lightConeCoeffZ 2 κ (d s) = 0) →
      (∏ s, nuZ (c' s) (d s)) = -1 by
    intro c' hc' d hd hA hC
    exact h1 c' hc' d ⟨hd, hC⟩ hA
  decide

/-- **The vanishing of the bad coefficients**: over a weight-zero generator, the inner
  transition sum vanishes on every component that is neither two pairs nor all
  distinct — slot by slot when some slot factor vanishes identically or the null-sector
  count is odd, and by the sign involution otherwise. -/
lemma sum_prod_transitionZ_coeffZ_eq_zero (c' : Fin 4 → Fin 4)
    (hc' : (∑ s, lightConeWeight (c' s)) = 0)
    (d : Fin 4 → Fin 1 ⊕ Fin 3) (hd : ¬IsPairedOrDistinct d) :
    (∑ c'' ∈ Finset.univ.filter (fun c'' : Fin 4 → Fin 4 =>
        (∑ s, lightConeWeight (c'' s)) = 0),
      (∏ s, lightConeTransitionZ 1 2 (c' s) (c'' s)) *
        (∏ s, lightConeCoeffZ 2 (c'' s) (d s))) = 0 := by
  by_cases hA : ∃ s, ∀ κ, lightConeTransitionZ 1 2 (c' s) κ * lightConeCoeffZ 2 κ (d s) = 0
  · obtain ⟨s, hs⟩ := hA
    refine Finset.sum_eq_zero fun c'' _ => ?_
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_zero (Finset.mem_univ s) (hs (c'' s))
  by_cases hC : Odd (Finset.univ.filter fun s => d s = Sum.inl 0 ∨ d s = Sum.inr 2).card
  · refine Finset.sum_eq_zero fun c'' hc'' => ?_
    obtain ⟨s, hs⟩ := exists_coeffZ_eq_zero_of_odd d hC c'' (Finset.mem_filter.1 hc'').2
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
    rw [hs, mul_zero]
  have hsgn : (∏ s, nuZ (c' s) (d s)) = -1 := prod_nuZ_eq_neg_one c' hc' d hd hA hC
  have hswap : ∀ c'' : Fin 4 → Fin 4,
      (∏ s, lightConeTransitionZ 1 2 (c' s) (swap01 (c'' s))) *
        (∏ s, lightConeCoeffZ 2 (swap01 (c'' s)) (d s))
      = (∏ s, nuZ (c' s) (d s)) *
        ((∏ s, lightConeTransitionZ 1 2 (c' s) (c'' s)) *
          (∏ s, lightConeCoeffZ 2 (c'' s) (d s))) := by
    intro c''
    simp only [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun s _ => transitionZ_swap01_mul_coeffZ (c' s) (c'' s) (d s)
  have hwt : ∀ c'' : Fin 4 → Fin 4, (∑ s, lightConeWeight (swap01 (c'' s)))
      = -∑ s, lightConeWeight (c'' s) := fun c'' => by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun s _ => lightConeWeight_swap01 (c'' s)
  have hrei : (∑ c'' ∈ Finset.univ.filter (fun c'' : Fin 4 → Fin 4 =>
        (∑ s, lightConeWeight (c'' s)) = 0),
      (∏ s, lightConeTransitionZ 1 2 (c' s) (c'' s)) *
        (∏ s, lightConeCoeffZ 2 (c'' s) (d s)))
      = ∑ c'' ∈ Finset.univ.filter (fun c'' : Fin 4 → Fin 4 =>
        (∑ s, lightConeWeight (c'' s)) = 0),
      ((∏ s, lightConeTransitionZ 1 2 (c' s) (swap01 (c'' s))) *
        (∏ s, lightConeCoeffZ 2 (swap01 (c'' s)) (d s))) := by
    refine Finset.sum_nbij' (i := fun c'' => fun s => swap01 (c'' s))
      (j := fun c'' => fun s => swap01 (c'' s)) ?_ ?_ ?_ ?_ ?_
    · intro c'' hc''
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      rw [hwt, (Finset.mem_filter.1 hc'').2, neg_zero]
    · intro c'' hc''
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      rw [hwt, (Finset.mem_filter.1 hc'').2, neg_zero]
    · intro c'' _
      funext s
      rw [swap01_swap01]
    · intro c'' _
      funext s
      rw [swap01_swap01]
    · intro c'' _
      simp only [swap01_swap01]
  have hkey := hrei.trans ((Finset.sum_congr rfl fun c'' _ => hswap c'').trans
    (Finset.mul_sum _ _ _).symm)
  rw [hsgn] at hkey
  omega

/-!

### Rotation equivariance and support of the boost average

Rotating both indices of `weightZeroTransition` advances the axis, so the average over
the axes is rotation invariant.  And the transition out of a paired-or-distinct index
vanishes on every bad index: a sector-incompatible slot kills every summand, and
otherwise the null-swap involution carries sign `-1`.

-/

/-- Rotating the direction letter advances the axis of the light-cone coefficient. -/
lemma lightConeCoeffZ_cycDir :
    ∀ (i : Fin 3) (κ : Fin 4) (μ : Fin 1 ⊕ Fin 3),
      lightConeCoeffZ (i + 1) κ (cycDir μ) = lightConeCoeffZ i κ μ := by
  decide

/-- Integer mirror of `lightConeCoeffInvQ`: twice the inverse coefficients, so that
  slot identities can be settled by kernel `decide` over `ℤ`. -/
def lightConeCoeffInvZ (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) (κ : Fin 4) : ℤ :=
  if μ = Sum.inl 0 then (if κ = 0 then 1 else if κ = 1 then 1 else 0)
  else if μ = Sum.inr i then (if κ = 0 then -1 else if κ = 1 then 1 else 0)
  else if μ = Sum.inr (i + 1) then (if κ = 2 then 2 else 0)
  else (if κ = 3 then 2 else 0)

/-- The integer mirror casts to twice the inverse coefficients. -/
lemma coe_lightConeCoeffInvZ (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) (κ : Fin 4) :
    ((lightConeCoeffInvZ i μ κ : ℤ) : ℚ) = 2 * lightConeCoeffInvQ i μ κ := by
  rw [lightConeCoeffInvZ, lightConeCoeffInvQ]
  split_ifs <;> norm_num

/-- Rotating the direction letter advances the axis of the integer mirror. -/
lemma lightConeCoeffInvZ_cycDir :
    ∀ (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) (κ : Fin 4),
      lightConeCoeffInvZ (i + 1) (cycDir μ) κ = lightConeCoeffInvZ i μ κ := by
  decide

/-- Rotating the direction letter advances the axis of the inverse coefficient. -/
lemma lightConeCoeffInvQ_cycDir (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) (κ : Fin 4) :
    lightConeCoeffInvQ (i + 1) (cycDir μ) κ = lightConeCoeffInvQ i μ κ := by
  have h := congrArg (fun n : ℤ => (n : ℚ)) (lightConeCoeffInvZ_cycDir i μ κ)
  simp only [coe_lightConeCoeffInvZ] at h
  linarith

/-- **Rotation equivariance of the weight-zero transition**: rotating both indices
  advances the axis. -/
lemma weightZeroTransition_cycDir (i : Fin 3) (d e : Fin 4 → Fin 1 ⊕ Fin 3) :
    weightZeroTransition (i + 1) (fun s => cycDir (d s)) (fun s => cycDir (e s))
      = weightZeroTransition i d e := by
  rw [weightZeroTransition, weightZeroTransition]
  refine Finset.sum_congr rfl fun c _ => Finset.prod_congr rfl fun s _ => ?_
  rw [lightConeCoeffInvQ_cycDir, lightConeCoeffZ_cycDir]

/-- **Rotation invariance of the boost average**: the average over the axes is
  invariant under rotating both indices. -/
lemma boostAverageTransition_cycDir (d e : Fin 4 → Fin 1 ⊕ Fin 3) :
    boostAverageTransition (fun s => cycDir (d s)) (fun s => cycDir (e s))
      = boostAverageTransition d e := by
  simp only [boostAverageTransition, Matrix.of_apply]
  congr 1
  exact (Fintype.sum_equiv (Equiv.addRight (1 : Fin 3)) _ _ fun i =>
    (weightZeroTransition_cycDir i d e).symm).symm

/-- The cyclic rotation of directions has order three. -/
lemma cycDir_cycDir_cycDir : ∀ μ : Fin 1 ⊕ Fin 3, cycDir (cycDir (cycDir μ)) = μ := by
  decide

/-- Rotating the column index moves a double rotation to the row index. -/
lemma boostAverageTransition_cycDir_right (d e : Fin 4 → Fin 1 ⊕ Fin 3) :
    boostAverageTransition d (fun s => cycDir (e s))
      = boostAverageTransition (fun s => cycDir (cycDir (d s))) e := by
  conv_lhs => rw [show d = (fun s => cycDir (cycDir (cycDir (d s)))) from
    funext fun s => (cycDir_cycDir_cycDir (d s)).symm]
  exact boostAverageTransition_cycDir (fun s => cycDir (cycDir (d s))) e

/-- Rotating the column index twice moves a single rotation to the row index. -/
lemma boostAverageTransition_cycDir_right2 (d e : Fin 4 → Fin 1 ⊕ Fin 3) :
    boostAverageTransition d (fun s => cycDir (cycDir (e s)))
      = boostAverageTransition (fun s => cycDir (d s)) e := by
  calc boostAverageTransition d (fun s => cycDir (cycDir (e s)))
      = boostAverageTransition (fun s => cycDir (cycDir (d s))) (fun s => cycDir (e s)) :=
        boostAverageTransition_cycDir_right d (fun s => cycDir (e s))
    _ = boostAverageTransition (fun s => cycDir (d s)) e :=
        boostAverageTransition_cycDir (fun s => cycDir (d s)) e

/-- Two direction letters lie in compatible sectors for the axis-`i` transition: both
  in the null sector, or equal. -/
def SameSlotSector (i : Fin 3) (μ ν : Fin 1 ⊕ Fin 3) : Prop :=
  ((μ = Sum.inl 0 ∨ μ = Sum.inr i) ∧ (ν = Sum.inl 0 ∨ ν = Sum.inr i)) ∨ μ = ν

instance (i : Fin 3) (μ ν : Fin 1 ⊕ Fin 3) : Decidable (SameSlotSector i μ ν) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- A sector-incompatible slot annihilates every slot factor. -/
lemma slot_eq_zero_of_not_sameSlotSector :
    ∀ (i : Fin 3) (μ ν : Fin 1 ⊕ Fin 3), ¬SameSlotSector i μ ν →
      ∀ κ, lightConeCoeffInvQ i μ κ * (lightConeCoeffZ i κ ν : ℚ) = 0 := by
  decide +kernel

/-- The sign by which the null swap changes an axis-`i` slot factor. -/
def nuSignZ (i : Fin 3) (μ ν : Fin 1 ⊕ Fin 3) : ℤ :=
  (if μ = Sum.inr i then -1 else 1) * (if ν = Sum.inr i then -1 else 1)

/-- Swapping the null directions multiplies the slot factor by the sign. -/
lemma invQ_swap01_mul_coeffZ_swap01 :
    ∀ (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) (κ : Fin 4) (ν : Fin 1 ⊕ Fin 3),
      lightConeCoeffInvQ i μ (swap01 κ) * (lightConeCoeffZ i (swap01 κ) ν : ℚ)
        = (nuSignZ i μ ν : ℚ)
          * (lightConeCoeffInvQ i μ κ * (lightConeCoeffZ i κ ν : ℚ)) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **The sign of a sector-compatible parity mismatch**: a paired-or-distinct column
  index against a bad row index with all slots sector-compatible carries sign `-1`. -/
lemma prod_nuSignZ_eq_neg_one :
    ∀ (i : Fin 3) (e : Fin 4 → Fin 1 ⊕ Fin 3), IsPairedOrDistinct e →
    ∀ d : Fin 4 → Fin 1 ⊕ Fin 3, ¬IsPairedOrDistinct d →
    (∀ s, SameSlotSector i (e s) (d s)) →
    (∏ s, nuSignZ i (e s) (d s)) = -1 := by
  suffices h1 : ∀ i : Fin 3, ∀ e ∈ {e : Fin 4 → Fin 1 ⊕ Fin 3 | IsPairedOrDistinct e},
      ∀ d ∈ {d : Fin 4 → Fin 1 ⊕ Fin 3 | ¬IsPairedOrDistinct d},
      (∀ s, SameSlotSector i (e s) (d s)) → (∏ s, nuSignZ i (e s) (d s)) = -1 by
    intro i e he d hd hs
    exact h1 i e he d hd hs
  decide +kernel

/-- **Support of the weight-zero transition**: the transition out of a
  paired-or-distinct index vanishes on every bad index. -/
lemma weightZeroTransition_eq_zero_of_not_isPairedOrDistinct (i : Fin 3)
    {d e : Fin 4 → Fin 1 ⊕ Fin 3} (he : IsPairedOrDistinct e)
    (hd : ¬IsPairedOrDistinct d) : weightZeroTransition i d e = 0 := by
  by_cases hA : ∀ s, SameSlotSector i (e s) (d s)
  · have hsgn := prod_nuSignZ_eq_neg_one i e he d hd hA
    have hswap : ∀ c : Fin 4 → Fin 4,
        (∏ s, lightConeCoeffInvQ i (e s) (swap01 (c s)) *
          (lightConeCoeffZ i (swap01 (c s)) (d s) : ℚ))
        = ((∏ s, nuSignZ i (e s) (d s) : ℤ) : ℚ) *
          ∏ s, lightConeCoeffInvQ i (e s) (c s) * (lightConeCoeffZ i (c s) (d s) : ℚ) := by
      intro c
      push_cast
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun s _ => invQ_swap01_mul_coeffZ_swap01 i (e s) (c s) (d s)
    have hwt : ∀ c : Fin 4 → Fin 4, (∑ s, lightConeWeight (swap01 (c s)))
        = -∑ s, lightConeWeight (c s) := fun c => by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun s _ => lightConeWeight_swap01 (c s)
    have hrei : weightZeroTransition i d e
        = ∑ c ∈ Finset.univ.filter (fun c : Fin 4 → Fin 4 =>
            (∑ s, lightConeWeight (c s)) = 0),
          ∏ s, lightConeCoeffInvQ i (e s) (swap01 (c s)) *
            (lightConeCoeffZ i (swap01 (c s)) (d s) : ℚ) := by
      rw [weightZeroTransition]
      refine Finset.sum_nbij' (i := fun c => fun s => swap01 (c s))
        (j := fun c => fun s => swap01 (c s)) ?_ ?_ ?_ ?_ ?_
      · intro c hc
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by
          rw [hwt, (Finset.mem_filter.1 hc).2, neg_zero]⟩
      · intro c hc
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by
          rw [hwt, (Finset.mem_filter.1 hc).2, neg_zero]⟩
      · intro c _
        funext s
        rw [swap01_swap01]
      · intro c _
        funext s
        rw [swap01_swap01]
      · intro c _
        simp only [swap01_swap01]
    have hkey := hrei.trans ((Finset.sum_congr rfl fun c _ => hswap c).trans
      (Finset.mul_sum _ _ _).symm)
    rw [← weightZeroTransition, hsgn] at hkey
    push_cast at hkey
    linarith [hkey]
  · push Not at hA
    obtain ⟨s₀, hs₀⟩ := hA
    rw [weightZeroTransition]
    refine Finset.sum_eq_zero fun c _ => ?_
    exact Finset.prod_eq_zero (Finset.mem_univ s₀)
      (slot_eq_zero_of_not_sameSlotSector i (e s₀) (d s₀) hs₀ (c s₀))

/-- **Support of the boost average**: the average out of a paired-or-distinct index is
  supported on the paired-or-distinct indices. -/
lemma boostAverageTransition_eq_zero_of_not_isPairedOrDistinct
    {d e : Fin 4 → Fin 1 ⊕ Fin 3} (he : IsPairedOrDistinct e)
    (hd : ¬IsPairedOrDistinct d) : boostAverageTransition d e = 0 := by
  simp only [boostAverageTransition, Matrix.of_apply]
  rw [Finset.sum_eq_zero fun i _ =>
    weightZeroTransition_eq_zero_of_not_isPairedOrDistinct i he hd, mul_zero]

/-- **The expansion of the weight-zero tied component into monomials**: the coefficient
  of each component `T d` is a sixteenth of the integer transition sum. -/
lemma boostComponent_zero_eq (c' : Fin 4 → Fin 4) :
    hT.boostComponent 1 2 c' 0 = ∑ d : Fin 4 → Fin 1 ⊕ Fin 3,
      ((16⁻¹ : ℂ) * ((∑ c'' ∈ Finset.univ.filter (fun c'' : Fin 4 → Fin 4 =>
          (∑ s, lightConeWeight (c'' s)) = 0),
        (∏ s, lightConeTransitionZ 1 2 (c' s) (c'' s)) *
          (∏ s, lightConeCoeffZ 2 (c'' s) (d s)) : ℤ) : ℂ)) • T d := by
  rw [boostComponent]
  simp only [lightCone, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c'' _ => ?_
  simp only [coe_lightConeTransition_eq, ← coe_lightConeCoeffZ, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

/-- **The weight-zero tied component of every weight-zero generator is supported on the
  paired-or-distinct components.** -/
lemma boostComponent_zero_mem_iSup_pairedOrDistinct (c' : Fin 4 → Fin 4)
    (hc' : (∑ s, lightConeWeight (c' s)) = 0) :
    hT.boostComponent 1 2 c' 0 ∈
      ⨆ d ∈ {d : Fin 4 → Fin 1 ⊕ Fin 3 | IsPairedOrDistinct d}, ℂ ∙ T d := by
  rw [hT.boostComponent_zero_eq c']
  refine sum_mem fun d _ => ?_
  by_cases hd : IsPairedOrDistinct d
  · exact Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem d
      (Submodule.mem_iSup_of_mem hd (Submodule.mem_span_singleton_self _)))
  · rw [sum_prod_transitionZ_coeffZ_eq_zero c' hc' d hd, Int.cast_zero, mul_zero, zero_smul]
    exact Submodule.zero_mem _

/-- **The support of the weight-zero tied piece**: it is spanned by the components whose
  four indices either form two identical pairs or are all different. The one-pair and
  three-of-a-kind components cancel out of every tied generator. -/
lemma boostPiece₃_zero_le_iSup_pairedOrDistinct :
    hT.boostPiece₃ 0 ≤
      ⨆ d ∈ {d : Fin 4 → Fin 1 ⊕ Fin 3 | IsPairedOrDistinct d}, ℂ ∙ T d := by
  refine iSup₂_le fun c' hc' => ?_
  rw [Submodule.span_singleton_le_iff_mem]
  exact hT.boostComponent_zero_mem_iSup_pairedOrDistinct c' hc'.1

def pairedOrDistinctSubmodule : Submodule ℂ B :=
  ⨆ d ∈ {d : Fin 4 → Fin 1 ⊕ Fin 3 | IsPairedOrDistinct d}, ℂ ∙ T d


/-!

## F. The rotational group

-/

/-- **The rotation orbit of an index vector**: the indices that `d` is carried onto by
  the powers of the cyclic rotation `x → y → z → x` of the rotational average. -/
def rotationIndexSet (d : Fin 4 → Fin 1 ⊕ Fin 3) : Finset (Fin 4 → Fin 1 ⊕ Fin 3) :=
  {d, fun s => cycDir (d s), fun s => cycDir (cycDir (d s))}

/-- **The rotational average**: the mean of the action of the three powers of the cyclic
  rotation `x → y → z → x`. -/
noncomputable def rotationAverage : B →ₗ[ℂ] B :=
  (3⁻¹ : ℂ) • ((LinearMap.id : B →ₗ[ℂ] B) + repLorentz rotationCycle
    + repLorentz (rotationCycle ^ 2))

/-- **The action of the rotational average on the paired-or-distinct span**: the image of
  the weight-zero tied piece's support under averaging over the cyclic rotation. -/
noncomputable def rotationSubmodule : Submodule ℂ B :=
  (pairedOrDistinctSubmodule (T := T)).map (rotationAverage (repLorentz := repLorentz))

include hT in
/-- **The cyclic rotation acts on components by cycling every index.** -/
lemma repLorentz_rotationCycle_apply (d : Fin 4 → Fin 1 ⊕ Fin 3) :
    repLorentz rotationCycle (T d) = T (fun s => cycDir (d s)) := by
  have hcoef : ∀ a : Fin 4 → Fin 1 ⊕ Fin 3,
      (∏ s, (((SL2C.toLorentzGroup rotationCycle).1 (a s) (d s) : ℝ) : ℂ))
        = if a = fun s => cycDir (d s) then 1 else 0 := by
    intro a
    by_cases had : a = fun s => cycDir (d s)
    · rw [if_pos had]
      refine Finset.prod_eq_one fun s _ => ?_
      rw [toLorentzGroup_rotationCycle_apply, if_pos (congrFun had s), Complex.ofReal_one]
    · rw [if_neg had]
      obtain ⟨s, hs⟩ := Function.ne_iff.1 had
      refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
      rw [toLorentzGroup_rotationCycle_apply, if_neg hs, Complex.ofReal_zero]
  rw [hT.repLorentz_T]
  simp only [hcoef, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]

/-- **The sum of a component over its rotation orbit** — the un-normalised rotational
  average of `T d`. Its support is `rotationIndexSet d`. -/
noncomputable def rotationOrbitSum (d : Fin 4 → Fin 1 ⊕ Fin 3) : B :=
  T d + T (fun s => cycDir (d s)) + T (fun s => cycDir (cycDir (d s)))

include hT in
/-- The rotational average carries a component to a third of its orbit sum. -/
lemma rotationAverage_apply (d : Fin 4 → Fin 1 ⊕ Fin 3) :
    rotationAverage (repLorentz := repLorentz) (T d)
      = (3⁻¹ : ℂ) • rotationOrbitSum (T := T) d := by
  rw [rotationAverage, sq, map_mul, rotationOrbitSum]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
    Module.End.mul_apply, hT.repLorentz_rotationCycle_apply]

include hT in
/-- **The rotational average of the paired-or-distinct span, presented by orbit
  sums.** -/
lemma rotationSubmodule_eq :
    rotationSubmodule (repLorentz := repLorentz) (T := T)
      = ⨆ d ∈ {d : Fin 4 → Fin 1 ⊕ Fin 3 | IsPairedOrDistinct d},
          ℂ ∙ rotationOrbitSum (T := T) d := by
  rw [rotationSubmodule, pairedOrDistinctSubmodule]
  simp only [Submodule.map_iSup]
  refine iSup_congr fun d => iSup_congr fun hd => ?_
  rw [Submodule.map_span, Set.image_singleton, hT.rotationAverage_apply d]
  exact Submodule.span_singleton_smul_eq ((by norm_num : (3⁻¹ : ℂ) ≠ 0).isUnit) _

include hT in
/-- **Extraction from the rotational average**: an element of the averaged span is a
  combination of the orbit sums of the paired-or-distinct components. -/
lemma exists_eq_sum_of_mem_rotationSubmodule {x : B}
    (hx : x ∈ rotationSubmodule (repLorentz := repLorentz) (T := T)) :
    ∃ c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ,
      x = ∑ d ∈ Finset.univ.filter (fun d : Fin 4 → Fin 1 ⊕ Fin 3 => IsPairedOrDistinct d),
        c d • rotationOrbitSum (T := T) d := by
  rw [hT.rotationSubmodule_eq] at hx
  refine Submodule.iSup_induction
    (motive := fun y => ∃ c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ,
      y = ∑ d ∈ Finset.univ.filter (fun d : Fin 4 → Fin 1 ⊕ Fin 3 => IsPairedOrDistinct d),
        c d • rotationOrbitSum (T := T) d)
    (fun d => ⨆ _ : d ∈ {d : Fin 4 → Fin 1 ⊕ Fin 3 | IsPairedOrDistinct d},
      ℂ ∙ rotationOrbitSum (T := T) d) hx ?_ ?_ ?_
  · intro d y hy
    by_cases hd : IsPairedOrDistinct d
    · rw [iSup_pos (show d ∈ {d : Fin 4 → Fin 1 ⊕ Fin 3 | IsPairedOrDistinct d}
        from hd)] at hy
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
      refine ⟨fun e => if e = d then a else 0, ?_⟩
      simp [ite_smul, Finset.sum_ite_eq', hd]
    · rw [iSup_neg (show d ∉ {d : Fin 4 → Fin 1 ⊕ Fin 3 | IsPairedOrDistinct d}
        from hd)] at hy
      rw [Submodule.mem_bot] at hy
      exact ⟨0, by simp [hy]⟩
  · exact ⟨0, by simp⟩
  · rintro y z ⟨c₁, rfl⟩ ⟨c₂, rfl⟩
    exact ⟨c₁ + c₂, by simp [add_smul, Finset.sum_add_distrib]⟩

/-!

### Orbit representatives

`rotationOrbitSum` is constant on rotation orbits, so the extraction over all
paired-or-distinct indices collapses to one term per orbit.  The canonical
representative of an orbit is the member whose first spatial letter is the first
spatial direction; `rotationSubset` lists the `22` representatives explicitly.

-/

omit [Algebra ℂ B] in
/-- The orbit sum is invariant under rotating the index. -/
lemma rotationOrbitSum_cycDir (d : Fin 4 → Fin 1 ⊕ Fin 3) :
    rotationOrbitSum (T := T) (fun s => cycDir (d s)) = rotationOrbitSum (T := T) d := by
  simp only [rotationOrbitSum]
  rw [show (fun s => cycDir (cycDir (cycDir (d s)))) = d from
    funext fun s => cycDir_cycDir_cycDir (d s)]
  abel

/-- An index is the canonical representative of its rotation orbit when its first
  spatial letter, if any, is the first spatial direction. -/
def IsOrbitRep (d : Fin 4 → Fin 1 ⊕ Fin 3) : Prop :=
  (∀ s, d s = Sum.inl 0) ∨ ∃ s, d s = Sum.inr 0 ∧ ∀ s' < s, d s' = Sum.inl 0

instance : DecidablePred IsOrbitRep := fun d =>
  inferInstanceAs (Decidable
    ((∀ s, d s = Sum.inl 0) ∨ ∃ s, d s = Sum.inr 0 ∧ ∀ s' < s, d s' = Sum.inl 0))

/-- The canonical representative of the rotation orbit of an index. -/
def orbitRepOf (d : Fin 4 → Fin 1 ⊕ Fin 3) : Fin 4 → Fin 1 ⊕ Fin 3 :=
  if IsOrbitRep d then d
  else if IsOrbitRep (fun s => cycDir (d s)) then fun s => cycDir (d s)
  else fun s => cycDir (cycDir (d s))

omit [Algebra ℂ B] in
/-- The orbit sum of an index equals that of its canonical representative. -/
lemma rotationOrbitSum_orbitRepOf (d : Fin 4 → Fin 1 ⊕ Fin 3) :
    rotationOrbitSum (T := T) (orbitRepOf d) = rotationOrbitSum (T := T) d := by
  rw [orbitRepOf]
  split_ifs
  · rfl
  · exact rotationOrbitSum_cycDir (T := T) d
  · exact (rotationOrbitSum_cycDir (T := T) _).trans (rotationOrbitSum_cycDir (T := T) d)

/-- The `22` canonical orbit representatives of the paired-or-distinct indices under
  cyclic rotation. -/
def rotationSubset : Finset (Fin 4 → Fin 1 ⊕ Fin 3) :=
  {![Sum.inl 0, Sum.inl 0, Sum.inl 0, Sum.inl 0],
    ![Sum.inl 0, Sum.inl 0, Sum.inr 0, Sum.inr 0],
    ![Sum.inl 0, Sum.inr 0, Sum.inl 0, Sum.inr 0],
    ![Sum.inl 0, Sum.inr 0, Sum.inr 0, Sum.inl 0],
    ![Sum.inl 0, Sum.inr 0, Sum.inr 1, Sum.inr 2],
    ![Sum.inl 0, Sum.inr 0, Sum.inr 2, Sum.inr 1],
    ![Sum.inr 0, Sum.inl 0, Sum.inl 0, Sum.inr 0],
    ![Sum.inr 0, Sum.inl 0, Sum.inr 0, Sum.inl 0],
    ![Sum.inr 0, Sum.inl 0, Sum.inr 1, Sum.inr 2],
    ![Sum.inr 0, Sum.inl 0, Sum.inr 2, Sum.inr 1],
    ![Sum.inr 0, Sum.inr 0, Sum.inl 0, Sum.inl 0],
    ![Sum.inr 0, Sum.inr 0, Sum.inr 0, Sum.inr 0],
    ![Sum.inr 0, Sum.inr 0, Sum.inr 1, Sum.inr 1],
    ![Sum.inr 0, Sum.inr 0, Sum.inr 2, Sum.inr 2],
    ![Sum.inr 0, Sum.inr 1, Sum.inl 0, Sum.inr 2],
    ![Sum.inr 0, Sum.inr 1, Sum.inr 0, Sum.inr 1],
    ![Sum.inr 0, Sum.inr 1, Sum.inr 1, Sum.inr 0],
    ![Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inl 0],
    ![Sum.inr 0, Sum.inr 2, Sum.inl 0, Sum.inr 1],
    ![Sum.inr 0, Sum.inr 2, Sum.inr 0, Sum.inr 2],
    ![Sum.inr 0, Sum.inr 2, Sum.inr 1, Sum.inl 0],
    ![Sum.inr 0, Sum.inr 2, Sum.inr 2, Sum.inr 0]}

set_option maxRecDepth 10000 in
/-- The canonical representative of a paired-or-distinct index is one of the `22`
  listed representatives. -/
lemma orbitRepOf_mem_rotationSubset :
    ∀ d : Fin 4 → Fin 1 ⊕ Fin 3, IsPairedOrDistinct d →
      orbitRepOf d ∈ rotationSubset := by
  decide

include hT in
/-- **Extraction over unique orbit representatives**: an element of the rotational
  average is a combination of the orbit sums of the `22` canonical representatives —
  one term per orbit. -/
lemma exists_eq_sum_rotationSubset_of_mem_rotationSubmodule {x : B}
    (hx : x ∈ rotationSubmodule (repLorentz := repLorentz) (T := T)) :
    ∃ c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ,
      x = ∑ d ∈ rotationSubset, c d • rotationOrbitSum (T := T) d := by
  obtain ⟨c, rfl⟩ := hT.exists_eq_sum_of_mem_rotationSubmodule hx
  refine ⟨fun r => ∑ d ∈ (Finset.univ.filter
      (fun d : Fin 4 → Fin 1 ⊕ Fin 3 => IsPairedOrDistinct d)).filter
      (fun d => orbitRepOf d = r), c d, ?_⟩
  calc ∑ d ∈ Finset.univ.filter (fun d : Fin 4 → Fin 1 ⊕ Fin 3 => IsPairedOrDistinct d),
        c d • rotationOrbitSum (T := T) d
      = ∑ r ∈ rotationSubset, ∑ d ∈ (Finset.univ.filter
            (fun d : Fin 4 → Fin 1 ⊕ Fin 3 => IsPairedOrDistinct d)).filter
            (fun d => orbitRepOf d = r),
          c d • rotationOrbitSum (T := T) d :=
        (Finset.sum_fiberwise_of_maps_to (fun d hd =>
          orbitRepOf_mem_rotationSubset d (Finset.mem_filter.1 hd).2) _).symm
    _ = _ := by
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun d hd => ?_
        rw [show rotationOrbitSum (T := T) r = rotationOrbitSum (T := T) d from
          (Finset.mem_filter.1 hd).2 ▸ rotationOrbitSum_orbitRepOf (T := T) d]

/-- The listed representatives are paired-or-distinct. -/
lemma isPairedOrDistinct_of_mem_rotationSubset :
    ∀ d ∈ rotationSubset, IsPairedOrDistinct d := by
  decide +kernel

/-- Goodness is preserved by rotating the index. -/
lemma isPairedOrDistinct_cycDir :
    ∀ d : Fin 4 → Fin 1 ⊕ Fin 3, IsPairedOrDistinct d →
      IsPairedOrDistinct (fun s => cycDir (d s)) := by
  decide +kernel

/-- The multiplicity with which `d` appears among the three rotations of `e`. -/
def rotationOrbitCoeff (e d : Fin 4 → Fin 1 ⊕ Fin 3) : ℤ :=
  (if d = e then 1 else 0) + (if d = (fun s => cycDir (e s)) then 1 else 0)
    + (if d = (fun s => cycDir (cycDir (e s))) then 1 else 0)

/-- Only members of the orbit of a listed representative meet its indicator. -/
lemma orbitRepOf_eq_of_rotationOrbitCoeff_ne_zero :
    ∀ r ∈ rotationSubset, ∀ d : Fin 4 → Fin 1 ⊕ Fin 3,
      rotationOrbitCoeff r d ≠ 0 → orbitRepOf d = r := by
  decide +kernel

/-- The orbit of the canonical representative is the orbit. -/
lemma rotationIndexSet_orbitRepOf :
    ∀ d : Fin 4 → Fin 1 ⊕ Fin 3,
      rotationIndexSet (orbitRepOf d) = rotationIndexSet d := by
  decide +kernel

/-- The multiplicity of an index in its own orbit: `3` on a rotation-fixed index and
  `1` otherwise. -/
lemma rotationOrbitCoeff_orbitRepOf :
    ∀ d : Fin 4 → Fin 1 ⊕ Fin 3, rotationOrbitCoeff (orbitRepOf d) d
      = if (fun s => cycDir (d s)) = d then 3 else 1 := by
  decide +kernel

/-- An index not fixed by the rotation has three distinct rotations. -/
lemma cycDir_orbit_distinct :
    ∀ d : Fin 4 → Fin 1 ⊕ Fin 3, (fun s => cycDir (d s)) ≠ d →
      ((fun s => cycDir (cycDir (d s))) ≠ d
        ∧ (fun s => cycDir (cycDir (d s))) ≠ (fun s => cycDir (d s))) := by
  decide +kernel

/-- The orbit indicator of a good index vanishes on every bad index. -/
lemma rotationOrbitCoeff_eq_zero {r d : Fin 4 → Fin 1 ⊕ Fin 3}
    (hr : IsPairedOrDistinct r) (hd : ¬IsPairedOrDistinct d) :
    rotationOrbitCoeff r d = 0 := by
  have h1 : ¬(d = r) := fun h => hd (by rw [h]; exact hr)
  have h2 : ¬(d = fun s => cycDir (r s)) := fun h =>
    hd (by rw [h]; exact isPairedOrDistinct_cycDir r hr)
  have h3 : ¬(d = fun s => cycDir (cycDir (r s))) := fun h =>
    hd (by rw [h]; exact isPairedOrDistinct_cycDir _ (isPairedOrDistinct_cycDir r hr))
  rw [rotationOrbitCoeff, if_neg h1, if_neg h2, if_neg h3]
  norm_num

/-- **Sums over the orbit of the representative**: for any weighting, the sum over the
  orbit of the canonical representative times the multiplicity equals the plain sum
  over the three rotations. -/
lemma sum_rotationIndexSet_orbitRepOf_mul (f : (Fin 4 → Fin 1 ⊕ Fin 3) → ℚ)
    (d : Fin 4 → Fin 1 ⊕ Fin 3) :
    (∑ d' ∈ rotationIndexSet (orbitRepOf d), f d')
        * ((rotationOrbitCoeff (orbitRepOf d) d : ℤ) : ℚ)
      = f d + f (fun s => cycDir (d s)) + f (fun s => cycDir (cycDir (d s))) := by
  rw [rotationIndexSet_orbitRepOf d, rotationOrbitCoeff_orbitRepOf d]
  by_cases hfix : (fun s => cycDir (d s)) = d
  · have h2 : (fun s => cycDir (cycDir (d s))) = d := by
      funext s
      rw [congrFun hfix s, congrFun hfix s]
    rw [rotationIndexSet, if_pos hfix, hfix, h2,
      show ({d, d, d} : Finset (Fin 4 → Fin 1 ⊕ Fin 3)) = {d} from by simp,
      Finset.sum_singleton]
    push_cast
    ring
  · obtain ⟨h31, h32⟩ := cycDir_orbit_distinct d hfix
    rw [rotationIndexSet, if_neg hfix,
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨fun h => hfix h.symm, fun h => h31 h.symm⟩),
      Finset.sum_insert (by
        simp only [Finset.mem_singleton]
        exact fun h => h32 h.symm),
      Finset.sum_singleton]
    push_cast
    ring

/-- **The rotated columns collapse onto the representatives**: for a good column index,
  the sum of the boost average over the three rotated columns equals the
  representative-indexed combination of its row-orbit sums. -/
lemma boostAverageTransition_orbit_eq (e : Fin 4 → Fin 1 ⊕ Fin 3)
    (he : IsPairedOrDistinct e) (d : Fin 4 → Fin 1 ⊕ Fin 3) :
    boostAverageTransition d e + boostAverageTransition d (fun s => cycDir (e s))
        + boostAverageTransition d (fun s => cycDir (cycDir (e s)))
      = ∑ r ∈ rotationSubset,
          (∑ d' ∈ rotationIndexSet r, boostAverageTransition d' e)
            * ((rotationOrbitCoeff r d : ℤ) : ℚ) := by
  by_cases hd : IsPairedOrDistinct d
  · have hsingle : (∑ r ∈ rotationSubset,
        (∑ d' ∈ rotationIndexSet r, boostAverageTransition d' e)
          * ((rotationOrbitCoeff r d : ℤ) : ℚ))
        = (∑ d' ∈ rotationIndexSet (orbitRepOf d), boostAverageTransition d' e)
          * ((rotationOrbitCoeff (orbitRepOf d) d : ℤ) : ℚ) :=
      Finset.sum_eq_single_of_mem _ (orbitRepOf_mem_rotationSubset d hd)
        (fun r hr hne => by
          rcases eq_or_ne (rotationOrbitCoeff r d) 0 with h0 | h0
          · rw [h0]
            push_cast
            ring
          · exact absurd (orbitRepOf_eq_of_rotationOrbitCoeff_ne_zero r hr d h0).symm hne)
    rw [hsingle,
      sum_rotationIndexSet_orbitRepOf_mul (fun d' => boostAverageTransition d' e) d,
      boostAverageTransition_cycDir_right, boostAverageTransition_cycDir_right2]
    ring
  · have hs1 := isPairedOrDistinct_cycDir e he
    have hs2 := isPairedOrDistinct_cycDir _ hs1
    have hz : (∑ r ∈ rotationSubset,
        (∑ d' ∈ rotationIndexSet r, boostAverageTransition d' e)
          * ((rotationOrbitCoeff r d : ℤ) : ℚ)) = 0 :=
      Finset.sum_eq_zero fun r hr => by
        rw [rotationOrbitCoeff_eq_zero
          (isPairedOrDistinct_of_mem_rotationSubset r hr) hd]
        push_cast
        ring
    rw [hz, boostAverageTransition_eq_zero_of_not_isPairedOrDistinct he hd,
      boostAverageTransition_eq_zero_of_not_isPairedOrDistinct hs1 hd,
      boostAverageTransition_eq_zero_of_not_isPairedOrDistinct hs2 hd]
    norm_num

/-- **Orbit-sum expansions in components**: a combination of orbit sums over the
  representatives, expanded into the generators through the orbit indicator. -/
lemma sum_rotationSubset_smul_rotationOrbitSum (b : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ) :
    ∑ d ∈ rotationSubset, b d • rotationOrbitSum (T := T) d
      = ∑ e : Fin 4 → Fin 1 ⊕ Fin 3,
          (∑ d ∈ rotationSubset, b d * ((rotationOrbitCoeff d e : ℤ) : ℂ)) • T e := by
  calc ∑ d ∈ rotationSubset, b d • rotationOrbitSum (T := T) d
      = ∑ d ∈ rotationSubset, ∑ e : Fin 4 → Fin 1 ⊕ Fin 3,
          (b d * ((rotationOrbitCoeff d e : ℤ) : ℂ)) • T e := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [rotationOrbitSum]
        simp [rotationOrbitCoeff, apply_ite (fun n : ℤ => (n : ℂ)), mul_add, add_smul,
          mul_ite, ite_smul, Finset.sum_add_distrib, Finset.sum_ite_eq', smul_add]
    _ = _ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun e _ => (Finset.sum_smul).symm

include hT in
/-- **One averaged round at orbit level**: an element of weight zero along all three
  axes expanded over the orbit sums of the representatives re-expands through the
  row-orbit sums of the boost average — the matrix of the boost average acting on the
  orbit-sum span. -/
lemma eq_sum_boostAverageTransition_of_mem_rotationSubset {x : B}
    (c : (Fin 4 → Fin 1 ⊕ Fin 3) → ℂ)
    (hx : x = ∑ d ∈ rotationSubset, c d • rotationOrbitSum (T := T) d)
    (hw : ∀ i : Fin 3, x ∈ boostWeightSubmodule repLorentz i 0) :
    x = ∑ d ∈ rotationSubset, (∑ e ∈ rotationSubset,
      ((∑ d' ∈ rotationIndexSet d, boostAverageTransition d' e : ℚ) : ℂ) * c e)
        • rotationOrbitSum (T := T) d := by
  have hxT := hx.trans (sum_rotationSubset_smul_rotationOrbitSum (T := T) c)
  have hround := hT.eq_sum_boostAverageTransition_smul _ hxT hw
  rw [hround, sum_rotationSubset_smul_rotationOrbitSum (T := T)]
  refine Finset.sum_congr rfl fun d _ => ?_
  congr 1
  calc ∑ e : Fin 4 → Fin 1 ⊕ Fin 3, ((boostAverageTransition d e : ℚ) : ℂ)
        * (∑ r ∈ rotationSubset, c r * ((rotationOrbitCoeff r e : ℤ) : ℂ))
      = ∑ r ∈ rotationSubset, c r * ∑ e : Fin 4 → Fin 1 ⊕ Fin 3,
          ((boostAverageTransition d e : ℚ) : ℂ) * ((rotationOrbitCoeff r e : ℤ) : ℂ) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun e _ => ?_
        ring
    _ = ∑ r ∈ rotationSubset, c r
          * ((boostAverageTransition d r + boostAverageTransition d (fun s => cycDir (r s))
            + boostAverageTransition d (fun s => cycDir (cycDir (r s))) : ℚ) : ℂ) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        congr 1
        push_cast
        simp [rotationOrbitCoeff, apply_ite (fun n : ℤ => (n : ℂ)), mul_add, mul_ite,
          Finset.sum_add_distrib, Finset.sum_ite_eq']
    _ = ∑ r ∈ rotationSubset, c r * ((∑ ρ ∈ rotationSubset,
          (∑ d' ∈ rotationIndexSet ρ, boostAverageTransition d' r)
            * ((rotationOrbitCoeff ρ d : ℤ) : ℚ) : ℚ) : ℂ) := by
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [boostAverageTransition_orbit_eq r
          (isPairedOrDistinct_of_mem_rotationSubset r hr) d]
    _ = _ := by
        push_cast
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun e _ => ?_
        ring

/-!

### The boost average as an integer `22 × 22` matrix

The representatives are enumerated by `Fin 22`, and the row-orbit sums of the boost
average, scaled by `48`, form an integer matrix defined directly from the integer
mirrors — the matrix of the boost average acting on the orbit-sum span.

-/

/-- The enumeration of the `22` canonical orbit representatives, in the order of
  `rotationSubset`. -/
def orbitRep : Fin 22 → Fin 4 → Fin 1 ⊕ Fin 3 :=
  ![![Sum.inl 0, Sum.inl 0, Sum.inl 0, Sum.inl 0],
    ![Sum.inl 0, Sum.inl 0, Sum.inr 0, Sum.inr 0],
    ![Sum.inl 0, Sum.inr 0, Sum.inl 0, Sum.inr 0],
    ![Sum.inl 0, Sum.inr 0, Sum.inr 0, Sum.inl 0],
    ![Sum.inl 0, Sum.inr 0, Sum.inr 1, Sum.inr 2],
    ![Sum.inl 0, Sum.inr 0, Sum.inr 2, Sum.inr 1],
    ![Sum.inr 0, Sum.inl 0, Sum.inl 0, Sum.inr 0],
    ![Sum.inr 0, Sum.inl 0, Sum.inr 0, Sum.inl 0],
    ![Sum.inr 0, Sum.inl 0, Sum.inr 1, Sum.inr 2],
    ![Sum.inr 0, Sum.inl 0, Sum.inr 2, Sum.inr 1],
    ![Sum.inr 0, Sum.inr 0, Sum.inl 0, Sum.inl 0],
    ![Sum.inr 0, Sum.inr 0, Sum.inr 0, Sum.inr 0],
    ![Sum.inr 0, Sum.inr 0, Sum.inr 1, Sum.inr 1],
    ![Sum.inr 0, Sum.inr 0, Sum.inr 2, Sum.inr 2],
    ![Sum.inr 0, Sum.inr 1, Sum.inl 0, Sum.inr 2],
    ![Sum.inr 0, Sum.inr 1, Sum.inr 0, Sum.inr 1],
    ![Sum.inr 0, Sum.inr 1, Sum.inr 1, Sum.inr 0],
    ![Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inl 0],
    ![Sum.inr 0, Sum.inr 2, Sum.inl 0, Sum.inr 1],
    ![Sum.inr 0, Sum.inr 2, Sum.inr 0, Sum.inr 2],
    ![Sum.inr 0, Sum.inr 2, Sum.inr 1, Sum.inl 0],
    ![Sum.inr 0, Sum.inr 2, Sum.inr 2, Sum.inr 0]]

/-- The enumeration of the representatives is injective. -/
lemma orbitRep_injective : Function.Injective orbitRep := by
  decide +kernel

/-- The set of representatives is the image of the enumeration. -/
lemma rotationSubset_eq_image :
    rotationSubset = Finset.univ.image orbitRep := by
  decide +kernel

/-- Sums over the representatives reindexed through the enumeration. -/
lemma sum_rotationSubset {β : Type*} [AddCommMonoid β]
    (f : (Fin 4 → Fin 1 ⊕ Fin 3) → β) :
    ∑ d ∈ rotationSubset, f d = ∑ k : Fin 22, f (orbitRep k) := by
  rw [rotationSubset_eq_image, Finset.sum_image fun k _ k' _ h => orbitRep_injective h]

/-- Integer mirror of the weight-zero transition: sixteen times its value. -/
def weightZeroTransitionZ (i : Fin 3) (d e : Fin 4 → Fin 1 ⊕ Fin 3) : ℤ :=
  ∑ c ∈ Finset.univ.filter (fun c : Fin 4 → Fin 4 => (∑ s, lightConeWeight (c s)) = 0),
    ∏ s, lightConeCoeffInvZ i (e s) (c s) * lightConeCoeffZ i (c s) (d s)

/-- The integer mirror casts to sixteen times the weight-zero transition. -/
lemma coe_weightZeroTransitionZ (i : Fin 3) (d e : Fin 4 → Fin 1 ⊕ Fin 3) :
    ((weightZeroTransitionZ i d e : ℤ) : ℚ) = 16 * weightZeroTransition i d e := by
  rw [weightZeroTransitionZ, weightZeroTransition]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  calc ∏ s, ((lightConeCoeffInvZ i (e s) (c s) : ℤ) : ℚ)
        * ((lightConeCoeffZ i (c s) (d s) : ℤ) : ℚ)
      = ∏ s, 2 * (lightConeCoeffInvQ i (e s) (c s)
          * ((lightConeCoeffZ i (c s) (d s) : ℤ) : ℚ)) := by
        refine Finset.prod_congr rfl fun s _ => ?_
        rw [coe_lightConeCoeffInvZ]
        ring
    _ = 16 * ∏ s, lightConeCoeffInvQ i (e s) (c s)
          * ((lightConeCoeffZ i (c s) (d s) : ℤ) : ℚ) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
        norm_num [Finset.card_univ]

/-- **The boost average on the orbit-sum span, as an integer matrix**: `48` times the
  row-orbit sums of the boost average between representatives. -/
def boostAverageOrbitZ : Matrix (Fin 22) (Fin 22) ℤ :=
  Matrix.of fun k l => ∑ d' ∈ rotationIndexSet (orbitRep k),
    ∑ i : Fin 3, weightZeroTransitionZ i d' (orbitRep l)

/-- The integer matrix casts to `48` times the row-orbit sums of the boost average. -/
lemma coe_boostAverageOrbitZ (k l : Fin 22) :
    ((boostAverageOrbitZ k l : ℤ) : ℚ)
      = 48 * ∑ d' ∈ rotationIndexSet (orbitRep k),
          boostAverageTransition d' (orbitRep l) := by
  simp only [boostAverageOrbitZ, Matrix.of_apply]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d' _ => ?_
  calc ∑ i : Fin 3, ((weightZeroTransitionZ i d' (orbitRep l) : ℤ) : ℚ)
      = ∑ i : Fin 3, 16 * weightZeroTransition i d' (orbitRep l) :=
        Finset.sum_congr rfl fun i _ => coe_weightZeroTransitionZ i d' (orbitRep l)
    _ = 48 * boostAverageTransition d' (orbitRep l) := by
        simp only [boostAverageTransition, Matrix.of_apply]
        rw [← Finset.mul_sum]
        ring


include hT in
/-- **One averaged round at orbit level, integer form**: over the enumerated
  representatives, an averaged round acts by the integer matrix `boostAverageOrbitZ`
  with the overall `48⁻¹` normalisation. -/
lemma eq_sum_boostAverageOrbitZ_smul {x : B} (c : Fin 22 → ℂ)
    (hx : x = ∑ k, c k • rotationOrbitSum (T := T) (orbitRep k))
    (hw : ∀ i : Fin 3, x ∈ boostWeightSubmodule repLorentz i 0) :
    x = ∑ k, ((48 : ℂ)⁻¹ * ∑ l, ((boostAverageOrbitZ k l : ℤ) : ℂ) * c l)
        • rotationOrbitSum (T := T) (orbitRep k) := by
  have hcS_rep : ∀ k : Fin 22,
      (∑ k' : Fin 22, if orbitRep k' = orbitRep k then c k' else 0) = c k := by
    intro k
    simp [orbitRep_injective.eq_iff]
  have hxS : x = ∑ d ∈ rotationSubset,
      (∑ k' : Fin 22, if orbitRep k' = d then c k' else 0)
        • rotationOrbitSum (T := T) d := by
    calc x = ∑ k, c k • rotationOrbitSum (T := T) (orbitRep k) := hx
      _ = ∑ k, (∑ k' : Fin 22, if orbitRep k' = orbitRep k then c k' else 0)
            • rotationOrbitSum (T := T) (orbitRep k) :=
          Finset.sum_congr rfl fun k _ => by rw [hcS_rep k]
      _ = _ := (sum_rotationSubset (fun d => (∑ k' : Fin 22,
            if orbitRep k' = d then c k' else 0) • rotationOrbitSum (T := T) d)).symm
  have hR := hT.eq_sum_boostAverageTransition_of_mem_rotationSubset _ hxS hw
  rw [hR, sum_rotationSubset]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [sum_rotationSubset (fun e => ((∑ d' ∈ rotationIndexSet (orbitRep k),
    boostAverageTransition d' e : ℚ) : ℂ)
      * ∑ k' : Fin 22, if orbitRep k' = e then c k' else 0)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hcS_rep l]
  have hb := congrArg (fun q : ℚ => (q : ℂ)) (coe_boostAverageOrbitZ k l)
  push_cast at hb
  push_cast
  rw [hb]
  ring

/-!

### X. Eigenvectors of the boost average on the orbit-sum span

On the span of the orbit sums of the paired-or-distinct components the boost average
acts with rational spectrum: eigenvalue `1` (dimension `4` — the invariant
contractions), `2/3` (dimension `6`), `1/3` (dimension `9`), `0` (dimension `1`), and a
two-dimensional block with characteristic polynomial `12λ² - 11λ + 1`.  We list integer
coefficient vectors for each block; together they span the orbit-sum span, and every
block except `1` is annihilated by the certificate polynomial
`q(λ) = λ(3λ-2)(3λ-1)(12λ²-11λ+1)/4`.

-/

/-!

## G. The invariant contractions

-/

def test : Matrix (Fin 22) (Fin 22) ℚ := Matrix.of fun i j => if i = j then 1 else 0


/-- The Minkowski sign of a coordinate direction: `+1` on the time direction and `-1` on
  the spatial directions. -/
def minkSign : Fin 1 ⊕ Fin 3 → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)

/-- The enumeration `t, x, y, z` of the coordinate directions. -/
def coordIdx : Fin 4 → Fin 1 ⊕ Fin 3 := ![Sum.inl 0, Sum.inr 0, Sum.inr 1, Sum.inr 2]

/-- **The Levi-Civita sign of an index vector**: the determinant of its indicator matrix
  against the coordinate enumeration — zero unless the four indices are a permutation of
  the coordinates, and the sign of that permutation otherwise. -/
def epsSign (d : Fin 4 → Fin 1 ⊕ Fin 3) : ℤ :=
  (Matrix.of fun s t : Fin 4 => if d s = coordIdx t then (1 : ℤ) else 0).det

/-- **The outer double contraction** `η^{μν} η^{ρσ} T_{μνρσ}`. -/
noncomputable def contractionOuter : B :=
  ∑ μ : Fin 1 ⊕ Fin 3, ∑ ν : Fin 1 ⊕ Fin 3, (minkSign μ * minkSign ν) • T ![μ, μ, ν, ν]

/-- **The crossed double contraction** `η^{μρ} η^{νσ} T_{μνρσ}`. -/
noncomputable def contractionCross : B :=
  ∑ μ : Fin 1 ⊕ Fin 3, ∑ ν : Fin 1 ⊕ Fin 3, (minkSign μ * minkSign ν) • T ![μ, ν, μ, ν]

/-- **The nested double contraction** `η^{μσ} η^{νρ} T_{μνρσ}`. -/
noncomputable def contractionNested : B :=
  ∑ μ : Fin 1 ⊕ Fin 3, ∑ ν : Fin 1 ⊕ Fin 3, (minkSign μ * minkSign ν) • T ![μ, ν, ν, μ]

/-- **The Levi-Civita contraction** `ε^{μνρσ} T_{μνρσ}`: supported on the all-distinct
  components. It is invariant under the connected Lorentz group, whose elements have unit
  determinant. -/
noncomputable def contractionEps : B :=
  ∑ d : Fin 4 → Fin 1 ⊕ Fin 3, ((epsSign d : ℤ) : ℂ) • T d

/-!

## H. The final phase

The endgame in the shape of the dimension-eight case: extract the orbit-sum coefficients
from membership in the rotational average, then let the extreme boost-weight components
along each axis vanish — `eq_zero_and_eq_zero_of_add_add_mem_boostWeightSubmodule` on the
concrete decomposition — and collapse the resulting relations onto the four invariant
contractions.

-/

include hT in
/-- **The final collapse** (in progress): an element of the rotational average of the
  paired-or-distinct span with boost weight zero along every axis is a combination of the
  three metric double contractions and the Levi-Civita contraction. -/
theorem mem_span_contractions_of_mem_rotationSubmodule {x : B}
    (hx : x ∈ rotationSubmodule (repLorentz := repLorentz) (T := T))
    (hw : ∀ i : Fin 3, x ∈ boostWeightSubmodule repLorentz i 0) :
    x ∈ ((ℂ ∙ contractionOuter (T := T) ⊔ ℂ ∙ contractionCross (T := T)) ⊔
        ℂ ∙ contractionNested (T := T)) ⊔ ℂ ∙ contractionEps (T := T) := by
  obtain ⟨c, rfl⟩ := hT.exists_eq_sum_of_mem_rotationSubmodule hx
  sorry

end IsQuadLorentz

end Lorentz
