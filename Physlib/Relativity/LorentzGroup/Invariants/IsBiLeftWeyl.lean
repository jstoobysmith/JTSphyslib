/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Invariants.IsLeftRightWeyl
/-!
# Lorentz invariants of two left-handed Weyl indices

`IsBiLeftWeyl repLorentz T` says that a family `T`, indexed by two left-handed Weyl
indices and valued in a module `B` carrying a representation of `SL(2,ℂ)`, transforms as
a tensor `T^{α₁ α₂}`. This is the shape of a fermion mass term: a Dirac or Majorana mass
contracts two Weyl spinors of the same handedness with the antisymmetric symbol `ε`,
`ψ^α χ_α = ε_{α β} ψ^α χ^β`.

Two spinor indices of the same handedness admit exactly one invariant contraction, the
`ε` contraction, because `SL(2,ℂ)` preserves the determinant and nothing else on a pair
of fundamental indices. The main theorem `exists_smul_epsilonContraction_of_invariant`
says accordingly that every Lorentz invariant in the span of the components is a scalar
multiple of `epsilonContraction`, and `repLorentz_epsilonContraction` checks that this
contraction really is invariant.

The proof is the same-handedness twin of `IsLeftRightWeyl`, and reuses its Weyl weight
bases. The only change is in the endgame: averaging the weight-zero projection over the
three axes now gives `M = 2 - swap`, whose eigenvalue `3` is simple and carried by the
antisymmetric line, so the linear certificate `(3 λ - 1) / 2` in `M / 3` collapses an
invariant onto the antisymmetrisation of its coefficients, which is the `ε` contraction.

The section headings tell the story: the weight basis of a pair of left-handed indices
(A), the tensors and the span of their components (B), the weight grading of the span
(C), the weight-zero round and its average over the three axes (D), the `ε` contraction
and the linear certificate which produces it (E), and the classification modulo a
Lorentz-stable submodule (F).
-/

@[expose] public section

namespace Lorentz

open TensorProduct Matrix MatrixGroups SL2C BoostWeight
open IsQuadLorentz (eq_component_zero_of_mem_boostWeightSubmodule
  mem_boostWeightSubmodule_zero_of_invariant quotRep quotRep_mkQ)

/-!

## A. The weight basis of a pair of left-handed indices

Both indices are graded by the same Weyl weight basis of `IsLeftRightWeyl`, so the
weight basis of the pair is the tensor square of it and the weight is `pairWeight`.

-/

/-- The axis-`i` weight basis of a pair of left-handed indices. -/
def biLeftCoeff (i : Fin 3) (κ α : Fin 2 × Fin 2) : ℂ :=
  weylCoeff i κ.1 α.1 * weylCoeff i κ.2 α.2

/-- The standard basis of a pair of left-handed indices written back in the axis-`i`
  weight basis. -/
noncomputable def biLeftCoeffInv (i : Fin 3) (α κ : Fin 2 × Fin 2) : ℂ :=
  weylCoeffInv i α.1 κ.1 * weylCoeffInv i α.2 κ.2

/-- The pair weight basis is a basis: the two coefficient matrices are inverse. -/
lemma sum_biLeftCoeffInv_mul (i : Fin 3) (α β : Fin 2 × Fin 2) :
    ∑ κ : Fin 2 × Fin 2, biLeftCoeffInv i α κ * biLeftCoeff i κ β
      = if α = β then 1 else 0 := by
  have hfac : (∑ κ₁, weylCoeffInv i α.1 κ₁ * weylCoeff i κ₁ β.1)
      * (∑ κ₂, weylCoeffInv i α.2 κ₂ * weylCoeff i κ₂ β.2)
      = ∑ κ : Fin 2 × Fin 2, biLeftCoeffInv i α κ * biLeftCoeff i κ β := by
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun κ₁ _ => Finset.sum_congr rfl fun κ₂ _ => by
      simp only [biLeftCoeff, biLeftCoeffInv]
      ring
  rw [← hfac, sum_weylCoeffInv_mul, sum_weylCoeffInv_mul]
  obtain ⟨α₁, α₂⟩ := α
  obtain ⟨β₁, β₂⟩ := β
  by_cases h1 : α₁ = β₁ <;> by_cases h2 : α₂ = β₂ <;> simp [h1, h2, Prod.mk.injEq]

/-- The pair weight basis diagonalises the axis-`i` boost, with the weight
  `pairWeight`. -/
lemma sum_boostAxis_biLeftCoeff (i : Fin 3) (κ a : Fin 2 × Fin 2) {t : ℝ} (ht : t ≠ 0) :
    ∑ l : Fin 2 × Fin 2, biLeftCoeff i κ l
        * ((SL2C.boostAxis i t ht).1 a.1 l.1 * (SL2C.boostAxis i t ht).1 a.2 l.2)
      = ((t : ℝ) : ℂ) ^ (pairWeight κ) * biLeftCoeff i κ a := by
  have htc : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  have hfac : (∑ l₁, (SL2C.boostAxis i t ht).1 a.1 l₁ * weylCoeff i κ.1 l₁)
      * (∑ l₂, (SL2C.boostAxis i t ht).1 a.2 l₂ * weylCoeff i κ.2 l₂)
      = ∑ l : Fin 2 × Fin 2, biLeftCoeff i κ l
        * ((SL2C.boostAxis i t ht).1 a.1 l.1 * (SL2C.boostAxis i t ht).1 a.2 l.2) := by
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun l₁ _ => Finset.sum_congr rfl fun l₂ _ => by
      simp only [biLeftCoeff]
      ring
  rw [← hfac, sum_boostAxis_weylCoeff i κ.1 a.1 ht, sum_boostAxis_weylCoeff i κ.2 a.2 ht,
    pairWeight, biLeftCoeff, zpow_add₀ htc]
  ring

/-!

## B. Bi-left-handed Weyl tensors and the span of their components

-/

/-- A family `T` of elements of `B`, indexed by two left-handed Weyl indices, transforms
  as a tensor `T^{α₁ α₂}` under the representation `repLorentz` of `SL(2,ℂ)`. -/
structure IsBiLeftWeyl (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B)
    (T : Fin 2 × Fin 2 → B) : Prop where
  repLorentz_T : ∀ (g : SL(2,ℂ)) l,
    repLorentz g (T l) = ∑ (a : Fin 2 × Fin 2), (g.1 a.1 l.1 * g.1 a.2 l.2) • T a

namespace IsBiLeftWeyl
set_option linter.unusedVariables false

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {T : Fin 2 × Fin 2 → B}
  (hT : IsBiLeftWeyl B repLorentz T)

/-- The span of all the components. -/
def span (hT : IsBiLeftWeyl B repLorentz T) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

/-- The span of the components is exactly the set of linear combinations of them. -/
lemma mem_span_iff (x : B) :
    x ∈ hT.span ↔ ∃ (c : Fin 2 × Fin 2 → ℂ), x = ∑ d, c d • T d := by
  constructor
  · intro hx
    rw [span] at hx
    refine Submodule.iSup_induction
      (motive := fun y => ∃ c : Fin 2 × Fin 2 → ℂ, y = ∑ d, c d • T d)
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

## C. The weight grading of the span

-/

/-- The axis-`i` weight component of `T` at the pair `κ` of Weyl weight indices. -/
noncomputable def weightVec (hT : IsBiLeftWeyl B repLorentz T) (i : Fin 3)
    (κ : Fin 2 × Fin 2) : B :=
  ∑ a : Fin 2 × Fin 2, biLeftCoeff i κ a • T a

/-- Each weight component lies in the span of the components. -/
lemma weightVec_mem_span (i : Fin 3) (κ : Fin 2 × Fin 2) :
    hT.weightVec i κ ∈ hT.span :=
  sum_mem fun a _ => Submodule.smul_mem _ _
    (Submodule.mem_iSup_of_mem a (Submodule.mem_span_singleton_self _))

/-- Each generator is recovered from the weight components along any axis. -/
lemma eq_sum_weightVec (i : Fin 3) (α : Fin 2 × Fin 2) :
    T α = ∑ κ : Fin 2 × Fin 2, biLeftCoeffInv i α κ • hT.weightVec i κ := by
  calc T α = ∑ β : Fin 2 × Fin 2,
        (∑ κ : Fin 2 × Fin 2, biLeftCoeffInv i α κ * biLeftCoeff i κ β) • T β := by
        simp only [sum_biLeftCoeffInv_mul, ite_smul, one_smul, zero_smul,
          Finset.sum_ite_eq, Finset.mem_univ, if_true]
    _ = _ := by
        simp only [weightVec, Finset.smul_sum, smul_smul, Finset.sum_smul]
        rw [Finset.sum_comm]

/-- The weight components along any axis span the same space as the components. -/
lemma span_eq_weightVec (hT : IsBiLeftWeyl B repLorentz T) (i : Fin 3) :
    hT.span = ⨆ κ, ℂ ∙ hT.weightVec i κ := by
  rw [span]
  refine le_antisymm (iSup_le fun α => ?_) (iSup_le fun κ => ?_)
  · rw [Submodule.span_singleton_le_iff_mem, hT.eq_sum_weightVec i α]
    exact sum_mem fun κ _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem κ (Submodule.mem_span_singleton_self _))
  · rw [Submodule.span_singleton_le_iff_mem]
    exact hT.weightVec_mem_span i κ

/-- The weight components are boost eigenvectors: along axis `i` the component at `κ`
  has boost weight `pairWeight κ`. -/
lemma weightVec_mem_boostWeightSubmodule (i : Fin 3) (κ : Fin 2 × Fin 2) :
    hT.weightVec i κ ∈ boostWeightSubmodule repLorentz i (pairWeight κ) := by
  refine mem_boostWeightSubmodule.2 fun t ht => ?_
  have hstep : ∀ l : Fin 2 × Fin 2,
      biLeftCoeff i κ l • repLorentz (SL2C.boostAxis i t ht) (T l)
        = ∑ a : Fin 2 × Fin 2, (biLeftCoeff i κ l
            * ((SL2C.boostAxis i t ht).1 a.1 l.1
              * (SL2C.boostAxis i t ht).1 a.2 l.2)) • T a := by
    intro l
    rw [hT.repLorentz_T, Finset.smul_sum]
    exact Finset.sum_congr rfl fun a _ => smul_smul _ _ _
  calc repLorentz (SL2C.boostAxis i t ht) (hT.weightVec i κ)
      = ∑ l : Fin 2 × Fin 2, biLeftCoeff i κ l
          • repLorentz (SL2C.boostAxis i t ht) (T l) := by
        simp only [weightVec, map_sum, map_smul]
    _ = ∑ a : Fin 2 × Fin 2, (∑ l : Fin 2 × Fin 2, biLeftCoeff i κ l
          * ((SL2C.boostAxis i t ht).1 a.1 l.1
            * (SL2C.boostAxis i t ht).1 a.2 l.2)) • T a := by
        simp only [hstep]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => (Finset.sum_smul).symm
    _ = ∑ a : Fin 2 × Fin 2,
          (((t : ℝ) : ℂ) ^ (pairWeight κ) * biLeftCoeff i κ a) • T a :=
        Finset.sum_congr rfl fun a _ => by rw [sum_boostAxis_biLeftCoeff i κ a ht]
    _ = (algebraMap ℝ ℂ) t ^ (pairWeight κ) • hT.weightVec i κ := by
        rw [show (algebraMap ℝ ℂ) t = ((t : ℝ) : ℂ) from rfl, weightVec, Finset.smul_sum]
        exact Finset.sum_congr rfl fun a _ => (smul_smul _ _ _).symm

/-- The axis-`i` weight-`m` component of the generator `T α`: the weight-`m` partial sum
  of `eq_sum_weightVec`. -/
noncomputable def monoComponent (i : Fin 3) (α : Fin 2 × Fin 2) (m : ℤ) : B :=
  ∑ κ ∈ Finset.univ.filter (fun κ : Fin 2 × Fin 2 => pairWeight κ = m),
    biLeftCoeffInv i α κ • hT.weightVec i κ

/-- The weight components are homogeneous of the stated weight. -/
lemma monoComponent_mem_boostWeightSubmodule (i : Fin 3) (α : Fin 2 × Fin 2) (m : ℤ) :
    hT.monoComponent i α m ∈ boostWeightSubmodule repLorentz i m := by
  refine sum_mem fun κ hκ => Submodule.smul_mem _ _ ?_
  exact (show pairWeight κ = m from (Finset.mem_filter.1 hκ).2) ▸
    hT.weightVec_mem_boostWeightSubmodule i κ

/-- A component is the sum of its weight components over the three possible weights. -/
lemma eq_sum_monoComponent_univ (i : Fin 3) (α : Fin 2 × Fin 2) :
    T α = ∑ m ∈ ({-2, 0, 2} : Finset ℤ), hT.monoComponent i α m := by
  rw [hT.eq_sum_weightVec i α]
  exact (Finset.sum_fiberwise_of_maps_to (fun κ _ => pairWeight_mem κ) _).symm

/-!

## D. The weight-zero round and its average over the axes

-/

/-- The matrix of the axis-`i` weight-zero projection in the `T`-basis: the coefficient
  of `T β` in the re-expansion of `monoComponent i α 0` through the weight basis. -/
noncomputable def weightZeroTransition (i : Fin 3) (β α : Fin 2 × Fin 2) : ℂ :=
  ∑ κ ∈ Finset.univ.filter (fun κ : Fin 2 × Fin 2 => pairWeight κ = 0),
    biLeftCoeffInv i α κ * biLeftCoeff i κ β

/-- The weight-zero component re-expanded in the `T`-basis: `monoComponent i α 0` is the
  `α`-th column of `weightZeroTransition` applied to the generators. -/
lemma monoComponent_zero_eq (i : Fin 3) (α : Fin 2 × Fin 2) :
    hT.monoComponent i α 0
      = ∑ β : Fin 2 × Fin 2, weightZeroTransition i β α • T β := by
  rw [monoComponent]
  simp only [weightVec, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [← Finset.sum_smul, weightZeroTransition]

include hT in
/-- One round of the recursion along one axis: an element of weight zero along axis `i`
  expanded in the generators re-expands with the weight-zero transition matrix applied
  to its coefficients. -/
lemma eq_sum_weightZeroTransition_smul (i : Fin 3) {x : B}
    (c : Fin 2 × Fin 2 → ℂ) (hx : x = ∑ α, c α • T α)
    (hw : x ∈ boostWeightSubmodule repLorentz i 0) :
    x = ∑ β, (∑ α, weightZeroTransition i β α * c α) • T β := by
  have hsum : x = ∑ m ∈ ({-2, 0, 2} : Finset ℤ),
      ∑ α, c α • hT.monoComponent i α m := by
    rw [hx]
    calc ∑ α, c α • T α
        = ∑ α, c α • ∑ m ∈ ({-2, 0, 2} : Finset ℤ), hT.monoComponent i α m :=
          Finset.sum_congr rfl fun α _ => by rw [← hT.eq_sum_monoComponent_univ i α]
      _ = _ := by
          simp only [Finset.smul_sum]
          exact Finset.sum_comm
  have hx0 : x = ∑ α, c α • hT.monoComponent i α 0 :=
    eq_component_zero_of_mem_boostWeightSubmodule
      (w := fun m => ∑ α, c α • hT.monoComponent i α m) hw
      (fun m _ => sum_mem fun α _ => Submodule.smul_mem _ _
        (hT.monoComponent_mem_boostWeightSubmodule i α m))
      (by decide) hsum
  calc x = ∑ α, c α • hT.monoComponent i α 0 := hx0
    _ = ∑ α, c α • ∑ β, weightZeroTransition i β α • T β :=
        Finset.sum_congr rfl fun α _ => by rw [hT.monoComponent_zero_eq i α]
    _ = ∑ β, (∑ α, weightZeroTransition i β α * c α) • T β := by
        simp only [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [← Finset.sum_smul]
        exact congrArg (· • T β) (Finset.sum_congr rfl fun α _ => mul_comm _ _)

/-- The closed form of the summed weight-zero transition: twice the identity minus the
  swap of the two indices. -/
def transitionEntry (β α : Fin 2 × Fin 2) : ℂ :=
  2 * (if β.1 = α.1 then 1 else 0) * (if β.2 = α.2 then 1 else 0)
    - (if β.1 = α.2 then 1 else 0) * (if β.2 = α.1 then 1 else 0)

/-- The sum over the three axes of the weight-zero transitions has the closed form
  `transitionEntry`. -/
lemma sum_weightZeroTransition_eq (β α : Fin 2 × Fin 2) :
    ∑ i : Fin 3, weightZeroTransition i β α = transitionEntry β α := by
  simp only [weightZeroTransition, sum_weightZeroFilter, Fin.sum_univ_three]
  obtain ⟨β₁, β₂⟩ := β
  obtain ⟨α₁, α₂⟩ := α
  fin_cases β₁ <;> fin_cases β₂ <;> fin_cases α₁ <;> fin_cases α₂ <;>
    simp [transitionEntry, biLeftCoeff, biLeftCoeffInv, weylCoeff, weylCoeffInv] <;>
    norm_num [Complex.ext_iff]

include hT in
/-- One averaged round of the recursion: an element of weight zero along all three axes
  re-expands with a third of the summed transition matrix applied to its
  coefficients. -/
lemma eq_sum_transitionEntry_smul {x : B} (c : Fin 2 × Fin 2 → ℂ)
    (hx : x = ∑ α, c α • T α)
    (hw : ∀ i : Fin 3, x ∈ boostWeightSubmodule repLorentz i 0) :
    x = ∑ β, ((3 : ℂ)⁻¹ * ∑ α, transitionEntry β α * c α) • T β := by
  have hround : ∀ i : Fin 3,
      x = ∑ β, (∑ α, weightZeroTransition i β α * c α) • T β :=
    fun i => hT.eq_sum_weightZeroTransition_smul i c hx (hw i)
  have h3 : (3 : ℂ) • x = ∑ i : Fin 3, x := by
    rw [Fin.sum_univ_three, show (3 : ℂ) = 1 + 1 + 1 from by norm_num,
      add_smul, add_smul, one_smul]
  calc x = (3 : ℂ)⁻¹ • ((3 : ℂ) • x) := by rw [smul_smul]; norm_num
    _ = (3 : ℂ)⁻¹ • ∑ i : Fin 3, x := by rw [h3]
    _ = (3 : ℂ)⁻¹ • ∑ i : Fin 3, ∑ β,
          (∑ α, weightZeroTransition i β α * c α) • T β :=
        congrArg (fun y => (3 : ℂ)⁻¹ • y) (Finset.sum_congr rfl fun i _ => hround i)
    _ = ∑ β, ((3 : ℂ)⁻¹ * ∑ α, transitionEntry β α * c α) • T β := by
        rw [Finset.sum_comm, Finset.smul_sum]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [← Finset.sum_smul, smul_smul]
        congr 1
        rw [show (∑ i : Fin 3, ∑ α, weightZeroTransition i β α * c α)
            = ∑ α, transitionEntry β α * c α from by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun α _ => by
            rw [← Finset.sum_mul, sum_weightZeroTransition_eq]]

/-!

## E. The epsilon contraction and the linear certificate

The summed transition is `2 - swap`, so a third of it fixes exactly the antisymmetric
line. The linear certificate `(3 λ - 1) / 2` therefore collapses an invariant onto the
antisymmetrisation of its coefficients, which is a multiple of the `ε` contraction.

-/

/-- The `ε` symbol on a pair of same-handedness spinor indices, in the convention of
  `Fermion.metricRaw`. -/
def epsZ (α : Fin 2 × Fin 2) : ℤ :=
  if α = (0, 1) then 1 else if α = (1, 0) then -1 else 0

/-- The `ε` contraction `ε_{α β} T^{α β}`, the only invariant contraction of two
  same-handedness Weyl indices, and the shape of a fermion mass term. -/
noncomputable def epsilonContraction : B :=
  ∑ α : Fin 2 × Fin 2, ((epsZ α : ℤ) : ℂ) • T α

/-- The `ε` contraction written out: the antisymmetric combination of the two mixed
  components. -/
lemma epsilonContraction_eq :
    epsilonContraction (T := T) = T (0, 1) - T (1, 0) := by
  rw [epsilonContraction]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, epsZ]
  module

include hT in
/-- The `ε` contraction is Lorentz invariant: the antisymmetric combination picks out
  the determinant of the `SL(2,ℂ)` matrix, which is one. -/
lemma repLorentz_epsilonContraction (g : SL(2,ℂ)) :
    repLorentz g (epsilonContraction (T := T)) = epsilonContraction (T := T) := by
  have hdet : g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0 = 1 := by
    have h := g.2
    rwa [Matrix.det_fin_two] at h
  rw [epsilonContraction_eq, map_sub, hT.repLorentz_T, hT.repLorentz_T]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  match_scalars
  · ring
  · linear_combination hdet
  · linear_combination -hdet
  · ring

/-- The action of the summed transition matrix on a coefficient vector is twice the
  vector minus its swap. -/
lemma sum_transitionEntry_mul (c : Fin 2 × Fin 2 → ℂ) (β : Fin 2 × Fin 2) :
    ∑ α, transitionEntry β α * c α = 2 * c β - c β.swap := by
  obtain ⟨β₁, β₂⟩ := β
  fin_cases β₁ <;> fin_cases β₂ <;>
    simp [transitionEntry, Fintype.sum_prod_type, Fin.sum_univ_two] <;> ring

/-- The antisymmetrisation of a coefficient vector is a multiple of the `ε`
  contraction. -/
lemma sum_antisymm_smul (c : Fin 2 × Fin 2 → ℂ) :
    ∑ β : Fin 2 × Fin 2, ((2 : ℂ)⁻¹ * (c β - c β.swap)) • T β
      = ((2 : ℂ)⁻¹ * (c (0, 1) - c (1, 0))) • epsilonContraction (T := T) := by
  rw [epsilonContraction_eq]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Prod.swap_prod_mk]
  module

include hT in
/-- The classification of the Lorentz invariants: every element of the span of the
  components fixed by the Lorentz group is a scalar multiple of the `ε` contraction. -/
theorem exists_smul_epsilonContraction_of_invariant {x : B} (hx : x ∈ hT.span)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, x = a • epsilonContraction (T := T) := by
  obtain ⟨c, hc⟩ := (hT.mem_span_iff x).1 hx
  have hw := mem_boostWeightSubmodule_zero_of_invariant (repLorentz := repLorentz) hinv
  have h1 : x = ∑ β, ((3 : ℂ)⁻¹ * (2 * c β - c β.swap)) • T β := by
    rw [hT.eq_sum_transitionEntry_smul c hc hw]
    exact Finset.sum_congr rfl fun β _ => by rw [sum_transitionEntry_mul]
  refine ⟨(2 : ℂ)⁻¹ * (c (0, 1) - c (1, 0)), ?_⟩
  rw [← sum_antisymm_smul c]
  calc x = (3 / 2 : ℂ) • x - (1 / 2 : ℂ) • x := by module
    _ = ∑ β : Fin 2 × Fin 2, ((2 : ℂ)⁻¹ * (c β - c β.swap)) • T β := by
        nth_rewrite 1 [h1]
        nth_rewrite 1 [hc]
        simp only [Finset.smul_sum, smul_smul, ← Finset.sum_sub_distrib, ← sub_smul]
        refine Finset.sum_congr rfl fun β _ => ?_
        congr 1
        ring

/-!

## F. The classification modulo a Lorentz-stable submodule

A Lorentz-stable submodule can be divided out: the quotient representation carries the
images of the components as a bi-left-handed tensor again, so the classification applies
verbatim in the quotient and lifts to a classification modulo the submodule. The
quotient representation itself is the one built in `IsQuadLorentz`.

-/

include hT in
/-- The images of the components in the quotient by a Lorentz-stable submodule again
  form a bi-left-handed Weyl tensor. -/
lemma isBiLeftWeyl_quotRep (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) :
    IsBiLeftWeyl (B ⧸ S) (quotRep (repLorentz := repLorentz) S hS)
      (fun l => S.mkQ (T l)) where
  repLorentz_T g l := by
    rw [quotRep_mkQ, hT.repLorentz_T g l, map_sum]
    exact Finset.sum_congr rfl fun a _ => map_smul _ _ _

/-- The quotient map carries the `ε` contraction to the `ε` contraction of the
  images. -/
lemma mkQ_epsilonContraction (S : Submodule ℂ B) :
    S.mkQ (epsilonContraction (T := T))
      = epsilonContraction (T := fun l => S.mkQ (T l)) := by
  rw [epsilonContraction, epsilonContraction, map_sum]
  exact Finset.sum_congr rfl fun α _ => map_smul _ _ _

include hT in
/-- The classification of the Lorentz invariants modulo a stable submodule: an element
  of the span of the components together with a Lorentz-stable submodule `S`, fixed by
  the Lorentz group, is a multiple of the `ε` contraction up to an error in `S`. -/
lemma exists_smul_epsilonContraction_of_invariant_subset {x : B} (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S)
    (hx : x ∈ hT.span ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ a : ℂ, ∃ y ∈ S, x = a • epsilonContraction (T := T) + y := by
  have hT' := hT.isBiLeftWeyl_quotRep S hS
  have hmk : S.mkQ x ∈ hT'.span := by
    obtain ⟨u, hu, z, hz, huz⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, hc⟩ := (hT.mem_span_iff u).1 hu
    refine (hT'.mem_span_iff _).2 ⟨c, ?_⟩
    rw [← huz, map_add, show S.mkQ z = 0 from (Submodule.Quotient.mk_eq_zero S).2 hz,
      add_zero, hc, map_sum]
    exact Finset.sum_congr rfl fun d _ => map_smul _ _ _
  have hinv' : ∀ g : SL(2,ℂ),
      quotRep (repLorentz := repLorentz) S hS g (S.mkQ x) = S.mkQ x := by
    intro g
    rw [quotRep_mkQ, hinv g]
  obtain ⟨a, hcomb⟩ := hT'.exists_smul_epsilonContraction_of_invariant hmk hinv'
  rw [← mkQ_epsilonContraction] at hcomb
  refine ⟨a, x - a • epsilonContraction (T := T), ?_, by abel⟩
  have hker : x - a • epsilonContraction (T := T) ∈ LinearMap.ker S.mkQ := by
    rw [LinearMap.mem_ker, map_sub, hcomb, map_smul]
    abel
  rwa [Submodule.ker_mkQ] at hker

end IsBiLeftWeyl

end Lorentz
