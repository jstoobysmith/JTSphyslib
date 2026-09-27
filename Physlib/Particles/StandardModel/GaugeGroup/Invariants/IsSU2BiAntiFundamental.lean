/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Nathaneal Sajan
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.IsSU2BiFundamental
/-!
# Families with two anti-fundamental `su(2)` indices

A family `T : (Fin 2 → Fin 2) → B` obeys this law when an isospin rotation `U` moves it by one
factor of the entrywise conjugate `conj U` per index, the summed index in the row slot. By the
symbol convention of `Invariants.Basic`, a product of two doublet symbols is such a family, as
in the isospin structure of the up-type Yukawa block.

Modulo an isospin-stable submodule, every isospin invariant of the span of the family is a
multiple of the epsilon contraction `T ![0, 1] - T ![1, 0]`.

As in `IsSU2FundamentalAntiFundamental`, no coefficient classification is needed: re-indexing
both slots by `su2Epsilon` turns the law into the bi-fundamental law of `IsSU2BiFundamental`,
for the same maps, and leaves both the span and the epsilon contraction unchanged.

- A. The transformation law
- B. The epsilon re-index of both slots
- C. The epsilon contraction
- D. The reduction modulo a stable submodule
-/

@[expose] public section

namespace StandardModel

open Matrix ComplexConjugate

/-!

## A. The transformation law

-/

/-- The linear map `f` moves the components of `T` as `U ∈ SU(2)` moves a tensor with two
  anti-fundamental isospin indices: one factor of the complex conjugate of `U` per index. -/
def IsSU2BiAntiFundamentalMat {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (U : specialUnitaryGroup (Fin 2) ℂ) (f : B →ₗ[ℂ] B)
    (T : (Fin 2 → Fin 2) → B) : Prop :=
  ∀ l : Fin 2 → Fin 2,
    f (T l) = ∑ a : Fin 2 → Fin 2,
      (conj (U.1 (a 0) (l 0)) * conj (U.1 (a 1) (l 1))) • T a

/-- A family `T` of elements of `B`, indexed by two `su(2)` anti-fundamental indices,
  transforms as a tensor `T_{a b}` under the isospin factor of the gauge group. Nothing is
  asked of the colour and hypercharge factors. -/
structure IsSU2BiAntiFundamental (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B)
    (T : (Fin 2 → Fin 2) → B) : Prop where
  repGauge_T : ∀ g : specialUnitaryGroup (Fin 2) ℂ,
    IsSU2BiAntiFundamentalMat g (repGauge (1, g, 1)) T

namespace IsSU2BiAntiFundamental

open IsSU2BiFundamental

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {U : specialUnitaryGroup (Fin 2) ℂ} {f : B →ₗ[ℂ] B}

/-- A finite sum of families carrying two anti-fundamental isospin indices is such a family
  again. -/
lemma sum {ι : Type} [Fintype ι] {T : ι → (Fin 2 → Fin 2) → B}
    (hT : ∀ i, IsSU2BiAntiFundamental B repGauge (T i)) :
    IsSU2BiAntiFundamental B repGauge (fun l => ∑ i, T i l) where
  repGauge_T V l := by
    rw [map_sum, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => (hT i).repGauge_T V l,
      Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.smul_sum.symm

/-!

## B. The epsilon re-index of both slots

-/

/-- The family obtained by re-indexing both slots with the antisymmetric symbol. -/
def reindex (T : (Fin 2 → Fin 2) → B) : (Fin 2 → Fin 2) → B :=
  fun l => ∑ m : Fin 2, ∑ n : Fin 2, (su2Epsilon (l 0) m * su2Epsilon (l 1) n) • T ![m, n]

/-- The re-index exchanges the two like components. -/
@[simp] lemma reindex_zero_zero (T : (Fin 2 → Fin 2) → B) :
    reindex T ![0, 0] = T ![1, 1] := by
  simp [reindex, Fin.sum_univ_two]

/-- The re-index exchanges the two mixed components and negates them. -/
@[simp] lemma reindex_zero_one (T : (Fin 2 → Fin 2) → B) :
    reindex T ![0, 1] = -T ![1, 0] := by
  simp [reindex, Fin.sum_univ_two]

/-- The re-index exchanges the two mixed components and negates them. -/
@[simp] lemma reindex_one_zero (T : (Fin 2 → Fin 2) → B) :
    reindex T ![1, 0] = -T ![0, 1] := by
  simp [reindex, Fin.sum_univ_two]

/-- The re-index exchanges the two like components. -/
@[simp] lemma reindex_one_one (T : (Fin 2 → Fin 2) → B) :
    reindex T ![1, 1] = T ![0, 0] := by
  simp [reindex, Fin.sum_univ_two]

/-- The re-indexed family obeys the bi-fundamental law. -/
lemma map_reindex {T : (Fin 2 → Fin 2) → B} (hf : IsSU2BiAntiFundamentalMat U f T) :
    IsSU2BiFundamentalMat U f (reindex T) := by
  have hl : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
  have hf' : ∀ k : Fin 2 → Fin 2, f (T k)
      = ∑ a : Fin 2 → Fin 2,
        (conj (U.1 (a 0) (k 0)) * conj (U.1 (a 1) (k 1))) • T a := hf
  intro l
  simp only [reindex, map_add, map_smul, hf', Family.sum_pi_two, Fin.sum_univ_two,
    Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rcases hl (l 0) with h0 | h0 <;> rcases hl (l 1) with h1 | h1 <;> rw [h0, h1] <;>
    simp only [su2Epsilon_zero_zero, su2Epsilon_zero_one, su2Epsilon_one_zero, su2Epsilon_one_one,
      su2_conj_apply_zero_zero, su2_conj_apply_zero_one, su2_conj_apply_one_zero,
      su2_conj_apply_one_one] <;>
    module

/-- The re-index of a family with two anti-fundamental indices is a bi-fundamental family
  for the same representation. -/
lemma isSU2BiFundamental_reindex {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2BiAntiFundamental B repGauge T) :
    IsSU2BiFundamental B repGauge (reindex T) where
  repGauge_T g := map_reindex (hT.repGauge_T g)

/-- Every component of the original family lies in the span of the re-indexed one. -/
lemma mem_span_range_reindex (T : (Fin 2 → Fin 2) → B) (d : Fin 2 → Fin 2) :
    T d ∈ Submodule.span ℂ (Set.range (reindex T)) := by
  have hl : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
  have hd : T d = T ![d 0, d 1] := congrArg T (FinVec.etaExpand_eq d).symm
  rw [hd]
  rcases hl (d 0) with h0 | h0 <;> rcases hl (d 1) with h1 | h1 <;> rw [h0, h1]
  · rw [← reindex_one_one T]
    exact Submodule.subset_span ⟨_, rfl⟩
  · rw [show T ![(0 : Fin 2), 1] = -reindex T ![1, 0] from by
      rw [reindex_one_zero, neg_neg]]
    exact neg_mem (Submodule.subset_span ⟨_, rfl⟩)
  · rw [show T ![(1 : Fin 2), 0] = -reindex T ![0, 1] from by
      rw [reindex_zero_one, neg_neg]]
    exact neg_mem (Submodule.subset_span ⟨_, rfl⟩)
  · rw [← reindex_zero_zero T]
    exact Submodule.subset_span ⟨_, rfl⟩

/-- The re-index does not change the span of the components. -/
lemma span_range_reindex (T : (Fin 2 → Fin 2) → B) :
    Submodule.span ℂ (Set.range (reindex T)) = Submodule.span ℂ (Set.range T) := by
  refine Submodule.span_eq_span (Set.range_subset_iff.2 fun d => ?_)
    (Set.range_subset_iff.2 (mem_span_range_reindex T))
  rw [reindex]
  exact sum_mem fun m _ => sum_mem fun n _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-!

## C. The epsilon contraction

The re-index exchanges the two mixed components and negates each, and the two signs cancel
in their antisymmetric combination: the epsilon contraction of the re-indexed family is the
epsilon contraction of the original one.

-/

/-- The re-index leaves the epsilon contraction alone. -/
lemma epsilonContraction_reindex (T : (Fin 2 → Fin 2) → B) :
    epsilonContraction (reindex T) = epsilonContraction T := by
  rw [epsilonContraction, reindex_zero_one, reindex_one_zero, epsilonContraction]
  abel

/-- Any map moving the components by an element of `SU(2)` in the anti-fundamental fixes
  the epsilon contraction. -/
lemma map_epsilonContraction {T : (Fin 2 → Fin 2) → B} (hf : IsSU2BiAntiFundamentalMat U f T) :
    f (epsilonContraction T) = epsilonContraction T := by
  have h := IsSU2BiFundamental.map_epsilonContraction (map_reindex hf)
  rwa [epsilonContraction_reindex] at h

/-- The epsilon contraction is isospin invariant. -/
lemma repGauge_epsilonContraction {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2BiAntiFundamental B repGauge T) (V : specialUnitaryGroup (Fin 2) ℂ) :
    repGauge (1, V, 1) (epsilonContraction T) = epsilonContraction T :=
  map_epsilonContraction (hT.repGauge_T V)

/-!

## D. The reduction modulo a stable submodule

-/

/-- For any family of maps `σ U` obeying the law, a `σ`-invariant of the span joined with a
  `σ`-stable submodule `S` is a multiple of the epsilon contraction plus an element of `S`. -/
lemma reducesInvariantsTo_span_epsilonContraction
    (σ : specialUnitaryGroup (Fin 2) ℂ → B →ₗ[ℂ] B) {T : (Fin 2 → Fin 2) → B}
    (hT : ∀ U, IsSU2BiAntiFundamentalMat U (σ U) T) :
    ReducesInvariantsTo σ (Submodule.span ℂ (Set.range T)) (ℂ ∙ epsilonContraction T) := by
  have h := IsSU2BiFundamental.reducesInvariantsTo_span_epsilonContraction σ
    fun U => map_reindex (hT U)
  rwa [span_range_reindex, epsilonContraction_reindex] at h

/-- The isospin invariants of the component span reduce to the span of the epsilon
  contraction. -/
noncomputable def invariantReductionToSpan {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2BiAntiFundamental B repGauge T) :
    InvariantReductionToSpan (fun V : specialUnitaryGroup (Fin 2) ℂ => repGauge (1, V, 1))
      (Submodule.span ℂ (Set.range T)) :=
  InvariantReductionToSpan.ofReducesInvariantsTo
    (isStableUnder_span_range_of_sum fun V l => ⟨_, hT.repGauge_T V l⟩)
    (epsilonContraction T) (repGauge_epsilonContraction hT)
    (reducesInvariantsTo_span_epsilonContraction _ hT.repGauge_T)

end IsSU2BiAntiFundamental

end StandardModel
