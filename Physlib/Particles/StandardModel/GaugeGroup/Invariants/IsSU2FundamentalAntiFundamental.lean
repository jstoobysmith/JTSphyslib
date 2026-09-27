/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Nathaneal Sajan
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.IsSU2BiFundamental
/-!
# Families with one fundamental and one anti-fundamental `su(2)` index

A family `T : (Fin 2 → Fin 2) → B` obeys this law when an isospin rotation `U` moves it by `U`
on the first index and by the entrywise conjugate `conj U` on the second, the summed index in
the row slot. For unitary `U`, `conj U = (U⁻¹)ᵀ`, so the anti-fundamental law is also the dual
law. By the symbol convention of `Invariants.Basic`, a conjugate doublet symbol supplies the
first index and a doublet symbol the second, as in the Higgs sector family `H̄ⁱ Hʲ`.

Modulo an isospin-stable submodule, every isospin invariant of the span of the family is a
multiple of the delta contraction `T ![0, 0] + T ![1, 1]`.

No coefficient classification is needed here. `SU(2)` is pseudo-real, `conj U = ε U ε⁻¹`
(`GaugeGroup.SU2Conjugation`), so re-indexing the second slot by `su2Epsilon` turns the law
into the bi-fundamental law of `IsSU2BiFundamental`, for the same maps.

- A. The transformation law
- B. The epsilon re-index of the anti-fundamental slot
- C. The delta contraction
- D. The reduction modulo a stable submodule
-/

@[expose] public section

namespace StandardModel

open Matrix ComplexConjugate

/-!

## A. The transformation law

-/

/-- The linear map `f` moves the components of `T` as `U ∈ SU(2)` moves a tensor with one
  fundamental and one anti-fundamental isospin index: a factor of `U` for the first index
  and a factor of its complex conjugate for the second. -/
def IsSU2FundamentalAntiFundamentalMat {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (U : specialUnitaryGroup (Fin 2) ℂ) (f : B →ₗ[ℂ] B)
    (T : (Fin 2 → Fin 2) → B) : Prop :=
  ∀ l : Fin 2 → Fin 2,
    f (T l) = ∑ a : Fin 2 → Fin 2, (U.1 (a 0) (l 0) * conj (U.1 (a 1) (l 1))) • T a

/-- A family `T` of elements of `B`, indexed by one `su(2)` fundamental index and one
  anti-fundamental one, transforms as a tensor `T^a_b` under the isospin factor of the gauge
  group. Nothing is asked of the colour and hypercharge factors. -/
structure IsSU2FundamentalAntiFundamental (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B)
    (T : (Fin 2 → Fin 2) → B) : Prop where
  repGauge_T : ∀ g : specialUnitaryGroup (Fin 2) ℂ,
    IsSU2FundamentalAntiFundamentalMat g (repGauge (1, g, 1)) T

namespace IsSU2FundamentalAntiFundamental

open IsSU2BiFundamental

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {U : specialUnitaryGroup (Fin 2) ℂ} {f : B →ₗ[ℂ] B}

/-- A finite sum of families carrying one fundamental and one anti-fundamental isospin
  index is such a family again. -/
lemma sum {ι : Type} [Fintype ι] {T : ι → (Fin 2 → Fin 2) → B}
    (hT : ∀ i, IsSU2FundamentalAntiFundamental B repGauge (T i)) :
    IsSU2FundamentalAntiFundamental B repGauge (fun l => ∑ i, T i l) where
  repGauge_T V l := by
    rw [map_sum, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => (hT i).repGauge_T V l,
      Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.smul_sum.symm

/-!

## B. The epsilon re-index of the anti-fundamental slot

Re-indexing the second slot by `su2Epsilon` turns the law into the bi-fundamental one: the
four conjugation identities of `GaugeGroup.SU2Conjugation` remove every complex conjugate.
The re-index is invertible, so the span of the components is unchanged.

-/

/-- The family obtained by re-indexing the anti-fundamental slot with the antisymmetric
  symbol. -/
def reindex (T : (Fin 2 → Fin 2) → B) : (Fin 2 → Fin 2) → B :=
  fun l => ∑ m : Fin 2, su2Epsilon (l 1) m • T ![l 0, m]

/-- The re-index at second index `0` picks out the component with second index `1`. -/
@[simp] lemma reindex_apply_zero (T : (Fin 2 → Fin 2) → B) (p : Fin 2) :
    reindex T ![p, 0] = T ![p, 1] := by
  simp [reindex, Fin.sum_univ_two]

/-- The re-index at second index `1` picks out minus the component with second index
  `0`. -/
@[simp] lemma reindex_apply_one (T : (Fin 2 → Fin 2) → B) (p : Fin 2) :
    reindex T ![p, 1] = -T ![p, 0] := by
  simp [reindex, Fin.sum_univ_two]

/-- The re-indexed family obeys the bi-fundamental law. -/
lemma map_reindex {T : (Fin 2 → Fin 2) → B} (hf : IsSU2FundamentalAntiFundamentalMat U f T) :
    IsSU2BiFundamentalMat U f (reindex T) := by
  have hl : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
  have hf' : ∀ k : Fin 2 → Fin 2, f (T k)
      = ∑ a : Fin 2 → Fin 2, (U.1 (a 0) (k 0) * conj (U.1 (a 1) (k 1))) • T a := hf
  intro l
  simp only [reindex, map_add, map_smul, hf', Family.sum_pi_two, Fin.sum_univ_two,
    Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rcases hl (l 0) with h0 | h0 <;> rcases hl (l 1) with h1 | h1 <;> rw [h0, h1] <;>
    simp only [su2Epsilon_zero_zero, su2Epsilon_zero_one, su2Epsilon_one_zero, su2Epsilon_one_one,
      su2_conj_apply_zero_zero, su2_conj_apply_zero_one, su2_conj_apply_one_zero,
      su2_conj_apply_one_one] <;>
    module

/-- The re-index of a fundamental and anti-fundamental family is a bi-fundamental family
  for the same representation. -/
lemma isSU2BiFundamental_reindex {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2FundamentalAntiFundamental B repGauge T) :
    IsSU2BiFundamental B repGauge (reindex T) where
  repGauge_T g := map_reindex (hT.repGauge_T g)

/-- Every component of the original family lies in the span of the re-indexed one. -/
lemma mem_span_range_reindex (T : (Fin 2 → Fin 2) → B) (d : Fin 2 → Fin 2) :
    T d ∈ Submodule.span ℂ (Set.range (reindex T)) := by
  have hl : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
  have hd : T d = T ![d 0, d 1] := congrArg T (FinVec.etaExpand_eq d).symm
  rw [hd]
  rcases hl (d 1) with h1 | h1 <;> rw [h1]
  · rw [show T ![d 0, (0 : Fin 2)] = -reindex T ![d 0, 1] from by
      rw [reindex_apply_one, neg_neg]]
    exact neg_mem (Submodule.subset_span ⟨_, rfl⟩)
  · rw [← reindex_apply_zero T (d 0)]
    exact Submodule.subset_span ⟨_, rfl⟩

/-- The re-index does not change the span of the components. -/
lemma span_range_reindex (T : (Fin 2 → Fin 2) → B) :
    Submodule.span ℂ (Set.range (reindex T)) = Submodule.span ℂ (Set.range T) := by
  refine Submodule.span_eq_span (Set.range_subset_iff.2 fun d => ?_)
    (Set.range_subset_iff.2 (mem_span_range_reindex T))
  rw [reindex]
  exact sum_mem fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-!

## C. The delta contraction

The delta contraction `T ![0, 0] + T ![1, 1]` is minus the epsilon contraction of the
re-indexed family. The sign is a lemma rather than part of a definition, so that the re-index
and the delta contraction stay plain.

-/

/-- The delta contraction: the trace of a family with one fundamental and one
  anti-fundamental index. -/
def deltaContraction (T : (Fin 2 → Fin 2) → B) : B := T ![0, 0] + T ![1, 1]

/-- The delta contraction lies in the span of the components. -/
lemma deltaContraction_mem_span (T : (Fin 2 → Fin 2) → B) :
    deltaContraction T ∈ Submodule.span ℂ (Set.range T) :=
  add_mem (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)

/-- The epsilon contraction of the re-indexed family is minus the delta contraction of the
  original one. -/
lemma epsilonContraction_reindex (T : (Fin 2 → Fin 2) → B) :
    epsilonContraction (reindex T) = -deltaContraction T := by
  rw [epsilonContraction, reindex_apply_zero, reindex_apply_one, deltaContraction]
  abel

/-- Any map moving the components by an element of `SU(2)` fixes the delta contraction. -/
lemma map_deltaContraction {T : (Fin 2 → Fin 2) → B}
    (hf : IsSU2FundamentalAntiFundamentalMat U f T) :
    f (deltaContraction T) = deltaContraction T := by
  have h := map_epsilonContraction (map_reindex hf)
  rw [epsilonContraction_reindex, map_neg, neg_inj] at h
  exact h

/-- The delta contraction is isospin invariant. Nothing constrains the colour and
  hypercharge factors, which may well move it. -/
lemma repGauge_deltaContraction {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2FundamentalAntiFundamental B repGauge T) (V : specialUnitaryGroup (Fin 2) ℂ) :
    repGauge (1, V, 1) (deltaContraction T) = deltaContraction T :=
  map_deltaContraction (hT.repGauge_T V)

/-!

## D. The reduction modulo a stable submodule

The reduction of `IsSU2BiFundamental` for the re-indexed family, transported along
`span_range_reindex` and the sign of `epsilonContraction_reindex`. In the gauge form the law
constrains only the isospin factor, so the invariance of the delta contraction under the whole
gauge group is a hypothesis.

-/

/-- For any family of maps `σ U` obeying the law, a `σ`-invariant of the span joined with a
  `σ`-stable submodule `S` is a multiple of the delta contraction plus an element of `S`. -/
lemma reducesInvariantsTo_span_deltaContraction
    (σ : specialUnitaryGroup (Fin 2) ℂ → B →ₗ[ℂ] B) {T : (Fin 2 → Fin 2) → B}
    (hT : ∀ U, IsSU2FundamentalAntiFundamentalMat U (σ U) T) :
    ReducesInvariantsTo σ (Submodule.span ℂ (Set.range T)) (ℂ ∙ deltaContraction T) := by
  have h := reducesInvariantsTo_span_epsilonContraction σ fun U => map_reindex (hT U)
  rwa [span_range_reindex, epsilonContraction_reindex, ← Set.neg_singleton,
    Submodule.span_neg] at h

/-- The isospin invariants of the component span reduce to the span of the delta
  contraction. -/
noncomputable def invariantReductionToSpan {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2FundamentalAntiFundamental B repGauge T) :
    InvariantReductionToSpan (fun V : specialUnitaryGroup (Fin 2) ℂ => repGauge (1, V, 1))
      (Submodule.span ℂ (Set.range T)) :=
  InvariantReductionToSpan.ofReducesInvariantsTo
    (isStableUnder_span_range_of_sum fun V l => ⟨_, hT.repGauge_T V l⟩)
    (deltaContraction T) (repGauge_deltaContraction hT)
    (reducesInvariantsTo_span_deltaContraction _ hT.repGauge_T)

/-- A gauge invariant of the span joined with a gauge-stable submodule is a multiple of the
  delta contraction plus a gauge-invariant remainder, once the delta contraction is known to
  be gauge invariant. The hypothesis on the delta contraction cannot be dropped: the law says
  nothing about the hypercharge factor, which may scale it. -/
lemma exists_smul_add_of_gauge_invariant {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2FundamentalAntiFundamental B repGauge T) (x : B) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hdc : ∀ g : GaugeGroupI, repGauge g (deltaContraction T) = deltaContraction T)
    (hx : x ∈ Submodule.span ℂ (Set.range T) ⊔ S) (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    ∃ c : ℂ, ∃ y ∈ S, x = c • deltaContraction T + y
      ∧ ∀ g : GaugeGroupI, repGauge g y = y := by
  obtain ⟨w, hw, y, hy, rfl, hyinv⟩ := (isFixedBy_span_singleton hdc).exists_add_of_mem_sup
    ((reducesInvariantsTo_span_deltaContraction _ hT.repGauge_T).comp
      (σ := fun g => repGauge g) (fun V => (1, V, 1)) S hS x hx hinv) hinv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
  exact ⟨c, y, hy, rfl, hyinv⟩

end IsSU2FundamentalAntiFundamental

end StandardModel
