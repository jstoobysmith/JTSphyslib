/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.Quotient.Basic
/-!
# Reducing invariants modulo a stable submodule

Let `σ : G → B →ₗ[R] B` be a family of linear maps, indexed by an arbitrary type. No group or
representation law is assumed. An element `x` is invariant when `σ g x = x` for every `g`, and
a submodule is stable when every `σ g` carries it into itself.

The relation `ReducesInvariantsTo σ V W` says: for every stable submodule `S`, every invariant
of `V ⊔ S` lies in `W ⊔ S`. It is transitive, antitone in the source, monotone in the target
and, for stable sources and a stable target, closed under finite joins of the source. A
classification of the invariants of a family can therefore be applied one family at a time,
the other families being kept in the stable remainder `S`.

Such a reduction is usually proved in the quotient `B ⧸ S`. If every invariant of the image of
`V` in `B ⧸ S` lies in the image of `W`, then every invariant of `V ⊔ S` lies in `W ⊔ S`, and
when `W` is pointwise fixed the remainder in `S` is itself invariant:
`IsStableUnder.exists_add_of_quotient`. The quotient hypothesis is not implied by a
classification of the invariants of `V` alone, since the invariants of `B ⧸ S` are the classes
`x` with `σ g x - x ∈ S`.

`InvariantReductionToSpan σ V` packages a reduction of `V` to the span of one fixed vector,
the form in which the classification theorems are applied.

- A. Stable and fixed submodules
- B. Reducing invariants
- C. Reduction through a quotient
- D. Reduction to the span of one vector

-/

@[expose] public section

/-!

## A. Stable and fixed submodules

-/

section Stability

variable {R B G : Type*} [Semiring R] [AddCommMonoid B] [Module R B]

/-- A submodule carried into itself by every map of the family `σ`. -/
def IsStableUnder (σ : G → B →ₗ[R] B) (V : Submodule R B) : Prop :=
  ∀ g, ∀ y ∈ V, σ g y ∈ V

/-- A submodule fixed pointwise by every map of the family `σ`. -/
def IsFixedBy (σ : G → B →ₗ[R] B) (V : Submodule R B) : Prop :=
  ∀ g, ∀ y ∈ V, σ g y = y

variable {σ : G → B →ₗ[R] B}

/-- Stability as an inclusion of images. -/
lemma isStableUnder_iff_map {V : Submodule R B} :
    IsStableUnder σ V ↔ ∀ g, Submodule.map (σ g) V ≤ V := by
  constructor
  · rintro hV g _ ⟨y, hy, rfl⟩
    exact hV g y hy
  · exact fun hV g y hy => hV g ⟨y, hy, rfl⟩

/-- A pointwise-fixed submodule is stable. -/
lemma IsFixedBy.isStableUnder {V : Submodule R B} (hV : IsFixedBy σ V) : IsStableUnder σ V :=
  fun g y hy => by rw [hV g y hy]; exact hy

/-- A join of two pointwise-fixed submodules is pointwise fixed. -/
lemma IsFixedBy.sup {V V' : Submodule R B} (hV : IsFixedBy σ V) (hV' : IsFixedBy σ V') :
    IsFixedBy σ (V ⊔ V') := by
  intro g y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
  rw [map_add, hV g a ha, hV' g b hb]

/-- The zero submodule is stable. -/
lemma isStableUnder_bot : IsStableUnder σ (⊥ : Submodule R B) := by
  intro g y hy
  rw [Submodule.mem_bot] at hy
  simp [hy]

/-- A join of two stable submodules is stable. -/
lemma IsStableUnder.sup {V V' : Submodule R B} (hV : IsStableUnder σ V)
    (hV' : IsStableUnder σ V') : IsStableUnder σ (V ⊔ V') :=
  isStableUnder_iff_map.2 fun g => by
    rw [Submodule.map_sup]
    exact sup_le_sup (isStableUnder_iff_map.1 hV g) (isStableUnder_iff_map.1 hV' g)

/-- An indexed join of stable submodules is stable. The index is a `Sort`, so this covers
  the bounded join `⨆ i ∈ s, V i`. -/
lemma isStableUnder_iSup {ι : Sort*} {V : ι → Submodule R B}
    (hV : ∀ i, IsStableUnder σ (V i)) : IsStableUnder σ (⨆ i, V i) :=
  isStableUnder_iff_map.2 fun g => by
    rw [Submodule.map_iSup]
    exact iSup_mono fun i => isStableUnder_iff_map.1 (hV i) g

/-- The span of a fixed vector is pointwise fixed. -/
lemma isFixedBy_span_singleton {b : B} (hb : ∀ g, σ g b = b) : IsFixedBy σ (R ∙ b) := by
  intro g y hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  rw [map_smul, hb]

/-- An indexed join of pointwise-fixed submodules is pointwise fixed. -/
lemma isFixedBy_iSup {ι : Sort*} {V : ι → Submodule R B} (hV : ∀ i, IsFixedBy σ (V i)) :
    IsFixedBy σ (⨆ i, V i) := by
  intro g y hy
  refine Submodule.iSup_induction (motive := fun z => σ g z = z) V hy (fun i z hz => hV i g z hz)
    (map_zero _) fun z z' hz hz' => by rw [map_add, hz, hz']

/-- The span of a family of fixed vectors is pointwise fixed. -/
lemma isFixedBy_iSup_span_singleton {ι : Sort*} {T : ι → B} (hT : ∀ i g, σ g (T i) = T i) :
    IsFixedBy σ (⨆ i, R ∙ T i) :=
  isFixedBy_iSup fun i => isFixedBy_span_singleton (hT i)

/-- The span of a family is stable when each map sends each member into the span. -/
lemma isStableUnder_iSup_span_singleton {ι : Type*} {T : ι → B}
    (hT : ∀ g i, σ g (T i) ∈ ⨆ j, R ∙ T j) : IsStableUnder σ (⨆ i, R ∙ T i) :=
  isStableUnder_iff_map.2 fun g => by
    rw [Submodule.map_iSup]
    exact iSup_le fun i => by
      rw [Submodule.map_span, Set.image_singleton, Submodule.span_singleton_le_iff_mem]
      exact hT g i

/-- The span of a finite family is stable when each map sends each member to a combination
  of the family. -/
lemma isStableUnder_iSup_span_singleton_of_sum {ι : Type*} [Fintype ι] {T : ι → B}
    (hT : ∀ g i, ∃ c : ι → R, σ g (T i) = ∑ a, c a • T a) :
    IsStableUnder σ (⨆ i, R ∙ T i) := by
  refine isStableUnder_iSup_span_singleton fun g i => ?_
  obtain ⟨c, hc⟩ := hT g i
  rw [hc]
  exact sum_mem fun a _ => Submodule.smul_mem _ _
    (Submodule.mem_iSup_of_mem a (Submodule.mem_span_singleton_self _))

/-- A product of two stable submodules of an algebra is stable under maps respecting
  multiplication. -/
lemma IsStableUnder.mul {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    {σ : G → A →ₗ[R] A} (hσ : ∀ g (a b : A), σ g (a * b) = σ g a * σ g b)
    {V V' : Submodule R A} (hV : IsStableUnder σ V) (hV' : IsStableUnder σ V') :
    IsStableUnder σ (V * V') :=
  isStableUnder_iff_map.2 fun g => by
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.mul_le.2 fun a ha b hb => ?_
    show σ g (a * b) ∈ V * V'
    rw [hσ]
    exact Submodule.mul_mem_mul (hV g a ha) (hV' g b hb)

end Stability

/-!

## B. Reducing invariants

To reduce `V₁ ⊔ V₂` to `W`, the summand `V₂` is first moved into the remainder, which needs `V₂`
stable; the result lies in `W ⊔ (V₂ ⊔ S)`, and reducing `V₂` from there needs `W` stable.

-/

section Reduction

variable {R B G : Type*} [Semiring R] [AddCommMonoid B] [Module R B] {σ : G → B →ₗ[R] B}

/-- Every invariant of `V ⊔ S`, for `S` a `σ`-stable submodule, lies in `W ⊔ S`. -/
def ReducesInvariantsTo (σ : G → B →ₗ[R] B) (V W : Submodule R B) : Prop :=
  ∀ S : Submodule R B, IsStableUnder σ S → ∀ x ∈ V ⊔ S, (∀ g, σ g x = x) → x ∈ W ⊔ S

/-- A submodule reduces to any submodule containing it. -/
lemma reducesInvariantsTo_of_le {V W : Submodule R B} (hVW : V ≤ W) :
    ReducesInvariantsTo σ V W :=
  fun S _ _ hx _ => sup_le_sup_right hVW S hx

/-- A reduction restricts to a smaller source. -/
lemma ReducesInvariantsTo.mono_left {V V' W : Submodule R B} (hP : ReducesInvariantsTo σ V' W)
    (hV : V ≤ V') : ReducesInvariantsTo σ V W :=
  fun S hS x hx hinv => hP S hS x (sup_le_sup_right hV S hx) hinv

/-- A reduction extends to a larger target. -/
lemma ReducesInvariantsTo.mono_right {V W W' : Submodule R B}
    (hP : ReducesInvariantsTo σ V W') (hW : W' ≤ W) : ReducesInvariantsTo σ V W :=
  fun S hS x hx hinv => sup_le_sup_right hW S (hP S hS x hx hinv)

/-- Successive reductions compose. -/
lemma ReducesInvariantsTo.trans {V W W' : Submodule R B} (hP : ReducesInvariantsTo σ V W)
    (hQ : ReducesInvariantsTo σ W W') : ReducesInvariantsTo σ V W' :=
  fun S hS x hx hinv => hQ S hS x (hP S hS x hx hinv) hinv

/-- Reductions of `V` and of a stable `V'` to a common stable target combine to a reduction of
  `V ⊔ V'`. -/
lemma ReducesInvariantsTo.sup {V V' W : Submodule R B} (hP : ReducesInvariantsTo σ V W)
    (hQ : ReducesInvariantsTo σ V' W) (hV' : IsStableUnder σ V') (hW : IsStableUnder σ W) :
    ReducesInvariantsTo σ (V ⊔ V') W := by
  intro S hS x hx hinv
  have h : x ∈ W ⊔ (V' ⊔ S) := hP (V' ⊔ S) (hV'.sup hS) x (by rwa [← sup_assoc]) hinv
  rw [sup_left_comm] at h
  have h' := hQ (W ⊔ S) (hW.sup hS) x h hinv
  rwa [← sup_assoc, sup_idem] at h'

/-- Reductions of stable submodules to a common stable target combine over a finite set. -/
lemma ReducesInvariantsTo.biSup {ι : Type*} [DecidableEq ι] {V : ι → Submodule R B}
    {W : Submodule R B} (hP : ∀ i, ReducesInvariantsTo σ (V i) W)
    (hV : ∀ i, IsStableUnder σ (V i)) (hW : IsStableUnder σ W) (s : Finset ι) :
    ReducesInvariantsTo σ (⨆ i ∈ s, V i) W := by
  induction s using Finset.induction_on with
  | empty => exact reducesInvariantsTo_of_le (by simp)
  | @insert a s _ ih =>
    rw [Finset.iSup_insert]
    exact (hP a).sup ih (isStableUnder_iSup fun i => isStableUnder_iSup fun _ => hV i) hW

/-- Reductions of stable submodules to a common stable target combine over a finite index
  type. -/
lemma ReducesInvariantsTo.iSup {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : ι → Submodule R B} {W : Submodule R B} (hP : ∀ i, ReducesInvariantsTo σ (V i) W)
    (hV : ∀ i, IsStableUnder σ (V i)) (hW : IsStableUnder σ W) :
    ReducesInvariantsTo σ (⨆ i, V i) W :=
  (ReducesInvariantsTo.biSup hP hV hW Finset.univ).mono_left
    (iSup_le fun i => le_iSup₂_of_le i (Finset.mem_univ i) le_rfl)

/-- A reduction for the subfamily `σ ∘ ι` is a reduction for `σ`: an invariant of `σ` is an
  invariant of the subfamily, and a `σ`-stable submodule is stable under the subfamily. -/
lemma ReducesInvariantsTo.comp {G' : Type*} (ι : G' → G) {V W : Submodule R B}
    (hP : ReducesInvariantsTo (fun g' => σ (ι g')) V W) : ReducesInvariantsTo σ V W :=
  fun S hS x hx hinv => hP S (fun g' y hy => hS (ι g') y hy) x hx fun g' => hinv (ι g')

end Reduction

/-!

## C. Reduction through a quotient

For a `σ`-stable `S`, the maps `S.mapQ S (σ g) _` act on `B ⧸ S`. The hypotheses below classify
invariants of that action on the image of the source, which is where a classification valid in
every module is applied.

-/

/-- The image of the span of a family is the span of the images. -/
lemma Submodule.map_iSup_span_singleton {R M M₂ ι : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [AddCommMonoid M₂] [Module R M₂] (f : M →ₗ[R] M₂) (T : ι → M) :
    (⨆ i, R ∙ T i).map f = ⨆ i, R ∙ f (T i) := by
  simp only [Submodule.map_iSup, Submodule.map_span, Set.image_singleton]

section Quotient

variable {R B G : Type*} [Ring R] [AddCommGroup B] [Module R B] {σ : G → B →ₗ[R] B}
  {S V W : Submodule R B}

/-- An invariant of `V ⊔ S` lies in `W ⊔ S` when every invariant of the image of `V` in
  `B ⧸ S` lies in the image of `W`. -/
lemma IsStableUnder.mem_sup_of_quotient (hS : IsStableUnder σ S)
    (hclass : ∀ x ∈ V.map S.mkQ, (∀ g, S.mapQ S (σ g) (hS g) x = x) → x ∈ W.map S.mkQ)
    {x : B} (hx : x ∈ V ⊔ S) (hinv : ∀ g, σ g x = x) : x ∈ W ⊔ S := by
  rw [sup_comm, ← Submodule.comap_map_mkQ, Submodule.mem_comap] at hx ⊢
  exact hclass _ hx fun g => by rw [Submodule.mkQ_apply, Submodule.mapQ_apply, hinv]

/-- `V` reduces to `W` when, for every stable `S`, every invariant of the image of `V` in
  `B ⧸ S` lies in the image of `W`. -/
lemma reducesInvariantsTo_of_quotient
    (hclass : ∀ S : Submodule R B, ∀ hS : IsStableUnder σ S, ∀ x ∈ V.map S.mkQ,
      (∀ g, S.mapQ S (σ g) (hS g) x = x) → x ∈ W.map S.mkQ) :
    ReducesInvariantsTo σ V W :=
  fun S hS _ hx hinv => hS.mem_sup_of_quotient (hclass S hS) hx hinv

/-- An invariant of `W ⊔ S`, for `W` pointwise fixed, is an element of `W` plus an invariant
  element of `S`. -/
lemma IsFixedBy.exists_add_of_mem_sup (hW : IsFixedBy σ W) {x : B} (hx : x ∈ W ⊔ S)
    (hinv : ∀ g, σ g x = x) : ∃ w ∈ W, ∃ y ∈ S, x = w + y ∧ ∀ g, σ g y = y := by
  obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
  refine ⟨w, hw, y, hy, rfl, fun g => add_left_cancel (a := w) ?_⟩
  have h := hinv g
  rwa [map_add, hW g w hw] at h

/-- Quotient to remainder: when every invariant of the image of `V` in `B ⧸ S` lies in the
  image of a pointwise-fixed `W`, an invariant of `V ⊔ S` is an element of `W` plus an
  invariant element of `S`. -/
lemma IsStableUnder.exists_add_of_quotient (hS : IsStableUnder σ S) (hW : IsFixedBy σ W)
    (hclass : ∀ x ∈ V.map S.mkQ, (∀ g, S.mapQ S (σ g) (hS g) x = x) → x ∈ W.map S.mkQ)
    {x : B} (hx : x ∈ V ⊔ S) (hinv : ∀ g, σ g x = x) :
    ∃ w ∈ W, ∃ y ∈ S, x = w + y ∧ ∀ g, σ g y = y :=
  hW.exists_add_of_mem_sup (hS.mem_sup_of_quotient hclass hx hinv) hinv

/-- Quotient to remainder for a single fixed vector `v`: when every invariant of the image of
  `V` in `B ⧸ S` is a multiple of the class of `v`, an invariant of `V ⊔ S` is a multiple of
  `v` plus an invariant element of `S`. -/
lemma IsStableUnder.exists_smul_add_of_quotient (hS : IsStableUnder σ S) {v : B}
    (hv : ∀ g, σ g v = v)
    (hclass : ∀ x ∈ V.map S.mkQ, (∀ g, S.mapQ S (σ g) (hS g) x = x) → ∃ c : R, x = c • S.mkQ v)
    {x : B} (hx : x ∈ V ⊔ S) (hinv : ∀ g, σ g x = x) :
    ∃ c : R, ∃ y ∈ S, x = c • v + y ∧ ∀ g, σ g y = y := by
  obtain ⟨w, hw, y, hy, rfl, hyinv⟩ := hS.exists_add_of_quotient (isFixedBy_span_singleton hv)
    (fun x hx hinv => by
      obtain ⟨c, rfl⟩ := hclass x hx hinv
      exact ⟨c • v, Submodule.smul_mem _ c (Submodule.mem_span_singleton_self v),
        map_smul _ c v⟩) hx hinv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
  exact ⟨c, y, hy, rfl, hyinv⟩

end Quotient

/-!

## D. Reduction to the span of one vector

-/

section Span

variable {R B G : Type*} [Semiring R] [AddCommMonoid B] [Module R B] {σ : G → B →ₗ[R] B}

/-- A stable submodule `V` together with a fixed vector such that, for every stable `S`, every
  invariant of `V ⊔ S` is a multiple of that vector plus an element of `S`. The vector need not
  be nonzero or lie in `V`. -/
structure InvariantReductionToSpan (σ : G → B →ₗ[R] B) (V : Submodule R B) where
  /-- The vector whose span receives the invariants of `V`. -/
  spanningVector : B
  /-- The submodule is stable. -/
  stable : IsStableUnder σ V
  /-- The spanning vector is invariant. -/
  spanningVector_fixed : ∀ g, σ g spanningVector = spanningVector
  /-- An invariant of `V ⊔ S`, for `S` stable, is a multiple of the spanning vector plus an
    element of `S`. -/
  reduce : ∀ S : Submodule R B, IsStableUnder σ S → ∀ x ∈ V ⊔ S, (∀ g, σ g x = x) →
    ∃ c : R, ∃ y ∈ S, x = c • spanningVector + y

namespace InvariantReductionToSpan

variable {V : Submodule R B}

/-- The submodule reduces to the span of the spanning vector. -/
lemma reducesInvariantsTo (r : InvariantReductionToSpan σ V) :
    ReducesInvariantsTo σ V (R ∙ r.spanningVector) := by
  intro S hS x hx hinv
  obtain ⟨c, y, hy, rfl⟩ := r.reduce S hS x hx hinv
  exact Submodule.add_mem_sup (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)) hy

/-- A finite family of reductions to spans reduces the join of the submodules to the span of
  the spanning vectors. -/
lemma reducesInvariantsTo_iSup {κ : Type*} [Fintype κ] [DecidableEq κ]
    {V : κ → Submodule R B} (r : ∀ k, InvariantReductionToSpan σ (V k)) :
    ReducesInvariantsTo σ (⨆ k, V k) (⨆ k, R ∙ (r k).spanningVector) :=
  ReducesInvariantsTo.iSup
    (fun k => (r k).reducesInvariantsTo.mono_right
      (le_iSup (fun k' => R ∙ (r k').spanningVector) k))
    (fun k => (r k).stable)
    (isFixedBy_iSup_span_singleton fun k => (r k).spanningVector_fixed).isStableUnder

/-- The span of a fixed vector reduces to itself. -/
def ofFixed (b : B) (hb : ∀ g, σ g b = b) :
    InvariantReductionToSpan σ (R ∙ b) where
  spanningVector := b
  stable := (isFixedBy_span_singleton hb).isStableUnder
  spanningVector_fixed := hb
  reduce S _ x hx _ := by
    obtain ⟨a, ha, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ha
    exact ⟨c, y, hy, rfl⟩

/-- The span of a nonempty family whose members all equal one fixed vector reduces to the
  span of that vector. -/
def ofFixedFamily {ι : Type*} [Nonempty ι] {T : ι → B} (b : B)
    (hTb : ∀ i, T i = b) (hb : ∀ g, σ g b = b) : InvariantReductionToSpan σ (⨆ i, R ∙ T i) :=
  have hspan : (⨆ i, R ∙ T i) = R ∙ b := by simp only [hTb, iSup_const]
  { spanningVector := b
    stable := hspan ▸ (ofFixed b hb).stable
    spanningVector_fixed := hb
    reduce := hspan ▸ (ofFixed b hb).reduce }

end InvariantReductionToSpan

end Span
