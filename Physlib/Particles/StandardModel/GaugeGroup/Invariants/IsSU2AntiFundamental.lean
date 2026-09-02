/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.IsSU2BiFundamental
/-!
# Gauge tensors carrying anti-fundamental `su(2)` indices

`IsSU2FunAntiFun B repGauge T` and `IsSU2BiAntiFun B repGauge T` are the two twisted
companions of `IsSU2BiFundamental`: a family indexed by one fundamental and one
anti-fundamental `su(2)` index, and a family indexed by two anti-fundamental ones. Between
them and `IsSU2BiFundamental` they cover the isospin content of every surviving term of the
Standard Model Yukawa sector, `2 ⊗ 2̄` for the down and lepton couplings and their
conjugates, `2̄ ⊗ 2̄` for the up coupling, `2 ⊗ 2` for its conjugate.

Neither needs a classification of its own, and that is the point of the file. `SU(2)` is
pseudo-real: for `U` in `SU(2)` and `ε` the antisymmetric symbol, `conj U = ε U ε⁻¹`, and
because `U` is unitary the matrix moving an anti-fundamental index, `(U⁻¹)ᵀ`, is `conj U`.
Those two identities are proved in section E of `IsSU2BiFundamental`, and they say that the
anti-fundamental representation is the fundamental one in a different basis. So re-indexing
an anti-fundamental slot by `ε` turns the law into the bi-fundamental one, for the very same
representation: no twisted representation, no transfer of invariance along a group
automorphism, nothing but a change of basis in one slot. `SU(3)` has no analogue, which is
why the colour side needs a separate `IsSU3FunAntiFun` and the isospin side does not.

Each re-index is invertible, so it leaves the span of the components alone, and every
conclusion of `IsSU2BiFundamental` — the classification of the isospin invariants, its
module-valued form, and its form modulo a stable submodule — transfers to the original
family. All that has to be tracked is which contraction of the original family the epsilon
contraction of the re-indexed one turns out to be. For `2 ⊗ 2̄` it is minus the delta
contraction `T^{0}{}_{0} + T^{1}{}_{1}`; for `2̄ ⊗ 2̄` it is the epsilon contraction itself,
with no sign at all. Those two factors are stated rather than absorbed into the definitions,
so that a re-index stays the plain re-index by `ε` and a contraction stays the plain trace
or the plain antisymmetric combination.

Both propositions inherit the weakness of `IsSU2BiFundamental`: they constrain the isospin
transformation `(1, U, 1)` alone and say nothing whatever about the colour and hypercharge
factors, so the conclusions are about invariance under the isospin factor, and every
statement about gauge invariance carries the invariance of the contraction as an explicit
hypothesis.

Section A is the `2 ⊗ 2̄` case, with its epsilon re-index, its delta contraction and the
classifications that follow, and section B the `2̄ ⊗ 2̄` case in the same order.
-/

@[expose] public section

namespace StandardModel

open Matrix ComplexConjugate

/-!

## A. One fundamental and one anti-fundamental isospin index

Four of the six surviving Yukawa terms contract a Higgs doublet against a quark or lepton
doublet of the opposite variance, so their isospin content is `2 ⊗ 2̄` rather than `2 ⊗ 2`.
`IsSU2FunAntiFun` records that law: a factor of `U` for the first index and a factor of
`conj U` for the second, the summed index in the row slot as always, and, as in
`IsSU2BiFundamental`, only the isospin transformation `(1, U, 1)` is constrained. It is the
law obeyed by `fun l => h.barHiggs d (l 0) * h.higgs d (l 1)` for `h : IsHiggsSector`, a
conjugate Higgs symbol and then a Higgs symbol, once the hypercharge character is set
aside; the anti-fundamental slot is the second one, so a family carrying its indices the
other way round must be presented with its two slots exchanged.

Section E of `IsSU2BiFundamental` is what makes this cheap. Because `conj U = ε U ε⁻¹`,
re-indexing the anti-fundamental slot by the antisymmetric symbol turns the law into the
bi-fundamental one, with the very same representation: no twisted representation, no transfer of
invariance along a group automorphism, nothing but a change of basis in one slot. The
re-index is invertible, so the span is unchanged, and every conclusion of
`IsSU2BiFundamental` is available for the original family once one knows which of its
contractions the epsilon contraction of the re-indexed family is.

That contraction is the delta contraction `T^{0}{}_{0} + T^{1}{}_{1}`, the only invariant
`2 ⊗ 2̄` admits, and the identification carries a sign: `epsilonContraction (reindex T)` is
`-deltaContraction T`. The sign is stated rather than absorbed into the definition, so that
`reindex` stays the plain re-index by `ε` and the delta contraction stays the plain trace.
Every classification below is the corresponding one of `IsSU2BiFundamental` read through
that sign, and each is stated for a family valued in a mere module, the square-zero
extension of that file having already removed the algebra hypotheses.

`of_isSU2BiFundamental` runs the re-index the other way and is the check that the variance
is the right way round: it produces genuine `IsSU2FunAntiFun` families out of the
bi-fundamental families the file already has, and it would fail if the conjugate had been
put on the wrong slot.

-/

/-- The linear map `f` moves the components of the family `T` as the `SU(2)` matrix `U`
  moves a tensor with one fundamental and one anti-fundamental isospin index: a factor of
  `U` for the first index, a factor of its complex conjugate for the second, with the
  summed index in the row slot. -/
def IsSU2FunAntiFunMat {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (U : specialUnitaryGroup (Fin 2) ℂ) (f : B →ₗ[ℂ] B)
    (T : (Fin 2 → Fin 2) → B) : Prop :=
  ∀ l : Fin 2 → Fin 2,
    f (T l) = ∑ a : Fin 2 → Fin 2, (U.1 (a 0) (l 0) * conj (U.1 (a 1) (l 1))) • T a

/-- A family `T` of elements of `B`, indexed by one `su(2)` fundamental index and one
  anti-fundamental one, transforms as a tensor `T^{a}{}_{b}` under the representation
  `repGauge` of the gauge group: an isospin transformation moves the components by the
  `SU(2)` element it is built from. As with `IsSU2BiFundamental`, nothing is asked of the
  colour or hypercharge factors. -/
structure IsSU2FunAntiFun (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B)
    (T : (Fin 2 → Fin 2) → B) : Prop where
  repGauge_T : ∀ g : specialUnitaryGroup (Fin 2) ℂ,
    IsSU2FunAntiFunMat g (repGauge (1, g, 1)) T

namespace IsSU2FunAntiFun
set_option linter.unusedVariables false
open IsSU2BiFundamental

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {U : specialUnitaryGroup (Fin 2) ℂ} {f : B →ₗ[ℂ] B}

/-!

## A.1. The epsilon re-index of the anti-fundamental slot

-/

/-- The family obtained by re-indexing the anti-fundamental slot with the antisymmetric
  symbol. This is the change of basis of section E of `IsSU2BiFundamental` applied to the second
  index alone, and it is what turns the anti-fundamental law into the bi-fundamental one. -/
def reindex (T : (Fin 2 → Fin 2) → B) : (Fin 2 → Fin 2) → B :=
  fun l => ∑ m : Fin 2, epsilon (l 1) m • T ![l 0, m]

/-- The re-index at a second index `0` picks out the component with second index `1`. -/
@[simp] lemma reindex_apply_zero (T : (Fin 2 → Fin 2) → B) (p : Fin 2) :
    reindex T ![p, 0] = T ![p, 1] := by
  simp [reindex, Fin.sum_univ_two]

/-- The re-index at a second index `1` picks out minus the component with second index
  `0`. -/
@[simp] lemma reindex_apply_one (T : (Fin 2 → Fin 2) → B) (p : Fin 2) :
    reindex T ![p, 1] = -T ![p, 0] := by
  simp [reindex, Fin.sum_univ_two]

/-- The re-indexed family obeys the bi-fundamental law. This is the whole content of the
  section: the four entry identities of `IsSU2BiFundamental` remove every complex conjugate,
  after which the two sides differ by nothing at all. -/
lemma map_reindex {T : (Fin 2 → Fin 2) → B} (hf : IsSU2FunAntiFunMat U f T) :
    IsSU2BiFundamentalMat U f (reindex T) := by
  have hl : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
  have hf' : ∀ k : Fin 2 → Fin 2, f (T k)
      = ∑ a : Fin 2 → Fin 2, (U.1 (a 0) (k 0) * conj (U.1 (a 1) (k 1))) • T a := hf
  intro l
  simp only [reindex, map_add, map_smul, hf', sum_pi_two, Fin.sum_univ_two,
    Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rcases hl (l 0) with h0 | h0 <;> rcases hl (l 1) with h1 | h1 <;> rw [h0, h1] <;>
    simp only [epsilon_zero_zero, epsilon_zero_one, epsilon_one_zero, epsilon_one_one,
      conj_apply_zero_zero, conj_apply_zero_one, conj_apply_one_zero,
      conj_apply_one_one] <;>
    module

/-- The re-index of a fundamental and anti-fundamental family is a bi-fundamental family
  for the same representation. -/
lemma isSU2BiFundamental_reindex {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2FunAntiFun B repGauge T) :
    IsSU2BiFundamental B repGauge (reindex T) where
  repGauge_T g := map_reindex (hT.repGauge_T g)

/-- The re-index run the other way: the second index of a bi-fundamental family, re-indexed
  by the antisymmetric symbol, is an anti-fundamental index. Together with
  `map_reindex` this says that the two laws are the same law in two bases, and it is what
  exhibits families obeying the anti-fundamental law: any bi-fundamental family gives
  one. -/
lemma map_reindex_of_biFundamental {T : (Fin 2 → Fin 2) → B}
    (hf : IsSU2BiFundamentalMat U f T) :
    IsSU2FunAntiFunMat U f (reindex T) := by
  have hl : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
  have hf' : ∀ k : Fin 2 → Fin 2, f (T k)
      = ∑ a : Fin 2 → Fin 2, (∏ i : Fin 2, U.1 (a i) (k i)) • T a := hf
  intro l
  simp only [reindex, map_add, map_smul, hf', sum_pi_two, Fin.sum_univ_two,
    Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rcases hl (l 0) with h0 | h0 <;> rcases hl (l 1) with h1 | h1 <;> rw [h0, h1] <;>
    simp only [epsilon_zero_zero, epsilon_zero_one, epsilon_one_zero, epsilon_one_one,
      conj_apply_zero_zero, conj_apply_zero_one, conj_apply_one_zero,
      conj_apply_one_one] <;>
    module

/-- Every bi-fundamental family yields a fundamental and anti-fundamental one, by the same
  re-index. This is the non-vacuity of the proposition: the products of conjugate Higgs
  doublet symbols that obey `IsSU2BiFundamental` obey this law once one of their slots is
  re-indexed. -/
lemma of_isSU2BiFundamental {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2BiFundamental B repGauge T) :
    IsSU2FunAntiFun B repGauge (reindex T) where
  repGauge_T g := map_reindex_of_biFundamental (hT.repGauge_T g)

/-- Every component of the original family lies in the span of the re-indexed one, the
  re-index being invertible. -/
lemma self_mem_span_reindex (T : (Fin 2 → Fin 2) → B) (d : Fin 2 → Fin 2) :
    T d ∈ span (reindex T) := by
  have hl : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
  have hd : T d = T ![d 0, d 1] := by rw [← eq_cons]
  rw [hd]
  rcases hl (d 1) with h1 | h1 <;> rw [h1]
  · rw [show T ![d 0, (0 : Fin 2)] = -reindex T ![d 0, 1] from by
      rw [reindex_apply_one, neg_neg]]
    exact neg_mem (mem_span _)
  · rw [← reindex_apply_zero T (d 0)]
    exact mem_span _

/-- The re-index does not change the span of the components, being invertible. This is what
  lets every conclusion below be stated with the span of the original family. -/
lemma span_reindex (T : (Fin 2 → Fin 2) → B) : span (reindex T) = span T := by
  refine le_antisymm (iSup_le fun d => ?_) (iSup_le fun d => ?_)
  · rw [Submodule.span_singleton_le_iff_mem, reindex]
    exact sum_mem fun m _ => Submodule.smul_mem _ _ (mem_span _)
  · rw [Submodule.span_singleton_le_iff_mem]
    exact self_mem_span_reindex T d

/-!

## A.2. The delta contraction

-/

/-- The delta contraction of a family carrying one fundamental and one anti-fundamental
  isospin index: the trace, which is the only invariant `2 ⊗ 2̄` admits. -/
def deltaContraction (T : (Fin 2 → Fin 2) → B) : B := T ![0, 0] + T ![1, 1]

/-- The delta contraction lies in the span of the components. -/
lemma deltaContraction_mem_span (T : (Fin 2 → Fin 2) → B) :
    deltaContraction T ∈ span T := by
  rw [deltaContraction]
  exact add_mem (mem_span _) (mem_span _)

/-- The epsilon contraction of the re-indexed family is minus the delta contraction of the
  original one. This is the sign the re-index introduces, and it is stated here rather than
  hidden in the definitions: the re-index sends the pair `(0, 1)` to `-T ![0,0]` and the
  pair `(1, 0)` to `T ![1,1]`, and the antisymmetric combination of those is minus the
  trace. -/
lemma epsilonContraction_reindex (T : (Fin 2 → Fin 2) → B) :
    epsilonContraction (reindex T) = -deltaContraction T := by
  rw [epsilonContraction, reindex_apply_zero, reindex_apply_one, deltaContraction]
  abel

/-- The delta contraction is fixed by any linear map moving the components by an element of
  `SU(2)`. It is the epsilon contraction of the re-indexed family up to sign, and that is
  fixed by `IsSU2BiFundamental.map_epsilonContraction`. -/
lemma map_deltaContraction {T : (Fin 2 → Fin 2) → B} (hf : IsSU2FunAntiFunMat U f T) :
    f (deltaContraction T) = deltaContraction T := by
  have h := map_epsilonContraction (map_reindex hf)
  rw [epsilonContraction_reindex, map_neg, neg_inj] at h
  exact h

/-- The delta contraction of a family with one fundamental and one anti-fundamental index
  is fixed by the isospin factor. That is all the transformation law constrains, the colour
  and hypercharge factors being free to move it. -/
lemma repGauge_deltaContraction {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2FunAntiFun B repGauge T) (V : specialUnitaryGroup (Fin 2) ℂ) :
    repGauge (1, V, 1) (deltaContraction T) = deltaContraction T :=
  map_deltaContraction (hT.repGauge_T V)

/-!

## A.3. The classification

-/

/-- Every isospin invariant in the span of the components is a multiple of the delta
  contraction. This is the classification of `IsSU2BiFundamental`, read through the re-index
  and the sign it carries, and it asks for no algebra structure on `B`, the square-zero
  extension having removed that. -/
lemma exists_smul_deltaContraction_of_su2_invariant {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2FunAntiFun B repGauge T) {x : B} (hx : x ∈ span T)
    (hinv : ∀ V : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, V, 1) x = x) :
    ∃ c : ℂ, x = c • deltaContraction T := by
  obtain ⟨c, hc⟩ :=
    hT.isSU2BiFundamental_reindex.exists_smul_epsilonContraction_of_su2_invariant_module
      (by rw [span_reindex]; exact hx) hinv
  refine ⟨-c, ?_⟩
  rw [hc, epsilonContraction_reindex, smul_neg, neg_smul]

/-- Every gauge invariant in the span of the components is a multiple of the delta
  contraction, a gauge invariant being in particular fixed by the isospin factor. -/
lemma exists_smul_deltaContraction_of_invariant {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2FunAntiFun B repGauge T) {x : B} (hx : x ∈ span T)
    (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    ∃ c : ℂ, x = c • deltaContraction T :=
  hT.exists_smul_deltaContraction_of_su2_invariant hx fun V => hinv (1, V, 1)

/-- The isospin invariants in the span of the components are exactly the multiples of the
  delta contraction. This is the one singlet of `2 ⊗ 2̄`. -/
lemma mem_span_and_su2_invariant_iff {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2FunAntiFun B repGauge T) (x : B) :
    (x ∈ span T ∧ ∀ V : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, V, 1) x = x)
      ↔ x ∈ ℂ ∙ deltaContraction T := by
  refine ⟨fun h => ?_, fun hx => ?_⟩
  · obtain ⟨c, rfl⟩ := hT.exists_smul_deltaContraction_of_su2_invariant h.1 h.2
    exact Submodule.mem_span_singleton.2 ⟨c, rfl⟩
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    exact ⟨Submodule.smul_mem _ _ (deltaContraction_mem_span T),
      fun V => by rw [map_smul, repGauge_deltaContraction hT]⟩

/-- The gauge invariants in the span of the components are exactly the multiples of the
  delta contraction, once the delta contraction is known to be gauge invariant. That
  hypothesis cannot be dropped, for the reason given at
  `IsSU2BiFundamental.mem_span_and_invariant_iff`: the transformation law says nothing about
  the colour and hypercharge factors, and the hypercharge factor by itself can scale the
  contraction. -/
lemma mem_span_and_invariant_iff {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2FunAntiFun B repGauge T) (x : B)
    (hdc : ∀ g : GaugeGroupI,
      repGauge g (deltaContraction T) = deltaContraction T) :
    (x ∈ span T ∧ ∀ g : GaugeGroupI, repGauge g x = x)
      ↔ x ∈ ℂ ∙ deltaContraction T := by
  refine ⟨fun h => ?_, fun hx => ?_⟩
  · obtain ⟨c, rfl⟩ := hT.exists_smul_deltaContraction_of_invariant h.1 h.2
    exact Submodule.mem_span_singleton.2 ⟨c, rfl⟩
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    exact ⟨Submodule.smul_mem _ _ (deltaContraction_mem_span T),
      fun g => by rw [map_smul, hdc]⟩

/-- The isospin invariants of the span of the components together with an isospin-stable
  submodule `S`: such an element is a multiple of the delta contraction up to an error in
  `S`, and the error is fixed by the isospin factor too. This is the form in which one
  family at a time is peeled off a join. -/
lemma mem_span_sup_su2_invariant_iff {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2FunAntiFun B repGauge T) (x : B) (S : Submodule ℂ B)
    (hS : ∀ V : specialUnitaryGroup (Fin 2) ℂ, ∀ y ∈ S, repGauge (1, V, 1) y ∈ S)
    (hx : x ∈ span T ⊔ S)
    (hinv : ∀ V : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, V, 1) x = x) :
    ∃ c : ℂ, ∃ y ∈ S, x = c • deltaContraction T + y
      ∧ ∀ V : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, V, 1) y = y := by
  obtain ⟨c, y, hyS, hxy, hyinv⟩ :=
    hT.isSU2BiFundamental_reindex.mem_span_sup_su2_invariant_iff x S hS
      (by rw [span_reindex]; exact hx) hinv
  refine ⟨-c, y, hyS, ?_, hyinv⟩
  rw [hxy, epsilonContraction_reindex, smul_neg, neg_smul]

/-- The same modulo a gauge-stable submodule, which needs the gauge invariance of the delta
  contraction for the error term to be a gauge invariant rather than merely an isospin
  one. -/
lemma mem_span_sup_invariant_iff {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2FunAntiFun B repGauge T) (x : B) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hdc : ∀ g : GaugeGroupI,
      repGauge g (deltaContraction T) = deltaContraction T)
    (hx : x ∈ span T ⊔ S)
    (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    ∃ c : ℂ, ∃ y ∈ S, x = c • deltaContraction T + y
      ∧ ∀ g : GaugeGroupI, repGauge g y = y := by
  obtain ⟨c, y, hyS, hxy, hyinv⟩ :=
    hT.isSU2BiFundamental_reindex.mem_span_sup_invariant_iff x S hS
      (fun g => by rw [epsilonContraction_reindex, map_neg, hdc g])
      (by rw [span_reindex]; exact hx) hinv
  refine ⟨-c, y, hyS, ?_, hyinv⟩
  rw [hxy, epsilonContraction_reindex, smul_neg, neg_smul]

end IsSU2FunAntiFun

/-!

## B. Two anti-fundamental isospin indices

The up-type Yukawa `ε H Q ū` carries both of its doublet indices in the anti-fundamental,
so its isospin content is `2̄ ⊗ 2̄`. `IsSU2BiAntiFun` records that law, a factor of `conj U`
per index, and again only for the isospin transformation `(1, U, 1)`. It is the law obeyed
by `fun l => h.higgs d (l 0) * h.higgs d (l 1)` for `h : IsHiggsSector`, once the
hypercharge character is set aside; the corresponding product of two conjugate Higgs
symbols, `h.barHiggs`, obeys `IsSU2BiFundamental` instead.

The re-index of section E of `IsSU2BiFundamental` is applied to both slots at once, and
this time it costs nothing
at all: `epsilonContraction (reindex T)` is `epsilonContraction T` on the nose, the two
signs the re-index puts on the mixed components cancelling in their antisymmetric
combination. So the invariant of `2̄ ⊗ 2̄` is the same epsilon contraction as that of
`2 ⊗ 2`, and every conclusion of `IsSU2BiFundamental` transfers with no factor to keep
track of.
As with the re-index of one slot, the map is invertible, so the span is unchanged, and the
conclusions are stated with the span of the original family. `of_isSU2BiFundamental` again
runs the re-index the other way, which exhibits families obeying the law and checks that
the conjugates sit on the slots they should.

-/

/-- The linear map `f` moves the components of the family `T` as the `SU(2)` matrix `U`
  moves a tensor with two anti-fundamental isospin indices: one factor of the complex
  conjugate of `U` per index, with the summed index in the row slot. -/
def IsSU2BiAntiFunMat {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (U : specialUnitaryGroup (Fin 2) ℂ) (f : B →ₗ[ℂ] B)
    (T : (Fin 2 → Fin 2) → B) : Prop :=
  ∀ l : Fin 2 → Fin 2,
    f (T l) = ∑ a : Fin 2 → Fin 2,
      (conj (U.1 (a 0) (l 0)) * conj (U.1 (a 1) (l 1))) • T a

/-- A family `T` of elements of `B`, indexed by two `su(2)` anti-fundamental indices,
  transforms as a tensor `T_{a₁ a₂}` under the representation `repGauge` of the gauge
  group: an isospin transformation moves the components by the conjugate of the `SU(2)`
  element it is built from. Nothing is asked of the colour or hypercharge factors. -/
structure IsSU2BiAntiFun (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B)
    (T : (Fin 2 → Fin 2) → B) : Prop where
  repGauge_T : ∀ g : specialUnitaryGroup (Fin 2) ℂ,
    IsSU2BiAntiFunMat g (repGauge (1, g, 1)) T

namespace IsSU2BiAntiFun
set_option linter.unusedVariables false
open IsSU2BiFundamental

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {U : specialUnitaryGroup (Fin 2) ℂ} {f : B →ₗ[ℂ] B}

/-!

## B.1. The epsilon re-index of both slots

-/

/-- The family obtained by re-indexing both slots with the antisymmetric symbol: the change
  of basis of section E of `IsSU2BiFundamental` applied to each index in turn. -/
def reindex (T : (Fin 2 → Fin 2) → B) : (Fin 2 → Fin 2) → B :=
  fun l => ∑ m : Fin 2, ∑ n : Fin 2, (epsilon (l 0) m * epsilon (l 1) n) • T ![m, n]

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

/-- The re-indexed family obeys the bi-fundamental law: the four entry identities of
  `IsSU2BiFundamental` remove both complex conjugates, leaving the two sides identical. -/
lemma map_reindex {T : (Fin 2 → Fin 2) → B} (hf : IsSU2BiAntiFunMat U f T) :
    IsSU2BiFundamentalMat U f (reindex T) := by
  have hl : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
  have hf' : ∀ k : Fin 2 → Fin 2, f (T k)
      = ∑ a : Fin 2 → Fin 2,
        (conj (U.1 (a 0) (k 0)) * conj (U.1 (a 1) (k 1))) • T a := hf
  intro l
  simp only [reindex, map_add, map_smul, hf', sum_pi_two, Fin.sum_univ_two,
    Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rcases hl (l 0) with h0 | h0 <;> rcases hl (l 1) with h1 | h1 <;> rw [h0, h1] <;>
    simp only [epsilon_zero_zero, epsilon_zero_one, epsilon_one_zero, epsilon_one_one,
      conj_apply_zero_zero, conj_apply_zero_one, conj_apply_one_zero,
      conj_apply_one_one] <;>
    module

/-- The re-index of a family with two anti-fundamental indices is a bi-fundamental family
  for the same representation. -/
lemma isSU2BiFundamental_reindex {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2BiAntiFun B repGauge T) :
    IsSU2BiFundamental B repGauge (reindex T) where
  repGauge_T g := map_reindex (hT.repGauge_T g)

/-- The re-index run the other way: both indices of a bi-fundamental family, re-indexed by
  the antisymmetric symbol, are anti-fundamental. -/
lemma map_reindex_of_biFundamental {T : (Fin 2 → Fin 2) → B}
    (hf : IsSU2BiFundamentalMat U f T) :
    IsSU2BiAntiFunMat U f (reindex T) := by
  have hl : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
  have hf' : ∀ k : Fin 2 → Fin 2, f (T k)
      = ∑ a : Fin 2 → Fin 2, (∏ i : Fin 2, U.1 (a i) (k i)) • T a := hf
  intro l
  simp only [reindex, map_add, map_smul, hf', sum_pi_two, Fin.sum_univ_two,
    Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rcases hl (l 0) with h0 | h0 <;> rcases hl (l 1) with h1 | h1 <;> rw [h0, h1] <;>
    simp only [epsilon_zero_zero, epsilon_zero_one, epsilon_one_zero, epsilon_one_one,
      conj_apply_zero_zero, conj_apply_zero_one, conj_apply_one_zero,
      conj_apply_one_one] <;>
    module

/-- Every bi-fundamental family yields one with two anti-fundamental indices, by the same
  re-index. This is the non-vacuity of the proposition. -/
lemma of_isSU2BiFundamental {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2BiFundamental B repGauge T) :
    IsSU2BiAntiFun B repGauge (reindex T) where
  repGauge_T g := map_reindex_of_biFundamental (hT.repGauge_T g)

/-- Every component of the original family lies in the span of the re-indexed one, the
  re-index being an involution up to signs. -/
lemma self_mem_span_reindex (T : (Fin 2 → Fin 2) → B) (d : Fin 2 → Fin 2) :
    T d ∈ span (reindex T) := by
  have hl : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
  have hd : T d = T ![d 0, d 1] := by rw [← eq_cons]
  rw [hd]
  rcases hl (d 0) with h0 | h0 <;> rcases hl (d 1) with h1 | h1 <;> rw [h0, h1]
  · rw [← reindex_one_one T]
    exact mem_span _
  · rw [show T ![(0 : Fin 2), 1] = -reindex T ![1, 0] from by
      rw [reindex_one_zero, neg_neg]]
    exact neg_mem (mem_span _)
  · rw [show T ![(1 : Fin 2), 0] = -reindex T ![0, 1] from by
      rw [reindex_zero_one, neg_neg]]
    exact neg_mem (mem_span _)
  · rw [← reindex_zero_zero T]
    exact mem_span _

/-- The re-index does not change the span of the components. -/
lemma span_reindex (T : (Fin 2 → Fin 2) → B) : span (reindex T) = span T := by
  refine le_antisymm (iSup_le fun d => ?_) (iSup_le fun d => ?_)
  · rw [Submodule.span_singleton_le_iff_mem, reindex]
    exact sum_mem fun m _ => sum_mem fun n _ => Submodule.smul_mem _ _ (mem_span _)
  · rw [Submodule.span_singleton_le_iff_mem]
    exact self_mem_span_reindex T d

/-!

## B.2. The epsilon contraction

-/

/-- The re-index leaves the epsilon contraction alone: it exchanges the two mixed
  components and negates each, and the two signs cancel in their antisymmetric combination.
  So the invariant of `2̄ ⊗ 2̄` is the very `IsSU2BiFundamental.epsilonContraction`, with no
  sign and no scalar to carry. -/
lemma epsilonContraction_reindex (T : (Fin 2 → Fin 2) → B) :
    epsilonContraction (reindex T) = epsilonContraction T := by
  rw [epsilonContraction, reindex_zero_one, reindex_one_zero, epsilonContraction]
  abel

/-- The epsilon contraction is fixed by any linear map moving the components by an element
  of `SU(2)` in the anti-fundamental. -/
lemma map_epsilonContraction {T : (Fin 2 → Fin 2) → B} (hf : IsSU2BiAntiFunMat U f T) :
    f (epsilonContraction T) = epsilonContraction T := by
  have h := IsSU2BiFundamental.map_epsilonContraction (map_reindex hf)
  rwa [epsilonContraction_reindex] at h

/-- The epsilon contraction of a family with two anti-fundamental indices is fixed by the
  isospin factor, which is all the transformation law constrains. -/
lemma repGauge_epsilonContraction {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2BiAntiFun B repGauge T) (V : specialUnitaryGroup (Fin 2) ℂ) :
    repGauge (1, V, 1) (epsilonContraction T) = epsilonContraction T :=
  map_epsilonContraction (hT.repGauge_T V)

/-!

## B.3. The classification

-/

/-- Every isospin invariant in the span of the components is a multiple of the epsilon
  contraction. This is the classification of `IsSU2BiFundamental` read through the re-index,
  which this time contributes nothing at all. -/
lemma exists_smul_epsilonContraction_of_su2_invariant {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2BiAntiFun B repGauge T) {x : B} (hx : x ∈ span T)
    (hinv : ∀ V : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, V, 1) x = x) :
    ∃ c : ℂ, x = c • epsilonContraction T := by
  obtain ⟨c, hc⟩ :=
    hT.isSU2BiFundamental_reindex.exists_smul_epsilonContraction_of_su2_invariant_module
      (by rw [span_reindex]; exact hx) hinv
  exact ⟨c, by rw [hc, epsilonContraction_reindex]⟩

/-- Every gauge invariant in the span of the components is a multiple of the epsilon
  contraction. -/
lemma exists_smul_epsilonContraction_of_invariant {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2BiAntiFun B repGauge T) {x : B} (hx : x ∈ span T)
    (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    ∃ c : ℂ, x = c • epsilonContraction T :=
  hT.exists_smul_epsilonContraction_of_su2_invariant hx fun V => hinv (1, V, 1)

/-- The isospin invariants in the span of the components are exactly the multiples of the
  epsilon contraction. This is the one singlet of `2̄ ⊗ 2̄`. -/
lemma mem_span_and_su2_invariant_iff {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2BiAntiFun B repGauge T) (x : B) :
    (x ∈ span T ∧ ∀ V : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, V, 1) x = x)
      ↔ x ∈ ℂ ∙ epsilonContraction T := by
  refine ⟨fun h => ?_, fun hx => ?_⟩
  · obtain ⟨c, rfl⟩ := hT.exists_smul_epsilonContraction_of_su2_invariant h.1 h.2
    exact Submodule.mem_span_singleton.2 ⟨c, rfl⟩
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    exact ⟨Submodule.smul_mem _ _ (epsilonContraction_mem_span T),
      fun V => by rw [map_smul, repGauge_epsilonContraction hT]⟩

/-- The gauge invariants in the span of the components are exactly the multiples of the
  epsilon contraction, once the epsilon contraction is known to be gauge invariant. The
  hypothesis cannot be dropped: the transformation law leaves the colour and hypercharge
  factors free, and the hypercharge factor by itself can scale the contraction. -/
lemma mem_span_and_invariant_iff {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2BiAntiFun B repGauge T) (x : B)
    (hec : ∀ g : GaugeGroupI,
      repGauge g (epsilonContraction T) = epsilonContraction T) :
    (x ∈ span T ∧ ∀ g : GaugeGroupI, repGauge g x = x)
      ↔ x ∈ ℂ ∙ epsilonContraction T := by
  refine ⟨fun h => ?_, fun hx => ?_⟩
  · obtain ⟨c, rfl⟩ := hT.exists_smul_epsilonContraction_of_invariant h.1 h.2
    exact Submodule.mem_span_singleton.2 ⟨c, rfl⟩
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    exact ⟨Submodule.smul_mem _ _ (epsilonContraction_mem_span T),
      fun g => by rw [map_smul, hec]⟩

/-- The isospin invariants of the span of the components together with an isospin-stable
  submodule `S`: such an element is a multiple of the epsilon contraction up to an error in
  `S`, and the error is fixed by the isospin factor too. -/
lemma mem_span_sup_su2_invariant_iff {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2BiAntiFun B repGauge T) (x : B) (S : Submodule ℂ B)
    (hS : ∀ V : specialUnitaryGroup (Fin 2) ℂ, ∀ y ∈ S, repGauge (1, V, 1) y ∈ S)
    (hx : x ∈ span T ⊔ S)
    (hinv : ∀ V : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, V, 1) x = x) :
    ∃ c : ℂ, ∃ y ∈ S, x = c • epsilonContraction T + y
      ∧ ∀ V : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, V, 1) y = y := by
  obtain ⟨c, y, hyS, hxy, hyinv⟩ :=
    hT.isSU2BiFundamental_reindex.mem_span_sup_su2_invariant_iff x S hS
      (by rw [span_reindex]; exact hx) hinv
  exact ⟨c, y, hyS, by rw [hxy, epsilonContraction_reindex], hyinv⟩

/-- The same modulo a gauge-stable submodule, which needs the gauge invariance of the
  epsilon contraction for the error term to be a gauge invariant rather than merely an
  isospin one. -/
lemma mem_span_sup_invariant_iff {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2BiAntiFun B repGauge T) (x : B) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hec : ∀ g : GaugeGroupI,
      repGauge g (epsilonContraction T) = epsilonContraction T)
    (hx : x ∈ span T ⊔ S)
    (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    ∃ c : ℂ, ∃ y ∈ S, x = c • epsilonContraction T + y
      ∧ ∀ g : GaugeGroupI, repGauge g y = y := by
  obtain ⟨c, y, hyS, hxy, hyinv⟩ :=
    hT.isSU2BiFundamental_reindex.mem_span_sup_invariant_iff x S hS
      (fun g => by rw [epsilonContraction_reindex, hec g])
      (by rw [span_reindex]; exact hx) hinv
  exact ⟨c, y, hyS, by rw [hxy, epsilonContraction_reindex], hyinv⟩

end IsSU2BiAntiFun

end StandardModel
