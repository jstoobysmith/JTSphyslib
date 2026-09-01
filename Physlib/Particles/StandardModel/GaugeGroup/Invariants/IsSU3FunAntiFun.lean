/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.GaugeWeightDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.SU3PermDecomposition
/-!
# Gauge tensors carrying an `su(3)` fundamental and an anti-fundamental index

`IsSU3FunAntiFun B repGauge T` says that a family `T`, indexed by one `su(3)` fundamental
colour index and one anti-fundamental colour index, and valued in a module `B` carrying a
representation of the gauge group `GaugeGroupI`, transforms as a tensor `T^{a}{}_{b}` in
the `su(3)` factor.

This is the case that `IsSU3BiFundamental` shows is unavailable to two fundamental indices.
There the centre `ℤ₃` of `SU(3)` scales a tensor carrying `k` fundamental indices by
`ω ^ k`, and two is not a multiple of three, so every gauge invariant in the span of the
components vanishes. Lowering the second index is precisely the escape: the centre then
contributes `ω * ω⁻¹ = 1` and the Kronecker delta `δ^{a}{}_{b}` survives. That is
`3 ⊗ 3̄ = 8 ⊕ 1` against `3 ⊗ 3 = 6 ⊕ 3̄`, and it is why a colour singlet is built from a
quark and an antiquark and not from two quarks.

The invariant here also reaches deeper into the group than the `SU(2)` one does. The
epsilon contraction of `IsSU2BiFundamental` is invariant because an `SU(2)` matrix has
determinant one, so it uses the `S` of `SU(2)`; the delta contraction is invariant because
a unitary matrix satisfies `U * star U = 1`, so it uses only the `U`, and it would be an
invariant of the full unitary group.

The law itself is `IsSU3FunAntiFunMat`, which relates one element of `SU(3)` to one linear
map on `B` and mentions no other factor of the gauge group, and `IsSU3FunAntiFun` says only
that every element of the gauge group obeys that law through its `SU(3)` part. Every
statement about how the components move is proved at the level of `IsSU3FunAntiFunMat` and
instantiated afterwards, so the mathematics is `SU(3)` mathematics. What stays about
`GaugeGroupI` is the bookkeeping of the two decompositions, `GaugeWeightDecomposition` and
`SU3PermDecomposition` being supplied only for representations of the gauge group.

Section A gives the transformation law, the proposition and the span of its components,
section B the delta contraction, which is the invariant the bi-fundamental case lacks, and
section C the gauge weight decomposition of the span, whose zero-weight piece is the space
spanned by the three diagonal components, three dimensional because the zero weight occurs
twice in the adjoint and once in the singlet. Section D grades that piece by the cyclic Weyl element
of the `SU(3)` factor, which the gauge weight alone cannot split, and the two gradings
together leave the delta contraction spanning the gauge invariants.
-/

@[expose] public section

namespace StandardModel

open Matrix ComplexConjugate

/-!

## A. Mixed `su(3)` families and the span of their components

The transformation law carries one factor of the fundamental matrix for the upper index and
one factor of its complex conjugate for the lower one, with the summed index in the row slot
in both cases. The conjugate is what the lower index means: a fundamental index moves by
`U`, and the anti-fundamental representation is the complex conjugate of the fundamental, so
its index moves by `conj U`. It is recorded by `IsSU3FunAntiFunMat`, a relation between one
element of `SU(3)` and one linear map on `B`, in which no other factor of the gauge group
appears.

`IsSU3FunAntiFun` then says that every gauge transformation obeys that law through its
`SU(3)` part. Since `GaugeGroupI.toSU3` is a monoid homomorphism this is an action.
Quantifying over the whole of `GaugeGroupI` is what makes the proposition say more than a
statement about a single `SU(3)` element would: an element of the isospin or hypercharge
factor is sent to `1` in `SU(3)`, so those factors fix every component, and section C reads
that off as the vanishing of the isospin and hypercharge coordinates of every weight.

-/

/-- The linear map `f` moves the components of the family `T` as the `SU(3)` matrix `U`
  moves a tensor with one fundamental and one anti-fundamental colour index: a factor of
  `U` for the fundamental index, a factor of its complex conjugate for the anti-fundamental
  one, with the summed index in the row slot. -/
def IsSU3FunAntiFunMat {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (U : specialUnitaryGroup (Fin 3) ℂ) (f : B →ₗ[ℂ] B)
    (T : (Fin 2 → Fin 3) → B) : Prop :=
  ∀ l : Fin 2 → Fin 3,
    f (T l) = ∑ a : Fin 2 → Fin 3, (U.1 (a 0) (l 0) * conj (U.1 (a 1) (l 1))) • T a

/-- A family `T` of elements of `B`, indexed by one `su(3)` fundamental colour index and one
  anti-fundamental one, transforms as a tensor `T^{a}{}_{b}` under the representation
  `repGauge` of the gauge group: every gauge transformation moves the components by its
  `SU(3)` part alone. -/
structure IsSU3FunAntiFun (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B)
    (T : (Fin 2 → Fin 3) → B) : Prop where
  repGauge_T : ∀ g : GaugeGroupI,
    IsSU3FunAntiFunMat (GaugeGroupI.toSU3 g) (repGauge g) T

namespace IsSU3FunAntiFun
set_option linter.unusedVariables false

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {U : specialUnitaryGroup (Fin 3) ℂ} {f : B →ₗ[ℂ] B}

/-- The span of all the components of a family indexed by one `su(3)` fundamental colour
  index and one anti-fundamental one. -/
def span (T : (Fin 2 → Fin 3) → B) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

/-- An element of `B` lies in the span of the components of `T` precisely when it is a
  linear combination of them. -/
lemma mem_span_iff {T : (Fin 2 → Fin 3) → B} (x : B) :
    x ∈ span T ↔ ∃ (c : (Fin 2 → Fin 3) → ℂ), x = ∑ d, c d • T d := by
  constructor
  · intro hx
    rw [span] at hx
    refine Submodule.iSup_induction
      (motive := fun y => ∃ c : (Fin 2 → Fin 3) → ℂ, y = ∑ d, c d • T d)
      (fun d => ℂ ∙ T d) hx ?_ ?_ ?_
    · intro d y hy
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
      refine ⟨fun e => if e = d then a else 0, ?_⟩
      simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · exact ⟨0, by simp⟩
    · rintro y z ⟨c₁, rfl⟩ ⟨c₂, rfl⟩
      exact ⟨c₁ + c₂, by simp [add_smul, Finset.sum_add_distrib]⟩
  · rintro ⟨c, rfl⟩
    exact sum_mem fun d _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem d (Submodule.mem_span_singleton_self _))

/-- Every component lies in the span. -/
lemma mem_span {T : (Fin 2 → Fin 3) → B} (d : Fin 2 → Fin 3) : T d ∈ span T :=
  Submodule.mem_iSup_of_mem d (Submodule.mem_span_singleton_self _)

/-!

## B. The delta contraction

An anti-fundamental index has exactly one place to be contracted, against a fundamental
one, and the tensor that does it is the Kronecker delta. Its invariance is the statement
that `U * star U = 1`, the row of `U` at one index dotted with the conjugate row at another
giving `1` or `0` according to whether the indices agree. Only unitarity is used, not the
determinant condition, so the delta contraction is an invariant of `U(3)` and not merely of
`SU(3)`.

The contraction itself is the sum of the three diagonal components, and the whole section
is about `SU(3)`: it is built from the family alone, and its invariance is proved for an
arbitrary element of `specialUnitaryGroup (Fin 3) ℂ` acting through an arbitrary linear
map, gauge invariance being that statement read at `GaugeGroupI.toSU3 g`.

-/

/-- A sum over families of two colour indices is a double sum. -/
lemma sum_pi_two {M : Type*} [AddCommMonoid M] (F : (Fin 2 → Fin 3) → M) :
    ∑ d : Fin 2 → Fin 3, F d = ∑ x : Fin 3, ∑ y : Fin 3, F ![x, y] := by
  rw [show (∑ d : Fin 2 → Fin 3, F d) = ∑ p : Fin 3 × Fin 3, F ![p.1, p.2] from
      Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin 3) _ _ fun d => by
        congr 1
        funext i
        fin_cases i <;> simp,
    Fintype.sum_prod_type]

/-- The rows of a unitary matrix are orthonormal: a row dotted with the conjugate of another
  row is `1` when the rows agree and `0` when they do not. This is the invariance of the
  Kronecker delta, and it is the whole content of the section. -/
lemma sum_mul_conj (U : specialUnitaryGroup (Fin 3) ℂ) (b c : Fin 3) :
    ∑ x : Fin 3, U.1 b x * conj (U.1 c x) = if b = c then 1 else 0 := by
  have hU : U.1 * (U.1)ᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp U.2).1
    rwa [Matrix.star_eq_conjTranspose] at h
  have h := congrFun (congrFun hU b) c
  rw [Matrix.mul_apply] at h
  simpa [Matrix.conjTranspose_apply, Matrix.one_apply, RCLike.star_def] using h

/-- The delta contraction of a family carrying one fundamental and one anti-fundamental
  colour index: the trace of the family, the sum of its three diagonal components. -/
def deltaContraction (T : (Fin 2 → Fin 3) → B) : B := ∑ a : Fin 3, T ![a, a]

/-- The delta contraction written as a sum over all pairs of colour indices weighted by the
  Kronecker delta. -/
lemma deltaContraction_eq_sum (T : (Fin 2 → Fin 3) → B) :
    deltaContraction T
      = ∑ d : Fin 2 → Fin 3, (if d 0 = d 1 then (1 : ℂ) else 0) • T d := by
  rw [sum_pi_two]
  simp [deltaContraction]

/-- The delta contraction lies in the span of the components. -/
lemma deltaContraction_mem_span (T : (Fin 2 → Fin 3) → B) :
    deltaContraction T ∈ span T :=
  sum_mem fun a _ => mem_span _

/-- The delta contraction is fixed by any linear map moving the components by an element of
  `SU(3)`, the Kronecker delta being invariant under a unitary matrix. This is the theorem
  that `IsSU3BiFundamental` has no analogue of. -/
lemma map_deltaContraction {T : (Fin 2 → Fin 3) → B} (hf : IsSU3FunAntiFunMat U f T) :
    f (deltaContraction T) = deltaContraction T := by
  have step : f (deltaContraction T)
      = ∑ b : Fin 2 → Fin 3, (if b 0 = b 1 then (1 : ℂ) else 0) • T b := by
    rw [deltaContraction, map_sum]
    have h1 : ∀ c : Fin 3, f (T ![c, c])
        = ∑ b : Fin 2 → Fin 3, (U.1 (b 0) c * conj (U.1 (b 1) c)) • T b := by
      intro c
      rw [hf ![c, c]]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    exact sum_mul_conj U (b 0) (b 1)
  rw [step, ← deltaContraction_eq_sum]

/-- The delta contraction of a mixed family is gauge invariant: a gauge transformation moves
  the components by its `SU(3)` part, which fixes the contraction. -/
lemma repGauge_deltaContraction {T : (Fin 2 → Fin 3) → B}
    (hT : IsSU3FunAntiFun B repGauge T) (g : GaugeGroupI) :
    repGauge g (deltaContraction T) = deltaContraction T :=
  map_deltaContraction (hT.repGauge_T g)

/-!

## C. The gauge weight decomposition of the span

The gauge torus is diagonal in the fundamental representation of the `SU(3)` factor, so the
three basis colour directions are already weight vectors, carrying the three colour weights
`colourWeight` of the triplet, and the anti-fundamental index carries the negatives of those
weights. A component `T d` therefore carries the definite weight `wtWeight d`, the weight of
its upper index minus the weight of its lower one, and the span of the components is already
the join of nine weight lines.

The `SU(3)` content of the section is `map_of_diagonal`: a family moved by a diagonal `SU(3)`
matrix has every component an eigenvector, at the diagonal entry of its upper index times the
conjugate of the diagonal entry of its lower one. The torus generators enter only through
`toSU3_gaugeTorusGen_apply`, which says that their `SU(3)` parts are diagonal with the
characters of `fundWeight` on the diagonal. The decomposition itself is where the gauge group
is unavoidable: `GaugeWeightDecomposition` is defined for a representation of `GaugeGroupI`,
and it is what records that the isospin and hypercharge coordinates of every weight vanish.

The stronger typeclass assumptions are forced: `GaugeWeightDecomposition` lives in an algebra
and records multiplicativity of the representation, neither of which `IsSU3FunAntiFun` needs,
so both appear as extra arguments here.

-/

/-!

## C.1. Diagonal matrices and the gauge torus

-/

/-- A family moved by a diagonal `SU(3)` matrix has every component an eigenvector, at the
  diagonal entry of its upper index times the conjugate of the diagonal entry of its lower
  one. -/
lemma map_of_diagonal {T : (Fin 2 → Fin 3) → B} (hf : IsSU3FunAntiFunMat U f T)
    (hU : ∀ a b : Fin 3, a ≠ b → U.1 a b = 0) (l : Fin 2 → Fin 3) :
    f (T l) = (U.1 (l 0) (l 0) * conj (U.1 (l 1) (l 1))) • T l := by
  rw [hf l, Finset.sum_eq_single l]
  · intro a _ hal
    have h : a 0 ≠ l 0 ∨ a 1 ≠ l 1 := by
      by_contra hc
      simp only [not_or, ne_eq, not_not] at hc
      exact hal (funext fun j => by fin_cases j <;> simp [hc.1, hc.2])
    rcases h with h | h
    · rw [hU _ _ h, zero_mul, zero_smul]
    · rw [hU _ _ h, map_zero, mul_zero, zero_smul]
  · intro hl
    exact absurd (Finset.mem_univ l) hl

/-- The gauge weight carried by one `su(3)` fundamental colour index: colour only, the three
  colours carrying the three colour weights of the triplet. -/
def fundWeight (c : Fin 3) : GaugeWeight := ((colourWeight c).1, (colourWeight c).2, 0, 0)

/-- The gauge weight carried by one `su(3)` anti-fundamental colour index: the negative of
  the weight of the fundamental index of the same colour, the weights of the antitriplet
  being the negatives of those of the triplet. -/
def antiFundWeight (c : Fin 3) : GaugeWeight := -fundWeight c

/-- The exponents of an anti-fundamental colour index are the negated exponents of the
  fundamental one. -/
lemma antiFundWeight_coord (c : Fin 3) (i : Fin 4) :
    GaugeWeight.coord (antiFundWeight c) i = -GaugeWeight.coord (fundWeight c) i := by
  rw [antiFundWeight, GaugeWeight.coord_neg]

/-- The gauge torus acts diagonally on a fundamental colour index, by the character of the
  weight of that index. Only the two colour generators act nontrivially. -/
lemma toSU3_gaugeTorusGen_apply (i : Fin 4) (a b : Fin 3) :
    (GaugeGroupI.toSU3 (gaugeTorusGen i)).1 a b
      = if a = b then (expI : ℂ) ^ GaugeWeight.coord (fundWeight a) i else 0 := by
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [gaugeTorusGen, GaugeGroupI.toSU3, su3ExpIOne, su3ExpITwo, fundWeight,
      colourWeight, expI_inv_eq_star]

/-- The `SU(3)` part of a torus generator has vanishing off-diagonal entries. -/
lemma toSU3_gaugeTorusGen_offDiag (i : Fin 4) (a b : Fin 3) (hab : a ≠ b) :
    (GaugeGroupI.toSU3 (gaugeTorusGen i)).1 a b = 0 := by
  rw [toSU3_gaugeTorusGen_apply, if_neg hab]

/-- The gauge weight carried by a component of a mixed family: the weight of its upper index
  plus the weight of its lower one, which is the difference of two colour weights. -/
def wtWeight (l : Fin 2 → Fin 3) : GaugeWeight := fundWeight (l 0) + antiFundWeight (l 1)

/-!

## C.2. The components are weight vectors

-/

/-- Every component of a mixed family is a simultaneous eigenvector of the gauge torus, at
  the character of the weight of its upper index minus that of its lower one. -/
lemma repGauge_gaugeTorusGen {T : (Fin 2 → Fin 3) → B}
    (hT : IsSU3FunAntiFun B repGauge T) (l : Fin 2 → Fin 3) (i : Fin 4) :
    repGauge (gaugeTorusGen i) (T l)
      = ((expI : ℂ) ^ GaugeWeight.coord (wtWeight l) i) • T l := by
  rw [map_of_diagonal (hT.repGauge_T (gaugeTorusGen i))
    (toSU3_gaugeTorusGen_offDiag i) l]
  congr 1
  rw [toSU3_gaugeTorusGen_apply, toSU3_gaugeTorusGen_apply, if_pos rfl, if_pos rfl,
    starRingEnd_expI_zpow, wtWeight, GaugeWeight.coord_add, antiFundWeight_coord,
    zpow_add₀ expI_ne_zero]

/-!

## C.3. The decomposition

-/

section Decomposition

variable {B : Type*} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {T : (Fin 2 → Fin 3) → B}

/-- The gauge weight decomposition of the span of a mixed `su(3)` family. The span is the
  join of the lines through the nine components, and each of those carries the weight of its
  upper index minus that of its lower one. -/
@[implicit_reducible]
noncomputable def gaugeWeightDecomposition (hT : IsSU3FunAntiFun B repGauge T)
    (hmul : IsMulRep repGauge) : GaugeWeightDecomposition repGauge (span T) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup hmul fun d : Fin 2 → Fin 3 =>
      GaugeWeightDecomposition.spanSingleton hmul (T d) (wtWeight d)
        (repGauge_gaugeTorusGen hT d))
    _ rfl

variable (hT : IsSU3FunAntiFun B repGauge T)

/-- The pieces of the decomposition: the weight-`w` piece is the join of the lines through
  those components whose weight is `w`. -/
lemma gaugeWeightDecomposition_piece (hmul : IsMulRep repGauge) (w : GaugeWeight) :
    (hT.gaugeWeightDecomposition hmul).piece w
      = ⨆ d : Fin 2 → Fin 3, (if w = wtWeight d then ℂ ∙ T d else ⊥) := rfl

/-- The support of the decomposition, before evaluation. -/
lemma gaugeWeightDecomposition_supp_eq (hmul : IsMulRep repGauge) :
    (hT.gaugeWeightDecomposition hmul).supp
      = Finset.univ.biUnion fun d : Fin 2 → Fin 3 =>
        ({wtWeight d} : Finset GaugeWeight) := rfl

/-- The gauge weights carried by a mixed `su(3)` family: the zero weight and the six roots
  of `su(3)`, which are the weights of `3 ⊗ 3̄ = 8 ⊕ 1`. Every one of them has vanishing
  isospin and hypercharge, since the family carries colour only. -/
lemma gaugeWeightDecomposition_supp (hmul : IsMulRep repGauge) :
    (hT.gaugeWeightDecomposition hmul).supp
      = {((0, 0, 0, 0) : GaugeWeight), (2, -1, 0, 0), (1, 1, 0, 0),
        (-2, 1, 0, 0), (-1, 2, 0, 0), (-1, -1, 0, 0), (1, -2, 0, 0)} := by
  rw [hT.gaugeWeightDecomposition_supp_eq hmul]
  decide

/-!

## C.4. The zero-weight piece

A gauge invariant built from `T` is fixed by the torus, so it lies in the zero-weight piece,
which makes that piece worth describing explicitly. The weight of a component is the
difference of the colour weights of its two indices, so it vanishes exactly when the two
indices agree: the three colour weights are distinct. That leaves the three diagonal
components, and the zero-weight piece is the three dimensional space they span, the
multiplicity of the zero weight in `3 ⊗ 3̄` being the rank two of `su(3)` plus one for the
singlet.

-/

/-- A component of a mixed family carries vanishing gauge weight precisely when its two
  colour indices agree, the two colour weights then cancelling. -/
lemma wtWeight_eq_zero_iff (l : Fin 2 → Fin 3) : wtWeight l = 0 ↔ l 0 = l 1 := by
  revert l
  decide

/-- The zero-weight piece of the gauge weight decomposition, explicitly: the space spanned
  by the three diagonal components. -/
lemma gaugeWeightDecomposition_piece_zero (hmul : IsMulRep repGauge) :
    (hT.gaugeWeightDecomposition hmul).piece 0 = ⨆ a : Fin 3, ℂ ∙ T ![a, a] := by
  rw [hT.gaugeWeightDecomposition_piece hmul]
  refine le_antisymm (iSup_le fun d => ?_) (iSup_le fun a => ?_)
  · split_ifs with hd
    · have hdd : d = ![d 0, d 0] :=
        funext fun j => by fin_cases j <;> simp [(wtWeight_eq_zero_iff d).1 hd.symm]
      rw [congrArg T hdd]
      exact le_iSup_of_le (d 0) le_rfl
    · exact bot_le
  · refine le_iSup_of_le ![a, a] (le_of_eq (if_pos ?_).symm)
    exact ((wtWeight_eq_zero_iff ![a, a]).2 (by simp)).symm

/-- The delta contraction lies in the zero-weight piece. It is gauge invariant, so in
  particular the torus fixes it. -/
lemma deltaContraction_mem_piece_zero (hmul : IsMulRep repGauge) :
    deltaContraction T ∈ (hT.gaugeWeightDecomposition hmul).piece 0 :=
  GaugeWeightDecomposition.mem_zero_of_invariant _ (deltaContraction_mem_span T)
    (repGauge_deltaContraction hT)

end Decomposition

/-!

## D. The `SU(3)` permutation decomposition of the zero-weight piece

The gauge weight cannot separate the three diagonal components: they all carry weight zero,
and section C.4 leaves the zero-weight piece as the space they span. The cyclic Weyl element
of the `SU(3)` factor does separate them. Its matrix `!![0, 0, 1; 1, 0, 0; 0, 1, 0]` cycles
the three colours, so it cycles the three diagonal components, and its eigenvectors on that
space are their three discrete Fourier combinations: the plain sum, which is the delta
contraction, at eigenvalue `1`, and the two twisted sums, at eigenvalues `ω` and `ω ^ 2`,
which are the two Cartan directions of the octet. The conjugate on the lower index costs
nothing in this section, a permutation matrix being real. That much is again `SU(3)`: the
Weyl element enters as the element `su3Perm` of `specialUnitaryGroup (Fin 3) ℂ`, and the
gauge group only through `toSU3_gaugeSU3Perm`.

Grade zero is in general only a sieve, since `SU3PermDecomposition.mem_zero_of_invariant`
has no converse, but here the two gradings together are sharp: the zero-weight piece is
three dimensional and grade zero is a line in it, so every gauge invariant in the span of
the components is a multiple of the delta contraction. That is the singlet of
`3 ⊗ 3̄ = 8 ⊕ 1`, counted exactly once, and it is the conclusion the bi-fundamental case
cannot reach, its zero-weight piece being `⊥`.

-/

/-!

## D.1. The cyclic Weyl element on the diagonal components

-/

/-- The entries of the cyclic Weyl element of `SU(3)`. -/
lemma su3Perm_apply (a b : Fin 3) :
    (su3Perm : specialUnitaryGroup (Fin 3) ℂ).1 a b = !![0, 0, 1; 1, 0, 0; 0, 1, 0] a b := rfl

/-- The `SU(3)` part of the cyclic Weyl element of the gauge group is the cyclic Weyl
  element of `SU(3)`. -/
lemma toSU3_gaugeSU3Perm : GaugeGroupI.toSU3 gaugeSU3Perm = su3Perm := rfl

/-- The cyclic element sends the first diagonal component to the second. -/
lemma map_su3Perm_zero {T : (Fin 2 → Fin 3) → B} (hf : IsSU3FunAntiFunMat su3Perm f T) :
    f (T ![0, 0]) = T ![1, 1] := by
  rw [hf ![0, 0], sum_pi_two]
  simp [Fin.sum_univ_three, su3Perm_apply]

/-- The cyclic element sends the second diagonal component to the third. -/
lemma map_su3Perm_one {T : (Fin 2 → Fin 3) → B} (hf : IsSU3FunAntiFunMat su3Perm f T) :
    f (T ![1, 1]) = T ![2, 2] := by
  rw [hf ![1, 1], sum_pi_two]
  simp [Fin.sum_univ_three, su3Perm_apply]

/-- The cyclic element sends the third diagonal component to the first. -/
lemma map_su3Perm_two {T : (Fin 2 → Fin 3) → B} (hf : IsSU3FunAntiFunMat su3Perm f T) :
    f (T ![2, 2]) = T ![0, 0] := by
  rw [hf ![2, 2], sum_pi_two]
  simp [Fin.sum_univ_three, su3Perm_apply]

omit [Module ℂ B] in
/-- The delta contraction as the sum of the three diagonal components. -/
lemma deltaContraction_eq_add (T : (Fin 2 → Fin 3) → B) :
    deltaContraction T = T ![0, 0] + T ![1, 1] + T ![2, 2] := by
  rw [deltaContraction, Fin.sum_univ_three]

/-- The grade one combination of the three diagonal components. -/
noncomputable def octetOne (T : (Fin 2 → Fin 3) → B) : B :=
  T ![0, 0] + su3Omega ^ 2 • T ![1, 1] + su3Omega • T ![2, 2]

/-- The grade two combination of the three diagonal components. -/
noncomputable def octetTwo (T : (Fin 2 → Fin 3) → B) : B :=
  T ![0, 0] + su3Omega • T ![1, 1] + su3Omega ^ 2 • T ![2, 2]

/-- The cyclic element multiplies the grade one combination by `ω`. -/
lemma map_su3Perm_octetOne {T : (Fin 2 → Fin 3) → B}
    (hf : IsSU3FunAntiFunMat su3Perm f T) :
    f (octetOne T) = su3Omega • octetOne T := by
  rw [octetOne, map_add, map_add, map_smul, map_smul, map_su3Perm_zero hf,
    map_su3Perm_one hf, map_su3Perm_two hf]
  match_scalars <;>
    first
      | ring1
      | linear_combination (-1 : ℂ) * su3Omega_pow_three

/-- The cyclic element multiplies the grade two combination by `ω ^ 2`. -/
lemma map_su3Perm_octetTwo {T : (Fin 2 → Fin 3) → B}
    (hf : IsSU3FunAntiFunMat su3Perm f T) :
    f (octetTwo T) = su3Omega ^ 2 • octetTwo T := by
  rw [octetTwo, map_add, map_add, map_smul, map_smul, map_su3Perm_zero hf,
    map_su3Perm_one hf, map_su3Perm_two hf]
  match_scalars <;>
    first
      | ring1
      | linear_combination (-1 : ℂ) * su3Omega_pow_three
      | linear_combination (-su3Omega) * su3Omega_pow_three

/-!

## D.2. The Fourier combinations span the diagonal components

-/

/-- The three cube roots of unity sum to zero, so the three colours enter the delta
  contraction and the two octet combinations with the characters of `ZMod 3`. -/
lemma su3Omega_geom_sum : 1 + su3Omega + su3Omega ^ 2 = 0 := by
  have h := su3PermSign_symmetrizer (k := 1) (by decide)
  rwa [su3PermSign_one] at h

/-- The three graded combinations recover three times the first diagonal component. -/
lemma sum_octet_zero (T : (Fin 2 → Fin 3) → B) :
    deltaContraction T + octetOne T + octetTwo T = (3 : ℂ) • T ![0, 0] := by
  rw [deltaContraction_eq_add, octetOne, octetTwo]
  match_scalars
  · ring1
  · linear_combination su3Omega_geom_sum
  · linear_combination su3Omega_geom_sum

/-- The three graded combinations, twisted once, recover three times the second diagonal
  component. -/
lemma sum_octet_one (T : (Fin 2 → Fin 3) → B) :
    deltaContraction T + su3Omega • octetOne T + su3Omega ^ 2 • octetTwo T
      = (3 : ℂ) • T ![1, 1] := by
  rw [deltaContraction_eq_add, octetOne, octetTwo]
  match_scalars
  · linear_combination su3Omega_geom_sum
  · linear_combination (2 : ℂ) * su3Omega_pow_three
  · linear_combination su3Omega_geom_sum + su3Omega * su3Omega_pow_three

/-- The three graded combinations, twisted twice, recover three times the third diagonal
  component. -/
lemma sum_octet_two (T : (Fin 2 → Fin 3) → B) :
    deltaContraction T + su3Omega ^ 2 • octetOne T + su3Omega • octetTwo T
      = (3 : ℂ) • T ![2, 2] := by
  rw [deltaContraction_eq_add, octetOne, octetTwo]
  match_scalars
  · linear_combination su3Omega_geom_sum
  · linear_combination su3Omega_geom_sum + su3Omega * su3Omega_pow_three
  · linear_combination (2 : ℂ) * su3Omega_pow_three

/-- The delta contraction and the two octet combinations span the space of the three
  diagonal components, being their three discrete Fourier combinations. -/
lemma sup_span_octet (T : (Fin 2 → Fin 3) → B) :
    ℂ ∙ deltaContraction T ⊔ ℂ ∙ octetOne T ⊔ ℂ ∙ octetTwo T
      = ⨆ a : Fin 3, ℂ ∙ T ![a, a] := by
  set W := ℂ ∙ deltaContraction T ⊔ ℂ ∙ octetOne T ⊔ ℂ ∙ octetTwo T
  have hdiag : ∀ a : Fin 3, T ![a, a] ∈ ⨆ b : Fin 3, ℂ ∙ T ![b, b] := fun a =>
    Submodule.mem_iSup_of_mem a (Submodule.mem_span_singleton_self _)
  have hd : deltaContraction T ∈ W :=
    Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))
  have h1 : octetOne T ∈ W :=
    Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  have h2 : octetTwo T ∈ W :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hthird : ∀ x : B, (3 : ℂ) • x ∈ W → x ∈ W := by
    intro x hx
    have h := Submodule.smul_mem W (3⁻¹ : ℂ) hx
    rwa [smul_smul, inv_mul_cancel₀ (by norm_num : (3 : ℂ) ≠ 0), one_smul] at h
  have hzero : T ![0, 0] ∈ W :=
    hthird _ (by rw [← sum_octet_zero]; exact add_mem (add_mem hd h1) h2)
  have hone : T ![1, 1] ∈ W :=
    hthird _ (by
      rw [← sum_octet_one]
      exact add_mem (add_mem hd (Submodule.smul_mem _ _ h1)) (Submodule.smul_mem _ _ h2))
  have htwo : T ![2, 2] ∈ W :=
    hthird _ (by
      rw [← sum_octet_two]
      exact add_mem (add_mem hd (Submodule.smul_mem _ _ h1)) (Submodule.smul_mem _ _ h2))
  refine le_antisymm (sup_le (sup_le ?_ ?_) ?_) (iSup_le fun a => ?_) <;>
    rw [Submodule.span_singleton_le_iff_mem]
  · rw [deltaContraction_eq_add]
    exact add_mem (add_mem (hdiag 0) (hdiag 1)) (hdiag 2)
  · rw [octetOne]
    exact add_mem (add_mem (hdiag 0) (Submodule.smul_mem _ _ (hdiag 1)))
      (Submodule.smul_mem _ _ (hdiag 2))
  · rw [octetTwo]
    exact add_mem (add_mem (hdiag 0) (Submodule.smul_mem _ _ (hdiag 1)))
      (Submodule.smul_mem _ _ (hdiag 2))
  · fin_cases a
    · exact hzero
    · exact hone
    · exact htwo

/-!

## D.3. The grading

-/

section Grading

variable {B : Type*} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}

/-- The grade `k` piece of the `SU(3)` permutation decomposition of the zero-weight piece:
  the delta contraction in grade zero, and the two octet combinations in grades one and
  two. -/
noncomputable def zeroPiece (T : (Fin 2 → Fin 3) → B) (k : ZMod 3) : Submodule ℂ B :=
  if k = 0 then ℂ ∙ deltaContraction T
  else if k = 1 then ℂ ∙ octetOne T else ℂ ∙ octetTwo T

variable {T : (Fin 2 → Fin 3) → B}

/-- The grade zero piece: the line through the delta contraction. -/
@[simp] lemma zeroPiece_zero : zeroPiece T 0 = ℂ ∙ deltaContraction T := by
  rw [zeroPiece, if_pos rfl]

/-- The grade one piece: the line through the first octet combination. -/
@[simp] lemma zeroPiece_one : zeroPiece T 1 = ℂ ∙ octetOne T := by
  rw [zeroPiece, if_neg (by decide), if_pos rfl]

/-- The grade two piece: the line through the second octet combination. -/
@[simp] lemma zeroPiece_two : zeroPiece T 2 = ℂ ∙ octetTwo T := by
  rw [zeroPiece, if_neg (by decide), if_neg (by decide)]

/-- Each graded piece is of pure sign under the cyclic Weyl element. -/
lemma zeroPiece_le_eigenspace (hT : IsSU3FunAntiFun B repGauge T) (k : ZMod 3) :
    zeroPiece T k ≤ Module.End.eigenspace (repGauge gaugeSU3Perm) (su3PermSign k) := by
  have hcases : ∀ j : ZMod 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
  rcases hcases k with rfl | rfl | rfl
  · rw [zeroPiece_zero, Submodule.span_singleton_le_iff_mem]
    exact Module.End.mem_eigenspace_iff.mpr
      (by rw [su3PermSign_zero, one_smul, repGauge_deltaContraction hT])
  · rw [zeroPiece_one, Submodule.span_singleton_le_iff_mem]
    exact Module.End.mem_eigenspace_iff.mpr
      (by rw [su3PermSign_one, map_su3Perm_octetOne (hT.repGauge_T gaugeSU3Perm)])
  · rw [zeroPiece_two, Submodule.span_singleton_le_iff_mem]
    exact Module.End.mem_eigenspace_iff.mpr
      (by rw [su3PermSign_two, map_su3Perm_octetTwo (hT.repGauge_T gaugeSU3Perm)])

variable (hT : IsSU3FunAntiFun B repGauge T)

/-- The graded pieces exhaust the zero-weight piece. -/
lemma iSup_zeroPiece (hmul : IsMulRep repGauge) :
    (⨆ k : ZMod 3, zeroPiece T k) = (hT.gaugeWeightDecomposition hmul).piece 0 := by
  rw [hT.gaugeWeightDecomposition_piece_zero hmul, ← sup_span_octet T]
  have hcases : ∀ j : ZMod 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
  refine le_antisymm (iSup_le fun k => ?_) (sup_le (sup_le ?_ ?_) ?_)
  · rcases hcases k with rfl | rfl | rfl
    · rw [zeroPiece_zero]
      exact le_sup_of_le_left le_sup_left
    · rw [zeroPiece_one]
      exact le_sup_of_le_left le_sup_right
    · rw [zeroPiece_two]
      exact le_sup_right
  · exact le_iSup_of_le 0 (le_of_eq zeroPiece_zero.symm)
  · exact le_iSup_of_le 1 (le_of_eq zeroPiece_one.symm)
  · exact le_iSup_of_le 2 (le_of_eq zeroPiece_two.symm)

/-- The `SU(3)` permutation decomposition of the zero-weight piece of the gauge weight
  decomposition: the cyclic Weyl element grades the space the gauge weight cannot split,
  putting the delta contraction in grade zero and the two octet combinations in grades one
  and two. -/
noncomputable def zeroPieceSU3Perm (hT : IsSU3FunAntiFun B repGauge T)
    (hmul : IsMulRep repGauge) :
    SU3PermDecomposition repGauge ((hT.gaugeWeightDecomposition hmul).piece 0) where
  piece := zeroPiece T
  piece_le k x hx := Module.End.mem_eigenspace_iff.mp (zeroPiece_le_eigenspace hT k hx)
  iSup_piece := hT.iSup_zeroPiece hmul

/-- The pieces of the decomposition are the graded pieces. -/
@[simp] lemma zeroPieceSU3Perm_piece (hmul : IsMulRep repGauge) (k : ZMod 3) :
    (hT.zeroPieceSU3Perm hmul).piece k = zeroPiece T k := rfl

/-- The delta contraction lies in the grade zero piece: it is gauge invariant, so in
  particular the cyclic Weyl element fixes it. -/
lemma deltaContraction_mem_zeroPiece_zero (hT : IsSU3FunAntiFun B repGauge T)
    (hmul : IsMulRep repGauge) :
    deltaContraction T ∈ zeroPiece T 0 :=
  SU3PermDecomposition.mem_zero_of_invariant (hT.zeroPieceSU3Perm hmul)
    (hT.deltaContraction_mem_piece_zero hmul) (repGauge_deltaContraction hT)

/-- Every gauge invariant in the span of the components is a multiple of the delta
  contraction. The gauge weight cuts the span down to the space of the three diagonal
  components, and the cyclic Weyl element cuts that space down to the line through their
  sum. This is the statement that `3 ⊗ 3̄` contains exactly one singlet, and it is what
  `IsSU3BiFundamental.eq_zero_of_invariant` denies to two fundamental indices. -/
lemma exists_smul_deltaContraction_of_invariant (hT : IsSU3FunAntiFun B repGauge T)
    (hmul : IsMulRep repGauge) {x : B}
    (hx : x ∈ span T) (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    ∃ c : ℂ, x = c • deltaContraction T := by
  have hmem : x ∈ zeroPiece T 0 :=
    SU3PermDecomposition.mem_zero_of_invariant (hT.zeroPieceSU3Perm hmul)
      (GaugeWeightDecomposition.mem_zero_of_invariant _ hx hinv) hinv
  rw [zeroPiece_zero] at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  exact ⟨c, hc.symm⟩

end Grading

end IsSU3FunAntiFun

end StandardModel
