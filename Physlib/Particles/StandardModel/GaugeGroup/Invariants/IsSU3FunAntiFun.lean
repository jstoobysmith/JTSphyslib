/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.GaugeWeightDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.SU3PermDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.IsSU3BiAdjoint
public import Mathlib.Algebra.TrivSqZeroExt.Basic
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
map on `B` and mentions no other factor of the gauge group. `IsSU3FunAntiFun` says that the
colour transformation `(U, 1, 1)` obeys that law with the matrix of `U`, for every `U` in
`SU(3)`, and it says nothing whatever about the isospin and hypercharge factors: those may
move the components as they please. So the mathematics here is `SU(3)` mathematics twice
over, in the law and in the hypothesis, and the conclusions are about invariance under the
colour factor. That weakness is what a Yukawa bilinear needs: a colour triplet paired with
an anti-triplet carries hypercharge, so a hypercharge transformation does move its
components, and a law quantified over the whole gauge group would be false of it.

What stays about `GaugeGroupI` is the bookkeeping of the two decompositions,
`GaugeWeightDecomposition` and `SU3PermDecomposition` being supplied only for
representations of the gauge group. They are built for `repSU3 repGauge` of section A.2,
the colour part of the representation, which is defined where the bi-adjoint case needs it,
in `IsSU3BiAdjoint`, and imported here. A decomposition must know how all four torus
generators act, and of the four only `gaugeTorusGen 0` and `gaugeTorusGen 1` are colour
transformations; the colour part sends the other two to the identity, so the isospin and
hypercharge coordinates of every weight vanish by construction rather than by hypothesis.

Section A gives the transformation law, the proposition, the colour part of a
representation and the span of the components, section B the delta contraction, which is
the invariant the bi-fundamental case lacks, and section C the gauge weight decomposition
of the span, whose zero-weight piece is the space spanned by the three diagonal components,
three dimensional because the zero weight occurs twice in the adjoint and once in the
singlet. Section D grades that piece by the cyclic Weyl element of the `SU(3)` factor,
which the gauge weight alone cannot split, and the two gradings together leave the delta
contraction spanning the colour invariants.

Sections E and F put that classification into the form the Yukawa sector needs, where
several colour bilinears are summed and one of them is peeled off at a time. Section E
sheds the algebra structure on the target and the multiplicativity hypothesis on the
representation, by running the classification in the trivial square-zero extension of a
module and pulling it back, and section F divides out a stable submodule, which is where
the families not yet reached are parked; the quotient is a module and no longer an algebra,
which is why section E comes first. Each conclusion is stated twice, once for the colour
factor and once for the whole gauge group, the colour form being what the transformation
law supports on its own and the gauge form asking in addition that the delta contraction be
gauge invariant.
-/

@[expose] public section

namespace StandardModel

open Matrix ComplexConjugate

/-!

## A. Mixed `su(3)` families and the span of their components

A fundamental colour index and an anti-fundamental one are acted on by the `SU(3)` factor
of the gauge group alone. A.1 phrases the transformation law through the fundamental matrix
of an `SU(3)` element and nothing else, so that no other factor of the gauge group appears
in the law, and A.2 reads a representation of the gauge group at its colour factor, which
is what carries the two decompositions of sections C and D.

## A.1. The transformation law and the proposition

The transformation law carries one factor of the fundamental matrix for the upper index and
one factor of its complex conjugate for the lower one, with the summed index in the row slot
in both cases. The conjugate is what the lower index means: a fundamental index moves by
`U`, and the anti-fundamental representation is the complex conjugate of the fundamental, so
its index moves by `conj U`. It is recorded by `IsSU3FunAntiFunMat`, a relation between one
element of `SU(3)` and one linear map on `B`, in which no other factor of the gauge group
appears.

`IsSU3FunAntiFun` then says that the colour transformation `(U, 1, 1)` obeys that law with
the matrix of `U`, for every `U` in `SU(3)`. Since `U ↦ (U, 1, 1)` is a monoid homomorphism
this is an action of `SU(3)`, and it is all that is assumed: a gauge transformation with a
nontrivial isospin or hypercharge factor is not mentioned, and may move the components
arbitrarily. That is what a Yukawa bilinear needs, its components carrying hypercharge.
Nothing here forces the isospin and hypercharge coordinates of a weight to vanish; section
C gets that instead from `repSU3`, which sends the isospin and hypercharge generators to
the identity outright.

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
  `repGauge` of the gauge group: a colour transformation moves the components by the
  `SU(3)` element it is built from. Nothing is asked of the isospin or hypercharge
  factors. -/
structure IsSU3FunAntiFun (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B)
    (T : (Fin 2 → Fin 3) → B) : Prop where
  repGauge_T : ∀ g : specialUnitaryGroup (Fin 3) ℂ,
    IsSU3FunAntiFunMat g (repGauge (g, 1, 1)) T

/-!

## A.2. The colour part of a representation, and the span

Reading a representation of the gauge group at the colour factor of its argument alone
gives `repSU3`, again a representation of the whole gauge group; it is defined in
`IsSU3BiAdjoint`, together with `repSU3_apply`, `isMulRep_repSU3`, the bridge
`repSU3_invariant_iff_su3` between invariance under it and invariance under the colour
factor, and the stability bridge `repSU3_stable_iff_su3`. A mixed family for `repGauge` is
a mixed family for `repSU3 repGauge`, with the same span and the same delta contraction,
which is `toRepSU3`.

That transport is what carries sections C and D, whose two decompositions need a
representation of the whole gauge group knowing all four torus generators, something the
transformation law cannot supply. The statements themselves are written with the colour
transformation `(U, 1, 1)` spelled out, so that reading one needs no unfolding.

-/

namespace IsSU3FunAntiFun
set_option linter.unusedVariables false

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {U : specialUnitaryGroup (Fin 3) ℂ} {f : B →ₗ[ℂ] B}

/-- A mixed family for a representation is a mixed family for its colour part: the
  transformation law reads only the colour factor to begin with. The span and the delta
  contraction do not mention the representation, so every statement of this file transports
  along this and is read at the colour factor alone. -/
lemma toRepSU3 {T : (Fin 2 → Fin 3) → B} (hT : IsSU3FunAntiFun B repGauge T) :
    IsSU3FunAntiFun B (repSU3 repGauge) T where
  repGauge_T g := hT.repGauge_T g

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
map, colour invariance being that statement read at the colour transformation `(U, 1, 1)`.

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

/-- The delta contraction of a mixed family is fixed by the colour factor: a colour
  transformation moves the components by the `SU(3)` element it is built from, which fixes
  the contraction. That is all the transformation law constrains, the isospin and
  hypercharge factors being free to move the contraction. -/
lemma repGauge_deltaContraction {T : (Fin 2 → Fin 3) → B}
    (hT : IsSU3FunAntiFun B repGauge T) (U : specialUnitaryGroup (Fin 3) ℂ) :
    repGauge (U, 1, 1) (deltaContraction T) = deltaContraction T :=
  map_deltaContraction (hT.repGauge_T U)

/-- The cyclic Weyl element of the gauge group moves the components by the cyclic Weyl
  element of `SU(3)`, being the colour transformation built from it. -/
lemma isSU3FunAntiFunMat_gaugeSU3Perm {T : (Fin 2 → Fin 3) → B}
    (hT : IsSU3FunAntiFun B repGauge T) :
    IsSU3FunAntiFunMat su3Perm (repGauge gaugeSU3Perm) T :=
  hT.repGauge_T su3Perm

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
characters of `fundWeight` on the diagonal.

The decomposition is for `repSU3 repGauge` and not for `repGauge` itself, because a
decomposition must know how all four torus generators act, and the transformation law
constrains only the colour factor: of the four generators only `gaugeTorusGen 0` and
`gaugeTorusGen 1` are colour transformations. The colour part sends the other two to the
identity, so their weights vanish by construction rather than by hypothesis, which is why
`gaugeWeightDecomposition_supp` still lists only weights of the form `(m, n, 0, 0)`.

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

/-- Any linear map moving the components of a mixed family by the colour part of a torus
  generator scales every one of them by the character of the weight of its upper index minus
  that of its lower one. -/
lemma map_gaugeTorusGen {T : (Fin 2 → Fin 3) → B} {i : Fin 4}
    (hf : IsSU3FunAntiFunMat (GaugeGroupI.toSU3 (gaugeTorusGen i)) f T)
    (l : Fin 2 → Fin 3) :
    f (T l) = ((expI : ℂ) ^ GaugeWeight.coord (wtWeight l) i) • T l := by
  rw [map_of_diagonal hf (toSU3_gaugeTorusGen_offDiag i) l]
  congr 1
  rw [toSU3_gaugeTorusGen_apply, toSU3_gaugeTorusGen_apply, if_pos rfl, if_pos rfl,
    starRingEnd_expI_zpow, wtWeight, GaugeWeight.coord_add, antiFundWeight_coord,
    zpow_add₀ expI_ne_zero]

/-- Every component of a mixed family is a simultaneous eigenvector of the gauge torus for
  the colour part of the representation, at the character of the weight of its upper index
  minus that of its lower one. -/
lemma repSU3_gaugeTorusGen {T : (Fin 2 → Fin 3) → B}
    (hT : IsSU3FunAntiFun B repGauge T) (l : Fin 2 → Fin 3) (i : Fin 4) :
    repSU3 repGauge (gaugeTorusGen i) (T l)
      = ((expI : ℂ) ^ GaugeWeight.coord (wtWeight l) i) • T l :=
  map_gaugeTorusGen (hT.repGauge_T (GaugeGroupI.toSU3 (gaugeTorusGen i))) l

/-- The colour part of a torus generator scales every component of a mixed family by the
  character of the weight of its upper index minus that of its lower one. This is
  `repSU3_gaugeTorusGen` with the colour transformation spelled out. -/
lemma repGauge_gaugeTorusGen {T : (Fin 2 → Fin 3) → B}
    (hT : IsSU3FunAntiFun B repGauge T) (l : Fin 2 → Fin 3) (i : Fin 4) :
    repGauge (GaugeGroupI.toSU3 (gaugeTorusGen i), 1, 1) (T l)
      = ((expI : ℂ) ^ GaugeWeight.coord (wtWeight l) i) • T l :=
  hT.repSU3_gaugeTorusGen l i

/-!

## C.3. The decomposition

-/

section Decomposition

variable {B : Type*} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {T : (Fin 2 → Fin 3) → B}

/-- The gauge weight decomposition of the span of a mixed `su(3)` family, for the colour
  part of the representation. The span is the join of the lines through the nine components,
  and each of those carries the weight of its upper index minus that of its lower one.

  The decomposition is for `repSU3 repGauge` and not for `repGauge` itself because a
  decomposition must know how all four torus generators act, and the transformation law
  constrains only the colour factor: of the four generators only `gaugeTorusGen 0` and
  `gaugeTorusGen 1` are colour transformations. The colour part sends the other two to the
  identity, so their weights vanish by construction. -/
@[implicit_reducible]
noncomputable def gaugeWeightDecomposition (hT : IsSU3FunAntiFun B repGauge T)
    (hmul : IsMulRep repGauge) : GaugeWeightDecomposition (repSU3 repGauge) (span T) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup (isMulRep_repSU3 hmul) fun d : Fin 2 → Fin 3 =>
      GaugeWeightDecomposition.spanSingleton (isMulRep_repSU3 hmul) (T d) (wtWeight d)
        (hT.repSU3_gaugeTorusGen d))
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
  isospin and hypercharge, the colour part of the representation sending the isospin and
  hypercharge generators to the identity. -/
lemma gaugeWeightDecomposition_supp (hmul : IsMulRep repGauge) :
    (hT.gaugeWeightDecomposition hmul).supp
      = {((0, 0, 0, 0) : GaugeWeight), (2, -1, 0, 0), (1, 1, 0, 0),
        (-2, 1, 0, 0), (-1, 2, 0, 0), (-1, -1, 0, 0), (1, -2, 0, 0)} := by
  rw [hT.gaugeWeightDecomposition_supp_eq hmul]
  decide

/-!

## C.4. The zero-weight piece

A colour invariant built from `T` is fixed by the colour part of the representation at the
torus, so it lies in the zero-weight piece, which makes that piece worth describing
explicitly. The weight of a component is the
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

/-- The delta contraction lies in the zero-weight piece. It is fixed by the colour factor,
  so in particular the colour part of the representation fixes it at the torus. -/
lemma deltaContraction_mem_piece_zero (hmul : IsMulRep repGauge) :
    deltaContraction T ∈ (hT.gaugeWeightDecomposition hmul).piece 0 :=
  GaugeWeightDecomposition.mem_zero_of_invariant _ (deltaContraction_mem_span T)
    ((repSU3_invariant_iff_su3 repGauge _).2 (repGauge_deltaContraction hT))

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

Like the gauge weight decomposition the grading is read for `repSU3 repGauge`, the colour
part of the representation, which is where the transformation law constrains every gauge
transformation. The cyclic Weyl element is itself a colour transformation, so the two
representations agree at it outright, which is `repSU3_gaugeSU3Perm`.

Grade zero is in general only a sieve, since `SU3PermDecomposition.mem_zero_of_invariant`
has no converse, but here the two gradings together are sharp: the zero-weight piece is
three dimensional and grade zero is a line in it, so every colour invariant in the span of
the components is a multiple of the delta contraction. That is the singlet of
`3 ⊗ 3̄ = 8 ⊕ 1`, counted exactly once, and it is the conclusion the bi-fundamental case
cannot reach, its zero-weight piece being `⊥`. The gauge form
`exists_smul_deltaContraction_of_invariant` follows at once, a gauge invariant being in
particular fixed by the colour factor.

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
    refine Module.End.mem_eigenspace_iff.mpr ?_
    rw [su3PermSign_zero, one_smul]
    exact repGauge_deltaContraction hT su3Perm
  · rw [zeroPiece_one, Submodule.span_singleton_le_iff_mem]
    exact Module.End.mem_eigenspace_iff.mpr
      (by rw [su3PermSign_one, map_su3Perm_octetOne hT.isSU3FunAntiFunMat_gaugeSU3Perm])
  · rw [zeroPiece_two, Submodule.span_singleton_le_iff_mem]
    exact Module.End.mem_eigenspace_iff.mpr
      (by rw [su3PermSign_two, map_su3Perm_octetTwo hT.isSU3FunAntiFunMat_gaugeSU3Perm])

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
  decomposition, for the colour part of the representation: the cyclic Weyl element grades
  the space the gauge weight cannot split, putting the delta contraction in grade zero and
  the two octet combinations in grades one and two. -/
noncomputable def zeroPieceSU3Perm (hT : IsSU3FunAntiFun B repGauge T)
    (hmul : IsMulRep repGauge) :
    SU3PermDecomposition (repSU3 repGauge) ((hT.gaugeWeightDecomposition hmul).piece 0) where
  piece := zeroPiece T
  piece_le k x hx := by
    rw [repSU3_gaugeSU3Perm]
    exact Module.End.mem_eigenspace_iff.mp (zeroPiece_le_eigenspace hT k hx)
  iSup_piece := hT.iSup_zeroPiece hmul

/-- The pieces of the decomposition are the graded pieces. -/
@[simp] lemma zeroPieceSU3Perm_piece (hmul : IsMulRep repGauge) (k : ZMod 3) :
    (hT.zeroPieceSU3Perm hmul).piece k = zeroPiece T k := rfl

/-- The delta contraction lies in the grade zero piece: it is fixed by the colour factor,
  so in particular the cyclic Weyl element fixes it. -/
lemma deltaContraction_mem_zeroPiece_zero (hT : IsSU3FunAntiFun B repGauge T)
    (hmul : IsMulRep repGauge) :
    deltaContraction T ∈ zeroPiece T 0 :=
  SU3PermDecomposition.mem_zero_of_invariant (hT.zeroPieceSU3Perm hmul)
    (hT.deltaContraction_mem_piece_zero hmul)
    ((repSU3_invariant_iff_su3 repGauge _).2 (repGauge_deltaContraction hT))

/-- Every colour invariant in the span of the components is a multiple of the delta
  contraction. The gauge weight cuts the span down to the space of the three diagonal
  components, and the cyclic Weyl element cuts that space down to the line through their
  sum. Only the colour factor is used, which is all the transformation law constrains. This
  is the statement that `3 ⊗ 3̄` contains exactly one singlet, and it is what
  `IsSU3BiFundamental.eq_zero_of_invariant` denies to two fundamental indices. -/
lemma exists_smul_deltaContraction_of_su3_invariant (hT : IsSU3FunAntiFun B repGauge T)
    (hmul : IsMulRep repGauge) {x : B} (hx : x ∈ span T)
    (hinv : ∀ U : specialUnitaryGroup (Fin 3) ℂ, repGauge (U, 1, 1) x = x) :
    ∃ c : ℂ, x = c • deltaContraction T := by
  have hinv' : ∀ g : GaugeGroupI, repSU3 repGauge g x = x :=
    (repSU3_invariant_iff_su3 repGauge x).2 hinv
  have hmem : x ∈ zeroPiece T 0 :=
    SU3PermDecomposition.mem_zero_of_invariant (hT.zeroPieceSU3Perm hmul)
      (GaugeWeightDecomposition.mem_zero_of_invariant _ hx hinv') hinv'
  rw [zeroPiece_zero] at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  exact ⟨c, hc.symm⟩

/-- Every gauge invariant in the span of the components is a multiple of the delta
  contraction. A gauge invariant is in particular fixed by the transformations trivial on
  isospin and hypercharge, and those alone already force the conclusion. -/
lemma exists_smul_deltaContraction_of_invariant (hT : IsSU3FunAntiFun B repGauge T)
    (hmul : IsMulRep repGauge) {x : B}
    (hx : x ∈ span T) (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    ∃ c : ℂ, x = c • deltaContraction T :=
  hT.exists_smul_deltaContraction_of_su3_invariant hmul hx fun U => hinv (U, 1, 1)

end Grading

/-!

## E. The classification for a family valued in a module

Section D states the classification for a family valued in an algebra, and asks that the
representation act by algebra maps. The conclusion needs neither. A mixed `su(3)` family
is a family of vectors and the delta contraction is a sum of them; the algebra structure
and `IsMulRep` are there only because the gauge weight decomposition and the `SU(3)`
permutation decomposition are set up in an algebra, `IsMulRep` being a statement about a
multiplication.

The gap closes once and for all through the trivial square-zero extension
`TrivSqZeroExt ℂ M` of a module `M`, a commutative `ℂ`-algebra built from the module
structure alone in which the product of two module elements is zero. A representation of
the gauge group on `M` extends to it by acting trivially on the scalar part, and that
extension acts by algebra maps for free, its product being built from the module structure
the representation is linear for. So section D applies in the extension, and
`TrivSqZeroExt.inr` carries the transformation law, the span and the delta contraction
into it and, being injective, brings the conclusion back to `M`. That is
`exists_smul_deltaContraction_of_invariant_module` and its colour companion
`exists_smul_deltaContraction_of_su3_invariant_module`, which are section D with the
algebra structure and the multiplicativity hypothesis both removed, and they are the form
section F divides a submodule out of. `su3_invariant_iff_invariant` closes the section by
reading the classification backwards: inside the span, and once the delta contraction is
known to be gauge invariant, a vector fixed by the colour factor is fixed by the whole
gauge group, which is the bridge a peeling argument crosses when the families are only
colour-covariant and the submodule they are parked in is gauge-stable.

-/

section SquareZero

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
  {ρ : Representation ℂ GaugeGroupI M} {T : (Fin 2 → Fin 3) → M}

/-- The opposite scalar action on a complex vector space, which the square-zero extension
  needs to be a ring. Since `ℂ` is commutative it is the given action read through `unop`,
  and it is given a low priority so that the action of `ℂ` on itself is unaffected. -/
noncomputable local instance (priority := 100) opModule : Module ℂᵐᵒᵖ M :=
  Module.compHom M ((RingHom.id ℂ).fromOpposite fun x y => mul_comm x y)

/-- The two scalar actions of `ℂ` on a complex vector space commute. -/
local instance (priority := 100) smulCommClassOpModule : SMulCommClass ℂ ℂᵐᵒᵖ M :=
  ⟨fun a b m => smul_comm a b.unop m⟩

/-- The opposite scalar action agrees with the given one, `ℂ` being commutative. -/
local instance (priority := 100) isCentralScalarOpModule : IsCentralScalar ℂ M :=
  ⟨fun _ _ => rfl⟩

/-- The linear map of the square-zero extension induced by a linear map of the module: the
  identity on the scalar part and the given map on the module part. -/
def sqZeroMap (f : M →ₗ[ℂ] M) : TrivSqZeroExt ℂ M →ₗ[ℂ] TrivSqZeroExt ℂ M where
  toFun u := TrivSqZeroExt.inl u.fst + TrivSqZeroExt.inr (f u.snd)
  map_add' u v := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_smul' c u := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp

/-- The induced map leaves the scalar part alone. -/
@[simp]
lemma fst_sqZeroMap (f : M →ₗ[ℂ] M) (u : TrivSqZeroExt ℂ M) :
    (sqZeroMap f u).fst = u.fst := by
  simp [sqZeroMap]

/-- The induced map acts by the given map on the module part. -/
@[simp]
lemma snd_sqZeroMap (f : M →ₗ[ℂ] M) (u : TrivSqZeroExt ℂ M) :
    (sqZeroMap f u).snd = f u.snd := by
  simp [sqZeroMap]

/-- The representation carried by the square-zero extension: trivial on the scalar part
  and the given representation on the module part. -/
def sqZeroRep (ρ : Representation ℂ GaugeGroupI M) :
    Representation ℂ GaugeGroupI (TrivSqZeroExt ℂ M) where
  toFun g := sqZeroMap (ρ g)
  map_one' := by
    refine LinearMap.ext fun u => TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_mul' g₁ g₂ := by
    refine LinearMap.ext fun u => TrivSqZeroExt.ext ?_ ?_ <;> simp [Module.End.mul_apply]

/-- The extended representation on the image of the module is the given one. -/
@[simp]
lemma sqZeroRep_inr (ρ : Representation ℂ GaugeGroupI M) (g : GaugeGroupI) (m : M) :
    sqZeroRep ρ g (TrivSqZeroExt.inr m) = TrivSqZeroExt.inr (ρ g m) := by
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp [sqZeroRep]

/-- The extended representation acts by algebra maps, whatever the representation it
  extends: the product of the extension is built from the module structure, which the
  representation is linear for. -/
lemma isMulRep_sqZeroRep (ρ : Representation ℂ GaugeGroupI M) : IsMulRep (sqZeroRep ρ) := by
  intro g u v
  refine TrivSqZeroExt.ext ?_ ?_
  · simp [sqZeroRep]
  · simp [sqZeroRep, TrivSqZeroExt.snd_mul, op_smul_eq_smul]

/-- The images of the components in the square-zero extension again form a family carrying
  one fundamental and one anti-fundamental colour index. -/
lemma isSU3FunAntiFun_sqZeroRep (hT : IsSU3FunAntiFun M ρ T) :
    IsSU3FunAntiFun (TrivSqZeroExt ℂ M) (sqZeroRep ρ) fun l => TrivSqZeroExt.inr (T l) where
  repGauge_T g l := by
    rw [sqZeroRep_inr, hT.repGauge_T g l]
    simp only [TrivSqZeroExt.inr_sum, TrivSqZeroExt.inr_smul]

omit [Module ℂ M] in
/-- The delta contraction of the images is the image of the delta contraction, both being
  the sum of the three diagonal components. -/
lemma deltaContraction_sqZeroRep (T : (Fin 2 → Fin 3) → M) :
    deltaContraction (fun l => TrivSqZeroExt.inr (R := ℂ) (T l))
      = TrivSqZeroExt.inr (deltaContraction T) := by
  simp only [deltaContraction, TrivSqZeroExt.inr_sum]

/-- The image of an element of the span lies in the span of the images. -/
lemma inr_mem_span_sqZeroRep {x : M} (hx : x ∈ span T) :
    TrivSqZeroExt.inr (R := ℂ) x ∈ span fun l => TrivSqZeroExt.inr (R := ℂ) (T l) := by
  obtain ⟨c, rfl⟩ := (mem_span_iff x).1 hx
  refine (mem_span_iff _).2 ⟨c, ?_⟩
  simp only [TrivSqZeroExt.inr_sum, TrivSqZeroExt.inr_smul]

/-- Every gauge invariant in the span of the components is a multiple of the delta
  contraction, for a family valued in a mere module. Neither an algebra structure on the
  target nor multiplicativity of the representation is needed: the square-zero extension
  supplies both, and the injection of the module reflects the conclusion back. -/
lemma exists_smul_deltaContraction_of_invariant_module (hT : IsSU3FunAntiFun M ρ T) {x : M}
    (hx : x ∈ span T) (hinv : ∀ g : GaugeGroupI, ρ g x = x) :
    ∃ c : ℂ, x = c • deltaContraction T := by
  obtain ⟨c, hc⟩ := exists_smul_deltaContraction_of_invariant hT.isSU3FunAntiFun_sqZeroRep
    (isMulRep_sqZeroRep ρ) (inr_mem_span_sqZeroRep hx)
    (fun g => by rw [sqZeroRep_inr, hinv g])
  refine ⟨c, TrivSqZeroExt.inr_injective (R := ℂ) ?_⟩
  rw [hc, deltaContraction_sqZeroRep, TrivSqZeroExt.inr_smul]

/-- The same classification for a family valued in a mere module, read at the colour factor
  alone, which is all the transformation law constrains. -/
lemma exists_smul_deltaContraction_of_su3_invariant_module (hT : IsSU3FunAntiFun M ρ T)
    {x : M} (hx : x ∈ span T)
    (hinv : ∀ V : specialUnitaryGroup (Fin 3) ℂ, ρ (V, 1, 1) x = x) :
    ∃ c : ℂ, x = c • deltaContraction T :=
  hT.toRepSU3.exists_smul_deltaContraction_of_invariant_module hx
    ((repSU3_invariant_iff_su3 ρ x).2 hinv)

/-- Inside the span of the components the two notions of invariance agree, provided the
  delta contraction is gauge invariant: a vector fixed by the colour factor is then fixed by
  the whole gauge group. One direction is free, a colour transformation being a gauge
  transformation; the other is the classification, the colour invariants being multiples of
  the delta contraction. The hypothesis `hdc` is exactly what the transformation law no
  longer supplies, and without it the statement is false, the isospin and hypercharge
  factors being unconstrained. It is stated here rather than in section D because the
  square-zero extension has already shed the algebra structure and the multiplicativity
  hypothesis, and a peeling argument crosses between the two notions in a quotient, which
  carries neither. -/
lemma su3_invariant_iff_invariant (hT : IsSU3FunAntiFun M ρ T)
    (hdc : ∀ g : GaugeGroupI, ρ g (deltaContraction T) = deltaContraction T)
    {x : M} (hx : x ∈ span T) :
    (∀ V : specialUnitaryGroup (Fin 3) ℂ, ρ (V, 1, 1) x = x)
      ↔ ∀ g : GaugeGroupI, ρ g x = x := by
  refine ⟨fun h g => ?_, fun h V => h (V, 1, 1)⟩
  obtain ⟨c, rfl⟩ := hT.exists_smul_deltaContraction_of_su3_invariant_module hx h
  rw [map_smul, hdc]

end SquareZero

/-!

## F. The invariants modulo a stable submodule

A gauge-stable submodule `S` can be divided out. The quotient `B ⧸ S` carries the induced
representation `quotRep`, the images of the components are a mixed `su(3)` family for it
again, and their span is the image of the span, so section E applies verbatim there and
lifts to a classification modulo `S`: an invariant of `span T ⊔ S` is a multiple of the
delta contraction up to an error in `S`, and the error is invariant as well, being the
difference of two invariants.

That is the form a peeling argument wants. Several families are summed, one is classified,
and the ones not yet reached are adjoined to `S`; the quotient is only a module, which is
why section E had to shed the algebra structure first. Stability of `S` is needed and not
just convenient: it is what makes the quotient representation exist, and without it the
statement fails, since for an unstable line `ℂ ∙ v` the only invariant of the line is `0`
while an invariant of the sum may lie outside the span.

`mem_span_sup_su3_invariant_iff` is the colour form, stable and invariant meaning under
`repGauge (U, 1, 1)` throughout, and it is the form the transformation law supports.
`mem_span_sup_invariant_iff`, the gauge form, asks in addition that the delta contraction be
gauge invariant, and cannot do without it: the law constrains the colour factor only, so
the isospin and hypercharge factors may scale the contraction, and that hypothesis is what
makes the error term a gauge invariant rather than merely a colour invariant. Where the two
factors do fix it, as they do for a colour bilinear whose hypercharges cancel, it is
supplied from the transformation law of the underlying fields.

-/

section Quotient

variable {T : (Fin 2 → Fin 3) → B}

/-- The representation induced on the quotient by a gauge-stable submodule. -/
noncomputable def quotRep (repGauge : Representation ℂ GaugeGroupI B) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S) :
    Representation ℂ GaugeGroupI (B ⧸ S) where
  toFun g := S.mapQ S (repGauge g) fun y hy => hS g y hy
  map_one' := by
    ext y
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.mapQ_apply, map_one, Module.End.one_apply]
  map_mul' g₁ g₂ := by
    ext y
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.mapQ_apply, map_mul, Module.End.mul_apply]

/-- The quotient representation on a class is the class of the representation. -/
@[simp]
lemma quotRep_mkQ (S : Submodule ℂ B) (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (g : GaugeGroupI) (y : B) : quotRep repGauge S hS g (S.mkQ y) = S.mkQ (repGauge g y) := rfl

/-- The images of the components in the quotient by a gauge-stable submodule again form a
  family carrying one fundamental and one anti-fundamental colour index. -/
lemma isSU3FunAntiFun_quotRep (hT : IsSU3FunAntiFun B repGauge T) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S) :
    IsSU3FunAntiFun (B ⧸ S) (quotRep repGauge S hS) fun l => S.mkQ (T l) where
  repGauge_T g l := by
    rw [quotRep_mkQ, hT.repGauge_T g l, map_sum]
    exact Finset.sum_congr rfl fun a _ => map_smul _ _ _

/-- The quotient map carries the delta contraction to the delta contraction of the
  images, both being the sum of the three diagonal components. -/
lemma mkQ_deltaContraction (T : (Fin 2 → Fin 3) → B) (S : Submodule ℂ B) :
    S.mkQ (deltaContraction T) = deltaContraction fun l => S.mkQ (T l) := by
  simp only [deltaContraction, map_sum]

/-- The class of an element of the span lies in the span of the classes. -/
lemma mkQ_mem_span_quotRep {x : B} (S : Submodule ℂ B) (hx : x ∈ span T) :
    S.mkQ x ∈ span fun l => S.mkQ (T l) := by
  obtain ⟨c, rfl⟩ := (mem_span_iff x).1 hx
  refine (mem_span_iff _).2 ⟨c, ?_⟩
  rw [map_sum]
  exact Finset.sum_congr rfl fun d _ => map_smul _ _ _

/-- The gauge invariants of the span of the components together with a gauge-stable
  submodule `S`: such an element is a multiple of the delta contraction up to an error in
  `S`, and the error is gauge invariant as well, being the difference of two invariants.
  Stability of `S` is needed, and not just convenient: for an unstable line the only
  invariant of the line is zero, while the sum can carry invariants outside the span. The
  classification is applied in the quotient by `S`, where the images of the components form
  a mixed family again and the target is only a module, which is what section E prepared
  for. This is the form in which one family at a time is peeled off a join of families.

  The gauge invariance `hdc` of the delta contraction is a hypothesis because the
  transformation law does not supply it: the law constrains the colour factor only, so the
  isospin and hypercharge factors may scale the contraction, and it is what makes the error
  term a gauge invariant rather than merely a colour invariant. -/
lemma mem_span_sup_invariant_iff (hT : IsSU3FunAntiFun B repGauge T)
    (x : B) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hdc : ∀ g : GaugeGroupI, repGauge g (deltaContraction T) = deltaContraction T)
    (hx : x ∈ span T ⊔ S)
    (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    ∃ c : ℂ, ∃ y ∈ S, x = c • deltaContraction T + y
      ∧ ∀ g : GaugeGroupI, repGauge g y = y := by
  have hmk : S.mkQ x ∈ span fun l => S.mkQ (T l) := by
    obtain ⟨u, hu, z, hz, huz⟩ := Submodule.mem_sup.1 hx
    rw [← huz, map_add, show S.mkQ z = 0 from (Submodule.Quotient.mk_eq_zero S).2 hz,
      add_zero]
    exact mkQ_mem_span_quotRep S hu
  have hinv' : ∀ g : GaugeGroupI, quotRep repGauge S hS g (S.mkQ x) = S.mkQ x :=
    fun g => by rw [quotRep_mkQ, hinv g]
  obtain ⟨c, hc⟩ :=
    (hT.isSU3FunAntiFun_quotRep S hS).exists_smul_deltaContraction_of_invariant_module hmk hinv'
  rw [← mkQ_deltaContraction T S] at hc
  refine ⟨c, x - c • deltaContraction T, ?_, by abel, fun g => ?_⟩
  · have hker : x - c • deltaContraction T ∈ LinearMap.ker S.mkQ := by
      rw [LinearMap.mem_ker, map_sub, map_smul, hc, sub_self]
    rwa [Submodule.ker_mkQ] at hker
  · rw [map_sub, map_smul, hinv g, hdc g]

/-- The same statement modulo a colour-stable submodule, read at the colour factor alone: a
  vector of the span joined with `S` that the colour factor fixes is a multiple of the delta
  contraction up to an error in `S`, and the error is fixed by the colour factor too. This
  is the form the transformation law supports on its own, no invariance of the delta
  contraction having to be assumed, since `repGauge_deltaContraction` supplies invariance
  under the colour factor outright. -/
lemma mem_span_sup_su3_invariant_iff (hT : IsSU3FunAntiFun B repGauge T)
    (x : B) (S : Submodule ℂ B)
    (hS : ∀ U : specialUnitaryGroup (Fin 3) ℂ, ∀ y ∈ S, repGauge (U, 1, 1) y ∈ S)
    (hx : x ∈ span T ⊔ S)
    (hinv : ∀ U : specialUnitaryGroup (Fin 3) ℂ, repGauge (U, 1, 1) x = x) :
    ∃ c : ℂ, ∃ y ∈ S, x = c • deltaContraction T + y
      ∧ ∀ U : specialUnitaryGroup (Fin 3) ℂ, repGauge (U, 1, 1) y = y := by
  obtain ⟨c, y, hyS, hxy, hyinv⟩ :=
    hT.toRepSU3.mem_span_sup_invariant_iff x S
      ((repSU3_stable_iff_su3 repGauge S).2 hS)
      ((repSU3_invariant_iff_su3 repGauge _).2 (repGauge_deltaContraction hT)) hx
      ((repSU3_invariant_iff_su3 repGauge x).2 hinv)
  exact ⟨c, y, hyS, hxy, (repSU3_invariant_iff_su3 repGauge y).1 hyinv⟩

end Quotient

end IsSU3FunAntiFun

end StandardModel
