/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.GaugeWeightDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.IsSU2BiAdjoint
public import Physlib.Particles.StandardModel.GaugeGroup.SU2PermDecomposition
/-!
# Gauge tensors carrying two `su(2)` fundamental indices

`IsSU2BiFundamental B repGauge T` says that a family `T`, indexed by two `su(2)`
fundamental indices and valued in a module `B` carrying a representation of the gauge
group `GaugeGroupI`, transforms as a tensor `T^{a₁ a₂}` in the `su(2)` factor of the
fundamental representation.

This is the doublet analogue of `IsSU2BiAdjoint`. The Higgs carries one `su(2)`
fundamental index, so a product of two Higgs symbols carries two, and the proposition
here records how such a product transforms.

Two things separate it from the adjoint case. The fundamental representation matrix
`GaugeGroupI.toSU2` has complex entries, where `GaugeAlgebra.adjointMatrix` is real, so
the transformation law is stated over `ℂ` throughout. And the natural invariant built
from two fundamental indices is not a trace: a doublet index has nowhere to be
contracted against another doublet index except through the antisymmetric symbol `ε`,
whose invariance is the statement that the determinant of an `SU(2)` matrix is one.

The law itself is `IsSU2BiFundamentalMat`, which relates one element of `SU(2)` to one
linear map on `B` and mentions no other factor of the gauge group. `IsSU2BiFundamental`
says that the isospin transformation `(1, U, 1)` obeys that law with the matrix of `U`,
for every `U` in `SU(2)`, and it says nothing whatever about the colour and hypercharge
factors: those may move the components as they please. So the mathematics here is `SU(2)`
mathematics twice over, in the law and in the hypothesis, and the conclusions are about
invariance under the isospin factor.

Two things follow that are worth stating at the outset. The gauge weight decomposition
must know how all four torus generators act, and only `gaugeTorusGen 2` is an isospin
transformation, so the decomposition cannot be built for `repGauge`. It is built instead
for `repSU2 repGauge`, the isospin part of the representation, which sends the colour and
hypercharge generators to the identity and so gives them weight zero by construction
rather than by hypothesis; `gaugeWeightDecomposition_supp` still lists exactly the three
weights of the tensor square of the `su(2)` fundamental. And the epsilon contraction is
fixed by the isospin factor only, which is why `repGauge_epsilonContraction` speaks of
`repGauge (1, U, 1)`: the hypercharge factor by itself is enough to scale the contraction,
so no statement about a general gauge transformation is available.

`repSU2` is not declared here. It is declared in `IsSU2BiAdjoint`, the file that first
needed it, and this file imports that one for it: the two constrain the same factor of the
gauge group in the same way, and a second copy of the definition in the same namespace
would collide with the first. The import is heavier than the borrowing warrants, and the
proper home for `repSU2` and its companions is a file both can lean on.

Section A gives the transformation law, the proposition, the isospin part of a
representation and the span of the components, section B the epsilon contraction, which is
the natural isospin invariant built from two fundamental indices, and section C the gauge
weight decomposition of the span, for the isospin part of the representation. Section D
grades the zero-weight piece of that decomposition by the Weyl element of the `SU(2)`
factor, which the gauge weight alone cannot split, and the two gradings together leave the
epsilon contraction spanning the isospin invariants.
-/

@[expose] public section

namespace StandardModel

open Matrix

/-!

## A. Bi-fundamental `su(2)` families and the span of their components

A.1 gives the transformation law and the proposition, A.2 reads a representation of the
gauge group at the isospin factor of its argument alone, and A.3 the span of the
components.

## A.1. The transformation law and the proposition

The transformation law carries one factor of the fundamental matrix per index, with the
summed index in the row slot, exactly as `IsSU2BiAdjoint` carries one factor of
`su2AdjointMatrix` per index. It is recorded by `IsSU2BiFundamentalMat`, a relation
between one element of `SU(2)` and one linear map on `B`, in which no other factor of the
gauge group appears. It is the law obeyed by the conjugate Higgs doublet symbols of
`IsHiggsSector` once their hypercharge character is set aside, the Higgs symbols
themselves obeying the complex conjugate law.

`IsSU2BiFundamental` then says that the gauge transformation `(1, U, 1)` obeys that law
with the matrix of `U`, for every `U` in `SU(2)`. Since `U ↦ (1, U, 1)` is a monoid
homomorphism this is an action of `SU(2)`, and it is all that is assumed: a gauge
transformation with a nontrivial colour or hypercharge factor is not mentioned, and may
move the components arbitrarily. So nothing here forces the colour and hypercharge
coordinates of a weight to vanish; section C gets that instead from `repSU2`, which sends
the colour and hypercharge generators to the identity outright.

-/

/-- The linear map `f` moves the components of the family `T` as the `SU(2)` matrix `U`
  moves a tensor with two fundamental indices: one factor of `U` per index, with the
  summed index in the row slot. -/
def IsSU2BiFundamentalMat {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (U : specialUnitaryGroup (Fin 2) ℂ) (f : B →ₗ[ℂ] B)
    (T : (Fin 2 → Fin 2) → B) : Prop :=
  ∀ l : Fin 2 → Fin 2,
    f (T l) = ∑ a : Fin 2 → Fin 2, (∏ i : Fin 2, U.1 (a i) (l i)) • T a

/-- A family `T` of elements of `B`, indexed by two `su(2)` fundamental indices,
  transforms as a tensor `T^{a₁ a₂}` under the representation `repGauge` of the gauge
  group: an isospin transformation moves the components by the `SU(2)` element it is built
  from. Nothing is asked of the colour or hypercharge factors. -/
structure IsSU2BiFundamental (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B)
    (T : (Fin 2 → Fin 2) → B) : Prop where
  repGauge_T : ∀ g : specialUnitaryGroup (Fin 2) ℂ,
    IsSU2BiFundamentalMat g (repGauge (1, g, 1)) T

namespace IsSU2BiFundamental
set_option linter.unusedVariables false

/-!

## A.2. The isospin part of a representation

Reading a representation of the gauge group at the isospin factor of its argument alone
gives `repSU2`, again a representation of the whole gauge group. It is declared in
`IsSU2BiAdjoint`, the file that first needed it, and imported here rather than repeated,
along with `repSU2_apply`, `isMulRep_repSU2`, `repSU2_invariant_iff_su2` and
`repSU2_stable_iff_su2`. Every construction stated for a representation of `GaugeGroupI`
applies to it verbatim, and a bi-fundamental family for `repGauge` is a bi-fundamental
family for `repSU2 repGauge`, with the same span and the same epsilon contraction.
Invariance under it is invariance under the isospin factor,
`∀ U : SU(2), repGauge (1, U, 1) x = x`, which is exactly what the transformation law
constrains.

`repSU2` carries the weight bookkeeping of section C and the Weyl grading of section D,
both of which ask how a gauge transformation acts and are not available for `repGauge`
itself. The statements are written with the isospin transformation `(1, U, 1)` spelled
out, so that reading one needs no unfolding, and `repSU2_invariant_iff_su2` is the bridge
between the two spellings.

All that is added here is the reading of `repSU2` at the Weyl element, which the adjoint
file has no use for; it sits in this file's own namespace, `repSU2` itself being a
`StandardModel` declaration.

-/

/-- The isospin part of a representation agrees with it at the Weyl element, which is an
  isospin transformation to begin with. -/
lemma repSU2_gaugeSU2Perm {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B) :
    repSU2 repGauge gaugeSU2Perm = repGauge gaugeSU2Perm := rfl

/-!

## A.3. The span of the components

-/

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {U : specialUnitaryGroup (Fin 2) ℂ} {f : B →ₗ[ℂ] B}

/-- A bi-fundamental family for a representation is a bi-fundamental family for its
  isospin part: the transformation law reads only the isospin factor to begin with. The
  span and the epsilon contraction do not mention the representation, so every statement
  of this file transports along this and is read at the isospin factor alone. -/
lemma toRepSU2 {T : (Fin 2 → Fin 2) → B} (hT : IsSU2BiFundamental B repGauge T) :
    IsSU2BiFundamental B (repSU2 repGauge) T where
  repGauge_T g := hT.repGauge_T g

/-- The span of all the components of a family indexed by two `su(2)` fundamental
  indices. -/
def span (T : (Fin 2 → Fin 2) → B) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

/-- An element of `B` lies in the span of the components of `T` precisely when it is a
  linear combination of them. -/
lemma mem_span_iff {T : (Fin 2 → Fin 2) → B} (x : B) :
    x ∈ span T ↔ ∃ (c : (Fin 2 → Fin 2) → ℂ), x = ∑ d, c d • T d := by
  constructor
  · intro hx
    rw [span] at hx
    refine Submodule.iSup_induction
      (motive := fun y => ∃ c : (Fin 2 → Fin 2) → ℂ, y = ∑ d, c d • T d)
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
lemma mem_span {T : (Fin 2 → Fin 2) → B} (d : Fin 2 → Fin 2) : T d ∈ span T :=
  Submodule.mem_iSup_of_mem d (Submodule.mem_span_singleton_self _)

/-!

## B. The epsilon contraction

A doublet index has nowhere to be contracted against another doublet index except through
the antisymmetric symbol, so there is exactly one contraction to make here. That symbol is
not new: Physlib writes a Levi-Civita symbol as the generalized Kronecker delta of a
multi-index against the identity, which is what `euclidLeviCivita` is in four dimensions
and what `epsilon` is here in two. Its invariance is the statement that the determinant of
an `SU(2)` matrix is one, and that is what makes the contraction isospin invariant.

The whole section is about `SU(2)`. The contraction is built from the family alone, and
its invariance is proved for an arbitrary element of `specialUnitaryGroup (Fin 2) ℂ`
acting through an arbitrary linear map; isospin invariance is that statement read at the
isospin transformation `(1, U, 1)`. Isospin invariance is all there is: the law says
nothing about the colour and hypercharge factors, and the hypercharge factor by itself
can scale the contraction, so no statement about a general gauge transformation holds.

-/

/-- A sum over families of two `su(2)` fundamental indices is a double sum. -/
lemma sum_pi_two {M : Type*} [AddCommMonoid M] (F : (Fin 2 → Fin 2) → M) :
    ∑ d : Fin 2 → Fin 2, F d = ∑ x : Fin 2, ∑ y : Fin 2, F ![x, y] := by
  rw [show (∑ d : Fin 2 → Fin 2, F d) = ∑ p : Fin 2 × Fin 2, F ![p.1, p.2] from
      Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin 2) _ _ fun d => by
        congr 1
        funext i
        fin_cases i <;> simp,
    Fintype.sum_prod_type]

/-- The antisymmetric symbol on a pair of `su(2)` fundamental indices: the Levi-Civita
  symbol of `Fin 2`, written the way Physlib writes every Levi-Civita symbol, as the
  generalized Kronecker delta of the pair against the identity. It is normalized so that
  its value on the increasing pair is one. -/
def epsilon (a b : Fin 2) : ℂ :=
  (KroneckerDelta.generalizedKroneckerDelta ![a, b] (id : Fin 2 → Fin 2) : ℤ)

/-- The antisymmetric symbol vanishes on the repeated lower index. -/
@[simp] lemma epsilon_zero_zero : epsilon 0 0 = 0 := by
  simp [epsilon, KroneckerDelta.generalizedKroneckerDelta, Matrix.det_fin_two]

/-- The antisymmetric symbol on the increasing pair. -/
@[simp] lemma epsilon_zero_one : epsilon 0 1 = 1 := by
  simp [epsilon, KroneckerDelta.generalizedKroneckerDelta, Matrix.det_fin_two]

/-- The antisymmetric symbol on the decreasing pair. -/
@[simp] lemma epsilon_one_zero : epsilon 1 0 = -1 := by
  simp [epsilon, KroneckerDelta.generalizedKroneckerDelta, Matrix.det_fin_two]

/-- The antisymmetric symbol vanishes on the repeated upper index. -/
@[simp] lemma epsilon_one_one : epsilon 1 1 = 0 := by
  simp [epsilon, KroneckerDelta.generalizedKroneckerDelta, Matrix.det_fin_two]

/-- The antisymmetric symbol is invariant under the fundamental representation of an
  element of `SU(2)`, because the determinant of an `SU(2)` matrix is one. -/
lemma sum_epsilon_mul (U : specialUnitaryGroup (Fin 2) ℂ) (b c : Fin 2) :
    ∑ x : Fin 2, ∑ y : Fin 2, epsilon x y * (U.1 b x * U.1 c y) = epsilon b c := by
  have hdet : U.1 0 0 * U.1 1 1 - U.1 0 1 * U.1 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact (Matrix.mem_specialUnitaryGroup_iff.mp U.2).2
  fin_cases b <;> fin_cases c <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.sum_univ_two,
      epsilon_zero_zero, epsilon_zero_one, epsilon_one_zero, epsilon_one_one]
  · ring
  · linear_combination hdet
  · linear_combination -hdet
  · ring

/-- The epsilon contraction of a family indexed by two `su(2)` fundamental indices: the
  antisymmetric contraction of the two indices. -/
def epsilonContraction (T : (Fin 2 → Fin 2) → B) : B := T ![0, 1] - T ![1, 0]

/-- The epsilon contraction written as a sum over all pairs of fundamental indices
  weighted by the antisymmetric symbol. -/
lemma epsilonContraction_eq_sum (T : (Fin 2 → Fin 2) → B) :
    epsilonContraction T = ∑ d : Fin 2 → Fin 2, epsilon (d 0) (d 1) • T d := by
  rw [sum_pi_two]
  simp [epsilonContraction, Fin.sum_univ_two, sub_eq_add_neg]

/-- The epsilon contraction lies in the span of the components. -/
lemma epsilonContraction_mem_span (T : (Fin 2 → Fin 2) → B) :
    epsilonContraction T ∈ span T := by
  rw [epsilonContraction]
  exact sub_mem (mem_span _) (mem_span _)

/-- The epsilon contraction is fixed by any linear map moving the components by an
  element of `SU(2)`, the antisymmetric symbol being invariant. This is the whole content
  of the section, and it mentions no factor of the gauge group. -/
lemma map_epsilonContraction {T : (Fin 2 → Fin 2) → B}
    (hf : IsSU2BiFundamentalMat U f T) :
    f (epsilonContraction T) = epsilonContraction T := by
  have step : f (epsilonContraction T)
      = ∑ b : Fin 2 → Fin 2, epsilon (b 0) (b 1) • T b := by
    rw [epsilonContraction_eq_sum, map_sum]
    have h1 : ∀ d : Fin 2 → Fin 2, f (epsilon (d 0) (d 1) • T d)
        = ∑ b : Fin 2 → Fin 2,
          (epsilon (d 0) (d 1) * (U.1 (b 0) (d 0) * U.1 (b 1) (d 1))) • T b := by
      intro d
      rw [map_smul, hf d, Finset.smul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [smul_smul, Fin.prod_univ_two]
    simp only [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    rw [sum_pi_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact sum_epsilon_mul U (b 0) (b 1)
  rw [step, ← epsilonContraction_eq_sum]

/-- The epsilon contraction of a bi-fundamental family is fixed by the isospin factor: an
  isospin transformation moves the components by the `SU(2)` element it is built from,
  which fixes the contraction. That is all the transformation law constrains, the colour
  and hypercharge factors being free to move the contraction. -/
lemma repGauge_epsilonContraction {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2BiFundamental B repGauge T) (U : specialUnitaryGroup (Fin 2) ℂ) :
    repGauge (1, U, 1) (epsilonContraction T) = epsilonContraction T :=
  map_epsilonContraction (hT.repGauge_T U)

/-- The isospin part of the representation fixes the epsilon contraction, at every gauge
  transformation. This is `repGauge_epsilonContraction` read through `repSU2`, and it is
  what the two decompositions of sections C and D consume. -/
lemma repSU2_epsilonContraction {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2BiFundamental B repGauge T) (g : GaugeGroupI) :
    repSU2 repGauge g (epsilonContraction T) = epsilonContraction T :=
  (repSU2_invariant_iff_su2 repGauge _).2 (repGauge_epsilonContraction hT) g

/-!

## C. The gauge weight decomposition of the span

Unlike the adjoint case, no change of basis is needed here. The gauge torus is diagonal
in the fundamental representation of the `SU(2)` factor, so the two basis doublet
directions are already weight vectors, with weights `+1` and `-1` in the isospin
normalization `2T₃`. A component `T d` therefore carries the definite weight `wtWeight d`,
the sum of the weights of its two indices, and the span of the components is already the
join of four weight lines.

The `SU(2)` content of the section is `map_of_diagonal`: a family moved by a diagonal
`SU(2)` matrix has every component an eigenvector, at the product of the diagonal entries
at its two indices. The torus generators enter only through `toSU2_gaugeTorusGen_apply`,
which says that their `SU(2)` parts are diagonal with the characters of `fundWeight` on
the diagonal.

The decomposition is for `repSU2 repGauge` and not for `repGauge` itself. A decomposition
must know how all four torus generators act, and of the four only `gaugeTorusGen 2` is an
isospin transformation, so the transformation law says nothing about the other three. The
isospin part sends them to the identity, so it fixes every component there and their
colour and hypercharge coordinates vanish for that reason. This is why
`gaugeWeightDecomposition_supp` still lists only the three weights of the tensor square of
the `su(2)` fundamental, all of them of the form `(0, 0, k, 0)`.

The stronger typeclass assumptions are forced: `GaugeWeightDecomposition` lives in an
algebra and records multiplicativity of the representation, neither of which
`IsSU2BiFundamental` needs, so both appear as extra arguments here.

-/

/-!

## C.1. Diagonal matrices and the gauge torus

-/

/-- A family moved by a diagonal `SU(2)` matrix has every component an eigenvector, at the
  product of the diagonal entries at its two indices. -/
lemma map_of_diagonal {T : (Fin 2 → Fin 2) → B} (hf : IsSU2BiFundamentalMat U f T)
    (hU : ∀ a b : Fin 2, a ≠ b → U.1 a b = 0) (l : Fin 2 → Fin 2) :
    f (T l) = (U.1 (l 0) (l 0) * U.1 (l 1) (l 1)) • T l := by
  rw [hf l, Finset.sum_eq_single l]
  · rw [Fin.prod_univ_two]
  · intro a _ hal
    have h : a 0 ≠ l 0 ∨ a 1 ≠ l 1 := by
      by_contra hc
      simp only [not_or, ne_eq, not_not] at hc
      exact hal (funext fun j => by fin_cases j <;> simp [hc.1, hc.2])
    rw [Fin.prod_univ_two]
    rcases h with h | h
    · rw [hU _ _ h, zero_mul, zero_smul]
    · rw [hU _ _ h, mul_zero, zero_smul]
  · intro hl
    exact absurd (Finset.mem_univ l) hl

/-- The gauge weight carried by one `su(2)` fundamental index: weak isospin only, with
  the two components of a doublet carrying `2T₃ = ±1`. -/
def fundWeight (s : Fin 2) : GaugeWeight := (0, 0, isoWeight s, 0)

/-- The gauge torus acts diagonally on a fundamental index, by the character of the
  weight of that index. Only the isospin generator acts nontrivially. -/
lemma toSU2_gaugeTorusGen_apply (i : Fin 4) (a b : Fin 2) :
    (GaugeGroupI.toSU2 (gaugeTorusGen i)).1 a b
      = if a = b then (expI : ℂ) ^ GaugeWeight.coord (fundWeight a) i else 0 := by
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [gaugeTorusGen, GaugeGroupI.toSU2, su2ExpI_coe, fundWeight, isoWeight,
      expI_inv_eq_star]

/-- The `SU(2)` part of a torus generator has vanishing off-diagonal entries. -/
lemma toSU2_gaugeTorusGen_offDiag (i : Fin 4) (a b : Fin 2) (hab : a ≠ b) :
    (GaugeGroupI.toSU2 (gaugeTorusGen i)).1 a b = 0 := by
  rw [toSU2_gaugeTorusGen_apply, if_neg hab]

/-- The gauge weight carried by a component of a bi-fundamental family: the sum of the
  weights of its two indices. -/
def wtWeight (l : Fin 2 → Fin 2) : GaugeWeight := fundWeight (l 0) + fundWeight (l 1)

/-!

## C.2. The components are weight vectors

-/

/-- An isospin transformation built from a diagonal `SU(2)` element scales every component
  of a bi-fundamental family, by the product of the diagonal entries at its two indices.
  This is `map_of_diagonal` read at the transformation law. -/
lemma repGauge_su2_of_diagonal {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2BiFundamental B repGauge T) (U : specialUnitaryGroup (Fin 2) ℂ)
    (hU : ∀ a b : Fin 2, a ≠ b → U.1 a b = 0) (l : Fin 2 → Fin 2) :
    repGauge (1, U, 1) (T l) = (U.1 (l 0) (l 0) * U.1 (l 1) (l 1)) • T l :=
  map_of_diagonal (hT.repGauge_T U) hU l

/-- Every component of a bi-fundamental family is a simultaneous eigenvector of the gauge
  torus in the isospin part of the representation, at the character of the sum of the
  weights of its two indices. The colour and hypercharge generators have trivial isospin
  factor, so the isospin part fixes every component at those, matching the vanishing
  colour and hypercharge coordinates of the weights. -/
lemma repSU2_gaugeTorusGen {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2BiFundamental B repGauge T) (l : Fin 2 → Fin 2) (i : Fin 4) :
    repSU2 repGauge (gaugeTorusGen i) (T l)
      = ((expI : ℂ) ^ GaugeWeight.coord (wtWeight l) i) • T l := by
  rw [repSU2_apply, hT.repGauge_su2_of_diagonal _ (toSU2_gaugeTorusGen_offDiag i) l]
  congr 1
  rw [toSU2_gaugeTorusGen_apply, toSU2_gaugeTorusGen_apply, if_pos rfl, if_pos rfl,
    wtWeight, GaugeWeight.coord_add, zpow_add₀ expI_ne_zero]

/-!

## C.3. The decomposition

-/

section Decomposition

variable {B : Type*} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {T : (Fin 2 → Fin 2) → B}

/-- The gauge weight decomposition of the span of a bi-fundamental `su(2)` family, for the
  isospin part of the representation. The span is the join of the lines through the four
  components, and each of those carries the sum of the weights of its two indices.

  The decomposition is for `repSU2 repGauge` and not for `repGauge` itself because a
  decomposition must know how all four torus generators act, and the transformation law
  constrains only the isospin factor: of the four generators only `gaugeTorusGen 2` is an
  isospin transformation. The isospin part sends the other three to the identity, so their
  weights vanish by construction. -/
@[implicit_reducible]
noncomputable def gaugeWeightDecomposition (hT : IsSU2BiFundamental B repGauge T)
    (hmul : IsMulRep repGauge) :
    GaugeWeightDecomposition (repSU2 repGauge) (span T) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup (isMulRep_repSU2 hmul) fun d : Fin 2 → Fin 2 =>
      GaugeWeightDecomposition.spanSingleton (isMulRep_repSU2 hmul) (T d) (wtWeight d)
        (repSU2_gaugeTorusGen hT d))
    _ rfl

variable (hT : IsSU2BiFundamental B repGauge T)

/-- The pieces of the decomposition: the weight-`w` piece is the join of the lines through
  those components whose weight is `w`. -/
lemma gaugeWeightDecomposition_piece (hmul : IsMulRep repGauge) (w : GaugeWeight) :
    (hT.gaugeWeightDecomposition hmul).piece w
      = ⨆ d : Fin 2 → Fin 2, (if w = wtWeight d then ℂ ∙ T d else ⊥) := rfl

/-- The support of the decomposition, before evaluation. -/
lemma gaugeWeightDecomposition_supp_eq (hmul : IsMulRep repGauge) :
    (hT.gaugeWeightDecomposition hmul).supp
      = Finset.univ.biUnion fun d : Fin 2 → Fin 2 =>
        ({wtWeight d} : Finset GaugeWeight) := rfl

/-- The gauge weights carried by a bi-fundamental `su(2)` family: the three weights of the
  tensor square of the `su(2)` fundamental. Every one of them has vanishing colour and
  hypercharge, the isospin part of the representation sending the colour and hypercharge
  generators to the identity. -/
lemma gaugeWeightDecomposition_supp (hmul : IsMulRep repGauge) :
    (hT.gaugeWeightDecomposition hmul).supp
      = {((0, 0, 2, 0) : GaugeWeight), (0, 0, 0, 0), (0, 0, -2, 0)} := by
  rw [hT.gaugeWeightDecomposition_supp_eq hmul]
  decide

/-!

## C.4. The zero-weight piece

An isospin invariant built from `T` is fixed by the isospin part of the representation at
the torus, so it lies in the zero-weight piece, which makes that piece worth describing
explicitly. The weight of a component is
the sum of the isospin weights of its two indices, each `±1`, so it vanishes exactly when
the two indices differ. That leaves the two mixed components, and the zero-weight piece is
the plane they span, the multiplicity of the zero weight in the tensor square of the
`su(2)` fundamental.

-/

/-- A component of a bi-fundamental family carries vanishing gauge weight precisely when
  its two indices differ, the isospin weights `+1` and `-1` then cancelling. -/
lemma wtWeight_eq_zero_iff (l : Fin 2 → Fin 2) :
    wtWeight l = 0 ↔ l = ![0, 1] ∨ l = ![1, 0] := by
  revert l
  decide

/-- The zero-weight piece of the gauge weight decomposition, explicitly: the plane spanned
  by the two mixed components. -/
lemma gaugeWeightDecomposition_piece_zero (hmul : IsMulRep repGauge) :
    (hT.gaugeWeightDecomposition hmul).piece 0 = ℂ ∙ T ![0, 1] ⊔ ℂ ∙ T ![1, 0] := by
  rw [hT.gaugeWeightDecomposition_piece hmul]
  refine le_antisymm (iSup_le fun d => ?_) (sup_le ?_ ?_)
  · split_ifs with hd
    · rcases (wtWeight_eq_zero_iff d).1 hd.symm with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    · exact bot_le
  · exact le_iSup_of_le ![0, 1] (le_of_eq (if_pos (by decide)).symm)
  · exact le_iSup_of_le ![1, 0] (le_of_eq (if_pos (by decide)).symm)

/-- The epsilon contraction lies in the zero-weight piece. The isospin factor fixes it, so
  in particular the isospin part of the representation fixes it at the torus. -/
lemma epsilonContraction_mem_piece_zero (hmul : IsMulRep repGauge) :
    epsilonContraction T ∈ (hT.gaugeWeightDecomposition hmul).piece 0 :=
  GaugeWeightDecomposition.mem_zero_of_invariant _ (epsilonContraction_mem_span T)
    (repSU2_epsilonContraction hT)

end Decomposition

/-!

## D. The `SU(2)` permutation decomposition of the zero-weight piece

The gauge weight cannot separate the two mixed components: they carry the same weight, and
section C.4 leaves the zero-weight piece as the plane they span. The Weyl element of the
`SU(2)` factor does separate them. Its matrix `!![0, -1; 1, 0]` exchanges the two doublet
directions, so it exchanges the two mixed components and negates them, and its
eigenvectors on that plane are their antisymmetric combination, which is the epsilon
contraction, at eigenvalue `1`, and their symmetric combination, the neutral component of
the isospin triplet, at eigenvalue `-1`. That much is again `SU(2)`: the Weyl element
enters as the element `su2Perm` of `specialUnitaryGroup (Fin 2) ℂ`, and the gauge group
only through `toSU2_gaugeSU2Perm`, which says that `gaugeSU2Perm` is that element.

The grading is therefore concentrated in the grades zero and two, as it must be for a
product of an even number of doublets. It is built for `repSU2 repGauge`, as is the gauge
weight decomposition it grades, and nothing is lost by that: `gaugeSU2Perm` is an isospin
transformation, so the isospin part of the representation acts at it exactly as the
representation itself does. Grade zero is in general only a sieve, since
`SU2PermDecomposition.mem_zero_of_invariant` has no converse, but here the two gradings
together are sharp: the zero-weight piece is a plane and grade zero is a line in it, so
every isospin invariant in the span of the components is a multiple of the epsilon
contraction. The ten-dimensional zero-weight piece of `IsSU3BiAdjoint` is what a sieve
looks like when it is not sharp.

`mem_span_and_su2_invariant_iff` of D.3 is the classification proper. Its gauge
counterpart `mem_span_and_invariant_iff` needs the epsilon contraction to be gauge
invariant and takes that as a hypothesis: the transformation law leaves the colour and
hypercharge factors free, so they may scale the contraction, and then the multiples of it
are not gauge invariants at all. The same hypothesis is what `su2_invariant_iff_invariant`
needs to upgrade isospin invariance in the span to gauge invariance; without it that
statement is false.

-/

/-!

## D.1. The Weyl element on the two mixed components

-/

/-- The entries of the Weyl element of `SU(2)`, which exchanges the two doublet directions
  and negates one of them. -/
lemma su2Perm_apply (a b : Fin 2) :
    (su2Perm : specialUnitaryGroup (Fin 2) ℂ).1 a b = !![0, -1; 1, 0] a b := rfl

/-- The `SU(2)` part of the Weyl element of the gauge group is the Weyl element of
  `SU(2)`. -/
lemma toSU2_gaugeSU2Perm : GaugeGroupI.toSU2 gaugeSU2Perm = su2Perm := rfl

/-- The Weyl element sends the first mixed component to minus the second. -/
lemma map_su2Perm_zero_one {T : (Fin 2 → Fin 2) → B}
    (hf : IsSU2BiFundamentalMat su2Perm f T) :
    f (T ![0, 1]) = -T ![1, 0] := by
  rw [hf ![0, 1], sum_pi_two]
  simp [Fin.sum_univ_two, Fin.prod_univ_two, su2Perm_apply]

/-- The Weyl element sends the second mixed component to minus the first. -/
lemma map_su2Perm_one_zero {T : (Fin 2 → Fin 2) → B}
    (hf : IsSU2BiFundamentalMat su2Perm f T) :
    f (T ![1, 0]) = -T ![0, 1] := by
  rw [hf ![1, 0], sum_pi_two]
  simp [Fin.sum_univ_two, Fin.prod_univ_two, su2Perm_apply]

/-- The symmetric combination of the two mixed components: the neutral component of the
  isospin triplet in the tensor square of the `su(2)` fundamental, and the partner of the
  epsilon contraction under the Weyl element. -/
def neutralTriplet (T : (Fin 2 → Fin 2) → B) : B := T ![0, 1] + T ![1, 0]

/-- The Weyl element negates the neutral triplet combination, exchanging the two mixed
  components and carrying a sign as it does so. -/
lemma map_su2Perm_neutralTriplet {T : (Fin 2 → Fin 2) → B}
    (hf : IsSU2BiFundamentalMat su2Perm f T) :
    f (neutralTriplet T) = -neutralTriplet T := by
  rw [neutralTriplet, map_add, map_su2Perm_zero_one hf, map_su2Perm_one_zero hf]
  abel

/-- The Weyl element of the gauge group sends the first mixed component to minus the
  second. It is an isospin transformation, so the transformation law reaches it. -/
lemma repGauge_gaugeSU2Perm_zero_one {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2BiFundamental B repGauge T) :
    repGauge gaugeSU2Perm (T ![0, 1]) = -T ![1, 0] :=
  map_su2Perm_zero_one (hT.repGauge_T su2Perm)

/-- The Weyl element of the gauge group sends the second mixed component to minus the
  first. -/
lemma repGauge_gaugeSU2Perm_one_zero {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2BiFundamental B repGauge T) :
    repGauge gaugeSU2Perm (T ![1, 0]) = -T ![0, 1] :=
  map_su2Perm_one_zero (hT.repGauge_T su2Perm)

/-- The Weyl element of the gauge group negates the neutral triplet combination. -/
lemma repGauge_gaugeSU2Perm_neutralTriplet {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2BiFundamental B repGauge T) :
    repGauge gaugeSU2Perm (neutralTriplet T) = -neutralTriplet T :=
  map_su2Perm_neutralTriplet (hT.repGauge_T su2Perm)

/-- The Weyl element of the gauge group fixes the epsilon contraction, being an isospin
  transformation. -/
lemma repGauge_gaugeSU2Perm_epsilonContraction {T : (Fin 2 → Fin 2) → B}
    (hT : IsSU2BiFundamental B repGauge T) :
    repGauge gaugeSU2Perm (epsilonContraction T) = epsilonContraction T :=
  repGauge_epsilonContraction hT su2Perm

/-- Replacing two elements by their antisymmetric and symmetric combinations spans the
  same submodule, since two is invertible. -/
lemma sup_span_sub_add (a b : B) : ℂ ∙ (a - b) ⊔ ℂ ∙ (a + b) = ℂ ∙ a ⊔ ℂ ∙ b := by
  have hmem : ∀ x y : B, x ∈ ℂ ∙ x ⊔ ℂ ∙ y ∧ y ∈ ℂ ∙ x ⊔ ℂ ∙ y := fun x y =>
    ⟨Submodule.mem_sup_left (Submodule.mem_span_singleton_self _),
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)⟩
  refine le_antisymm (sup_le ?_ ?_) (sup_le ?_ ?_) <;>
    rw [Submodule.span_singleton_le_iff_mem]
  · exact sub_mem (hmem a b).1 (hmem a b).2
  · exact add_mem (hmem a b).1 (hmem a b).2
  · have h : (2⁻¹ : ℂ) • ((a - b) + (a + b)) ∈ ℂ ∙ (a - b) ⊔ ℂ ∙ (a + b) :=
      Submodule.smul_mem _ _ (add_mem (hmem (a - b) (a + b)).1 (hmem (a - b) (a + b)).2)
    rwa [show (2⁻¹ : ℂ) • ((a - b) + (a + b)) = a from by module] at h
  · have h : (2⁻¹ : ℂ) • ((a + b) - (a - b)) ∈ ℂ ∙ (a - b) ⊔ ℂ ∙ (a + b) :=
      Submodule.smul_mem _ _ (sub_mem (hmem (a - b) (a + b)).2 (hmem (a - b) (a + b)).1)
    rwa [show (2⁻¹ : ℂ) • ((a + b) - (a - b)) = b from by module] at h

/-- The epsilon contraction and the neutral triplet combination span the plane of the two
  mixed components, being their antisymmetric and symmetric combinations. -/
lemma sup_span_epsilonContraction_neutralTriplet (T : (Fin 2 → Fin 2) → B) :
    ℂ ∙ epsilonContraction T ⊔ ℂ ∙ neutralTriplet T
      = ℂ ∙ T ![0, 1] ⊔ ℂ ∙ T ![1, 0] :=
  sup_span_sub_add _ _

/-!

## D.2. The grading

-/

section Grading

variable {B : Type*} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}

/-- The grade `k` piece of the `SU(2)` permutation decomposition of the zero-weight piece:
  the epsilon contraction in grade zero, the neutral triplet combination in grade two, and
  nothing in the odd grades, which carry the odd-degree terms alone. -/
noncomputable def zeroPiece (T : (Fin 2 → Fin 2) → B) (k : ZMod 4) : Submodule ℂ B :=
  if k = 0 then ℂ ∙ epsilonContraction T
  else if k = 2 then ℂ ∙ neutralTriplet T else ⊥

variable {T : (Fin 2 → Fin 2) → B}

/-- The grade zero piece: the line through the epsilon contraction. -/
@[simp] lemma zeroPiece_zero : zeroPiece T 0 = ℂ ∙ epsilonContraction T := by
  rw [zeroPiece, if_pos rfl]

/-- The grade one piece is empty. -/
@[simp] lemma zeroPiece_one : zeroPiece T 1 = ⊥ := by
  rw [zeroPiece, if_neg (by decide), if_neg (by decide)]

/-- The grade two piece: the line through the neutral triplet combination. -/
@[simp] lemma zeroPiece_two : zeroPiece T 2 = ℂ ∙ neutralTriplet T := by
  rw [zeroPiece, if_neg (by decide), if_pos rfl]

/-- The grade three piece is empty. -/
@[simp] lemma zeroPiece_three : zeroPiece T 3 = ⊥ := by
  rw [zeroPiece, if_neg (by decide), if_neg (by decide)]

/-- Each graded piece is of pure sign under the Weyl element. -/
lemma zeroPiece_le_eigenspace (hT : IsSU2BiFundamental B repGauge T) (k : ZMod 4) :
    zeroPiece T k ≤ Module.End.eigenspace (repGauge gaugeSU2Perm) (su2PermSign k) := by
  have hcases : ∀ j : ZMod 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
  rcases hcases k with rfl | rfl | rfl | rfl
  · rw [zeroPiece_zero, Submodule.span_singleton_le_iff_mem]
    exact Module.End.mem_eigenspace_iff.mpr
      (by rw [su2PermSign_zero, one_smul, repGauge_gaugeSU2Perm_epsilonContraction hT])
  · rw [zeroPiece_one]
    exact bot_le
  · rw [zeroPiece_two, Submodule.span_singleton_le_iff_mem]
    exact Module.End.mem_eigenspace_iff.mpr
      (by rw [su2PermSign_two, neg_one_smul, repGauge_gaugeSU2Perm_neutralTriplet hT])
  · rw [zeroPiece_three]
    exact bot_le

variable (hT : IsSU2BiFundamental B repGauge T)

/-- The graded pieces exhaust the zero-weight piece. -/
lemma iSup_zeroPiece (hmul : IsMulRep repGauge) :
    (⨆ k : ZMod 4, zeroPiece T k) = (hT.gaugeWeightDecomposition hmul).piece 0 := by
  rw [hT.gaugeWeightDecomposition_piece_zero hmul,
    ← sup_span_epsilonContraction_neutralTriplet T]
  have hcases : ∀ j : ZMod 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide
  refine le_antisymm (iSup_le fun k => ?_) (sup_le ?_ ?_)
  · rcases hcases k with rfl | rfl | rfl | rfl
    · rw [zeroPiece_zero]
      exact le_sup_left
    · rw [zeroPiece_one]
      exact bot_le
    · rw [zeroPiece_two]
      exact le_sup_right
    · rw [zeroPiece_three]
      exact bot_le
  · exact le_iSup_of_le 0 (le_of_eq zeroPiece_zero.symm)
  · exact le_iSup_of_le 2 (le_of_eq zeroPiece_two.symm)

/-- The `SU(2)` permutation decomposition of the zero-weight piece of the gauge weight
  decomposition: the Weyl element grades the plane the gauge weight cannot split, putting
  the epsilon contraction in grade zero and the neutral triplet combination in grade two.
  It is stated for the isospin part of the representation, as the decomposition it grades
  is, though the two agree at the Weyl element. -/
noncomputable def zeroPieceSU2Perm (hT : IsSU2BiFundamental B repGauge T)
    (hmul : IsMulRep repGauge) :
    SU2PermDecomposition (repSU2 repGauge)
      ((hT.gaugeWeightDecomposition hmul).piece 0) where
  piece := zeroPiece T
  piece_le k x hx := by
    rw [repSU2_gaugeSU2Perm]
    exact Module.End.mem_eigenspace_iff.mp (zeroPiece_le_eigenspace hT k hx)
  iSup_piece := hT.iSup_zeroPiece hmul

/-- The pieces of the decomposition are the graded pieces. -/
@[simp] lemma zeroPieceSU2Perm_piece (hmul : IsMulRep repGauge) (k : ZMod 4) :
    (hT.zeroPieceSU2Perm hmul).piece k = zeroPiece T k := rfl

/-- The epsilon contraction lies in the grade zero piece: the isospin factor fixes it, so
  in particular the Weyl element does. -/
lemma epsilonContraction_mem_zeroPiece_zero (hT : IsSU2BiFundamental B repGauge T)
    (hmul : IsMulRep repGauge) :
    epsilonContraction T ∈ zeroPiece T 0 :=
  SU2PermDecomposition.mem_zero_of_invariant (hT.zeroPieceSU2Perm hmul)
    (hT.epsilonContraction_mem_piece_zero hmul) (repSU2_epsilonContraction hT)

/-!

## D.3. The classification

-/

/-- Every isospin invariant in the span of the components is a multiple of the epsilon
  contraction. The gauge weight cuts the span down to the plane of the two mixed
  components, and the Weyl element cuts that plane down to the line through their
  antisymmetric combination. Only the isospin factor is used, which is all the
  transformation law constrains. -/
lemma exists_smul_epsilonContraction_of_su2_invariant
    (hT : IsSU2BiFundamental B repGauge T) (hmul : IsMulRep repGauge) {x : B}
    (hx : x ∈ span T)
    (hinv : ∀ U : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, U, 1) x = x) :
    ∃ c : ℂ, x = c • epsilonContraction T := by
  have hinv' : ∀ g : GaugeGroupI, repSU2 repGauge g x = x :=
    (repSU2_invariant_iff_su2 repGauge x).2 hinv
  have hmem : x ∈ zeroPiece T 0 :=
    SU2PermDecomposition.mem_zero_of_invariant (hT.zeroPieceSU2Perm hmul)
      (GaugeWeightDecomposition.mem_zero_of_invariant _ hx hinv') hinv'
  rw [zeroPiece_zero] at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  exact ⟨c, hc.symm⟩

/-- Every gauge invariant in the span of the components is a multiple of the epsilon
  contraction. A gauge invariant is in particular fixed by the transformations trivial on
  colour and hypercharge, and those alone already force the conclusion. -/
lemma exists_smul_epsilonContraction_of_invariant (hT : IsSU2BiFundamental B repGauge T)
    (hmul : IsMulRep repGauge) {x : B}
    (hx : x ∈ span T) (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    ∃ c : ℂ, x = c • epsilonContraction T :=
  hT.exists_smul_epsilonContraction_of_su2_invariant hmul hx fun U => hinv (1, U, 1)

/-- The isospin invariants in the span of the components are exactly the multiples of the
  epsilon contraction. The gauge weight and the Weyl element bound them from above, and
  the epsilon contraction is itself isospin invariant and in the span, which bounds them
  from below. This is the one singlet of `2 ⊗ 2`. -/
lemma mem_span_and_su2_invariant_iff (hT : IsSU2BiFundamental B repGauge T)
    (hmul : IsMulRep repGauge) (x : B) :
    (x ∈ span T ∧ ∀ U : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, U, 1) x = x)
      ↔ x ∈ ℂ ∙ epsilonContraction T := by
  refine ⟨fun h => ?_, fun hx => ?_⟩
  · obtain ⟨c, rfl⟩ := hT.exists_smul_epsilonContraction_of_su2_invariant hmul h.1 h.2
    exact Submodule.mem_span_singleton.2 ⟨c, rfl⟩
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    exact ⟨Submodule.smul_mem _ _ (epsilonContraction_mem_span T),
      fun U => by rw [map_smul, repGauge_epsilonContraction hT]⟩

/-- The gauge invariants in the span of the components are exactly the multiples of the
  epsilon contraction, once the epsilon contraction is known to be gauge invariant. That
  hypothesis cannot be dropped: the transformation law says nothing about the colour and
  hypercharge factors, and the hypercharge factor by itself can scale the contraction,
  after which the right-hand side has invariants that the left-hand side has not. Where
  the two factors do fix it, as they do for a product of a Higgs doublet with its
  conjugate, the hypothesis is supplied from the transformation law of the underlying
  field. -/
lemma mem_span_and_invariant_iff (hT : IsSU2BiFundamental B repGauge T)
    (hmul : IsMulRep repGauge) (x : B)
    (hec : ∀ g : GaugeGroupI,
      repGauge g (epsilonContraction T) = epsilonContraction T) :
    (x ∈ span T ∧ ∀ g : GaugeGroupI, repGauge g x = x)
      ↔ x ∈ ℂ ∙ epsilonContraction T := by
  refine ⟨fun h => ?_, fun hx => ?_⟩
  · obtain ⟨c, rfl⟩ := hT.exists_smul_epsilonContraction_of_invariant hmul h.1 h.2
    exact Submodule.mem_span_singleton.2 ⟨c, rfl⟩
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    exact ⟨Submodule.smul_mem _ _ (epsilonContraction_mem_span T),
      fun g => by rw [map_smul, hec]⟩

/-- Inside the span of the components the two notions of invariance agree, provided the
  epsilon contraction is gauge invariant: a vector fixed by the isospin factor is then
  fixed by the whole gauge group. One direction is free, an isospin transformation being a
  gauge transformation; the other is the classification, the isospin invariants being
  multiples of the epsilon contraction. The hypothesis `hec` is exactly what the
  transformation law no longer supplies, and without it the statement is false, the colour
  and hypercharge factors being unconstrained. -/
lemma su2_invariant_iff_invariant (hT : IsSU2BiFundamental B repGauge T)
    (hmul : IsMulRep repGauge)
    (hec : ∀ g : GaugeGroupI,
      repGauge g (epsilonContraction T) = epsilonContraction T)
    {x : B} (hx : x ∈ span T) :
    (∀ U : specialUnitaryGroup (Fin 2) ℂ, repGauge (1, U, 1) x = x)
      ↔ ∀ g : GaugeGroupI, repGauge g x = x := by
  refine ⟨fun h g => ?_, fun h U => h (1, U, 1)⟩
  obtain ⟨c, rfl⟩ := hT.exists_smul_epsilonContraction_of_su2_invariant hmul hx h
  rw [map_smul, hec]

end Grading

end IsSU2BiFundamental

end StandardModel
