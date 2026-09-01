/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.GaugeWeightDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.SU3PermDecomposition
/-!
# Gauge tensors carrying two `su(3)` fundamental indices

`IsSU3BiFundamental B repGauge T` says that a family `T`, indexed by two `su(3)`
fundamental indices and valued in a module `B` carrying a representation of the gauge
group `GaugeGroupI`, transforms as a tensor `T^{a₁ a₂}` in the `su(3)` factor of the
fundamental representation.

This is the colour analogue of `IsSU2BiFundamental`, and the two files agree until the
moment an invariant is asked for. Two `su(2)` doublet indices can be contracted, through
the antisymmetric symbol `ε`, because the doublet is pseudo-real. Two colour triplet
indices cannot. The invariant tensors of `SU(3)` are `ε_{abc}`, which needs three
fundamental indices, and `δ^a_b`, which needs one fundamental index and one
anti-fundamental one; `3 ⊗ 3 = 6 ⊕ 3̄` contains no singlet. So the analogue of
`epsilonContraction` is not merely missing from this file: it does not exist.

Section A gives the proposition and the span of its components. Section B replaces the
epsilon contraction of the doublet case by the theorem that stands in its place: the centre
`ℤ₃` of `SU(3)` scales a two-index tensor by `ω²`, so an invariant pairing of two colour
triplet indices vanishes, and so does every gauge invariant in the span of the components.
Section C is the gauge weight decomposition of the span, and it reaches the same conclusion
from the torus alone: no sum of two colour weights of the triplet vanishes, so the
zero-weight piece is `⊥`.

There is no section D. The `SU(2)` file grades its zero-weight piece by the Weyl element
because the gauge weight leaves a plane it cannot split; here the gauge weight leaves
nothing at all, and `SU3PermDecomposition` has nothing to refine.
-/

@[expose] public section

namespace StandardModel

open Matrix

/-!

## A. Bi-fundamental `su(3)` families and the span of their components

The transformation law carries one factor of the fundamental matrix `GaugeGroupI.toSU3 g`
per index, with the summed index in the row slot, exactly as `IsSU2BiFundamental` carries
one factor of `GaugeGroupI.toSU2 g` per index. Since `toSU3` is a monoid homomorphism this
is an action. It is the `SU(3)` factor alone, and is the law obeyed by a product of two
colour triplet symbols once their weak isospin and hypercharge characters are set aside.

The element `g` still ranges over the whole of `GaugeGroupI`, and that is what makes the
proposition say more than a statement about `SU(3)` would. The right-hand side sees only
`GaugeGroupI.toSU3 g`, so taking `g` in the weak isospin or hypercharge factor forces that
factor to fix every component. Section C reads that off as the vanishing of the isospin and
hypercharge coordinates of every weight, and `GaugeWeightDecomposition` is stated for
representations of `GaugeGroupI`, which a bare `SU(3)` representation cannot supply.

-/

/-- A family `T` of elements of `B`, indexed by two `su(3)` fundamental indices,
  transforms as a tensor `T^{a₁ a₂}` under the representation `repGauge` of the gauge
  group. -/
structure IsSU3BiFundamental (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B)
    (T : (Fin 2 → Fin 3) → B) : Prop where
  repGauge_T : ∀ (g : GaugeGroupI) (l : Fin 2 → Fin 3),
    repGauge g (T l) = ∑ a : Fin 2 → Fin 3,
      (∏ i : Fin 2, (GaugeGroupI.toSU3 g).1 (a i) (l i)) • T a

namespace IsSU3BiFundamental
set_option linter.unusedVariables false

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {T : (Fin 2 → Fin 3) → B}
  (hT : IsSU3BiFundamental B repGauge T)

/-- The span of all the components. -/
def span (hT : IsSU3BiFundamental B repGauge T) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

/-- An element of `B` lies in the span of the components of `T` precisely when it is a
  linear combination of them. -/
lemma mem_span_iff (x : B) :
    x ∈ hT.span ↔ ∃ (c : (Fin 2 → Fin 3) → ℂ), x = ∑ d, c d • T d := by
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

end IsSU3BiFundamental

/-!

## B. The absence of a two-index invariant

Here the file parts company with `IsSU2BiFundamental`. There the two doublet indices are
contracted by the antisymmetric symbol, and its invariance is the statement that an `SU(2)`
matrix has determinant one. Nothing plays that role for two colour triplet indices: the
invariant tensors of `SU(3)` are the three-index `ε_{abc}` and the mixed `δ^a_b`, and
`3 ⊗ 3 = 6 ⊕ 3̄` has no singlet in it.

That is a theorem rather than an absence, and the centre of `SU(3)` proves it. The scalar
matrix `ω • 1`, with `ω` the primitive cube root of unity already used by
`SU3PermDecomposition`, lies in `SU(3)` precisely because `ω ^ 3 = 1` is the determinant
condition. It scales a tensor carrying `k` fundamental indices by `ω ^ k`, so an invariant
one forces `3 ∣ k`, and `k = 2` fails. This is triality: a colour singlet is built from
three quarks, or from a quark and an antiquark, never from two quarks.

The same element settles the question for the family itself, with no hypothesis beyond the
transformation law: every gauge invariant in the span of the components is zero. Section C
reaches that conclusion again from the gauge torus alone, at the price of the extra
assumptions that a gauge weight decomposition carries.

-/

/-- The primitive cube root of unity has modulus one, so it is inverted by conjugation. -/
lemma su3Omega_mul_star : su3Omega * star su3Omega = 1 := by
  have hnorm : ‖su3Omega‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one su3Omega_pow_three (by norm_num)
  rw [show star su3Omega = (starRingEnd ℂ) su3Omega from rfl, Complex.mul_conj]
  simp [Complex.normSq_eq_norm_sq, hnorm]

/-- The square of the primitive cube root of unity is not one. -/
lemma su3Omega_pow_two_ne_one : su3Omega ^ 2 ≠ 1 :=
  su3Omega_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)

/-- The generator `ω • 1` of the centre `ℤ₃` of `SU(3)`. It is a scalar matrix, so it
  commutes with everything, and it lies in the special unitary group because the
  determinant condition on a scalar matrix in three dimensions is exactly `ω ^ 3 = 1`. -/
noncomputable def su3Centre : specialUnitaryGroup (Fin 3) ℂ :=
  ⟨Matrix.diagonal ![su3Omega, su3Omega, su3Omega],
    Matrix.mem_specialUnitaryGroup_diagonal _
      (fun i => by fin_cases i <;> simpa using su3Omega_mul_star)
      (by simp [Fin.prod_univ_three, ← pow_three'])⟩

/-- The central element acts on a colour index by the scalar `ω`. -/
lemma su3Centre_apply (a b : Fin 3) :
    (su3Centre : specialUnitaryGroup (Fin 3) ℂ).1 a b = if a = b then su3Omega else 0 := by
  fin_cases a <;> fin_cases b <;> simp [su3Centre]

/-- The generator of the centre `ℤ₃` of the colour factor, as an element of the gauge
  group. -/
noncomputable def gaugeSU3Centre : GaugeGroupI := ⟨su3Centre, 1, 1⟩

/-- The colour part of the central gauge element is the central element of `SU(3)`. -/
lemma toSU3_gaugeSU3Centre : GaugeGroupI.toSU3 gaugeSU3Centre = su3Centre := rfl

namespace IsSU3BiFundamental
set_option linter.unusedVariables false

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {T : (Fin 2 → Fin 3) → B}

/-- Contracting a coefficient family against the central element in both colour indices
  multiplies it by `ω ^ 2`, since the central element is `ω` times the identity. -/
lemma sum_mul_prod_su3Centre (c : (Fin 2 → Fin 3) → ℂ) (a : Fin 2 → Fin 3) :
    ∑ d : Fin 2 → Fin 3, c d * ∏ i : Fin 2, (su3Centre.1 (a i) (d i))
      = su3Omega ^ 2 * c a := by
  rw [Finset.sum_eq_single a]
  · rw [Fin.prod_univ_two, su3Centre_apply, su3Centre_apply, if_pos rfl, if_pos rfl]
    ring
  · intro d _ hda
    have h : a 0 ≠ d 0 ∨ a 1 ≠ d 1 := by
      by_contra hc
      simp only [not_or, ne_eq, not_not] at hc
      exact hda (funext fun j => by fin_cases j <;> simp [hc.1, hc.2])
    rw [Fin.prod_univ_two, su3Centre_apply, su3Centre_apply]
    rcases h with h | h
    · rw [if_neg h, zero_mul, mul_zero]
    · rw [if_neg h, mul_zero, mul_zero]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

/-- There is no invariant pairing of two `su(3)` fundamental indices: a coefficient family
  left unchanged by contraction against two fundamental matrices is zero. Only the centre is
  used, and that is the sharp form of the obstruction, the number of indices, two, not being
  a multiple of the order three of the centre. -/
lemma eq_zero_of_sum_mul_prod (c : (Fin 2 → Fin 3) → ℂ)
    (hc : ∀ (U : specialUnitaryGroup (Fin 3) ℂ) (a : Fin 2 → Fin 3),
      ∑ d : Fin 2 → Fin 3, c d * ∏ i : Fin 2, (U.1 (a i) (d i)) = c a) :
    c = 0 := by
  funext a
  have h := hc su3Centre a
  rw [sum_mul_prod_su3Centre] at h
  have h0 : (su3Omega ^ 2 - 1) * c a = 0 := by
    rw [sub_mul, one_mul, h, sub_self]
  rcases mul_eq_zero.1 h0 with h1 | h1
  · exact absurd (sub_eq_zero.1 h1) su3Omega_pow_two_ne_one
  · exact h1

/-- The centre of the colour factor scales every component of a bi-fundamental family by
  `ω ^ 2`, one factor of `ω` for each of its two colour indices. -/
lemma repGauge_gaugeSU3Centre (hT : IsSU3BiFundamental B repGauge T) (l : Fin 2 → Fin 3) :
    repGauge gaugeSU3Centre (T l) = (su3Omega ^ 2) • T l := by
  rw [hT.repGauge_T gaugeSU3Centre l, Finset.sum_eq_single l]
  · rw [Fin.prod_univ_two, toSU3_gaugeSU3Centre, su3Centre_apply, su3Centre_apply,
      if_pos rfl, if_pos rfl, sq]
  · intro a _ hal
    have h : a 0 ≠ l 0 ∨ a 1 ≠ l 1 := by
      by_contra hc
      simp only [not_or, ne_eq, not_not] at hc
      exact hal (funext fun j => by fin_cases j <;> simp [hc.1, hc.2])
    rw [Fin.prod_univ_two, toSU3_gaugeSU3Centre, su3Centre_apply, su3Centre_apply]
    rcases h with h | h
    · rw [if_neg h, zero_mul, zero_smul]
    · rw [if_neg h, mul_zero, zero_smul]
  · intro hl
    exact absurd (Finset.mem_univ l) hl

/-- Every gauge invariant in the span of the components of a bi-fundamental family
  vanishes. The central element scales the whole span by `ω ^ 2`, an invariant element is
  fixed as well, and `ω ^ 2 - 1` is not zero. -/
lemma eq_zero_of_invariant (hT : IsSU3BiFundamental B repGauge T) {x : B}
    (hx : x ∈ hT.span) (hinv : ∀ g : GaugeGroupI, repGauge g x = x) : x = 0 := by
  obtain ⟨c, rfl⟩ := (hT.mem_span_iff x).1 hx
  have hscale : repGauge gaugeSU3Centre (∑ d, c d • T d) = (su3Omega ^ 2) • ∑ d, c d • T d := by
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [map_smul, hT.repGauge_gaugeSU3Centre d, smul_comm]
  rw [hinv gaugeSU3Centre] at hscale
  have h0 : (su3Omega ^ 2 - 1) • (∑ d, c d • T d) = 0 := by
    rw [sub_smul, one_smul, ← hscale, sub_self]
  have hne : su3Omega ^ 2 - 1 ≠ 0 := sub_ne_zero.2 su3Omega_pow_two_ne_one
  have := congrArg (fun y => (su3Omega ^ 2 - 1)⁻¹ • y) h0
  simpa [inv_smul_smul₀ hne] using this

end IsSU3BiFundamental

/-!

## C. The gauge weight decomposition of the span

The gauge torus is diagonal in the fundamental representation of the `SU(3)` factor, so the
three basis colour directions are already weight vectors, carrying the three colour weights
`colourWeight` of the triplet. A component `T d` therefore carries the definite weight
`wtWeight d`, the sum of the weights of its two indices, and the span of the components is
already the join of nine weight lines. Six weights occur: the three weights of the
symmetric `6` that are not shared, and the three weights of the `3̄`, each of which occurs
twice, once from the `6` and once from the `3̄`.

The stronger typeclass assumptions are forced: `GaugeWeightDecomposition` lives in an
algebra and records multiplicativity of the representation, neither of which
`IsSU3BiFundamental` needs, so both appear as extra arguments here.

-/

namespace IsSU3BiFundamental

set_option linter.unusedVariables false

/-!

## C.1. The gauge torus in the fundamental representation

-/

/-- The gauge weight carried by one `su(3)` fundamental index: colour only, the three
  colours carrying the three colour weights of the triplet. -/
def fundWeight (c : Fin 3) : GaugeWeight := ((colourWeight c).1, (colourWeight c).2, 0, 0)

/-- The gauge torus acts diagonally on a colour index, by the character of the weight of
  that index. Only the two colour generators act nontrivially. -/
lemma toSU3_gaugeTorusGen_apply (i : Fin 4) (a b : Fin 3) :
    (GaugeGroupI.toSU3 (gaugeTorusGen i)).1 a b
      = if a = b then (expI : ℂ) ^ GaugeWeight.coord (fundWeight a) i else 0 := by
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [gaugeTorusGen, GaugeGroupI.toSU3, su3ExpIOne, su3ExpITwo, fundWeight,
      colourWeight, expI_inv_eq_star]

/-- The gauge weight carried by a component of a bi-fundamental family: the sum of the
  weights of its two indices. -/
def wtWeight (l : Fin 2 → Fin 3) : GaugeWeight := fundWeight (l 0) + fundWeight (l 1)

/-!

## C.2. The components are weight vectors

-/

section Weights

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {T : (Fin 2 → Fin 3) → B}

/-- Every component of a bi-fundamental family is a simultaneous eigenvector of the gauge
  torus, at the character of the sum of the weights of its two indices. -/
lemma repGauge_gaugeTorusGen (hT : IsSU3BiFundamental B repGauge T) (l : Fin 2 → Fin 3)
    (i : Fin 4) :
    repGauge (gaugeTorusGen i) (T l)
      = ((expI : ℂ) ^ GaugeWeight.coord (wtWeight l) i) • T l := by
  rw [hT.repGauge_T (gaugeTorusGen i) l, Finset.sum_eq_single l]
  · congr 1
    rw [Fin.prod_univ_two, toSU3_gaugeTorusGen_apply, toSU3_gaugeTorusGen_apply,
      if_pos rfl, if_pos rfl, wtWeight, GaugeWeight.coord_add,
      zpow_add₀ expI_ne_zero]
  · intro a _ hal
    have h : a 0 ≠ l 0 ∨ a 1 ≠ l 1 := by
      by_contra hc
      simp only [not_or, ne_eq, not_not] at hc
      exact hal (funext fun j => by fin_cases j <;> simp [hc.1, hc.2])
    rw [Fin.prod_univ_two, toSU3_gaugeTorusGen_apply, toSU3_gaugeTorusGen_apply]
    rcases h with h | h
    · rw [if_neg h, zero_mul, zero_smul]
    · rw [if_neg h, mul_zero, zero_smul]
  · intro hl
    exact absurd (Finset.mem_univ l) hl

end Weights

/-!

## C.3. The decomposition

-/

section Decomposition

variable {B : Type*} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {T : (Fin 2 → Fin 3) → B}

variable (hT : IsSU3BiFundamental B repGauge T)

/-- The gauge weight decomposition of the span of a bi-fundamental `su(3)` family. The span
  is the join of the lines through the nine components, and each of those carries the sum of
  the weights of its two indices. -/
@[implicit_reducible]
noncomputable def gaugeWeightDecomposition (hT : IsSU3BiFundamental B repGauge T)
    (hmul : IsMulRep repGauge) : GaugeWeightDecomposition repGauge hT.span :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup hmul fun d : Fin 2 → Fin 3 =>
      GaugeWeightDecomposition.spanSingleton hmul (T d) (wtWeight d)
        (hT.repGauge_gaugeTorusGen d))
    _ rfl

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

/-- The gauge weights carried by a bi-fundamental `su(3)` family: the six weights of the
  tensor square of the `su(3)` fundamental, three of them carried twice. Every one of them
  has vanishing weak isospin and hypercharge, since the family carries colour only. -/
lemma gaugeWeightDecomposition_supp (hmul : IsMulRep repGauge) :
    (hT.gaugeWeightDecomposition hmul).supp
      = {((2, 0, 0, 0) : GaugeWeight), (-2, 2, 0, 0), (0, -2, 0, 0),
        (0, 1, 0, 0), (1, -1, 0, 0), (-1, 0, 0, 0)} := by
  rw [hT.gaugeWeightDecomposition_supp_eq hmul]
  decide

/-!

## C.4. The zero-weight piece is trivial

A gauge invariant built from `T` is fixed by the torus, so it lies in the zero-weight
piece, and here that piece is `⊥`. The weight of a component is the sum of two colour
weights of the triplet, and no such sum vanishes: the three colour weights are nonzero, and
no one of them is the negative of another, since the negatives of the triplet weights are
the weights of the antitriplet. That is the weight-theoretic form of the statement that
`3 ⊗ 3` contains no singlet, and it recovers the conclusion of section B for a
representation that carries a gauge weight decomposition.

-/

/-- No component of a bi-fundamental family carries vanishing gauge weight: a sum of two
  colour weights of the triplet is never zero. -/
lemma wtWeight_ne_zero (l : Fin 2 → Fin 3) : wtWeight l ≠ 0 := by
  revert l
  decide

/-- The zero-weight piece of the gauge weight decomposition is trivial, no component
  carrying vanishing colour weight. -/
lemma gaugeWeightDecomposition_piece_zero (hmul : IsMulRep repGauge) :
    (hT.gaugeWeightDecomposition hmul).piece 0 = ⊥ := by
  rw [hT.gaugeWeightDecomposition_piece hmul]
  refine le_antisymm (iSup_le fun d => ?_) bot_le
  rw [if_neg fun h => wtWeight_ne_zero d h.symm]

/-- The gauge torus alone already forbids an invariant: an element of the span fixed by
  the four torus generators is zero. Compared with `eq_zero_of_invariant` this asks less of
  the element, invariance under the torus rather than under the whole gauge group, and more
  of `B`, which has to carry a gauge weight decomposition. -/
lemma eq_zero_of_gaugeTorusGen_invariant (hmul : IsMulRep repGauge) {x : B}
    (hx : x ∈ hT.span) (hinv : ∀ i : Fin 4, repGauge (gaugeTorusGen i) x = x) : x = 0 := by
  have hmem : x ∈ (hT.gaugeWeightDecomposition hmul).piece 0 := by
    rw [GaugeWeightDecomposition.piece_eq_inf]
    refine ⟨hx, Submodule.mem_iInf _ |>.mpr fun i => ?_⟩
    rw [Module.End.mem_eigenspace_iff, GaugeWeight.zero_coord, zpow_zero, one_smul]
    exact hinv i
  rw [hT.gaugeWeightDecomposition_piece_zero hmul] at hmem
  exact (Submodule.mem_bot ℂ).mp hmem

end Decomposition

end IsSU3BiFundamental

end StandardModel
