/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeAlgebra.Basis
public import Physlib.Particles.StandardModel.GaugeAlgebra.RootDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.SU3PermDecomposition
public import Mathlib.Algebra.TrivSqZeroExt.Basic
/-!
# Gauge tensors carrying two `su(3)` adjoint indices

`IsSU3BiAdjoint B repGauge T` says that a family `T`, indexed by two `su(3)` adjoint
indices and valued in a module `B` carrying a representation of the gauge group
`GaugeGroupI`, transforms as a tensor `T^{a₁ a₂}` in the `su(3)` factor of the adjoint
representation.

This is the gauge analogue of `IsQuadLorentz`. The field strength of the gluons carries
one `su(3)` adjoint index, so a product of two field strengths carries two, and the
proposition here records how such a product transforms.

Section A gives the proposition and the span of its components, section B the trace
contraction, which is the natural gauge invariant built from two adjoint indices, and
section C the gauge weight decomposition of the span. Section D grades the zero-weight
piece of that decomposition by the cyclic colour rotation, which is what the gauge weight
alone cannot do, and section E upgrades that grading to the isotypic decomposition of the
whole Weyl group `S₃`, in which the trace contraction lands in the trivial isotype. Those
four sections are all built from the normaliser of the torus, and they stop two dimensions
short. Section F leaves the normaliser behind: a quarter turn in the `SU(2)` of the first
two colours carries a Cartan direction to a root direction, which no element of the
normaliser does, and that cuts the two lines section E leaves down to the one line through
the trace contraction. So `mem_span_and_invariant_iff` says the gauge invariants in the
span are exactly the multiples of the trace contraction, the single singlet of `8 ⊗ 8`.
Sections F.4 and F.5 shed the hypotheses that classification is stated under. The trivial
square-zero extension of a module is an algebra on which every representation acts by
algebra maps, so the classification needs no algebra structure and no multiplicativity at
all, and it then descends to the quotient by a gauge-stable submodule, which is
`mem_span_sup_invariant_iff`. The row orthonormality of the `su(3)` block of
`adjointMatrix` that section B rests on is proved where the matrix is defined, in
`GaugeAlgebra.Basis`.
-/

@[expose] public section

namespace StandardModel

open Matrix

/-!

## A. Bi-adjoint `su(3)` families and the span of their components

-/

/-- A family `T` of elements of `B`, indexed by two `su(3)` adjoint indices, transforms
  as a tensor `T^{a₁ a₂}` under the representation `repGauge` of the gauge group. -/
structure IsSU3BiAdjoint (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B)
    (T : (Fin 2 → Fin 8) → B) : Prop where
  repGauge_T : ∀ (g : GaugeGroupI) (l : Fin 2 → Fin 8),
    repGauge g (T l) = ∑ a : Fin 2 → Fin 8,
      (∏ i : Fin 2, ((GaugeAlgebra.adjointMatrix g (Sum.inl (a i))
        (Sum.inl (l i)) : ℝ) : ℂ)) • T a

TODO (lines := 56-60) "The `g` in this expression should only
  be the `SU(3)` part of this gauge group, and this hypothesis should
  only be about how that part acts. The same is true for
  every other result in this file."

namespace IsSU3BiAdjoint
set_option linter.unusedVariables false

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {T : (Fin 2 → Fin 8) → B}
  (hT : IsSU3BiAdjoint B repGauge T)

/-- The span of all the components. -/
def span (hT : IsSU3BiAdjoint B repGauge T) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

/-- An element of `B` lies in the span of the components of `T` precisely when it is a
  linear combination of them. -/
lemma mem_span_iff (x : B) :
    x ∈ hT.span ↔ ∃ (c : (Fin 2 → Fin 8) → ℂ), x = ∑ d, c d • T d := by
  constructor
  · intro hx
    rw [span] at hx
    refine Submodule.iSup_induction
      (motive := fun y => ∃ c : (Fin 2 → Fin 8) → ℂ, y = ∑ d, c d • T d)
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

/-!

## B. The trace contraction

-/

/-- A sum over families of two `su(3)` adjoint indices is a double sum. -/
lemma sum_pi_two {M : Type*} [AddCommMonoid M] (F : (Fin 2 → Fin 8) → M) :
    ∑ d : Fin 2 → Fin 8, F d = ∑ x : Fin 8, ∑ y : Fin 8, F ![x, y] := by
  rw [show (∑ d : Fin 2 → Fin 8, F d) = ∑ p : Fin 8 × Fin 8, F ![p.1, p.2] from
      Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin 8) _ _ fun d => by
        congr 1
        funext i
        fin_cases i <;> simp,
    Fintype.sum_prod_type]

/-- The trace contraction of a bi-adjoint family: the Kronecker contraction of the two
  `su(3)` adjoint indices. -/
def traceContraction (hT : IsSU3BiAdjoint B repGauge T) : B := ∑ a : Fin 8, T ![a, a]

/-- The trace contraction written as a sum over all pairs of adjoint indices weighted by
  the Kronecker delta. -/
lemma traceContraction_eq_sum (hT : IsSU3BiAdjoint B repGauge T) :
    hT.traceContraction
      = ∑ d : Fin 2 → Fin 8, (if d 0 = d 1 then (1 : ℂ) else 0) • T d := by
  rw [sum_pi_two]
  simp [traceContraction, ite_smul]

/-- The trace contraction lies in the span of the components. -/
lemma traceContraction_mem_span (hT : IsSU3BiAdjoint B repGauge T) :
    hT.traceContraction ∈ hT.span := by
  rw [traceContraction]
  exact sum_mem fun d _ =>
    Submodule.mem_iSup_of_mem _ (Submodule.mem_span_singleton_self _)

/-- The trace contraction of a bi-adjoint family is gauge invariant. -/
lemma repGauge_traceContraction (hT : IsSU3BiAdjoint B repGauge T) (g : GaugeGroupI) :
    repGauge g hT.traceContraction = hT.traceContraction := by
  have step : repGauge g hT.traceContraction
      = ∑ b : Fin 2 → Fin 8, (if b 0 = b 1 then (1 : ℂ) else 0) • T b := by
    show repGauge g (∑ c : Fin 8, T ![c, c]) = _
    rw [map_sum]
    have h1 : ∀ c : Fin 8, repGauge g (T ![c, c])
        = ∑ b : Fin 2 → Fin 8,
          ((GaugeAlgebra.adjointMatrix g (Sum.inl (b 0)) (Sum.inl c) *
            GaugeAlgebra.adjointMatrix g (Sum.inl (b 1)) (Sum.inl c) : ℝ) : ℂ) • T b := by
      intro c
      rw [hT.repGauge_T g ![c, c]]
      refine Finset.sum_congr rfl fun b _ => ?_
      congr 1
      simp [Fin.prod_univ_two]
    simp only [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    rw [← Complex.ofReal_sum, GaugeAlgebra.sum_adjointMatrix_inl_row_mul]
    simp [apply_ite]
  rw [step, ← hT.traceContraction_eq_sum]


end IsSU3BiAdjoint

/-!

## C. The gauge weight decomposition of the span

The Gell-Mann basis vectors are not eigenvectors of the gauge torus, so the components
`T d` do not carry a definite gauge weight. The eigenvectors appear only after passing to
the weight basis of the `su(3)` adjoint: for each of the three root directions the two
complex combinations `x₁ ± i x₂` of the paired Gell-Mann coordinates, and the two Cartan
directions as they stand. That is eight coordinate vectors, recorded in `wtCoeff`, with
weights `wtWeight`. The two Cartan directions are named in the gauge algebra itself, as
`GaugeAlgebra.su3CartanId`, since the Cartan directions of the whole algebra are
assembled from them; the root pairs are recorded here and matched with those of the whole
algebra in C.1.

With two adjoint indices a weight vector is a product of two of these, contracted against
`T` by `biVec`, and its weight is the sum of the two individual weights. There are sixty
four such products, they span the same subspace as the components, and joining their
lines one weight at a time gives `gaugeWeightDecomposition`.

The stronger typeclass assumptions are forced: `GaugeWeightDecomposition` lives in an
algebra and records multiplicativity of the representation, neither of which
`IsSU3BiAdjoint` needs, so both appear as extra arguments here.

-/

namespace IsSU3BiAdjoint

set_option linter.unusedVariables false

/-!

## C.1. The weight basis of the `su(3)` adjoint

-/

/-- The index type of the `su(3)` adjoint weight basis: three positive roots, three
  negative roots and two Cartan directions. -/
abbrev WeightIdx : Type := Fin 3 ⊕ Fin 3 ⊕ Fin 2

/-- The pairs of Gell-Mann indices making up the three root directions of `su(3)`. -/
def rootPair : Fin 3 → Fin 8 × Fin 8
  | 0 => (0, 1)
  | 1 => (3, 4)
  | 2 => (5, 6)

/-- The gauge weight of each `su(3)` root direction. -/
def rootWt : Fin 3 → GaugeWeight
  | 0 => (2, -1, 0, 0)
  | 1 => (1, 1, 0, 0)
  | 2 => (-1, 2, 0, 0)

/-- The root directions here are the `su(3)` root directions of the full gauge algebra. -/
lemma rootIdx_castSucc (r : Fin 3) :
    GaugeAlgebra.rootIdx r.castSucc
      = (Sum.inl (rootPair r).1, Sum.inl (rootPair r).2) := by
  fin_cases r <;> rfl

/-- The root weights here are the `su(3)` root weights of the full gauge algebra. -/
lemma rootWeight_castSucc (r : Fin 3) :
    GaugeAlgebra.rootWeight r.castSucc = rootWt r := by
  fin_cases r <;> rfl

/-- The Cartan directions here are the `su(3)` Cartan directions of the full gauge
  algebra. -/
lemma cartanIdx_castSucc (c : Fin 2) :
    GaugeAlgebra.cartanIdx c.castSucc.castSucc = Sum.inl (GaugeAlgebra.su3CartanId c) := by
  fin_cases c <;> rfl

/-- Every Gell-Mann index is either one of the two members of a root pair or a Cartan
  index. -/
lemma exists_rootPair_or_cartanId (a : Fin 8) :
    (∃ r : Fin 3, a = (rootPair r).1) ∨ (∃ r : Fin 3, a = (rootPair r).2)
      ∨ ∃ c : Fin 2, a = GaugeAlgebra.su3CartanId c := by
  revert a
  decide

TODO (lines := 195-235) "All of these should be in a more general file
  in the GaugeAlgebra section."

/-!

## C.2. The adjoint matrix of a torus generator in the weight basis

-/

/-- A standard coordinate functional evaluated on a standard basis vector. -/
lemma coord_stdBasis_apply (b a : Fin 8 ⊕ Fin 3 ⊕ Fin 1) :
    GaugeAlgebra.stdBasis.coord b (GaugeAlgebra.stdBasis a) = if a = b then 1 else 0 := by
  simp [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

/-- The entries of the adjoint matrix, read off the dual adjoint action of the inverse on
  the standard coordinate functionals. -/
lemma dualMap_coord_apply (g : GaugeGroupI) (a b : Fin 8 ⊕ Fin 3 ⊕ Fin 1) :
    (GaugeAlgebra.adjointMap g⁻¹).dualMap (GaugeAlgebra.stdBasis.coord b)
        (GaugeAlgebra.stdBasis a)
      = GaugeAlgebra.adjointMatrix g a b := by
  have h1 : GaugeAlgebra.adjointMap g⁻¹ (GaugeAlgebra.stdBasis a)
      = ∑ c, GaugeAlgebra.adjointMatrix g⁻¹ c a • GaugeAlgebra.stdBasis c :=
    GaugeAlgebra.adjoint_stdBasis g⁻¹ a
  rw [LinearMap.dualMap_apply, h1, map_sum]
  simp only [map_smul, smul_eq_mul, coord_stdBasis_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [GaugeAlgebra.adjointMatrix_inv_apply]

/-- The first column of a root pair: the torus rotates the two columns of the adjoint
  matrix belonging to a root direction into each other. -/
lemma adjointMatrix_rootPair_fst (i : Fin 4) (r : Fin 3) (a : Fin 8) :
    GaugeAlgebra.adjointMatrix (gaugeTorusGen i) (Sum.inl a) (Sum.inl (rootPair r).1)
      = ((expI : ℂ) ^ GaugeWeight.coord (rootWt r) i).re *
          (if a = (rootPair r).1 then 1 else 0)
        - ((expI : ℂ) ^ GaugeWeight.coord (rootWt r) i).im *
          (if a = (rootPair r).2 then 1 else 0) := by
  obtain ⟨p1, -⟩ := GaugeAlgebra.dualMap_pair_of_entry
    (GaugeAlgebra.coord_rootIdx_fst r.castSucc)
    (GaugeAlgebra.coord_rootIdx_snd r.castSucc)
    (GaugeAlgebra.rootEntry_adjointMap r.castSucc i)
  simp only [rootIdx_castSucc, rootWeight_castSucc] at p1
  have e := LinearMap.congr_fun p1 (GaugeAlgebra.stdBasis (Sum.inl a))
  rw [dualMap_coord_apply] at e
  rw [e]
  simp [Finsupp.single_apply]

/-- The second column of a root pair. -/
lemma adjointMatrix_rootPair_snd (i : Fin 4) (r : Fin 3) (a : Fin 8) :
    GaugeAlgebra.adjointMatrix (gaugeTorusGen i) (Sum.inl a) (Sum.inl (rootPair r).2)
      = ((expI : ℂ) ^ GaugeWeight.coord (rootWt r) i).im *
          (if a = (rootPair r).1 then 1 else 0)
        + ((expI : ℂ) ^ GaugeWeight.coord (rootWt r) i).re *
          (if a = (rootPair r).2 then 1 else 0) := by
  obtain ⟨-, p2⟩ := GaugeAlgebra.dualMap_pair_of_entry
    (GaugeAlgebra.coord_rootIdx_fst r.castSucc)
    (GaugeAlgebra.coord_rootIdx_snd r.castSucc)
    (GaugeAlgebra.rootEntry_adjointMap r.castSucc i)
  simp only [rootIdx_castSucc, rootWeight_castSucc] at p2
  have e := LinearMap.congr_fun p2 (GaugeAlgebra.stdBasis (Sum.inl a))
  rw [dualMap_coord_apply] at e
  rw [e]
  simp [Finsupp.single_apply]

/-- The torus fixes the Cartan columns of the adjoint matrix. -/
lemma adjointMatrix_cartanId (i : Fin 4) (c : Fin 2) (a : Fin 8) :
    GaugeAlgebra.adjointMatrix (gaugeTorusGen i) (Sum.inl a) (Sum.inl (GaugeAlgebra.su3CartanId c))
      = if a = GaugeAlgebra.su3CartanId c then 1 else 0 := by
  have p := GaugeAlgebra.dualMap_coord_cartanIdx c.castSucc.castSucc i
  simp only [cartanIdx_castSucc] at p
  have e := LinearMap.congr_fun p (GaugeAlgebra.stdBasis (Sum.inl a))
  rw [dualMap_coord_apply] at e
  rw [e]
  simp [Finsupp.single_apply]

/-!

## C.3. The weight vectors of one adjoint index

-/

/-- The coordinates of the `su(3)` adjoint weight basis in the Gell-Mann basis: for each
  root the two combinations `x₁ ± i x₂` of the paired coordinates, and for each Cartan
  direction the coordinate itself. -/
noncomputable def wtCoeff : WeightIdx → Fin 8 → ℂ
  | Sum.inl r, a => (if a = (rootPair r).1 then 1 else 0)
      + Complex.I * (if a = (rootPair r).2 then 1 else 0)
  | Sum.inr (Sum.inl r), a => (if a = (rootPair r).1 then 1 else 0)
      - Complex.I * (if a = (rootPair r).2 then 1 else 0)
  | Sum.inr (Sum.inr c), a => if a = GaugeAlgebra.su3CartanId c then 1 else 0

/-- The gauge weight carried by each `su(3)` adjoint weight vector. -/
def wtWeight : WeightIdx → GaugeWeight
  | Sum.inl r => rootWt r
  | Sum.inr (Sum.inl r) => -(rootWt r)
  | Sum.inr (Sum.inr _) => 0

/-- The coordinate vector of a single Gell-Mann direction. -/
def unitVec (a : Fin 8) : Fin 8 → ℂ := fun x => if x = a then 1 else 0

/-- The action of a gauge transformation on the coordinates of one `su(3)` adjoint
  index. -/
noncomputable def rowAct (g : GaugeGroupI) (c : Fin 8 → ℂ) : Fin 8 → ℂ := fun a =>
  ∑ x : Fin 8, ((GaugeAlgebra.adjointMatrix g (Sum.inl a) (Sum.inl x) : ℝ) : ℂ) * c x

/-- Collapsing a sum against the two Kronecker deltas of a root pair. -/
lemma sum_mul_pair (f : Fin 8 → ℂ) (b₁ b₂ : Fin 8) (s : ℂ) :
    ∑ x : Fin 8, f x * ((if x = b₁ then (1 : ℂ) else 0) + s * (if x = b₂ then 1 else 0))
      = f b₁ + s * f b₂ := by
  have h : ∀ x : Fin 8,
      f x * ((if x = b₁ then (1 : ℂ) else 0) + s * (if x = b₂ then 1 else 0))
        = (if x = b₁ then f x else 0) + (if x = b₂ then s * f x else 0) := by
    intro x
    split_ifs <;> ring
  simp only [h]
  simp [Finset.sum_add_distrib]

/-- The complex pair identity behind the positive root eigenvectors. -/
lemma pair_add_eq (z u v : ℂ) :
    (z.re : ℂ) * u - (z.im : ℂ) * v + Complex.I * ((z.im : ℂ) * u + (z.re : ℂ) * v)
      = z * (u + Complex.I * v) := by
  conv_rhs => rw [← Complex.re_add_im z]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The complex pair identity behind the negative root eigenvectors. -/
lemma pair_sub_eq (z u v : ℂ) :
    (z.re : ℂ) * u - (z.im : ℂ) * v - Complex.I * ((z.im : ℂ) * u + (z.re : ℂ) * v)
      = (starRingEnd ℂ) z * (u - Complex.I * v) := by
  rw [show (starRingEnd ℂ) z = (z.re : ℂ) - (z.im : ℂ) * Complex.I by
    rw [Complex.ext_iff]; simp]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Each weight vector of the `su(3)` adjoint is an eigenvector of every torus
  generator, at the character of its weight. -/
lemma rowAct_wtCoeff (i : Fin 4) (k : WeightIdx) :
    rowAct (gaugeTorusGen i) (wtCoeff k)
      = ((expI : ℂ) ^ GaugeWeight.coord (wtWeight k) i) • wtCoeff k := by
  funext a
  match k with
  | Sum.inl r =>
    have hw : ∀ x : Fin 8, wtCoeff (Sum.inl r) x
        = (if x = (rootPair r).1 then (1 : ℂ) else 0)
          + Complex.I * (if x = (rootPair r).2 then 1 else 0) := fun _ => rfl
    show ∑ x : Fin 8, _ * wtCoeff (Sum.inl r) x = _
    simp only [hw]
    rw [sum_mul_pair]
    simp only [adjointMatrix_rootPair_fst, adjointMatrix_rootPair_snd]
    simp only [apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_one, Complex.ofReal_zero,
      Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul]
    show _ = ((expI : ℂ) ^ GaugeWeight.coord (rootWt r) i) * _
    rw [pair_add_eq]
    rfl
  | Sum.inr (Sum.inl r) =>
    have hw : ∀ x : Fin 8, wtCoeff (Sum.inr (Sum.inl r)) x
        = (if x = (rootPair r).1 then (1 : ℂ) else 0)
          + (-Complex.I) * (if x = (rootPair r).2 then 1 else 0) := by
      intro x
      show (if x = (rootPair r).1 then (1 : ℂ) else 0)
          - Complex.I * (if x = (rootPair r).2 then 1 else 0) = _
      ring
    show ∑ x : Fin 8, _ * wtCoeff (Sum.inr (Sum.inl r)) x = _
    simp only [hw]
    rw [sum_mul_pair]
    simp only [adjointMatrix_rootPair_fst, adjointMatrix_rootPair_snd]
    simp only [apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_one, Complex.ofReal_zero,
      Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul]
    rw [show ((expI : ℂ) ^ GaugeWeight.coord (wtWeight (Sum.inr (Sum.inl r) : WeightIdx)) i)
        = (starRingEnd ℂ) ((expI : ℂ) ^ GaugeWeight.coord (rootWt r) i) from by
      rw [starRingEnd_expI_zpow]
      congr 1
      show GaugeWeight.coord (-(rootWt r)) i = _
      rw [GaugeWeight.coord_neg]]
    rw [show ∀ x y z : ℂ, x - y + -Complex.I * z = x - y - Complex.I * z from
      fun x y z => by ring]
    rw [pair_sub_eq]
    show _ = _ * wtCoeff (Sum.inr (Sum.inl r)) a
    rfl
  | Sum.inr (Sum.inr c) =>
    have hw : ∀ x : Fin 8, wtCoeff (Sum.inr (Sum.inr c)) x
        = if x = GaugeAlgebra.su3CartanId c then (1 : ℂ) else 0 := fun _ => rfl
    have hz : ((expI : ℂ) ^ GaugeWeight.coord
        (wtWeight (Sum.inr (Sum.inr c) : WeightIdx)) i) = 1 := by
      show ((expI : ℂ) ^ GaugeWeight.coord (0 : GaugeWeight) i) = 1
      simp
    show ∑ x : Fin 8, _ * wtCoeff (Sum.inr (Sum.inr c)) x = _
    rw [hz]
    simp only [hw, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, adjointMatrix_cartanId, one_smul]
    simp only [apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_one, Complex.ofReal_zero]

/-!

## C.4. The bi-adjoint weight vectors and their span

-/

section Decomposition

variable {B : Type*} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {T : (Fin 2 → Fin 8) → B}

/-- The element of `B` obtained by contracting the two `su(3)` adjoint indices of `T`
  against a pair of coordinate vectors. -/
noncomputable def biVec (hT : IsSU3BiAdjoint B repGauge T) (c₀ c₁ : Fin 8 → ℂ) : B :=
  ∑ d : Fin 2 → Fin 8, (c₀ (d 0) * c₁ (d 1)) • T d

variable (hT : IsSU3BiAdjoint B repGauge T)

/-- Contracting against a scaled coordinate vector on the left. -/
lemma biVec_smul_left (z : ℂ) (c₀ c₁ : Fin 8 → ℂ) :
    hT.biVec (z • c₀) c₁ = z • hT.biVec c₀ c₁ := by
  simp only [biVec, Finset.smul_sum, Pi.smul_apply, smul_eq_mul, smul_smul, mul_assoc]

/-- Contracting against a scaled coordinate vector on the right. -/
lemma biVec_smul_right (z : ℂ) (c₀ c₁ : Fin 8 → ℂ) :
    hT.biVec c₀ (z • c₁) = z • hT.biVec c₀ c₁ := by
  simp only [biVec, Finset.smul_sum, Pi.smul_apply, smul_eq_mul, smul_smul]
  exact Finset.sum_congr rfl fun d _ => by ring_nf

/-- Contracting against a sum of coordinate vectors on the left. -/
lemma biVec_add_left (c₀ c₀' c₁ : Fin 8 → ℂ) :
    hT.biVec (c₀ + c₀') c₁ = hT.biVec c₀ c₁ + hT.biVec c₀' c₁ := by
  simp only [biVec, Pi.add_apply, add_mul, add_smul, Finset.sum_add_distrib]

/-- Contracting against a difference of coordinate vectors on the left. -/
lemma biVec_sub_left (c₀ c₀' c₁ : Fin 8 → ℂ) :
    hT.biVec (c₀ - c₀') c₁ = hT.biVec c₀ c₁ - hT.biVec c₀' c₁ := by
  simp only [biVec, Pi.sub_apply, sub_mul, sub_smul, Finset.sum_sub_distrib]

/-- Contracting against a sum of coordinate vectors on the right. -/
lemma biVec_add_right (c₀ c₁ c₁' : Fin 8 → ℂ) :
    hT.biVec c₀ (c₁ + c₁') = hT.biVec c₀ c₁ + hT.biVec c₀ c₁' := by
  simp only [biVec, Pi.add_apply, mul_add, add_smul, Finset.sum_add_distrib]

/-- Contracting against a difference of coordinate vectors on the right. -/
lemma biVec_sub_right (c₀ c₁ c₁' : Fin 8 → ℂ) :
    hT.biVec c₀ (c₁ - c₁') = hT.biVec c₀ c₁ - hT.biVec c₀ c₁' := by
  simp only [biVec, Pi.sub_apply, mul_sub, sub_smul, Finset.sum_sub_distrib]

/-- Negating both coordinate vectors leaves the contraction unchanged: the two signs
  cancel against each other. -/
lemma biVec_neg_neg (c₀ c₁ : Fin 8 → ℂ) : hT.biVec (-c₀) (-c₁) = hT.biVec c₀ c₁ := by
  simp only [biVec, Pi.neg_apply, neg_mul_neg]

/-- Contracting against two single Gell-Mann directions returns a component of `T`. -/
lemma biVec_unitVec (a b : Fin 8) : hT.biVec (unitVec a) (unitVec b) = T ![a, b] := by
  rw [biVec, sum_pi_two]
  simp [unitVec, ite_smul]

/-- Every bi-adjoint weight vector transforms by the product of the two characters. -/
lemma repGauge_biVec (g : GaugeGroupI) (c₀ c₁ : Fin 8 → ℂ) :
    repGauge g (hT.biVec c₀ c₁) = hT.biVec (rowAct g c₀) (rowAct g c₁) := by
  have step : ∀ d : Fin 2 → Fin 8, repGauge g ((c₀ (d 0) * c₁ (d 1)) • T d)
      = ∑ a : Fin 2 → Fin 8,
        ((c₀ (d 0) * c₁ (d 1)) *
          (((GaugeAlgebra.adjointMatrix g (Sum.inl (a 0)) (Sum.inl (d 0)) : ℝ) : ℂ) *
            ((GaugeAlgebra.adjointMatrix g (Sum.inl (a 1)) (Sum.inl (d 1)) : ℝ) : ℂ)))
          • T a := by
    intro d
    rw [map_smul, hT.repGauge_T g d, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_smul, Fin.prod_univ_two]
  simp only [biVec, rowAct]
  rw [map_sum]
  simp only [step]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  rw [sum_pi_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

/-- **The bi-adjoint weight vectors are simultaneous eigenvectors of the gauge torus**,
  at the character of the sum of the two individual weights. -/
lemma repGauge_biVec_wtCoeff (k₀ k₁ : WeightIdx) (i : Fin 4) :
    repGauge (gaugeTorusGen i) (hT.biVec (wtCoeff k₀) (wtCoeff k₁))
      = ((expI : ℂ) ^ GaugeWeight.coord (wtWeight k₀ + wtWeight k₁) i)
        • hT.biVec (wtCoeff k₀) (wtCoeff k₁) := by
  rw [hT.repGauge_biVec, rowAct_wtCoeff, rowAct_wtCoeff, hT.biVec_smul_left,
    hT.biVec_smul_right, smul_smul, GaugeWeight.coord_add,
    zpow_add₀ expI_ne_zero]

/-- The join of the lines spanned by the bi-adjoint weight vectors. -/
noncomputable def wtSpan (hT : IsSU3BiAdjoint B repGauge T) : Submodule ℂ B :=
  ⨆ k : WeightIdx × WeightIdx, ℂ ∙ hT.biVec (wtCoeff k.1) (wtCoeff k.2)

/-- The Gell-Mann coordinate vector of the first member of a root pair, in the weight
  basis. -/
lemma unitVec_rootPair_fst (r : Fin 3) :
    unitVec (rootPair r).1
      = (2 : ℂ)⁻¹ • (wtCoeff (Sum.inl r) + wtCoeff (Sum.inr (Sum.inl r))) := by
  funext x
  simp only [unitVec, wtCoeff, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The Gell-Mann coordinate vector of the second member of a root pair, in the weight
  basis. -/
lemma unitVec_rootPair_snd (r : Fin 3) :
    unitVec (rootPair r).2
      = (-(Complex.I / 2)) • (wtCoeff (Sum.inl r) - wtCoeff (Sum.inr (Sum.inl r))) := by
  funext x
  simp only [unitVec, wtCoeff, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- A Cartan direction is already a weight vector. -/
lemma unitVec_cartanId (c : Fin 2) :
    unitVec (GaugeAlgebra.su3CartanId c) = wtCoeff (Sum.inr (Sum.inr c)) := rfl

/-- Contracting a weight vector against a single Gell-Mann direction stays in the join of
  the weight lines. -/
lemma biVec_wtCoeff_unitVec_mem (k : WeightIdx) (b : Fin 8) :
    hT.biVec (wtCoeff k) (unitVec b) ∈ hT.wtSpan := by
  have hgen : ∀ k' : WeightIdx, hT.biVec (wtCoeff k) (wtCoeff k') ∈ hT.wtSpan :=
    fun k' => Submodule.mem_iSup_of_mem (k, k') (Submodule.mem_span_singleton_self _)
  rcases exists_rootPair_or_cartanId b with ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨c, rfl⟩
  · rw [unitVec_rootPair_fst, hT.biVec_smul_right, hT.biVec_add_right]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ (hgen _) (hgen _))
  · rw [unitVec_rootPair_snd, hT.biVec_smul_right, hT.biVec_sub_right]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hgen _) (hgen _))
  · rw [unitVec_cartanId]
    exact hgen _

/-- Every component of `T` lies in the join of the weight lines. -/
lemma biVec_unitVec_mem (a b : Fin 8) :
    hT.biVec (unitVec a) (unitVec b) ∈ hT.wtSpan := by
  rcases exists_rootPair_or_cartanId a with ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨c, rfl⟩
  · rw [unitVec_rootPair_fst, hT.biVec_smul_left, hT.biVec_add_left]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _
      (hT.biVec_wtCoeff_unitVec_mem _ _) (hT.biVec_wtCoeff_unitVec_mem _ _))
  · rw [unitVec_rootPair_snd, hT.biVec_smul_left, hT.biVec_sub_left]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (hT.biVec_wtCoeff_unitVec_mem _ _) (hT.biVec_wtCoeff_unitVec_mem _ _))
  · rw [unitVec_cartanId]
    exact hT.biVec_wtCoeff_unitVec_mem _ _

/-- **The weight vectors span the components.** The change of basis from the Gell-Mann
  basis to the weight basis is invertible, so nothing is lost. -/
lemma span_eq_wtSpan : hT.span = hT.wtSpan := by
  refine le_antisymm (iSup_le fun d => (Submodule.span_singleton_le_iff_mem _ _).mpr ?_)
    (iSup_le fun k => (Submodule.span_singleton_le_iff_mem _ _).mpr ?_)
  · have hd : T d = T ![d 0, d 1] := by
      congr 1
      funext j
      fin_cases j <;> simp
    rw [hd, ← hT.biVec_unitVec]
    exact hT.biVec_unitVec_mem _ _
  · rw [span, biVec]
    exact sum_mem fun d _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem d (Submodule.mem_span_singleton_self _))

/-!

## C.5. The decomposition

-/

/-- **The gauge weight decomposition of the span of a bi-adjoint `su(3)` family.** The
  span is the join of the lines through the sixty four products of weight vectors, and
  each of those carries the sum of the two weights. -/
@[implicit_reducible]
noncomputable def gaugeWeightDecomposition (hT : IsSU3BiAdjoint B repGauge T)
    (hmul : IsMulRep repGauge) : GaugeWeightDecomposition repGauge hT.span :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup hmul fun k : WeightIdx × WeightIdx =>
      GaugeWeightDecomposition.spanSingleton hmul
        (hT.biVec (wtCoeff k.1) (wtCoeff k.2)) (wtWeight k.1 + wtWeight k.2)
        (hT.repGauge_biVec_wtCoeff k.1 k.2))
    _ hT.span_eq_wtSpan

/-- The pieces of the decomposition: the weight-`w` piece is the join of the lines through
  those products of weight vectors whose weights sum to `w`. -/
lemma gaugeWeightDecomposition_piece (hmul : IsMulRep repGauge) (w : GaugeWeight) :
    (hT.gaugeWeightDecomposition hmul).piece w
      = ⨆ k : WeightIdx × WeightIdx,
        (if w = wtWeight k.1 + wtWeight k.2 then
          ℂ ∙ hT.biVec (wtCoeff k.1) (wtCoeff k.2) else ⊥) := rfl

/-- The support of the decomposition, before evaluation. -/
lemma gaugeWeightDecomposition_supp_eq (hmul : IsMulRep repGauge) :
    (hT.gaugeWeightDecomposition hmul).supp
      = Finset.univ.biUnion fun k : WeightIdx × WeightIdx =>
        ({wtWeight k.1 + wtWeight k.2} : Finset GaugeWeight) := rfl

/-- **The gauge weights carried by a bi-adjoint `su(3)` family**: the nineteen weights of
  the tensor square of the `su(3)` adjoint. Every one of them has vanishing weak isospin
  and hypercharge, since the family carries colour only. -/
lemma gaugeWeightDecomposition_supp (hmul : IsMulRep repGauge) :
    (hT.gaugeWeightDecomposition hmul).supp
      = {((0, 0, 0, 0) : GaugeWeight), (2, -1, 0, 0), (1, 1, 0, 0), (-1, 2, 0, 0),
        (-2, 1, 0, 0), (-1, -1, 0, 0), (1, -2, 0, 0), (4, -2, 0, 0), (3, 0, 0, 0),
        (3, -3, 0, 0), (2, 2, 0, 0), (0, 3, 0, 0), (-2, 4, 0, 0), (-3, 3, 0, 0),
        (-4, 2, 0, 0), (-3, 0, 0, 0), (-2, -2, 0, 0), (0, -3, 0, 0), (2, -4, 0, 0)} := by
  rw [hT.gaugeWeightDecomposition_supp_eq hmul]
  decide +kernel

/-!

## C.6. The zero-weight piece

A gauge invariant built from `T` is fixed by the torus, so it lies in the zero-weight
piece, which makes that piece worth describing explicitly. A product of two weight vectors
has weight zero exactly when the two weights cancel: a root against its negative, in
either order, or any two Cartan directions. That is ten lines, the multiplicity of the
zero weight in the tensor square of the `su(3)` adjoint.

-/

/-- Two `su(3)` adjoint weight vectors have cancelling weights precisely when they are a
  root and its negative, in either order, or two Cartan directions. -/
lemma wtWeight_add_eq_zero_iff (k : WeightIdx × WeightIdx) :
    wtWeight k.1 + wtWeight k.2 = 0
      ↔ (∃ r : Fin 3, k = (Sum.inl r, Sum.inr (Sum.inl r)))
        ∨ (∃ r : Fin 3, k = (Sum.inr (Sum.inl r), Sum.inl r))
        ∨ ∃ c₀ c₁ : Fin 2, k = (Sum.inr (Sum.inr c₀), Sum.inr (Sum.inr c₁)) := by
  revert k
  decide

/-- The line through a product of two weight vectors whose weights cancel lies in the
  zero-weight piece. -/
lemma span_biVec_le_piece_zero (hmul : IsMulRep repGauge) {k₀ k₁ : WeightIdx}
    (h : wtWeight k₀ + wtWeight k₁ = 0) :
    ℂ ∙ hT.biVec (wtCoeff k₀) (wtCoeff k₁)
      ≤ (hT.gaugeWeightDecomposition hmul).piece 0 := by
  rw [hT.gaugeWeightDecomposition_piece hmul]
  exact le_iSup_of_le (k₀, k₁) (le_of_eq (if_pos h.symm).symm)

/-- The zero-weight piece of the gauge weight decomposition, explicitly: the join of the
  ten lines through the products of two weight vectors of opposite weight, one for each
  root against its negative in either order and one for each pair of Cartan directions. -/
lemma gaugeWeightDecomposition_piece_zero (hmul : IsMulRep repGauge) :
    (hT.gaugeWeightDecomposition hmul).piece 0
      = (⨆ r : Fin 3, ℂ ∙ hT.biVec (wtCoeff (Sum.inl r)) (wtCoeff (Sum.inr (Sum.inl r))))
        ⊔ (⨆ r : Fin 3, ℂ ∙ hT.biVec (wtCoeff (Sum.inr (Sum.inl r))) (wtCoeff (Sum.inl r)))
        ⊔ ⨆ c₀ : Fin 2, ⨆ c₁ : Fin 2, ℂ ∙ hT.biVec (wtCoeff (Sum.inr (Sum.inr c₀)))
            (wtCoeff (Sum.inr (Sum.inr c₁))) := by
  refine le_antisymm ?_ (sup_le (sup_le (iSup_le fun r => ?_) (iSup_le fun r => ?_))
    (iSup_le fun c₀ => iSup_le fun c₁ => ?_))
  · rw [hT.gaugeWeightDecomposition_piece hmul]
    refine iSup_le fun k => ?_
    split_ifs with hk
    · rcases (wtWeight_add_eq_zero_iff k).1 hk.symm with
        ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨c₀, c₁, rfl⟩
      · exact le_sup_of_le_left (le_sup_of_le_left (le_iSup_of_le r le_rfl))
      · exact le_sup_of_le_left (le_sup_of_le_right (le_iSup_of_le r le_rfl))
      · exact le_sup_of_le_right (le_iSup_of_le c₀ (le_iSup_of_le c₁ le_rfl))
    · exact bot_le
  · exact hT.span_biVec_le_piece_zero hmul (by simp [wtWeight])
  · exact hT.span_biVec_le_piece_zero hmul (by simp [wtWeight])
  · exact hT.span_biVec_le_piece_zero hmul (by simp [wtWeight])

/-- **The trace contraction lies in the zero-weight piece.** It is gauge invariant, so in
  particular the torus fixes it. -/
lemma traceContraction_mem_piece_zero (hmul : IsMulRep repGauge) :
    hT.traceContraction ∈ (hT.gaugeWeightDecomposition hmul).piece 0 :=
  GaugeWeightDecomposition.mem_zero_of_invariant _ hT.traceContraction_mem_span
    hT.repGauge_traceContraction

/-!

## C.7. The ten zero-weight products written out

Each of the ten lines of the previous section is the line through an explicit element of
`B`: for each of the three roots the raising vector paired with the matching lowering
vector and the same pair in the other order, and the four products of two Cartan
directions. Expanding the weight vectors in the Gell-Mann basis writes each of the ten as
a combination of the components of `T`, and the zero-weight piece is the span of the ten
element set they form.

-/

/-- The weight vector of a positive root, in terms of the two Gell-Mann coordinate
  directions of its root pair. -/
lemma wtCoeff_inl (r : Fin 3) :
    wtCoeff (Sum.inl r) = unitVec (rootPair r).1 + Complex.I • unitVec (rootPair r).2 := by
  funext x
  simp [wtCoeff, unitVec]

/-- The weight vector of a negative root, in terms of the two Gell-Mann coordinate
  directions of its root pair. -/
lemma wtCoeff_inr_inl (r : Fin 3) :
    wtCoeff (Sum.inr (Sum.inl r))
      = unitVec (rootPair r).1 - Complex.I • unitVec (rootPair r).2 := by
  funext x
  simp [wtCoeff, unitVec]

/-- The raising vector of a root paired with the matching lowering vector. -/
noncomputable def posNegProd (hT : IsSU3BiAdjoint B repGauge T) (r : Fin 3) : B :=
  hT.biVec (wtCoeff (Sum.inl r)) (wtCoeff (Sum.inr (Sum.inl r)))

/-- The lowering vector of a root paired with the matching raising vector. -/
noncomputable def negPosProd (hT : IsSU3BiAdjoint B repGauge T) (r : Fin 3) : B :=
  hT.biVec (wtCoeff (Sum.inr (Sum.inl r))) (wtCoeff (Sum.inl r))

/-- The product of two Cartan directions. -/
noncomputable def cartanProd (hT : IsSU3BiAdjoint B repGauge T) (c₀ c₁ : Fin 2) : B :=
  hT.biVec (wtCoeff (Sum.inr (Sum.inr c₀))) (wtCoeff (Sum.inr (Sum.inr c₁)))

/-- The raising-lowering product of a root, written out in the components of `T`. -/
lemma posNegProd_eq (r : Fin 3) :
    hT.posNegProd r
      = T ![(rootPair r).1, (rootPair r).1] + T ![(rootPair r).2, (rootPair r).2]
        + Complex.I • (T ![(rootPair r).2, (rootPair r).1]
          - T ![(rootPair r).1, (rootPair r).2]) := by
  rw [posNegProd, wtCoeff_inl, wtCoeff_inr_inl, hT.biVec_add_left, hT.biVec_smul_left,
    hT.biVec_sub_right, hT.biVec_sub_right, hT.biVec_smul_right, hT.biVec_smul_right,
    hT.biVec_unitVec, hT.biVec_unitVec, hT.biVec_unitVec, hT.biVec_unitVec, smul_sub,
    smul_smul, Complex.I_mul_I, neg_one_smul, smul_sub]
  abel

/-- The lowering-raising product of a root, written out in the components of `T`. -/
lemma negPosProd_eq (r : Fin 3) :
    hT.negPosProd r
      = T ![(rootPair r).1, (rootPair r).1] + T ![(rootPair r).2, (rootPair r).2]
        + Complex.I • (T ![(rootPair r).1, (rootPair r).2]
          - T ![(rootPair r).2, (rootPair r).1]) := by
  rw [negPosProd, wtCoeff_inl, wtCoeff_inr_inl, hT.biVec_sub_left, hT.biVec_smul_left,
    hT.biVec_add_right, hT.biVec_add_right, hT.biVec_smul_right, hT.biVec_smul_right,
    hT.biVec_unitVec, hT.biVec_unitVec, hT.biVec_unitVec, hT.biVec_unitVec, smul_add,
    smul_smul, Complex.I_mul_I, neg_one_smul, smul_sub]
  abel

/-- A product of two Cartan directions is a single component of `T`: the Cartan
  directions are already Gell-Mann coordinate directions. -/
lemma cartanProd_eq (c₀ c₁ : Fin 2) :
    hT.cartanProd c₀ c₁
      = T ![GaugeAlgebra.su3CartanId c₀, GaugeAlgebra.su3CartanId c₁] := by
  rw [cartanProd, ← unitVec_cartanId, ← unitVec_cartanId, hT.biVec_unitVec]

/-- The zero-weight piece of the gauge weight decomposition, fully explicitly: the span
  of the ten products of two weight vectors of opposite weight. -/
lemma gaugeWeightDecomposition_piece_zero_span (hmul : IsMulRep repGauge) :
    (hT.gaugeWeightDecomposition hmul).piece 0
      = Submodule.span ℂ
        {hT.posNegProd 0, hT.posNegProd 1, hT.posNegProd 2,
          hT.negPosProd 0, hT.negPosProd 1, hT.negPosProd 2,
          hT.cartanProd 0 0, hT.cartanProd 0 1, hT.cartanProd 1 0, hT.cartanProd 1 1} := by
  refine le_antisymm ?_ ?_
  · rw [hT.gaugeWeightDecomposition_piece_zero hmul]
    refine sup_le (sup_le (iSup_le fun r => ?_) (iSup_le fun r => ?_))
      (iSup_le fun c₀ => iSup_le fun c₁ => ?_)
    · refine (Submodule.span_singleton_le_iff_mem _ _).mpr (Submodule.subset_span ?_)
      fin_cases r <;> simp [posNegProd]
    · refine (Submodule.span_singleton_le_iff_mem _ _).mpr (Submodule.subset_span ?_)
      fin_cases r <;> simp [negPosProd]
    · refine (Submodule.span_singleton_le_iff_mem _ _).mpr (Submodule.subset_span ?_)
      fin_cases c₀ <;> fin_cases c₁ <;> simp [cartanProd]
  · rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    have hmem : ∀ k₀ k₁ : WeightIdx, wtWeight k₀ + wtWeight k₁ = 0 →
        hT.biVec (wtCoeff k₀) (wtCoeff k₁)
          ∈ (hT.gaugeWeightDecomposition hmul).piece 0 := fun k₀ k₁ h =>
      (Submodule.span_singleton_le_iff_mem _ _).mp (hT.span_biVec_le_piece_zero hmul h)
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hmem (Sum.inl 0) (Sum.inr (Sum.inl 0)) (by simp [wtWeight])
    · exact hmem (Sum.inl 1) (Sum.inr (Sum.inl 1)) (by simp [wtWeight])
    · exact hmem (Sum.inl 2) (Sum.inr (Sum.inl 2)) (by simp [wtWeight])
    · exact hmem (Sum.inr (Sum.inl 0)) (Sum.inl 0) (by simp [wtWeight])
    · exact hmem (Sum.inr (Sum.inl 1)) (Sum.inl 1) (by simp [wtWeight])
    · exact hmem (Sum.inr (Sum.inl 2)) (Sum.inl 2) (by simp [wtWeight])
    · exact hmem (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 0)) (by simp [wtWeight])
    · exact hmem (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 1)) (by simp [wtWeight])
    · exact hmem (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (by simp [wtWeight])
    · exact hmem (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 1)) (by simp [wtWeight])

/-!

## D. The `SU(3)` permutation decomposition of the zero-weight piece

The gauge weight cannot see inside its own zero-weight piece: the torus fixes all ten of
the products above. The cyclic colour rotation `gaugeSU3Perm` does see inside it. It
normalises the torus and sends each weight to another weight, fixing the weight zero, so
it acts on the zero-weight piece, and `SU3PermDecomposition` grades that action by the
cube roots of unity.

Sections D.1 and D.2 compute the action, first on the Gell-Mann coordinate directions and
then on the weight vectors: the six root directions are permuted in two three-cycles,
while the two Cartan directions are rotated into each other and are diagonalised by the
combinations `x₂ ∓ i x₇`. Section D.3 transfers this to the ten products, section D.4
grades a three-cycle by the cube roots of unity, and section D.5 assembles the
decomposition.

This grading is a sieve, not a classification: `SU3PermDecomposition` records that grade
zero is necessary for gauge invariance but proves no converse. It is also only half of the
Weyl group of `SU(3)`. Section E adds the other half, and the decomposition built here is
the scaffolding that the isotypic decomposition there is assembled from, rather than the
end of the story.

## D.1. The cyclic colour rotation on the Gell-Mann directions

Conjugation by the cyclic matrix permutes the matrix units, hence the Gell-Mann matrices,
up to signs; only the two diagonal ones are mixed, by a rotation through `2 π / 3`.

-/

/-- The star of the cyclic colour matrix is the permutation matrix of the inverse
  three-cycle. -/
lemma star_su3PermMatrix :
    star !![(0 : ℂ), 0, 1; 1, 0, 0; 0, 1, 0] = !![(0 : ℂ), 1, 0; 0, 0, 1; 1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- An entry of the `su(3)` block of an adjoint matrix is a Gell-Mann coordinate of the
  conjugated Gell-Mann matrix. -/
lemma adjointMatrix_inl_inl_eq_gellMannCoeff (g : GaugeGroupI) (a b : Fin 8) :
    GaugeAlgebra.adjointMatrix g (Sum.inl a) (Sum.inl b)
      = gellMannCoeff (g.toSU3.1 * gellMannMatrix b * star g.toSU3.1) a := by
  have hmem := GaugeAlgebra.conj_mem g.toSU3.2.1
    (gellMannMatrix_selfAdjoint b) (gellMannMatrix_trace b)
  rw [GaugeAlgebra.adjointMatrix_inl_inl, gellMannCoeff_eq_trace hmem.1 hmem.2]

/-- The conjugate of each Gell-Mann matrix by the cyclic colour rotation. -/
noncomputable def permGellMann : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ
  | 0 => !![0, 0, 0; 0, 0, 1; 0, 1, 0]
  | 1 => !![0, 0, 0; 0, 0, -Complex.I; 0, Complex.I, 0]
  | 2 => !![0, 0, 0; 0, 1, 0; 0, 0, -1]
  | 3 => !![0, 1, 0; 1, 0, 0; 0, 0, 0]
  | 4 => !![0, Complex.I, 0; -Complex.I, 0, 0; 0, 0, 0]
  | 5 => !![0, 0, 1; 0, 0, 0; 1, 0, 0]
  | 6 => !![0, 0, Complex.I; 0, 0, 0; -Complex.I, 0, 0]
  | 7 => !![((-2 * (Real.sqrt 3)⁻¹ : ℝ) : ℂ), 0, 0;
            0, (((Real.sqrt 3)⁻¹ : ℝ) : ℂ), 0;
            0, 0, (((Real.sqrt 3)⁻¹ : ℝ) : ℂ)]

/-- Conjugating a Gell-Mann matrix by the cyclic colour rotation. -/
lemma conj_gellMannMatrix_gaugeSU3Perm (b : Fin 8) :
    gaugeSU3Perm.toSU3.1 * gellMannMatrix b * star gaugeSU3Perm.toSU3.1 = permGellMann b := by
  rw [show gaugeSU3Perm.toSU3.1 = !![(0 : ℂ), 0, 1; 1, 0, 0; 0, 1, 0] from rfl,
    star_su3PermMatrix]
  fin_cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [permGellMann, gellMannMatrix_zero, gellMannMatrix_one, gellMannMatrix_two,
      gellMannMatrix_three, gellMannMatrix_four, gellMannMatrix_five, gellMannMatrix_six,
      gellMannMatrix_seven, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

/-- The coordinates of the image of each Gell-Mann direction under the cyclic colour
  rotation: the six directions of the root pairs are permuted up to sign, and the two
  Cartan directions are rotated into each other. -/
noncomputable def permCol : Fin 8 → Fin 8 → ℂ
  | 0 => unitVec 5
  | 1 => unitVec 6
  | 2 => -(2 : ℂ)⁻¹ • unitVec 2 + (((Real.sqrt 3 : ℝ) : ℂ) / 2) • unitVec 7
  | 3 => unitVec 0
  | 4 => -unitVec 1
  | 5 => unitVec 3
  | 6 => -unitVec 4
  | 7 => -((((Real.sqrt 3 : ℝ) : ℂ) / 2) • unitVec 2) - (2 : ℂ)⁻¹ • unitVec 7

/-- The row action on a Gell-Mann coordinate direction is a column of the adjoint
  matrix. -/
lemma rowAct_unitVec (g : GaugeGroupI) (b a : Fin 8) :
    rowAct g (unitVec b) a
      = ((GaugeAlgebra.adjointMatrix g (Sum.inl a) (Sum.inl b) : ℝ) : ℂ) := by
  simp [rowAct, unitVec, mul_ite]

/-- The cyclic colour rotation on the Gell-Mann coordinate directions. -/
lemma rowAct_gaugeSU3Perm_unitVec (b : Fin 8) :
    rowAct gaugeSU3Perm (unitVec b) = permCol b := by
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) = 3 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  funext a
  rw [rowAct_unitVec, adjointMatrix_inl_inl_eq_gellMannCoeff, conj_gellMannMatrix_gaugeSU3Perm]
  fin_cases b <;> fin_cases a <;> simp [permGellMann, gellMannCoeff, permCol, unitVec]
  all_goals first
    | ring1
    | linear_combination (-(1 : ℂ) / 6) * h3

/-!

## D.2. The cyclic colour rotation on the weight vectors

The six root weight vectors are permuted in two three-cycles, `wtCycle j` for `j = 0, 1`.
The two Cartan weight vectors are not permuted but rotated, and the combinations
`x₂ ∓ i x₇` recorded in `cartanVec` diagonalise the rotation, at the eigenvalues `ω` and
`ω ^ 2`.

-/

/-- The row action is additive in the coordinate vector. -/
lemma rowAct_add (g : GaugeGroupI) (c c' : Fin 8 → ℂ) :
    rowAct g (c + c') = rowAct g c + rowAct g c' := by
  funext a
  simp only [rowAct, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The row action is additive on differences of coordinate vectors. -/
lemma rowAct_sub (g : GaugeGroupI) (c c' : Fin 8 → ℂ) :
    rowAct g (c - c') = rowAct g c - rowAct g c' := by
  funext a
  simp only [rowAct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- The row action is homogeneous in the coordinate vector. -/
lemma rowAct_smul (g : GaugeGroupI) (z : ℂ) (c : Fin 8 → ℂ) :
    rowAct g (z • c) = z • rowAct g c := by
  funext a
  simp only [rowAct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- The six root weight indices arranged in the two three-cycles along which the cyclic
  colour rotation moves them. -/
def wtCycle : Fin 2 → Fin 3 → WeightIdx
  | 0, 0 => Sum.inl 0
  | 0, 1 => Sum.inl 2
  | 0, 2 => Sum.inr (Sum.inl 1)
  | 1, 0 => Sum.inl 1
  | 1, 1 => Sum.inr (Sum.inl 0)
  | 1, 2 => Sum.inr (Sum.inl 2)

/-- The cyclic colour rotation moves the root weight vectors one step along their
  cycle. -/
lemma rowAct_gaugeSU3Perm_wtCoeff (j : Fin 2) (i : Fin 3) :
    rowAct gaugeSU3Perm (wtCoeff (wtCycle j i)) = wtCoeff (wtCycle j (i + 1)) := by
  fin_cases j <;> fin_cases i <;>
    simp [wtCycle, wtCoeff_inl, wtCoeff_inr_inl, rootPair, rowAct_add, rowAct_sub,
      rowAct_smul, rowAct_gaugeSU3Perm_unitVec, permCol]
  all_goals module

/-- The two eigenvectors of the cyclic colour rotation in the Cartan plane. -/
noncomputable def cartanVec : Fin 2 → Fin 8 → ℂ
  | 0 => wtCoeff (Sum.inr (Sum.inr 0)) - Complex.I • wtCoeff (Sum.inr (Sum.inr 1))
  | 1 => wtCoeff (Sum.inr (Sum.inr 0)) + Complex.I • wtCoeff (Sum.inr (Sum.inr 1))

/-- The grade of each Cartan eigenvector. -/
def cartanGrade : Fin 2 → ZMod 3
  | 0 => 1
  | 1 => 2

/-- The cube root of unity `ω = exp (2 π i / 3)`, written out. -/
lemma su3Omega_eq : su3Omega = -2⁻¹ + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I := by
  have h : (2 * (Real.pi : ℂ) * Complex.I / 3)
      = ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [su3Omega, h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
    Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast
  ring

/-- The square of `ω`, written out. -/
lemma su3Omega_sq : su3Omega ^ 2 = -2⁻¹ - ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I := by
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  rw [su3Omega_eq]
  push_cast
  linear_combination (((Real.sqrt 3 : ℝ) : ℂ) ^ 2 / 4) * Complex.I_sq + (-(1 : ℂ) / 4) * h3

/-- The grade-one sign, written out. -/
lemma su3PermSign_one_eq :
    su3PermSign 1 = -2⁻¹ + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [su3PermSign_one, su3Omega_eq]

/-- The grade-two sign, written out. -/
lemma su3PermSign_two_eq :
    su3PermSign 2 = -2⁻¹ - ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [su3PermSign_two, su3Omega_sq]

/-- The cyclic colour rotation scales each Cartan eigenvector by the cube root of unity
  of its grade. -/
lemma rowAct_gaugeSU3Perm_cartanVec (c : Fin 2) :
    rowAct gaugeSU3Perm (cartanVec c) = su3PermSign (cartanGrade c) • cartanVec c := by
  fin_cases c <;>
    simp only [cartanVec, cartanGrade, ← unitVec_cartanId, GaugeAlgebra.su3CartanId,
      rowAct_sub, rowAct_add, rowAct_smul, rowAct_gaugeSU3Perm_unitVec, permCol,
      su3PermSign_one_eq, su3PermSign_two_eq] <;>
    match_scalars
  all_goals ring_nf
  all_goals try simp only [Complex.I_sq]
  all_goals ring1

/-- The first Cartan weight vector in terms of the two eigenvectors. -/
lemma wtCoeff_cartan_zero :
    wtCoeff (Sum.inr (Sum.inr 0)) = (2 : ℂ)⁻¹ • (cartanVec 0 + cartanVec 1) := by
  simp only [cartanVec]
  module

/-- The second Cartan weight vector in terms of the two eigenvectors. -/
lemma wtCoeff_cartan_one :
    wtCoeff (Sum.inr (Sum.inr 1)) = (Complex.I / 2) • (cartanVec 0 - cartanVec 1) := by
  simp only [cartanVec]
  match_scalars
  all_goals first
    | ring1
    | linear_combination Complex.I_sq

/-!

## D.3. The ten zero-weight products under the rotation

Pairing each weight vector of a cycle with the opposite weight vector turns the two
three-cycles of weight vectors into two three-cycles of zero-weight products, `prodCycle 0`
and `prodCycle 1`. The four Cartan products are not permuted: written in the eigenbasis
`cartanVec` they are scaled, by the product of the two eigenvalues.

-/

/-- The six root products of weight zero, arranged in the two three-cycles along which the
  cyclic colour rotation moves them. -/
noncomputable def prodCycle (hT : IsSU3BiAdjoint B repGauge T) : Fin 2 → Fin 3 → B
  | 0, i => hT.biVec (wtCoeff (wtCycle 0 i)) (wtCoeff (wtCycle 1 (i + 1)))
  | 1, i => hT.biVec (wtCoeff (wtCycle 1 (i + 1))) (wtCoeff (wtCycle 0 i))

/-- The forward cycle starts at the first raising-lowering product. -/
lemma prodCycle_zero_zero : hT.prodCycle 0 0 = hT.posNegProd 0 := rfl

/-- The forward cycle continues with the third raising-lowering product. -/
lemma prodCycle_zero_one : hT.prodCycle 0 1 = hT.posNegProd 2 := rfl

/-- The forward cycle closes on the second lowering-raising product. -/
lemma prodCycle_zero_two : hT.prodCycle 0 2 = hT.negPosProd 1 := rfl

/-- The reverse cycle starts at the first lowering-raising product. -/
lemma prodCycle_one_zero : hT.prodCycle 1 0 = hT.negPosProd 0 := rfl

/-- The reverse cycle continues with the third lowering-raising product. -/
lemma prodCycle_one_one : hT.prodCycle 1 1 = hT.negPosProd 2 := rfl

/-- The reverse cycle closes on the second raising-lowering product. -/
lemma prodCycle_one_two : hT.prodCycle 1 2 = hT.posNegProd 1 := rfl

/-- The cyclic colour rotation moves each root product one step along its cycle. -/
lemma repGauge_gaugeSU3Perm_prodCycle (j : Fin 2) (i : Fin 3) :
    repGauge gaugeSU3Perm (hT.prodCycle j i) = hT.prodCycle j (i + 1) := by
  fin_cases j <;>
    simp only [prodCycle, hT.repGauge_biVec, rowAct_gaugeSU3Perm_wtCoeff]

/-- The two weight vectors of a root product carry opposite weights. -/
lemma wtWeight_wtCycle_add (i : Fin 3) :
    wtWeight (wtCycle 0 i) + wtWeight (wtCycle 1 (i + 1)) = 0 := by
  revert i
  decide

/-- The same pair of weight vectors in the other order. -/
lemma wtWeight_wtCycle_add' (i : Fin 3) :
    wtWeight (wtCycle 1 (i + 1)) + wtWeight (wtCycle 0 i) = 0 := by
  revert i
  decide

/-- Every root product lies in the zero-weight piece. -/
lemma prodCycle_mem_piece_zero (hmul : IsMulRep repGauge) (j : Fin 2) (i : Fin 3) :
    hT.prodCycle j i ∈ (hT.gaugeWeightDecomposition hmul).piece 0 := by
  fin_cases j
  · exact (Submodule.span_singleton_le_iff_mem _ _).mp
      (hT.span_biVec_le_piece_zero hmul (wtWeight_wtCycle_add i))
  · exact (Submodule.span_singleton_le_iff_mem _ _).mp
      (hT.span_biVec_le_piece_zero hmul (wtWeight_wtCycle_add' i))

/-- The products of two Cartan eigenvectors. -/
noncomputable def cartanEigenProd (hT : IsSU3BiAdjoint B repGauge T) (a b : Fin 2) : B :=
  hT.biVec (cartanVec a) (cartanVec b)

/-- A product of two Cartan eigenvectors is scaled by the cube root of unity of the sum of
  the two grades. -/
lemma repGauge_gaugeSU3Perm_cartanEigenProd (a b : Fin 2) :
    repGauge gaugeSU3Perm (hT.cartanEigenProd a b)
      = su3PermSign (cartanGrade a + cartanGrade b) • hT.cartanEigenProd a b := by
  rw [cartanEigenProd, hT.repGauge_biVec, rowAct_gaugeSU3Perm_cartanVec,
    rowAct_gaugeSU3Perm_cartanVec, hT.biVec_smul_left, hT.biVec_smul_right, smul_smul,
    su3PermSign_add]

/-- Every product of two Cartan eigenvectors lies in the zero-weight piece. -/
lemma cartanEigenProd_mem_piece_zero (hmul : IsMulRep repGauge) (a b : Fin 2) :
    hT.cartanEigenProd a b ∈ (hT.gaugeWeightDecomposition hmul).piece 0 := by
  have hbase : ∀ c₀ c₁ : Fin 2, hT.biVec (wtCoeff (Sum.inr (Sum.inr c₀)))
      (wtCoeff (Sum.inr (Sum.inr c₁))) ∈ (hT.gaugeWeightDecomposition hmul).piece 0 :=
    fun c₀ c₁ => (Submodule.span_singleton_le_iff_mem _ _).mp
      (hT.span_biVec_le_piece_zero hmul (by simp [wtWeight]))
  have hc : ∀ c : Fin 2, c = 0 ∨ c = 1 := by decide
  rcases hc a with rfl | rfl <;> rcases hc b with rfl | rfl <;>
    simp only [cartanEigenProd, cartanVec, hT.biVec_add_left, hT.biVec_sub_left,
      hT.biVec_smul_left, hT.biVec_add_right, hT.biVec_sub_right, hT.biVec_smul_right]
  all_goals
    repeat' first
      | exact hbase _ _
      | apply add_mem
      | apply sub_mem
      | apply Submodule.smul_mem

/-!

## D.4. The graded combinations of a three-cycle

A three-cycle `x` of elements of `B` has three graded combinations, one for each cube root
of unity: `cycleEigen x k` is scaled by `ω ^ k`, and the three of them span the same
subspace as the cycle, by the inverse of the Vandermonde matrix of the cube roots of unity.

-/

/-- The grade `k` combination of a three-cycle. -/
noncomputable def cycleEigen (x : Fin 3 → B) (k : ZMod 3) : B :=
  x 0 + su3PermSign (2 * k) • x 1 + su3PermSign k • x 2

/-- The grade zero combination of a three-cycle is the plain sum of its three members:
  the character is trivial there. -/
lemma cycleEigen_zero_eq (x : Fin 3 → B) : cycleEigen x 0 = x 0 + x 1 + x 2 := by
  simp [cycleEigen, su3PermSign_zero]

/-- The cube roots of unity sum to zero. -/
lemma su3Omega_add : 1 + su3Omega + su3Omega ^ 2 = 0 := by
  rw [su3Omega_sq, su3Omega_eq]
  ring

/-- The cyclic element scales the grade `k` combination of a three-cycle by `ω ^ k`. -/
lemma repGauge_cycleEigen (x : Fin 3 → B)
    (hx : ∀ i : Fin 3, repGauge gaugeSU3Perm (x i) = x (i + 1)) (k : ZMod 3) :
    repGauge gaugeSU3Perm (cycleEigen x k) = su3PermSign k • cycleEigen x k := by
  have h3k : k + 2 * k = 0 := by
    have h : (3 : ZMod 3) * k = 0 := by
      rw [show (3 : ZMod 3) = 0 from rfl, zero_mul]
    linear_combination h
  have h2k : k + k = 2 * k := by ring
  rw [cycleEigen, map_add, map_add, map_smul, map_smul, hx 0, hx 1, hx 2,
    show (0 : Fin 3) + 1 = 1 from rfl, show (1 : Fin 3) + 1 = 2 from rfl,
    show (2 : Fin 3) + 1 = 0 from rfl, smul_add, smul_add, smul_smul, smul_smul,
    ← su3PermSign_add, ← su3PermSign_add, h3k, h2k, su3PermSign_zero, one_smul]
  abel

/-- The three graded combinations sum to three times the first member of the cycle. -/
lemma cycleEigen_sum_zero (x : Fin 3 → B) :
    cycleEigen x 0 + cycleEigen x 1 + cycleEigen x 2 = (3 : ℂ) • x 0 := by
  simp only [cycleEigen, show (2 : ZMod 3) * 0 = 0 from rfl, show (2 : ZMod 3) * 1 = 2 from rfl,
    show (2 : ZMod 3) * 2 = 1 from rfl, su3PermSign_zero, su3PermSign_one, su3PermSign_two]
  match_scalars
  all_goals first
    | ring1
    | linear_combination su3Omega_add

/-- Weighting the graded combinations by the cube roots of unity picks out the second
  member of the cycle. -/
lemma cycleEigen_sum_one (x : Fin 3 → B) :
    cycleEigen x 0 + su3Omega • cycleEigen x 1 + su3Omega ^ 2 • cycleEigen x 2
      = (3 : ℂ) • x 1 := by
  simp only [cycleEigen, show (2 : ZMod 3) * 0 = 0 from rfl, show (2 : ZMod 3) * 1 = 2 from rfl,
    show (2 : ZMod 3) * 2 = 1 from rfl, su3PermSign_zero, su3PermSign_one, su3PermSign_two]
  match_scalars
  all_goals first
    | ring1
    | linear_combination su3Omega_add
    | linear_combination (2 : ℂ) * su3Omega_pow_three
    | linear_combination su3Omega_add + su3Omega * su3Omega_pow_three

/-- Weighting by the other cube root of unity picks out the third member of the cycle. -/
lemma cycleEigen_sum_two (x : Fin 3 → B) :
    cycleEigen x 0 + su3Omega ^ 2 • cycleEigen x 1 + su3Omega • cycleEigen x 2
      = (3 : ℂ) • x 2 := by
  simp only [cycleEigen, show (2 : ZMod 3) * 0 = 0 from rfl, show (2 : ZMod 3) * 1 = 2 from rfl,
    show (2 : ZMod 3) * 2 = 1 from rfl, su3PermSign_zero, su3PermSign_one, su3PermSign_two]
  match_scalars
  all_goals first
    | ring1
    | linear_combination su3Omega_add
    | linear_combination (2 : ℂ) * su3Omega_pow_three
    | linear_combination su3Omega_add + su3Omega * su3Omega_pow_three

/-- Every member of a three-cycle lies in the join of the lines through its three graded
  combinations. -/
lemma cycle_mem_iSup (x : Fin 3 → B) (i : Fin 3) :
    x i ∈ ⨆ k : ZMod 3, ℂ ∙ cycleEigen x k := by
  have hmem : ∀ k : ZMod 3, cycleEigen x k ∈ ⨆ k : ZMod 3, ℂ ∙ cycleEigen x k :=
    fun k => Submodule.mem_iSup_of_mem k (Submodule.mem_span_singleton_self _)
  have hcomb : ∀ z₀ z₁ z₂ : ℂ,
      z₀ • cycleEigen x 0 + z₁ • cycleEigen x 1 + z₂ • cycleEigen x 2
        ∈ ⨆ k : ZMod 3, ℂ ∙ cycleEigen x k := fun z₀ z₁ z₂ =>
    add_mem (add_mem (Submodule.smul_mem _ _ (hmem 0)) (Submodule.smul_mem _ _ (hmem 1)))
      (Submodule.smul_mem _ _ (hmem 2))
  have hthree : ∀ y : B, (3 : ℂ) • y ∈ (⨆ k : ZMod 3, ℂ ∙ cycleEigen x k) →
      y ∈ ⨆ k : ZMod 3, ℂ ∙ cycleEigen x k := by
    intro y hy
    have h := Submodule.smul_mem _ ((3 : ℂ)⁻¹) hy
    rwa [smul_smul, inv_mul_cancel₀ (by norm_num : (3 : ℂ) ≠ 0), one_smul] at h
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
    revert i
    decide
  rcases hi with rfl | rfl | rfl
  · refine hthree _ ?_
    rw [← cycleEigen_sum_zero x]
    simpa using hcomb 1 1 1
  · refine hthree _ ?_
    rw [← cycleEigen_sum_one x]
    simpa using hcomb 1 su3Omega (su3Omega ^ 2)
  · refine hthree _ ?_
    rw [← cycleEigen_sum_two x]
    simpa using hcomb 1 (su3Omega ^ 2) su3Omega

/-!

## D.5. The decomposition

The grade `k` piece holds one line from each of the two cycles of root products, together
with those products of Cartan eigenvectors whose two grades sum to `k`. That is four of the
ten lines in grade zero and three in each of the grades one and two.

-/

/-- The grade `k` piece of the `SU(3)` permutation decomposition of the zero-weight
  piece. -/
noncomputable def zeroPiece (hT : IsSU3BiAdjoint B repGauge T) (k : ZMod 3) : Submodule ℂ B :=
  ℂ ∙ cycleEigen (hT.prodCycle 0) k ⊔ ℂ ∙ cycleEigen (hT.prodCycle 1) k
    ⊔ ⨆ (a : Fin 2) (b : Fin 2) (_ : cartanGrade a + cartanGrade b = k),
      ℂ ∙ hT.cartanEigenProd a b

/-- Each graded piece is of pure sign under the cyclic colour rotation. -/
lemma zeroPiece_le_eigenspace (k : ZMod 3) :
    hT.zeroPiece k ≤ Module.End.eigenspace (repGauge gaugeSU3Perm) (su3PermSign k) := by
  refine sup_le (sup_le ?_ ?_) (iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Module.End.mem_eigenspace_iff.mpr
      (repGauge_cycleEigen _ (hT.repGauge_gaugeSU3Perm_prodCycle 0) k)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Module.End.mem_eigenspace_iff.mpr
      (repGauge_cycleEigen _ (hT.repGauge_gaugeSU3Perm_prodCycle 1) k)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    refine Module.End.mem_eigenspace_iff.mpr ?_
    rw [hT.repGauge_gaugeSU3Perm_cartanEigenProd, hab]

/-- Every product of two Cartan directions lies in the join of the graded pieces. -/
lemma cartanProd_mem_iSup_zeroPiece (c₀ c₁ : Fin 2) :
    hT.cartanProd c₀ c₁ ∈ ⨆ k : ZMod 3, hT.zeroPiece k := by
  have hbase : ∀ a b : Fin 2,
      hT.biVec (cartanVec a) (cartanVec b) ∈ ⨆ k : ZMod 3, hT.zeroPiece k := fun a b =>
    Submodule.mem_iSup_of_mem (cartanGrade a + cartanGrade b)
      (Submodule.mem_sup_right (Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem b
        (Submodule.mem_iSup_of_mem rfl (Submodule.mem_span_singleton_self _)))))
  have hc : ∀ c : Fin 2, c = 0 ∨ c = 1 := by decide
  rcases hc c₀ with rfl | rfl <;> rcases hc c₁ with rfl | rfl <;>
    simp only [cartanProd, wtCoeff_cartan_zero, wtCoeff_cartan_one, hT.biVec_add_left,
      hT.biVec_sub_left, hT.biVec_smul_left, hT.biVec_add_right, hT.biVec_sub_right,
      hT.biVec_smul_right]
  all_goals
    repeat' first
      | exact hbase _ _
      | apply add_mem
      | apply sub_mem
      | apply Submodule.smul_mem

/-- The graded pieces exhaust the zero-weight piece. -/
lemma iSup_zeroPiece (hmul : IsMulRep repGauge) :
    (⨆ k : ZMod 3, hT.zeroPiece k) = (hT.gaugeWeightDecomposition hmul).piece 0 := by
  have hcyc : ∀ (j : Fin 2) (i : Fin 3),
      hT.prodCycle j i ∈ ⨆ k : ZMod 3, hT.zeroPiece k := by
    intro j i
    have hle : (⨆ k : ZMod 3, ℂ ∙ cycleEigen (hT.prodCycle j) k)
        ≤ ⨆ k : ZMod 3, hT.zeroPiece k := by
      refine iSup_mono fun k => ?_
      fin_cases j
      · exact le_sup_of_le_left le_sup_left
      · exact le_sup_of_le_left le_sup_right
    exact hle (cycle_mem_iSup (hT.prodCycle j) i)
  refine le_antisymm (iSup_le fun k => ?_) ?_
  · refine sup_le (sup_le ?_ ?_) (iSup_le fun a => iSup_le fun b => iSup_le fun _ => ?_)
    · exact (Submodule.span_singleton_le_iff_mem _ _).mpr
        (add_mem (add_mem (hT.prodCycle_mem_piece_zero hmul 0 0)
          (Submodule.smul_mem _ _ (hT.prodCycle_mem_piece_zero hmul 0 1)))
          (Submodule.smul_mem _ _ (hT.prodCycle_mem_piece_zero hmul 0 2)))
    · exact (Submodule.span_singleton_le_iff_mem _ _).mpr
        (add_mem (add_mem (hT.prodCycle_mem_piece_zero hmul 1 0)
          (Submodule.smul_mem _ _ (hT.prodCycle_mem_piece_zero hmul 1 1)))
          (Submodule.smul_mem _ _ (hT.prodCycle_mem_piece_zero hmul 1 2)))
    · exact (Submodule.span_singleton_le_iff_mem _ _).mpr
        (hT.cartanEigenProd_mem_piece_zero hmul a b)
  · rw [hT.gaugeWeightDecomposition_piece_zero_span hmul, Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hcyc 0 0
    · exact hcyc 1 2
    · exact hcyc 0 1
    · exact hcyc 1 0
    · exact hcyc 0 2
    · exact hcyc 1 1
    · exact hT.cartanProd_mem_iSup_zeroPiece 0 0
    · exact hT.cartanProd_mem_iSup_zeroPiece 0 1
    · exact hT.cartanProd_mem_iSup_zeroPiece 1 0
    · exact hT.cartanProd_mem_iSup_zeroPiece 1 1

/-- The `SU(3)` permutation decomposition of the zero-weight piece of the gauge weight
  decomposition: the cyclic colour rotation grades the ten dimensions the gauge weight
  cannot separate. Grade zero is necessary for gauge invariance but not sufficient;
  `zeroPiece_zero` says more about what a further reduction would need. -/
noncomputable def zeroPieceSU3Perm (hT : IsSU3BiAdjoint B repGauge T) (hmul : IsMulRep repGauge) :
    SU3PermDecomposition repGauge ((hT.gaugeWeightDecomposition hmul).piece 0) where
  piece := hT.zeroPiece
  piece_le k x hx := Module.End.mem_eigenspace_iff.mp (hT.zeroPiece_le_eigenspace k hx)
  iSup_piece := hT.iSup_zeroPiece hmul

/-- The pieces of the decomposition are the graded pieces. -/
@[simp]
lemma zeroPieceSU3Perm_piece (hmul : IsMulRep repGauge) (k : ZMod 3) :
    (hT.zeroPieceSU3Perm hmul).piece k = hT.zeroPiece k := rfl

/-- The grade zero piece, written out: one line from each cycle of root products, together
  with the two mixed products of Cartan eigenvectors.

  The four generators, written out in the components of `T`. The three root pairs are
  `rootPair 0 = (0, 1)`, `rootPair 1 = (3, 4)`, `rootPair 2 = (5, 6)`, and the two Cartan
  directions are `GaugeAlgebra.su3CartanId 0 = 2`, `GaugeAlgebra.su3CartanId 1 = 7`.

  `cycleEigen (hT.prodCycle 0) 0` unfolds, by `cycleEigen`, `prodCycle_zero_zero`,
  `prodCycle_zero_one`, `prodCycle_zero_two`, `posNegProd_eq` and `negPosProd_eq`, to
  `T ![0, 0] + T ![1, 1] + T ![3, 3] + T ![4, 4] + T ![5, 5] + T ![6, 6]`
  `+ Complex.I • (T ![1, 0] - T ![0, 1] + T ![3, 4] - T ![4, 3] + T ![6, 5] - T ![5, 6])`.

  `cycleEigen (hT.prodCycle 1) 0` unfolds the same way, with `prodCycle_one_zero`,
  `prodCycle_one_one`, `prodCycle_one_two` in place of the forward cycle, to
  `T ![0, 0] + T ![1, 1] + T ![3, 3] + T ![4, 4] + T ![5, 5] + T ![6, 6]`
  `+ Complex.I • (T ![0, 1] - T ![1, 0] + T ![4, 3] - T ![3, 4] + T ![5, 6] - T ![6, 5])`,
  the same six diagonal terms with the antisymmetric part negated.

  `hT.cartanEigenProd 0 1` and `hT.cartanEigenProd 1 0` unfold, by `cartanEigenProd`,
  `cartanVec` and the bilinearity of `biVec` (`biVec_add_left`, `biVec_sub_left`,
  `biVec_smul_left`, `biVec_add_right`, `biVec_sub_right`, `biVec_smul_right`), to
  `cartanProd 0 0 + cartanProd 1 1 ± Complex.I • (cartanProd 0 1 - cartanProd 1 0)`,
  the sign matching the order of the two arguments, which `cartanProd_eq` writes as
  `T ![2, 2] + T ![7, 7] + Complex.I • (T ![2, 7] - T ![7, 2])` and
  `T ![2, 2] + T ![7, 7] + Complex.I • (T ![7, 2] - T ![2, 7])` respectively.

  Grade zero is necessary for a gauge invariant to land here, not sufficient:
  `SU3PermDecomposition.mem_zero_of_invariant` has no converse, and combining the gauge
  weight decomposition with this `SU(3)` permutation decomposition only reaches the cyclic
  subgroup of the Weyl group. Section E cuts these four lines down to two, the trivial
  isotype of the whole Weyl group, by separating the two combinations of them that the
  transposition fixes from the two it negates. That is as far as a finite group takes the
  argument; section F leaves the normaliser of the torus behind and cuts those two lines
  down to one, by a quarter turn in the `SU(2)` of the first two colours, which carries a
  Cartan direction to a root direction outright. -/
lemma zeroPiece_zero :
    hT.zeroPiece 0
      = ℂ ∙ cycleEigen (hT.prodCycle 0) 0 ⊔ ℂ ∙ cycleEigen (hT.prodCycle 1) 0
      ⊔ (ℂ ∙ hT.cartanEigenProd 0 1 ⊔ ℂ ∙ hT.cartanEigenProd 1 0) := by
  have hgrade : ∀ a b : Fin 2, cartanGrade a + cartanGrade b = 0 →
      (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by decide
  rw [zeroPiece]
  refine congrArg _ (le_antisymm (iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_)
    (sup_le ?_ ?_))
  · rcases hgrade a b hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact le_sup_left
    · exact le_sup_right
  · exact le_iSup_of_le 0 (le_iSup_of_le 1 (le_iSup_of_le (by decide) le_rfl))
  · exact le_iSup_of_le 1 (le_iSup_of_le 0 (le_iSup_of_le (by decide) le_rfl))

/-- The grade one piece, written out: one line from each cycle of root products, together
  with the square of the second Cartan eigenvector. -/
lemma zeroPiece_one :
    hT.zeroPiece 1
      = ℂ ∙ cycleEigen (hT.prodCycle 0) 1 ⊔ ℂ ∙ cycleEigen (hT.prodCycle 1) 1
      ⊔ ℂ ∙ hT.cartanEigenProd 1 1 := by
  have hgrade : ∀ a b : Fin 2, cartanGrade a + cartanGrade b = 1 → a = 1 ∧ b = 1 := by decide
  rw [zeroPiece]
  refine congrArg _ (le_antisymm (iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_)
    (le_iSup_of_le 1 (le_iSup_of_le 1 (le_iSup_of_le (by decide) le_rfl))))
  obtain ⟨rfl, rfl⟩ := hgrade a b hab
  exact le_rfl

/-- The grade two piece, written out: one line from each cycle of root products, together
  with the square of the first Cartan eigenvector. -/
lemma zeroPiece_two :
    hT.zeroPiece 2
      = ℂ ∙ cycleEigen (hT.prodCycle 0) 2 ⊔ ℂ ∙ cycleEigen (hT.prodCycle 1) 2
      ⊔ ℂ ∙ hT.cartanEigenProd 0 0 := by
  have hgrade : ∀ a b : Fin 2, cartanGrade a + cartanGrade b = 2 → a = 0 ∧ b = 0 := by decide
  rw [zeroPiece]
  refine congrArg _ (le_antisymm (iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_)
    (le_iSup_of_le 0 (le_iSup_of_le 0 (le_iSup_of_le (by decide) le_rfl))))
  obtain ⟨rfl, rfl⟩ := hgrade a b hab
  exact le_rfl

/-!

## E. The `S₃` isotypic decomposition of the zero-weight piece

The cyclic rotation generates half of the Weyl group `S₃` of `SU(3)`; the transposition
`gaugeSU3Transp` reaches the other half, and it does not preserve the cyclic grading.
Conjugating the three-cycle by it inverts the three-cycle, so it carries grade `k` to grade
`-k`: it fixes grade zero and exchanges grades one and two. What replaces the grading is
the isotypic decomposition `SU3WeylDecomposition`, whose three pieces are the trivial, sign
and standard isotypes of `S₃`.

Section E.1 computes the transposition, first on the Gell-Mann coordinate directions and
then on the weight vectors. Unlike the cyclic rotation it mixes nothing: it fixes the first
root pair up to the sign of its second member, exchanges the other two root pairs, and
negates the first Cartan direction while fixing the second. On the weight vectors it
therefore exchanges the raising and lowering vectors of the first root, exchanges the other
two roots, and exchanges the two Cartan eigenvectors up to a sign. Section E.2 transfers
this to the ten products: the two cycles of root products are exchanged, each running
backwards, and the four products of Cartan eigenvectors are exchanged in pairs. Grade zero
is stable under the transposition as a result, which is the hypothesis that
`SU3PermDecomposition.toWeyl` needs. Section E.3 names the four combinations of the grade
zero generators that the transposition fixes or negates, and section E.4 assembles the
isotypic decomposition and places the trace contraction in its trivial piece.

The sharpening is real but finite. The trivial isotype is the join of two of the four lines
of grade zero, so this sieve discards the sign isotype — spanned by the two antisymmetric
combinations, which vanish for `T` symmetric in its two indices but not in general — as
well as the two nonzero grades. It remains a sieve:
`SU3WeylDecomposition.mem_triv_of_invariant` has no converse, and `S₃` is finite, so the
gauge weight and the Weyl group together decide invariance under the normaliser of the
torus and nothing more. `rootTriv_add_cartanTriv` measures what is left over: the trace
contraction is half the sum of the two generators of the trivial isotype, and nothing here
says anything about the other combinations of those two generators. Which of them are gauge
invariant is settled in section F, by an element of `SU(3)` that does not normalise the
torus; no finite group settles it.

## E.1. The transposition on the Gell-Mann directions and the weight vectors

Conjugation by the transposition matrix permutes the matrix units by the transposition of
the first two colours, so it permutes the Gell-Mann matrices up to signs, this time without
mixing any two of them.

-/

/-- The transposition colour matrix is real and symmetric, so it is its own star. -/
lemma star_su3TranspMatrix :
    star !![(0 : ℂ), -1, 0; -1, 0, 0; 0, 0, -1] = !![(0 : ℂ), -1, 0; -1, 0, 0; 0, 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The conjugate of each Gell-Mann matrix by the transposition: the sign of the
  transposition cancels between the two factors, leaving conjugation by the permutation
  matrix of the transposition of the first two colours. -/
noncomputable def transpGellMann : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ
  | 0 => gellMannMatrix 0
  | 1 => -gellMannMatrix 1
  | 2 => -gellMannMatrix 2
  | 3 => gellMannMatrix 5
  | 4 => gellMannMatrix 6
  | 5 => gellMannMatrix 3
  | 6 => gellMannMatrix 4
  | 7 => gellMannMatrix 7

/-- Conjugating a Gell-Mann matrix by the transposition. -/
lemma conj_gellMannMatrix_gaugeSU3Transp (b : Fin 8) :
    gaugeSU3Transp.toSU3.1 * gellMannMatrix b * star gaugeSU3Transp.toSU3.1
      = transpGellMann b := by
  rw [show gaugeSU3Transp.toSU3.1 = !![(0 : ℂ), -1, 0; -1, 0, 0; 0, 0, -1] from su3Transp_coe,
    star_su3TranspMatrix]
  fin_cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [transpGellMann, gellMannMatrix_zero, gellMannMatrix_one, gellMannMatrix_two,
      gellMannMatrix_three, gellMannMatrix_four, gellMannMatrix_five, gellMannMatrix_six,
      gellMannMatrix_seven, Matrix.mul_apply, Fin.sum_univ_three]

/-- The coordinates of the image of each Gell-Mann direction under the transposition: the
  first root pair is fixed up to the sign of its second member, the other two root pairs
  are exchanged, and of the two Cartan directions the first is negated and the second
  fixed. -/
noncomputable def transpCol : Fin 8 → Fin 8 → ℂ
  | 0 => unitVec 0
  | 1 => -unitVec 1
  | 2 => -unitVec 2
  | 3 => unitVec 5
  | 4 => unitVec 6
  | 5 => unitVec 3
  | 6 => unitVec 4
  | 7 => unitVec 7

/-- The transposition on the Gell-Mann coordinate directions. -/
lemma rowAct_gaugeSU3Transp_unitVec (b : Fin 8) :
    rowAct gaugeSU3Transp (unitVec b) = transpCol b := by
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) = 3 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  funext a
  rw [rowAct_unitVec, adjointMatrix_inl_inl_eq_gellMannCoeff,
    conj_gellMannMatrix_gaugeSU3Transp]
  fin_cases b <;> fin_cases a <;>
    simp [transpGellMann, gellMannCoeff, transpCol, unitVec, gellMannMatrix_zero,
      gellMannMatrix_one, gellMannMatrix_two, gellMannMatrix_three, gellMannMatrix_four,
      gellMannMatrix_five, gellMannMatrix_six, gellMannMatrix_seven]
  all_goals first
    | linear_combination ((1 : ℂ) / 3) * h3
    | norm_num

/-- The transposition moves each root weight vector into the other cycle, sending the
  member at index `i` there to the member at index `1 - i`. -/
lemma rowAct_gaugeSU3Transp_wtCoeff (j : Fin 2) (i : Fin 3) :
    rowAct gaugeSU3Transp (wtCoeff (wtCycle j i)) = wtCoeff (wtCycle (j + 1) (1 - i)) := by
  fin_cases j <;> fin_cases i <;>
    simp [wtCycle, wtCoeff_inl, wtCoeff_inr_inl, rootPair, rowAct_add, rowAct_sub,
      rowAct_smul, rowAct_gaugeSU3Transp_unitVec, transpCol]
  all_goals module

/-- The transposition exchanges the two Cartan eigenvectors, up to a sign. It cannot fix
  them: they are the grade one and grade two eigenvectors of the cyclic rotation, and the
  transposition inverts grades. -/
lemma rowAct_gaugeSU3Transp_cartanVec (c : Fin 2) :
    rowAct gaugeSU3Transp (cartanVec c) = -cartanVec (c + 1) := by
  fin_cases c <;>
    simp [cartanVec, ← unitVec_cartanId, GaugeAlgebra.su3CartanId, rowAct_sub,
      rowAct_add, rowAct_smul, rowAct_gaugeSU3Transp_unitVec, transpCol]
  all_goals module

/-!

## E.2. The transposition on the zero-weight products

The transposition exchanges the two cycles of root products, reversing the direction of
travel, and exchanges the four products of Cartan eigenvectors in pairs. In particular it
exchanges the two grade zero cycle sums, and exchanges the two mixed Cartan products, which
is what makes the grade zero piece stable under it.

-/

/-- The transposition exchanges the two cycles of root products, reversing each. -/
lemma repGauge_gaugeSU3Transp_prodCycle (j : Fin 2) (i : Fin 3) :
    repGauge gaugeSU3Transp (hT.prodCycle j i) = hT.prodCycle (j + 1) (-i) := by
  fin_cases j <;> fin_cases i <;>
    simp only [prodCycle, hT.repGauge_biVec, rowAct_gaugeSU3Transp_wtCoeff] <;>
    rfl

/-- The transposition exchanges the two Cartan eigenvectors in each product. The two signs
  it picks up, one from each factor, cancel. -/
lemma repGauge_gaugeSU3Transp_cartanEigenProd (a b : Fin 2) :
    repGauge gaugeSU3Transp (hT.cartanEigenProd a b)
      = hT.cartanEigenProd (a + 1) (b + 1) := by
  rw [cartanEigenProd, hT.repGauge_biVec, rowAct_gaugeSU3Transp_cartanVec,
    rowAct_gaugeSU3Transp_cartanVec, hT.biVec_neg_neg, cartanEigenProd]

/-- The transposition exchanges the two grade zero cycle sums. -/
lemma repGauge_gaugeSU3Transp_cycleEigen_zero (j : Fin 2) :
    repGauge gaugeSU3Transp (cycleEigen (hT.prodCycle j) 0)
      = cycleEigen (hT.prodCycle (j + 1)) 0 := by
  rw [cycleEigen_zero_eq, cycleEigen_zero_eq, map_add, map_add,
    hT.repGauge_gaugeSU3Transp_prodCycle, hT.repGauge_gaugeSU3Transp_prodCycle,
    hT.repGauge_gaugeSU3Transp_prodCycle, show (-0 : Fin 3) = 0 from rfl,
    show (-1 : Fin 3) = 2 from rfl, show (-2 : Fin 3) = 1 from rfl]
  abel

/-- Each grade zero cycle sum lies in the grade zero piece. -/
lemma cycleEigen_mem_zeroPiece_zero (j : Fin 2) :
    cycleEigen (hT.prodCycle j) 0 ∈ hT.zeroPiece 0 := by
  rw [zeroPiece]
  fin_cases j
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.mem_span_singleton_self _))
  · exact Submodule.mem_sup_left (Submodule.mem_sup_right
      (Submodule.mem_span_singleton_self _))

/-- A product of two Cartan eigenvectors whose grades cancel lies in the grade zero
  piece. -/
lemma cartanEigenProd_mem_zeroPiece_zero {a b : Fin 2}
    (hab : cartanGrade a + cartanGrade b = 0) :
    hT.cartanEigenProd a b ∈ hT.zeroPiece 0 :=
  Submodule.mem_sup_right (Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem b
    (Submodule.mem_iSup_of_mem hab (Submodule.mem_span_singleton_self _))))

/-!

## E.3. The symmetric and antisymmetric combinations of grade zero

The transposition exchanges the two grade zero cycle sums, and exchanges the two mixed
Cartan products. Their sums are therefore fixed by it and their differences negated, which
is exactly the split of grade zero into the trivial and the sign isotype. Written in the
components of `T` the two symmetric combinations are the symmetric part of the trace: twice
the six root diagonal terms, and twice the two Cartan diagonal terms. The two antisymmetric
combinations are the corresponding antisymmetric parts, and vanish when `T` is symmetric in
its two indices.

-/

/-- The symmetric combination of the two cycles of root products, spanning one line of the
  trivial isotype. -/
noncomputable def rootTriv (hT : IsSU3BiAdjoint B repGauge T) : B :=
  cycleEigen (hT.prodCycle 0) 0 + cycleEigen (hT.prodCycle 1) 0

/-- The antisymmetric combination of the two cycles of root products, spanning one line of
  the sign isotype. -/
noncomputable def rootSign (hT : IsSU3BiAdjoint B repGauge T) : B :=
  cycleEigen (hT.prodCycle 0) 0 - cycleEigen (hT.prodCycle 1) 0

/-- The symmetric combination of the two mixed products of Cartan eigenvectors, spanning
  the other line of the trivial isotype. -/
noncomputable def cartanTriv (hT : IsSU3BiAdjoint B repGauge T) : B :=
  hT.cartanEigenProd 0 1 + hT.cartanEigenProd 1 0

/-- The antisymmetric combination of the two mixed products of Cartan eigenvectors,
  spanning the other line of the sign isotype. -/
noncomputable def cartanSign (hT : IsSU3BiAdjoint B repGauge T) : B :=
  hT.cartanEigenProd 0 1 - hT.cartanEigenProd 1 0

/-- The transposition fixes the symmetric root combination. -/
lemma repGauge_gaugeSU3Transp_rootTriv :
    repGauge gaugeSU3Transp hT.rootTriv = hT.rootTriv := by
  rw [rootTriv, map_add, hT.repGauge_gaugeSU3Transp_cycleEigen_zero,
    hT.repGauge_gaugeSU3Transp_cycleEigen_zero]
  show cycleEigen (hT.prodCycle 1) 0 + cycleEigen (hT.prodCycle 0) 0 = _
  abel

/-- The transposition negates the antisymmetric root combination. -/
lemma repGauge_gaugeSU3Transp_rootSign :
    repGauge gaugeSU3Transp hT.rootSign = -hT.rootSign := by
  rw [rootSign, map_sub, hT.repGauge_gaugeSU3Transp_cycleEigen_zero,
    hT.repGauge_gaugeSU3Transp_cycleEigen_zero]
  show cycleEigen (hT.prodCycle 1) 0 - cycleEigen (hT.prodCycle 0) 0 = _
  abel

/-- The transposition fixes the symmetric Cartan combination. -/
lemma repGauge_gaugeSU3Transp_cartanTriv :
    repGauge gaugeSU3Transp hT.cartanTriv = hT.cartanTriv := by
  rw [cartanTriv, map_add, hT.repGauge_gaugeSU3Transp_cartanEigenProd,
    hT.repGauge_gaugeSU3Transp_cartanEigenProd]
  show hT.cartanEigenProd 1 0 + hT.cartanEigenProd 0 1 = _
  abel

/-- The transposition negates the antisymmetric Cartan combination. -/
lemma repGauge_gaugeSU3Transp_cartanSign :
    repGauge gaugeSU3Transp hT.cartanSign = -hT.cartanSign := by
  rw [cartanSign, map_sub, hT.repGauge_gaugeSU3Transp_cartanEigenProd,
    hT.repGauge_gaugeSU3Transp_cartanEigenProd]
  show hT.cartanEigenProd 1 0 - hT.cartanEigenProd 0 1 = _
  abel

/-- The symmetric root combination, written out in the components of `T`: twice the six
  diagonal components of the root directions. -/
lemma rootTriv_eq :
    hT.rootTriv = (2 : ℂ) • (T ![0, 0] + T ![1, 1] + T ![3, 3] + T ![4, 4]
      + T ![5, 5] + T ![6, 6]) := by
  rw [rootTriv, cycleEigen_zero_eq, cycleEigen_zero_eq]
  simp only [prodCycle_zero_zero, prodCycle_zero_one, prodCycle_zero_two,
    prodCycle_one_zero, prodCycle_one_one, prodCycle_one_two, hT.posNegProd_eq,
    hT.negPosProd_eq, rootPair]
  module

/-- The antisymmetric root combination, written out in the components of `T`: the
  antisymmetric part of the same six components. -/
lemma rootSign_eq :
    hT.rootSign = (2 * Complex.I) • (T ![1, 0] - T ![0, 1] + T ![3, 4] - T ![4, 3]
      + T ![6, 5] - T ![5, 6]) := by
  rw [rootSign, cycleEigen_zero_eq, cycleEigen_zero_eq]
  simp only [prodCycle_zero_zero, prodCycle_zero_one, prodCycle_zero_two,
    prodCycle_one_zero, prodCycle_one_one, prodCycle_one_two, hT.posNegProd_eq,
    hT.negPosProd_eq, rootPair]
  module

/-- The symmetric Cartan combination, written out in the components of `T`: twice the two
  diagonal components of the Cartan directions. -/
lemma cartanTriv_eq : hT.cartanTriv = (2 : ℂ) • (T ![2, 2] + T ![7, 7]) := by
  have hc : ∀ a b : Fin 2, hT.biVec (wtCoeff (Sum.inr (Sum.inr a)))
      (wtCoeff (Sum.inr (Sum.inr b)))
      = T ![GaugeAlgebra.su3CartanId a, GaugeAlgebra.su3CartanId b] :=
    fun a b => hT.cartanProd_eq a b
  simp only [cartanTriv, cartanEigenProd, cartanVec, hT.biVec_add_left, hT.biVec_sub_left,
    hT.biVec_smul_left, hT.biVec_add_right, hT.biVec_sub_right, hT.biVec_smul_right, hc]
  match_scalars
  all_goals ring_nf
  all_goals try simp only [Complex.I_sq]
  all_goals ring1

/-- The antisymmetric Cartan combination, written out in the components of `T`: the
  antisymmetric part of the two mixed Cartan components. -/
lemma cartanSign_eq : hT.cartanSign = (2 * Complex.I) • (T ![2, 7] - T ![7, 2]) := by
  have hc : ∀ a b : Fin 2, hT.biVec (wtCoeff (Sum.inr (Sum.inr a)))
      (wtCoeff (Sum.inr (Sum.inr b)))
      = T ![GaugeAlgebra.su3CartanId a, GaugeAlgebra.su3CartanId b] :=
    fun a b => hT.cartanProd_eq a b
  simp only [cartanSign, cartanEigenProd, cartanVec, hT.biVec_add_left, hT.biVec_sub_left,
    hT.biVec_smul_left, hT.biVec_add_right, hT.biVec_sub_right, hT.biVec_smul_right, hc]
  match_scalars
  all_goals ring1

/-- The two symmetric combinations sum to twice the trace contraction: between them they
  cover the eight diagonal components, six from the root directions and two from the Cartan
  directions. -/
lemma rootTriv_add_cartanTriv :
    hT.rootTriv + hT.cartanTriv = (2 : ℂ) • hT.traceContraction := by
  rw [hT.rootTriv_eq, hT.cartanTriv_eq, traceContraction, Fin.sum_univ_eight]
  module

/-!

## E.4. The isotypic decomposition

Symmetrizing and antisymmetrizing over the transposition carry the grade zero piece into
the two symmetric and the two antisymmetric lines respectively, which is enough for three
things at once: grade zero is stable under the transposition, so `toWeyl` applies; the
trivial piece of the resulting decomposition is the join of the two symmetric lines; and
the sign piece is the join of the two antisymmetric ones. The standard piece is the join of
the two nonzero grades, which the transposition exchanges.

-/

/-- Symmetrizing an element of the grade zero piece over the transposition lands in the
  join of the two symmetric lines. -/
lemma add_transp_mem_triv {x : B} (hx : x ∈ hT.zeroPiece 0) :
    x + repGauge gaugeSU3Transp x ∈ ℂ ∙ hT.rootTriv ⊔ ℂ ∙ hT.cartanTriv := by
  have key : hT.zeroPiece 0 ≤ Submodule.comap
      (LinearMap.id + (repGauge gaugeSU3Transp : Module.End ℂ B))
      (ℂ ∙ hT.rootTriv ⊔ ℂ ∙ hT.cartanTriv) := by
    rw [hT.zeroPiece_zero]
    refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_) <;>
      rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_comap,
        LinearMap.add_apply, LinearMap.id_apply]
    · rw [hT.repGauge_gaugeSU3Transp_cycleEigen_zero]
      exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
    · rw [hT.repGauge_gaugeSU3Transp_cycleEigen_zero]
      show cycleEigen (hT.prodCycle 1) 0 + cycleEigen (hT.prodCycle 0) 0 ∈ _
      rw [add_comm]
      exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
    · rw [hT.repGauge_gaugeSU3Transp_cartanEigenProd]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    · rw [hT.repGauge_gaugeSU3Transp_cartanEigenProd]
      show hT.cartanEigenProd 1 0 + hT.cartanEigenProd 0 1 ∈ _
      rw [add_comm]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have h := key hx
  rwa [Submodule.mem_comap, LinearMap.add_apply, LinearMap.id_apply] at h

/-- Antisymmetrizing an element of the grade zero piece over the transposition lands in the
  join of the two antisymmetric lines. -/
lemma sub_transp_mem_sign {x : B} (hx : x ∈ hT.zeroPiece 0) :
    x - repGauge gaugeSU3Transp x ∈ ℂ ∙ hT.rootSign ⊔ ℂ ∙ hT.cartanSign := by
  have key : hT.zeroPiece 0 ≤ Submodule.comap
      (LinearMap.id - (repGauge gaugeSU3Transp : Module.End ℂ B))
      (ℂ ∙ hT.rootSign ⊔ ℂ ∙ hT.cartanSign) := by
    rw [hT.zeroPiece_zero]
    refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_) <;>
      rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_comap,
        LinearMap.sub_apply, LinearMap.id_apply]
    · rw [hT.repGauge_gaugeSU3Transp_cycleEigen_zero]
      exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
    · rw [hT.repGauge_gaugeSU3Transp_cycleEigen_zero]
      show cycleEigen (hT.prodCycle 1) 0 - cycleEigen (hT.prodCycle 0) 0 ∈ _
      rw [← neg_sub]
      exact Submodule.mem_sup_left (neg_mem (Submodule.mem_span_singleton_self _))
    · rw [hT.repGauge_gaugeSU3Transp_cartanEigenProd]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    · rw [hT.repGauge_gaugeSU3Transp_cartanEigenProd]
      show hT.cartanEigenProd 1 0 - hT.cartanEigenProd 0 1 ∈ _
      rw [← neg_sub]
      exact Submodule.mem_sup_right (neg_mem (Submodule.mem_span_singleton_self _))
  have h := key hx
  rwa [Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply] at h

/-- The two symmetric lines lie inside the grade zero piece. -/
lemma sup_span_triv_le_zeroPiece_zero :
    ℂ ∙ hT.rootTriv ⊔ ℂ ∙ hT.cartanTriv ≤ hT.zeroPiece 0 := by
  refine sup_le ?_ ?_ <;> rw [Submodule.span_singleton_le_iff_mem]
  · exact add_mem (hT.cycleEigen_mem_zeroPiece_zero 0) (hT.cycleEigen_mem_zeroPiece_zero 1)
  · exact add_mem (hT.cartanEigenProd_mem_zeroPiece_zero (by decide))
      (hT.cartanEigenProd_mem_zeroPiece_zero (by decide))

/-- The two antisymmetric lines lie inside the grade zero piece. -/
lemma sup_span_sign_le_zeroPiece_zero :
    ℂ ∙ hT.rootSign ⊔ ℂ ∙ hT.cartanSign ≤ hT.zeroPiece 0 := by
  refine sup_le ?_ ?_ <;> rw [Submodule.span_singleton_le_iff_mem]
  · exact sub_mem (hT.cycleEigen_mem_zeroPiece_zero 0) (hT.cycleEigen_mem_zeroPiece_zero 1)
  · exact sub_mem (hT.cartanEigenProd_mem_zeroPiece_zero (by decide))
      (hT.cartanEigenProd_mem_zeroPiece_zero (by decide))

/-- The transposition preserves the grade zero piece: an element and its symmetrization
  both lie there, so the image of the element does too. -/
lemma repGauge_gaugeSU3Transp_mem_zeroPiece_zero {x : B} (hx : x ∈ hT.zeroPiece 0) :
    repGauge gaugeSU3Transp x ∈ hT.zeroPiece 0 := by
  have h := hT.sup_span_triv_le_zeroPiece_zero (hT.add_transp_mem_triv hx)
  simpa using sub_mem h hx

/-- The `S₃` isotypic decomposition of the zero-weight piece of the gauge weight
  decomposition: the whole Weyl group of `SU(3)` sorting the ten dimensions that the gauge
  weight cannot separate. It is the cyclic decomposition upgraded by
  `SU3PermDecomposition.toWeyl`, whose hypothesis is met because the transposition
  exchanges the two grade zero cycle sums and the two mixed Cartan products. -/
noncomputable def zeroPieceSU3Weyl (hT : IsSU3BiAdjoint B repGauge T)
    (hmul : IsMulRep repGauge) :
    SU3WeylDecomposition repGauge ((hT.gaugeWeightDecomposition hmul).piece 0) :=
  (hT.zeroPieceSU3Perm hmul).toWeyl fun _ hx =>
    hT.repGauge_gaugeSU3Transp_mem_zeroPiece_zero hx

/-- The trivial isotype piece, written out: the join of the two symmetric lines. Two of the
  four dimensions of grade zero survive here; the other two are of sign isotype. -/
lemma zeroPieceSU3Weyl_isotypic_triv (hmul : IsMulRep repGauge) :
    (hT.zeroPieceSU3Weyl hmul).isotypic .triv
      = ℂ ∙ hT.rootTriv ⊔ ℂ ∙ hT.cartanTriv := by
  rw [zeroPieceSU3Weyl, SU3PermDecomposition.toWeyl_isotypic_triv, zeroPieceSU3Perm_piece]
  refine le_antisymm ?_ ?_
  · rintro x ⟨hx0, hxR⟩
    have hR : repGauge gaugeSU3Transp x = x := by
      simpa using Module.End.mem_eigenspace_iff.mp hxR
    have h := hT.add_transp_mem_triv hx0
    rw [hR] at h
    have h2 := Submodule.smul_mem _ ((2 : ℂ)⁻¹) h
    rwa [show (2 : ℂ)⁻¹ • (x + x) = x from by module] at h2
  · refine sup_le ?_ ?_ <;> rw [Submodule.span_singleton_le_iff_mem]
    · exact ⟨hT.sup_span_triv_le_zeroPiece_zero
        (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)),
        Module.End.mem_eigenspace_iff.mpr
          (by rw [one_smul]; exact hT.repGauge_gaugeSU3Transp_rootTriv)⟩
    · exact ⟨hT.sup_span_triv_le_zeroPiece_zero
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)),
        Module.End.mem_eigenspace_iff.mpr
          (by rw [one_smul]; exact hT.repGauge_gaugeSU3Transp_cartanTriv)⟩

/-- The sign isotype piece, written out: the join of the two antisymmetric lines. This is
  the part of grade zero that the cyclic grading alone cannot discard. -/
lemma zeroPieceSU3Weyl_isotypic_sign (hmul : IsMulRep repGauge) :
    (hT.zeroPieceSU3Weyl hmul).isotypic .sign
      = ℂ ∙ hT.rootSign ⊔ ℂ ∙ hT.cartanSign := by
  rw [zeroPieceSU3Weyl, SU3PermDecomposition.toWeyl_isotypic_sign, zeroPieceSU3Perm_piece]
  refine le_antisymm ?_ ?_
  · rintro x ⟨hx0, hxR⟩
    have hR : repGauge gaugeSU3Transp x = -x := by
      simpa using Module.End.mem_eigenspace_iff.mp hxR
    have h := hT.sub_transp_mem_sign hx0
    rw [hR] at h
    have h2 := Submodule.smul_mem _ ((2 : ℂ)⁻¹) h
    rwa [show (2 : ℂ)⁻¹ • (x - -x) = x from by module] at h2
  · refine sup_le ?_ ?_ <;> rw [Submodule.span_singleton_le_iff_mem]
    · exact ⟨hT.sup_span_sign_le_zeroPiece_zero
        (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)),
        Module.End.mem_eigenspace_iff.mpr
          (by rw [neg_one_smul]; exact hT.repGauge_gaugeSU3Transp_rootSign)⟩
    · exact ⟨hT.sup_span_sign_le_zeroPiece_zero
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)),
        Module.End.mem_eigenspace_iff.mpr
          (by rw [neg_one_smul]; exact hT.repGauge_gaugeSU3Transp_cartanSign)⟩

/-- The standard isotype piece: the join of the two nonzero grades, which the transposition
  exchanges and which therefore pair into two-dimensional irreducibles. -/
lemma zeroPieceSU3Weyl_isotypic_std (hmul : IsMulRep repGauge) :
    (hT.zeroPieceSU3Weyl hmul).isotypic .std = hT.zeroPiece 1 ⊔ hT.zeroPiece 2 := rfl

/-- The trace contraction is of trivial isotype: it is gauge invariant, so in particular
  the whole Weyl group fixes it. This is strictly stronger than lying in grade zero, which
  is the join of the trivial and the sign isotype. -/
lemma traceContraction_mem_isotypic_triv (hmul : IsMulRep repGauge) :
    hT.traceContraction ∈ (hT.zeroPieceSU3Weyl hmul).isotypic .triv :=
  SU3WeylDecomposition.mem_triv_of_invariant _ (hT.traceContraction_mem_piece_zero hmul)
    hT.repGauge_traceContraction

/-- The trace contraction lies in the join of the two symmetric lines: of the ten
  dimensions of the zero-weight piece, the gauge weight and the Weyl group together confine
  it to two. By `rootTriv_add_cartanTriv` it is half the sum of the two generators, so it is
  one particular element of that join; which other elements of the join are gauge invariant
  is settled in section F, where the answer turns out to be only its own multiples. -/
lemma traceContraction_mem_span_triv (hmul : IsMulRep repGauge) :
    hT.traceContraction ∈ ℂ ∙ hT.rootTriv ⊔ ℂ ∙ hT.cartanTriv := by
  rw [← hT.zeroPieceSU3Weyl_isotypic_triv hmul]
  exact hT.traceContraction_mem_isotypic_triv hmul

/-!

## F. Closing the gap with a quarter turn

Everything from section C to section E is a sieve built from the normaliser of the torus,
and all of it stops at two dimensions because it must: `rootTriv` and `cartanTriv` are
separately fixed by the torus and by the whole Weyl group, so no element of `N(T)` can tell
a general combination of the two from the trace contraction. The tensor square `8 ⊗ 8` of
the `su(3)` adjoint decomposes as `1 ⊕ 8 ⊕ 8 ⊕ 10 ⊕ 10̄ ⊕ 27` and so carries exactly one
singlet: the truth is one dimension, and reaching it needs an element of the gauge group
that does not normalise the torus.

Section F.1 exhibits one, and the choice is forced by the Gell-Mann conventions. The
directions `0`, `1` and `2`, that is `λ₁`, `λ₂` and `λ₃`, span an `su(2)` acting on the
first two colours, and the adjoint action of the matching `SU(2)` subgroup on that triple
is the rotation group `SO(3)`. A quarter turn there carries the Cartan direction `λ₃` to a
root direction outright, which is exactly what no element of `N(T)` can do. Two turns are
needed, one landing on `λ₁` and one on `λ₂`, because the Weyl group preserves the split of
the six root directions into those two classes. Section F.2 computes what the two turns do
to `rootTriv` and to `cartanTriv`: they move weight between the six root diagonal terms and
the two Cartan ones while preserving the total, which is `2 • traceContraction`. Section
F.3 turns that into the statement that the gauge invariants in the span are exactly the
multiples of the trace contraction.

## F.1. A quarter turn in the `SU(2)` of the first two colours

Written in the first two colours a quarter turn is the block `!![u, v; -conj v, conj u]`
with `u` and `v` of equal modulus. Taking `u = (1 + i) / 2` keeps every entry a Gaussian
rational, so no square roots enter, and the two values `v = (1 - i) / 2` and
`v = (1 + i) / 2` give the two turns wanted. The conjugate of `λ₃` by such a block is
`-2 u v` off the diagonal and nothing on it, since `u` and `v` have equal modulus; the
conjugate of `λ₈` is `λ₈`, since `λ₈` is a multiple of the identity on the first two
colours.

-/

/-- The matrix of a quarter turn in the `SU(2)` subgroup of the first two colours: the
  block `!![u, v; -conj v, conj u]` at `u = (1 + i) / 2`, with the third colour fixed. -/
noncomputable def su3TurnMatrix (v : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(1 + Complex.I) / 2, v, 0; -(starRingEnd ℂ) v, (1 - Complex.I) / 2, 0; 0, 0, 1]

/-- The star of a quarter turn matrix is the quarter turn matrix of the opposite turn. -/
lemma star_su3TurnMatrix (v : ℂ) :
    star (su3TurnMatrix v)
      = !![(1 - Complex.I) / 2, -v, 0; (starRingEnd ℂ) v, (1 + Complex.I) / 2, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su3TurnMatrix, Complex.ext_iff]

/-- A quarter turn matrix lies in `SU(3)` precisely when its off-diagonal entry has the
  same modulus as its diagonal one. Unitarity is the length of each row, and the
  determinant is that same length. -/
lemma su3TurnMatrix_mem {v : ℂ} (hv : v * (starRingEnd ℂ) v = 2⁻¹) :
    su3TurnMatrix v ∈ specialUnitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, star_su3TurnMatrix]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [su3TurnMatrix, Matrix.mul_apply, Fin.sum_univ_three]
    all_goals first
      | ring1
      | linear_combination hv - (1 / 4 : ℂ) * Complex.I_sq
  · rw [Matrix.det_fin_three]
    simp [su3TurnMatrix]
    all_goals first
      | ring1
      | linear_combination hv - (1 / 4 : ℂ) * Complex.I_sq

/-- A quarter turn as an element of `SU(3)`. -/
noncomputable def su3Turn (v : ℂ) (hv : v * (starRingEnd ℂ) v = 2⁻¹) :
    specialUnitaryGroup (Fin 3) ℂ := ⟨su3TurnMatrix v, su3TurnMatrix_mem hv⟩

/-- A quarter turn as a gauge transformation: trivial on isospin and hypercharge. -/
noncomputable def gaugeSU3Turn (v : ℂ) (hv : v * (starRingEnd ℂ) v = 2⁻¹) : GaugeGroupI :=
  ⟨su3Turn v hv, 1, 1⟩

/-- Conjugating the first Cartan direction by a quarter turn: the diagonal of the result
  cancels, since the two entries of the turn have the same modulus, and what is left is a
  combination of the two members of the first root pair. -/
lemma conj_gellMannMatrix_two_gaugeSU3Turn {v : ℂ} (hv : v * (starRingEnd ℂ) v = 2⁻¹) :
    (gaugeSU3Turn v hv).toSU3.1 * gellMannMatrix 2 * star (gaugeSU3Turn v hv).toSU3.1
      = !![0, -((1 + Complex.I) * v), 0;
          -((1 - Complex.I) * (starRingEnd ℂ) v), 0, 0;
          0, 0, 0] := by
  rw [show (gaugeSU3Turn v hv).toSU3.1 = su3TurnMatrix v from rfl, star_su3TurnMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su3TurnMatrix, gellMannMatrix_two, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals first
    | ring1
    | linear_combination hv - (1 / 4 : ℂ) * Complex.I_sq
    | linear_combination -hv + (1 / 4 : ℂ) * Complex.I_sq
    | linear_combination hv + (1 / 4 : ℂ) * Complex.I_sq
    | linear_combination -hv - (1 / 4 : ℂ) * Complex.I_sq

/-- A quarter turn fixes the diagonal matrix behind the second Cartan direction: on the
  first two colours that matrix is a multiple of the identity, and the third colour is
  fixed. -/
lemma conj_diag_su3TurnMatrix {v : ℂ} (hv : v * (starRingEnd ℂ) v = 2⁻¹) :
    su3TurnMatrix v * !![1, 0, 0; 0, 1, 0; 0, 0, -2] * star (su3TurnMatrix v)
      = !![1, 0, 0; 0, 1, 0; 0, 0, -2] := by
  rw [star_su3TurnMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su3TurnMatrix, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals first
    | ring1
    | linear_combination hv - (1 / 4 : ℂ) * Complex.I_sq

/-- Conjugating the second Cartan direction by a quarter turn leaves it alone. -/
lemma conj_gellMannMatrix_seven_gaugeSU3Turn {v : ℂ} (hv : v * (starRingEnd ℂ) v = 2⁻¹) :
    (gaugeSU3Turn v hv).toSU3.1 * gellMannMatrix 7 * star (gaugeSU3Turn v hv).toSU3.1
      = gellMannMatrix 7 := by
  rw [show (gaugeSU3Turn v hv).toSU3.1 = su3TurnMatrix v from rfl, gellMannMatrix_seven,
    Matrix.mul_smul, Matrix.smul_mul, conj_diag_su3TurnMatrix hv]

/-- The first quarter turn, at `v = (1 - i) / 2`: it carries `λ₃` to `-λ₁`. -/
noncomputable def gaugeSU3TurnFst : GaugeGroupI :=
  gaugeSU3Turn ((1 - Complex.I) / 2)
    (by rw [map_div₀, map_sub, map_one, Complex.conj_I, map_ofNat]
        linear_combination (-1 / 4 : ℂ) * Complex.I_sq)

/-- The second quarter turn, at `v = (1 + i) / 2`: it carries `λ₃` to `λ₂`. -/
noncomputable def gaugeSU3TurnSnd : GaugeGroupI :=
  gaugeSU3Turn ((1 + Complex.I) / 2)
    (by rw [map_div₀, map_add, map_one, Complex.conj_I, map_ofNat]
        linear_combination (-1 / 4 : ℂ) * Complex.I_sq)

/-- The first quarter turn on the first Cartan coordinate direction: it lands on the first
  member of the first root pair, up to sign. This is the step no element of the normaliser
  of the torus can take. -/
lemma rowAct_gaugeSU3TurnFst_unitVec_two :
    rowAct gaugeSU3TurnFst (unitVec 2) = -unitVec 0 := by
  funext a
  rw [gaugeSU3TurnFst, rowAct_unitVec, adjointMatrix_inl_inl_eq_gellMannCoeff,
    conj_gellMannMatrix_two_gaugeSU3Turn]
  fin_cases a <;> simp [gellMannCoeff, unitVec]
  all_goals norm_num

/-- The second quarter turn on the first Cartan coordinate direction: it lands on the
  second member of the first root pair. The two turns are both needed, since the Weyl group
  never mixes the two members of a root pair with each other. -/
lemma rowAct_gaugeSU3TurnSnd_unitVec_two :
    rowAct gaugeSU3TurnSnd (unitVec 2) = unitVec 1 := by
  funext a
  rw [gaugeSU3TurnSnd, rowAct_unitVec, adjointMatrix_inl_inl_eq_gellMannCoeff,
    conj_gellMannMatrix_two_gaugeSU3Turn]
  fin_cases a <;> simp [gellMannCoeff, unitVec]
  all_goals norm_num

/-- A quarter turn fixes the second Cartan coordinate direction. -/
lemma rowAct_gaugeSU3Turn_unitVec_seven {v : ℂ} (hv : v * (starRingEnd ℂ) v = 2⁻¹) :
    rowAct (gaugeSU3Turn v hv) (unitVec 7) = unitVec 7 := by
  have h3 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  funext a
  rw [rowAct_unitVec, adjointMatrix_inl_inl_eq_gellMannCoeff,
    conj_gellMannMatrix_seven_gaugeSU3Turn hv]
  fin_cases a <;> simp [gellMannCoeff, gellMannMatrix_seven, unitVec]
  field_simp
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

/-- The first quarter turn fixes the second Cartan coordinate direction. -/
lemma rowAct_gaugeSU3TurnFst_unitVec_seven :
    rowAct gaugeSU3TurnFst (unitVec 7) = unitVec 7 := by
  rw [gaugeSU3TurnFst]
  exact rowAct_gaugeSU3Turn_unitVec_seven _

/-- The second quarter turn fixes the second Cartan coordinate direction. -/
lemma rowAct_gaugeSU3TurnSnd_unitVec_seven :
    rowAct gaugeSU3TurnSnd (unitVec 7) = unitVec 7 := by
  rw [gaugeSU3TurnSnd]
  exact rowAct_gaugeSU3Turn_unitVec_seven _


/-!

## F.2. The two turns on the two trivial lines

`cartanTriv` is twice the sum of the two Cartan diagonal components `T ![2, 2]` and
`T ![7, 7]`, and `rootTriv` twice the sum of the six root ones. A quarter turn fixes
`T ![7, 7]` and carries `T ![2, 2]` to a root diagonal component, so it moves the weight
`2 • (T ![2, 2] - T ![0, 0])` out of `cartanTriv` and exactly the same weight into
`rootTriv`, leaving their sum `2 • traceContraction` alone, as it must, that sum being
gauge invariant. This is the mixing no element of the normaliser of the torus can produce,
and it is what a bare grading cannot see.

One turn ties one root diagonal component to the Cartan pair; the six of them are reached
by pushing the two base relations through the cyclic colour rotation of section D.
`cartanTurn` records the three directions that rotation moves `λ₃` through, one Cartan
direction of each of the three colour pairs, and `biVec_cartanTurn_sum` says that the three
products they make add up to `3 / 2` times the Cartan pair. So the six root diagonal
components sum to three times that pair, and the trace contraction, which is the six of
them plus the pair, to four times it.

-/

/-- The first quarter turn on the Cartan pair of diagonal components: the second is fixed,
  and the first is carried to the diagonal component of the first root direction. -/
lemma repGauge_gaugeSU3TurnFst_cartanPair (hT : IsSU3BiAdjoint B repGauge T) :
    repGauge gaugeSU3TurnFst (T ![2, 2] + T ![7, 7]) = T ![0, 0] + T ![7, 7] := by
  rw [← hT.biVec_unitVec 2 2, ← hT.biVec_unitVec 7 7, map_add, hT.repGauge_biVec,
    hT.repGauge_biVec, rowAct_gaugeSU3TurnFst_unitVec_two,
    rowAct_gaugeSU3TurnFst_unitVec_seven, hT.biVec_neg_neg, hT.biVec_unitVec,
    hT.biVec_unitVec]

/-- The second quarter turn on the Cartan pair of diagonal components. -/
lemma repGauge_gaugeSU3TurnSnd_cartanPair (hT : IsSU3BiAdjoint B repGauge T) :
    repGauge gaugeSU3TurnSnd (T ![2, 2] + T ![7, 7]) = T ![1, 1] + T ![7, 7] := by
  rw [← hT.biVec_unitVec 2 2, ← hT.biVec_unitVec 7 7, map_add, hT.repGauge_biVec,
    hT.repGauge_biVec, rowAct_gaugeSU3TurnSnd_unitVec_two,
    rowAct_gaugeSU3TurnSnd_unitVec_seven, hT.biVec_unitVec, hT.biVec_unitVec]

/-- The first quarter turn on the symmetric Cartan combination: one of its two diagonal
  components becomes a root one, so it leaves the line it spans. -/
lemma repGauge_gaugeSU3TurnFst_cartanTriv :
    repGauge gaugeSU3TurnFst hT.cartanTriv = (2 : ℂ) • (T ![0, 0] + T ![7, 7]) := by
  rw [hT.cartanTriv_eq, map_smul, hT.repGauge_gaugeSU3TurnFst_cartanPair]

/-- The second quarter turn on the symmetric Cartan combination. -/
lemma repGauge_gaugeSU3TurnSnd_cartanTriv :
    repGauge gaugeSU3TurnSnd hT.cartanTriv = (2 : ℂ) • (T ![1, 1] + T ![7, 7]) := by
  rw [hT.cartanTriv_eq, map_smul, hT.repGauge_gaugeSU3TurnSnd_cartanPair]

/-- The first quarter turn on the symmetric root combination: it gains exactly the weight
  the symmetric Cartan combination loses, the two together summing to twice the gauge
  invariant trace contraction. -/
lemma repGauge_gaugeSU3TurnFst_rootTriv :
    repGauge gaugeSU3TurnFst hT.rootTriv
      = hT.rootTriv + (2 : ℂ) • (T ![2, 2] - T ![0, 0]) := by
  have hr : hT.rootTriv = (2 : ℂ) • hT.traceContraction - hT.cartanTriv :=
    eq_sub_of_add_eq hT.rootTriv_add_cartanTriv
  rw [hr, map_sub, map_smul, hT.repGauge_traceContraction,
    hT.repGauge_gaugeSU3TurnFst_cartanTriv, hT.cartanTriv_eq]
  module

/-- The second quarter turn on the symmetric root combination. -/
lemma repGauge_gaugeSU3TurnSnd_rootTriv :
    repGauge gaugeSU3TurnSnd hT.rootTriv
      = hT.rootTriv + (2 : ℂ) • (T ![2, 2] - T ![1, 1]) := by
  have hr : hT.rootTriv = (2 : ℂ) • hT.traceContraction - hT.cartanTriv :=
    eq_sub_of_add_eq hT.rootTriv_add_cartanTriv
  rw [hr, map_sub, map_smul, hT.repGauge_traceContraction,
    hT.repGauge_gaugeSU3TurnSnd_cartanTriv, hT.cartanTriv_eq]
  module

/-- The three coordinate directions the cyclic colour rotation moves the first Cartan
  direction through: one Cartan direction for each of the three colour pairs. -/
noncomputable def cartanTurn : Fin 3 → Fin 8 → ℂ
  | 0 => unitVec 2
  | 1 => (-(2 : ℂ)⁻¹) • unitVec 2 + (((Real.sqrt 3 : ℝ) : ℂ) / 2) • unitVec 7
  | 2 => (-(2 : ℂ)⁻¹) • unitVec 2 - (((Real.sqrt 3 : ℝ) : ℂ) / 2) • unitVec 7

/-- The cycle starts at the first Cartan coordinate direction. -/
lemma cartanTurn_zero : cartanTurn 0 = unitVec 2 := rfl

/-- The cyclic colour rotation moves each of the three directions one step along the
  cycle. -/
lemma rowAct_gaugeSU3Perm_cartanTurn (i : Fin 3) :
    rowAct gaugeSU3Perm (cartanTurn i) = cartanTurn (i + 1) := by
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) = 3 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  fin_cases i
  · show rowAct gaugeSU3Perm (cartanTurn 0) = cartanTurn 1
    simp only [cartanTurn, rowAct_gaugeSU3Perm_unitVec, permCol]
  · show rowAct gaugeSU3Perm (cartanTurn 1) = cartanTurn 2
    simp only [cartanTurn, rowAct_add, rowAct_smul, rowAct_gaugeSU3Perm_unitVec, permCol]
    match_scalars
    all_goals first
      | ring1
      | linear_combination (-(1 : ℂ) / 4) * h3
  · show rowAct gaugeSU3Perm (cartanTurn 2) = cartanTurn 0
    simp only [cartanTurn, rowAct_sub, rowAct_smul, rowAct_gaugeSU3Perm_unitVec, permCol]
    match_scalars
    all_goals first
      | ring1
      | linear_combination ((1 : ℂ) / 4) * h3

/-- The three products the cycle makes add up to `3 / 2` times the Cartan pair: the three
  Cartan directions of the three colour pairs are not independent, and what survives the
  sum is the pair of diagonal components the torus already sees. -/
lemma biVec_cartanTurn_sum :
    hT.biVec (cartanTurn 0) (cartanTurn 0) + hT.biVec (cartanTurn 1) (cartanTurn 1)
        + hT.biVec (cartanTurn 2) (cartanTurn 2)
      = ((3 : ℂ) / 2) • (T ![2, 2] + T ![7, 7]) := by
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) = 3 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  simp only [cartanTurn, hT.biVec_add_left, hT.biVec_sub_left, hT.biVec_smul_left,
    hT.biVec_add_right, hT.biVec_sub_right, hT.biVec_smul_right, hT.biVec_unitVec]
  match_scalars
  all_goals first
    | ring1
    | linear_combination ((1 : ℂ) / 2) * h3

/-- A multiple of the Cartan pair that is gauge invariant is a quarter of the same multiple
  of the trace contraction. The two quarter turns tie the first two root diagonal
  components to the Cartan pair, and the cyclic colour rotation carries those two relations
  to the remaining four. -/
lemma smul_traceContraction_eq_of_invariant (f : ℂ)
    (hinv : ∀ g : GaugeGroupI, repGauge g (f • (T ![2, 2] + T ![7, 7]))
      = f • (T ![2, 2] + T ![7, 7])) :
    f • hT.traceContraction = (4 : ℂ) • (f • (T ![2, 2] + T ![7, 7])) := by
  have hperm : ∀ c₀ c₁ : Fin 8 → ℂ, f • hT.biVec c₀ c₀ = f • hT.biVec c₁ c₁ →
      f • hT.biVec (rowAct gaugeSU3Perm c₀) (rowAct gaugeSU3Perm c₀)
        = f • hT.biVec (rowAct gaugeSU3Perm c₁) (rowAct gaugeSU3Perm c₁) := by
    intro c₀ c₁ h
    have h' := congrArg (repGauge gaugeSU3Perm) h
    rwa [map_smul, map_smul, hT.repGauge_biVec, hT.repGauge_biVec] at h'
  have hbase : ∀ g : GaugeGroupI, ∀ y : B,
      repGauge g (T ![2, 2] + T ![7, 7]) = y + T ![7, 7] → f • y = f • T ![2, 2] := by
    intro g y hg
    have h := hinv g
    rw [map_smul, hg, smul_add, smul_add] at h
    exact add_right_cancel h
  have hA0 : f • hT.biVec (unitVec 0) (unitVec 0)
      = f • hT.biVec (cartanTurn 0) (cartanTurn 0) := by
    rw [cartanTurn_zero, hT.biVec_unitVec, hT.biVec_unitVec]
    exact hbase _ _ hT.repGauge_gaugeSU3TurnFst_cartanPair
  have hB0 : f • hT.biVec (unitVec 1) (unitVec 1)
      = f • hT.biVec (cartanTurn 0) (cartanTurn 0) := by
    rw [cartanTurn_zero, hT.biVec_unitVec, hT.biVec_unitVec]
    exact hbase _ _ hT.repGauge_gaugeSU3TurnSnd_cartanPair
  have hA1 : f • hT.biVec (unitVec 5) (unitVec 5)
      = f • hT.biVec (cartanTurn 1) (cartanTurn 1) := by
    have h := hperm _ _ hA0
    rwa [rowAct_gaugeSU3Perm_unitVec, rowAct_gaugeSU3Perm_cartanTurn,
      show ((0 : Fin 3) + 1) = 1 from rfl, show permCol 0 = unitVec 5 from rfl] at h
  have hB1 : f • hT.biVec (unitVec 6) (unitVec 6)
      = f • hT.biVec (cartanTurn 1) (cartanTurn 1) := by
    have h := hperm _ _ hB0
    rwa [rowAct_gaugeSU3Perm_unitVec, rowAct_gaugeSU3Perm_cartanTurn,
      show ((0 : Fin 3) + 1) = 1 from rfl, show permCol 1 = unitVec 6 from rfl] at h
  have hA2 : f • hT.biVec (unitVec 3) (unitVec 3)
      = f • hT.biVec (cartanTurn 2) (cartanTurn 2) := by
    have h := hperm _ _ hA1
    rwa [rowAct_gaugeSU3Perm_unitVec, rowAct_gaugeSU3Perm_cartanTurn,
      show ((1 : Fin 3) + 1) = 2 from rfl, show permCol 5 = unitVec 3 from rfl] at h
  have hB2 : f • hT.biVec (unitVec 4) (unitVec 4)
      = f • hT.biVec (cartanTurn 2) (cartanTurn 2) := by
    have h := hperm _ _ hB1
    rwa [rowAct_gaugeSU3Perm_unitVec, rowAct_gaugeSU3Perm_cartanTurn,
      show ((1 : Fin 3) + 1) = 2 from rfl, show permCol 6 = -unitVec 4 from rfl,
      hT.biVec_neg_neg] at h
  simp only [hT.biVec_unitVec] at hA0 hB0 hA1 hB1 hA2 hB2
  rw [traceContraction, Fin.sum_univ_eight, smul_add, smul_add, smul_add, smul_add,
    smul_add, smul_add, smul_add, hA0, hB0, hA1, hB1, hA2, hB2]
  linear_combination (norm := module) (2 * f) • hT.biVec_cartanTurn_sum


/-!

## F.3. The gauge invariants in the span

A gauge invariant in the span is of trivial isotype by section E, so it is a combination
`a • rootTriv + b • cartanTriv`. Subtracting the right multiple of the trace contraction
leaves a multiple of `cartanTriv` alone, still gauge invariant, and F.2 says such a multiple
is a multiple of the trace contraction as well. So the two lines the finite group left
collapse to one, which is the one singlet of `8 ⊗ 8`, and the containment of section B
becomes an equality.

-/

/-- Every gauge invariant in the span of the components is a multiple of the trace
  contraction. The gauge weight, the cyclic colour rotation and the Weyl group cut the span
  down to the two lines through `rootTriv` and `cartanTriv`, and the quarter turns of F.1
  cut those two down to one. -/
lemma exists_smul_traceContraction_of_invariant (hT : IsSU3BiAdjoint B repGauge T)
    (hmul : IsMulRep repGauge) {x : B} (hx : x ∈ hT.span)
    (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    ∃ c : ℂ, x = c • hT.traceContraction := by
  have hmem : x ∈ ℂ ∙ hT.rootTriv ⊔ ℂ ∙ hT.cartanTriv := by
    rw [← hT.zeroPieceSU3Weyl_isotypic_triv hmul]
    exact SU3WeylDecomposition.mem_triv_of_invariant _
      (GaugeWeightDecomposition.mem_zero_of_invariant _ hx hinv) hinv
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hz
  have hrt := hT.rootTriv_add_cartanTriv
  have hct := hT.cartanTriv_eq
  have hE : ((b - a) * 2) • (T ![2, 2] + T ![7, 7])
      = (a • hT.rootTriv + b • hT.cartanTriv) - (2 * a) • hT.traceContraction := by
    linear_combination (norm := module) (-a) • hrt + (a - b) • hct
  have hinvC : ∀ g : GaugeGroupI,
      repGauge g (((b - a) * 2) • (T ![2, 2] + T ![7, 7]))
        = ((b - a) * 2) • (T ![2, 2] + T ![7, 7]) := by
    intro g
    rw [hE, map_sub, map_smul, hinv g, hT.repGauge_traceContraction]
  have hkey := hT.smul_traceContraction_eq_of_invariant ((b - a) * 2) hinvC
  exact ⟨2 * a + (b - a) / 2, by
    linear_combination (norm := module) a • hrt + (b - a) • hct + (-1 / 4 : ℂ) • hkey⟩

/-- The gauge invariants in the span of the components are exactly the multiples of the
  trace contraction. The three sieves of sections C, D and E together with the quarter turns
  of section F bound them from above, and the trace contraction is itself invariant and in
  the span, which bounds them from below. This is the one singlet of `8 ⊗ 8`. -/
lemma mem_span_and_invariant_iff (hT : IsSU3BiAdjoint B repGauge T) (hmul : IsMulRep repGauge)
    (x : B) :
    (x ∈ hT.span ∧ ∀ g : GaugeGroupI, repGauge g x = x)
      ↔ x ∈ ℂ ∙ hT.traceContraction := by
  refine ⟨fun h => ?_, fun hx => ?_⟩
  · obtain ⟨c, rfl⟩ := hT.exists_smul_traceContraction_of_invariant hmul h.1 h.2
    exact Submodule.mem_span_singleton.2 ⟨c, rfl⟩
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    exact ⟨Submodule.smul_mem _ _ hT.traceContraction_mem_span,
      fun g => by rw [map_smul, hT.repGauge_traceContraction]⟩

/-!

## F.4. The trivial square-zero extension of a module

Section F.3 asks for a ring: `IsMulRep` is a statement about multiplication, and the
decomposition machinery of sections C to E is set up in an algebra. The conclusion asks
for none of that, and the gap can be closed once and for all. The trivial square-zero
extension `TrivSqZeroExt ℂ M` of a module `M` is a commutative `ℂ`-algebra built from the
module structure alone, a representation on `M` extends to it by acting trivially on the
scalar part, and that extension acts by algebra maps for free. So F.3 holds in the
extension, and the injection of `M` carries the conclusion back:
`exists_smul_traceContraction_of_invariant_module` is F.3 with the algebra structure and
the multiplicativity hypothesis both removed.

-/

section SquareZero

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
  {ρ : Representation ℂ GaugeGroupI M} {U : (Fin 2 → Fin 8) → M}

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

/-- The images of the components in the square-zero extension again form a bi-adjoint
  family. -/
lemma isSU3BiAdjoint_sqZeroRep (hU : IsSU3BiAdjoint M ρ U) :
    IsSU3BiAdjoint (TrivSqZeroExt ℂ M) (sqZeroRep ρ) fun l => TrivSqZeroExt.inr (U l) where
  repGauge_T g l := by
    rw [sqZeroRep_inr, hU.repGauge_T g l]
    simp only [TrivSqZeroExt.inr_sum, TrivSqZeroExt.inr_smul]

/-- The trace contraction of the images is the image of the trace contraction. -/
lemma traceContraction_sqZeroRep (hU : IsSU3BiAdjoint M ρ U) :
    hU.isSU3BiAdjoint_sqZeroRep.traceContraction = TrivSqZeroExt.inr hU.traceContraction := by
  simp only [traceContraction, TrivSqZeroExt.inr_sum]

/-- The image of an element of the span lies in the span of the images. -/
lemma inr_mem_span_sqZeroRep (hU : IsSU3BiAdjoint M ρ U) {x : M} (hx : x ∈ hU.span) :
    TrivSqZeroExt.inr x ∈ hU.isSU3BiAdjoint_sqZeroRep.span := by
  obtain ⟨c, rfl⟩ := (hU.mem_span_iff x).1 hx
  refine (hU.isSU3BiAdjoint_sqZeroRep.mem_span_iff _).2 ⟨c, ?_⟩
  simp only [TrivSqZeroExt.inr_sum, TrivSqZeroExt.inr_smul]

/-- Every gauge invariant in the span of the components is a multiple of the trace
  contraction, for a family valued in a mere module. Neither an algebra structure on the
  target nor multiplicativity of the representation is needed: the square-zero extension
  supplies both, and the injection of the module reflects the conclusion back. -/
lemma exists_smul_traceContraction_of_invariant_module (hU : IsSU3BiAdjoint M ρ U) {x : M}
    (hx : x ∈ hU.span) (hinv : ∀ g : GaugeGroupI, ρ g x = x) :
    ∃ c : ℂ, x = c • hU.traceContraction := by
  obtain ⟨c, hc⟩ := hU.isSU3BiAdjoint_sqZeroRep.exists_smul_traceContraction_of_invariant
    (isMulRep_sqZeroRep ρ) (hU.inr_mem_span_sqZeroRep hx)
    (fun g => by rw [sqZeroRep_inr, hinv g])
  refine ⟨c, TrivSqZeroExt.inr_injective (R := ℂ) ?_⟩
  rw [hc, hU.traceContraction_sqZeroRep, TrivSqZeroExt.inr_smul]

end SquareZero

/-!

## F.5. The gauge invariants modulo a gauge-stable submodule

A gauge-stable submodule can be divided out: the quotient representation carries the
images of the components as a bi-adjoint family again, so F.4 applies verbatim in the
quotient and lifts to a classification modulo the submodule. Stability of the submodule is
what makes the quotient representation exist, and it cannot be dropped: for an unstable
line `ℂ ∙ v` the only invariant of the line is `0`, while an invariant of the sum may well
lie outside the span. The error term is invariant for free, since it is the difference of
two invariants.

-/

section Quotient

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
  {ρ : Representation ℂ GaugeGroupI M} {U : (Fin 2 → Fin 8) → M}

/-- The representation induced on the quotient by a gauge-stable submodule. -/
noncomputable def quotRep (ρ : Representation ℂ GaugeGroupI M) (S : Submodule ℂ M)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, ρ g y ∈ S) :
    Representation ℂ GaugeGroupI (M ⧸ S) where
  toFun g := S.mapQ S (ρ g) fun y hy => hS g y hy
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
lemma quotRep_mkQ (S : Submodule ℂ M) (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, ρ g y ∈ S)
    (g : GaugeGroupI) (y : M) : quotRep ρ S hS g (S.mkQ y) = S.mkQ (ρ g y) := rfl

/-- The images of the components in the quotient by a gauge-stable submodule again form a
  bi-adjoint family. -/
lemma isSU3BiAdjoint_quotRep (hU : IsSU3BiAdjoint M ρ U) (S : Submodule ℂ M)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, ρ g y ∈ S) :
    IsSU3BiAdjoint (M ⧸ S) (quotRep ρ S hS) fun l => S.mkQ (U l) where
  repGauge_T g l := by
    rw [quotRep_mkQ, hU.repGauge_T g l, map_sum]
    exact Finset.sum_congr rfl fun a _ => map_smul _ _ _

/-- The quotient map carries the trace contraction to the trace contraction of the
  images. -/
lemma mkQ_traceContraction (hU : IsSU3BiAdjoint M ρ U) (S : Submodule ℂ M)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, ρ g y ∈ S) :
    S.mkQ hU.traceContraction = (hU.isSU3BiAdjoint_quotRep S hS).traceContraction := by
  simp only [traceContraction, map_sum]

end Quotient

/-- The gauge invariants of the span of the components together with a gauge-stable
  submodule `S`: such an element is a multiple of the trace contraction up to an error in
  `S`, and the error is gauge invariant as well, being the difference of two invariants.
  Stability of `S` is needed, and not just convenient: for an unstable line the only
  invariant of the line is zero, while the sum can carry invariants outside the span. The
  classification is applied in the quotient by `S`, where the images of the components
  form a bi-adjoint family again. -/
lemma mem_span_sup_invariant_iff (hT : IsSU3BiAdjoint B repGauge T) (hmul : IsMulRep repGauge)
    (x : B) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S) (hx : x ∈ hT.span ⊔ S)
    (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    ∃ c : ℂ, ∃ y ∈ S, x = c • hT.traceContraction + y
      ∧ ∀ g : GaugeGroupI, repGauge g y = y := by
  have hmk : S.mkQ x ∈ (hT.isSU3BiAdjoint_quotRep S hS).span := by
    obtain ⟨u, hu, z, hz, huz⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, hc⟩ := (hT.mem_span_iff u).1 hu
    refine ((hT.isSU3BiAdjoint_quotRep S hS).mem_span_iff _).2 ⟨c, ?_⟩
    rw [← huz, map_add, show S.mkQ z = 0 from (Submodule.Quotient.mk_eq_zero S).2 hz,
      add_zero, hc, map_sum]
    exact Finset.sum_congr rfl fun d _ => map_smul _ _ _
  have hinv' : ∀ g : GaugeGroupI, quotRep repGauge S hS g (S.mkQ x) = S.mkQ x :=
    fun g => by rw [quotRep_mkQ, hinv g]
  obtain ⟨c, hc⟩ :=
    (hT.isSU3BiAdjoint_quotRep S hS).exists_smul_traceContraction_of_invariant_module hmk hinv'
  rw [← hT.mkQ_traceContraction S hS] at hc
  refine ⟨c, x - c • hT.traceContraction, ?_, by abel, fun g => ?_⟩
  · have hker : x - c • hT.traceContraction ∈ LinearMap.ker S.mkQ := by
      rw [LinearMap.mem_ker, map_sub, map_smul, hc, sub_self]
    rwa [Submodule.ker_mkQ] at hker
  · rw [map_sub, map_smul, hinv g, hT.repGauge_traceContraction]

end Decomposition

end IsSU3BiAdjoint

end StandardModel
