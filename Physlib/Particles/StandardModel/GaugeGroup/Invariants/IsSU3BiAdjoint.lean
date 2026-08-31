/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeAlgebra.Basis
public import Physlib.Particles.StandardModel.GaugeAlgebra.RootDecomposition
/-!
# Gauge tensors carrying two `su(3)` adjoint indices

`IsSU3BiAdjoint B repGauge T` says that a family `T`, indexed by two `su(3)` adjoint
indices and valued in a module `B` carrying a representation of the gauge group
`GaugeGroupI`, transforms as a tensor `T^{a₁ a₂}` in the `su(3)` factor of the adjoint
representation.

This is the gauge analogue of `IsQuadLorentz`. The field strength of the gluons carries
one `su(3)` adjoint index, so a product of two field strengths carries two, and the
proposition here records how such a product transforms.

Section A gives the proposition and the span of its components, section B the
orthogonality of the `su(3)` block of `adjointMatrix`, section C the trace
contraction, which is the natural gauge invariant built from two adjoint indices, and
section D the gauge weight decomposition of the span.
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

## B. Orthogonality of the adjoint matrix

Orthogonality of `adjointMatrix` is proved where the matrix is defined, in
`GaugeAlgebra.Basis`. All that is needed here is the row orthonormality of the block
belonging to this gauge factor, which is what makes the trace contraction of section C
gauge invariant.

-/

/-- The rows of the `su(3)` block of the adjoint matrix are orthonormal. -/
lemma sum_adjointMatrix_row_mul (g : GaugeGroupI) (c d : Fin 8) :
    ∑ a : Fin 8, GaugeAlgebra.adjointMatrix g (Sum.inl c) (Sum.inl a) *
      GaugeAlgebra.adjointMatrix g (Sum.inl d) (Sum.inl a)
      = if c = d then 1 else 0 := by
  have h : (GaugeAlgebra.adjointMatrix g * (GaugeAlgebra.adjointMatrix g)ᵀ)
      (Sum.inl c) (Sum.inl d) = (1 : Matrix (Fin 8 ⊕ Fin 3 ⊕ Fin 1)
        (Fin 8 ⊕ Fin 3 ⊕ Fin 1) ℝ) (Sum.inl c) (Sum.inl d) := by
    rw [GaugeAlgebra.adjointMatrix_mul_transpose]
  rw [Matrix.mul_apply, Fintype.sum_sum_type] at h
  simpa [Fintype.sum_sum_type, Matrix.one_apply] using h

TODO (lines := 92-104) "Move this to where `adjointMatrix` is defined."

/-!

## C. The trace contraction

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
    rw [← Complex.ofReal_sum, sum_adjointMatrix_row_mul]
    simp [apply_ite]
  rw [step, ← hT.traceContraction_eq_sum]


end IsSU3BiAdjoint

/-!

## D. The gauge weight decomposition of the span

The Gell-Mann basis vectors are not eigenvectors of the gauge torus, so the components
`T d` do not carry a definite gauge weight. The eigenvectors appear only after passing to
the weight basis of the `su(3)` adjoint: for each of the three root directions the two
complex combinations `x₁ ± i x₂` of the paired Gell-Mann coordinates, and the two Cartan
directions as they stand. That is eight coordinate vectors, recorded in `wtCoeff`, with
weights `wtWeight`.

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

## D.1. The weight basis of the `su(3)` adjoint

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

/-- The Gell-Mann indices of the two Cartan directions of `su(3)`. -/
def cartanId : Fin 2 → Fin 8
  | 0 => 2
  | 1 => 7

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
    GaugeAlgebra.cartanIdx c.castSucc.castSucc = Sum.inl (cartanId c) := by
  fin_cases c <;> rfl

/-- Every Gell-Mann index is either one of the two members of a root pair or a Cartan
  index. -/
lemma exists_rootPair_or_cartanId (a : Fin 8) :
    (∃ r : Fin 3, a = (rootPair r).1) ∨ (∃ r : Fin 3, a = (rootPair r).2)
      ∨ ∃ c : Fin 2, a = cartanId c := by
  revert a
  decide

/-!

## D.2. The adjoint matrix of a torus generator in the weight basis

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
    GaugeAlgebra.adjointMatrix (gaugeTorusGen i) (Sum.inl a) (Sum.inl (cartanId c))
      = if a = cartanId c then 1 else 0 := by
  have p := GaugeAlgebra.dualMap_coord_cartanIdx c.castSucc.castSucc i
  simp only [cartanIdx_castSucc] at p
  have e := LinearMap.congr_fun p (GaugeAlgebra.stdBasis (Sum.inl a))
  rw [dualMap_coord_apply] at e
  rw [e]
  simp [Finsupp.single_apply]

/-!

## D.3. The weight vectors of one adjoint index

-/

/-- The coordinates of the `su(3)` adjoint weight basis in the Gell-Mann basis: for each
  root the two combinations `x₁ ± i x₂` of the paired coordinates, and for each Cartan
  direction the coordinate itself. -/
noncomputable def wtCoeff : WeightIdx → Fin 8 → ℂ
  | Sum.inl r, a => (if a = (rootPair r).1 then 1 else 0)
      + Complex.I * (if a = (rootPair r).2 then 1 else 0)
  | Sum.inr (Sum.inl r), a => (if a = (rootPair r).1 then 1 else 0)
      - Complex.I * (if a = (rootPair r).2 then 1 else 0)
  | Sum.inr (Sum.inr c), a => if a = cartanId c then 1 else 0

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
        = if x = cartanId c then (1 : ℂ) else 0 := fun _ => rfl
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

## D.4. The bi-adjoint weight vectors and their span

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
    unitVec (cartanId c) = wtCoeff (Sum.inr (Sum.inr c)) := rfl

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

## D.5. The decomposition

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

## D.6. The zero-weight piece

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

end Decomposition

end IsSU3BiAdjoint

end StandardModel
