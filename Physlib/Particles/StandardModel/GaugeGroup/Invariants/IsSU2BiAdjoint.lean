/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeAlgebra.Basis
public import Physlib.Particles.StandardModel.GaugeAlgebra.RootDecomposition
/-!
# Gauge tensors carrying two `su(2)` adjoint indices

`IsSU2BiAdjoint B repGauge T` says that a family `T`, indexed by two `su(2)` adjoint
indices and valued in a module `B` carrying a representation of the gauge group
`GaugeGroupI`, transforms as a tensor `T^{a₁ a₂}` in the `su(2)` factor of the adjoint
representation.

This is the gauge analogue of `IsQuadLorentz`. The field strength of the `W` bosons
carries one `su(2)` adjoint index, so a product of two field strengths carries two, and
the proposition here records how such a product transforms.

Section A gives the proposition and the span of its components, section B the
orthogonality of the `su(2)` block of `adjointMatrix`, section C the trace contraction,
which is the natural gauge invariant built from two adjoint indices, and section D the
gauge weight decomposition of the span.
-/

@[expose] public section

namespace StandardModel

open Matrix

/-!

## A. Bi-adjoint `su(2)` families and the span of their components

-/

/-- A family `T` of elements of `B`, indexed by two `su(2)` adjoint indices, transforms
  as a tensor `T^{a₁ a₂}` under the representation `repGauge` of the gauge group. -/
structure IsSU2BiAdjoint (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B)
    (T : (Fin 2 → Fin 3) → B) : Prop where
  repGauge_T : ∀ (g : GaugeGroupI) (l : Fin 2 → Fin 3),
    repGauge g (T l) = ∑ a : Fin 2 → Fin 3,
      (∏ i : Fin 2, ((GaugeAlgebra.adjointMatrix g (Sum.inr (Sum.inl (a i)))
        (Sum.inr (Sum.inl (l i))) : ℝ) : ℂ)) • T a

TODO (lines := 43-47) "we could probably make this just be about
 the action of the SU(2) factor."

namespace IsSU2BiAdjoint
set_option linter.unusedVariables false

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {T : (Fin 2 → Fin 3) → B}
  (hT : IsSU2BiAdjoint B repGauge T)

/-- The span of all the components. -/
def span (hT : IsSU2BiAdjoint B repGauge T) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

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

/-!

## B. Orthogonality of the adjoint matrix

Orthogonality of `adjointMatrix` is proved where the matrix is defined, in
`GaugeAlgebra.Basis`. All that is needed here is the row orthonormality of the block
belonging to this gauge factor, which is what makes the trace contraction of section C
gauge invariant.

-/

/-- The rows of the `su(2)` block of the adjoint matrix are orthonormal. -/
lemma sum_adjointMatrix_row_mul (g : GaugeGroupI) (c d : Fin 3) :
    ∑ a : Fin 3, GaugeAlgebra.adjointMatrix g (Sum.inr (Sum.inl c)) (Sum.inr (Sum.inl a)) *
      GaugeAlgebra.adjointMatrix g (Sum.inr (Sum.inl d)) (Sum.inr (Sum.inl a))
      = if c = d then 1 else 0 := by
  have h : (GaugeAlgebra.adjointMatrix g * (GaugeAlgebra.adjointMatrix g)ᵀ)
      (Sum.inr (Sum.inl c)) (Sum.inr (Sum.inl d)) = (1 : Matrix (Fin 8 ⊕ Fin 3 ⊕ Fin 1)
        (Fin 8 ⊕ Fin 3 ⊕ Fin 1) ℝ) (Sum.inr (Sum.inl c)) (Sum.inr (Sum.inl d)) := by
    rw [GaugeAlgebra.adjointMatrix_mul_transpose]
  rw [Matrix.mul_apply, Fintype.sum_sum_type] at h
  simpa [Fintype.sum_sum_type, Matrix.one_apply] using h

TODO (lines := 90-102) "Move this to where `adjointMatrix` is
  defined."

/-!

## C. The trace contraction

-/

/-- A sum over families of two `su(2)` adjoint indices is a double sum. -/
lemma sum_pi_two {M : Type*} [AddCommMonoid M] (F : (Fin 2 → Fin 3) → M) :
    ∑ d : Fin 2 → Fin 3, F d = ∑ x : Fin 3, ∑ y : Fin 3, F ![x, y] := by
  rw [show (∑ d : Fin 2 → Fin 3, F d) = ∑ p : Fin 3 × Fin 3, F ![p.1, p.2] from
      Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin 3) _ _ fun d => by
        congr 1
        funext i
        fin_cases i <;> simp,
    Fintype.sum_prod_type]

/-- The trace contraction of a bi-adjoint family: the Kronecker contraction of the two
  `su(2)` adjoint indices. -/
def traceContraction (hT : IsSU2BiAdjoint B repGauge T) : B := ∑ a : Fin 3, T ![a, a]

/-- The trace contraction written as a sum over all pairs of adjoint indices weighted by
  the Kronecker delta. -/
lemma traceContraction_eq_sum (hT : IsSU2BiAdjoint B repGauge T) :
    hT.traceContraction
      = ∑ d : Fin 2 → Fin 3, (if d 0 = d 1 then (1 : ℂ) else 0) • T d := by
  rw [sum_pi_two]
  simp [traceContraction, ite_smul]

/-- The trace contraction lies in the span of the components. -/
lemma traceContraction_mem_span (hT : IsSU2BiAdjoint B repGauge T) :
    hT.traceContraction ∈ hT.span := by
  rw [traceContraction]
  exact sum_mem fun d _ =>
    Submodule.mem_iSup_of_mem _ (Submodule.mem_span_singleton_self _)

/-- The trace contraction of a bi-adjoint family is gauge invariant. -/
lemma repGauge_traceContraction (hT : IsSU2BiAdjoint B repGauge T) (g : GaugeGroupI) :
    repGauge g hT.traceContraction = hT.traceContraction := by
  have step : repGauge g hT.traceContraction
      = ∑ b : Fin 2 → Fin 3, (if b 0 = b 1 then (1 : ℂ) else 0) • T b := by
    show repGauge g (∑ c : Fin 3, T ![c, c]) = _
    rw [map_sum]
    have h1 : ∀ c : Fin 3, repGauge g (T ![c, c])
        = ∑ b : Fin 2 → Fin 3,
          ((GaugeAlgebra.adjointMatrix g (Sum.inr (Sum.inl (b 0))) (Sum.inr (Sum.inl c)) *
            GaugeAlgebra.adjointMatrix g (Sum.inr (Sum.inl (b 1)))
              (Sum.inr (Sum.inl c)) : ℝ) : ℂ) • T b := by
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

TODO (lines := 170-171) "Make a corresponding
  file to this one for IsSU2BiFundamental."

end IsSU2BiAdjoint

/-!

## D. The gauge weight decomposition of the span

The Pauli basis vectors are not eigenvectors of the gauge torus, so the components `T d`
do not carry a definite gauge weight. The eigenvectors appear only after passing to the
weight basis of the `su(2)` adjoint: for the one root direction the two complex
combinations `x₁ ± i x₂` of the paired Pauli coordinates, and the Cartan direction as it
stands. That is three coordinate vectors, recorded in `wtCoeff`, with weights `wtWeight`.

With two adjoint indices a weight vector is a product of two of these, contracted against
`T` by `biVec`, and its weight is the sum of the two individual weights. There are nine
such products, they span the same subspace as the components, and joining their lines one
weight at a time gives `gaugeWeightDecomposition`.

The stronger typeclass assumptions are forced: `GaugeWeightDecomposition` lives in an
algebra and records multiplicativity of the representation, neither of which
`IsSU2BiAdjoint` needs, so both appear as extra arguments here.

-/

namespace IsSU2BiAdjoint

set_option linter.unusedVariables false

/-!

## D.1. The weight basis of the `su(2)` adjoint

-/

/-- The index type of the `su(2)` adjoint weight basis: the positive root, the negative
  root and the Cartan direction. -/
abbrev WeightIdx : Type := Fin 1 ⊕ Fin 1 ⊕ Fin 1

/-- The pair of Pauli indices making up the root direction of `su(2)`. -/
def rootPair : Fin 3 × Fin 3 := (0, 1)

/-- The gauge weight of the `su(2)` root direction. -/
def rootWt : GaugeWeight := (0, 0, 2, 0)

/-- The Pauli index of the Cartan direction of `su(2)`. -/
def cartanId : Fin 3 := 2

/-- The root direction here is the `su(2)` root direction of the full gauge algebra. -/
lemma rootIdx_three :
    GaugeAlgebra.rootIdx 3
      = (Sum.inr (Sum.inl rootPair.1), Sum.inr (Sum.inl rootPair.2)) := rfl

/-- The root weight here is the `su(2)` root weight of the full gauge algebra. -/
lemma rootWeight_three : GaugeAlgebra.rootWeight 3 = rootWt := rfl

/-- The Cartan direction here is the `su(2)` Cartan direction of the full gauge
  algebra. -/
lemma cartanIdx_two : GaugeAlgebra.cartanIdx 2 = Sum.inr (Sum.inl cartanId) := rfl

/-- Every Pauli index is either one of the two members of the root pair or the Cartan
  index. -/
lemma eq_rootPair_or_cartanId (a : Fin 3) :
    a = rootPair.1 ∨ a = rootPair.2 ∨ a = cartanId := by
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

/-- The first column of the root pair: the torus rotates the two columns of the adjoint
  matrix belonging to the root direction into each other. -/
lemma adjointMatrix_rootPair_fst (i : Fin 4) (a : Fin 3) :
    GaugeAlgebra.adjointMatrix (gaugeTorusGen i) (Sum.inr (Sum.inl a))
        (Sum.inr (Sum.inl rootPair.1))
      = ((expI : ℂ) ^ GaugeWeight.coord rootWt i).re *
          (if a = rootPair.1 then 1 else 0)
        - ((expI : ℂ) ^ GaugeWeight.coord rootWt i).im *
          (if a = rootPair.2 then 1 else 0) := by
  obtain ⟨p1, -⟩ := GaugeAlgebra.dualMap_pair_of_entry
    (GaugeAlgebra.coord_rootIdx_fst 3)
    (GaugeAlgebra.coord_rootIdx_snd 3)
    (GaugeAlgebra.rootEntry_adjointMap 3 i)
  simp only [rootIdx_three, rootWeight_three] at p1
  have e := LinearMap.congr_fun p1 (GaugeAlgebra.stdBasis (Sum.inr (Sum.inl a)))
  rw [dualMap_coord_apply] at e
  rw [e]
  simp [Finsupp.single_apply]

/-- The second column of the root pair. -/
lemma adjointMatrix_rootPair_snd (i : Fin 4) (a : Fin 3) :
    GaugeAlgebra.adjointMatrix (gaugeTorusGen i) (Sum.inr (Sum.inl a))
        (Sum.inr (Sum.inl rootPair.2))
      = ((expI : ℂ) ^ GaugeWeight.coord rootWt i).im *
          (if a = rootPair.1 then 1 else 0)
        + ((expI : ℂ) ^ GaugeWeight.coord rootWt i).re *
          (if a = rootPair.2 then 1 else 0) := by
  obtain ⟨-, p2⟩ := GaugeAlgebra.dualMap_pair_of_entry
    (GaugeAlgebra.coord_rootIdx_fst 3)
    (GaugeAlgebra.coord_rootIdx_snd 3)
    (GaugeAlgebra.rootEntry_adjointMap 3 i)
  simp only [rootIdx_three, rootWeight_three] at p2
  have e := LinearMap.congr_fun p2 (GaugeAlgebra.stdBasis (Sum.inr (Sum.inl a)))
  rw [dualMap_coord_apply] at e
  rw [e]
  simp [Finsupp.single_apply]

/-- The torus fixes the Cartan column of the adjoint matrix. -/
lemma adjointMatrix_cartanId (i : Fin 4) (a : Fin 3) :
    GaugeAlgebra.adjointMatrix (gaugeTorusGen i) (Sum.inr (Sum.inl a))
        (Sum.inr (Sum.inl cartanId))
      = if a = cartanId then 1 else 0 := by
  have p := GaugeAlgebra.dualMap_coord_cartanIdx 2 i
  simp only [cartanIdx_two] at p
  have e := LinearMap.congr_fun p (GaugeAlgebra.stdBasis (Sum.inr (Sum.inl a)))
  rw [dualMap_coord_apply] at e
  rw [e]
  simp [Finsupp.single_apply]

/-!

## D.3. The weight vectors of one adjoint index

-/

/-- The coordinates of the `su(2)` adjoint weight basis in the Pauli basis: for the root
  the two combinations `x₁ ± i x₂` of the paired coordinates, and for the Cartan
  direction the coordinate itself. -/
noncomputable def wtCoeff : WeightIdx → Fin 3 → ℂ
  | Sum.inl _, a => (if a = rootPair.1 then 1 else 0)
      + Complex.I * (if a = rootPair.2 then 1 else 0)
  | Sum.inr (Sum.inl _), a => (if a = rootPair.1 then 1 else 0)
      - Complex.I * (if a = rootPair.2 then 1 else 0)
  | Sum.inr (Sum.inr _), a => if a = cartanId then 1 else 0

/-- The gauge weight carried by each `su(2)` adjoint weight vector. -/
def wtWeight : WeightIdx → GaugeWeight
  | Sum.inl _ => rootWt
  | Sum.inr (Sum.inl _) => -rootWt
  | Sum.inr (Sum.inr _) => 0

/-- The coordinate vector of a single Pauli direction. -/
def unitVec (a : Fin 3) : Fin 3 → ℂ := fun x => if x = a then 1 else 0

/-- The action of a gauge transformation on the coordinates of one `su(2)` adjoint
  index. -/
noncomputable def rowAct (g : GaugeGroupI) (c : Fin 3 → ℂ) : Fin 3 → ℂ := fun a =>
  ∑ x : Fin 3, ((GaugeAlgebra.adjointMatrix g (Sum.inr (Sum.inl a))
    (Sum.inr (Sum.inl x)) : ℝ) : ℂ) * c x

/-- Collapsing a sum against the two Kronecker deltas of the root pair. -/
lemma sum_mul_pair (f : Fin 3 → ℂ) (b₁ b₂ : Fin 3) (s : ℂ) :
    ∑ x : Fin 3, f x * ((if x = b₁ then (1 : ℂ) else 0) + s * (if x = b₂ then 1 else 0))
      = f b₁ + s * f b₂ := by
  have h : ∀ x : Fin 3,
      f x * ((if x = b₁ then (1 : ℂ) else 0) + s * (if x = b₂ then 1 else 0))
        = (if x = b₁ then f x else 0) + (if x = b₂ then s * f x else 0) := by
    intro x
    split_ifs <;> ring
  simp only [h]
  simp [Finset.sum_add_distrib]

/-- The complex pair identity behind the positive root eigenvector. -/
lemma pair_add_eq (z u v : ℂ) :
    (z.re : ℂ) * u - (z.im : ℂ) * v + Complex.I * ((z.im : ℂ) * u + (z.re : ℂ) * v)
      = z * (u + Complex.I * v) := by
  conv_rhs => rw [← Complex.re_add_im z]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The complex pair identity behind the negative root eigenvector. -/
lemma pair_sub_eq (z u v : ℂ) :
    (z.re : ℂ) * u - (z.im : ℂ) * v - Complex.I * ((z.im : ℂ) * u + (z.re : ℂ) * v)
      = (starRingEnd ℂ) z * (u - Complex.I * v) := by
  rw [show (starRingEnd ℂ) z = (z.re : ℂ) - (z.im : ℂ) * Complex.I by
    rw [Complex.ext_iff]; simp]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Each weight vector of the `su(2)` adjoint is an eigenvector of every torus generator,
  at the character of its weight. -/
lemma rowAct_wtCoeff (i : Fin 4) (k : WeightIdx) :
    rowAct (gaugeTorusGen i) (wtCoeff k)
      = ((expI : ℂ) ^ GaugeWeight.coord (wtWeight k) i) • wtCoeff k := by
  funext a
  match k with
  | Sum.inl r =>
    show ∑ x : Fin 3, _ = _
    simp only [wtCoeff]
    rw [sum_mul_pair, adjointMatrix_rootPair_fst, adjointMatrix_rootPair_snd]
    simp only [wtCoeff, wtWeight, Pi.smul_apply, smul_eq_mul,
      apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_one, Complex.ofReal_zero,
      Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul]
    exact pair_add_eq _ _ _
  | Sum.inr (Sum.inl r) =>
    show ∑ x : Fin 3, _ = _
    have hneg : ∀ x : Fin 3, wtCoeff (Sum.inr (Sum.inl r)) x
        = (if x = rootPair.1 then (1 : ℂ) else 0)
          + (-Complex.I) * (if x = rootPair.2 then 1 else 0) := by
      intro x
      simp only [wtCoeff]
      ring
    simp only [hneg]
    rw [sum_mul_pair, adjointMatrix_rootPair_fst, adjointMatrix_rootPair_snd]
    simp only [wtWeight, Pi.smul_apply, smul_eq_mul,
      apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_one, Complex.ofReal_zero,
      Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul]
    rw [show ((expI : ℂ) ^ GaugeWeight.coord (-rootWt) i)
        = (starRingEnd ℂ) ((expI : ℂ) ^ GaugeWeight.coord rootWt i) from by
      rw [starRingEnd_expI_zpow, GaugeWeight.coord_neg]]
    simp only [show ∀ x y : ℂ, x + -Complex.I * y = x - Complex.I * y from
      fun x y => by ring]
    exact pair_sub_eq _ _ _
  | Sum.inr (Sum.inr c) =>
    show ∑ x : Fin 3, _ = _
    simp only [wtCoeff, wtWeight, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, adjointMatrix_cartanId, Pi.smul_apply, smul_eq_mul,
      GaugeWeight.zero_coord, zpow_zero,
      apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_one, Complex.ofReal_zero]

/-!

## D.4. The bi-adjoint weight vectors and their span

-/

section Decomposition

variable {B : Type*} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {T : (Fin 2 → Fin 3) → B}

/-- The element of `B` obtained by contracting the two `su(2)` adjoint indices of `T`
  against a pair of coordinate vectors. -/
noncomputable def biVec (hT : IsSU2BiAdjoint B repGauge T) (c₀ c₁ : Fin 3 → ℂ) : B :=
  ∑ d : Fin 2 → Fin 3, (c₀ (d 0) * c₁ (d 1)) • T d

variable (hT : IsSU2BiAdjoint B repGauge T)

/-- Contracting against a scaled coordinate vector on the left. -/
lemma biVec_smul_left (z : ℂ) (c₀ c₁ : Fin 3 → ℂ) :
    hT.biVec (z • c₀) c₁ = z • hT.biVec c₀ c₁ := by
  simp only [biVec, Finset.smul_sum, Pi.smul_apply, smul_eq_mul, smul_smul, mul_assoc]

/-- Contracting against a scaled coordinate vector on the right. -/
lemma biVec_smul_right (z : ℂ) (c₀ c₁ : Fin 3 → ℂ) :
    hT.biVec c₀ (z • c₁) = z • hT.biVec c₀ c₁ := by
  simp only [biVec, Finset.smul_sum, Pi.smul_apply, smul_eq_mul, smul_smul]
  exact Finset.sum_congr rfl fun d _ => by ring_nf

/-- Contracting against a sum of coordinate vectors on the left. -/
lemma biVec_add_left (c₀ c₀' c₁ : Fin 3 → ℂ) :
    hT.biVec (c₀ + c₀') c₁ = hT.biVec c₀ c₁ + hT.biVec c₀' c₁ := by
  simp only [biVec, Pi.add_apply, add_mul, add_smul, Finset.sum_add_distrib]

/-- Contracting against a difference of coordinate vectors on the left. -/
lemma biVec_sub_left (c₀ c₀' c₁ : Fin 3 → ℂ) :
    hT.biVec (c₀ - c₀') c₁ = hT.biVec c₀ c₁ - hT.biVec c₀' c₁ := by
  simp only [biVec, Pi.sub_apply, sub_mul, sub_smul, Finset.sum_sub_distrib]

/-- Contracting against a sum of coordinate vectors on the right. -/
lemma biVec_add_right (c₀ c₁ c₁' : Fin 3 → ℂ) :
    hT.biVec c₀ (c₁ + c₁') = hT.biVec c₀ c₁ + hT.biVec c₀ c₁' := by
  simp only [biVec, Pi.add_apply, mul_add, add_smul, Finset.sum_add_distrib]

/-- Contracting against a difference of coordinate vectors on the right. -/
lemma biVec_sub_right (c₀ c₁ c₁' : Fin 3 → ℂ) :
    hT.biVec c₀ (c₁ - c₁') = hT.biVec c₀ c₁ - hT.biVec c₀ c₁' := by
  simp only [biVec, Pi.sub_apply, mul_sub, sub_smul, Finset.sum_sub_distrib]

/-- Contracting against two single Pauli directions returns a component of `T`. -/
lemma biVec_unitVec (a b : Fin 3) : hT.biVec (unitVec a) (unitVec b) = T ![a, b] := by
  rw [biVec, sum_pi_two]
  simp [unitVec, ite_smul]

/-- Every bi-adjoint weight vector transforms by the product of the two characters. -/
lemma repGauge_biVec (g : GaugeGroupI) (c₀ c₁ : Fin 3 → ℂ) :
    repGauge g (hT.biVec c₀ c₁) = hT.biVec (rowAct g c₀) (rowAct g c₁) := by
  have step : ∀ d : Fin 2 → Fin 3, repGauge g ((c₀ (d 0) * c₁ (d 1)) • T d)
      = ∑ a : Fin 2 → Fin 3,
        ((c₀ (d 0) * c₁ (d 1)) *
          (((GaugeAlgebra.adjointMatrix g (Sum.inr (Sum.inl (a 0)))
              (Sum.inr (Sum.inl (d 0))) : ℝ) : ℂ) *
            ((GaugeAlgebra.adjointMatrix g (Sum.inr (Sum.inl (a 1)))
              (Sum.inr (Sum.inl (d 1))) : ℝ) : ℂ)))
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
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

/-- The bi-adjoint weight vectors are simultaneous eigenvectors of the gauge torus,
  at the character of the sum of the two individual weights. -/
lemma repGauge_biVec_wtCoeff (k₀ k₁ : WeightIdx) (i : Fin 4) :
    repGauge (gaugeTorusGen i) (hT.biVec (wtCoeff k₀) (wtCoeff k₁))
      = ((expI : ℂ) ^ GaugeWeight.coord (wtWeight k₀ + wtWeight k₁) i)
        • hT.biVec (wtCoeff k₀) (wtCoeff k₁) := by
  rw [hT.repGauge_biVec, rowAct_wtCoeff, rowAct_wtCoeff, hT.biVec_smul_left,
    hT.biVec_smul_right, smul_smul, GaugeWeight.coord_add,
    zpow_add₀ expI_ne_zero]

/-- The join of the lines spanned by the bi-adjoint weight vectors. -/
noncomputable def wtSpan (hT : IsSU2BiAdjoint B repGauge T) : Submodule ℂ B :=
  ⨆ k : WeightIdx × WeightIdx, ℂ ∙ hT.biVec (wtCoeff k.1) (wtCoeff k.2)

/-- The Pauli coordinate vector of the first member of the root pair, in the weight
  basis. -/
lemma unitVec_rootPair_fst :
    unitVec rootPair.1
      = (2 : ℂ)⁻¹ • (wtCoeff (Sum.inl 0) + wtCoeff (Sum.inr (Sum.inl 0))) := by
  funext x
  simp only [unitVec, wtCoeff, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The Pauli coordinate vector of the second member of the root pair, in the weight
  basis. -/
lemma unitVec_rootPair_snd :
    unitVec rootPair.2
      = (-(Complex.I / 2)) • (wtCoeff (Sum.inl 0) - wtCoeff (Sum.inr (Sum.inl 0))) := by
  funext x
  simp only [unitVec, wtCoeff, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The Cartan direction is already a weight vector. -/
lemma unitVec_cartanId : unitVec cartanId = wtCoeff (Sum.inr (Sum.inr 0)) := rfl

/-- Contracting a weight vector against a single Pauli direction stays in the join of the
  weight lines. -/
lemma biVec_wtCoeff_unitVec_mem (k : WeightIdx) (b : Fin 3) :
    hT.biVec (wtCoeff k) (unitVec b) ∈ hT.wtSpan := by
  have hgen : ∀ k' : WeightIdx, hT.biVec (wtCoeff k) (wtCoeff k') ∈ hT.wtSpan :=
    fun k' => Submodule.mem_iSup_of_mem (k, k') (Submodule.mem_span_singleton_self _)
  rcases eq_rootPair_or_cartanId b with rfl | rfl | rfl
  · rw [unitVec_rootPair_fst, hT.biVec_smul_right, hT.biVec_add_right]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ (hgen _) (hgen _))
  · rw [unitVec_rootPair_snd, hT.biVec_smul_right, hT.biVec_sub_right]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hgen _) (hgen _))
  · rw [unitVec_cartanId]
    exact hgen _

/-- Every component of `T` lies in the join of the weight lines. -/
lemma biVec_unitVec_mem (a b : Fin 3) :
    hT.biVec (unitVec a) (unitVec b) ∈ hT.wtSpan := by
  rcases eq_rootPair_or_cartanId a with rfl | rfl | rfl
  · rw [unitVec_rootPair_fst, hT.biVec_smul_left, hT.biVec_add_left]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _
      (hT.biVec_wtCoeff_unitVec_mem _ _) (hT.biVec_wtCoeff_unitVec_mem _ _))
  · rw [unitVec_rootPair_snd, hT.biVec_smul_left, hT.biVec_sub_left]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (hT.biVec_wtCoeff_unitVec_mem _ _) (hT.biVec_wtCoeff_unitVec_mem _ _))
  · rw [unitVec_cartanId]
    exact hT.biVec_wtCoeff_unitVec_mem _ _

/-- The weight vectors span the components. The change of basis from the Pauli basis
  to the weight basis is invertible, so nothing is lost. -/
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

/-- The gauge weight decomposition of the span of a bi-adjoint `su(2)` family. The
  span is the join of the lines through the nine products of weight vectors, and each of
  those carries the sum of the two weights. -/
@[implicit_reducible]
noncomputable def gaugeWeightDecomposition (hT : IsSU2BiAdjoint B repGauge T)
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

/-- The gauge weights carried by a bi-adjoint `su(2)` family: the five weights of the
  tensor square of the `su(2)` adjoint. Every one of them has vanishing colour and
  hypercharge, since the family carries weak isospin only. -/
lemma gaugeWeightDecomposition_supp (hmul : IsMulRep repGauge) :
    (hT.gaugeWeightDecomposition hmul).supp
      = {((0, 0, 0, 0) : GaugeWeight), (0, 0, 4, 0), (0, 0, 2, 0), (0, 0, -2, 0),
        (0, 0, -4, 0)} := by
  rw [hT.gaugeWeightDecomposition_supp_eq hmul]
  decide

/-- The trace contraction lies in the zero-weight piece. It is gauge invariant, so in
  particular the torus fixes it. -/
lemma traceContraction_mem_piece_zero (hmul : IsMulRep repGauge) :
    hT.traceContraction ∈ (hT.gaugeWeightDecomposition hmul).piece 0 :=
  GaugeWeightDecomposition.mem_zero_of_invariant _ hT.traceContraction_mem_span
    hT.repGauge_traceContraction

end Decomposition

end IsSU2BiAdjoint

end StandardModel
