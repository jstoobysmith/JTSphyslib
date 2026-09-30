/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.SU.Invariants.Basic
public import Physlib.Relativity.Tensors.UnitTensor
/-!
# Invariants of one and of two adjoint indices of `SU(N)`

## i. Overview

A tensor with one adjoint index is a traceless matrix `A`, moved by `g` to `g A g⁻¹`. An invariant
one commutes with every element of `SU(N)`, so it is scalar (`SU.eq_smul_one_of_commute`), and
being traceless it is zero (A).

A tensor with two adjoint indices has a matrix of components `C` in the Gell-Mann basis, moved by
`g` to `M C Mᵀ`, where `M` is the matrix of the adjoint action of `g`. That matrix is real and
`Mᵀ` is the matrix of `g⁻¹`, so the components of an invariant tensor are the matrix of an
endomorphism of the traceless matrices commuting with the adjoint action. By
`suTensor.eq_smul_id_of_commute_adjRep` that endomorphism is scalar, and the invariant tensors are
the multiples of the unit tensor of the adjoint color, `∑ λ_a ⊗ λ_a / 2` (B).

For equivariant maps out of these tensors the invariants of the range reduce to `⊥` for one
adjoint index and to the image of the unit tensor for two (C). Families indexed by the Gell-Mann
labels are turned into maps by `adjMap` and `adjPairMap`, and for two indices the image of twice
the unit tensor is the trace contraction `∑ a, T ![a, a]` (D).

## ii. Key results

- `suTensor.eq_zero_of_invariant_adj` : an invariant tensor with one adjoint index is zero.
- `suTensor.exists_eq_smul_unitTensor_of_invariant_adjPair` : an invariant tensor with two adjoint
  indices is a multiple of the unit tensor.
- `suTensor.invariantReductionToTrace` : the reduction of the invariants of the span of a family
  with two adjoint indices to the trace contraction.

## iii. Table of contents

- A. One adjoint index
- B. Two adjoint indices
- C. The invariants of equivariant maps
- D. Maps from components

-/

@[expose] public section

namespace suTensor

open Matrix MatrixGroups TensorSpecies Tensor SU

variable {N : ℕ}

/-!

## A. One adjoint index

-/

/-- An invariant traceless matrix is zero: it commutes with every element of `SU(N)`, so it is a
  scalar, and its trace vanishes. -/
lemma eq_zero_of_adjRep_eq_self {A : AdjointModule N} (hA : ∀ g : SU N, adjRep N g A = A) :
    A = 0 := by
  obtain ⟨z, hz⟩ := eq_smul_one_of_commute (C := A.1) fun g => by
    have h := congrArg Subtype.val (hA g)
    rw [adjRep_apply_val] at h
    conv_rhs => rw [← h]
    simp only [Matrix.mul_assoc, val_inv_mul_val, Matrix.mul_one]
  have htr : (A.1).trace = 0 := A.2
  rw [hz, trace_smul, trace_one, smul_eq_mul, mul_eq_zero, Fintype.card_fin] at htr
  ext1
  rcases htr with rfl | hN
  · rw [hz, zero_smul]
    rfl
  · have : IsEmpty (Fin N) := by
      rw [Fin.isEmpty_iff]
      exact_mod_cast hN
    exact Subsingleton.elim _ _

/-- An invariant tensor with one adjoint index is zero. -/
lemma eq_zero_of_invariant_adj (t : SuT[N, .adj]) (ht : ∀ g : SU N, g • t = t) : t = 0 := by
  obtain ⟨A, rfl⟩ := (fromSingleT (S := suTensor N) (c := .adj)).surjective t
  have hA : ∀ g : SU N, adjRep N g A = A := fun g =>
    (fromSingleT (S := suTensor N) (c := .adj)).injective
      ((actionT_fromSingleT (S := suTensor N) A g).symm.trans (ht g))
  rw [eq_zero_of_adjRep_eq_self hA, map_zero]

/-!

## B. Two adjoint indices

-/

/-- The matrix of the adjoint action of `g` in the Gell-Mann basis. -/
noncomputable abbrev adjMatrix (g : SU N) : Matrix (GellMann.Index N) (GellMann.Index N) ℂ :=
  LinearMap.toMatrix GellMann.basis GellMann.basis (adjRep N g)

/-- The matrix of the adjoint action is real, the Gell-Mann matrices being hermitian. -/
lemma star_adjMatrix_apply (g : SU N) (a b : GellMann.Index N) :
    star (adjMatrix g a b) = adjMatrix g a b := by
  simp only [adjMatrix]
  rw [toMatrix_adjRep_apply, star_div₀, ← trace_conjTranspose]
  simp only [conjTranspose_mul, GellMann.conjTranspose_matrix, val_inv, star_eq_conjTranspose,
    conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [show star (2 : ℂ) = 2 by simp, trace_mul_comm g.1]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (GellMann.matrix b), trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- The matrix of the adjoint action of `g⁻¹` is the transpose of that of `g`. -/
lemma adjMatrix_inv (g : SU N) : adjMatrix g⁻¹ = (adjMatrix g)ᵀ := by
  rw [adjMatrix, toMatrix_rep_inv N .adj g]
  ext a b
  exact star_adjMatrix_apply g b a

/-- The component indices of a tensor with two adjoint indices, as the pair of their Gell-Mann
  labels. -/
def adjPairIdx : ComponentIdx (S := suTensor N) ![.adj, .adj] ≃ (Fin 2 → GellMann.Index N) where
  toFun v := ![v 0, v 1]
  invFun v := fun | 0 => v 0 | 1 => v 1
  left_inv v := by
    funext x
    fin_cases x <;> rfl
  right_inv v := by
    funext x
    fin_cases x <;> rfl

/-- The components of `g • t` for a tensor with two adjoint indices: the matrix of components
  `C` is moved to `M C Mᵀ`. -/
lemma basis_repr_smul_adjPair (g : SU N) (t : SuT[N, .adj, .adj])
    (n : Fin 2 → GellMann.Index N) :
    (Tensor.basis _).repr (g • t) (adjPairIdx.symm n)
      = ∑ x, ∑ y, adjMatrix g (n 0) x * adjMatrix g (n 1) y
        * (Tensor.basis _).repr t (adjPairIdx.symm ![x, y]) := by
  rw [basis_repr_smul, ← adjPairIdx.symm.sum_comp, ← (finTwoArrowEquiv _).symm.sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [Fin.prod_univ_two]
  rfl

variable (N) in
/-- The unit tensor of the adjoint color, `∑ λ_a ⊗ λ_a / 2`, with two adjoint indices. -/
noncomputable def adjUnitTensor : SuT[N, .adj, .adj] := unitTensor (S := suTensor N) .adj

/-- The unit tensor of the adjoint color is invariant. -/
lemma adjUnitTensor_invariant (g : SU N) : g • adjUnitTensor N = adjUnitTensor N :=
  actionT_fromConstPair ((suTensor N).unit .adj) g

/-- The components of the unit tensor of the adjoint color: `δ / 2`, the Gell-Mann matrices
  being orthogonal with `tr (λ_a λ_b) = 2 δ_ab`. -/
lemma basis_repr_adjUnitTensor (n : Fin 2 → GellMann.Index N) :
    (Tensor.basis _).repr (adjUnitTensor N) (adjPairIdx.symm n)
      = if n 0 = n 1 then 1 / 2 else 0 := by
  refine (unitTensor_basis_repr (S := suTensor N) .adj (adjPairIdx.symm n)).trans ?_
  change (Module.Basis.tensorProduct GellMann.basis GellMann.basis).repr
    ((1 : ℂ) • adjUnitVal N) (n 0, n 1) = _
  simp only [one_smul, adjUnitVal, map_sum, Module.Basis.tensorProduct_repr_tmul_apply,
    Finsupp.coe_finsetSum, Finset.sum_apply, Module.Basis.repr_self, GellMann.basis_repr_apply]
  rw [Finset.sum_eq_single (n 0) (fun x _ hx => by simp [hx]) (by simp),
    Finsupp.single_eq_same, smul_eq_mul, mul_one]
  have h := LinearMap.BilinForm.apply_dualBasis_right (traceForm_nondegenerate N)
    (traceForm_isSymm N) GellMann.basis (n 1) (n 0)
  rw [traceForm_apply, GellMann.basis_apply_val] at h
  rw [h]
  by_cases h01 : n 0 = n 1
  · simp [h01]
  · simp [h01, Ne.symm h01]

/-- The matrix of the adjoint action of `g⁻¹` times that of `g` is the identity. -/
lemma adjMatrix_inv_mul (g : SU N) : adjMatrix g⁻¹ * adjMatrix g = 1 := by
  rw [adjMatrix, adjMatrix, ← LinearMap.toMatrix_mul, ← map_mul, inv_mul_cancel, map_one,
    LinearMap.toMatrix_one]

/-- An invariant tensor with two adjoint indices is a multiple of the unit tensor of the adjoint
  color. Its matrix of components commutes with the matrices of the adjoint action, so it is the
  matrix of an endomorphism commuting with the adjoint action, which is scalar. -/
lemma exists_eq_smul_adjUnitTensor_of_invariant (t : SuT[N, .adj, .adj])
    (ht : ∀ g : SU N, g • t = t) : ∃ a : ℂ, t = a • adjUnitTensor N := by
  set C : Matrix (GellMann.Index N) (GellMann.Index N) ℂ :=
    Matrix.of fun a b => (Tensor.basis _).repr t (adjPairIdx.symm ![a, b])
  have hconj : ∀ g : SU N, adjMatrix g * C * (adjMatrix g)ᵀ = C := fun g => by
    ext a b
    have h := basis_repr_smul_adjPair g t ![a, b]
    rw [ht] at h
    simp only [Matrix.mul_apply, transpose_apply, Finset.sum_mul, C, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine (Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_).trans h.symm
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  have hcomm : ∀ g : SU N, C * adjMatrix g = adjMatrix g * C := fun g => by
    conv_lhs => rw [← hconj g, ← adjMatrix_inv]
    rw [Matrix.mul_assoc, adjMatrix_inv_mul, Matrix.mul_one]
  set L := Matrix.toLin GellMann.basis GellMann.basis C
  obtain ⟨μ, hμ⟩ := eq_smul_id_of_commute_adjRep (L := L) fun g A => by
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply (adjRep N g)]
    congr 1
    apply (LinearMap.toMatrix GellMann.basis GellMann.basis).injective
    rw [LinearMap.toMatrix_comp _ GellMann.basis, LinearMap.toMatrix_comp _ GellMann.basis,
      LinearMap.toMatrix_toLin]
    exact hcomm g
  have hC : C = μ • 1 := by
    have hLC : LinearMap.toMatrix GellMann.basis GellMann.basis L = C :=
      LinearMap.toMatrix_toLin _ _ C
    rw [← hLC, hμ, map_smul, LinearMap.toMatrix_id]
  refine ⟨2 * μ, (Tensor.basis _).repr.injective (Finsupp.ext fun φ => ?_)⟩
  obtain ⟨n, rfl⟩ := adjPairIdx.symm.surjective φ
  rw [map_smul, Finsupp.smul_apply, basis_repr_adjUnitTensor, smul_eq_mul]
  have h := congrFun (congrFun hC (n 0)) (n 1)
  simp only [C, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h
  rw [show (![n 0, n 1] : Fin 2 → GellMann.Index N) = n from by funext i; fin_cases i <;> rfl]
    at h
  rw [h]
  split_ifs <;> ring

/-!

## C. The invariants of equivariant maps

-/

variable {B : Type*} [AddCommGroup B] [Module ℂ B] {ρ : Representation ℂ (SU N) B}

/-- For an equivariant map out of the tensors with one adjoint index, the invariants of the range
  reduce to `⊥`. -/
lemma reducesInvariantsTo_bot_of_isEquivariant_adj {f : SuT[N, .adj] →ₗ[ℂ] B}
    (hf : (suTensor N).IsEquivariant ![.adj] ρ f) :
    ReducesInvariantsTo (fun g : SU N => ρ g) (LinearMap.range f) ⊥ :=
  hf.reducesInvariantsTo_bot (isAdjointClosed N _) eq_zero_of_invariant_adj

/-- For an equivariant map `f` out of the tensors with two adjoint indices, the invariants of the
  range reduce to the span of the image of the unit tensor. -/
noncomputable def invariantReductionToAdjUnitImage {f : SuT[N, .adj, .adj] →ₗ[ℂ] B}
    (hf : (suTensor N).IsEquivariant ![.adj, .adj] ρ f) :
    InvariantReductionToSpan (fun g : SU N => ρ g) (LinearMap.range f) :=
  hf.invariantReductionToSpan (isAdjointClosed N _) (adjUnitTensor N) adjUnitTensor_invariant
    exists_eq_smul_adjUnitTensor_of_invariant

/-!

## D. Maps from components

-/

/-- The component indices of a tensor with one adjoint index, as its Gell-Mann label. -/
def adjIdx : ComponentIdx (S := suTensor N) ![.adj] ≃ GellMann.Index N where
  toFun v := v 0
  invFun a := fun | 0 => a
  left_inv v := by
    funext x
    fin_cases x
    rfl
  right_inv a := rfl

/-- The linear map out of the tensors with one adjoint index sending the basis tensor with label
  `a` to `T a`. -/
noncomputable def adjMap (T : GellMann.Index N → B) : SuT[N, .adj] →ₗ[ℂ] B :=
  familyMap adjIdx T

/-- A linear map moving a family indexed by one adjoint label by the matrix of the adjoint action
  of `g` intertwines the map of the family with the action of `g`. -/
lemma adjMap_smul_of_law (T : GellMann.Index N → B) {σ : B →ₗ[ℂ] B} (g : SU N)
    (hσ : ∀ a : GellMann.Index N, σ (T a) = ∑ b, adjMatrix g b a • T b) (t : SuT[N, .adj]) :
    σ (adjMap T t) = adjMap T (g • t) :=
  familyMap_smul_of_law _ T g (fun a => (hσ a).trans <|
    Finset.sum_congr rfl fun b _ => by rw [Fin.prod_univ_one]; rfl) t

/-- The map of a family indexed by one adjoint label is equivariant when the family moves by the
  matrix of the adjoint action, the summed label first. -/
lemma isEquivariant_adjMap (T : GellMann.Index N → B)
    (hT : ∀ (g : SU N) (a : GellMann.Index N), ρ g (T a) = ∑ b, adjMatrix g b a • T b) :
    (suTensor N).IsEquivariant ![.adj] ρ (adjMap T) :=
  ⟨fun g t => (adjMap_smul_of_law T g (hT g) t).symm⟩

/-- For a family indexed by one adjoint label whose map is equivariant, the invariants of the
  span of the family reduce to `⊥`. -/
lemma reducesInvariantsTo_bot_span_of_adjMap {T : GellMann.Index N → B}
    (hT : (suTensor N).IsEquivariant ![.adj] ρ (adjMap T)) :
    ReducesInvariantsTo (fun g : SU N => ρ g) (Submodule.span ℂ (Set.range T)) ⊥ := by
  rw [← range_familyMap adjIdx T]
  exact reducesInvariantsTo_bot_of_isEquivariant_adj hT

/-- The linear map out of the tensors with two adjoint indices sending the basis tensor with
  labels `n` to `T n`. -/
noncomputable def adjPairMap (T : (Fin 2 → GellMann.Index N) → B) :
    SuT[N, .adj, .adj] →ₗ[ℂ] B :=
  familyMap adjPairIdx T

/-- The map of a family sends twice the unit tensor to the trace contraction `∑ a, T ![a, a]`. -/
lemma adjPairMap_two_smul_adjUnitTensor (T : (Fin 2 → GellMann.Index N) → B) :
    adjPairMap T ((2 : ℂ) • adjUnitTensor N) = ∑ a, T ![a, a] := by
  conv_lhs => rw [← (Tensor.basis _).sum_repr (adjUnitTensor N)]
  rw [Finset.smul_sum, map_sum, ← adjPairIdx.symm.sum_comp, ← (finTwoArrowEquiv _).symm.sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a]
  · simp [adjPairMap, basis_repr_adjUnitTensor, smul_smul]
  · intro b _ hb
    simp [adjPairMap, basis_repr_adjUnitTensor, Ne.symm hb]
  · simp

/-- A linear map moving a family indexed by two adjoint labels by the matrix of the adjoint
  action of `g` on each label intertwines the map of the family with the action of `g`. -/
lemma adjPairMap_smul_of_law (T : (Fin 2 → GellMann.Index N) → B) {σ : B →ₗ[ℂ] B} (g : SU N)
    (hσ : ∀ l : Fin 2 → GellMann.Index N, σ (T l)
      = ∑ a : Fin 2 → GellMann.Index N, (adjMatrix g (a 0) (l 0) * adjMatrix g (a 1) (l 1)) • T a)
    (t : SuT[N, .adj, .adj]) :
    σ (adjPairMap T t) = adjPairMap T (g • t) :=
  familyMap_smul_of_law _ T g (fun l => (hσ l).trans <|
    Finset.sum_congr rfl fun a _ => by rw [Fin.prod_univ_two]; rfl) t

/-- The map of a family indexed by two adjoint labels is equivariant when the family moves by the
  matrix of the adjoint action on each label, the summed label first. -/
lemma isEquivariant_adjPairMap (T : (Fin 2 → GellMann.Index N) → B)
    (hT : ∀ (g : SU N) (l : Fin 2 → GellMann.Index N), ρ g (T l)
      = ∑ a : Fin 2 → GellMann.Index N, (adjMatrix g (a 0) (l 0) * adjMatrix g (a 1) (l 1)) • T a) :
    (suTensor N).IsEquivariant ![.adj, .adj] ρ (adjPairMap T) :=
  ⟨fun g t => (adjPairMap_smul_of_law T g (hT g) t).symm⟩

/-- For a family indexed by two adjoint labels whose map is equivariant, the invariants of the
  span of the family reduce to the span of the trace contraction `∑ a, T ![a, a]`. -/
noncomputable def invariantReductionToTrace {T : (Fin 2 → GellMann.Index N) → B}
    (hT : (suTensor N).IsEquivariant ![.adj, .adj] ρ (adjPairMap T)) :
    InvariantReductionToSpan (fun g : SU N => ρ g) (Submodule.span ℂ (Set.range T)) :=
  hT.invariantReductionToSpanOfEq (isAdjointClosed N _) ((2 : ℂ) • adjUnitTensor N)
    (fun g => by rw [smul_comm, adjUnitTensor_invariant])
    (fun t ht => by
      obtain ⟨a, rfl⟩ := exists_eq_smul_adjUnitTensor_of_invariant t ht
      exact ⟨a / 2, by rw [smul_smul, div_mul_cancel₀ a two_ne_zero]⟩)
    (range_familyMap _ T) _ (adjPairMap_two_smul_adjUnitTensor T)

end suTensor
