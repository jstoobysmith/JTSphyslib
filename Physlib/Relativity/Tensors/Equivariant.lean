/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.Basic
public import Physlib.Mathematics.InvariantReduction
/-!
# Equivariant maps out of the tensors of a species

## i. Overview

A family of vectors in a representation `ρ` of the group `G` of a tensor species `S`, carrying
indices of colors `c`, is packaged as a linear map `f : S.Tensor c →ₗ[k] B`, and
`S.IsEquivariant c ρ f` says that `f` intertwines the action of `G` on tensors with `ρ` (A).

Over `ℂ`, the invariants in the range of such a map come from invariant tensors (C): every
invariant of `LinearMap.range f ⊔ W`, for `W` a `G`-stable submodule, is `f t + y` with `t` an
invariant tensor and `y ∈ W`. This holds whenever the colors are closed under adjoints (B): for
every `g` some `g'` acts on each color by the conjugate transpose of the matrix of `g`. The
classification of the invariants in the range of `f` is thereby reduced to that of the invariant
tensors of `S.Tensor c`, `IsEquivariant.invariantReductionToSpan`.

A map is specified by its values on the basis tensors with `Basis.constr`, and
`isEquivariant_constr` turns a transformation law of those values into equivariance (D).

## ii. Key results

- `TensorSpecies.IsEquivariant` : equivariant linear maps out of `S.Tensor c`.
- `TensorSpecies.smul_basis_eq_sum` : the action on the basis tensors.
- `TensorSpecies.IsAdjointClosed` : the colors are closed under conjugate transposition.
- `TensorSpecies.IsEquivariant.exists_invariant_add_of_mem_sup` : invariants of the range come from
  invariant tensors.
- `TensorSpecies.IsEquivariant.invariantReductionToSpan` : the reduction to one invariant tensor.

## iii. Table of contents

- A. Equivariant maps and the action on basis tensors
- B. Colors closed under adjoints
- C. Invariants in the range come from invariant tensors
- D. Building equivariant maps

-/

@[expose] public section

namespace TensorSpecies

open Module Matrix Tensor

/-!

## A. Equivariant maps and the action on basis tensors

-/

section General

variable {k : Type} [CommRing k] {C G : Type} [Group G]
  {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
  {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
  {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}

/-- A linear map `f` from the tensors of the species `S` with index colors `c` to a
  representation `ρ` of the group of the species, which is equivariant: it intertwines the action
  of the group on tensors with `ρ`. -/
structure IsEquivariant (S : TensorSpecies k C G V basisIdx rep b) {n : ℕ} (c : Fin n → C)
    {B : Type*} [AddCommMonoid B] [Module k B] (ρ : Representation k G B)
    (f : S.Tensor c →ₗ[k] B) : Prop where
  equivariant : ∀ (g : G) (t : S.Tensor c), f (g • t) = ρ g (f t)

variable {S : TensorSpecies k C G V basisIdx rep b}

/-- The action of `g` on a basis tensor: the coefficient of `e_ψ` in `g • e_φ` is the product over
  the indices of the matrix entries of `g` in the color of that index. -/
lemma smul_basis_eq_sum {n : ℕ} (c : Fin n → C) (g : G) (φ : ComponentIdx (S := S) c) :
    g • Tensor.basis (S := S) c φ
      = ∑ ψ : ComponentIdx (S := S) c,
        (∏ i, LinearMap.toMatrix (b (c i)) (b (c i)) (rep (c i) g) (ψ i) (φ i)) •
        Tensor.basis (S := S) c ψ := by
  simp only [Tensor.basis_apply, LinearMap.toMatrix_apply]
  rw [actionT_pure]
  have h : g • Pure.basisVector (S := S) c φ
      = (fun i => ∑ j, (b (c i)).repr (rep (c i) g (b (c i) (φ i))) j • b (c i) j :
        Pure S c) := by
    funext i
    exact ((b (c i)).sum_repr _).symm
  rw [h]
  unfold Pure.toTensor
  rw [MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [← MultilinearMap.map_smul_univ]
  rfl

/-- The components of `g • t`: the matrix of products of the matrix entries of `g`, one factor
  per index, applied to the components of `t`. -/
lemma basis_repr_smul {n : ℕ} (c : Fin n → C) (g : G) (t : S.Tensor c)
    (φ : ComponentIdx (S := S) c) :
    (Tensor.basis c).repr (g • t) φ
      = ∑ ψ, (∏ i, LinearMap.toMatrix (b (c i)) (b (c i)) (rep (c i) g) (φ i) (ψ i)) *
        (Tensor.basis c).repr t ψ := by
  conv_lhs => rw [← (Tensor.basis (S := S) c).sum_repr t]
  rw [actionT_eq, map_sum, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  congr 1
  have h := smul_basis_eq_sum c g ψ
  rw [actionT_eq] at h
  rw [h, map_sum]
  simp [Finsupp.single_apply]

namespace IsEquivariant

variable {n : ℕ} {c : Fin n → C} {B : Type*} [AddCommGroup B] [Module k B]
  {ρ : Representation k G B} {f : S.Tensor c →ₗ[k] B} (hf : S.IsEquivariant c ρ f)

include hf in
/-- The range of an equivariant map is stable under the group. -/
lemma isStableUnder_range : IsStableUnder (fun g : G => ρ g) (LinearMap.range f) := by
  rintro g _ ⟨t, rfl⟩
  exact ⟨g • t, hf.equivariant g t⟩

include hf in
/-- The image of an invariant tensor under an equivariant map is invariant. -/
lemma rep_map_of_invariant {t : S.Tensor c} (ht : ∀ g : G, g • t = t) (g : G) :
    ρ g (f t) = f t := by
  rw [← hf.equivariant, ht]

/-- A sum of equivariant maps is equivariant. -/
lemma sum {ι : Type*} (s : Finset ι) {F : ι → S.Tensor c →ₗ[k] B}
    (hF : ∀ i ∈ s, S.IsEquivariant c ρ (F i)) : S.IsEquivariant c ρ (∑ i ∈ s, F i) where
  equivariant g t := by
    rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun i hi => (hF i hi).equivariant g t

include hf in
/-- A difference of equivariant maps is equivariant. -/
lemma sub {f' : S.Tensor c →ₗ[k] B} (hf' : S.IsEquivariant c ρ f') :
    S.IsEquivariant c ρ (f - f') where
  equivariant g t := by
    rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, hf.equivariant, hf'.equivariant]

end IsEquivariant

end General

/-!

## B. Colors closed under adjoints

-/

section Complex

variable {C G : Type} [Group G]
  {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module ℂ (V c)]
  {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
  {rep : (c : C) → Representation ℂ G (V c)} {b : (c : C) → Basis (basisIdx c) ℂ (V c)}

set_option linter.unusedVariables false in
/-- The colors `c` of a complex species are closed under adjoints when for every `g` some `g'`
  acts on each of them by the conjugate transpose of the matrix of `g`. For a unitary group
  `g' = g⁻¹` and orthonormal bases; for `SL(2,ℂ)` on the Weyl colors, `g' = g†`. -/
@[nolint unusedArguments]
def IsAdjointClosed (S : TensorSpecies ℂ C G V basisIdx rep b) {n : ℕ} (c : Fin n → C) :
    Prop :=
  ∀ g : G, ∃ g' : G, ∀ i,
    LinearMap.toMatrix (b (c i)) (b (c i)) (rep (c i) g')
      = (LinearMap.toMatrix (b (c i)) (b (c i)) (rep (c i) g))ᴴ

/-!

## C. Invariants in the range come from invariant tensors

-/

namespace IsEquivariant

variable {S : TensorSpecies ℂ C G V basisIdx rep b} {n : ℕ} {c : Fin n → C} {B : Type*}
  [AddCommGroup B] [Module ℂ B] {ρ : Representation ℂ G B} {f : S.Tensor c →ₗ[ℂ] B}
  (hf : S.IsEquivariant c ρ f)

include hf in
/-- An invariant in the range of `f` is the image of an invariant tensor, when the colors are
  closed under adjoints: the adjoint of the action of `g` on the coefficients is that of `g'`. -/
lemma exists_invariant_eq_of_mem_range (hc : S.IsAdjointClosed c) {x : B}
    (hx : x ∈ LinearMap.range f) (hinv : ∀ g : G, ρ g x = x) :
    ∃ t : S.Tensor c, (∀ g : G, g • t = t) ∧ f t = x := by
  rw [LinearMap.range_eq_span_range_basis (Tensor.basis c)] at hx
  obtain ⟨a, rfl, ha⟩ := Fintype.exists_mulVec_eq_of_conjTranspose_mem
    (fun ψ => f (Tensor.basis c ψ)) (fun g => ρ g)
    (fun g => Matrix.of fun ψ φ => ∏ i, LinearMap.toMatrix (b (c i)) (b (c i))
      (rep (c i) g) (ψ i) (φ i))
    (fun g φ => by
      rw [← hf.equivariant, smul_basis_eq_sum, map_sum]
      exact Finset.sum_congr rfl fun ψ _ => map_smul _ _ _)
    (fun g => by
      obtain ⟨g', hg'⟩ := hc g
      refine ⟨g', Matrix.ext fun ψ φ => ?_⟩
      simp only [Matrix.of_apply, Matrix.conjTranspose_apply, star_prod]
      exact Finset.prod_congr rfl fun i _ => by rw [hg' i]; rfl) hx hinv
  refine ⟨∑ ψ, a ψ • Tensor.basis c ψ, fun g => ?_, by simp [map_sum]⟩
  apply (Tensor.basis (S := S) c).repr.injective
  ext φ
  rw [basis_repr_smul, Module.Basis.repr_sum_self]
  conv_rhs => rw [← ha g]
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]

include hf in
/-- An invariant of `LinearMap.range f ⊔ W`, for `W` a stable submodule, is the image of an
  invariant tensor plus an element of `W`. -/
lemma exists_invariant_add_of_mem_sup (hc : S.IsAdjointClosed c) (W : Submodule ℂ B)
    (hW : ∀ g : G, ∀ y ∈ W, ρ g y ∈ W) {x : B} (hx : x ∈ LinearMap.range f ⊔ W)
    (hinv : ∀ g : G, ρ g x = x) :
    ∃ t : S.Tensor c, (∀ g : G, g • t = t) ∧ ∃ y ∈ W, x = f t + y := by
  have hq : S.IsEquivariant c (ρ.quotient W fun g y hy => hW g y hy) (W.mkQ ∘ₗ f) :=
    ⟨fun g t => by
      simp only [LinearMap.comp_apply]
      rw [hf.equivariant]
      rfl⟩
  obtain ⟨t, ht, hft⟩ := hq.exists_invariant_eq_of_mem_range hc (x := W.mkQ x) (by
      rw [LinearMap.range_comp]
      have h := Submodule.mem_map_of_mem (f := W.mkQ) hx
      rwa [Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq] at h)
    (fun g => by
      change W.mkQ (ρ g x) = W.mkQ x
      rw [hinv])
  exact ⟨t, ht, x - f t, (Submodule.Quotient.eq W).1 hft.symm, by abel⟩

include hf in
/-- When the invariant tensors of `S.Tensor c` are the multiples of one tensor `t₀`, the
  invariants of the range of `f` reduce to the span of `f t₀`. -/
noncomputable def invariantReductionToSpan (hc : S.IsAdjointClosed c) (t₀ : S.Tensor c)
    (ht₀ : ∀ g : G, g • t₀ = t₀)
    (hclass : ∀ t : S.Tensor c, (∀ g : G, g • t = t) → ∃ a : ℂ, t = a • t₀) :
    InvariantReductionToSpan (fun g : G => ρ g) (LinearMap.range f) where
  spanningVector := f t₀
  stable := hf.isStableUnder_range
  spanningVector_fixed := hf.rep_map_of_invariant ht₀
  reduce W hW _ hx hinv := by
    obtain ⟨t, ht, y, hy, rfl⟩ := hf.exists_invariant_add_of_mem_sup hc W hW hx hinv
    obtain ⟨a, rfl⟩ := hclass t ht
    exact ⟨a, y, hy, by rw [map_smul]⟩

end IsEquivariant

end Complex

/-!

## D. Building equivariant maps

-/

section Constr

variable {k : Type} [CommRing k] {C G : Type} [Group G]
  {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
  {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
  {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Basis (basisIdx c) k (V c)}
  {S : TensorSpecies k C G V basisIdx rep b}

/-- The linear map with prescribed values `T ψ` on the basis tensors is equivariant when the
  values are moved by `ρ` as the basis tensors are moved by the group. -/
lemma isEquivariant_constr {n : ℕ} {c : Fin n → C} {B : Type*} [AddCommGroup B] [Module k B]
    {ρ : Representation k G B} (T : ComponentIdx (S := S) c → B)
    (hT : ∀ (g : G) φ, ρ g (T φ)
      = ∑ ψ, (∏ i, LinearMap.toMatrix (b (c i)) (b (c i)) (rep (c i) g) (ψ i) (φ i)) • T ψ) :
    S.IsEquivariant c ρ ((Tensor.basis c).constr k T) where
  equivariant g t := by
    have h : (Tensor.basis c).constr k T ∘ₗ PiTensorProduct.map (fun i => rep (c i) g)
        = ρ g ∘ₗ (Tensor.basis c).constr k T := by
      refine (Tensor.basis (S := S) c).ext fun φ => ?_
      have h1 := smul_basis_eq_sum (S := S) c g φ
      rw [actionT_eq] at h1
      simp only [LinearMap.comp_apply, h1, map_sum, map_smul, Module.Basis.constr_basis, hT]
    exact LinearMap.congr_fun h t

end Constr

end TensorSpecies
