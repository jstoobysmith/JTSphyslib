/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Invariants.LorentzCovariance
public import Physlib.Relativity.Tensors.ComplexTensor.Metrics.Basic
public import Physlib.Mathematics.InvariantReduction
/-!
# Lorentz-equivariant maps out of complex Lorentz tensors

A family of vectors in a representation `repLorentz` of `SL(2,ℂ)` on `B`, carrying Lorentz
indices of colours `c`, is packaged as a linear map `f : ℂT(c) →ₗ[ℂ] B` out of the complex
Lorentz tensors with those indices, and `IsLorentzEquivariant c B repLorentz f` says that `f`
intertwines the action on tensors with `repLorentz` (A).

The invariants in the range of such a map come from invariant tensors (C): every Lorentz
invariant of `LinearMap.range f ⊔ S`, for `S` a Lorentz-stable submodule, is `f t + y` with `t`
an invariant tensor and `y ∈ S`. This holds whenever each colour `c i` is dagger compatible (B),
that is the matrix of `g†` is the conjugate transpose of the matrix of `g`, which is proved for
the four Weyl colours. The classification of the invariants in the range of `f` is thereby
reduced to that of the invariant tensors of `ℂT(c)`.

A map is specified by its values on the basis tensors with `Basis.constr`, and
`isLorentzEquivariant_constr` turns a transformation law of those values into equivariance (D).
-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups SL2C Invariants TensorSpecies Tensor complexLorentzTensor

/-!

## A. Equivariant maps and the action on basis tensors

-/

/-- A linear map `f` from the complex Lorentz tensors with index colours `c` to a representation
  `repLorentz` of `SL(2,ℂ)` on `B`, which is equivariant: it intertwines the action of
  `SL(2,ℂ)` on tensors with `repLorentz`. -/
structure IsLorentzEquivariant {n : ℕ} (c : Fin n → complexLorentzTensor.Color) (B : Type*)
    [AddCommMonoid B] [Module ℂ B] (repLorentz : Representation ℂ SL(2,ℂ) B)
    (f : ℂT(c) →ₗ[ℂ] B) : Prop where
  equivariant : ∀ (g : SL(2,ℂ)) (t : ℂT(c)), f (g • t) = repLorentz g (f t)

/-- The action of `g : SL(2,ℂ)` on a basis tensor: the coefficient of `e_ψ` in `g • e_φ` is the
  product over the indices of the matrix entries of `g` in the colour of that index. -/
lemma smul_basis_eq_sum {n : ℕ} (c : Fin n → complexLorentzTensor.Color) (g : SL(2,ℂ))
    (φ : ComponentIdx (S := complexLorentzTensor) c) :
    g • Tensor.basis (S := complexLorentzTensor) c φ
      = ∑ ψ : ComponentIdx (S := complexLorentzTensor) c,
        (∏ i, LinearMap.toMatrix (complexLorentzTensor.basis (c i))
          (complexLorentzTensor.basis (c i)) (complexLorentzTensor.rep (c i) g) (ψ i) (φ i)) •
        Tensor.basis (S := complexLorentzTensor) c ψ := by
  simp only [Tensor.basis_apply, LinearMap.toMatrix_apply]
  rw [actionT_pure]
  have h : g • Pure.basisVector (S := complexLorentzTensor) c φ
      = (fun i => ∑ j, (complexLorentzTensor.basis (c i)).repr
          (complexLorentzTensor.rep (c i) g (complexLorentzTensor.basis (c i) (φ i))) j •
          complexLorentzTensor.basis (c i) j :
        Pure complexLorentzTensor c) := by
    funext i
    exact ((complexLorentzTensor.basis (c i)).sum_repr _).symm
  rw [h]
  unfold Pure.toTensor
  rw [MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [← MultilinearMap.map_smul_univ]
  rfl

/-- The components of `g • t`: the matrix of products of the matrix entries of `g`, one factor
  per index, applied to the components of `t`. -/
lemma basis_repr_smul {n : ℕ} (c : Fin n → complexLorentzTensor.Color) (g : SL(2,ℂ))
    (t : ℂT(c)) (φ : ComponentIdx (S := complexLorentzTensor) c) :
    (Tensor.basis c).repr (g • t) φ
      = ∑ ψ, (∏ i, LinearMap.toMatrix (complexLorentzTensor.basis (c i))
          (complexLorentzTensor.basis (c i)) (complexLorentzTensor.rep (c i) g) (φ i) (ψ i)) *
        (Tensor.basis c).repr t ψ := by
  conv_lhs => rw [← (Tensor.basis (S := complexLorentzTensor) c).sum_repr t]
  rw [actionT_eq, map_sum, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  congr 1
  have h := smul_basis_eq_sum c g ψ
  rw [actionT_eq] at h
  rw [h, map_sum]
  simp [Finsupp.single_apply]

/-!

## B. Dagger-compatible colours

-/

/-- The matrix of `g` on the left-handed Weyl colour is `g`. -/
lemma toMatrix_rep_upL (g : SL(2,ℂ)) :
    LinearMap.toMatrix (complexLorentzTensor.basis .upL) (complexLorentzTensor.basis .upL)
      (complexLorentzTensor.rep .upL g) = g.1 :=
  Fermion.LeftHandedWeyl.rep_toMatrix g

/-- The matrix of `g` on the dual left-handed Weyl colour is `(g⁻¹)ᵀ`. -/
lemma toMatrix_rep_downL (g : SL(2,ℂ)) :
    LinearMap.toMatrix (complexLorentzTensor.basis .downL) (complexLorentzTensor.basis .downL)
      (complexLorentzTensor.rep .downL g) = (g.1⁻¹)ᵀ :=
  Fermion.DualLeftHandedWeyl.rep_toMatrix g

/-- The matrix of `g` on the right-handed Weyl colour is the entrywise conjugate of `g`. -/
lemma toMatrix_rep_upR (g : SL(2,ℂ)) :
    LinearMap.toMatrix (complexLorentzTensor.basis .upR) (complexLorentzTensor.basis .upR)
      (complexLorentzTensor.rep .upR g) = g.1.map star :=
  Fermion.RightHandedWeyl.rep_toMatrix g

/-- The matrix of `g` on the dual right-handed Weyl colour is `(g⁻¹)ᴴ`. -/
lemma toMatrix_rep_downR (g : SL(2,ℂ)) :
    LinearMap.toMatrix (complexLorentzTensor.basis .downR) (complexLorentzTensor.basis .downR)
      (complexLorentzTensor.rep .downR g) = (g.1⁻¹)ᴴ :=
  Fermion.DualRightHandedWeyl.rep_toMatrix g

/-- The matrix of `g` on the contravariant vector colour is the Lorentz matrix of `g`, with
  the vector indices relabelled by `finSumFinEquiv`. -/
lemma toMatrix_rep_up_apply (g : SL(2,ℂ)) (μ ν : Fin 1 ⊕ Fin 3) :
    LinearMap.toMatrix (complexLorentzTensor.basis .up) (complexLorentzTensor.basis .up)
      (complexLorentzTensor.rep .up g) (finSumFinEquiv μ) (finSumFinEquiv ν)
      = (((SL2C.toLorentzGroup g).1 μ ν : ℝ) : ℂ) := by
  change LinearMap.toMatrix (complexContrBasis.reindex finSumFinEquiv)
    (complexContrBasis.reindex finSumFinEquiv) (ContrℂModule.SL2CRep g) _ _ = _
  rw [LinearMap.toMatrix_apply, Module.Basis.reindex_apply, Module.Basis.repr_reindex_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply, ← LinearMap.toMatrix_apply,
    complexContrBasis_ρ_apply]
  rfl

/-- A colour is dagger compatible when, in its basis, the matrix of `g†` is the conjugate
  transpose of the matrix of `g`. -/
def IsDaggerCompatible (k : complexLorentzTensor.Color) : Prop :=
  ∀ g : SL(2,ℂ),
    LinearMap.toMatrix (complexLorentzTensor.basis k) (complexLorentzTensor.basis k)
      (complexLorentzTensor.rep k (dagger g))
    = (LinearMap.toMatrix (complexLorentzTensor.basis k) (complexLorentzTensor.basis k)
      (complexLorentzTensor.rep k g))ᴴ

/-- The four Weyl colours are dagger compatible. -/
lemma isDaggerCompatible_of_weyl {k : complexLorentzTensor.Color}
    (hk : k = .upL ∨ k = .downL ∨ k = .upR ∨ k = .downR) : IsDaggerCompatible k := by
  rcases hk with rfl | rfl | rfl | rfl <;> intro g
  · rw [toMatrix_rep_upL, toMatrix_rep_upL]
    rfl
  · rw [toMatrix_rep_downL, toMatrix_rep_downL]
    change ((g.1ᴴ)⁻¹)ᵀ = _
    rw [← Matrix.conjTranspose_nonsing_inv]
    rfl
  · rw [toMatrix_rep_upR, toMatrix_rep_upR]
    ext i j
    simp [dagger]
  · rw [toMatrix_rep_downR, toMatrix_rep_downR]
    change ((g.1ᴴ)⁻¹)ᴴ = _
    rw [← Matrix.conjTranspose_nonsing_inv]

/-!

## C. Invariants in the range come from invariant tensors

-/

namespace IsLorentzEquivariant

variable {n : ℕ} {c : Fin n → complexLorentzTensor.Color} {B : Type*} [AddCommGroup B]
  [Module ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B} {f : ℂT(c) →ₗ[ℂ] B}
  (hf : IsLorentzEquivariant c B repLorentz f)

include hf in
/-- The range of an equivariant map is Lorentz stable. -/
lemma isStableUnder_range :
    IsStableUnder (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f) := by
  rintro g _ ⟨t, rfl⟩
  exact ⟨g • t, hf.equivariant g t⟩

include hf in
/-- The image of an invariant tensor under an equivariant map is Lorentz invariant. -/
lemma repLorentz_map_of_invariant {t : ℂT(c)} (ht : ∀ g : SL(2,ℂ), g • t = t)
    (g : SL(2,ℂ)) : repLorentz g (f t) = f t := by
  rw [← hf.equivariant, ht]

include hf in
/-- An invariant in the range of `f` is the image of an invariant tensor, when every colour is
  dagger compatible: the adjoint of the action of `g` is the action of `g†`. -/
lemma exists_invariant_eq_of_mem_range (hc : ∀ i, IsDaggerCompatible (c i)) {x : B}
    (hx : x ∈ LinearMap.range f) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ t : ℂT(c), (∀ g : SL(2,ℂ), g • t = t) ∧ f t = x := by
  rw [← Submodule.map_top, ← (Tensor.basis c).span_eq, Submodule.map_span,
    ← Set.range_comp] at hx
  obtain ⟨a, ha, rfl⟩ := Invariants.exists_invariantCoeff_matrix (f ∘ Tensor.basis c)
    (fun g => repLorentz g)
    (fun g ψ φ => ∏ i, LinearMap.toMatrix (complexLorentzTensor.basis (c i))
      (complexLorentzTensor.basis (c i)) (complexLorentzTensor.rep (c i) g) (ψ i) (φ i))
    (fun g φ => by
      rw [Function.comp_apply, ← hf.equivariant, smul_basis_eq_sum, map_sum]
      exact Finset.sum_congr rfl fun ψ _ => map_smul _ _ _)
    (fun g => ⟨dagger g, fun ψ φ => by
      rw [star_prod]
      exact Finset.prod_congr rfl fun i _ => by rw [hc i g]; rfl⟩) hx hinv
  refine ⟨∑ ψ, a ψ • Tensor.basis c ψ, fun g => ?_, by simp [map_sum]⟩
  apply (Tensor.basis (S := complexLorentzTensor) c).repr.injective
  ext φ
  rw [basis_repr_smul, Module.Basis.repr_sum_self]
  conv_rhs => rw [← ha g]
  simp only [actMat]
  exact Finset.sum_congr rfl fun ψ _ => mul_comm _ _

include hf in
/-- An invariant of `LinearMap.range f ⊔ S`, for `S` a Lorentz-stable submodule, is the image of
  an invariant tensor plus an element of `S`. -/
lemma exists_invariant_add_of_mem_sup (hc : ∀ i, IsDaggerCompatible (c i))
    (S : Submodule ℂ B) (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) {x : B}
    (hx : x ∈ LinearMap.range f ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) :
    ∃ t : ℂT(c), (∀ g : SL(2,ℂ), g • t = t) ∧ ∃ y ∈ S, x = f t + y := by
  have hq : IsLorentzEquivariant c (B ⧸ S) (repLorentz.quotient S fun g y hy => hS g y hy)
      (S.mkQ ∘ₗ f) := ⟨fun g t => by
    simp only [LinearMap.comp_apply]
    rw [hf.equivariant, quotient_apply_mkQ]⟩
  obtain ⟨t, ht, hft⟩ := hq.exists_invariant_eq_of_mem_range hc (x := S.mkQ x) (by
      rw [LinearMap.range_comp]
      have h := Submodule.mem_map_of_mem (f := S.mkQ) hx
      rwa [Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq] at h)
    (fun g => by rw [quotient_apply_mkQ, hinv])
  refine ⟨t, ht, x - f t, (Submodule.Quotient.eq S).1 hft.symm, by abel⟩

include hf in
/-- When the invariant tensors of `ℂT(c)` are the multiples of one tensor `t₀`, the Lorentz
  invariants of the range of `f` reduce to the span of `f t₀`. -/
noncomputable def invariantReductionToSpan (hc : ∀ i, IsDaggerCompatible (c i)) (t₀ : ℂT(c))
    (ht₀ : ∀ g : SL(2,ℂ), g • t₀ = t₀)
    (hclass : ∀ t : ℂT(c), (∀ g : SL(2,ℂ), g • t = t) → ∃ a : ℂ, t = a • t₀) :
    InvariantReductionToSpan (fun g : SL(2,ℂ) => repLorentz g) (LinearMap.range f) where
  spanningVector := f t₀
  stable := hf.isStableUnder_range
  spanningVector_fixed := hf.repLorentz_map_of_invariant ht₀
  reduce S hS _ hx hinv := by
    obtain ⟨t, ht, y, hy, rfl⟩ := hf.exists_invariant_add_of_mem_sup hc S hS hx hinv
    obtain ⟨a, rfl⟩ := hclass t ht
    exact ⟨a, y, hy, by rw [map_smul]⟩

/-!

## D. Building equivariant maps

-/

/-- A sum of equivariant maps is equivariant. -/
lemma sum {ι : Type*} (s : Finset ι) {F : ι → ℂT(c) →ₗ[ℂ] B}
    (hF : ∀ i ∈ s, IsLorentzEquivariant c B repLorentz (F i)) :
    IsLorentzEquivariant c B repLorentz (∑ i ∈ s, F i) where
  equivariant g t := by
    rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun i hi => (hF i hi).equivariant g t

include hf in
/-- A difference of equivariant maps is equivariant. -/
lemma sub {f' : ℂT(c) →ₗ[ℂ] B} (hf' : IsLorentzEquivariant c B repLorentz f') :
    IsLorentzEquivariant c B repLorentz (f - f') where
  equivariant g t := by
    rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, hf.equivariant, hf'.equivariant]

end IsLorentzEquivariant

/-- The linear map with prescribed values `T ψ` on the basis tensors is equivariant when the
  values are moved by `repLorentz` as the basis tensors are moved by `SL(2,ℂ)`. -/
lemma isLorentzEquivariant_constr {n : ℕ} {c : Fin n → complexLorentzTensor.Color} {B : Type*}
    [AddCommGroup B] [Module ℂ B] {repLorentz : Representation ℂ SL(2,ℂ) B}
    (T : ComponentIdx (S := complexLorentzTensor) c → B)
    (hT : ∀ (g : SL(2,ℂ)) φ, repLorentz g (T φ)
      = ∑ ψ, (∏ i, LinearMap.toMatrix (complexLorentzTensor.basis (c i))
          (complexLorentzTensor.basis (c i)) (complexLorentzTensor.rep (c i) g) (ψ i) (φ i)) •
        T ψ) :
    IsLorentzEquivariant c B repLorentz ((Tensor.basis c).constr ℂ T) where
  equivariant g t := by
    have h : (Tensor.basis c).constr ℂ T ∘ₗ
        PiTensorProduct.map (fun i => complexLorentzTensor.rep (c i) g)
        = repLorentz g ∘ₗ (Tensor.basis c).constr ℂ T := by
      refine (Tensor.basis (S := complexLorentzTensor) c).ext fun φ => ?_
      have h1 := smul_basis_eq_sum c g φ
      rw [actionT_eq] at h1
      simp only [LinearMap.comp_apply, h1, map_sum, map_smul, Module.Basis.constr_basis, hT]
    exact LinearMap.congr_fun h t

end Lorentz
