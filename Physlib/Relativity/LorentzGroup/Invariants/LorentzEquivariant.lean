/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Invariants.LorentzCovariance
public import Physlib.Relativity.Tensors.ComplexTensor.Metrics.Basic
public import Physlib.Relativity.Tensors.Equivariant
/-!
# Lorentz-equivariant maps out of complex Lorentz tensors

A family of vectors in a representation `repLorentz` of `SL(2,ℂ)` on `B`, carrying Lorentz
indices of colours `c`, is packaged as a linear map `f : ℂT(c) →ₗ[ℂ] B` out of the complex
Lorentz tensors with those indices, and `IsLorentzEquivariant c B repLorentz f` says that `f`
intertwines the action on tensors with `repLorentz` (A). It is the equivariance
`TensorSpecies.IsEquivariant` of the species `complexLorentzTensor`, whose results
(`Physlib.Relativity.Tensors.Equivariant`) therefore apply.

The invariants in the range of such a map come from invariant tensors whenever the colours are
closed under adjoints, `TensorSpecies.IsAdjointClosed`. For `SL(2,ℂ)` this follows from each
colour `c i` being dagger compatible (B): the matrix of `g†` is the conjugate transpose of the
matrix of `g`, which is proved for the four Weyl colours.
-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups SL2C Invariants TensorSpecies Tensor complexLorentzTensor

/-!

## A. Equivariant maps

-/

/-- A linear map `f` from the complex Lorentz tensors with index colours `c` to a representation
  `repLorentz` of `SL(2,ℂ)` on `B`, which is equivariant: it intertwines the action of
  `SL(2,ℂ)` on tensors with `repLorentz`. -/
abbrev IsLorentzEquivariant {n : ℕ} (c : Fin n → complexLorentzTensor.Color) (B : Type*)
    [AddCommMonoid B] [Module ℂ B] (repLorentz : Representation ℂ SL(2,ℂ) B)
    (f : ℂT(c) →ₗ[ℂ] B) : Prop :=
  complexLorentzTensor.IsEquivariant c repLorentz f

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

/-- Colours that are all dagger compatible are closed under adjoints, with `g' = g†`. -/
lemma isAdjointClosed_of_isDaggerCompatible {n : ℕ} {c : Fin n → complexLorentzTensor.Color}
    (hc : ∀ i, IsDaggerCompatible (c i)) : complexLorentzTensor.IsAdjointClosed c :=
  fun g => ⟨dagger g, fun i => hc i g⟩

end Lorentz
