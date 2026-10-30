/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Nikolai Kashcheev
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Metrics.Pre
public import Physlib.Relativity.Fermions.Weyl.Metric
/-!

## Complex Lorentz tensors

-/

@[expose] public section

open Matrix
open MatrixGroups
open Complex
open TensorProduct

namespace complexLorentzTensor

set_option backward.isDefEq.respectTransparency false in
/-- The colors associated with complex representations of SL(2, ℂ) of interest to physics. -/
inductive Color
  /-- The color associated with Left handed fermions. -/
  | upL : Color
  /-- The color associated with dual-Left handed fermions. -/
  | downL : Color
  /-- The color associated with Right handed fermions. -/
  | upR : Color
  /-- The color associated with dual-Right handed fermions. -/
  | downR : Color
  /-- The color associated with contravariant Lorentz vectors. -/
  | up : Color
  /-- The color associated with covariant Lorentz vectors. -/
  | down : Color
deriving Fintype

/-- Color for complex Lorentz tensors is decidable. -/
instance : DecidableEq Color := fun x y =>
  match x, y with
  | Color.upL, Color.upL => isTrue rfl
  | Color.downL, Color.downL => isTrue rfl
  | Color.upR, Color.upR => isTrue rfl
  | Color.downR, Color.downR => isTrue rfl
  | Color.up, Color.up => isTrue rfl
  | Color.down, Color.down => isTrue rfl
  /- The false -/
  | Color.upL, Color.downL => isFalse fun h => Color.noConfusion h
  | Color.upL, Color.upR => isFalse fun h => Color.noConfusion h
  | Color.upL, Color.downR => isFalse fun h => Color.noConfusion h
  | Color.upL, Color.up => isFalse fun h => Color.noConfusion h
  | Color.upL, Color.down => isFalse fun h => Color.noConfusion h
  | Color.downL, Color.upL => isFalse fun h => Color.noConfusion h
  | Color.downL, Color.upR => isFalse fun h => Color.noConfusion h
  | Color.downL, Color.downR => isFalse fun h => Color.noConfusion h
  | Color.downL, Color.up => isFalse fun h => Color.noConfusion h
  | Color.downL, Color.down => isFalse fun h => Color.noConfusion h
  | Color.upR, Color.upL => isFalse fun h => Color.noConfusion h
  | Color.upR, Color.downL => isFalse fun h => Color.noConfusion h
  | Color.upR, Color.downR => isFalse fun h => Color.noConfusion h
  | Color.upR, Color.up => isFalse fun h => Color.noConfusion h
  | Color.upR, Color.down => isFalse fun h => Color.noConfusion h
  | Color.downR, Color.upL => isFalse fun h => Color.noConfusion h
  | Color.downR, Color.downL => isFalse fun h => Color.noConfusion h
  | Color.downR, Color.upR => isFalse fun h => Color.noConfusion h
  | Color.downR, Color.up => isFalse fun h => Color.noConfusion h
  | Color.downR, Color.down => isFalse fun h => Color.noConfusion h
  | Color.up, Color.upL => isFalse fun h => Color.noConfusion h
  | Color.up, Color.downL => isFalse fun h => Color.noConfusion h
  | Color.up, Color.upR => isFalse fun h => Color.noConfusion h
  | Color.up, Color.downR => isFalse fun h => Color.noConfusion h
  | Color.up, Color.down => isFalse fun h => Color.noConfusion h
  | Color.down, Color.upL => isFalse fun h => Color.noConfusion h
  | Color.down, Color.downL => isFalse fun h => Color.noConfusion h
  | Color.down, Color.upR => isFalse fun h => Color.noConfusion h
  | Color.down, Color.downR => isFalse fun h => Color.noConfusion h
  | Color.down, Color.up => isFalse fun h => Color.noConfusion h

/-- The dimensions of each of the different types of complex Lorentz vector space. -/
abbrev repDim (c : Color) : ℕ :=
  match c with
  | Color.upL => 2
  | Color.downL => 2
  | Color.upR => 2
  | Color.downR => 2
  | Color.up => 4
  | Color.down => 4

/-- The type indexing the standard basis of each complex Lorentz vector space: `Fin 2` for the
  Weyl colors and `Fin 1 ⊕ Fin 3` for the vector colors. -/
abbrev basisIdx : Color → Type
  | Color.upL => Fin 2
  | Color.downL => Fin 2
  | Color.upR => Fin 2
  | Color.downR => Fin 2
  | Color.up => Fin 1 ⊕ Fin 3
  | Color.down => Fin 1 ⊕ Fin 3

instance basisIdxFintype : ∀ c, Fintype (basisIdx c)
  | Color.upL => inferInstance
  | Color.downL => inferInstance
  | Color.upR => inferInstance
  | Color.downR => inferInstance
  | Color.up => inferInstance
  | Color.down => inferInstance

instance basisIdxDecidableEq : ∀ c, DecidableEq (basisIdx c)
  | Color.upL => inferInstance
  | Color.downL => inferInstance
  | Color.upR => inferInstance
  | Color.downR => inferInstance
  | Color.up => inferInstance
  | Color.down => inferInstance

/-- The modules associated with each of the different types of complex Lorentz vector space. -/
abbrev modules : Color → Type
  | Color.upL => Fermion.LeftHandedWeyl
  | Color.downL => Fermion.DualLeftHandedWeyl
  | Color.upR => Fermion.RightHandedWeyl
  | Color.downR => Fermion.DualRightHandedWeyl
  | Color.up => Lorentz.ComplexVector
  | Color.down => Lorentz.ComplexCoVector

instance modulesAddCommGroup : ∀ c, AddCommGroup (modules c)
  | Color.upL => inferInstance
  | Color.downL => inferInstance
  | Color.upR => inferInstance
  | Color.downR => inferInstance
  | Color.up => inferInstance
  | Color.down => inferInstance

noncomputable instance modulesModule : ∀ c, Module ℂ (modules c)
  | Color.upL => inferInstance
  | Color.downL => inferInstance
  | Color.upR => inferInstance
  | Color.downR => inferInstance
  | Color.up => inferInstance
  | Color.down => inferInstance

end complexLorentzTensor

noncomputable section
open complexLorentzTensor in
set_option maxHeartbeats 0 in
/-- The tensor structure for complex Lorentz tensors. -/
def complexLorentzTensor : TensorSpecies ℂ complexLorentzTensor.Color SL(2, ℂ)
    (fun c => match c with
      | Color.upL => Fermion.LeftHandedWeyl
      | Color.downL => Fermion.DualLeftHandedWeyl
      | Color.upR => Fermion.RightHandedWeyl
      | Color.downR => Fermion.DualRightHandedWeyl
      | Color.up => Lorentz.ComplexVector
      | Color.down => Lorentz.ComplexCoVector)
    basisIdx
    (fun c => match c with
      | Color.upL => Fermion.LeftHandedWeyl.rep
      | Color.downL => Fermion.DualLeftHandedWeyl.rep
      | Color.upR => Fermion.RightHandedWeyl.rep
      | Color.downR => Fermion.DualRightHandedWeyl.rep
      | Color.up => Lorentz.ComplexVector.SL2CRep
      | Color.down => Lorentz.ComplexCoVector.SL2CRep)
    (fun c => match c with
    | Color.upL => Fermion.LeftHandedWeyl.basis
    | Color.downL => Fermion.DualLeftHandedWeyl.basis
    | Color.upR => Fermion.RightHandedWeyl.basis
    | Color.downR => Fermion.DualRightHandedWeyl.basis
    | Color.up => Lorentz.ComplexVector.basis
    | Color.down => Lorentz.ComplexCoVector.basis) where

  τ := fun c =>
    match c with
    | Color.upL => Color.downL
    | Color.downL => Color.upL
    | Color.upR => Color.downR
    | Color.downR => Color.upR
    | Color.up => Color.down
    | Color.down => Color.up
  τ_involution c := by
    match c with
    | Color.upL => rfl
    | Color.downL => rfl
    | Color.upR => rfl
    | Color.downR => rfl
    | Color.up => rfl
    | Color.down => rfl
  contr := fun c =>
    match c with
    | Color.upL => Fermion.LeftHandedWeyl.contr
    | Color.downL => Fermion.DualLeftHandedWeyl.contr
    | Color.upR => Fermion.RightHandedWeyl.contr
    | Color.downR => Fermion.DualRightHandedWeyl.contr
    | Color.up => Lorentz.ComplexVector.contr
    | Color.down => Lorentz.ComplexCoVector.contr
  unit := fun c =>
    match c with
    | Color.upL => Fermion.LeftHandedWeyl.unit
    | Color.downL => Fermion.DualLeftHandedWeyl.unit
    | Color.upR => Fermion.RightHandedWeyl.unit
    | Color.downR => Fermion.DualRightHandedWeyl.unit
    | Color.up => Lorentz.ComplexVector.unit
    | Color.down => Lorentz.ComplexCoVector.unit
  contr_tmul_symm := fun c =>
    match c with
    | Color.upL => Fermion.LeftHandedWeyl.contr_tmul_symm
    | Color.downL => Fermion.DualLeftHandedWeyl.contr_tmul_symm
    | Color.upR => Fermion.RightHandedWeyl.contr_tmul_symm
    | Color.downR => Fermion.DualRightHandedWeyl.contr_tmul_symm
    | Color.up => Lorentz.ComplexVector.contr_tmul_symm
    | Color.down => Lorentz.ComplexCoVector.contr_tmul_symm
  contr_unit := fun c =>
    match c with
    | Color.upL => Fermion.LeftHandedWeyl.contr_unit
    | Color.downL => Fermion.DualLeftHandedWeyl.contr_unit
    | Color.upR => Fermion.RightHandedWeyl.contr_unit
    | Color.downR => Fermion.DualRightHandedWeyl.contr_unit
    | Color.up => Lorentz.ComplexVector.contr_unit
    | Color.down => Lorentz.ComplexCoVector.contr_unit
  unit_symm := fun c =>
    match c with
    | Color.upL => Fermion.LeftHandedWeyl.unit_symm
    | Color.downL => Fermion.DualLeftHandedWeyl.unit_symm
    | Color.upR => Fermion.RightHandedWeyl.unit_symm
    | Color.downR => Fermion.DualRightHandedWeyl.unit_symm
    | Color.up => Lorentz.ComplexVector.unit_symm
    | Color.down => Lorentz.ComplexCoVector.unit_symm

namespace complexLorentzTensor

/-- The metrics of the complex Lorentz tensors: `ε` on the four Weyl colors and `η` on the two
  vector colors. -/
instance instWithMetric : complexLorentzTensor.WithMetric where
  metric := fun c =>
    match c with
    | Color.upL => Fermion.LeftHandedWeyl.metric
    | Color.downL => Fermion.DualLeftHandedWeyl.metric
    | Color.upR => Fermion.RightHandedWeyl.metric
    | Color.downR => Fermion.DualRightHandedWeyl.metric
    | Color.up => Lorentz.ComplexVector.metric
    | Color.down => Lorentz.ComplexCoVector.metric
  contr_metric := fun c =>
    match c with
    | Color.upL => Fermion.LeftHandedWeyl.contr_metric
    | Color.downL => Fermion.DualLeftHandedWeyl.contr_metric
    | Color.upR => Fermion.RightHandedWeyl.contr_metric
    | Color.downR => Fermion.DualRightHandedWeyl.contr_metric
    | Color.up => Lorentz.ComplexVector.contr_metric
    | Color.down => Lorentz.ComplexCoVector.contr_metric

/-- Complex Lorentz tensor. -/
syntax (name := complexLorentzTensorSyntax) "ℂT[" term,* "]" : term

/-- The basis associated with each of the different types of complex Lorentz vector space. -/
abbrev basis (c : Color) : Module.Basis (basisIdx c) ℂ (modules c) :=
  match c with
  | Color.upL => Fermion.LeftHandedWeyl.basis
  | Color.downL => Fermion.DualLeftHandedWeyl.basis
  | Color.upR => Fermion.RightHandedWeyl.basis
  | Color.downR => Fermion.DualRightHandedWeyl.basis
  | Color.up => Lorentz.ComplexVector.basis
  | Color.down => Lorentz.ComplexCoVector.basis

/-- The reps associated with each of the different types of complex Lorentz vector space. -/
abbrev rep (c : Color) : Representation ℂ SL(2, ℂ) (modules c) :=
  match c with
  | Color.upL => Fermion.LeftHandedWeyl.rep
  | Color.downL => Fermion.DualLeftHandedWeyl.rep
  | Color.upR => Fermion.RightHandedWeyl.rep
  | Color.downR => Fermion.DualRightHandedWeyl.rep
  | Color.up => Lorentz.ComplexVector.SL2CRep
  | Color.down => Lorentz.ComplexCoVector.SL2CRep

macro_rules
  | `(ℂT[$term:term, $terms:term,*]) =>
    `(complexLorentzTensor.Tensor (vecCons $term ![$terms,*]))
  | `(ℂT[$term:term]) => `(complexLorentzTensor.Tensor (vecCons $term ![]))
  | `(ℂT[]) =>`(complexLorentzTensor.Tensor (vecEmpty))

/-- Complex Lorentz tensor. -/
scoped[complexLorentzTensor] notation "ℂT(" c ")" => complexLorentzTensor.Tensor c

open TensorSpecies Tensor

lemma repDim_tau {c : complexLorentzTensor.Color} :
    repDim (complexLorentzTensor.τ c) = repDim c := by
  cases c <;> rfl

/-- A color and its dual carry the same basis index type. -/
def basisIdxTauEquiv : (c : complexLorentzTensor.Color) →
    basisIdx (complexLorentzTensor.τ c) ≃ basisIdx c
  | Color.upL => Equiv.refl _
  | Color.downL => Equiv.refl _
  | Color.upR => Equiv.refl _
  | Color.downR => Equiv.refl _
  | Color.up => Equiv.refl _
  | Color.down => Equiv.refl _

/-- At every complex Lorentz color, the bases at the color and its dual are dual bases, with
labels matched by the identity. -/
lemma isContrDualMatching_basisIdxTauEquiv (c : complexLorentzTensor.Color) :
    IsContrDualMatching complexLorentzTensor c (basisIdxTauEquiv c) := by
  intro x₁ x₂
  cases c
  · exact (Fermion.LeftHandedWeyl.contr_basis x₁ x₂).trans (if_congr Fin.ext_iff.symm rfl rfl)
  · exact (Fermion.DualLeftHandedWeyl.contr_basis x₁ x₂).trans (if_congr Fin.ext_iff.symm rfl rfl)
  · exact (Fermion.RightHandedWeyl.contr_basis x₁ x₂).trans (if_congr Fin.ext_iff.symm rfl rfl)
  · exact (Fermion.DualRightHandedWeyl.contr_basis x₁ x₂).trans
      (if_congr Fin.ext_iff.symm rfl rfl)
  · exact Lorentz.ComplexVector.contr_basis' x₁ x₂
  · exact Lorentz.ComplexCoVector.contr_basis' x₁ x₂

/-- Complex Lorentz tensors have dual bases under contraction, with the identity matching. -/
instance : HasContrDualBases complexLorentzTensor where
  exists_matching c := ⟨_, isContrDualMatching_basisIdxTauEquiv c⟩

/-- The dual-label matching of complex Lorentz tensors is the identity. -/
@[simp]
lemma contrDualIdxEquiv_eq_basisIdxTauEquiv (c : complexLorentzTensor.Color) :
    HasContrDualBases.contrDualIdxEquiv complexLorentzTensor c = basisIdxTauEquiv c :=
  HasContrDualBases.contrDualIdxEquiv_eq_of_isContrDualMatching
    (isContrDualMatching_basisIdxTauEquiv c)

lemma contrPCoeff_basis {n : ℕ} {c : Fin n → complexLorentzTensor.Color} (i j : Fin n)
    (hij : i ≠ j ∧ (complexLorentzTensor.τ (c i) = c j))
    (b : ComponentIdx (S := complexLorentzTensor) c) :
    Pure.contrPCoeff i j hij (Pure.basisVector c b) =
      if b i = basisIdxTauEquiv (c i) (basisIdxCongr hij.2.symm (b j)) then 1 else 0 := by
  rw [Pure.contrPCoeff_basisVector, contrDualIdxEquiv_eq_basisIdxTauEquiv]

/-- Complex conjugation of colours: it swaps handedness and fixes the vector colours. -/
def Color.bar : Color → Color
  | Color.upL => Color.upR
  | Color.downL => Color.downR
  | Color.upR => Color.upL
  | Color.downR => Color.downL
  | Color.up => Color.up
  | Color.down => Color.down

end complexLorentzTensor

open complexLorentzTensor in
/-- The complex Lorentz tensors as a conjugation species: conjugation swaps left- and
  right-handed Weyl colours and fixes the vector colours. -/
def complexLorentzConjTensor : ConjTensorSpecies ℂ Color SL(2, ℂ) modules
    basisIdx rep basis where
  toTensorSpecies := complexLorentzTensor
  bar := Color.bar
  bar_involution c := by cases c <;> rfl
  bar_tau c := by cases c <;> rfl
  barIdx_eq c := by cases c <;> rfl
  conj_basis_equivariant c g i j := by
    cases c
    · change Fermion.LeftHandedWeyl.basis.repr (Fermion.LeftHandedWeyl.rep g
          (Fermion.LeftHandedWeyl.basis i)) j = star (Fermion.RightHandedWeyl.basis.repr
          (Fermion.RightHandedWeyl.rep g (Fermion.RightHandedWeyl.basis i)) j)
      rw [Fermion.LeftHandedWeyl.rep_apply_basis_repr,
        Fermion.RightHandedWeyl.rep_apply_basis_repr, star_star]
    · change Fermion.DualLeftHandedWeyl.basis.repr (Fermion.DualLeftHandedWeyl.rep g
          (Fermion.DualLeftHandedWeyl.basis i)) j = star (Fermion.DualRightHandedWeyl.basis.repr
          (Fermion.DualRightHandedWeyl.rep g (Fermion.DualRightHandedWeyl.basis i)) j)
      rw [Fermion.DualLeftHandedWeyl.rep_apply_basis_repr,
        Fermion.DualRightHandedWeyl.rep_apply_basis_repr, star_star]
    · change Fermion.RightHandedWeyl.basis.repr (Fermion.RightHandedWeyl.rep g
          (Fermion.RightHandedWeyl.basis i)) j = star (Fermion.LeftHandedWeyl.basis.repr
          (Fermion.LeftHandedWeyl.rep g (Fermion.LeftHandedWeyl.basis i)) j)
      rw [Fermion.LeftHandedWeyl.rep_apply_basis_repr,
        Fermion.RightHandedWeyl.rep_apply_basis_repr]
    · change Fermion.DualRightHandedWeyl.basis.repr (Fermion.DualRightHandedWeyl.rep g
          (Fermion.DualRightHandedWeyl.basis i)) j = star (Fermion.DualLeftHandedWeyl.basis.repr
          (Fermion.DualLeftHandedWeyl.rep g (Fermion.DualLeftHandedWeyl.basis i)) j)
      rw [Fermion.DualLeftHandedWeyl.rep_apply_basis_repr,
        Fermion.DualRightHandedWeyl.rep_apply_basis_repr]
    · change Lorentz.ComplexVector.basis.repr (Lorentz.ComplexVector.SL2CRep g
          (Lorentz.ComplexVector.basis i)) j = star (Lorentz.ComplexVector.basis.repr
          (Lorentz.ComplexVector.SL2CRep g (Lorentz.ComplexVector.basis i)) j)
      rw [← LinearMap.toMatrix_apply, Lorentz.ComplexVector.basis_ρ_apply,
        LorentzGroup.star_toComplex_apply]
    · change Lorentz.ComplexCoVector.basis.repr (Lorentz.ComplexCoVector.SL2CRep g
          (Lorentz.ComplexCoVector.basis i)) j = star (Lorentz.ComplexCoVector.basis.repr
          (Lorentz.ComplexCoVector.SL2CRep g (Lorentz.ComplexCoVector.basis i)) j)
      rw [← LinearMap.toMatrix_apply, Lorentz.ComplexCoVector.basis_ρ_apply,
        LorentzGroup.toComplex_inv, Matrix.transpose_apply, LorentzGroup.star_toComplex_apply]
  conj_contrComm d x₁ x₂ := by
    cases d <;>
    · simp only [TensorSpecies.HasContrDualBases.contr_basis_eq_ite,
        contrDualIdxEquiv_eq_basisIdxTauEquiv]
      rw [apply_ite star]
      exact if_congr Iff.rfl (by simp) (by simp)

/-!

## Tensorial instances

Complex Lorentz vectors and left- and right-handed Weyl fermions are tensors with one index,
of colour `up`, `upL` and `upR` respectively, through `Tensor.fromSingleT`. Under this
identification the `SL(2, ℂ)` action is the representation on each type, and basis vectors go to
basis tensors.

-/

open TensorSpecies

/-- Complex Lorentz vectors as complex Lorentz tensors with a single `up` index. -/
instance Lorentz.ComplexVector.tensorial :
    Tensorial complexLorentzTensor ![.up] Lorentz.ComplexVector where
  toTensor := Tensor.fromSingleT (S := complexLorentzTensor) (c := .up)

/-- Left-handed Weyl fermions as complex Lorentz tensors with a single `upL` index. -/
instance Fermion.LeftHandedWeyl.tensorial :
    Tensorial complexLorentzTensor ![.upL] Fermion.LeftHandedWeyl where
  toTensor := Tensor.fromSingleT (S := complexLorentzTensor) (c := .upL)

/-- Right-handed Weyl fermions as complex Lorentz tensors with a single `upR` index. -/
instance Fermion.RightHandedWeyl.tensorial :
    Tensorial complexLorentzTensor ![.upR] Fermion.RightHandedWeyl where
  toTensor := Tensor.fromSingleT (S := complexLorentzTensor) (c := .upR)

@[simp]
lemma Lorentz.ComplexVector.toTensor_basis (μ : Fin 1 ⊕ Fin 3) :
    Tensorial.toTensor (Lorentz.ComplexVector.basis μ) =
      Tensor.basis (S := complexLorentzTensor) ![.up] (Tensor.ComponentIdx.single.symm μ) := by
  change Tensor.fromSingleT _ = _
  rw [Tensor.fromSingleT_eq_pureT, Tensor.basis_apply]
  congr 1
  funext i
  fin_cases i
  rfl

@[simp]
lemma Fermion.LeftHandedWeyl.toTensor_basis (a : Fin 2) :
    Tensorial.toTensor (Fermion.LeftHandedWeyl.basis a) =
      Tensor.basis (S := complexLorentzTensor) ![.upL] (Tensor.ComponentIdx.single.symm a) := by
  change Tensor.fromSingleT _ = _
  rw [Tensor.fromSingleT_eq_pureT, Tensor.basis_apply]
  congr 1
  funext i
  fin_cases i
  rfl

@[simp]
lemma Fermion.RightHandedWeyl.toTensor_basis (a : Fin 2) :
    Tensorial.toTensor (Fermion.RightHandedWeyl.basis a) =
      Tensor.basis (S := complexLorentzTensor) ![.upR] (Tensor.ComponentIdx.single.symm a) := by
  change Tensor.fromSingleT _ = _
  rw [Tensor.fromSingleT_eq_pureT, Tensor.basis_apply]
  congr 1
  funext i
  fin_cases i
  rfl

/-- The one-index tensor basis, transported back along `toTensor`, is
  `Lorentz.ComplexVector.basis` relabelled by `ComponentIdx.single`. -/
lemma Lorentz.ComplexVector.basis_map_toTensor_symm :
    (Tensor.basis (S := complexLorentzTensor) ![.up]).map
        (Tensorial.toTensor (S := complexLorentzTensor) (M := Lorentz.ComplexVector)).symm =
      Lorentz.ComplexVector.basis.reindex
        (Tensor.ComponentIdx.single (S := complexLorentzTensor) (c := .up)).symm := by
  refine Module.Basis.eq_of_apply_eq fun φ => ?_
  apply (Tensorial.toTensor (S := complexLorentzTensor) (M := Lorentz.ComplexVector)).injective
  rw [Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Module.Basis.reindex_apply,
    Equiv.symm_symm, Lorentz.ComplexVector.toTensor_basis, Equiv.symm_apply_apply]

/-- The components of `toTensor v` are the coordinates of `v` in `Lorentz.ComplexVector.basis`. -/
lemma Lorentz.ComplexVector.toTensor_basis_repr (v : Lorentz.ComplexVector)
    (φ : Tensor.ComponentIdx (S := complexLorentzTensor) ![.up]) :
    (Tensor.basis (S := complexLorentzTensor) ![.up]).repr (Tensorial.toTensor v) φ =
      Lorentz.ComplexVector.basis.repr v
        (Tensor.ComponentIdx.single (S := complexLorentzTensor) (c := .up) φ) := by
  have h := congrArg (fun B => B.repr v φ) Lorentz.ComplexVector.basis_map_toTensor_symm
  simpa only [Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm,
    Module.Basis.repr_reindex_apply, Equiv.symm_symm] using h

/-- The one-index tensor basis, transported back along `toTensor`, is
  `Fermion.LeftHandedWeyl.basis` relabelled by `ComponentIdx.single`. -/
lemma Fermion.LeftHandedWeyl.basis_map_toTensor_symm :
    (Tensor.basis (S := complexLorentzTensor) ![.upL]).map
        (Tensorial.toTensor (S := complexLorentzTensor) (M := Fermion.LeftHandedWeyl)).symm =
      Fermion.LeftHandedWeyl.basis.reindex
        (Tensor.ComponentIdx.single (S := complexLorentzTensor) (c := .upL)).symm := by
  refine Module.Basis.eq_of_apply_eq fun φ => ?_
  apply (Tensorial.toTensor (S := complexLorentzTensor) (M := Fermion.LeftHandedWeyl)).injective
  rw [Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Module.Basis.reindex_apply,
    Equiv.symm_symm, Fermion.LeftHandedWeyl.toTensor_basis, Equiv.symm_apply_apply]

/-- The components of `toTensor v` are the coordinates of `v` in `Fermion.LeftHandedWeyl.basis`. -/
lemma Fermion.LeftHandedWeyl.toTensor_basis_repr (v : Fermion.LeftHandedWeyl)
    (φ : Tensor.ComponentIdx (S := complexLorentzTensor) ![.upL]) :
    (Tensor.basis (S := complexLorentzTensor) ![.upL]).repr (Tensorial.toTensor v) φ =
      Fermion.LeftHandedWeyl.basis.repr v
        (Tensor.ComponentIdx.single (S := complexLorentzTensor) (c := .upL) φ) := by
  have h := congrArg (fun B => B.repr v φ) Fermion.LeftHandedWeyl.basis_map_toTensor_symm
  simpa only [Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm,
    Module.Basis.repr_reindex_apply, Equiv.symm_symm] using h

/-- The one-index tensor basis, transported back along `toTensor`, is
  `Fermion.RightHandedWeyl.basis` relabelled by `ComponentIdx.single`. -/
lemma Fermion.RightHandedWeyl.basis_map_toTensor_symm :
    (Tensor.basis (S := complexLorentzTensor) ![.upR]).map
        (Tensorial.toTensor (S := complexLorentzTensor) (M := Fermion.RightHandedWeyl)).symm =
      Fermion.RightHandedWeyl.basis.reindex
        (Tensor.ComponentIdx.single (S := complexLorentzTensor) (c := .upR)).symm := by
  refine Module.Basis.eq_of_apply_eq fun φ => ?_
  apply (Tensorial.toTensor (S := complexLorentzTensor) (M := Fermion.RightHandedWeyl)).injective
  rw [Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Module.Basis.reindex_apply,
    Equiv.symm_symm, Fermion.RightHandedWeyl.toTensor_basis, Equiv.symm_apply_apply]

/-- The components of `toTensor v` are the coordinates of `v` in `Fermion.RightHandedWeyl.basis`. -/
lemma Fermion.RightHandedWeyl.toTensor_basis_repr (v : Fermion.RightHandedWeyl)
    (φ : Tensor.ComponentIdx (S := complexLorentzTensor) ![.upR]) :
    (Tensor.basis (S := complexLorentzTensor) ![.upR]).repr (Tensorial.toTensor v) φ =
      Fermion.RightHandedWeyl.basis.repr v
        (Tensor.ComponentIdx.single (S := complexLorentzTensor) (c := .upR) φ) := by
  have h := congrArg (fun B => B.repr v φ) Fermion.RightHandedWeyl.basis_map_toTensor_symm
  simpa only [Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm,
    Module.Basis.repr_reindex_apply, Equiv.symm_symm] using h

/-- The `SL(2, ℂ)` action on complex Lorentz vectors as tensors is `ComplexVector.SL2CRep`. -/
lemma Lorentz.ComplexVector.smul_eq_SL2CRep (g : SL(2, ℂ)) (v : Lorentz.ComplexVector) :
    g • v = Lorentz.ComplexVector.SL2CRep g v := by
  apply (Tensorial.toTensor (S := complexLorentzTensor)).injective
  rw [Tensorial.toTensor_smul]
  exact Tensor.actionT_fromSingleT (S := complexLorentzTensor) (c := .up) v g

/-- The `SL(2, ℂ)` action on left-handed Weyl fermions as tensors is `LeftHandedWeyl.rep`. -/
lemma Fermion.LeftHandedWeyl.smul_eq_rep (g : SL(2, ℂ)) (v : Fermion.LeftHandedWeyl) :
    g • v = Fermion.LeftHandedWeyl.rep g v := by
  apply (Tensorial.toTensor (S := complexLorentzTensor)).injective
  rw [Tensorial.toTensor_smul]
  exact Tensor.actionT_fromSingleT (S := complexLorentzTensor) (c := .upL) v g

/-- The `SL(2, ℂ)` action on right-handed Weyl fermions as tensors is `RightHandedWeyl.rep`. -/
lemma Fermion.RightHandedWeyl.smul_eq_rep (g : SL(2, ℂ)) (v : Fermion.RightHandedWeyl) :
    g • v = Fermion.RightHandedWeyl.rep g v := by
  apply (Tensorial.toTensor (S := complexLorentzTensor)).injective
  rw [Tensorial.toTensor_smul]
  exact Tensor.actionT_fromSingleT (S := complexLorentzTensor) (c := .upR) v g

end
