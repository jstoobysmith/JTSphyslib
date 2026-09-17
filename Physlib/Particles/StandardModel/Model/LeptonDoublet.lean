/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Particles.StandardModel.Model.Consistency
public import Physlib.Particles.StandardModel.Fermions.MatterField
/-!

# The lepton doublet of the Standard Model table

## i. Overview

The lepton doublet of the Standard Model is the datum `StandardModel.Model.leptonDoublet`,
`(.L, .singlet, .fund, -3)`, of `Physlib.Particles.StandardModel.Basic`. This file records
what the general theory derives from it and checks it against the hand-built
`StandardModel.LeptonDoublet`: the datum is indexed by the weak index alone, its gauge jets
act by the matrix `ū³ · U₂` of the hand-built doublet and its gauge algebra by the
hand-built action matrix, and, on the target space `LeptonDoublet` identified with its
tensor-product value, the matter field the general theory derives from the datum is the
hand-built matter field itself.

## ii. Key results

- `StandardModel.Model.leptonDoublet_rep_mat`, `leptonDoublet_rep_act` : the datum acts by
  `LeptonDoublet.doubletMatrix` and `LeptonDoublet.actionMatrix`.
- `StandardModel.Model.leptonDoublet_toMatterFieldOn_eq` : on the target space
  `LeptonDoublet`, the matter field of the datum is `LeptonDoublet.matterField`.

## iii. Table of contents

- A. The index and the matrices
- B. The matter field on the hand-built target space

-/

@[expose] public section

open LocalGaugeData Matrix TensorProduct

namespace StandardModel

namespace Model

/-!

## A. The index and the matrices

-/

/-- The lepton doublet is indexed by a weak index alone, as the hand-built lepton doublet. -/
example : leptonDoublet.Idx = Fin 2 := rfl

/-- The lepton doublet has mass weight `3`. -/
example : leptonDoublet.massWeight = 3 := rfl

/-- The lepton doublet acts on its weak index by the matrix `ū³ · U₂` of the hand-built
  lepton doublet. -/
lemma leptonDoublet_rep_mat (U : JetGaugeGroupI) :
    leptonDoublet.rep.mat U = LeptonDoublet.doubletMatrix U := by
  show MatterField.chargePow (-3) U.2.2 • U.2.1.1 = LeptonDoublet.doubletMatrix U
  rw [LeptonDoublet.doubletMatrix]
  congr 1

/-- The gauge algebra acts on the weak index of the lepton doublet by the action matrix of
  the hand-built lepton doublet. -/
lemma leptonDoublet_rep_act (c : GaugeAlgebra) :
    leptonDoublet.rep.act c = LeptonDoublet.actionMatrix c := by
  show Complex.I • (c.2.1 : Matrix (Fin 2) (Fin 2) ℂ)
      + (Complex.I * ((-3 : ℤ) : ℂ) * (c.2.2 : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
    = LeptonDoublet.actionMatrix c
  rw [LeptonDoublet.actionMatrix, GaugeAlgebra.toSU2Matrix, GaugeAlgebra.toU1Value]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring

/-!

## B. The matter field on the hand-built target space

The hand-built target space `LeptonDoublet` is a Weyl spinor tensored with a Euclidean
weak index; forgetting the Euclidean structure identifies it with the tensor-product target
space of the datum.

-/

/-- The identification of the hand-built target space with the target space of the datum. -/
local notation "valIdx" =>
  LeptonDoublet.valLinEquiv.trans
    (TensorProduct.congr (LinearEquiv.refl ℂ Fermion.LeftHandedWeyl)
      (WithLp.linearEquiv 2 ℂ (Fin 2 → ℂ)))

/-- The identification sends a pure tensor to the pure tensor of the weak coordinates. -/
lemma valIdx_symm_tmul (s : Fermion.LeftHandedWeyl) (w : EuclideanSpace ℂ (Fin 2)) :
    LeptonDoublet.valLinEquiv.symm (s ⊗ₜ w) = (valIdx).symm (s ⊗ₜ (WithLp.ofLp w)) := by
  simp

/-- The gauge algebra action of the datum on `LeptonDoublet` is the hand-built action. -/
lemma leptonDoublet_rep_repAlgebra :
    leptonDoublet.rep.repAlgebra valIdx = LeptonDoublet.gaugeAlgebraAction := by
  refine LinearMap.ext fun c => LinearMap.ext fun v => ?_
  show MatrixRep.valEnd valIdx (leptonDoublet.rep.act c) v
    = LeptonDoublet.weakEnd (LeptonDoublet.actionMatrix c) v
  erw [leptonDoublet_rep_act]
  obtain ⟨t, rfl⟩ := LeptonDoublet.valLinEquiv.symm.surjective v
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul s w =>
    rw [valIdx_symm_tmul, MatrixRep.valEnd_apply_symm_tmul, LeptonDoublet.weakEnd]
    simp [Matrix.toLpLinAlgEquiv, Matrix.toLpLin_apply, TensorProduct.liftAux_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The Lorentz action of the datum on `LeptonDoublet` is the hand-built action. -/
lemma leptonDoublet_repLorentz :
    MatrixRep.repLorentz valIdx leptonDoublet.lorentz.rep = LeptonDoublet.repLorentzGroup := by
  refine MonoidHom.ext fun Λ => LinearMap.ext fun v => ?_
  obtain ⟨t, rfl⟩ := LeptonDoublet.valLinEquiv.symm.surjective v
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul s w =>
    rw [valIdx_symm_tmul, MatrixRep.repLorentz_apply_symm_tmul, LeptonDoublet.repLorentzGroup]
    simp [LorentzLabel.rep]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The hand-built jet identification on a scalar jet times a pure tensor. -/
lemma jetValLinEquiv_tmul (χ : JetRing) (s : Fermion.LeftHandedWeyl) (v : Fin 2 → ℂ) :
    LeptonDoublet.jetValLinEquiv (χ ⊗ₜ (valIdx).symm (s ⊗ₜ v))
      = s ⊗ₜ WithLp.toLp 2 (fun i => v i • χ) := by
  simp [LeptonDoublet.jetValLinEquiv, TensorProduct.piScalarRight_apply]

/-- The jet identification of the datum and the hand-built one agree on pure tensors. -/
lemma jetEquiv_valIdx_symm_tmul (s : Fermion.LeftHandedWeyl) (y : Fin 2 → JetRing) :
    (MatrixRep.jetEquiv valIdx).symm (s ⊗ₜ y)
      = LeptonDoublet.jetValLinEquiv.symm (s ⊗ₜ WithLp.toLp 2 y) := by
  obtain ⟨t, rfl⟩ := (TensorProduct.piScalarRight ℂ JetRing JetRing (Fin 2)).surjective y
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul f v =>
    simp [-TensorProduct.piScalarRight_apply, MatrixRep.jetEquiv, LeptonDoublet.jetValLinEquiv]
  | add x y hx hy => simp only [map_add, WithLp.toLp_add, tmul_add, hx, hy]

/-- The jet gauge action of the datum on `LeptonDoublet` is the hand-built action. -/
lemma leptonDoublet_rep_repJet :
    leptonDoublet.rep.repJet valIdx = LeptonDoublet.repJetGaugeGroupI := by
  refine MonoidHom.ext fun U => LinearMap.ext fun z => ?_
  change (MatrixRep.jetEquiv valIdx).symm (MatrixRep.jetEnd Fermion.LeftHandedWeyl
      (leptonDoublet.rep.mat U) (MatrixRep.jetEquiv valIdx z))
    = LeptonDoublet.jetValLinEquiv.symm
        (Module.End.lTensorAlgHom ℂ (EuclideanSpace JetRing (Fin 2)) Fermion.LeftHandedWeyl
          ((Matrix.toLpLinAlgEquiv 2 (LeptonDoublet.doubletMatrix U)).restrictScalars ℂ)
          (LeptonDoublet.jetValLinEquiv z))
  erw [leptonDoublet_rep_mat]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul χ v =>
    obtain ⟨t, rfl⟩ := (valIdx).symm.surjective v
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul s w =>
      rw [MatrixRep.jetEquiv_tmul, MatrixRep.jetEnd_tmul, jetValLinEquiv_tmul,
        jetEquiv_valIdx_symm_tmul]
      simp [Matrix.toLpLinAlgEquiv, Matrix.toLpLin_apply, TensorProduct.liftAux_tmul]
    | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **The matter field of the datum on `LeptonDoublet` is the hand-built matter field**:
  the two descriptions of the lepton doublet, the table's and the hand-built one, agree on
  the same target space. -/
theorem leptonDoublet_toMatterFieldOn_eq :
    leptonDoublet.toMatterFieldOn valIdx = LeptonDoublet.matterField := by
  have hL := leptonDoublet_repLorentz
  have hJ := leptonDoublet_rep_repJet
  have hA := leptonDoublet_rep_repAlgebra
  unfold MatterFieldData.toMatterFieldOn MatrixRep.matterField LeptonDoublet.matterField
  congr 1

end Model

end StandardModel
