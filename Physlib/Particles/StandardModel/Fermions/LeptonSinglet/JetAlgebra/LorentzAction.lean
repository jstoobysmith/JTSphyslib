/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.Particles.StandardModel.Fermions.LeptonSinglet.JetAlgebra.Basic
/-!
# The Lorentz action on the charged-lepton jet algebra

## i. Overview

The Lorentz group acts on the jet algebra of the charged-lepton singlet by the
exterior-algebra functor applied to its action on the jet component space. On a
generator the derivative symbols transform by the Lorentz matrix and the spinor
index contragrediently.

## ii. Key results

- `JetAlgebra.repLorentzGroup` : the Lorentz action on the jet algebra.
- `JetAlgebra.repLorentzGroup_ofGenerator` : the action on a generator.
- `JetAlgebra.repLorentzGroupAlgHom` : the action as an algebra homomorphism.

## iii. Table of contents

- A. The action of the Lorentz group

-/

@[expose] public section

namespace StandardModel

namespace LeptonSinglet

namespace JetAlgebra

open Matrix MatrixGroups

/-!

## A. The action of the Lorentz group

-/

noncomputable def repLorentzGroup : Representation ℂ SL(2,ℂ) JetAlgebra where
  toFun g := (ExteriorAlgebra.map (JetComponentSpace.repLorentzGroup g)).toLinearMap
  map_one' := by
    simp only [map_one, Module.End.one_eq_id, ExteriorAlgebra.map_id,
      AlgHom.toLinearMap_id]
  map_mul' g1 g2 := by
    simp only [map_mul, Module.End.mul_eq_comp, ← ExteriorAlgebra.map_comp_map,
      AlgHom.comp_toLinearMap]

lemma repLorentzGroup_apply (g : SL(2,ℂ)) (x : JetAlgebra) :
    repLorentzGroup g x =
      ExteriorAlgebra.map (JetComponentSpace.repLorentzGroup g) x := rfl

lemma repLorentzGroup_apply_one (g : SL(2,ℂ)) :
    repLorentzGroup g 1 = 1 := by simp [repLorentzGroup_apply]

lemma repLorentzGroup_apply_mul (g : SL(2,ℂ)) (x y : JetAlgebra) :
    repLorentzGroup g (x * y) = repLorentzGroup g x * repLorentzGroup g y := by
  simp [repLorentzGroup_apply]

/-- The Lorentz action on a jet-algebra generator. -/
lemma repLorentzGroup_ofGenerator (Λ : SL(2,ℂ)) (j : JetGenerators) :
    repLorentzGroup Λ (ofGenerator j) =
      ExteriorAlgebra.ι ℂ
        (JetComponentSpace.repLorentzGroup Λ (JetComponentSpace.basis j)) := by
  rw [ofGenerator, repLorentzGroup_apply, ExteriorAlgebra.map_apply_ι]

/-- The Lorentz action on the zeroth-order lepton generator. -/
lemma repLorentzGroup_ofGenerator_ψ_nil (Λ : SL(2,ℂ)) (α : Fin 2) :
    repLorentzGroup Λ (ofGenerator (.dψ {} α)) =
      ∑ β, star ((Λ⁻¹).1 α β) • ofGenerator (.dψ {} β) := by
  rw [repLorentzGroup_ofGenerator,
    JetComponentSpace.repLorentzGroup_basis_dψ_nil, map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul, ofGenerator]

/-- The Lorentz action on the first-order lepton generator. -/
lemma repLorentzGroup_ofGenerator_ψ_singleton (Λ : SL(2,ℂ))
    (μ : Fin 1 ⊕ Fin 3) (α : Fin 2) :
    repLorentzGroup Λ (ofGenerator (.dψ {μ} α)) =
      ∑ ν, ∑ β, ((((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) *
        star ((Λ⁻¹).1 α β)) • ofGenerator (.dψ {ν} β) := by
  rw [repLorentzGroup_ofGenerator,
    JetComponentSpace.repLorentzGroup_basis_dψ_singleton, map_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul, ofGenerator]

/-- The Lorentz action on the zeroth-order conjugate lepton generator. -/
lemma repLorentzGroup_ofGenerator_barψ_nil (Λ : SL(2,ℂ)) (α : Fin 2) :
    repLorentzGroup Λ (ofGenerator (.dbarψ {} α)) =
      ∑ β, (Λ⁻¹).1 α β • ofGenerator (.dbarψ {} β) := by
  rw [repLorentzGroup_ofGenerator,
    JetComponentSpace.repLorentzGroup_basis_dbarψ_nil, map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul, ofGenerator]

/-- The Lorentz action on the first-order conjugate lepton generator. -/
lemma repLorentzGroup_ofGenerator_barψ_singleton (Λ : SL(2,ℂ))
    (μ : Fin 1 ⊕ Fin 3) (α : Fin 2) :
    repLorentzGroup Λ (ofGenerator (.dbarψ {μ} α)) =
      ∑ ν, ∑ β, ((((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) *
        (Λ⁻¹).1 α β) • ofGenerator (.dbarψ {ν} β) := by
  rw [repLorentzGroup_ofGenerator,
    JetComponentSpace.repLorentzGroup_basis_dbarψ_singleton, map_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul, ofGenerator]


noncomputable def repLorentzGroupAlgHom (Λ : SL(2,ℂ)) :
    AlgHom ℂ JetAlgebra JetAlgebra where
  toFun := repLorentzGroup Λ
  map_add' := LinearMap.map_add _
  map_zero' := LinearMap.map_zero _
  map_one' := repLorentzGroup_apply_one Λ
  map_mul' := repLorentzGroup_apply_mul Λ
  commutes' r := by simp [repLorentzGroup_apply]

end JetAlgebra

end LeptonSinglet

end StandardModel
