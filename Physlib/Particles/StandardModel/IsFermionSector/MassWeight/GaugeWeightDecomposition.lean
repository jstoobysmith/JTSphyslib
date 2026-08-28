/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsFermionSector.MassWeight.Basic
public import Physlib.Particles.StandardModel.IsFermionSector.DerivSubmodule.GaugeWeightDecomposition
/-!
# The gauge weight decomposition of the fermion mass-weight submodules

Each mass-weight submodule of the fermion sector up to weight eight has an explicit
description in terms of the derivative submodules, and the derivative submodules carry
a gauge weight decomposition.  Transporting the latter along the former decomposes
every mass-weight submodule up to weight eight: weights one, two and four are trivial,
weights three, five and seven are the towers with zero, one and two covariant
derivatives, weight six is the product of two underived towers, and weight eight is the
kinetic sector.

-/

@[expose] public section

namespace StandardModel

open Matrix MatrixGroups

namespace IsFermionSector

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {hrepGauge_mul : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
    repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {hrepLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂}
  {d : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ DownSinglet →ₗ[ℂ] B}
  {bard : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule DownSinglet) →ₗ[ℂ] B}
  {u : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ UpSinglet →ₗ[ℂ] B}
  {baru : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule UpSinglet) →ₗ[ℂ] B}
  {Q : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ QuarkDoublet →ₗ[ℂ] B}
  {barQ : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule QuarkDoublet) →ₗ[ℂ] B}
  {L : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonDoublet →ₗ[ℂ] B}
  {barL : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule LeptonDoublet) →ₗ[ℂ] B}
  {e : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonSinglet →ₗ[ℂ] B}
  {bare : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule LeptonSinglet) →ₗ[ℂ] B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : IsFermionSector B repGauge hrepGauge_mul repLorentz hrepLorentz_mul
      d bard u baru Q barQ L barL e bare massWeightPoly)

/-- Weight one is trivial. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightOne :
    GaugeWeightDecomposition repGauge (h.massWeightSubmodule 1) :=
  GaugeWeightDecomposition.copy (GaugeWeightDecomposition.bot hrepGauge_mul) _
    h.massWeightSubmodule_one_eq

/-- Weight two is trivial. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightTwo :
    GaugeWeightDecomposition repGauge (h.massWeightSubmodule 2) :=
  GaugeWeightDecomposition.copy (GaugeWeightDecomposition.bot hrepGauge_mul) _
    h.massWeightSubmodule_two_eq

/-- Weight three is the underived fermion towers. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightThree :
    GaugeWeightDecomposition repGauge (h.massWeightSubmodule 3) :=
  GaugeWeightDecomposition.copy (h.derivSubmoduleGaugeWeight 0) _
    h.massWeightSubmodule_three_eq

/-- Weight four is trivial. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightFour :
    GaugeWeightDecomposition repGauge (h.massWeightSubmodule 4) :=
  GaugeWeightDecomposition.copy (GaugeWeightDecomposition.bot hrepGauge_mul) _
    h.massWeightSubmodule_four_eq

/-- Weight five is the once-derived fermion towers. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightFive :
    GaugeWeightDecomposition repGauge (h.massWeightSubmodule 5) :=
  GaugeWeightDecomposition.copy (h.derivSubmoduleGaugeWeight 1) _
    h.massWeightSubmodule_five_eq

/-- Weight six is the products of two underived fermion towers. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightSix :
    GaugeWeightDecomposition repGauge (h.massWeightSubmodule 6) :=
  GaugeWeightDecomposition.copy (GaugeWeightDecomposition.mul (d := h.derivSubmoduleGaugeWeight 0)
      (d' := h.derivSubmoduleGaugeWeight 0)) _
    h.massWeightSubmodule_six_eq

/-- Weight seven is the twice-derived fermion towers. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightSeven :
    GaugeWeightDecomposition repGauge (h.massWeightSubmodule 7) :=
  GaugeWeightDecomposition.copy (h.derivSubmoduleGaugeWeight 2) _
    h.massWeightSubmodule_seven_eq

/-- Weight eight is the kinetic sector: an underived tower against a once-derived one. -/
@[implicit_reducible]
noncomputable def massWeightSubmoduleGaugeWeightEight :
    GaugeWeightDecomposition repGauge (h.massWeightSubmodule 8) :=
  GaugeWeightDecomposition.copy (GaugeWeightDecomposition.mul (d := h.derivSubmoduleGaugeWeight 0)
      (d' := h.derivSubmoduleGaugeWeight 1)) _
    h.massWeightSubmodule_eight_eq

end IsFermionSector

end StandardModel
