/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module
public import Physlib.Particles.StandardModel.Fermions.DownSinglet.GaugeAlgebraAction
public import Physlib.Particles.StandardModel.Fermions.LeptonDoublet.GaugeAlgebraAction
public import Physlib.Particles.StandardModel.Fermions.LeptonSinglet.GaugeAlgebraAction
public import Physlib.Particles.StandardModel.Fermions.QuarkDoublet.GaugeAlgebraAction
public import Physlib.Particles.StandardModel.Fermions.UpSinglet.GaugeAlgebraAction
public import Physlib.Particles.StandardModel.GaugeBosons.AlgebraValued.Symmeterized
public import Physlib.Particles.StandardModel.HiggsBoson.GaugeAlgebraAction
/-!
# The algebra valued Standard model

The basic idea here is to just reduce things
down to the covariant version.
In the covariant version we will do the work with
the invariants.

-/

@[expose] public section

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz

structure IsCovStandardModel (B : Type) [Ring B] [Algebra ℂ B]
    -- The representations
    (repGauge : Representation ℂ GaugeGroupI B) (repLorentz : Representation ℂ SL(2,ℂ) B)
    -- The mass weights
    (massWeightPoly : B →ₐ[ℂ] Polynomial B)
    -- The Higgs fields + covariant derivatives
    (H : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ HiggsVec →ₗ[ℂ] B)
    (barH : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule HiggsVec) →ₗ[ℂ] B)
    -- The field strength + covariant derivatives derivatives
    (F : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) →
      Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    -- Three families of down-type quarks + derivatives + conjugates
    (d : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ DownSinglet →ₗ[ℂ] B)
    (bard : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule DownSinglet) →ₗ[ℂ] B)
    -- Three families of up-type quarks + derivatives + conjugates
    (u : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ UpSinglet →ₗ[ℂ] B)
    (baru :{n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule UpSinglet) →ₗ[ℂ] B)
    -- Three families of quark doublets + derivatives + conjugates
    (Q : {n : ℕ} →Fin 3 → (Fin n → Fin 1 ⊕ Fin 3)→ Module.Dual ℂ QuarkDoublet →ₗ[ℂ] B)
    (barQ : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule QuarkDoublet) →ₗ[ℂ] B)
    -- Three families of lepton doublets + derivatives + conjugates
    (L : {n : ℕ} → Fin 3  → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonDoublet →ₗ[ℂ] B)
    (barL : {n : ℕ} → Fin 3 →  (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule LeptonDoublet) →ₗ[ℂ] B)
    -- Three families of lepton singlets + derivatives + conjugates
    (e : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonSinglet →ₗ[ℂ] B)
    (bare : {n : ℕ} →  Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule LeptonSinglet) →ₗ[ℂ] B)
    : Prop where
  -- *Gauge transformation*
  -- Every field transforms homogeneously under the global gauge group, which acts on
  -- the dual value index through the dual (contragredient) of the species
  -- representation — the conjugate representation for the barred fields, and the
  -- adjoint action for the field strength. The gauge action on the algebra is
  -- multiplicative.
  repGauge_mul : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
    repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂
  repGauge_H : ∀ (g : GaugeGroupI) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ HiggsVec),
    repGauge g (H l φ) = H l (HiggsVec.repGaugeGroupI.dual g φ)
  repGauge_barH : ∀ (g : GaugeGroupI) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ (ConjModule HiggsVec)),
    repGauge g (barH l φ) = barH l (HiggsVec.repGaugeGroupI.conj.dual g φ)
  repGauge_F : ∀ (g : GaugeGroupI) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra),
    repGauge g (F l μ ν φ) = F l μ ν ((GaugeAlgebra.adjointMap g⁻¹).dualMap φ)
  repGauge_d : ∀ (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
      (l : Fin n → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ DownSinglet),
    repGauge g (d i l φ) = d i l (DownSinglet.repGaugeGroupI.dual g φ)
  repGauge_bard : ∀ (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
      (l : Fin n → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule DownSinglet)),
    repGauge g (bard i l φ) = bard i l (DownSinglet.repGaugeGroupI.conj.dual g φ)
  repGauge_u : ∀ (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
      (l : Fin n → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ UpSinglet),
    repGauge g (u i l φ) = u i l (UpSinglet.repGaugeGroupI.dual g φ)
  repGauge_baru : ∀ (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
      (l : Fin n → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule UpSinglet)),
    repGauge g (baru i l φ) = baru i l (UpSinglet.repGaugeGroupI.conj.dual g φ)
  repGauge_Q : ∀ (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
      (l : Fin n → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ QuarkDoublet),
    repGauge g (Q i l φ) = Q i l (QuarkDoublet.repGaugeGroupI.dual g φ)
  repGauge_barQ : ∀ (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
      (l : Fin n → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule QuarkDoublet)),
    repGauge g (barQ i l φ) = barQ i l (QuarkDoublet.repGaugeGroupI.conj.dual g φ)
  repGauge_L : ∀ (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
      (l : Fin n → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ LeptonDoublet),
    repGauge g (L i l φ) = L i l (LeptonDoublet.repGaugeGroupI.dual g φ)
  repGauge_barL : ∀ (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
      (l : Fin n → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule LeptonDoublet)),
    repGauge g (barL i l φ) = barL i l (LeptonDoublet.repGaugeGroupI.conj.dual g φ)
  repGauge_e : ∀ (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
      (l : Fin n → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ LeptonSinglet),
    repGauge g (e i l φ) = e i l (LeptonSinglet.repGaugeGroupI.dual g φ)
  repGauge_bare : ∀ (g : GaugeGroupI) (i : Fin 3) {n : ℕ}
      (l : Fin n → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule LeptonSinglet)),
    repGauge g (bare i l φ) = bare i l (LeptonSinglet.repGaugeGroupI.conj.dual g φ)

end StandardModel
