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

This file carries the structure `IsCovStandardModel` itself — the covariant fields
with their gauge, Lorentz, mass-weight and commutation properties — together with the
algebra they generate. The covariant generators of that algebra are in
`IsCovStandardModel.Generators`, and the mass-weight grading in
`IsCovStandardModel.MassWeight`.

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
  -- *Lorentz transformation*
  -- Every field together with its covariant derivatives transforms as a Lorentz
  -- tensor: each covariant-derivative slot mixes by the Lorentz matrix (ordered
  -- tuples, since covariant derivatives need not commute) and the value index by the
  -- contragredient of the species' Lorentz representation — the conjugate
  -- representation for the barred fields. The two covector indices of the field
  -- strength are explicit, and each mixes by the Lorentz matrix. The Lorentz action
  -- on the algebra is multiplicative.
  repLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂
  repLorentz_H : IsLorentzCovDerivTransforms repLorentz
    (Representation.trivial ℂ SL(2,ℂ) HiggsVec) H
  repLorentz_barH : IsLorentzCovDerivTransforms repLorentz
    (Representation.trivial ℂ SL(2,ℂ) HiggsVec).conj barH
  repLorentz_F : ∀ (Λ : SL(2,ℂ)) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3))
      (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra),
    repLorentz Λ (F l μ ν φ) =
      ∑ p : Fin n → (Fin 1 ⊕ Fin 3),
        (∏ i, (((SL2C.toLorentzGroup Λ).1 (p i) (l i) : ℝ) : ℂ)) •
      ∑ a, (((SL2C.toLorentzGroup Λ).1 a μ : ℝ) : ℂ) •
      ∑ b, (((SL2C.toLorentzGroup Λ).1 b ν : ℝ) : ℂ) • F p a b φ
  repLorentz_d : ∀ i, IsLorentzCovDerivTransforms repLorentz
    DownSinglet.repLorentzGroup (d i)
  repLorentz_bard : ∀ i, IsLorentzCovDerivTransforms repLorentz
    DownSinglet.repLorentzGroup.conj (bard i)
  repLorentz_u : ∀ i, IsLorentzCovDerivTransforms repLorentz
    UpSinglet.repLorentzGroup (u i)
  repLorentz_baru : ∀ i, IsLorentzCovDerivTransforms repLorentz
    UpSinglet.repLorentzGroup.conj (baru i)
  repLorentz_Q : ∀ i, IsLorentzCovDerivTransforms repLorentz
    QuarkDoublet.repLorentzGroup (Q i)
  repLorentz_barQ : ∀ i, IsLorentzCovDerivTransforms repLorentz
    QuarkDoublet.repLorentzGroup.conj (barQ i)
  repLorentz_L : ∀ i, IsLorentzCovDerivTransforms repLorentz
    LeptonDoublet.repLorentzGroup (L i)
  repLorentz_barL : ∀ i, IsLorentzCovDerivTransforms repLorentz
    LeptonDoublet.repLorentzGroup.conj (barL i)
  repLorentz_e : ∀ i, IsLorentzCovDerivTransforms repLorentz
    LeptonSinglet.repLorentzGroup (e i)
  repLorentz_bare : ∀ i, IsLorentzCovDerivTransforms repLorentz
    LeptonSinglet.repLorentzGroup.conj (bare i)
  -- **Mass weights (= 2 * mass dimension)**
  -- Every covariant tower is a `massWeightPoly`-eigenvector of pure monomial weight:
  -- each covariant derivative adds one to the mass dimension, so the Higgs towers
  -- have mass dimension `1 + n` (weight `2 * (1 + n)`), the field-strength towers
  -- mass dimension `2 + n` (weight `2 * (2 + n)`), and the fermion towers mass
  -- dimension `3/2 + n` (weight `3 + 2 * n`)
  massWeight_H : ∀ {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) φ,
    massWeightPoly (H l φ) = Polynomial.monomial (2 * (1 + n)) (H l φ)
  massWeight_barH : ∀ {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) φ,
    massWeightPoly (barH l φ) = Polynomial.monomial (2 * (1 + n)) (barH l φ)
  massWeight_F : ∀ {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3) φ,
    massWeightPoly (F l μ ν φ) = Polynomial.monomial (2 * (2 + n)) (F l μ ν φ)
  massWeight_d : ∀ i {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) φ,
    massWeightPoly (d i l φ) = Polynomial.monomial (3 + 2 * n) (d i l φ)
  massWeight_bard : ∀ i {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) φ,
    massWeightPoly (bard i l φ) = Polynomial.monomial (3 + 2 * n) (bard i l φ)
  massWeight_u : ∀ i {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) φ,
    massWeightPoly (u i l φ) = Polynomial.monomial (3 + 2 * n) (u i l φ)
  massWeight_baru : ∀ i {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) φ,
    massWeightPoly (baru i l φ) = Polynomial.monomial (3 + 2 * n) (baru i l φ)
  massWeight_Q : ∀ i {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) φ,
    massWeightPoly (Q i l φ) = Polynomial.monomial (3 + 2 * n) (Q i l φ)
  massWeight_barQ : ∀ i {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) φ,
    massWeightPoly (barQ i l φ) = Polynomial.monomial (3 + 2 * n) (barQ i l φ)
  massWeight_L : ∀ i {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) φ,
    massWeightPoly (L i l φ) = Polynomial.monomial (3 + 2 * n) (L i l φ)
  massWeight_barL : ∀ i {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) φ,
    massWeightPoly (barL i l φ) = Polynomial.monomial (3 + 2 * n) (barL i l φ)
  massWeight_e : ∀ i {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) φ,
    massWeightPoly (e i l φ) = Polynomial.monomial (3 + 2 * n) (e i l φ)
  massWeight_bare : ∀ i {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) φ,
    massWeightPoly (bare i l φ) = Polynomial.monomial (3 + 2 * n) (bare i l φ)
  -- **The commutation rules**
  -- The gauge sector is bosonic: every field-strength tower commutes with every
  -- field.
  F_comm_F : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
      (ψ : Module.Dual ℝ GaugeAlgebra) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (μ' ν' : Fin 1 ⊕ Fin 3) (ψ' : Module.Dual ℝ GaugeAlgebra),
    Commute (F l μ ν ψ) (F l' μ' ν' ψ')
  F_comm_H : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
      (ψ : Module.Dual ℝ GaugeAlgebra) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ HiggsVec),
    Commute (F l μ ν ψ) (H l' φ)
  F_comm_barH : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
      (ψ : Module.Dual ℝ GaugeAlgebra) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ (ConjModule HiggsVec)),
    Commute (F l μ ν ψ) (barH l' φ)
  F_comm_d : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
      (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ DownSinglet),
    Commute (F l μ ν ψ) (d i l' φ)
  F_comm_bard : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
      (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ (ConjModule DownSinglet)),
    Commute (F l μ ν ψ) (bard i l' φ)
  F_comm_u : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
      (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ UpSinglet),
    Commute (F l μ ν ψ) (u i l' φ)
  F_comm_baru : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
      (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ (ConjModule UpSinglet)),
    Commute (F l μ ν ψ) (baru i l' φ)
  F_comm_Q : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
      (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ QuarkDoublet),
    Commute (F l μ ν ψ) (Q i l' φ)
  F_comm_barQ : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
      (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ (ConjModule QuarkDoublet)),
    Commute (F l μ ν ψ) (barQ i l' φ)
  F_comm_L : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
      (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ LeptonDoublet),
    Commute (F l μ ν ψ) (L i l' φ)
  F_comm_barL : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
      (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ (ConjModule LeptonDoublet)),
    Commute (F l μ ν ψ) (barL i l' φ)
  F_comm_e : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
      (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ LeptonSinglet),
    Commute (F l μ ν ψ) (e i l' φ)
  F_comm_bare : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
      (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ (ConjModule LeptonSinglet)),
    Commute (F l μ ν ψ) (bare i l' φ)
  -- The Higgs sector is bosonic: the Higgs towers and their conjugates commute
  -- with each other and with every fermion.
  H_comm_H : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ HiggsVec) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ HiggsVec),
    Commute (H l φ) (H l' φ')
  H_comm_barH : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ HiggsVec) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ (ConjModule HiggsVec)),
    Commute (H l φ) (barH l' φ')
  barH_comm_barH : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ (ConjModule HiggsVec)) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ (ConjModule HiggsVec)),
    Commute (barH l φ) (barH l' φ')
  H_comm_d : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ DownSinglet),
    Commute (H l φ) (d i l' φ')
  H_comm_bard : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ (ConjModule DownSinglet)),
    Commute (H l φ) (bard i l' φ')
  H_comm_u : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ UpSinglet),
    Commute (H l φ) (u i l' φ')
  H_comm_baru : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ (ConjModule UpSinglet)),
    Commute (H l φ) (baru i l' φ')
  H_comm_Q : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ QuarkDoublet),
    Commute (H l φ) (Q i l' φ')
  H_comm_barQ : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)),
    Commute (H l φ) (barQ i l' φ')
  H_comm_L : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ LeptonDoublet),
    Commute (H l φ) (L i l' φ')
  H_comm_barL : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    Commute (H l φ) (barL i l' φ')
  H_comm_e : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ LeptonSinglet),
    Commute (H l φ) (e i l' φ')
  H_comm_bare : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ HiggsVec) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    Commute (H l φ) (bare i l' φ')
  barH_comm_d : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ DownSinglet),
    Commute (barH l φ) (d i l' φ')
  barH_comm_bard : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ (ConjModule DownSinglet)),
    Commute (barH l φ) (bard i l' φ')
  barH_comm_u : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ UpSinglet),
    Commute (barH l φ) (u i l' φ')
  barH_comm_baru : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ (ConjModule UpSinglet)),
    Commute (barH l φ) (baru i l' φ')
  barH_comm_Q : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ QuarkDoublet),
    Commute (barH l φ) (Q i l' φ')
  barH_comm_barQ : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)),
    Commute (barH l φ) (barQ i l' φ')
  barH_comm_L : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ LeptonDoublet),
    Commute (barH l φ) (L i l' φ')
  barH_comm_barL : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    Commute (barH l φ) (barL i l' φ')
  barH_comm_e : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ LeptonSinglet),
    Commute (barH l φ) (e i l' φ')
  barH_comm_bare : ∀ {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℂ (ConjModule HiggsVec)) (i : Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
      (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    Commute (barH l φ) (bare i l' φ')
  -- The fermion sector: any two fermionic towers anticommute. On the diagonal
  -- (same species, family, derivative slots and dual vector) this forces the
  -- square of every fermionic symbol to vanish, since `2` is invertible in `B`.
  d_anticomm_d : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ DownSinglet)
      (φ' : Module.Dual ℂ DownSinglet),
    d i l φ * d j l' φ' = -(d j l' φ' * d i l φ)
  d_anticomm_bard : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ DownSinglet)
      (φ' : Module.Dual ℂ (ConjModule DownSinglet)),
    d i l φ * bard j l' φ' = -(bard j l' φ' * d i l φ)
  d_anticomm_u : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ DownSinglet)
      (φ' : Module.Dual ℂ UpSinglet),
    d i l φ * u j l' φ' = -(u j l' φ' * d i l φ)
  d_anticomm_baru : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ DownSinglet)
      (φ' : Module.Dual ℂ (ConjModule UpSinglet)),
    d i l φ * baru j l' φ' = -(baru j l' φ' * d i l φ)
  d_anticomm_Q : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ DownSinglet)
      (φ' : Module.Dual ℂ QuarkDoublet),
    d i l φ * Q j l' φ' = -(Q j l' φ' * d i l φ)
  d_anticomm_barQ : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ DownSinglet)
      (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)),
    d i l φ * barQ j l' φ' = -(barQ j l' φ' * d i l φ)
  d_anticomm_L : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ DownSinglet)
      (φ' : Module.Dual ℂ LeptonDoublet),
    d i l φ * L j l' φ' = -(L j l' φ' * d i l φ)
  d_anticomm_barL : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ DownSinglet)
      (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    d i l φ * barL j l' φ' = -(barL j l' φ' * d i l φ)
  d_anticomm_e : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ DownSinglet)
      (φ' : Module.Dual ℂ LeptonSinglet),
    d i l φ * e j l' φ' = -(e j l' φ' * d i l φ)
  d_anticomm_bare : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ DownSinglet)
      (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    d i l φ * bare j l' φ' = -(bare j l' φ' * d i l φ)
  bard_anticomm_bard : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule DownSinglet))
      (φ' : Module.Dual ℂ (ConjModule DownSinglet)),
    bard i l φ * bard j l' φ' = -(bard j l' φ' * bard i l φ)
  bard_anticomm_u : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule DownSinglet))
      (φ' : Module.Dual ℂ UpSinglet),
    bard i l φ * u j l' φ' = -(u j l' φ' * bard i l φ)
  bard_anticomm_baru : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule DownSinglet))
      (φ' : Module.Dual ℂ (ConjModule UpSinglet)),
    bard i l φ * baru j l' φ' = -(baru j l' φ' * bard i l φ)
  bard_anticomm_Q : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule DownSinglet))
      (φ' : Module.Dual ℂ QuarkDoublet),
    bard i l φ * Q j l' φ' = -(Q j l' φ' * bard i l φ)
  bard_anticomm_barQ : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule DownSinglet))
      (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)),
    bard i l φ * barQ j l' φ' = -(barQ j l' φ' * bard i l φ)
  bard_anticomm_L : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule DownSinglet))
      (φ' : Module.Dual ℂ LeptonDoublet),
    bard i l φ * L j l' φ' = -(L j l' φ' * bard i l φ)
  bard_anticomm_barL : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule DownSinglet))
      (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    bard i l φ * barL j l' φ' = -(barL j l' φ' * bard i l φ)
  bard_anticomm_e : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule DownSinglet))
      (φ' : Module.Dual ℂ LeptonSinglet),
    bard i l φ * e j l' φ' = -(e j l' φ' * bard i l φ)
  bard_anticomm_bare : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule DownSinglet))
      (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    bard i l φ * bare j l' φ' = -(bare j l' φ' * bard i l φ)
  u_anticomm_u : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ UpSinglet)
      (φ' : Module.Dual ℂ UpSinglet),
    u i l φ * u j l' φ' = -(u j l' φ' * u i l φ)
  u_anticomm_baru : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ UpSinglet)
      (φ' : Module.Dual ℂ (ConjModule UpSinglet)),
    u i l φ * baru j l' φ' = -(baru j l' φ' * u i l φ)
  u_anticomm_Q : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ UpSinglet)
      (φ' : Module.Dual ℂ QuarkDoublet),
    u i l φ * Q j l' φ' = -(Q j l' φ' * u i l φ)
  u_anticomm_barQ : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ UpSinglet)
      (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)),
    u i l φ * barQ j l' φ' = -(barQ j l' φ' * u i l φ)
  u_anticomm_L : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ UpSinglet)
      (φ' : Module.Dual ℂ LeptonDoublet),
    u i l φ * L j l' φ' = -(L j l' φ' * u i l φ)
  u_anticomm_barL : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ UpSinglet)
      (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    u i l φ * barL j l' φ' = -(barL j l' φ' * u i l φ)
  u_anticomm_e : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ UpSinglet)
      (φ' : Module.Dual ℂ LeptonSinglet),
    u i l φ * e j l' φ' = -(e j l' φ' * u i l φ)
  u_anticomm_bare : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ UpSinglet)
      (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    u i l φ * bare j l' φ' = -(bare j l' φ' * u i l φ)
  baru_anticomm_baru : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule UpSinglet))
      (φ' : Module.Dual ℂ (ConjModule UpSinglet)),
    baru i l φ * baru j l' φ' = -(baru j l' φ' * baru i l φ)
  baru_anticomm_Q : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule UpSinglet))
      (φ' : Module.Dual ℂ QuarkDoublet),
    baru i l φ * Q j l' φ' = -(Q j l' φ' * baru i l φ)
  baru_anticomm_barQ : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule UpSinglet))
      (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)),
    baru i l φ * barQ j l' φ' = -(barQ j l' φ' * baru i l φ)
  baru_anticomm_L : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule UpSinglet))
      (φ' : Module.Dual ℂ LeptonDoublet),
    baru i l φ * L j l' φ' = -(L j l' φ' * baru i l φ)
  baru_anticomm_barL : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule UpSinglet))
      (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    baru i l φ * barL j l' φ' = -(barL j l' φ' * baru i l φ)
  baru_anticomm_e : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule UpSinglet))
      (φ' : Module.Dual ℂ LeptonSinglet),
    baru i l φ * e j l' φ' = -(e j l' φ' * baru i l φ)
  baru_anticomm_bare : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule UpSinglet))
      (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    baru i l φ * bare j l' φ' = -(bare j l' φ' * baru i l φ)
  Q_anticomm_Q : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ QuarkDoublet)
      (φ' : Module.Dual ℂ QuarkDoublet),
    Q i l φ * Q j l' φ' = -(Q j l' φ' * Q i l φ)
  Q_anticomm_barQ : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ QuarkDoublet)
      (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)),
    Q i l φ * barQ j l' φ' = -(barQ j l' φ' * Q i l φ)
  Q_anticomm_L : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ QuarkDoublet)
      (φ' : Module.Dual ℂ LeptonDoublet),
    Q i l φ * L j l' φ' = -(L j l' φ' * Q i l φ)
  Q_anticomm_barL : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ QuarkDoublet)
      (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    Q i l φ * barL j l' φ' = -(barL j l' φ' * Q i l φ)
  Q_anticomm_e : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ QuarkDoublet)
      (φ' : Module.Dual ℂ LeptonSinglet),
    Q i l φ * e j l' φ' = -(e j l' φ' * Q i l φ)
  Q_anticomm_bare : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ QuarkDoublet)
      (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    Q i l φ * bare j l' φ' = -(bare j l' φ' * Q i l φ)
  barQ_anticomm_barQ : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule QuarkDoublet))
      (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)),
    barQ i l φ * barQ j l' φ' = -(barQ j l' φ' * barQ i l φ)
  barQ_anticomm_L : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule QuarkDoublet))
      (φ' : Module.Dual ℂ LeptonDoublet),
    barQ i l φ * L j l' φ' = -(L j l' φ' * barQ i l φ)
  barQ_anticomm_barL : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule QuarkDoublet))
      (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    barQ i l φ * barL j l' φ' = -(barL j l' φ' * barQ i l φ)
  barQ_anticomm_e : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule QuarkDoublet))
      (φ' : Module.Dual ℂ LeptonSinglet),
    barQ i l φ * e j l' φ' = -(e j l' φ' * barQ i l φ)
  barQ_anticomm_bare : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule QuarkDoublet))
      (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    barQ i l φ * bare j l' φ' = -(bare j l' φ' * barQ i l φ)
  L_anticomm_L : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ LeptonDoublet)
      (φ' : Module.Dual ℂ LeptonDoublet),
    L i l φ * L j l' φ' = -(L j l' φ' * L i l φ)
  L_anticomm_barL : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ LeptonDoublet)
      (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    L i l φ * barL j l' φ' = -(barL j l' φ' * L i l φ)
  L_anticomm_e : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ LeptonDoublet)
      (φ' : Module.Dual ℂ LeptonSinglet),
    L i l φ * e j l' φ' = -(e j l' φ' * L i l φ)
  L_anticomm_bare : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ LeptonDoublet)
      (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    L i l φ * bare j l' φ' = -(bare j l' φ' * L i l φ)
  barL_anticomm_barL : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule LeptonDoublet))
      (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    barL i l φ * barL j l' φ' = -(barL j l' φ' * barL i l φ)
  barL_anticomm_e : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule LeptonDoublet))
      (φ' : Module.Dual ℂ LeptonSinglet),
    barL i l φ * e j l' φ' = -(e j l' φ' * barL i l φ)
  barL_anticomm_bare : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule LeptonDoublet))
      (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    barL i l φ * bare j l' φ' = -(bare j l' φ' * barL i l φ)
  e_anticomm_e : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ LeptonSinglet)
      (φ' : Module.Dual ℂ LeptonSinglet),
    e i l φ * e j l' φ' = -(e j l' φ' * e i l φ)
  e_anticomm_bare : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ LeptonSinglet)
      (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    e i l φ * bare j l' φ' = -(bare j l' φ' * e i l φ)
  bare_anticomm_bare : ∀ (i j : Fin 3) {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
      (l' : Fin m → Fin 1 ⊕ Fin 3) (φ : Module.Dual ℂ (ConjModule LeptonSinglet))
      (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    bare i l φ * bare j l' φ' = -(bare j l' φ' * bare i l φ)

namespace IsCovStandardModel

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  {H : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ HiggsVec →ₗ[ℂ] B}
  {barH : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule HiggsVec) →ₗ[ℂ] B}
  {F : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) →
    Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B}
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
  (h : IsCovStandardModel B repGauge repLorentz massWeightPoly H barH F
    d bard u baru Q barQ L barL e bare)

/-!

## A. The gauge and Lorentz actions

The two actions on the algebra are multiplicative, so each is a unital algebra
automorphism; in particular each fixes the unit.

-/

include h in
/-- The multiplicative gauge action fixes the unit of the algebra. -/
lemma repGauge_one (g : GaugeGroupI) : repGauge g (1 : B) = 1 := by
  obtain ⟨u, hu⟩ : ∃ u, repGauge g u = 1 :=
    ⟨repGauge g⁻¹ 1, by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one repGauge,
        Module.End.one_apply]⟩
  have h1 := h.repGauge_mul g u 1
  rw [mul_one, hu, one_mul] at h1
  exact h1.symm

include h in
/-- The multiplicative Lorentz action fixes the unit of the algebra. -/
lemma repLorentz_one (Λ : SL(2,ℂ)) : repLorentz Λ (1 : B) = 1 := by
  obtain ⟨u, hu⟩ : ∃ u, repLorentz Λ u = 1 :=
    ⟨repLorentz Λ⁻¹ 1, by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one repLorentz,
        Module.End.one_apply]⟩
  have h1 := h.repLorentz_mul Λ u 1
  rw [mul_one, hu, one_mul] at h1
  exact h1.symm

/-!

## B. The field algebra

-/

/-- The algebra generated by all the covariant fields of the Standard Model: the
  covariant-derivative towers of the field strength, of the Higgs and its conjugate,
  and of the three families of each fermion species with their conjugates. -/
def fieldAlgebra (_ : IsCovStandardModel B repGauge repLorentz massWeightPoly H barH F
    d bard u baru Q barQ L barL e bare) : Subalgebra ℂ B :=
  Algebra.adjoin ℂ
    ((⋃ (n : ℕ) (l : Fin n → Fin 1 ⊕ Fin 3) (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3),
        Set.range (F l μ ν)) ∪
      (⋃ (n : ℕ) (l : Fin n → Fin 1 ⊕ Fin 3), Set.range (H l) ∪ Set.range (barH l)) ∪
      (⋃ (i : Fin 3) (n : ℕ) (l : Fin n → Fin 1 ⊕ Fin 3),
        Set.range (d i l) ∪ Set.range (bard i l) ∪
        Set.range (u i l) ∪ Set.range (baru i l) ∪
        Set.range (Q i l) ∪ Set.range (barQ i l) ∪
        Set.range (L i l) ∪ Set.range (barL i l) ∪
        Set.range (e i l) ∪ Set.range (bare i l)))

/-!

### B.1. Basic commutation relations

-/

lemma F_commute_mem_fieldAlgebra {n : ℕ} {l : Fin n → Fin 1 ⊕ Fin 3} {μ ν : Fin 1 ⊕ Fin 3}
    (φ : Module.Dual ℝ GaugeAlgebra) (x : B) (hx : x ∈ h.fieldAlgebra) :
    F l μ ν φ * x = x * F l μ ν φ := by
  rw [fieldAlgebra] at hx
  refine (IsGaugeField.commute_of_mem_adjoin (y := F l μ ν φ) ?_ hx).symm
  intro z hz
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_range] at hz
  obtain ((⟨n', l', μ', ν', ψ, rfl⟩ | ⟨n', l', ⟨φ', rfl⟩ | ⟨φ', rfl⟩⟩) | ⟨i, n', l', hz⟩) := hz
  · exact (h.F_comm_F l μ ν φ l' μ' ν' ψ).symm
  · exact (h.F_comm_H l μ ν φ l' φ').symm
  · exact (h.F_comm_barH l μ ν φ l' φ').symm
  · obtain (((((((((⟨φ', rfl⟩ | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) |
      ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) := hz
    · exact (h.F_comm_d l μ ν φ i l' φ').symm
    · exact (h.F_comm_bard l μ ν φ i l' φ').symm
    · exact (h.F_comm_u l μ ν φ i l' φ').symm
    · exact (h.F_comm_baru l μ ν φ i l' φ').symm
    · exact (h.F_comm_Q l μ ν φ i l' φ').symm
    · exact (h.F_comm_barQ l μ ν φ i l' φ').symm
    · exact (h.F_comm_L l μ ν φ i l' φ').symm
    · exact (h.F_comm_barL l μ ν φ i l' φ').symm
    · exact (h.F_comm_e l μ ν φ i l' φ').symm
    · exact (h.F_comm_bare l μ ν φ i l' φ').symm

lemma H_commute_mem_fieldAlgebra {n : ℕ} {l : Fin n → Fin 1 ⊕ Fin 3}
    (φ : Module.Dual ℂ HiggsVec) (x : B) (hx : x ∈ h.fieldAlgebra) :
    H l φ * x = x * H l φ := by
  rw [fieldAlgebra] at hx
  refine (IsGaugeField.commute_of_mem_adjoin (y := H l φ) ?_ hx).symm
  intro z hz
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_range] at hz
  obtain ((⟨n', l', μ', ν', ψ, rfl⟩ | ⟨n', l', ⟨φ', rfl⟩ | ⟨φ', rfl⟩⟩) | ⟨i, n', l', hz⟩) := hz
  · exact h.F_comm_H l' μ' ν' ψ l φ
  · exact h.H_comm_H l' φ' l φ
  · exact (h.H_comm_barH l φ l' φ').symm
  · obtain (((((((((⟨φ', rfl⟩ | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) |
      ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) := hz
    · exact (h.H_comm_d l φ i l' φ').symm
    · exact (h.H_comm_bard l φ i l' φ').symm
    · exact (h.H_comm_u l φ i l' φ').symm
    · exact (h.H_comm_baru l φ i l' φ').symm
    · exact (h.H_comm_Q l φ i l' φ').symm
    · exact (h.H_comm_barQ l φ i l' φ').symm
    · exact (h.H_comm_L l φ i l' φ').symm
    · exact (h.H_comm_barL l φ i l' φ').symm
    · exact (h.H_comm_e l φ i l' φ').symm
    · exact (h.H_comm_bare l φ i l' φ').symm

lemma barH_commute_mem_fieldAlgebra {n : ℕ} {l : Fin n → Fin 1 ⊕ Fin 3}
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) (x : B) (hx : x ∈ h.fieldAlgebra) :
    barH l φ * x = x * barH l φ := by
  rw [fieldAlgebra] at hx
  refine (IsGaugeField.commute_of_mem_adjoin (y := barH l φ) ?_ hx).symm
  intro z hz
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_range] at hz
  obtain ((⟨n', l', μ', ν', ψ, rfl⟩ | ⟨n', l', ⟨φ', rfl⟩ | ⟨φ', rfl⟩⟩) | ⟨i, n', l', hz⟩) := hz
  · exact h.F_comm_barH l' μ' ν' ψ l φ
  · exact h.H_comm_barH l' φ' l φ
  · exact h.barH_comm_barH l' φ' l φ
  · obtain (((((((((⟨φ', rfl⟩ | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) |
      ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) := hz
    · exact (h.barH_comm_d l φ i l' φ').symm
    · exact (h.barH_comm_bard l φ i l' φ').symm
    · exact (h.barH_comm_u l φ i l' φ').symm
    · exact (h.barH_comm_baru l φ i l' φ').symm
    · exact (h.barH_comm_Q l φ i l' φ').symm
    · exact (h.barH_comm_barQ l φ i l' φ').symm
    · exact (h.barH_comm_L l φ i l' φ').symm
    · exact (h.barH_comm_barL l φ i l' φ').symm
    · exact (h.barH_comm_e l φ i l' φ').symm
    · exact (h.barH_comm_bare l φ i l' φ').symm

end IsCovStandardModel

end StandardModel
