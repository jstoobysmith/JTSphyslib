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

## A. The field algebra

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

## B. The mass dimension submodules

-/

/-- All elements of the field algebra of mass weight exactly `n`: the intersection of
  the algebra generated by the covariant fields with the part on which
  `massWeightPoly` is the monomial `X ^ n`. -/
noncomputable def massWeightSubmodule
    (h : IsCovStandardModel B repGauge repLorentz massWeightPoly H barH F
    d bard u baru Q barQ L barL e bare) (n : ℕ) : Submodule ℂ B :=
  (h.fieldAlgebra).toSubmodule
    ⊓ LinearMap.ker (massWeightPoly.toLinearMap
      - (Polynomial.monomial n : B →ₗ[B] Polynomial B).restrictScalars ℂ)

lemma massWeightPoly_of_mem_massWeightSubmodule {n : ℕ} {x : B}
    (hx : x ∈ h.massWeightSubmodule n) :
    massWeightPoly x = Polynomial.monomial n x := by
  rw [massWeightSubmodule, Submodule.mem_inf] at hx
  rcases hx with ⟨-, hx'⟩
  rw [LinearMap.mem_ker] at hx'
  simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply, LinearMap.coe_restrictScalars,
    sub_eq_zero] at hx'
  exact hx'

lemma mem_fieldAlgebra_of_mem_massWeightSubmodule {n : ℕ} {x : B}
    (hx : x ∈ h.massWeightSubmodule n) : x ∈ h.fieldAlgebra := by
  rw [massWeightSubmodule, Submodule.mem_inf] at hx
  exact hx.1

/-!

## C. Covariant generators and the weight-graded monomial span

-/

/-- The abstract index of a single covariant generator of the field algebra: one of
  the covariant-derivative towers of the field strength, of the Higgs and its
  conjugate, or of the three families of each fermion species and their conjugates,
  applied to a member of the dual basis of its value space. Only basis indices are
  stored, so for a fixed tower length the generators of a given mass weight form a
  finite type. The evaluation in `B` is `generatorVal`. -/
inductive Generators where
  /-- The Higgs tower `∇_l H` applied to a dual basis vector. -/
  | H : (n : ℕ) → (Fin n → Fin 1 ⊕ Fin 3) → Fin 2 → Generators
  /-- The conjugate-Higgs tower `∇_l H̄` applied to a dual basis vector. -/
  | barH : (n : ℕ) → (Fin n → Fin 1 ⊕ Fin 3) → Fin 2 → Generators
  /-- The field-strength tower `∇_l F_μν` applied to a dual basis vector. -/
  | F : (n : ℕ) → (Fin n → Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) →
      (Fin 8 ⊕ Fin 3 ⊕ Fin 1) → Generators
  /-- The fermion tower `∇_l d` of the `i`-th family applied to a dual basis vector. -/
  | d : Fin 3 → (n : ℕ) → (Fin n → Fin 1 ⊕ Fin 3) → Fin 2 × Fin 3 → Generators
  /-- The fermion tower `∇_l bard` of the `i`-th family applied to a dual basis vector. -/
  | bard : Fin 3 → (n : ℕ) → (Fin n → Fin 1 ⊕ Fin 3) → Fin 2 × Fin 3 → Generators
  /-- The fermion tower `∇_l u` of the `i`-th family applied to a dual basis vector. -/
  | u : Fin 3 → (n : ℕ) → (Fin n → Fin 1 ⊕ Fin 3) → Fin 2 × Fin 3 → Generators
  /-- The fermion tower `∇_l baru` of the `i`-th family applied to a dual basis vector. -/
  | baru : Fin 3 → (n : ℕ) → (Fin n → Fin 1 ⊕ Fin 3) → Fin 2 × Fin 3 → Generators
  /-- The fermion tower `∇_l Q` of the `i`-th family applied to a dual basis vector. -/
  | Q : Fin 3 → (n : ℕ) → (Fin n → Fin 1 ⊕ Fin 3) → Fin 2 × Fin 3 × Fin 2 → Generators
  /-- The fermion tower `∇_l barQ` of the `i`-th family applied to a dual basis vector. -/
  | barQ : Fin 3 → (n : ℕ) → (Fin n → Fin 1 ⊕ Fin 3) → Fin 2 × Fin 3 × Fin 2 → Generators
  /-- The fermion tower `∇_l L` of the `i`-th family applied to a dual basis vector. -/
  | L : Fin 3 → (n : ℕ) → (Fin n → Fin 1 ⊕ Fin 3) → Fin 2 × Fin 2 → Generators
  /-- The fermion tower `∇_l barL` of the `i`-th family applied to a dual basis vector. -/
  | barL : Fin 3 → (n : ℕ) → (Fin n → Fin 1 ⊕ Fin 3) → Fin 2 × Fin 2 → Generators
  /-- The fermion tower `∇_l e` of the `i`-th family applied to a dual basis vector. -/
  | e : Fin 3 → (n : ℕ) → (Fin n → Fin 1 ⊕ Fin 3) → Fin 2 → Generators
  /-- The fermion tower `∇_l bare` of the `i`-th family applied to a dual basis vector. -/
  | bare : Fin 3 → (n : ℕ) → (Fin n → Fin 1 ⊕ Fin 3) → Fin 2 → Generators
deriving DecidableEq

/-- The mass weight (twice the mass dimension) of a covariant generator. -/
def Generators.weight : Generators → ℕ
  | .H n _ _ => 2 * (1 + n)
  | .barH n _ _ => 2 * (1 + n)
  | .F n _ _ _ _ => 2 * (2 + n)
  | .d _ n _ _ => 3 + 2 * n
  | .bard _ n _ _ => 3 + 2 * n
  | .u _ n _ _ => 3 + 2 * n
  | .baru _ n _ _ => 3 + 2 * n
  | .Q _ n _ _ => 3 + 2 * n
  | .barQ _ n _ _ => 3 + 2 * n
  | .L _ n _ _ => 3 + 2 * n
  | .barL _ n _ _ => 3 + 2 * n
  | .e _ n _ _ => 3 + 2 * n
  | .bare _ n _ _ => 3 + 2 * n

set_option linter.unusedVariables false in
/-- The value in `B` of a covariant generator: the corresponding covariant tower
  applied to the indicated dual basis vector of its value space. -/
noncomputable def generatorVal
    (h : IsCovStandardModel B repGauge repLorentz massWeightPoly H barH F
    d bard u baru Q barQ L barL e bare) : Generators → B
  | .H _ l j => H l (HiggsVec.orthonormBasis.toBasis.coord j)
  | .barH _ l j => barH l (HiggsVec.orthonormBasis.toBasis.conj.coord j)
  | .F _ l μ ν j => F l μ ν (GaugeAlgebra.stdBasis.coord j)
  | .d i _ l j => d i l (DownSinglet.basis.coord j)
  | .bard i _ l j => bard i l (DownSinglet.basis.conj.coord j)
  | .u i _ l j => u i l (UpSinglet.basis.coord j)
  | .baru i _ l j => baru i l (UpSinglet.basis.conj.coord j)
  | .Q i _ l j => Q i l (QuarkDoublet.basis.coord j)
  | .barQ i _ l j => barQ i l (QuarkDoublet.basis.conj.coord j)
  | .L i _ l j => L i l (LeptonDoublet.basis.coord j)
  | .barL i _ l j => barL i l (LeptonDoublet.basis.conj.coord j)
  | .e i _ l j => e i l (LeptonSinglet.basis.coord j)
  | .bare i _ l j => bare i l (LeptonSinglet.basis.conj.coord j)

/-- Every covariant generator is a `massWeightPoly`-eigenvector of its weight. -/
lemma massWeightPoly_generatorVal (g : Generators) :
    massWeightPoly (h.generatorVal g) = Polynomial.monomial g.weight (h.generatorVal g) := by
  cases g with
  | H n l j => exact h.massWeight_H l _
  | barH n l j => exact h.massWeight_barH l _
  | F n l μ ν j => exact h.massWeight_F l μ ν _
  | d i n l j => exact h.massWeight_d i l _
  | bard i n l j => exact h.massWeight_bard i l _
  | u i n l j => exact h.massWeight_u i l _
  | baru i n l j => exact h.massWeight_baru i l _
  | Q i n l j => exact h.massWeight_Q i l _
  | barQ i n l j => exact h.massWeight_barQ i l _
  | L i n l j => exact h.massWeight_L i l _
  | barL i n l j => exact h.massWeight_barL i l _
  | e i n l j => exact h.massWeight_e i l _
  | bare i n l j => exact h.massWeight_bare i l _

lemma generatorVal_mem_fieldAlgebra (g : Generators) :
    h.generatorVal g ∈ h.fieldAlgebra := by
  rw [fieldAlgebra]
  refine Algebra.subset_adjoin ?_
  cases g with
    | F n l μ ν j =>
      exact Set.mem_union_left _ (Set.mem_union_left _
        (Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨l, Set.mem_iUnion.mpr ⟨μ,
          Set.mem_iUnion.mpr ⟨ν, ⟨_, rfl⟩⟩⟩⟩⟩))
    | H n l j =>
      exact Set.mem_union_left _ (Set.mem_union_right _
        (Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨l, Set.mem_union_left _ ⟨_, rfl⟩⟩⟩))
    | barH n l j =>
      exact Set.mem_union_left _ (Set.mem_union_right _
        (Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨l, Set.mem_union_right _ ⟨_, rfl⟩⟩⟩))
    | d i n l j =>
      exact Set.mem_union_right _
        (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨l,
          Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (⟨_, rfl⟩)))))))))⟩⟩⟩)
    | bard i n l j =>
      exact Set.mem_union_right _
        (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨l,
          Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ ⟨_, rfl⟩))))))))⟩⟩⟩)
    | u i n l j =>
      exact Set.mem_union_right _
        (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨l,
          Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ ⟨_, rfl⟩)))))))⟩⟩⟩)
    | baru i n l j =>
      exact Set.mem_union_right _
        (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨l,
          Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ ⟨_, rfl⟩))))))⟩⟩⟩)
    | Q i n l j =>
      exact Set.mem_union_right _
        (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨l,
          Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ ⟨_, rfl⟩)))))⟩⟩⟩)
    | barQ i n l j =>
      exact Set.mem_union_right _
        (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨l,
          Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ ⟨_, rfl⟩))))⟩⟩⟩)
    | L i n l j =>
      exact Set.mem_union_right _
        (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨l,
          Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ ⟨_, rfl⟩)))⟩⟩⟩)
    | barL i n l j =>
      exact Set.mem_union_right _
        (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨l,
          Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ ⟨_, rfl⟩))⟩⟩⟩)
    | e i n l j =>
      exact Set.mem_union_right _
        (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨l,
          Set.mem_union_left _ (Set.mem_union_right _ ⟨_, rfl⟩)⟩⟩⟩)
    | bare i n l j =>
      exact Set.mem_union_right _
        (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨l,
          Set.mem_union_right _ ⟨_, rfl⟩⟩⟩⟩)

/-- Expanding every dual vector in the dual basis of its value space: the field
  algebra is already generated by the countable family of basis generators. -/
lemma fieldAlgebra_le_adjoin_range :
    h.fieldAlgebra ≤ Algebra.adjoin ℂ (Set.range h.generatorVal) := by
  rw [fieldAlgebra]
  refine Algebra.adjoin_le fun x hx => ?_
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_range] at hx
  obtain ((⟨n, l, μ, ν, φ, rfl⟩ | ⟨n, l, ⟨φ, rfl⟩ | ⟨φ, rfl⟩⟩) | ⟨i, n, l, hx⟩) := hx
  · rw [← GaugeAlgebra.stdBasis.sum_dual_apply_smul_coord φ]
    simp only [map_sum, map_smul]
    refine Subalgebra.sum_mem _ fun j _ => ?_
    rw [← algebraMap_smul ℂ (φ (GaugeAlgebra.stdBasis j))]
    exact Subalgebra.smul_mem _ (Algebra.subset_adjoin
          (Set.mem_range_self (f := h.generatorVal) (Generators.F n l μ ν j))) _
  · rw [← HiggsVec.orthonormBasis.toBasis.sum_dual_apply_smul_coord φ]
    simp only [map_sum, map_smul]
    exact Subalgebra.sum_mem _ fun j _ => Subalgebra.smul_mem _
      (Algebra.subset_adjoin
          (Set.mem_range_self (f := h.generatorVal) (Generators.H n l j))) _
  · rw [← HiggsVec.orthonormBasis.toBasis.conj.sum_dual_apply_smul_coord φ]
    simp only [map_sum, map_smul]
    exact Subalgebra.sum_mem _ fun j _ => Subalgebra.smul_mem _
      (Algebra.subset_adjoin
          (Set.mem_range_self (f := h.generatorVal) (Generators.barH n l j))) _
  · obtain (((((((((⟨φ, rfl⟩ | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) |
      ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) := hx
    · rw [← DownSinglet.basis.sum_dual_apply_smul_coord φ]
      simp only [map_sum, map_smul]
      exact Subalgebra.sum_mem _ fun j _ => Subalgebra.smul_mem _
        (Algebra.subset_adjoin
          (Set.mem_range_self (f := h.generatorVal) (Generators.d i n l j))) _
    · rw [← DownSinglet.basis.conj.sum_dual_apply_smul_coord φ]
      simp only [map_sum, map_smul]
      exact Subalgebra.sum_mem _ fun j _ => Subalgebra.smul_mem _
        (Algebra.subset_adjoin
          (Set.mem_range_self (f := h.generatorVal) (Generators.bard i n l j))) _
    · rw [← UpSinglet.basis.sum_dual_apply_smul_coord φ]
      simp only [map_sum, map_smul]
      exact Subalgebra.sum_mem _ fun j _ => Subalgebra.smul_mem _
        (Algebra.subset_adjoin
          (Set.mem_range_self (f := h.generatorVal) (Generators.u i n l j))) _
    · rw [← UpSinglet.basis.conj.sum_dual_apply_smul_coord φ]
      simp only [map_sum, map_smul]
      exact Subalgebra.sum_mem _ fun j _ => Subalgebra.smul_mem _
        (Algebra.subset_adjoin
          (Set.mem_range_self (f := h.generatorVal) (Generators.baru i n l j))) _
    · rw [← QuarkDoublet.basis.sum_dual_apply_smul_coord φ]
      simp only [map_sum, map_smul]
      exact Subalgebra.sum_mem _ fun j _ => Subalgebra.smul_mem _
        (Algebra.subset_adjoin
          (Set.mem_range_self (f := h.generatorVal) (Generators.Q i n l j))) _
    · rw [← QuarkDoublet.basis.conj.sum_dual_apply_smul_coord φ]
      simp only [map_sum, map_smul]
      exact Subalgebra.sum_mem _ fun j _ => Subalgebra.smul_mem _
        (Algebra.subset_adjoin
          (Set.mem_range_self (f := h.generatorVal) (Generators.barQ i n l j))) _
    · rw [← LeptonDoublet.basis.sum_dual_apply_smul_coord φ]
      simp only [map_sum, map_smul]
      exact Subalgebra.sum_mem _ fun j _ => Subalgebra.smul_mem _
        (Algebra.subset_adjoin
          (Set.mem_range_self (f := h.generatorVal) (Generators.L i n l j))) _
    · rw [← LeptonDoublet.basis.conj.sum_dual_apply_smul_coord φ]
      simp only [map_sum, map_smul]
      exact Subalgebra.sum_mem _ fun j _ => Subalgebra.smul_mem _
        (Algebra.subset_adjoin
          (Set.mem_range_self (f := h.generatorVal) (Generators.barL i n l j))) _
    · rw [← LeptonSinglet.basis.sum_dual_apply_smul_coord φ]
      simp only [map_sum, map_smul]
      exact Subalgebra.sum_mem _ fun j _ => Subalgebra.smul_mem _
        (Algebra.subset_adjoin
          (Set.mem_range_self (f := h.generatorVal) (Generators.e i n l j))) _
    · rw [← LeptonSinglet.basis.conj.sum_dual_apply_smul_coord φ]
      simp only [map_sum, map_smul]
      exact Subalgebra.sum_mem _ fun j _ => Subalgebra.smul_mem _
        (Algebra.subset_adjoin
          (Set.mem_range_self (f := h.generatorVal) (Generators.bare i n l j))) _

/-- The field algebra is generated by the covariant basis generators. -/
lemma fieldAlgebra_eq_adjoin_range :
    h.fieldAlgebra = Algebra.adjoin ℂ (Set.range h.generatorVal) := by
  refine le_antisymm h.fieldAlgebra_le_adjoin_range (Algebra.adjoin_le ?_)
  rintro x ⟨g, rfl⟩
  exact h.generatorVal_mem_fieldAlgebra g

/-- A word in the covariant generators is a `massWeightPoly`-eigenvector whose
  weight is the sum of the weights of its factors. -/
lemma massWeightPoly_generatorVal_list_prod (gl : List Generators) :
    massWeightPoly ((gl.map h.generatorVal).prod) =
      Polynomial.monomial ((gl.map Generators.weight).sum) ((gl.map h.generatorVal).prod) := by
  induction gl with
  | nil => simp
  | cons g t ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, map_mul,
      h.massWeightPoly_generatorVal, ih, Polynomial.monomial_mul_monomial]

/-- The span of the words in the covariant basis generators of total mass weight `w`. -/
def covMonomialSpan (h : IsCovStandardModel B repGauge repLorentz massWeightPoly H barH F
    d bard u baru Q barQ L barL e bare) (w : ℕ) : Submodule ℂ B :=
  Submodule.span ℂ
    {x | ∃ gl : List Generators,
      (gl.map Generators.weight).sum = w ∧ (gl.map h.generatorVal).prod = x}

lemma list_prod_mem_covMonomialSpan {w : ℕ} {gl : List Generators}
    (hw : (gl.map Generators.weight).sum = w) :
    (gl.map h.generatorVal).prod ∈ h.covMonomialSpan w :=
  Submodule.subset_span ⟨gl, hw, rfl⟩

private lemma exists_list_map_eq (l₀ : List B) :
    (∀ y ∈ l₀, y ∈ Set.range h.generatorVal) →
    ∃ gl : List Generators, gl.map h.generatorVal = l₀ := by
  induction l₀ with
  | nil => exact fun _ => ⟨[], rfl⟩
  | cons a t ih =>
    intro hl₀
    obtain ⟨g, hg⟩ := hl₀ a (by simp)
    obtain ⟨gl, hgl⟩ := ih (fun y hy => hl₀ y (by simp [hy]))
    exact ⟨g :: gl, by rw [List.map_cons, hg, hgl]⟩

/-- Reading off the `X ^ w` coefficient of `massWeightPoly` sends the field algebra
  into the weight-`w` monomial span — the projection onto the weight-`w` component,
  with no independence argument needed. -/
lemma coeff_massWeightPoly_mem_covMonomialSpan (w : ℕ) {x : B}
    (hx : x ∈ h.fieldAlgebra) :
    (massWeightPoly x).coeff w ∈ h.covMonomialSpan w := by
  rw [h.fieldAlgebra_eq_adjoin_range, ← Subalgebra.mem_toSubmodule,
    Algebra.adjoin_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l₀, hl₀, rfl⟩ := Submonoid.exists_list_of_mem_closure hy
    obtain ⟨gl, rfl⟩ := h.exists_list_map_eq l₀ hl₀
    rw [h.massWeightPoly_generatorVal_list_prod, Polynomial.coeff_monomial]
    by_cases hw : (gl.map Generators.weight).sum = w
    · rw [if_pos hw]
      exact h.list_prod_mem_covMonomialSpan hw
    · rw [if_neg hw]
      exact Submodule.zero_mem _
  | zero =>
    rw [map_zero, Polynomial.coeff_zero]
    exact Submodule.zero_mem _
  | add a b ha hb iha ihb =>
    rw [map_add, Polynomial.coeff_add]
    exact Submodule.add_mem _ iha ihb
  | smul c a ha iha =>
    rw [map_smul, Polynomial.coeff_smul]
    exact Submodule.smul_mem _ _ iha

/-- **The weight grading of the field algebra.** The submodule of elements of the
  field algebra of mass weight `w` is exactly the span of the words in the covariant
  basis generators of total weight `w`. -/
theorem massWeightSubmodule_eq_covMonomialSpan (w : ℕ) :
    h.massWeightSubmodule w = h.covMonomialSpan w := by
  refine le_antisymm (fun x hx => ?_) ?_
  · have h1 := h.massWeightPoly_of_mem_massWeightSubmodule hx
    have h2 := h.coeff_massWeightPoly_mem_covMonomialSpan w
      (h.mem_fieldAlgebra_of_mem_massWeightSubmodule hx)
    rwa [h1, Polynomial.coeff_monomial, if_pos rfl] at h2
  · rw [covMonomialSpan, Submodule.span_le]
    rintro x ⟨gl, hw, rfl⟩
    rw [massWeightSubmodule]
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · refine Subalgebra.list_prod_mem _ (fun y hy => ?_)
      obtain ⟨g, -, rfl⟩ := List.mem_map.mp hy
      exact h.generatorVal_mem_fieldAlgebra g
    · rw [LinearMap.mem_ker]
      simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply,
        LinearMap.coe_restrictScalars, sub_eq_zero]
      rw [h.massWeightPoly_generatorVal_list_prod, hw]

end  IsCovStandardModel

end StandardModel
