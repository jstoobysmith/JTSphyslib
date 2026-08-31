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

structure IsStandardModel (B : Type) [Ring B] [Algebra ℂ B]
    -- The representations
    (repJet : Representation ℂ JetGaugeGroupI B) (repLorentz : Representation ℂ SL(2,ℂ) B)
    -- The mass weights
    (massWeightPoly : B →ₐ[ℂ] Polynomial B)
    -- The Higgs fields + derivatives
    (H : Multiset (Fin 1 ⊕ Fin 3) →  Module.Dual ℂ HiggsVec →ₗ[ℂ] B)
    (barH : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule HiggsVec) →ₗ[ℂ] B)
    -- The gauge fields + derivatives
    (A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B)
    -- Three families of down-type quarks + derivatives + conjugates
    (d : Fin 3 → Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ DownSinglet →ₗ[ℂ] B)
    (bard : Fin 3 → Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule DownSinglet) →ₗ[ℂ] B)
    -- Three families of up-type quarks + derivatives + conjugates
    (u : Fin 3 → Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ UpSinglet →ₗ[ℂ] B)
    (baru : Fin 3 → Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule UpSinglet) →ₗ[ℂ] B)
    -- Three families of quark doublets + derivatives + conjugates
    (Q : Fin 3 → Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ QuarkDoublet →ₗ[ℂ] B)
    (barQ : Fin 3 → Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule QuarkDoublet) →ₗ[ℂ] B)
    -- Three families of lepton doublets + derivatives + conjugates
    (L : Fin 3 → Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonDoublet →ₗ[ℂ] B)
    (barL : Fin 3 → Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule LeptonDoublet) →ₗ[ℂ] B)
    -- Three families of lepton singlets + derivatives + conjugates
    (e : Fin 3 → Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonSinglet →ₗ[ℂ] B)
    (bare : Fin 3 → Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule LeptonSinglet) →ₗ[ℂ] B)
    : Prop where
  -- *Gauge transformation*
  -- The gauge field transforms as a gauge field: Lorentz covector symbols, the
  -- all-orders adjoint Leibniz convolution with the Maurer–Cartan shift, and a
  -- multiplicative gauge action
  repJet_A : IsGaugeField repLorentz repJet A
  -- The Higgs field and its conjugate transform in the Higgs representation
  repJet_H : TransformsIn repJet HiggsVec.repJetGaugeGroupI H
  repJet_barH : TransformsIn repJet (repConj HiggsVec.repJetGaugeGroupI) barH
  -- The down-type quarks and their conjugates transform in the down-singlet
  -- representation
  repJet_d : ∀ i, TransformsIn repJet DownSinglet.repJetGaugeGroupI (d i)
  repJet_bard : ∀ i, TransformsIn repJet (repConj DownSinglet.repJetGaugeGroupI) (bard i)
  -- The up-type quarks and their conjugates transform in the up-singlet representation
  repJet_u : ∀ i, TransformsIn repJet UpSinglet.repJetGaugeGroupI (u i)
  repJet_baru : ∀ i, TransformsIn repJet (repConj UpSinglet.repJetGaugeGroupI) (baru i)
  -- The quark doublets and their conjugates transform in the quark-doublet
  -- representation
  repJet_Q : ∀ i, TransformsIn repJet QuarkDoublet.repJetGaugeGroupI (Q i)
  repJet_barQ : ∀ i, TransformsIn repJet (repConj QuarkDoublet.repJetGaugeGroupI) (barQ i)
  -- The lepton doublets and their conjugates transform in the lepton-doublet
  -- representation
  repJet_L : ∀ i, TransformsIn repJet LeptonDoublet.repJetGaugeGroupI (L i)
  repJet_barL : ∀ i, TransformsIn repJet (repConj LeptonDoublet.repJetGaugeGroupI) (barL i)
  -- The lepton singlets and their conjugates transform in the lepton-singlet
  -- representation
  repJet_e : ∀ i, TransformsIn repJet LeptonSinglet.repJetGaugeGroupI (e i)
  repJet_bare : ∀ i, TransformsIn repJet (repConj LeptonSinglet.repJetGaugeGroupI) (bare i)
  -- *The Lorentz transformation*
  -- The Lorentz transformations: the derivative slots of every field mix by per-slot
  -- Lorentz matrices, the value index by the contragredient of the species' Lorentz
  -- representation — the Higgs is a scalar, the fermions are Weyl spinors, and the
  -- barred fields carry the conjugate representations
  repLorentz_H : IsLorentzDerivTransforms repLorentz
    (Representation.trivial ℂ SL(2,ℂ) HiggsVec) H
  repLorentz_barH : IsLorentzDerivTransforms repLorentz
    (Representation.trivial ℂ SL(2,ℂ) HiggsVec).conj barH
  repLorentz_d : ∀ i, IsLorentzDerivTransforms repLorentz
    DownSinglet.repLorentzGroup (d i)
  repLorentz_bard : ∀ i, IsLorentzDerivTransforms repLorentz
    DownSinglet.repLorentzGroup.conj (bard i)
  repLorentz_u : ∀ i, IsLorentzDerivTransforms repLorentz
    UpSinglet.repLorentzGroup (u i)
  repLorentz_baru : ∀ i, IsLorentzDerivTransforms repLorentz
    UpSinglet.repLorentzGroup.conj (baru i)
  repLorentz_Q : ∀ i, IsLorentzDerivTransforms repLorentz
    QuarkDoublet.repLorentzGroup (Q i)
  repLorentz_barQ : ∀ i, IsLorentzDerivTransforms repLorentz
    QuarkDoublet.repLorentzGroup.conj (barQ i)
  repLorentz_L : ∀ i, IsLorentzDerivTransforms repLorentz
    LeptonDoublet.repLorentzGroup (L i)
  repLorentz_barL : ∀ i, IsLorentzDerivTransforms repLorentz
    LeptonDoublet.repLorentzGroup.conj (barL i)
  repLorentz_e : ∀ i, IsLorentzDerivTransforms repLorentz
    LeptonSinglet.repLorentzGroup (e i)
  repLorentz_bare : ∀ i, IsLorentzDerivTransforms repLorentz
    LeptonSinglet.repLorentzGroup.conj (bare i)
  -- **Mass weights (= 2 * mass dimension)**
  -- Every derivative symbol is a `massWeightPoly`-eigenvector of pure monomial weight:
  -- the bosons have mass dimension `1 + |s|` (weight `2 * (1 + |s|)`), the fermions
  -- mass dimension `3/2 + |s|` (weight `3 + 2 * |s|`)
  massWeight_H : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) φ,
    massWeightPoly (H s φ) = Polynomial.monomial (2 * (1 + Multiset.card s)) (H s φ)
  massWeight_barH : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) φ,
    massWeightPoly (barH s φ) = Polynomial.monomial (2 * (1 + Multiset.card s)) (barH s φ)
  massWeight_A : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) μ φ,
    massWeightPoly (A s μ φ) = Polynomial.monomial (2 * (1 + Multiset.card s)) (A s μ φ)
  massWeight_d : ∀ i (s : Multiset (Fin 1 ⊕ Fin 3)) φ,
    massWeightPoly (d i s φ) = Polynomial.monomial (3 + 2 * Multiset.card s) (d i s φ)
  massWeight_bard : ∀ i (s : Multiset (Fin 1 ⊕ Fin 3)) φ,
    massWeightPoly (bard i s φ) = Polynomial.monomial (3 + 2 * Multiset.card s) (bard i s φ)
  massWeight_u : ∀ i (s : Multiset (Fin 1 ⊕ Fin 3)) φ,
    massWeightPoly (u i s φ) = Polynomial.monomial (3 + 2 * Multiset.card s) (u i s φ)
  massWeight_baru : ∀ i (s : Multiset (Fin 1 ⊕ Fin 3)) φ,
    massWeightPoly (baru i s φ) = Polynomial.monomial (3 + 2 * Multiset.card s) (baru i s φ)
  massWeight_Q : ∀ i (s : Multiset (Fin 1 ⊕ Fin 3)) φ,
    massWeightPoly (Q i s φ) = Polynomial.monomial (3 + 2 * Multiset.card s) (Q i s φ)
  massWeight_barQ : ∀ i (s : Multiset (Fin 1 ⊕ Fin 3)) φ,
    massWeightPoly (barQ i s φ) = Polynomial.monomial (3 + 2 * Multiset.card s) (barQ i s φ)
  massWeight_L : ∀ i (s : Multiset (Fin 1 ⊕ Fin 3)) φ,
    massWeightPoly (L i s φ) = Polynomial.monomial (3 + 2 * Multiset.card s) (L i s φ)
  massWeight_barL : ∀ i (s : Multiset (Fin 1 ⊕ Fin 3)) φ,
    massWeightPoly (barL i s φ) = Polynomial.monomial (3 + 2 * Multiset.card s) (barL i s φ)
  massWeight_e : ∀ i (s : Multiset (Fin 1 ⊕ Fin 3)) φ,
    massWeightPoly (e i s φ) = Polynomial.monomial (3 + 2 * Multiset.card s) (e i s φ)
  massWeight_bare : ∀ i (s : Multiset (Fin 1 ⊕ Fin 3)) φ,
    massWeightPoly (bare i s φ) = Polynomial.monomial (3 + 2 * Multiset.card s) (bare i s φ)
  -- **Commutation**: the gauge field is bosonic — its derivative symbols commute with
  -- each other and with every matter symbol (the matter symbols themselves are free to
  -- anticommute among each other)
  A_comm_A : ∀ (s s' : Multiset (Fin 1 ⊕ Fin 3)) (μ μ' : Fin 1 ⊕ Fin 3)
    (ψ ψ' : Module.Dual ℝ GaugeAlgebra), Commute (A s μ ψ) (A s' μ' ψ')
  A_comm_H : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ HiggsVec),
    Commute (A s μ ψ) (H s' φ)
  A_comm_barH : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule HiggsVec)),
    Commute (A s μ ψ) (barH s' φ)
  A_comm_d : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ DownSinglet),
    Commute (A s μ ψ) (d i s' φ)
  A_comm_bard : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule DownSinglet)),
    Commute (A s μ ψ) (bard i s' φ)
  A_comm_u : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ UpSinglet),
    Commute (A s μ ψ) (u i s' φ)
  A_comm_baru : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule UpSinglet)),
    Commute (A s μ ψ) (baru i s' φ)
  A_comm_Q : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ QuarkDoublet),
    Commute (A s μ ψ) (Q i s' φ)
  A_comm_barQ : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule QuarkDoublet)),
    Commute (A s μ ψ) (barQ i s' φ)
  A_comm_L : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ LeptonDoublet),
    Commute (A s μ ψ) (L i s' φ)
  A_comm_barL : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule LeptonDoublet)),
    Commute (A s μ ψ) (barL i s' φ)
  A_comm_e : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ LeptonSinglet),
    Commute (A s μ ψ) (e i s' φ)
  A_comm_bare : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
    (ψ : Module.Dual ℝ GaugeAlgebra) (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule LeptonSinglet)),
    Commute (A s μ ψ) (bare i s' φ)
  -- *Multiplicativity of the Lorentz action*
  -- A `Representation` records only a linear action, so being an algebra map is a
  -- separate demand; it is what carries the Lorentz action through products of
  -- symbols, as the covariant derivative of a matter field needs
  /-- Lorentz transformations act on `B` by algebra maps: the action preserves products, so each
    `repLorentz Λ` is an algebra endomorphism of `B`. -/
  repLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂
  -- **Statistics of the matter symbols**
  -- The gauge field is bosonic above; here the matter symbols are typed. The Higgs
  -- symbols commute with each other and with every fermion symbol, and the fermion
  -- symbols anticommute among themselves. Together with the `A_comm_*` rules these
  -- fix the statistics of every symbol of the theory
  /-- The Higgs is bosonic: two Higgs symbols commute. -/
  H_comm_H : ∀ (s s' : Multiset (Fin 1 ⊕ Fin 3)) (φ φ' : Module.Dual ℂ HiggsVec),
    Commute (H s φ) (H s' φ')
  /-- A Higgs symbol commutes with a conjugate Higgs symbol. -/
  H_comm_barH : ∀ (s s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ HiggsVec)
      (φ' : Module.Dual ℂ (ConjModule HiggsVec)),
    Commute (H s φ) (barH s' φ')
  /-- Two conjugate Higgs symbols commute. -/
  barH_comm_barH : ∀ (s s' : Multiset (Fin 1 ⊕ Fin 3)) (φ φ' : Module.Dual ℂ (ConjModule HiggsVec)),
    Commute (barH s φ) (barH s' φ')
  /-- The Higgs symbols commute with the down-type quark symbols: the Higgs is a boson, so it
    carries no statistics against the fermions. -/
  H_comm_d : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ HiggsVec) (i : Fin 3)
      (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ DownSinglet),
    Commute (H s φ) (d i s' φ')
  /-- The Higgs symbols commute with the conjugate down-type quark symbols: the Higgs is a boson, so
    it carries no statistics against the fermions. -/
  H_comm_bard : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ HiggsVec) (i : Fin 3)
      (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ (ConjModule DownSinglet)),
    Commute (H s φ) (bard i s' φ')
  /-- The Higgs symbols commute with the up-type quark symbols: the Higgs is a boson, so it carries
    no statistics against the fermions. -/
  H_comm_u : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ HiggsVec) (i : Fin 3)
      (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ UpSinglet),
    Commute (H s φ) (u i s' φ')
  /-- The Higgs symbols commute with the conjugate up-type quark symbols: the Higgs is a boson, so
    it carries no statistics against the fermions. -/
  H_comm_baru : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ HiggsVec) (i : Fin 3)
      (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ (ConjModule UpSinglet)),
    Commute (H s φ) (baru i s' φ')
  /-- The Higgs symbols commute with the quark doublet symbols: the Higgs is a boson, so it carries
    no statistics against the fermions. -/
  H_comm_Q : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ HiggsVec) (i : Fin 3)
      (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ QuarkDoublet),
    Commute (H s φ) (Q i s' φ')
  /-- The Higgs symbols commute with the conjugate quark doublet symbols: the Higgs is a boson, so
    it carries no statistics against the fermions. -/
  H_comm_barQ : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ HiggsVec) (i : Fin 3)
      (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)),
    Commute (H s φ) (barQ i s' φ')
  /-- The Higgs symbols commute with the lepton doublet symbols: the Higgs is a boson, so it carries
    no statistics against the fermions. -/
  H_comm_L : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ HiggsVec) (i : Fin 3)
      (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ LeptonDoublet),
    Commute (H s φ) (L i s' φ')
  /-- The Higgs symbols commute with the conjugate lepton doublet symbols: the Higgs is a boson, so
    it carries no statistics against the fermions. -/
  H_comm_barL : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ HiggsVec) (i : Fin 3)
      (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    Commute (H s φ) (barL i s' φ')
  /-- The Higgs symbols commute with the lepton singlet symbols: the Higgs is a boson, so it carries
    no statistics against the fermions. -/
  H_comm_e : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ HiggsVec) (i : Fin 3)
      (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ LeptonSinglet),
    Commute (H s φ) (e i s' φ')
  /-- The Higgs symbols commute with the conjugate lepton singlet symbols: the Higgs is a boson, so
    it carries no statistics against the fermions. -/
  H_comm_bare : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ HiggsVec) (i : Fin 3)
      (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    Commute (H s φ) (bare i s' φ')
  /-- The conjugate Higgs symbols commute with the down-type quark symbols: the Higgs is a boson, so
    it carries no statistics against the fermions. -/
  barH_comm_d : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule HiggsVec))
      (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ DownSinglet),
    Commute (barH s φ) (d i s' φ')
  /-- The conjugate Higgs symbols commute with the conjugate down-type quark symbols: the Higgs is a
    boson, so it carries no statistics against the fermions. -/
  barH_comm_bard : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule HiggsVec))
      (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ (ConjModule DownSinglet)),
    Commute (barH s φ) (bard i s' φ')
  /-- The conjugate Higgs symbols commute with the up-type quark symbols: the Higgs is a boson, so
    it carries no statistics against the fermions. -/
  barH_comm_u : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule HiggsVec))
      (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ UpSinglet),
    Commute (barH s φ) (u i s' φ')
  /-- The conjugate Higgs symbols commute with the conjugate up-type quark symbols: the Higgs is a
    boson, so it carries no statistics against the fermions. -/
  barH_comm_baru : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule HiggsVec))
      (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ (ConjModule UpSinglet)),
    Commute (barH s φ) (baru i s' φ')
  /-- The conjugate Higgs symbols commute with the quark doublet symbols: the Higgs is a boson, so
    it carries no statistics against the fermions. -/
  barH_comm_Q : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule HiggsVec))
      (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ QuarkDoublet),
    Commute (barH s φ) (Q i s' φ')
  /-- The conjugate Higgs symbols commute with the conjugate quark doublet symbols: the Higgs is a
    boson, so it carries no statistics against the fermions. -/
  barH_comm_barQ : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule HiggsVec))
      (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)),
    Commute (barH s φ) (barQ i s' φ')
  /-- The conjugate Higgs symbols commute with the lepton doublet symbols: the Higgs is a boson, so
    it carries no statistics against the fermions. -/
  barH_comm_L : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule HiggsVec))
      (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ LeptonDoublet),
    Commute (barH s φ) (L i s' φ')
  /-- The conjugate Higgs symbols commute with the conjugate lepton doublet symbols: the Higgs is a
    boson, so it carries no statistics against the fermions. -/
  barH_comm_barL : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule HiggsVec))
      (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    Commute (barH s φ) (barL i s' φ')
  /-- The conjugate Higgs symbols commute with the lepton singlet symbols: the Higgs is a boson, so
    it carries no statistics against the fermions. -/
  barH_comm_e : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule HiggsVec))
      (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ LeptonSinglet),
    Commute (barH s φ) (e i s' φ')
  /-- The conjugate Higgs symbols commute with the conjugate lepton singlet symbols: the Higgs is a
    boson, so it carries no statistics against the fermions. -/
  barH_comm_bare : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule HiggsVec))
      (i : Fin 3) (s' : Multiset (Fin 1 ⊕ Fin 3)) (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    Commute (barH s φ) (bare i s' φ')
  /-- The down-type quark symbols anticommute among themselves. -/
  d_anticomm_d : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ φ' : Module.Dual ℂ DownSinglet),
    d i s φ * d j s' φ' = -(d j s' φ' * d i s φ)
  /-- The down-type quark symbols anticommute with the conjugate down-type quark symbols. -/
  d_anticomm_bard : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ DownSinglet) (φ' : Module.Dual ℂ (ConjModule DownSinglet)),
    d i s φ * bard j s' φ' = -(bard j s' φ' * d i s φ)
  /-- The down-type quark symbols anticommute with the up-type quark symbols. -/
  d_anticomm_u : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ DownSinglet)
      (φ' : Module.Dual ℂ UpSinglet),
    d i s φ * u j s' φ' = -(u j s' φ' * d i s φ)
  /-- The down-type quark symbols anticommute with the conjugate up-type quark symbols. -/
  d_anticomm_baru : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ DownSinglet) (φ' : Module.Dual ℂ (ConjModule UpSinglet)),
    d i s φ * baru j s' φ' = -(baru j s' φ' * d i s φ)
  /-- The down-type quark symbols anticommute with the quark doublet symbols. -/
  d_anticomm_Q : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ DownSinglet)
      (φ' : Module.Dual ℂ QuarkDoublet),
    d i s φ * Q j s' φ' = -(Q j s' φ' * d i s φ)
  /-- The down-type quark symbols anticommute with the conjugate quark doublet symbols. -/
  d_anticomm_barQ : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ DownSinglet) (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)),
    d i s φ * barQ j s' φ' = -(barQ j s' φ' * d i s φ)
  /-- The down-type quark symbols anticommute with the lepton doublet symbols. -/
  d_anticomm_L : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ DownSinglet)
      (φ' : Module.Dual ℂ LeptonDoublet),
    d i s φ * L j s' φ' = -(L j s' φ' * d i s φ)
  /-- The down-type quark symbols anticommute with the conjugate lepton doublet symbols. -/
  d_anticomm_barL : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ DownSinglet) (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    d i s φ * barL j s' φ' = -(barL j s' φ' * d i s φ)
  /-- The down-type quark symbols anticommute with the lepton singlet symbols. -/
  d_anticomm_e : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ DownSinglet)
      (φ' : Module.Dual ℂ LeptonSinglet),
    d i s φ * e j s' φ' = -(e j s' φ' * d i s φ)
  /-- The down-type quark symbols anticommute with the conjugate lepton singlet symbols. -/
  d_anticomm_bare : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ DownSinglet) (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    d i s φ * bare j s' φ' = -(bare j s' φ' * d i s φ)
  /-- The conjugate down-type quark symbols anticommute among themselves. -/
  bard_anticomm_bard : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ φ' : Module.Dual ℂ (ConjModule DownSinglet)),
    bard i s φ * bard j s' φ' = -(bard j s' φ' * bard i s φ)
  /-- The conjugate down-type quark symbols anticommute with the up-type quark symbols. -/
  bard_anticomm_u : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule DownSinglet)) (φ' : Module.Dual ℂ UpSinglet),
    bard i s φ * u j s' φ' = -(u j s' φ' * bard i s φ)
  /-- The conjugate down-type quark symbols anticommute with the conjugate up-type quark symbols. -/
  bard_anticomm_baru : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule DownSinglet)) (φ' : Module.Dual ℂ (ConjModule UpSinglet)),
    bard i s φ * baru j s' φ' = -(baru j s' φ' * bard i s φ)
  /-- The conjugate down-type quark symbols anticommute with the quark doublet symbols. -/
  bard_anticomm_Q : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule DownSinglet)) (φ' : Module.Dual ℂ QuarkDoublet),
    bard i s φ * Q j s' φ' = -(Q j s' φ' * bard i s φ)
  /-- The conjugate down-type quark symbols anticommute with the conjugate quark doublet symbols. -/
  bard_anticomm_barQ : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule DownSinglet)) (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)),
    bard i s φ * barQ j s' φ' = -(barQ j s' φ' * bard i s φ)
  /-- The conjugate down-type quark symbols anticommute with the lepton doublet symbols. -/
  bard_anticomm_L : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule DownSinglet)) (φ' : Module.Dual ℂ LeptonDoublet),
    bard i s φ * L j s' φ' = -(L j s' φ' * bard i s φ)
  /-- The conjugate down-type quark symbols anticommute with the conjugate lepton doublet symbols.
    -/
  bard_anticomm_barL : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule DownSinglet)) (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    bard i s φ * barL j s' φ' = -(barL j s' φ' * bard i s φ)
  /-- The conjugate down-type quark symbols anticommute with the lepton singlet symbols. -/
  bard_anticomm_e : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule DownSinglet)) (φ' : Module.Dual ℂ LeptonSinglet),
    bard i s φ * e j s' φ' = -(e j s' φ' * bard i s φ)
  /-- The conjugate down-type quark symbols anticommute with the conjugate lepton singlet symbols.
    -/
  bard_anticomm_bare : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule DownSinglet)) (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    bard i s φ * bare j s' φ' = -(bare j s' φ' * bard i s φ)
  /-- The up-type quark symbols anticommute among themselves. -/
  u_anticomm_u : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3)) (φ φ' : Module.Dual ℂ UpSinglet),
    u i s φ * u j s' φ' = -(u j s' φ' * u i s φ)
  /-- The up-type quark symbols anticommute with the conjugate up-type quark symbols. -/
  u_anticomm_baru : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ UpSinglet)
      (φ' : Module.Dual ℂ (ConjModule UpSinglet)),
    u i s φ * baru j s' φ' = -(baru j s' φ' * u i s φ)
  /-- The up-type quark symbols anticommute with the quark doublet symbols. -/
  u_anticomm_Q : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ UpSinglet)
      (φ' : Module.Dual ℂ QuarkDoublet),
    u i s φ * Q j s' φ' = -(Q j s' φ' * u i s φ)
  /-- The up-type quark symbols anticommute with the conjugate quark doublet symbols. -/
  u_anticomm_barQ : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ UpSinglet)
      (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)),
    u i s φ * barQ j s' φ' = -(barQ j s' φ' * u i s φ)
  /-- The up-type quark symbols anticommute with the lepton doublet symbols. -/
  u_anticomm_L : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ UpSinglet)
      (φ' : Module.Dual ℂ LeptonDoublet),
    u i s φ * L j s' φ' = -(L j s' φ' * u i s φ)
  /-- The up-type quark symbols anticommute with the conjugate lepton doublet symbols. -/
  u_anticomm_barL : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ UpSinglet)
      (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    u i s φ * barL j s' φ' = -(barL j s' φ' * u i s φ)
  /-- The up-type quark symbols anticommute with the lepton singlet symbols. -/
  u_anticomm_e : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ UpSinglet)
      (φ' : Module.Dual ℂ LeptonSinglet),
    u i s φ * e j s' φ' = -(e j s' φ' * u i s φ)
  /-- The up-type quark symbols anticommute with the conjugate lepton singlet symbols. -/
  u_anticomm_bare : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ UpSinglet)
      (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    u i s φ * bare j s' φ' = -(bare j s' φ' * u i s φ)
  /-- The conjugate up-type quark symbols anticommute among themselves. -/
  baru_anticomm_baru : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ φ' : Module.Dual ℂ (ConjModule UpSinglet)),
    baru i s φ * baru j s' φ' = -(baru j s' φ' * baru i s φ)
  /-- The conjugate up-type quark symbols anticommute with the quark doublet symbols. -/
  baru_anticomm_Q : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule UpSinglet)) (φ' : Module.Dual ℂ QuarkDoublet),
    baru i s φ * Q j s' φ' = -(Q j s' φ' * baru i s φ)
  /-- The conjugate up-type quark symbols anticommute with the conjugate quark doublet symbols. -/
  baru_anticomm_barQ : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule UpSinglet)) (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)),
    baru i s φ * barQ j s' φ' = -(barQ j s' φ' * baru i s φ)
  /-- The conjugate up-type quark symbols anticommute with the lepton doublet symbols. -/
  baru_anticomm_L : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule UpSinglet)) (φ' : Module.Dual ℂ LeptonDoublet),
    baru i s φ * L j s' φ' = -(L j s' φ' * baru i s φ)
  /-- The conjugate up-type quark symbols anticommute with the conjugate lepton doublet symbols. -/
  baru_anticomm_barL : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule UpSinglet)) (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    baru i s φ * barL j s' φ' = -(barL j s' φ' * baru i s φ)
  /-- The conjugate up-type quark symbols anticommute with the lepton singlet symbols. -/
  baru_anticomm_e : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule UpSinglet)) (φ' : Module.Dual ℂ LeptonSinglet),
    baru i s φ * e j s' φ' = -(e j s' φ' * baru i s φ)
  /-- The conjugate up-type quark symbols anticommute with the conjugate lepton singlet symbols. -/
  baru_anticomm_bare : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule UpSinglet)) (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    baru i s φ * bare j s' φ' = -(bare j s' φ' * baru i s φ)
  /-- The quark doublet symbols anticommute among themselves. -/
  Q_anticomm_Q : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ φ' : Module.Dual ℂ QuarkDoublet),
    Q i s φ * Q j s' φ' = -(Q j s' φ' * Q i s φ)
  /-- The quark doublet symbols anticommute with the conjugate quark doublet symbols. -/
  Q_anticomm_barQ : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ QuarkDoublet) (φ' : Module.Dual ℂ (ConjModule QuarkDoublet)),
    Q i s φ * barQ j s' φ' = -(barQ j s' φ' * Q i s φ)
  /-- The quark doublet symbols anticommute with the lepton doublet symbols. -/
  Q_anticomm_L : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ QuarkDoublet)
      (φ' : Module.Dual ℂ LeptonDoublet),
    Q i s φ * L j s' φ' = -(L j s' φ' * Q i s φ)
  /-- The quark doublet symbols anticommute with the conjugate lepton doublet symbols. -/
  Q_anticomm_barL : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ QuarkDoublet) (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    Q i s φ * barL j s' φ' = -(barL j s' φ' * Q i s φ)
  /-- The quark doublet symbols anticommute with the lepton singlet symbols. -/
  Q_anticomm_e : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ QuarkDoublet)
      (φ' : Module.Dual ℂ LeptonSinglet),
    Q i s φ * e j s' φ' = -(e j s' φ' * Q i s φ)
  /-- The quark doublet symbols anticommute with the conjugate lepton singlet symbols. -/
  Q_anticomm_bare : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ QuarkDoublet) (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    Q i s φ * bare j s' φ' = -(bare j s' φ' * Q i s φ)
  /-- The conjugate quark doublet symbols anticommute among themselves. -/
  barQ_anticomm_barQ : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ φ' : Module.Dual ℂ (ConjModule QuarkDoublet)),
    barQ i s φ * barQ j s' φ' = -(barQ j s' φ' * barQ i s φ)
  /-- The conjugate quark doublet symbols anticommute with the lepton doublet symbols. -/
  barQ_anticomm_L : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule QuarkDoublet)) (φ' : Module.Dual ℂ LeptonDoublet),
    barQ i s φ * L j s' φ' = -(L j s' φ' * barQ i s φ)
  /-- The conjugate quark doublet symbols anticommute with the conjugate lepton doublet symbols. -/
  barQ_anticomm_barL : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule QuarkDoublet)) (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    barQ i s φ * barL j s' φ' = -(barL j s' φ' * barQ i s φ)
  /-- The conjugate quark doublet symbols anticommute with the lepton singlet symbols. -/
  barQ_anticomm_e : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule QuarkDoublet)) (φ' : Module.Dual ℂ LeptonSinglet),
    barQ i s φ * e j s' φ' = -(e j s' φ' * barQ i s φ)
  /-- The conjugate quark doublet symbols anticommute with the conjugate lepton singlet symbols. -/
  barQ_anticomm_bare : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule QuarkDoublet)) (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    barQ i s φ * bare j s' φ' = -(bare j s' φ' * barQ i s φ)
  /-- The lepton doublet symbols anticommute among themselves. -/
  L_anticomm_L : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ φ' : Module.Dual ℂ LeptonDoublet),
    L i s φ * L j s' φ' = -(L j s' φ' * L i s φ)
  /-- The lepton doublet symbols anticommute with the conjugate lepton doublet symbols. -/
  L_anticomm_barL : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ LeptonDoublet) (φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    L i s φ * barL j s' φ' = -(barL j s' φ' * L i s φ)
  /-- The lepton doublet symbols anticommute with the lepton singlet symbols. -/
  L_anticomm_e : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ LeptonDoublet)
      (φ' : Module.Dual ℂ LeptonSinglet),
    L i s φ * e j s' φ' = -(e j s' φ' * L i s φ)
  /-- The lepton doublet symbols anticommute with the conjugate lepton singlet symbols. -/
  L_anticomm_bare : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ LeptonDoublet) (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    L i s φ * bare j s' φ' = -(bare j s' φ' * L i s φ)
  /-- The conjugate lepton doublet symbols anticommute among themselves. -/
  barL_anticomm_barL : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ φ' : Module.Dual ℂ (ConjModule LeptonDoublet)),
    barL i s φ * barL j s' φ' = -(barL j s' φ' * barL i s φ)
  /-- The conjugate lepton doublet symbols anticommute with the lepton singlet symbols. -/
  barL_anticomm_e : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule LeptonDoublet)) (φ' : Module.Dual ℂ LeptonSinglet),
    barL i s φ * e j s' φ' = -(e j s' φ' * barL i s φ)
  /-- The conjugate lepton doublet symbols anticommute with the conjugate lepton singlet symbols. -/
  barL_anticomm_bare : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule LeptonDoublet)) (φ' : Module.Dual ℂ (ConjModule LeptonSinglet))
      ,
    barL i s φ * bare j s' φ' = -(bare j s' φ' * barL i s φ)
  /-- The lepton singlet symbols anticommute among themselves. -/
  e_anticomm_e : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ φ' : Module.Dual ℂ LeptonSinglet),
    e i s φ * e j s' φ' = -(e j s' φ' * e i s φ)
  /-- The lepton singlet symbols anticommute with the conjugate lepton singlet symbols. -/
  e_anticomm_bare : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ LeptonSinglet) (φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    e i s φ * bare j s' φ' = -(bare j s' φ' * e i s φ)
  /-- The conjugate lepton singlet symbols anticommute among themselves. -/
  bare_anticomm_bare : ∀ (i j : Fin 3) (s s' : Multiset (Fin 1 ⊕ Fin 3))
      (φ φ' : Module.Dual ℂ (ConjModule LeptonSinglet)),
    bare i s φ * bare j s' φ' = -(bare j s' φ' * bare i s φ)

set_option linter.unusedVariables false
namespace IsStandardModel

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repJet : Representation ℂ JetGaugeGroupI B}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  {H : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ HiggsVec →ₗ[ℂ] B}
  {barH : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule HiggsVec) →ₗ[ℂ] B}
  {A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B}
  {d : Fin 3 → Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ DownSinglet →ₗ[ℂ] B}
  {bard : Fin 3 → Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule DownSinglet) →ₗ[ℂ] B}
  {u : Fin 3 → Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ UpSinglet →ₗ[ℂ] B}
  {baru : Fin 3 → Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule UpSinglet) →ₗ[ℂ] B}
  {Q : Fin 3 → Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ QuarkDoublet →ₗ[ℂ] B}
  {barQ : Fin 3 → Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule QuarkDoublet) →ₗ[ℂ] B}
  {L : Fin 3 → Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonDoublet →ₗ[ℂ] B}
  {barL : Fin 3 → Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule LeptonDoublet) →ₗ[ℂ] B}
  {e : Fin 3 → Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonSinglet →ₗ[ℂ] B}
  {bare : Fin 3 → Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule LeptonSinglet) →ₗ[ℂ] B}
  (h : IsStandardModel B repJet repLorentz massWeightPoly H barH A
    d bard u baru Q barQ L barL e bare)


/-!

## A. The field algebra

-/

/-- The algebra generated by all the fields of the Standard Model and their derivative
  symbols: the gauge field, the Higgs and its conjugate, and the three families of each
  fermion species with their conjugates. -/
def fieldAlgebra (h : IsStandardModel B repJet repLorentz massWeightPoly H barH A
    d bard u baru Q barQ L barL e bare): Subalgebra ℂ B :=
  Algebra.adjoin ℂ
    ((⋃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3), Set.range (A s μ)) ∪
      (⋃ (s : Multiset (Fin 1 ⊕ Fin 3)), Set.range (H s) ∪ Set.range (barH s)) ∪
      (⋃ (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)),
        Set.range (d i s) ∪ Set.range (bard i s) ∪
        Set.range (u i s) ∪ Set.range (baru i s) ∪
        Set.range (Q i s) ∪ Set.range (barQ i s) ∪
        Set.range (L i s) ∪ Set.range (barL i s) ∪
        Set.range (e i s) ∪ Set.range (bare i s)))

/-!

## B. Covariant derivatives

-/

include h in
noncomputable def covDerivD (h : IsStandardModel B repJet repLorentz massWeightPoly H barH A
    d bard u baru Q barQ L barL e bare) (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ DownSinglet →ₗ[ℂ] B :=
  IsGaugeField.covDerivIter A DownSinglet.gaugeAlgebraAction (d i) n l 0

noncomputable def covDerivBarD (h : IsStandardModel B repJet repLorentz massWeightPoly H barH A
    d bard u baru Q barQ L barL e bare) (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule DownSinglet) →ₗ[ℂ] B :=
  IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj DownSinglet.gaugeAlgebraAction)
  (bard i) n l 0

/-- The iterated covariant derivative of the Higgs field. -/
noncomputable def covDerivH (h : IsStandardModel B repJet repLorentz massWeightPoly H barH A
    d bard u baru Q barQ L barL e bare) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ HiggsVec →ₗ[ℂ] B :=
  IsGaugeField.covDerivIter A HiggsVec.gaugeAlgebraAction H n l 0

/-- The iterated covariant derivative of the conjugate Higgs field. -/
noncomputable def covDerivBarH (h : IsStandardModel B repJet repLorentz massWeightPoly H barH A
    d bard u baru Q barQ L barL e bare) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule HiggsVec) →ₗ[ℂ] B :=
  IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj HiggsVec.gaugeAlgebraAction)
  barH n l 0

/-- The iterated covariant derivative of the up-type quarks. -/
noncomputable def covDerivU (h : IsStandardModel B repJet repLorentz massWeightPoly H barH A
    d bard u baru Q barQ L barL e bare) (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ UpSinglet →ₗ[ℂ] B :=
  IsGaugeField.covDerivIter A UpSinglet.gaugeAlgebraAction (u i) n l 0

/-- The iterated covariant derivative of the conjugate up-type quarks. -/
noncomputable def covDerivBarU (h : IsStandardModel B repJet repLorentz massWeightPoly H barH A
    d bard u baru Q barQ L barL e bare) (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule UpSinglet) →ₗ[ℂ] B :=
  IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj UpSinglet.gaugeAlgebraAction)
  (baru i) n l 0

/-- The iterated covariant derivative of the quark doublets. -/
noncomputable def covDerivQ (h : IsStandardModel B repJet repLorentz massWeightPoly H barH A
    d bard u baru Q barQ L barL e bare) (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ QuarkDoublet →ₗ[ℂ] B :=
  IsGaugeField.covDerivIter A QuarkDoublet.gaugeAlgebraAction (Q i) n l 0

/-- The iterated covariant derivative of the conjugate quark doublets. -/
noncomputable def covDerivBarQ (h : IsStandardModel B repJet repLorentz massWeightPoly H barH A
    d bard u baru Q barQ L barL e bare) (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule QuarkDoublet) →ₗ[ℂ] B :=
  IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj QuarkDoublet.gaugeAlgebraAction)
  (barQ i) n l 0

/-- The iterated covariant derivative of the lepton doublets. -/
noncomputable def covDerivL (h : IsStandardModel B repJet repLorentz massWeightPoly H barH A
    d bard u baru Q barQ L barL e bare) (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ LeptonDoublet →ₗ[ℂ] B :=
  IsGaugeField.covDerivIter A LeptonDoublet.gaugeAlgebraAction (L i) n l 0

/-- The iterated covariant derivative of the conjugate lepton doublets. -/
noncomputable def covDerivBarL (h : IsStandardModel B repJet repLorentz massWeightPoly H barH A
    d bard u baru Q barQ L barL e bare) (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule LeptonDoublet) →ₗ[ℂ] B :=
  IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj LeptonDoublet.gaugeAlgebraAction)
  (barL i) n l 0

/-- The iterated covariant derivative of the lepton singlets. -/
noncomputable def covDerivE (h : IsStandardModel B repJet repLorentz massWeightPoly H barH A
    d bard u baru Q barQ L barL e bare) (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ LeptonSinglet →ₗ[ℂ] B :=
  IsGaugeField.covDerivIter A LeptonSinglet.gaugeAlgebraAction (e i) n l 0

/-- The iterated covariant derivative of the conjugate lepton singlets. -/
noncomputable def covDerivBarE (h : IsStandardModel B repJet repLorentz massWeightPoly H barH A
    d bard u baru Q barQ L barL e bare) (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ (ConjModule LeptonSinglet) →ₗ[ℂ] B :=
  IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj LeptonSinglet.gaugeAlgebraAction)
  (bare i) n l 0


/-!

## Gauge group actions on the covariant derivatives

-/


/-!

## The algebra written in terms of covariant derivatives


-/
/-- **The covariant field algebra**: replacing the plain derivative symbols of every
  matter field — the Higgs, the fermions, and all their conjugates — by their covariant
  derivative towers does not change the generated algebra; only the gauge-field symbols
  remain plain. Each replacement is the span lemma
  `IsGaugeField.adjoin_symbols_eq_adjoin_covDerivIter`, instantiated with the species'
  infinitesimal action (`GaugeAlgebra.actionConj` of it for the conjugates). -/
lemma fieldAlgebra_eq_covDeriv :
    h.fieldAlgebra = Algebra.adjoin ℂ
    ((⋃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3), Set.range (A s μ)) ∪
      (⋃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
        Set.range (h.covDerivH l) ∪ Set.range (h.covDerivBarH l)) ∪
      (⋃ (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
        Set.range (h.covDerivD i l) ∪ Set.range (h.covDerivBarD i l) ∪
        Set.range (h.covDerivU i l) ∪ Set.range (h.covDerivBarU i l) ∪
        Set.range (h.covDerivQ i l) ∪ Set.range (h.covDerivBarQ i l) ∪
        Set.range (h.covDerivL i l) ∪ Set.range (h.covDerivBarL i l) ∪
        Set.range (h.covDerivE i l) ∪ Set.range (h.covDerivBarE i l))) := by
  -- the span lemma, per field
  have hATH :
      Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (HiggsVec)),
            b = H s φ}) =
      Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3))
            (φ : Module.Dual ℂ (HiggsVec)),
            b = IsGaugeField.covDerivIter A (HiggsVec.gaugeAlgebraAction) H n l 0 φ}) :=
    IsGaugeField.adjoin_symbols_eq_adjoin_covDerivIter (HiggsVec.gaugeAlgebraAction) H
  have hATbarH :
      Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule HiggsVec)),
            b = barH s φ}) =
      Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3))
            (φ : Module.Dual ℂ (ConjModule HiggsVec)),
            b = IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj HiggsVec.gaugeAlgebraAction) barH n l 0 φ}) :=
    IsGaugeField.adjoin_symbols_eq_adjoin_covDerivIter (GaugeAlgebra.actionConj HiggsVec.gaugeAlgebraAction) barH
  have hATd : ∀ i : Fin 3,
      Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (DownSinglet)),
            b = d i s φ}) =
      Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3))
            (φ : Module.Dual ℂ (DownSinglet)),
            b = IsGaugeField.covDerivIter A (DownSinglet.gaugeAlgebraAction) (d i) n l 0 φ}) :=
    fun i => IsGaugeField.adjoin_symbols_eq_adjoin_covDerivIter (DownSinglet.gaugeAlgebraAction) (d i)
  have hATbard : ∀ i : Fin 3,
      Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule DownSinglet)),
            b = bard i s φ}) =
      Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3))
            (φ : Module.Dual ℂ (ConjModule DownSinglet)),
            b = IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj DownSinglet.gaugeAlgebraAction) (bard i) n l 0 φ}) :=
    fun i => IsGaugeField.adjoin_symbols_eq_adjoin_covDerivIter (GaugeAlgebra.actionConj DownSinglet.gaugeAlgebraAction) (bard i)
  have hATu : ∀ i : Fin 3,
      Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (UpSinglet)),
            b = u i s φ}) =
      Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3))
            (φ : Module.Dual ℂ (UpSinglet)),
            b = IsGaugeField.covDerivIter A (UpSinglet.gaugeAlgebraAction) (u i) n l 0 φ}) :=
    fun i => IsGaugeField.adjoin_symbols_eq_adjoin_covDerivIter (UpSinglet.gaugeAlgebraAction) (u i)
  have hATbaru : ∀ i : Fin 3,
      Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule UpSinglet)),
            b = baru i s φ}) =
      Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3))
            (φ : Module.Dual ℂ (ConjModule UpSinglet)),
            b = IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj UpSinglet.gaugeAlgebraAction) (baru i) n l 0 φ}) :=
    fun i => IsGaugeField.adjoin_symbols_eq_adjoin_covDerivIter (GaugeAlgebra.actionConj UpSinglet.gaugeAlgebraAction) (baru i)
  have hATQ : ∀ i : Fin 3,
      Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (QuarkDoublet)),
            b = Q i s φ}) =
      Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3))
            (φ : Module.Dual ℂ (QuarkDoublet)),
            b = IsGaugeField.covDerivIter A (QuarkDoublet.gaugeAlgebraAction) (Q i) n l 0 φ}) :=
    fun i => IsGaugeField.adjoin_symbols_eq_adjoin_covDerivIter (QuarkDoublet.gaugeAlgebraAction) (Q i)
  have hATbarQ : ∀ i : Fin 3,
      Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule QuarkDoublet)),
            b = barQ i s φ}) =
      Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3))
            (φ : Module.Dual ℂ (ConjModule QuarkDoublet)),
            b = IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj QuarkDoublet.gaugeAlgebraAction) (barQ i) n l 0 φ}) :=
    fun i => IsGaugeField.adjoin_symbols_eq_adjoin_covDerivIter (GaugeAlgebra.actionConj QuarkDoublet.gaugeAlgebraAction) (barQ i)
  have hATL : ∀ i : Fin 3,
      Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (LeptonDoublet)),
            b = L i s φ}) =
      Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3))
            (φ : Module.Dual ℂ (LeptonDoublet)),
            b = IsGaugeField.covDerivIter A (LeptonDoublet.gaugeAlgebraAction) (L i) n l 0 φ}) :=
    fun i => IsGaugeField.adjoin_symbols_eq_adjoin_covDerivIter (LeptonDoublet.gaugeAlgebraAction) (L i)
  have hATbarL : ∀ i : Fin 3,
      Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule LeptonDoublet)),
            b = barL i s φ}) =
      Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3))
            (φ : Module.Dual ℂ (ConjModule LeptonDoublet)),
            b = IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj LeptonDoublet.gaugeAlgebraAction) (barL i) n l 0 φ}) :=
    fun i => IsGaugeField.adjoin_symbols_eq_adjoin_covDerivIter (GaugeAlgebra.actionConj LeptonDoublet.gaugeAlgebraAction) (barL i)
  have hATe : ∀ i : Fin 3,
      Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (LeptonSinglet)),
            b = e i s φ}) =
      Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3))
            (φ : Module.Dual ℂ (LeptonSinglet)),
            b = IsGaugeField.covDerivIter A (LeptonSinglet.gaugeAlgebraAction) (e i) n l 0 φ}) :=
    fun i => IsGaugeField.adjoin_symbols_eq_adjoin_covDerivIter (LeptonSinglet.gaugeAlgebraAction) (e i)
  have hATbare : ∀ i : Fin 3,
      Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule LeptonSinglet)),
            b = bare i s φ}) =
      Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3))
            (φ : Module.Dual ℂ (ConjModule LeptonSinglet)),
            b = IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj LeptonSinglet.gaugeAlgebraAction) (bare i) n l 0 φ}) :=
    fun i => IsGaugeField.adjoin_symbols_eq_adjoin_covDerivIter (GaugeAlgebra.actionConj LeptonSinglet.gaugeAlgebraAction) (bare i)
  -- every plain matter symbol lies in the covariant algebra
  have hmem_H : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (HiggsVec)),
      H s φ ∈ Algebra.adjoin ℂ
    ((⋃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3), Set.range (A s μ)) ∪
      (⋃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
        Set.range (h.covDerivH l) ∪ Set.range (h.covDerivBarH l)) ∪
      (⋃ (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
        Set.range (h.covDerivD i l) ∪ Set.range (h.covDerivBarD i l) ∪
        Set.range (h.covDerivU i l) ∪ Set.range (h.covDerivBarU i l) ∪
        Set.range (h.covDerivQ i l) ∪ Set.range (h.covDerivBarQ i l) ∪
        Set.range (h.covDerivL i l) ∪ Set.range (h.covDerivBarL i l) ∪
        Set.range (h.covDerivE i l) ∪ Set.range (h.covDerivBarE i l))) := by
    intro s φ
    have h1 : H s φ ∈ Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3))
            (φ : Module.Dual ℂ (HiggsVec)),
            b = IsGaugeField.covDerivIter A (HiggsVec.gaugeAlgebraAction) H n l 0 φ}) :=
      hATH.le (Algebra.subset_adjoin (Or.inr ⟨s, φ, rfl⟩))
    refine SetLike.le_def.mp (Algebra.adjoin_mono ?_) h1
    rintro b (⟨u', μ, ψ, rfl⟩ | ⟨n, l, φ', rfl⟩)
    · exact Or.inl (Or.inl
        (Set.mem_iUnion.mpr ⟨u', Set.mem_iUnion.mpr ⟨μ, ⟨ψ, rfl⟩⟩⟩))
    · refine Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨l, ?_⟩⟩))
      have hmem : IsGaugeField.covDerivIter A (HiggsVec.gaugeAlgebraAction) H n l 0 φ'
          ∈ Set.range (h.covDerivH l) := ⟨φ', rfl⟩
      simp only [Set.mem_union]
      tauto
  have hmem_barH : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule HiggsVec)),
      barH s φ ∈ Algebra.adjoin ℂ
    ((⋃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3), Set.range (A s μ)) ∪
      (⋃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
        Set.range (h.covDerivH l) ∪ Set.range (h.covDerivBarH l)) ∪
      (⋃ (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
        Set.range (h.covDerivD i l) ∪ Set.range (h.covDerivBarD i l) ∪
        Set.range (h.covDerivU i l) ∪ Set.range (h.covDerivBarU i l) ∪
        Set.range (h.covDerivQ i l) ∪ Set.range (h.covDerivBarQ i l) ∪
        Set.range (h.covDerivL i l) ∪ Set.range (h.covDerivBarL i l) ∪
        Set.range (h.covDerivE i l) ∪ Set.range (h.covDerivBarE i l))) := by
    intro s φ
    have h1 : barH s φ ∈ Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3))
            (φ : Module.Dual ℂ (ConjModule HiggsVec)),
            b = IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj HiggsVec.gaugeAlgebraAction) barH n l 0 φ}) :=
      hATbarH.le (Algebra.subset_adjoin (Or.inr ⟨s, φ, rfl⟩))
    refine SetLike.le_def.mp (Algebra.adjoin_mono ?_) h1
    rintro b (⟨u', μ, ψ, rfl⟩ | ⟨n, l, φ', rfl⟩)
    · exact Or.inl (Or.inl
        (Set.mem_iUnion.mpr ⟨u', Set.mem_iUnion.mpr ⟨μ, ⟨ψ, rfl⟩⟩⟩))
    · refine Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨l, ?_⟩⟩))
      have hmem : IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj HiggsVec.gaugeAlgebraAction) barH n l 0 φ'
          ∈ Set.range (h.covDerivBarH l) := ⟨φ', rfl⟩
      simp only [Set.mem_union]
      tauto
  have hmem_d : ∀ (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (DownSinglet)),
      d i s φ ∈ Algebra.adjoin ℂ
    ((⋃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3), Set.range (A s μ)) ∪
      (⋃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
        Set.range (h.covDerivH l) ∪ Set.range (h.covDerivBarH l)) ∪
      (⋃ (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
        Set.range (h.covDerivD i l) ∪ Set.range (h.covDerivBarD i l) ∪
        Set.range (h.covDerivU i l) ∪ Set.range (h.covDerivBarU i l) ∪
        Set.range (h.covDerivQ i l) ∪ Set.range (h.covDerivBarQ i l) ∪
        Set.range (h.covDerivL i l) ∪ Set.range (h.covDerivBarL i l) ∪
        Set.range (h.covDerivE i l) ∪ Set.range (h.covDerivBarE i l))) := by
    intro i s φ
    have h1 : d i s φ ∈ Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3))
            (φ : Module.Dual ℂ (DownSinglet)),
            b = IsGaugeField.covDerivIter A (DownSinglet.gaugeAlgebraAction) (d i) n l 0 φ}) :=
      (hATd i).le (Algebra.subset_adjoin (Or.inr ⟨s, φ, rfl⟩))
    refine SetLike.le_def.mp (Algebra.adjoin_mono ?_) h1
    rintro b (⟨u', μ, ψ, rfl⟩ | ⟨n, l, φ', rfl⟩)
    · exact Or.inl (Or.inl
        (Set.mem_iUnion.mpr ⟨u', Set.mem_iUnion.mpr ⟨μ, ⟨ψ, rfl⟩⟩⟩))
    · refine Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨n,
        Set.mem_iUnion.mpr ⟨l, ?_⟩⟩⟩)
      have hmem : IsGaugeField.covDerivIter A (DownSinglet.gaugeAlgebraAction) (d i) n l 0 φ'
          ∈ Set.range (h.covDerivD i l) := ⟨φ', rfl⟩
      simp only [Set.mem_union]
      tauto
  have hmem_bard : ∀ (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule DownSinglet)),
      bard i s φ ∈ Algebra.adjoin ℂ
    ((⋃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3), Set.range (A s μ)) ∪
      (⋃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
        Set.range (h.covDerivH l) ∪ Set.range (h.covDerivBarH l)) ∪
      (⋃ (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
        Set.range (h.covDerivD i l) ∪ Set.range (h.covDerivBarD i l) ∪
        Set.range (h.covDerivU i l) ∪ Set.range (h.covDerivBarU i l) ∪
        Set.range (h.covDerivQ i l) ∪ Set.range (h.covDerivBarQ i l) ∪
        Set.range (h.covDerivL i l) ∪ Set.range (h.covDerivBarL i l) ∪
        Set.range (h.covDerivE i l) ∪ Set.range (h.covDerivBarE i l))) := by
    intro i s φ
    have h1 : bard i s φ ∈ Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3))
            (φ : Module.Dual ℂ (ConjModule DownSinglet)),
            b = IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj DownSinglet.gaugeAlgebraAction) (bard i) n l 0 φ}) :=
      (hATbard i).le (Algebra.subset_adjoin (Or.inr ⟨s, φ, rfl⟩))
    refine SetLike.le_def.mp (Algebra.adjoin_mono ?_) h1
    rintro b (⟨u', μ, ψ, rfl⟩ | ⟨n, l, φ', rfl⟩)
    · exact Or.inl (Or.inl
        (Set.mem_iUnion.mpr ⟨u', Set.mem_iUnion.mpr ⟨μ, ⟨ψ, rfl⟩⟩⟩))
    · refine Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨n,
        Set.mem_iUnion.mpr ⟨l, ?_⟩⟩⟩)
      have hmem : IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj DownSinglet.gaugeAlgebraAction) (bard i) n l 0 φ'
          ∈ Set.range (h.covDerivBarD i l) := ⟨φ', rfl⟩
      simp only [Set.mem_union]
      tauto
  have hmem_u : ∀ (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (UpSinglet)),
      u i s φ ∈ Algebra.adjoin ℂ
    ((⋃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3), Set.range (A s μ)) ∪
      (⋃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
        Set.range (h.covDerivH l) ∪ Set.range (h.covDerivBarH l)) ∪
      (⋃ (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
        Set.range (h.covDerivD i l) ∪ Set.range (h.covDerivBarD i l) ∪
        Set.range (h.covDerivU i l) ∪ Set.range (h.covDerivBarU i l) ∪
        Set.range (h.covDerivQ i l) ∪ Set.range (h.covDerivBarQ i l) ∪
        Set.range (h.covDerivL i l) ∪ Set.range (h.covDerivBarL i l) ∪
        Set.range (h.covDerivE i l) ∪ Set.range (h.covDerivBarE i l))) := by
    intro i s φ
    have h1 : u i s φ ∈ Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3))
            (φ : Module.Dual ℂ (UpSinglet)),
            b = IsGaugeField.covDerivIter A (UpSinglet.gaugeAlgebraAction) (u i) n l 0 φ}) :=
      (hATu i).le (Algebra.subset_adjoin (Or.inr ⟨s, φ, rfl⟩))
    refine SetLike.le_def.mp (Algebra.adjoin_mono ?_) h1
    rintro b (⟨u', μ, ψ, rfl⟩ | ⟨n, l, φ', rfl⟩)
    · exact Or.inl (Or.inl
        (Set.mem_iUnion.mpr ⟨u', Set.mem_iUnion.mpr ⟨μ, ⟨ψ, rfl⟩⟩⟩))
    · refine Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨n,
        Set.mem_iUnion.mpr ⟨l, ?_⟩⟩⟩)
      have hmem : IsGaugeField.covDerivIter A (UpSinglet.gaugeAlgebraAction) (u i) n l 0 φ'
          ∈ Set.range (h.covDerivU i l) := ⟨φ', rfl⟩
      simp only [Set.mem_union]
      tauto
  have hmem_baru : ∀ (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule UpSinglet)),
      baru i s φ ∈ Algebra.adjoin ℂ
    ((⋃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3), Set.range (A s μ)) ∪
      (⋃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
        Set.range (h.covDerivH l) ∪ Set.range (h.covDerivBarH l)) ∪
      (⋃ (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
        Set.range (h.covDerivD i l) ∪ Set.range (h.covDerivBarD i l) ∪
        Set.range (h.covDerivU i l) ∪ Set.range (h.covDerivBarU i l) ∪
        Set.range (h.covDerivQ i l) ∪ Set.range (h.covDerivBarQ i l) ∪
        Set.range (h.covDerivL i l) ∪ Set.range (h.covDerivBarL i l) ∪
        Set.range (h.covDerivE i l) ∪ Set.range (h.covDerivBarE i l))) := by
    intro i s φ
    have h1 : baru i s φ ∈ Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3))
            (φ : Module.Dual ℂ (ConjModule UpSinglet)),
            b = IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj UpSinglet.gaugeAlgebraAction) (baru i) n l 0 φ}) :=
      (hATbaru i).le (Algebra.subset_adjoin (Or.inr ⟨s, φ, rfl⟩))
    refine SetLike.le_def.mp (Algebra.adjoin_mono ?_) h1
    rintro b (⟨u', μ, ψ, rfl⟩ | ⟨n, l, φ', rfl⟩)
    · exact Or.inl (Or.inl
        (Set.mem_iUnion.mpr ⟨u', Set.mem_iUnion.mpr ⟨μ, ⟨ψ, rfl⟩⟩⟩))
    · refine Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨n,
        Set.mem_iUnion.mpr ⟨l, ?_⟩⟩⟩)
      have hmem : IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj UpSinglet.gaugeAlgebraAction) (baru i) n l 0 φ'
          ∈ Set.range (h.covDerivBarU i l) := ⟨φ', rfl⟩
      simp only [Set.mem_union]
      tauto
  have hmem_Q : ∀ (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (QuarkDoublet)),
      Q i s φ ∈ Algebra.adjoin ℂ
    ((⋃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3), Set.range (A s μ)) ∪
      (⋃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
        Set.range (h.covDerivH l) ∪ Set.range (h.covDerivBarH l)) ∪
      (⋃ (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
        Set.range (h.covDerivD i l) ∪ Set.range (h.covDerivBarD i l) ∪
        Set.range (h.covDerivU i l) ∪ Set.range (h.covDerivBarU i l) ∪
        Set.range (h.covDerivQ i l) ∪ Set.range (h.covDerivBarQ i l) ∪
        Set.range (h.covDerivL i l) ∪ Set.range (h.covDerivBarL i l) ∪
        Set.range (h.covDerivE i l) ∪ Set.range (h.covDerivBarE i l))) := by
    intro i s φ
    have h1 : Q i s φ ∈ Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3))
            (φ : Module.Dual ℂ (QuarkDoublet)),
            b = IsGaugeField.covDerivIter A (QuarkDoublet.gaugeAlgebraAction) (Q i) n l 0 φ}) :=
      (hATQ i).le (Algebra.subset_adjoin (Or.inr ⟨s, φ, rfl⟩))
    refine SetLike.le_def.mp (Algebra.adjoin_mono ?_) h1
    rintro b (⟨u', μ, ψ, rfl⟩ | ⟨n, l, φ', rfl⟩)
    · exact Or.inl (Or.inl
        (Set.mem_iUnion.mpr ⟨u', Set.mem_iUnion.mpr ⟨μ, ⟨ψ, rfl⟩⟩⟩))
    · refine Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨n,
        Set.mem_iUnion.mpr ⟨l, ?_⟩⟩⟩)
      have hmem : IsGaugeField.covDerivIter A (QuarkDoublet.gaugeAlgebraAction) (Q i) n l 0 φ'
          ∈ Set.range (h.covDerivQ i l) := ⟨φ', rfl⟩
      simp only [Set.mem_union]
      tauto
  have hmem_barQ : ∀ (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule QuarkDoublet)),
      barQ i s φ ∈ Algebra.adjoin ℂ
    ((⋃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3), Set.range (A s μ)) ∪
      (⋃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
        Set.range (h.covDerivH l) ∪ Set.range (h.covDerivBarH l)) ∪
      (⋃ (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
        Set.range (h.covDerivD i l) ∪ Set.range (h.covDerivBarD i l) ∪
        Set.range (h.covDerivU i l) ∪ Set.range (h.covDerivBarU i l) ∪
        Set.range (h.covDerivQ i l) ∪ Set.range (h.covDerivBarQ i l) ∪
        Set.range (h.covDerivL i l) ∪ Set.range (h.covDerivBarL i l) ∪
        Set.range (h.covDerivE i l) ∪ Set.range (h.covDerivBarE i l))) := by
    intro i s φ
    have h1 : barQ i s φ ∈ Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3))
            (φ : Module.Dual ℂ (ConjModule QuarkDoublet)),
            b = IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj QuarkDoublet.gaugeAlgebraAction) (barQ i) n l 0 φ}) :=
      (hATbarQ i).le (Algebra.subset_adjoin (Or.inr ⟨s, φ, rfl⟩))
    refine SetLike.le_def.mp (Algebra.adjoin_mono ?_) h1
    rintro b (⟨u', μ, ψ, rfl⟩ | ⟨n, l, φ', rfl⟩)
    · exact Or.inl (Or.inl
        (Set.mem_iUnion.mpr ⟨u', Set.mem_iUnion.mpr ⟨μ, ⟨ψ, rfl⟩⟩⟩))
    · refine Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨n,
        Set.mem_iUnion.mpr ⟨l, ?_⟩⟩⟩)
      have hmem : IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj QuarkDoublet.gaugeAlgebraAction) (barQ i) n l 0 φ'
          ∈ Set.range (h.covDerivBarQ i l) := ⟨φ', rfl⟩
      simp only [Set.mem_union]
      tauto
  have hmem_L : ∀ (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (LeptonDoublet)),
      L i s φ ∈ Algebra.adjoin ℂ
    ((⋃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3), Set.range (A s μ)) ∪
      (⋃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
        Set.range (h.covDerivH l) ∪ Set.range (h.covDerivBarH l)) ∪
      (⋃ (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
        Set.range (h.covDerivD i l) ∪ Set.range (h.covDerivBarD i l) ∪
        Set.range (h.covDerivU i l) ∪ Set.range (h.covDerivBarU i l) ∪
        Set.range (h.covDerivQ i l) ∪ Set.range (h.covDerivBarQ i l) ∪
        Set.range (h.covDerivL i l) ∪ Set.range (h.covDerivBarL i l) ∪
        Set.range (h.covDerivE i l) ∪ Set.range (h.covDerivBarE i l))) := by
    intro i s φ
    have h1 : L i s φ ∈ Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3))
            (φ : Module.Dual ℂ (LeptonDoublet)),
            b = IsGaugeField.covDerivIter A (LeptonDoublet.gaugeAlgebraAction) (L i) n l 0 φ}) :=
      (hATL i).le (Algebra.subset_adjoin (Or.inr ⟨s, φ, rfl⟩))
    refine SetLike.le_def.mp (Algebra.adjoin_mono ?_) h1
    rintro b (⟨u', μ, ψ, rfl⟩ | ⟨n, l, φ', rfl⟩)
    · exact Or.inl (Or.inl
        (Set.mem_iUnion.mpr ⟨u', Set.mem_iUnion.mpr ⟨μ, ⟨ψ, rfl⟩⟩⟩))
    · refine Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨n,
        Set.mem_iUnion.mpr ⟨l, ?_⟩⟩⟩)
      have hmem : IsGaugeField.covDerivIter A (LeptonDoublet.gaugeAlgebraAction) (L i) n l 0 φ'
          ∈ Set.range (h.covDerivL i l) := ⟨φ', rfl⟩
      simp only [Set.mem_union]
      tauto
  have hmem_barL : ∀ (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule LeptonDoublet)),
      barL i s φ ∈ Algebra.adjoin ℂ
    ((⋃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3), Set.range (A s μ)) ∪
      (⋃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
        Set.range (h.covDerivH l) ∪ Set.range (h.covDerivBarH l)) ∪
      (⋃ (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
        Set.range (h.covDerivD i l) ∪ Set.range (h.covDerivBarD i l) ∪
        Set.range (h.covDerivU i l) ∪ Set.range (h.covDerivBarU i l) ∪
        Set.range (h.covDerivQ i l) ∪ Set.range (h.covDerivBarQ i l) ∪
        Set.range (h.covDerivL i l) ∪ Set.range (h.covDerivBarL i l) ∪
        Set.range (h.covDerivE i l) ∪ Set.range (h.covDerivBarE i l))) := by
    intro i s φ
    have h1 : barL i s φ ∈ Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3))
            (φ : Module.Dual ℂ (ConjModule LeptonDoublet)),
            b = IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj LeptonDoublet.gaugeAlgebraAction) (barL i) n l 0 φ}) :=
      (hATbarL i).le (Algebra.subset_adjoin (Or.inr ⟨s, φ, rfl⟩))
    refine SetLike.le_def.mp (Algebra.adjoin_mono ?_) h1
    rintro b (⟨u', μ, ψ, rfl⟩ | ⟨n, l, φ', rfl⟩)
    · exact Or.inl (Or.inl
        (Set.mem_iUnion.mpr ⟨u', Set.mem_iUnion.mpr ⟨μ, ⟨ψ, rfl⟩⟩⟩))
    · refine Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨n,
        Set.mem_iUnion.mpr ⟨l, ?_⟩⟩⟩)
      have hmem : IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj LeptonDoublet.gaugeAlgebraAction) (barL i) n l 0 φ'
          ∈ Set.range (h.covDerivBarL i l) := ⟨φ', rfl⟩
      simp only [Set.mem_union]
      tauto
  have hmem_e : ∀ (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (LeptonSinglet)),
      e i s φ ∈ Algebra.adjoin ℂ
    ((⋃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3), Set.range (A s μ)) ∪
      (⋃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
        Set.range (h.covDerivH l) ∪ Set.range (h.covDerivBarH l)) ∪
      (⋃ (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
        Set.range (h.covDerivD i l) ∪ Set.range (h.covDerivBarD i l) ∪
        Set.range (h.covDerivU i l) ∪ Set.range (h.covDerivBarU i l) ∪
        Set.range (h.covDerivQ i l) ∪ Set.range (h.covDerivBarQ i l) ∪
        Set.range (h.covDerivL i l) ∪ Set.range (h.covDerivBarL i l) ∪
        Set.range (h.covDerivE i l) ∪ Set.range (h.covDerivBarE i l))) := by
    intro i s φ
    have h1 : e i s φ ∈ Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3))
            (φ : Module.Dual ℂ (LeptonSinglet)),
            b = IsGaugeField.covDerivIter A (LeptonSinglet.gaugeAlgebraAction) (e i) n l 0 φ}) :=
      (hATe i).le (Algebra.subset_adjoin (Or.inr ⟨s, φ, rfl⟩))
    refine SetLike.le_def.mp (Algebra.adjoin_mono ?_) h1
    rintro b (⟨u', μ, ψ, rfl⟩ | ⟨n, l, φ', rfl⟩)
    · exact Or.inl (Or.inl
        (Set.mem_iUnion.mpr ⟨u', Set.mem_iUnion.mpr ⟨μ, ⟨ψ, rfl⟩⟩⟩))
    · refine Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨n,
        Set.mem_iUnion.mpr ⟨l, ?_⟩⟩⟩)
      have hmem : IsGaugeField.covDerivIter A (LeptonSinglet.gaugeAlgebraAction) (e i) n l 0 φ'
          ∈ Set.range (h.covDerivE i l) := ⟨φ', rfl⟩
      simp only [Set.mem_union]
      tauto
  have hmem_bare : ∀ (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule LeptonSinglet)),
      bare i s φ ∈ Algebra.adjoin ℂ
    ((⋃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3), Set.range (A s μ)) ∪
      (⋃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
        Set.range (h.covDerivH l) ∪ Set.range (h.covDerivBarH l)) ∪
      (⋃ (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
        Set.range (h.covDerivD i l) ∪ Set.range (h.covDerivBarD i l) ∪
        Set.range (h.covDerivU i l) ∪ Set.range (h.covDerivBarU i l) ∪
        Set.range (h.covDerivQ i l) ∪ Set.range (h.covDerivBarQ i l) ∪
        Set.range (h.covDerivL i l) ∪ Set.range (h.covDerivBarL i l) ∪
        Set.range (h.covDerivE i l) ∪ Set.range (h.covDerivBarE i l))) := by
    intro i s φ
    have h1 : bare i s φ ∈ Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3))
            (φ : Module.Dual ℂ (ConjModule LeptonSinglet)),
            b = IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj LeptonSinglet.gaugeAlgebraAction) (bare i) n l 0 φ}) :=
      (hATbare i).le (Algebra.subset_adjoin (Or.inr ⟨s, φ, rfl⟩))
    refine SetLike.le_def.mp (Algebra.adjoin_mono ?_) h1
    rintro b (⟨u', μ, ψ, rfl⟩ | ⟨n, l, φ', rfl⟩)
    · exact Or.inl (Or.inl
        (Set.mem_iUnion.mpr ⟨u', Set.mem_iUnion.mpr ⟨μ, ⟨ψ, rfl⟩⟩⟩))
    · refine Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨n,
        Set.mem_iUnion.mpr ⟨l, ?_⟩⟩⟩)
      have hmem : IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj LeptonSinglet.gaugeAlgebraAction) (bare i) n l 0 φ'
          ∈ Set.range (h.covDerivBarE i l) := ⟨φ', rfl⟩
      simp only [Set.mem_union]
      tauto
  refine le_antisymm (Algebra.adjoin_le ?_) (Algebra.adjoin_le ?_)
  · rintro b (hAH | hbF)
    · rcases hAH with hA | hH
      · exact Algebra.subset_adjoin (Or.inl (Or.inl hA))
      · simp only [Set.mem_iUnion] at hH
        obtain ⟨s, hH⟩ := hH
        rcases hH with ⟨φ, rfl⟩ | ⟨φ, rfl⟩
        · exact hmem_H s φ
        · exact hmem_barH s φ
    · simp only [Set.mem_iUnion] at hbF
      obtain ⟨i, s, hbF⟩ := hbF
      rcases hbF with (((((((((⟨φ, rfl⟩ | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) |
        ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩)
      · exact hmem_d i s φ
      · exact hmem_bard i s φ
      · exact hmem_u i s φ
      · exact hmem_baru i s φ
      · exact hmem_Q i s φ
      · exact hmem_barQ i s φ
      · exact hmem_L i s φ
      · exact hmem_barL i s φ
      · exact hmem_e i s φ
      · exact hmem_bare i s φ
  · rintro b ((hA | hHT) | hFT)
    · exact Algebra.subset_adjoin (Or.inl (Or.inl hA))
    · simp only [Set.mem_iUnion] at hHT
      obtain ⟨n, l, hHT⟩ := hHT
      rcases hHT with ⟨φ, rfl⟩ | ⟨φ, rfl⟩
      · have h1 : IsGaugeField.covDerivIter A (HiggsVec.gaugeAlgebraAction) H n l 0 φ
            ∈ Algebra.adjoin ℂ
              ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
                {b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3))
                  (φ : Module.Dual ℂ (HiggsVec)), b = H s φ}) :=
          hATH.ge (Algebra.subset_adjoin (Or.inr ⟨n, l, φ, rfl⟩))
        refine SetLike.le_def.mp (Algebra.adjoin_mono ?_) h1
        rintro b (⟨u', μ, ψ, rfl⟩ | ⟨s', φ', rfl⟩)
        · exact Or.inl (Or.inl
            (Set.mem_iUnion.mpr ⟨u', Set.mem_iUnion.mpr ⟨μ, ⟨ψ, rfl⟩⟩⟩))
        · refine Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨s', ?_⟩))
          exact Or.inl ⟨φ', rfl⟩
      · have h1 : IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj HiggsVec.gaugeAlgebraAction) barH n l 0 φ
            ∈ Algebra.adjoin ℂ
              ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
                {b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3))
                  (φ : Module.Dual ℂ (ConjModule HiggsVec)), b = barH s φ}) :=
          hATbarH.ge (Algebra.subset_adjoin (Or.inr ⟨n, l, φ, rfl⟩))
        refine SetLike.le_def.mp (Algebra.adjoin_mono ?_) h1
        rintro b (⟨u', μ, ψ, rfl⟩ | ⟨s', φ', rfl⟩)
        · exact Or.inl (Or.inl
            (Set.mem_iUnion.mpr ⟨u', Set.mem_iUnion.mpr ⟨μ, ⟨ψ, rfl⟩⟩⟩))
        · refine Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨s', ?_⟩))
          exact Or.inr ⟨φ', rfl⟩
    · simp only [Set.mem_iUnion] at hFT
      obtain ⟨i, n, l, hFT⟩ := hFT
      rcases hFT with (((((((((⟨φ, rfl⟩ | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) |
        ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩)
      · have h1 : IsGaugeField.covDerivIter A (DownSinglet.gaugeAlgebraAction) (d i) n l 0 φ
            ∈ Algebra.adjoin ℂ
              ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
                {b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3))
                  (φ : Module.Dual ℂ (DownSinglet)), b = d i s φ}) :=
          (hATd i).ge (Algebra.subset_adjoin (Or.inr ⟨n, l, φ, rfl⟩))
        refine SetLike.le_def.mp (Algebra.adjoin_mono ?_) h1
        rintro b (⟨u', μ, ψ, rfl⟩ | ⟨s', φ', rfl⟩)
        · exact Or.inl (Or.inl
            (Set.mem_iUnion.mpr ⟨u', Set.mem_iUnion.mpr ⟨μ, ⟨ψ, rfl⟩⟩⟩))
        · refine Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨s', ?_⟩⟩)
          have hmem : d i s' φ' ∈ Set.range (d i s') := ⟨φ', rfl⟩
          simp only [Set.mem_union]
          tauto
      · have h1 : IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj DownSinglet.gaugeAlgebraAction) (bard i) n l 0 φ
            ∈ Algebra.adjoin ℂ
              ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
                {b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3))
                  (φ : Module.Dual ℂ (ConjModule DownSinglet)), b = bard i s φ}) :=
          (hATbard i).ge (Algebra.subset_adjoin (Or.inr ⟨n, l, φ, rfl⟩))
        refine SetLike.le_def.mp (Algebra.adjoin_mono ?_) h1
        rintro b (⟨u', μ, ψ, rfl⟩ | ⟨s', φ', rfl⟩)
        · exact Or.inl (Or.inl
            (Set.mem_iUnion.mpr ⟨u', Set.mem_iUnion.mpr ⟨μ, ⟨ψ, rfl⟩⟩⟩))
        · refine Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨s', ?_⟩⟩)
          have hmem : bard i s' φ' ∈ Set.range (bard i s') := ⟨φ', rfl⟩
          simp only [Set.mem_union]
          tauto
      · have h1 : IsGaugeField.covDerivIter A (UpSinglet.gaugeAlgebraAction) (u i) n l 0 φ
            ∈ Algebra.adjoin ℂ
              ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
                {b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3))
                  (φ : Module.Dual ℂ (UpSinglet)), b = u i s φ}) :=
          (hATu i).ge (Algebra.subset_adjoin (Or.inr ⟨n, l, φ, rfl⟩))
        refine SetLike.le_def.mp (Algebra.adjoin_mono ?_) h1
        rintro b (⟨u', μ, ψ, rfl⟩ | ⟨s', φ', rfl⟩)
        · exact Or.inl (Or.inl
            (Set.mem_iUnion.mpr ⟨u', Set.mem_iUnion.mpr ⟨μ, ⟨ψ, rfl⟩⟩⟩))
        · refine Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨s', ?_⟩⟩)
          have hmem : u i s' φ' ∈ Set.range (u i s') := ⟨φ', rfl⟩
          simp only [Set.mem_union]
          tauto
      · have h1 : IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj UpSinglet.gaugeAlgebraAction) (baru i) n l 0 φ
            ∈ Algebra.adjoin ℂ
              ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
                {b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3))
                  (φ : Module.Dual ℂ (ConjModule UpSinglet)), b = baru i s φ}) :=
          (hATbaru i).ge (Algebra.subset_adjoin (Or.inr ⟨n, l, φ, rfl⟩))
        refine SetLike.le_def.mp (Algebra.adjoin_mono ?_) h1
        rintro b (⟨u', μ, ψ, rfl⟩ | ⟨s', φ', rfl⟩)
        · exact Or.inl (Or.inl
            (Set.mem_iUnion.mpr ⟨u', Set.mem_iUnion.mpr ⟨μ, ⟨ψ, rfl⟩⟩⟩))
        · refine Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨s', ?_⟩⟩)
          have hmem : baru i s' φ' ∈ Set.range (baru i s') := ⟨φ', rfl⟩
          simp only [Set.mem_union]
          tauto
      · have h1 : IsGaugeField.covDerivIter A (QuarkDoublet.gaugeAlgebraAction) (Q i) n l 0 φ
            ∈ Algebra.adjoin ℂ
              ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
                {b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3))
                  (φ : Module.Dual ℂ (QuarkDoublet)), b = Q i s φ}) :=
          (hATQ i).ge (Algebra.subset_adjoin (Or.inr ⟨n, l, φ, rfl⟩))
        refine SetLike.le_def.mp (Algebra.adjoin_mono ?_) h1
        rintro b (⟨u', μ, ψ, rfl⟩ | ⟨s', φ', rfl⟩)
        · exact Or.inl (Or.inl
            (Set.mem_iUnion.mpr ⟨u', Set.mem_iUnion.mpr ⟨μ, ⟨ψ, rfl⟩⟩⟩))
        · refine Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨s', ?_⟩⟩)
          have hmem : Q i s' φ' ∈ Set.range (Q i s') := ⟨φ', rfl⟩
          simp only [Set.mem_union]
          tauto
      · have h1 : IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj QuarkDoublet.gaugeAlgebraAction) (barQ i) n l 0 φ
            ∈ Algebra.adjoin ℂ
              ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
                {b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3))
                  (φ : Module.Dual ℂ (ConjModule QuarkDoublet)), b = barQ i s φ}) :=
          (hATbarQ i).ge (Algebra.subset_adjoin (Or.inr ⟨n, l, φ, rfl⟩))
        refine SetLike.le_def.mp (Algebra.adjoin_mono ?_) h1
        rintro b (⟨u', μ, ψ, rfl⟩ | ⟨s', φ', rfl⟩)
        · exact Or.inl (Or.inl
            (Set.mem_iUnion.mpr ⟨u', Set.mem_iUnion.mpr ⟨μ, ⟨ψ, rfl⟩⟩⟩))
        · refine Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨s', ?_⟩⟩)
          have hmem : barQ i s' φ' ∈ Set.range (barQ i s') := ⟨φ', rfl⟩
          simp only [Set.mem_union]
          tauto
      · have h1 : IsGaugeField.covDerivIter A (LeptonDoublet.gaugeAlgebraAction) (L i) n l 0 φ
            ∈ Algebra.adjoin ℂ
              ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
                {b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3))
                  (φ : Module.Dual ℂ (LeptonDoublet)), b = L i s φ}) :=
          (hATL i).ge (Algebra.subset_adjoin (Or.inr ⟨n, l, φ, rfl⟩))
        refine SetLike.le_def.mp (Algebra.adjoin_mono ?_) h1
        rintro b (⟨u', μ, ψ, rfl⟩ | ⟨s', φ', rfl⟩)
        · exact Or.inl (Or.inl
            (Set.mem_iUnion.mpr ⟨u', Set.mem_iUnion.mpr ⟨μ, ⟨ψ, rfl⟩⟩⟩))
        · refine Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨s', ?_⟩⟩)
          have hmem : L i s' φ' ∈ Set.range (L i s') := ⟨φ', rfl⟩
          simp only [Set.mem_union]
          tauto
      · have h1 : IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj LeptonDoublet.gaugeAlgebraAction) (barL i) n l 0 φ
            ∈ Algebra.adjoin ℂ
              ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
                {b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3))
                  (φ : Module.Dual ℂ (ConjModule LeptonDoublet)), b = barL i s φ}) :=
          (hATbarL i).ge (Algebra.subset_adjoin (Or.inr ⟨n, l, φ, rfl⟩))
        refine SetLike.le_def.mp (Algebra.adjoin_mono ?_) h1
        rintro b (⟨u', μ, ψ, rfl⟩ | ⟨s', φ', rfl⟩)
        · exact Or.inl (Or.inl
            (Set.mem_iUnion.mpr ⟨u', Set.mem_iUnion.mpr ⟨μ, ⟨ψ, rfl⟩⟩⟩))
        · refine Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨s', ?_⟩⟩)
          have hmem : barL i s' φ' ∈ Set.range (barL i s') := ⟨φ', rfl⟩
          simp only [Set.mem_union]
          tauto
      · have h1 : IsGaugeField.covDerivIter A (LeptonSinglet.gaugeAlgebraAction) (e i) n l 0 φ
            ∈ Algebra.adjoin ℂ
              ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
                {b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3))
                  (φ : Module.Dual ℂ (LeptonSinglet)), b = e i s φ}) :=
          (hATe i).ge (Algebra.subset_adjoin (Or.inr ⟨n, l, φ, rfl⟩))
        refine SetLike.le_def.mp (Algebra.adjoin_mono ?_) h1
        rintro b (⟨u', μ, ψ, rfl⟩ | ⟨s', φ', rfl⟩)
        · exact Or.inl (Or.inl
            (Set.mem_iUnion.mpr ⟨u', Set.mem_iUnion.mpr ⟨μ, ⟨ψ, rfl⟩⟩⟩))
        · refine Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨s', ?_⟩⟩)
          have hmem : e i s' φ' ∈ Set.range (e i s') := ⟨φ', rfl⟩
          simp only [Set.mem_union]
          tauto
      · have h1 : IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj LeptonSinglet.gaugeAlgebraAction) (bare i) n l 0 φ
            ∈ Algebra.adjoin ℂ
              ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
                {b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3))
                  (φ : Module.Dual ℂ (ConjModule LeptonSinglet)), b = bare i s φ}) :=
          (hATbare i).ge (Algebra.subset_adjoin (Or.inr ⟨n, l, φ, rfl⟩))
        refine SetLike.le_def.mp (Algebra.adjoin_mono ?_) h1
        rintro b (⟨u', μ, ψ, rfl⟩ | ⟨s', φ', rfl⟩)
        · exact Or.inl (Or.inl
            (Set.mem_iUnion.mpr ⟨u', Set.mem_iUnion.mpr ⟨μ, ⟨ψ, rfl⟩⟩⟩))
        · refine Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨s', ?_⟩⟩)
          have hmem : bare i s' φ' ∈ Set.range (bare i s') := ⟨φ', rfl⟩
          simp only [Set.mem_union]
          tauto

/-!

## C. Gauge covariance of the covariant derivatives

-/

include h in
/-- **Gauge covariance of the covariant derivatives of the Higgs field**: every derivative
  symbol of the tower transforms by the pure Leibniz convolution of the dual
  representation coefficients, with no inhomogeneous term. -/
lemma transformsIn_covDerivH (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    TransformsIn repJet (HiggsVec.repJetGaugeGroupI)
      (IsGaugeField.covDerivIter A (HiggsVec.gaugeAlgebraAction) H n l) :=
  TransformsIn.covDerivIter h.repJet_A h.repJet_H (HiggsVec.isInfinitesimalActionOf) n l

include h in
/-- **Gauge covariance of the covariant derivatives of the conjugate Higgs field**: every derivative
  symbol of the tower transforms by the pure Leibniz convolution of the dual
  representation coefficients, with no inhomogeneous term. -/
lemma transformsIn_covDerivBarH (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    TransformsIn repJet (repConj HiggsVec.repJetGaugeGroupI)
      (IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj HiggsVec.gaugeAlgebraAction) barH n l) :=
  TransformsIn.covDerivIter h.repJet_A h.repJet_barH (HiggsVec.isInfinitesimalActionOf.conj) n l

include h in
/-- **Gauge covariance of the covariant derivatives of the down-type quarks**: every derivative
  symbol of the tower transforms by the pure Leibniz convolution of the dual
  representation coefficients, with no inhomogeneous term. -/
lemma transformsIn_covDerivD (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    TransformsIn repJet (DownSinglet.repJetGaugeGroupI)
      (IsGaugeField.covDerivIter A (DownSinglet.gaugeAlgebraAction) (d i) n l) :=
  TransformsIn.covDerivIter h.repJet_A (h.repJet_d i) (DownSinglet.isInfinitesimalActionOf) n l

include h in
/-- **Gauge covariance of the covariant derivatives of the conjugate down-type quarks**: every derivative
  symbol of the tower transforms by the pure Leibniz convolution of the dual
  representation coefficients, with no inhomogeneous term. -/
lemma transformsIn_covDerivBarD (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    TransformsIn repJet (repConj DownSinglet.repJetGaugeGroupI)
      (IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj DownSinglet.gaugeAlgebraAction) (bard i) n l) :=
  TransformsIn.covDerivIter h.repJet_A (h.repJet_bard i) (DownSinglet.isInfinitesimalActionOf.conj) n l

include h in
/-- **Gauge covariance of the covariant derivatives of the up-type quarks**: every derivative
  symbol of the tower transforms by the pure Leibniz convolution of the dual
  representation coefficients, with no inhomogeneous term. -/
lemma transformsIn_covDerivU (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    TransformsIn repJet (UpSinglet.repJetGaugeGroupI)
      (IsGaugeField.covDerivIter A (UpSinglet.gaugeAlgebraAction) (u i) n l) :=
  TransformsIn.covDerivIter h.repJet_A (h.repJet_u i) (UpSinglet.isInfinitesimalActionOf) n l

include h in
/-- **Gauge covariance of the covariant derivatives of the conjugate up-type quarks**: every derivative
  symbol of the tower transforms by the pure Leibniz convolution of the dual
  representation coefficients, with no inhomogeneous term. -/
lemma transformsIn_covDerivBarU (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    TransformsIn repJet (repConj UpSinglet.repJetGaugeGroupI)
      (IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj UpSinglet.gaugeAlgebraAction) (baru i) n l) :=
  TransformsIn.covDerivIter h.repJet_A (h.repJet_baru i) (UpSinglet.isInfinitesimalActionOf.conj) n l

include h in
/-- **Gauge covariance of the covariant derivatives of the quark doublets**: every derivative
  symbol of the tower transforms by the pure Leibniz convolution of the dual
  representation coefficients, with no inhomogeneous term. -/
lemma transformsIn_covDerivQ (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    TransformsIn repJet (QuarkDoublet.repJetGaugeGroupI)
      (IsGaugeField.covDerivIter A (QuarkDoublet.gaugeAlgebraAction) (Q i) n l) :=
  TransformsIn.covDerivIter h.repJet_A (h.repJet_Q i) (QuarkDoublet.isInfinitesimalActionOf) n l

include h in
/-- **Gauge covariance of the covariant derivatives of the conjugate quark doublets**: every derivative
  symbol of the tower transforms by the pure Leibniz convolution of the dual
  representation coefficients, with no inhomogeneous term. -/
lemma transformsIn_covDerivBarQ (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    TransformsIn repJet (repConj QuarkDoublet.repJetGaugeGroupI)
      (IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj QuarkDoublet.gaugeAlgebraAction) (barQ i) n l) :=
  TransformsIn.covDerivIter h.repJet_A (h.repJet_barQ i) (QuarkDoublet.isInfinitesimalActionOf.conj) n l

include h in
/-- **Gauge covariance of the covariant derivatives of the lepton doublets**: every derivative
  symbol of the tower transforms by the pure Leibniz convolution of the dual
  representation coefficients, with no inhomogeneous term. -/
lemma transformsIn_covDerivL (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    TransformsIn repJet (LeptonDoublet.repJetGaugeGroupI)
      (IsGaugeField.covDerivIter A (LeptonDoublet.gaugeAlgebraAction) (L i) n l) :=
  TransformsIn.covDerivIter h.repJet_A (h.repJet_L i) (LeptonDoublet.isInfinitesimalActionOf) n l

include h in
/-- **Gauge covariance of the covariant derivatives of the conjugate lepton doublets**: every derivative
  symbol of the tower transforms by the pure Leibniz convolution of the dual
  representation coefficients, with no inhomogeneous term. -/
lemma transformsIn_covDerivBarL (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    TransformsIn repJet (repConj LeptonDoublet.repJetGaugeGroupI)
      (IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj LeptonDoublet.gaugeAlgebraAction) (barL i) n l) :=
  TransformsIn.covDerivIter h.repJet_A (h.repJet_barL i) (LeptonDoublet.isInfinitesimalActionOf.conj) n l

include h in
/-- **Gauge covariance of the covariant derivatives of the lepton singlets**: every derivative
  symbol of the tower transforms by the pure Leibniz convolution of the dual
  representation coefficients, with no inhomogeneous term. -/
lemma transformsIn_covDerivE (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    TransformsIn repJet (LeptonSinglet.repJetGaugeGroupI)
      (IsGaugeField.covDerivIter A (LeptonSinglet.gaugeAlgebraAction) (e i) n l) :=
  TransformsIn.covDerivIter h.repJet_A (h.repJet_e i) (LeptonSinglet.isInfinitesimalActionOf) n l

include h in
/-- **Gauge covariance of the covariant derivatives of the conjugate lepton singlets**: every derivative
  symbol of the tower transforms by the pure Leibniz convolution of the dual
  representation coefficients, with no inhomogeneous term. -/
lemma transformsIn_covDerivBarE (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    TransformsIn repJet (repConj LeptonSinglet.repJetGaugeGroupI)
      (IsGaugeField.covDerivIter A (GaugeAlgebra.actionConj LeptonSinglet.gaugeAlgebraAction) (bare i) n l) :=
  TransformsIn.covDerivIter h.repJet_A (h.repJet_bare i) (LeptonSinglet.isInfinitesimalActionOf.conj) n l

/-!

## D. The field strength and its covariant derivatives

-/

/-- The iterated covariant derivative `∇_{l₁} ⋯ ∇_{lₙ} F_{μν}` of the field strength
  of the gauge field, along an ordered list of directions. -/
noncomputable def covDerivFieldStrength (h : IsStandardModel B repJet repLorentz
    massWeightPoly H barH A d bard u baru Q barQ L barL e bare)
    (l : List (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) :
    Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B :=
  IsGaugeField.iteratedCovDerivAdjoint A l (IsGaugeField.fieldStrength A μ ν) 0

include h in
/-- **Gauge covariance of the covariant derivatives of the field strength**: every
  derivative symbol of the tower transforms in the adjoint, with no inhomogeneous
  term. -/
lemma transformsInAdjoint_covDerivFieldStrength (l : List (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) :
    IsGaugeField.TransformsInAdjoint repJet
      (IsGaugeField.iteratedCovDerivAdjoint A l (IsGaugeField.fieldStrength A μ ν)) :=
  IsGaugeField.transformsInAdjoint_iteratedCovDerivAdjoint h.repJet_A l μ ν

include h in
/-- **The covariant derivatives of the field strength transform under just the global
  gauge group**: the whole gauge jet acts through the base-point adjoint coefficient
  of its value alone — no derivative of the gauge transformation enters. -/
lemma repJet_covDerivFieldStrength (U : JetGaugeGroupI) (l : List (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra) :
    repJet U (h.covDerivFieldStrength l μ ν φ) =
      h.covDerivFieldStrength l μ ν (adjointDualCoeff U⁻¹ 0 φ) := by
  have h1 := h.transformsInAdjoint_covDerivFieldStrength l μ ν U φ 0
  simp only [Multiset.antidiagonal_zero, Multiset.map_singleton,
    Multiset.sum_singleton] at h1
  exact h1

include h in
/-- **Pure gauge jets act trivially on the covariant derivatives of the field
  strength**: gauge jets with trivial base-point value fix the whole covariant
  tower. -/
lemma repJet_covDerivFieldStrength_of_mem_truncationKer_zero
    (U : JetGaugeGroupI.truncationKer 0) (l : List (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra) :
    repJet U.1 (h.covDerivFieldStrength l μ ν φ) = h.covDerivFieldStrength l μ ν φ :=
  IsGaugeField.repGauge_iteratedCovDerivAdjoint_fieldStrength_of_mem_truncationKer_zero
    h.repJet_A U l μ ν φ

/-!

## E. The matter covariant derivatives transform through the base point

-/

include h in
/-- **The covariant derivatives of the Higgs field transform under just the global
  gauge group**: the whole gauge jet acts through the base-point dual representation
  coefficient of its value alone. -/
lemma repJet_covDerivH {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (U : JetGaugeGroupI) (φ) :
    repJet U (h.covDerivH l φ) =
      h.covDerivH l (IsGaugeField.repDualCoeff (HiggsVec.repJetGaugeGroupI) U⁻¹ 0 φ) := by
  have h1 := h.transformsIn_covDerivH n l U φ 0
  simp only [Multiset.antidiagonal_zero, Multiset.map_singleton,
    Multiset.sum_singleton] at h1
  exact h1

include h in
/-- **The covariant derivatives of the conjugate Higgs field transform under just the global
  gauge group**: the whole gauge jet acts through the base-point dual representation
  coefficient of its value alone. -/
lemma repJet_covDerivBarH {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (U : JetGaugeGroupI) (φ) :
    repJet U (h.covDerivBarH l φ) =
      h.covDerivBarH l (IsGaugeField.repDualCoeff (repConj HiggsVec.repJetGaugeGroupI) U⁻¹ 0 φ) := by
  have h1 := h.transformsIn_covDerivBarH n l U φ 0
  simp only [Multiset.antidiagonal_zero, Multiset.map_singleton,
    Multiset.sum_singleton] at h1
  exact h1

include h in
/-- **The covariant derivatives of the down-type quarks transform under just the global
  gauge group**: the whole gauge jet acts through the base-point dual representation
  coefficient of its value alone. -/
lemma repJet_covDerivD (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (U : JetGaugeGroupI) (φ) :
    repJet U (h.covDerivD i l φ) =
      h.covDerivD i l (IsGaugeField.repDualCoeff (DownSinglet.repJetGaugeGroupI) U⁻¹ 0 φ) := by
  have h1 := h.transformsIn_covDerivD i n l U φ 0
  simp only [Multiset.antidiagonal_zero, Multiset.map_singleton,
    Multiset.sum_singleton] at h1
  exact h1

include h in
/-- **The covariant derivatives of the conjugate down-type quarks transform under just the global
  gauge group**: the whole gauge jet acts through the base-point dual representation
  coefficient of its value alone. -/
lemma repJet_covDerivBarD (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (U : JetGaugeGroupI) (φ) :
    repJet U (h.covDerivBarD i l φ) =
      h.covDerivBarD i l (IsGaugeField.repDualCoeff (repConj DownSinglet.repJetGaugeGroupI) U⁻¹ 0 φ) := by
  have h1 := h.transformsIn_covDerivBarD i n l U φ 0
  simp only [Multiset.antidiagonal_zero, Multiset.map_singleton,
    Multiset.sum_singleton] at h1
  exact h1

include h in
/-- **The covariant derivatives of the up-type quarks transform under just the global
  gauge group**: the whole gauge jet acts through the base-point dual representation
  coefficient of its value alone. -/
lemma repJet_covDerivU (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (U : JetGaugeGroupI) (φ) :
    repJet U (h.covDerivU i l φ) =
      h.covDerivU i l (IsGaugeField.repDualCoeff (UpSinglet.repJetGaugeGroupI) U⁻¹ 0 φ) := by
  have h1 := h.transformsIn_covDerivU i n l U φ 0
  simp only [Multiset.antidiagonal_zero, Multiset.map_singleton,
    Multiset.sum_singleton] at h1
  exact h1

include h in
/-- **The covariant derivatives of the conjugate up-type quarks transform under just the global
  gauge group**: the whole gauge jet acts through the base-point dual representation
  coefficient of its value alone. -/
lemma repJet_covDerivBarU (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (U : JetGaugeGroupI) (φ) :
    repJet U (h.covDerivBarU i l φ) =
      h.covDerivBarU i l (IsGaugeField.repDualCoeff (repConj UpSinglet.repJetGaugeGroupI) U⁻¹ 0 φ) := by
  have h1 := h.transformsIn_covDerivBarU i n l U φ 0
  simp only [Multiset.antidiagonal_zero, Multiset.map_singleton,
    Multiset.sum_singleton] at h1
  exact h1

include h in
/-- **The covariant derivatives of the quark doublets transform under just the global
  gauge group**: the whole gauge jet acts through the base-point dual representation
  coefficient of its value alone. -/
lemma repJet_covDerivQ (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (U : JetGaugeGroupI) (φ) :
    repJet U (h.covDerivQ i l φ) =
      h.covDerivQ i l (IsGaugeField.repDualCoeff (QuarkDoublet.repJetGaugeGroupI) U⁻¹ 0 φ) := by
  have h1 := h.transformsIn_covDerivQ i n l U φ 0
  simp only [Multiset.antidiagonal_zero, Multiset.map_singleton,
    Multiset.sum_singleton] at h1
  exact h1

include h in
/-- **The covariant derivatives of the conjugate quark doublets transform under just the global
  gauge group**: the whole gauge jet acts through the base-point dual representation
  coefficient of its value alone. -/
lemma repJet_covDerivBarQ (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (U : JetGaugeGroupI) (φ) :
    repJet U (h.covDerivBarQ i l φ) =
      h.covDerivBarQ i l (IsGaugeField.repDualCoeff (repConj QuarkDoublet.repJetGaugeGroupI) U⁻¹ 0 φ) := by
  have h1 := h.transformsIn_covDerivBarQ i n l U φ 0
  simp only [Multiset.antidiagonal_zero, Multiset.map_singleton,
    Multiset.sum_singleton] at h1
  exact h1

include h in
/-- **The covariant derivatives of the lepton doublets transform under just the global
  gauge group**: the whole gauge jet acts through the base-point dual representation
  coefficient of its value alone. -/
lemma repJet_covDerivL (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (U : JetGaugeGroupI) (φ) :
    repJet U (h.covDerivL i l φ) =
      h.covDerivL i l (IsGaugeField.repDualCoeff (LeptonDoublet.repJetGaugeGroupI) U⁻¹ 0 φ) := by
  have h1 := h.transformsIn_covDerivL i n l U φ 0
  simp only [Multiset.antidiagonal_zero, Multiset.map_singleton,
    Multiset.sum_singleton] at h1
  exact h1

include h in
/-- **The covariant derivatives of the conjugate lepton doublets transform under just the global
  gauge group**: the whole gauge jet acts through the base-point dual representation
  coefficient of its value alone. -/
lemma repJet_covDerivBarL (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (U : JetGaugeGroupI) (φ) :
    repJet U (h.covDerivBarL i l φ) =
      h.covDerivBarL i l (IsGaugeField.repDualCoeff (repConj LeptonDoublet.repJetGaugeGroupI) U⁻¹ 0 φ) := by
  have h1 := h.transformsIn_covDerivBarL i n l U φ 0
  simp only [Multiset.antidiagonal_zero, Multiset.map_singleton,
    Multiset.sum_singleton] at h1
  exact h1

include h in
/-- **The covariant derivatives of the lepton singlets transform under just the global
  gauge group**: the whole gauge jet acts through the base-point dual representation
  coefficient of its value alone. -/
lemma repJet_covDerivE (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (U : JetGaugeGroupI) (φ) :
    repJet U (h.covDerivE i l φ) =
      h.covDerivE i l (IsGaugeField.repDualCoeff (LeptonSinglet.repJetGaugeGroupI) U⁻¹ 0 φ) := by
  have h1 := h.transformsIn_covDerivE i n l U φ 0
  simp only [Multiset.antidiagonal_zero, Multiset.map_singleton,
    Multiset.sum_singleton] at h1
  exact h1

include h in
/-- **The covariant derivatives of the conjugate lepton singlets transform under just the global
  gauge group**: the whole gauge jet acts through the base-point dual representation
  coefficient of its value alone. -/
lemma repJet_covDerivBarE (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (U : JetGaugeGroupI) (φ) :
    repJet U (h.covDerivBarE i l φ) =
      h.covDerivBarE i l (IsGaugeField.repDualCoeff (repConj LeptonSinglet.repJetGaugeGroupI) U⁻¹ 0 φ) := by
  have h1 := h.transformsIn_covDerivBarE i n l U φ 0
  simp only [Multiset.antidiagonal_zero, Multiset.map_singleton,
    Multiset.sum_singleton] at h1
  exact h1

/-!

## F. Pure gauge jets fix the matter covariant derivatives

-/

include h in
/-- Pure gauge jets act trivially on the covariant derivatives of the
  Higgs field: together with `repJet_covDerivH`, the
  tower transforms under just the global gauge group. -/
lemma repJet_covDerivH_of_mem_truncationKer_zero {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (U : JetGaugeGroupI.truncationKer 0) (φ) :
    repJet U.1 (h.covDerivH l φ) = h.covDerivH l φ :=
  (h.transformsIn_covDerivH n l).repGauge_eq_of_mem_truncationKer_zero
    (fun hW => HiggsVec.repCoeff_zero_of_eval_eq_one hW) U φ

include h in
/-- Pure gauge jets act trivially on the covariant derivatives of the
  conjugate Higgs field: together with `repJet_covDerivBarH`, the
  tower transforms under just the global gauge group. -/
lemma repJet_covDerivBarH_of_mem_truncationKer_zero {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (U : JetGaugeGroupI.truncationKer 0) (φ) :
    repJet U.1 (h.covDerivBarH l φ) = h.covDerivBarH l φ :=
  (h.transformsIn_covDerivBarH n l).repGauge_eq_of_mem_truncationKer_zero
    (fun hW => GaugeAlgebra.repCoeff_repConj_zero_eq_id (HiggsVec.repCoeff_zero_of_eval_eq_one hW)) U φ

include h in
/-- Pure gauge jets act trivially on the covariant derivatives of the
  DownSinglet fields: together with `repJet_covDerivD`, the
  tower transforms under just the global gauge group. -/
lemma repJet_covDerivD_of_mem_truncationKer_zero (i : Fin 3) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (U : JetGaugeGroupI.truncationKer 0) (φ) :
    repJet U.1 (h.covDerivD i l φ) = h.covDerivD i l φ :=
  (h.transformsIn_covDerivD i n l).repGauge_eq_of_mem_truncationKer_zero
    (fun hW => DownSinglet.repCoeff_zero_of_eval_eq_one hW) U φ

include h in
/-- Pure gauge jets act trivially on the covariant derivatives of the
  conjugate DownSinglet fields: together with `repJet_covDerivBarD`, the
  tower transforms under just the global gauge group. -/
lemma repJet_covDerivBarD_of_mem_truncationKer_zero (i : Fin 3) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (U : JetGaugeGroupI.truncationKer 0) (φ) :
    repJet U.1 (h.covDerivBarD i l φ) = h.covDerivBarD i l φ :=
  (h.transformsIn_covDerivBarD i n l).repGauge_eq_of_mem_truncationKer_zero
    (fun hW => GaugeAlgebra.repCoeff_repConj_zero_eq_id (DownSinglet.repCoeff_zero_of_eval_eq_one hW)) U φ

include h in
/-- Pure gauge jets act trivially on the covariant derivatives of the
  UpSinglet fields: together with `repJet_covDerivU`, the
  tower transforms under just the global gauge group. -/
lemma repJet_covDerivU_of_mem_truncationKer_zero (i : Fin 3) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (U : JetGaugeGroupI.truncationKer 0) (φ) :
    repJet U.1 (h.covDerivU i l φ) = h.covDerivU i l φ :=
  (h.transformsIn_covDerivU i n l).repGauge_eq_of_mem_truncationKer_zero
    (fun hW => UpSinglet.repCoeff_zero_of_eval_eq_one hW) U φ

include h in
/-- Pure gauge jets act trivially on the covariant derivatives of the
  conjugate UpSinglet fields: together with `repJet_covDerivBarU`, the
  tower transforms under just the global gauge group. -/
lemma repJet_covDerivBarU_of_mem_truncationKer_zero (i : Fin 3) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (U : JetGaugeGroupI.truncationKer 0) (φ) :
    repJet U.1 (h.covDerivBarU i l φ) = h.covDerivBarU i l φ :=
  (h.transformsIn_covDerivBarU i n l).repGauge_eq_of_mem_truncationKer_zero
    (fun hW => GaugeAlgebra.repCoeff_repConj_zero_eq_id (UpSinglet.repCoeff_zero_of_eval_eq_one hW)) U φ

include h in
/-- Pure gauge jets act trivially on the covariant derivatives of the
  QuarkDoublet fields: together with `repJet_covDerivQ`, the
  tower transforms under just the global gauge group. -/
lemma repJet_covDerivQ_of_mem_truncationKer_zero (i : Fin 3) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (U : JetGaugeGroupI.truncationKer 0) (φ) :
    repJet U.1 (h.covDerivQ i l φ) = h.covDerivQ i l φ :=
  (h.transformsIn_covDerivQ i n l).repGauge_eq_of_mem_truncationKer_zero
    (fun hW => QuarkDoublet.repCoeff_zero_of_eval_eq_one hW) U φ

include h in
/-- Pure gauge jets act trivially on the covariant derivatives of the
  conjugate QuarkDoublet fields: together with `repJet_covDerivBarQ`, the
  tower transforms under just the global gauge group. -/
lemma repJet_covDerivBarQ_of_mem_truncationKer_zero (i : Fin 3) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (U : JetGaugeGroupI.truncationKer 0) (φ) :
    repJet U.1 (h.covDerivBarQ i l φ) = h.covDerivBarQ i l φ :=
  (h.transformsIn_covDerivBarQ i n l).repGauge_eq_of_mem_truncationKer_zero
    (fun hW => GaugeAlgebra.repCoeff_repConj_zero_eq_id (QuarkDoublet.repCoeff_zero_of_eval_eq_one hW)) U φ

include h in
/-- Pure gauge jets act trivially on the covariant derivatives of the
  LeptonDoublet fields: together with `repJet_covDerivL`, the
  tower transforms under just the global gauge group. -/
lemma repJet_covDerivL_of_mem_truncationKer_zero (i : Fin 3) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (U : JetGaugeGroupI.truncationKer 0) (φ) :
    repJet U.1 (h.covDerivL i l φ) = h.covDerivL i l φ :=
  (h.transformsIn_covDerivL i n l).repGauge_eq_of_mem_truncationKer_zero
    (fun hW => LeptonDoublet.repCoeff_zero_of_eval_eq_one hW) U φ

include h in
/-- Pure gauge jets act trivially on the covariant derivatives of the
  conjugate LeptonDoublet fields: together with `repJet_covDerivBarL`, the
  tower transforms under just the global gauge group. -/
lemma repJet_covDerivBarL_of_mem_truncationKer_zero (i : Fin 3) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (U : JetGaugeGroupI.truncationKer 0) (φ) :
    repJet U.1 (h.covDerivBarL i l φ) = h.covDerivBarL i l φ :=
  (h.transformsIn_covDerivBarL i n l).repGauge_eq_of_mem_truncationKer_zero
    (fun hW => GaugeAlgebra.repCoeff_repConj_zero_eq_id (LeptonDoublet.repCoeff_zero_of_eval_eq_one hW)) U φ

include h in
/-- Pure gauge jets act trivially on the covariant derivatives of the
  LeptonSinglet fields: together with `repJet_covDerivE`, the
  tower transforms under just the global gauge group. -/
lemma repJet_covDerivE_of_mem_truncationKer_zero (i : Fin 3) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (U : JetGaugeGroupI.truncationKer 0) (φ) :
    repJet U.1 (h.covDerivE i l φ) = h.covDerivE i l φ :=
  (h.transformsIn_covDerivE i n l).repGauge_eq_of_mem_truncationKer_zero
    (fun hW => LeptonSinglet.repCoeff_zero_of_eval_eq_one hW) U φ

include h in
/-- Pure gauge jets act trivially on the covariant derivatives of the
  conjugate LeptonSinglet fields: together with `repJet_covDerivBarE`, the
  tower transforms under just the global gauge group. -/
lemma repJet_covDerivBarE_of_mem_truncationKer_zero (i : Fin 3) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (U : JetGaugeGroupI.truncationKer 0) (φ) :
    repJet U.1 (h.covDerivBarE i l φ) = h.covDerivBarE i l φ :=
  (h.transformsIn_covDerivBarE i n l).repGauge_eq_of_mem_truncationKer_zero
    (fun hW => GaugeAlgebra.repCoeff_repConj_zero_eq_id (LeptonSinglet.repCoeff_zero_of_eval_eq_one hW)) U φ

/-!

## G. The classification of gauge invariants

-/

include h in
set_option maxHeartbeats 1000000 in
/-- **The classification of gauge invariants of the Standard Model field algebra**:
  a `repJet`-invariant element of the field algebra is a polynomial in the covariant
  derivatives of the field strength and the covariant derivatives of the matter
  fields. Gauge invariance eliminates the bare gauge-field symbols; only the covariant
  objects — all of which transform under just the global gauge group — remain. -/
theorem invariant_mem_adjoin_covDeriv {x : B}
    (hx : x ∈ h.fieldAlgebra)
    (hinv : ∀ U : JetGaugeGroupI, repJet U x = x) :
    x ∈ Algebra.adjoin ℂ
      ((⋃ (l : List (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3),
          Set.range (h.covDerivFieldStrength l μ ν)) ∪
        (⋃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
          Set.range (h.covDerivH l) ∪ Set.range (h.covDerivBarH l)) ∪
        (⋃ (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
          Set.range (h.covDerivD i l) ∪ Set.range (h.covDerivBarD i l) ∪
          Set.range (h.covDerivU i l) ∪ Set.range (h.covDerivBarU i l) ∪
          Set.range (h.covDerivQ i l) ∪ Set.range (h.covDerivBarQ i l) ∪
          Set.range (h.covDerivL i l) ∪ Set.range (h.covDerivBarL i l) ∪
          Set.range (h.covDerivE i l) ∪ Set.range (h.covDerivBarE i l))) := by
  set S : Set B :=
    (⋃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
      Set.range (h.covDerivH l) ∪ Set.range (h.covDerivBarH l)) ∪
    (⋃ (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
      Set.range (h.covDerivD i l) ∪ Set.range (h.covDerivBarD i l) ∪
      Set.range (h.covDerivU i l) ∪ Set.range (h.covDerivBarU i l) ∪
      Set.range (h.covDerivQ i l) ∪ Set.range (h.covDerivBarQ i l) ∪
      Set.range (h.covDerivL i l) ∪ Set.range (h.covDerivBarL i l) ∪
      Set.range (h.covDerivE i l) ∪ Set.range (h.covDerivBarE i l)) with hSdef
  -- the matter covariant towers commute with the gauge-field symbols
  have hcS : ∀ (p : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
      (ψ : Module.Dual ℝ GaugeAlgebra), ∀ y ∈ S, Commute y (A p μ ψ) := by
    intro p μ ψ y hy
    rw [hSdef] at hy
    rcases hy with hy | hy
    · simp only [Set.mem_iUnion] at hy
      obtain ⟨n, l, hy⟩ := hy
      rcases hy with ⟨φ', rfl⟩ | ⟨φ', rfl⟩
      · refine IsGaugeField.commute_of_mem_adjoin ?_
          (IsGaugeField.covDerivIter_mem_adjoin_symbols
            (HiggsVec.gaugeAlgebraAction) H n l 0 φ')
        rintro x' (⟨s', μ', ψ', rfl⟩ | ⟨s', φ'', rfl⟩)
        · exact h.A_comm_A s' p μ' μ ψ' ψ
        · exact (h.A_comm_H p μ ψ s' φ'').symm
      · refine IsGaugeField.commute_of_mem_adjoin ?_
          (IsGaugeField.covDerivIter_mem_adjoin_symbols
            (GaugeAlgebra.actionConj HiggsVec.gaugeAlgebraAction) barH n l 0 φ')
        rintro x' (⟨s', μ', ψ', rfl⟩ | ⟨s', φ'', rfl⟩)
        · exact h.A_comm_A s' p μ' μ ψ' ψ
        · exact (h.A_comm_barH p μ ψ s' φ'').symm
    · simp only [Set.mem_iUnion] at hy
      obtain ⟨i, n, l, hy⟩ := hy
      rcases hy with (((((((((⟨φ', rfl⟩ | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) |
        ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩)
      · refine IsGaugeField.commute_of_mem_adjoin ?_
          (IsGaugeField.covDerivIter_mem_adjoin_symbols
            (DownSinglet.gaugeAlgebraAction) (d i) n l 0 φ')
        rintro x' (⟨s', μ', ψ', rfl⟩ | ⟨s', φ'', rfl⟩)
        · exact h.A_comm_A s' p μ' μ ψ' ψ
        · exact (h.A_comm_d p μ ψ i s' φ'').symm
      · refine IsGaugeField.commute_of_mem_adjoin ?_
          (IsGaugeField.covDerivIter_mem_adjoin_symbols
            (GaugeAlgebra.actionConj DownSinglet.gaugeAlgebraAction) (bard i) n l 0 φ')
        rintro x' (⟨s', μ', ψ', rfl⟩ | ⟨s', φ'', rfl⟩)
        · exact h.A_comm_A s' p μ' μ ψ' ψ
        · exact (h.A_comm_bard p μ ψ i s' φ'').symm
      · refine IsGaugeField.commute_of_mem_adjoin ?_
          (IsGaugeField.covDerivIter_mem_adjoin_symbols
            (UpSinglet.gaugeAlgebraAction) (u i) n l 0 φ')
        rintro x' (⟨s', μ', ψ', rfl⟩ | ⟨s', φ'', rfl⟩)
        · exact h.A_comm_A s' p μ' μ ψ' ψ
        · exact (h.A_comm_u p μ ψ i s' φ'').symm
      · refine IsGaugeField.commute_of_mem_adjoin ?_
          (IsGaugeField.covDerivIter_mem_adjoin_symbols
            (GaugeAlgebra.actionConj UpSinglet.gaugeAlgebraAction) (baru i) n l 0 φ')
        rintro x' (⟨s', μ', ψ', rfl⟩ | ⟨s', φ'', rfl⟩)
        · exact h.A_comm_A s' p μ' μ ψ' ψ
        · exact (h.A_comm_baru p μ ψ i s' φ'').symm
      · refine IsGaugeField.commute_of_mem_adjoin ?_
          (IsGaugeField.covDerivIter_mem_adjoin_symbols
            (QuarkDoublet.gaugeAlgebraAction) (Q i) n l 0 φ')
        rintro x' (⟨s', μ', ψ', rfl⟩ | ⟨s', φ'', rfl⟩)
        · exact h.A_comm_A s' p μ' μ ψ' ψ
        · exact (h.A_comm_Q p μ ψ i s' φ'').symm
      · refine IsGaugeField.commute_of_mem_adjoin ?_
          (IsGaugeField.covDerivIter_mem_adjoin_symbols
            (GaugeAlgebra.actionConj QuarkDoublet.gaugeAlgebraAction) (barQ i) n l 0 φ')
        rintro x' (⟨s', μ', ψ', rfl⟩ | ⟨s', φ'', rfl⟩)
        · exact h.A_comm_A s' p μ' μ ψ' ψ
        · exact (h.A_comm_barQ p μ ψ i s' φ'').symm
      · refine IsGaugeField.commute_of_mem_adjoin ?_
          (IsGaugeField.covDerivIter_mem_adjoin_symbols
            (LeptonDoublet.gaugeAlgebraAction) (L i) n l 0 φ')
        rintro x' (⟨s', μ', ψ', rfl⟩ | ⟨s', φ'', rfl⟩)
        · exact h.A_comm_A s' p μ' μ ψ' ψ
        · exact (h.A_comm_L p μ ψ i s' φ'').symm
      · refine IsGaugeField.commute_of_mem_adjoin ?_
          (IsGaugeField.covDerivIter_mem_adjoin_symbols
            (GaugeAlgebra.actionConj LeptonDoublet.gaugeAlgebraAction) (barL i) n l 0 φ')
        rintro x' (⟨s', μ', ψ', rfl⟩ | ⟨s', φ'', rfl⟩)
        · exact h.A_comm_A s' p μ' μ ψ' ψ
        · exact (h.A_comm_barL p μ ψ i s' φ'').symm
      · refine IsGaugeField.commute_of_mem_adjoin ?_
          (IsGaugeField.covDerivIter_mem_adjoin_symbols
            (LeptonSinglet.gaugeAlgebraAction) (e i) n l 0 φ')
        rintro x' (⟨s', μ', ψ', rfl⟩ | ⟨s', φ'', rfl⟩)
        · exact h.A_comm_A s' p μ' μ ψ' ψ
        · exact (h.A_comm_e p μ ψ i s' φ'').symm
      · refine IsGaugeField.commute_of_mem_adjoin ?_
          (IsGaugeField.covDerivIter_mem_adjoin_symbols
            (GaugeAlgebra.actionConj LeptonSinglet.gaugeAlgebraAction) (bare i) n l 0 φ')
        rintro x' (⟨s', μ', ψ', rfl⟩ | ⟨s', φ'', rfl⟩)
        · exact h.A_comm_A s' p μ' μ ψ' ψ
        · exact (h.A_comm_bare p μ ψ i s' φ'').symm
  -- the matter covariant towers are fixed by pure gauge jets
  have hS : ∀ y ∈ S, ∀ U : JetGaugeGroupI.truncationKer 0, repJet U.1 y = y := by
    intro y hy U
    rw [hSdef] at hy
    rcases hy with hy | hy
    · simp only [Set.mem_iUnion] at hy
      obtain ⟨n, l, hy⟩ := hy
      rcases hy with ⟨φ', rfl⟩ | ⟨φ', rfl⟩
      · exact h.repJet_covDerivH_of_mem_truncationKer_zero l U φ'
      · exact h.repJet_covDerivBarH_of_mem_truncationKer_zero l U φ'
    · simp only [Set.mem_iUnion] at hy
      obtain ⟨i, n, l, hy⟩ := hy
      rcases hy with (((((((((⟨φ', rfl⟩ | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) |
        ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩) | ⟨φ', rfl⟩)
      · exact h.repJet_covDerivD_of_mem_truncationKer_zero i l U φ'
      · exact h.repJet_covDerivBarD_of_mem_truncationKer_zero i l U φ'
      · exact h.repJet_covDerivU_of_mem_truncationKer_zero i l U φ'
      · exact h.repJet_covDerivBarU_of_mem_truncationKer_zero i l U φ'
      · exact h.repJet_covDerivQ_of_mem_truncationKer_zero i l U φ'
      · exact h.repJet_covDerivBarQ_of_mem_truncationKer_zero i l U φ'
      · exact h.repJet_covDerivL_of_mem_truncationKer_zero i l U φ'
      · exact h.repJet_covDerivBarL_of_mem_truncationKer_zero i l U φ'
      · exact h.repJet_covDerivE_of_mem_truncationKer_zero i l U φ'
      · exact h.repJet_covDerivBarE_of_mem_truncationKer_zero i l U φ'
  -- the invariant lies in the algebra of gauge symbols over the matter towers
  have hx' : x ∈ Algebra.adjoin ℂ
      ({b : B | ∃ (p : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
        (ψ : Module.Dual ℝ GaugeAlgebra), b = A p μ ψ} ∪ S) := by
    rw [h.fieldAlgebra_eq_covDeriv] at hx
    refine SetLike.le_def.mp (Algebra.adjoin_mono ?_) hx
    rintro b ((hA | hHT) | hFT)
    · simp only [Set.mem_iUnion, Set.mem_range] at hA
      obtain ⟨s, μ, ψ, hψ⟩ := hA
      exact Or.inl ⟨s, μ, ψ, hψ.symm⟩
    · exact Or.inr (Or.inl hHT)
    · exact Or.inr (Or.inr hFT)
  -- the abstract classification
  have hres := IsGaugeField.invariant_mem_adjoin_fieldStrength h.repJet_A
    (fun p q μ ν φ ψ => h.A_comm_A p q μ ν φ ψ) S hcS hS hx' hinv
  refine SetLike.le_def.mp (Algebra.adjoin_mono ?_) hres
  rintro b (⟨l, ν, lam, φ', rfl⟩ | hbS)
  · exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨l, Set.mem_iUnion.mpr ⟨ν,
      Set.mem_iUnion.mpr ⟨lam, ⟨φ', rfl⟩⟩⟩⟩))
  · rw [hSdef] at hbS
    rcases hbS with h1 | h2
    · exact Or.inl (Or.inr h1)
    · exact Or.inr h2


TODO (lines := 2029-2030) "Prove the Lorentz transformation laws of the covariant
  towers, the last thing missing from the construction of `IsCovStandardModel` in
  CovStandardModel.lean: with them, `isCovStandardModel_of_lorentzCovDeriv` loses its
  thirteen hypotheses. What is needed is that `IsGaugeField.covDerivIter` and
  `IsGaugeField.iteratedCovDerivAdjoint` satisfy `IsLorentzCovDerivTransforms`, given
  the Lorentz laws of the bare symbols — the `repLorentz_*` fields above and
  `lorentz_apply` of `IsGaugeField`. Three ingredients. First, the Lorentz mixing of the
  derivative slots should be written as an operator on multiset-indexed families defined
  by recursion on the multiset — peel a direction `a`, replace it by every direction `b`
  weighted by the Lorentz matrix entry, mix the rest — rather than as a sum over ordered
  tuples; peeling two directions commutes, so the recursion is well defined on a
  multiset, and it agrees with the tuple form of `IsLorentzDerivTransforms`. Second,
  that operator is a morphism for the Leibniz convolution over `Multiset.antidiagonal`,
  by induction on the multiset using `Multiset.antidiagonal_cons`; this is what carries
  the law through `actionFamConv` and `bracketFamConv`, both of which are, after
  expansion in a basis, scalar combinations of convolutions of products in the algebra.
  Third — and this is not yet recorded anywhere — the gauge-algebra action on each value
  space must commute with the Lorentz action on it, since the correction term of a
  covariant derivative acts on the value index by `act` while the Lorentz group acts on
  it by the species representation. That is true because the two act on different tensor
  factors, but it needs a lemma for each of the ten fermion species (for the Higgs it is
  trivial, the Lorentz representation being trivial)."

end IsStandardModel

end StandardModel
