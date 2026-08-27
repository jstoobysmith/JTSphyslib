/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.HiggsBoson.Basic
public import Physlib.Relativity.IsLorentzDeriv
public import Physlib.Particles.StandardModel.HiggsBoson.AlgebraValued.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.Jet.Basic
public import Physlib.Relativity.LorentzGroup.Boosts.WeightGrading
public import Physlib.Particles.StandardModel.GaugeGroup.SU2PermDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.GaugeWeightDecomposition
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.JetDeriv
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.LorentzAction
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.GaugeAction
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.MassDim
public import Physlib.Particles.StandardModel.Fermions.DownSinglet
public import Physlib.Particles.StandardModel.Fermions.UpSinglet
public import Physlib.Particles.StandardModel.Fermions.LeptonSinglet.Basic
public import Physlib.Particles.StandardModel.Fermions.QuarkDoublet
public import Physlib.Particles.StandardModel.Fermions.LeptonDoublet
public import Physlib.Particles.StandardModel.GaugeBosons.AlgebraValued.Basic
public import Physlib.Particles.StandardModel.Matter.JetComponentSpace.Basic
public import Physlib.Particles.StandardModel.Matter.JetComponentSpace.CovariantDeriv
public import Physlib.Particles.StandardModel.HiggsBoson.JetAlgebra.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Analysis.Normed.Lp.Matrix
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RepresentationTheory.Invariants
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


lemma fieldAlgebra_eq_covDerivD :
    h.fieldAlgebra = Algebra.adjoin ℂ
    ((⋃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3), Set.range (A s μ)) ∪
      (⋃ (s : Multiset (Fin 1 ⊕ Fin 3)), Set.range (H s) ∪ Set.range (barH s)) ∪
      (⋃ (i : Fin 3) (n : ℕ) (l :  Fin n → (Fin 1 ⊕ Fin 3)), Set.range (h.covDerivD i l)) ∪
      (⋃ (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)),
        Set.range (bard i s) ∪
        Set.range (u i s) ∪ Set.range (baru i s) ∪
        Set.range (Q i s) ∪ Set.range (barQ i s) ∪
        Set.range (L i s) ∪ Set.range (barL i s) ∪
        Set.range (e i s) ∪ Set.range (bare i s))) := by
  -- the span lemma, per family
  have hAT : ∀ i : Fin 3,
      Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ DownSinglet),
            b = d i s φ}) =
      Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3))
            (φ : Module.Dual ℂ DownSinglet),
            b = IsGaugeField.covDerivIter A DownSinglet.gaugeAlgebraAction (d i)
              n l 0 φ}) :=
    fun i => IsGaugeField.adjoin_symbols_eq_adjoin_covDerivIter
      DownSinglet.gaugeAlgebraAction (d i)
  -- the down symbols lie in the covariant-tower algebra
  have hdmem : ∀ (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ DownSinglet),
      d i s φ ∈ Algebra.adjoin ℂ
        ((⋃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3), Set.range (A s μ)) ∪
          (⋃ (s : Multiset (Fin 1 ⊕ Fin 3)), Set.range (H s) ∪ Set.range (barH s)) ∪
          (⋃ (i : Fin 3) (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)),
            Set.range (h.covDerivD i l)) ∪
          (⋃ (i : Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)),
            Set.range (bard i s) ∪
            Set.range (u i s) ∪ Set.range (baru i s) ∪
            Set.range (Q i s) ∪ Set.range (barQ i s) ∪
            Set.range (L i s) ∪ Set.range (barL i s) ∪
            Set.range (e i s) ∪ Set.range (bare i s))) := by
    intro i s φ
    have h1 : d i s φ ∈ Algebra.adjoin ℂ
        ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
            (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
          {b : B | ∃ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3))
            (φ : Module.Dual ℂ DownSinglet),
            b = IsGaugeField.covDerivIter A DownSinglet.gaugeAlgebraAction (d i)
              n l 0 φ}) :=
      (hAT i).le (Algebra.subset_adjoin (Or.inr ⟨s, φ, rfl⟩))
    refine SetLike.le_def.mp (Algebra.adjoin_mono ?_) h1
    rintro b (⟨u', μ, ψ, rfl⟩ | ⟨n, l, φ', rfl⟩)
    · exact Or.inl (Or.inl (Or.inl
        (Set.mem_iUnion.mpr ⟨u', Set.mem_iUnion.mpr ⟨μ, ⟨ψ, rfl⟩⟩⟩)))
    · exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨n,
        Set.mem_iUnion.mpr ⟨l, ⟨φ', rfl⟩⟩⟩⟩))
  refine le_antisymm (Algebra.adjoin_le ?_) (Algebra.adjoin_le ?_)
  · rintro b (hAH | hbF)
    · exact Algebra.subset_adjoin (Or.inl (Or.inl hAH))
    · simp only [Set.mem_iUnion] at hbF
      obtain ⟨i, s, hbF⟩ := hbF
      by_cases hd : b ∈ Set.range (d i s)
      · obtain ⟨φ, rfl⟩ := hd
        exact hdmem i s φ
      · refine Algebra.subset_adjoin (Or.inr (Set.mem_iUnion.mpr ⟨i,
          Set.mem_iUnion.mpr ⟨s, ?_⟩⟩))
        simp only [Set.mem_union] at hbF ⊢
        tauto
  · rintro b ((hAH | hT) | hbF)
    · exact Algebra.subset_adjoin (Or.inl hAH)
    · simp only [Set.mem_iUnion, Set.mem_range] at hT
      obtain ⟨i, n, l, φ, rfl⟩ := hT
      have h1 : IsGaugeField.covDerivIter A DownSinglet.gaugeAlgebraAction (d i)
          n l 0 φ ∈ Algebra.adjoin ℂ
            ({b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3)
                (ψ : Module.Dual ℝ GaugeAlgebra), b = A s μ ψ} ∪
              {b : B | ∃ (s : Multiset (Fin 1 ⊕ Fin 3))
                (φ : Module.Dual ℂ DownSinglet), b = d i s φ}) :=
        (hAT i).ge (Algebra.subset_adjoin (Or.inr ⟨n, l, φ, rfl⟩))
      refine SetLike.le_def.mp (Algebra.adjoin_mono ?_) h1
      rintro b (⟨u', μ, ψ, rfl⟩ | ⟨s', φ', rfl⟩)
      · exact Or.inl (Or.inl
          (Set.mem_iUnion.mpr ⟨u', Set.mem_iUnion.mpr ⟨μ, ⟨ψ, rfl⟩⟩⟩))
      · refine Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨s', ?_⟩⟩)
        have hmem : d i s' φ' ∈ Set.range (d i s') := ⟨φ', rfl⟩
        simp only [Set.mem_union]
        tauto
    · simp only [Set.mem_iUnion] at hbF
      obtain ⟨i, s, hbF⟩ := hbF
      refine Algebra.subset_adjoin (Or.inr (Set.mem_iUnion.mpr ⟨i,
        Set.mem_iUnion.mpr ⟨s, ?_⟩⟩))
      simp only [Set.mem_union] at hbF ⊢
      tauto
end IsStandardModel

end StandardModel
