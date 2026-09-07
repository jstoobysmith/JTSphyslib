/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module
public import Physlib.Particles.StandardModel.AlgebraRealization.CovStandardModel
/-!
# The covariant jet algebra

## i. Overview

Placeholder.

## ii. Key results

Placeholder.

## iii. Table of contents

- A. The covariant subalgebra is the covariant field algebra

-/

@[expose] public section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
set_option synthInstance.maxSize 2048
set_option maxRecDepth 8000

namespace StandardModel

open TensorProduct Matrix MatrixGroups Lorentz

namespace AlgebraRealization

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repJet : Representation ℂ JetGaugeGroupI B}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : AlgebraRealization B repJet repLorentz massWeightPoly)

/-!

## A. The covariant subalgebra is the covariant field algebra

-/

/-- The covariant field algebra of `CovFieldAlgebra.Basic` and the covariant subalgebra of
  `CovStandardModel` are the same subalgebra: their generating sets are the two indexings
  of the covariant towers, which agree. -/
lemma covFieldAlgebra_eq_covAlgebra : h.covFieldAlgebra = h.covAlgebra := by
  rw [covAlgebra, covGenerators_eq_covGeneratorsList]
  rfl

/-!

### A.1. The covariant towers lie in the covariant subalgebra

-/

/-- The field-strength tower lies in the covariant subalgebra. -/
lemma covF_mem_covAlgebra {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ GaugeAlgebra) : h.covF l μ ν φ ∈ h.covAlgebra :=
  Algebra.subset_adjoin <| Or.inl <| Or.inl <| Set.mem_iUnion_of_mem n <|
    Set.mem_iUnion_of_mem l <| Set.mem_iUnion_of_mem μ <| Set.mem_iUnion_of_mem ν <| ⟨φ, rfl⟩

/-- The Higgs tower lies in the covariant subalgebra. -/
lemma covDerivH_mem_covAlgebra {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ HiggsVec) : h.covDerivH l φ ∈ h.covAlgebra :=
  Algebra.subset_adjoin <| Or.inl <| Or.inr <| Set.mem_iUnion_of_mem n <|
    Set.mem_iUnion_of_mem l <| Or.inl ⟨φ, rfl⟩

/-- The conjugate Higgs tower lies in the covariant subalgebra. -/
lemma covDerivBarH_mem_covAlgebra {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule HiggsVec)) : h.covDerivBarH l φ ∈ h.covAlgebra :=
  Algebra.subset_adjoin <| Or.inl <| Or.inr <| Set.mem_iUnion_of_mem n <|
    Set.mem_iUnion_of_mem l <| Or.inr ⟨φ, rfl⟩

/-- The down-type quark tower lies in the covariant subalgebra. -/
lemma covDerivD_mem_covAlgebra (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ DownSinglet) : h.covDerivD i l φ ∈ h.covAlgebra :=
  Algebra.subset_adjoin <| Or.inr <| Set.mem_iUnion_of_mem i <| Set.mem_iUnion_of_mem n <|
    Set.mem_iUnion_of_mem l <| Or.inl <| Or.inl <| Or.inl <| Or.inl <| Or.inl <| Or.inl <|
      Or.inl <| Or.inl <| Or.inl <| ⟨φ, rfl⟩

/-- The conjugate down-type quark tower lies in the covariant subalgebra. -/
lemma covDerivBarD_mem_covAlgebra (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule DownSinglet)) : h.covDerivBarD i l φ ∈ h.covAlgebra :=
  Algebra.subset_adjoin <| Or.inr <| Set.mem_iUnion_of_mem i <| Set.mem_iUnion_of_mem n <|
    Set.mem_iUnion_of_mem l <| Or.inl <| Or.inl <| Or.inl <| Or.inl <| Or.inl <| Or.inl <|
      Or.inl <| Or.inl <| Or.inr <| ⟨φ, rfl⟩

/-- The up-type quark tower lies in the covariant subalgebra. -/
lemma covDerivU_mem_covAlgebra (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ UpSinglet) : h.covDerivU i l φ ∈ h.covAlgebra :=
  Algebra.subset_adjoin <| Or.inr <| Set.mem_iUnion_of_mem i <| Set.mem_iUnion_of_mem n <|
    Set.mem_iUnion_of_mem l <| Or.inl <| Or.inl <| Or.inl <| Or.inl <| Or.inl <| Or.inl <|
      Or.inl <| Or.inr <| ⟨φ, rfl⟩

/-- The conjugate up-type quark tower lies in the covariant subalgebra. -/
lemma covDerivBarU_mem_covAlgebra (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule UpSinglet)) : h.covDerivBarU i l φ ∈ h.covAlgebra :=
  Algebra.subset_adjoin <| Or.inr <| Set.mem_iUnion_of_mem i <| Set.mem_iUnion_of_mem n <|
    Set.mem_iUnion_of_mem l <| Or.inl <| Or.inl <| Or.inl <| Or.inl <| Or.inl <| Or.inl <|
      Or.inr <| ⟨φ, rfl⟩

/-- The quark doublet tower lies in the covariant subalgebra. -/
lemma covDerivQ_mem_covAlgebra (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ QuarkDoublet) : h.covDerivQ i l φ ∈ h.covAlgebra :=
  Algebra.subset_adjoin <| Or.inr <| Set.mem_iUnion_of_mem i <| Set.mem_iUnion_of_mem n <|
    Set.mem_iUnion_of_mem l <| Or.inl <| Or.inl <| Or.inl <| Or.inl <| Or.inl <| Or.inr <|
      ⟨φ, rfl⟩

/-- The conjugate quark doublet tower lies in the covariant subalgebra. -/
lemma covDerivBarQ_mem_covAlgebra (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule QuarkDoublet)) : h.covDerivBarQ i l φ ∈ h.covAlgebra :=
  Algebra.subset_adjoin <| Or.inr <| Set.mem_iUnion_of_mem i <| Set.mem_iUnion_of_mem n <|
    Set.mem_iUnion_of_mem l <| Or.inl <| Or.inl <| Or.inl <| Or.inl <| Or.inr <| ⟨φ, rfl⟩

/-- The lepton doublet tower lies in the covariant subalgebra. -/
lemma covDerivL_mem_covAlgebra (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ LeptonDoublet) : h.covDerivL i l φ ∈ h.covAlgebra :=
  Algebra.subset_adjoin <| Or.inr <| Set.mem_iUnion_of_mem i <| Set.mem_iUnion_of_mem n <|
    Set.mem_iUnion_of_mem l <| Or.inl <| Or.inl <| Or.inl <| Or.inr <| ⟨φ, rfl⟩

/-- The conjugate lepton doublet tower lies in the covariant subalgebra. -/
lemma covDerivBarL_mem_covAlgebra (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule LeptonDoublet)) : h.covDerivBarL i l φ ∈ h.covAlgebra :=
  Algebra.subset_adjoin <| Or.inr <| Set.mem_iUnion_of_mem i <| Set.mem_iUnion_of_mem n <|
    Set.mem_iUnion_of_mem l <| Or.inl <| Or.inl <| Or.inr <| ⟨φ, rfl⟩

/-- The charged-lepton singlet tower lies in the covariant subalgebra. -/
lemma covDerivE_mem_covAlgebra (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ LeptonSinglet) : h.covDerivE i l φ ∈ h.covAlgebra :=
  Algebra.subset_adjoin <| Or.inr <| Set.mem_iUnion_of_mem i <| Set.mem_iUnion_of_mem n <|
    Set.mem_iUnion_of_mem l <| Or.inl <| Or.inr <| ⟨φ, rfl⟩

/-- The conjugate charged-lepton singlet tower lies in the covariant subalgebra. -/
lemma covDerivBarE_mem_covAlgebra (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule LeptonSinglet)) : h.covDerivBarE i l φ ∈ h.covAlgebra :=
  Algebra.subset_adjoin <| Or.inr <| Set.mem_iUnion_of_mem i <| Set.mem_iUnion_of_mem n <|
    Set.mem_iUnion_of_mem l <| Or.inr <| ⟨φ, rfl⟩


/-!

## B. The covariant subalgebra is closed under the actions

The global gauge action, the Lorentz action and the mass-weight polynomial all carry a
covariant tower to a combination of covariant towers, and each is multiplicative, so each
carries the whole covariant subalgebra into itself. Those three closure facts are what let
the covariant subalgebra be regarded as an algebra with a gauge action, a Lorentz action
and a mass-weight grading of its own.

-/

include h in
/-- A property that holds of every covariant tower holds of every covariant generator:
  the case analysis of the generating set, done once. -/
lemma covGenerators_induction {P : B → Prop}
    (hF : ∀ {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3)
      (φ : Module.Dual ℝ GaugeAlgebra), P (h.covF l μ ν φ))
    (hH : ∀ {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ HiggsVec),
      P (h.covDerivH l φ))
    (hBarH : ∀ {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule HiggsVec)),
      P (h.covDerivBarH l φ))
    (hD : ∀ (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ DownSinglet), P (h.covDerivD i l φ))
    (hBarD : ∀ (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule DownSinglet)), P (h.covDerivBarD i l φ))
    (hU : ∀ (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ UpSinglet), P (h.covDerivU i l φ))
    (hBarU : ∀ (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule UpSinglet)), P (h.covDerivBarU i l φ))
    (hQ : ∀ (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ QuarkDoublet), P (h.covDerivQ i l φ))
    (hBarQ : ∀ (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule QuarkDoublet)), P (h.covDerivBarQ i l φ))
    (hL : ∀ (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ LeptonDoublet), P (h.covDerivL i l φ))
    (hBarL : ∀ (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule LeptonDoublet)), P (h.covDerivBarL i l φ))
    (hE : ∀ (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ LeptonSinglet), P (h.covDerivE i l φ))
    (hBarE : ∀ (i : Fin 3) {n : ℕ} (l : Fin n → (Fin 1 ⊕ Fin 3))
      (φ : Module.Dual ℂ (ConjModule LeptonSinglet)), P (h.covDerivBarE i l φ))
    : ∀ x ∈ h.covGenerators, P x := by
  rintro x hx
  rw [covGenerators] at hx
  rcases hx with hx | hx
  · rcases hx with hx | hx
    · simp only [Set.mem_iUnion, Set.mem_range] at hx
      obtain ⟨n, l, μ, ν, φ, rfl⟩ := hx
      exact hF l μ ν φ
    · simp only [Set.mem_iUnion] at hx
      obtain ⟨n, l, hx⟩ := hx
      rcases hx with ⟨φ, rfl⟩ | ⟨φ, rfl⟩
      · exact hH l φ
      · exact hBarH l φ
  · simp only [Set.mem_iUnion] at hx
    obtain ⟨i, n, l, hx⟩ := hx
    rcases hx with (((((((((⟨φ, rfl⟩ | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) |
      ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩) | ⟨φ, rfl⟩)
    · exact hD i l φ
    · exact hBarD i l φ
    · exact hU i l φ
    · exact hBarU i l φ
    · exact hQ i l φ
    · exact hBarQ i l φ
    · exact hL i l φ
    · exact hBarL i l φ
    · exact hE i l φ
    · exact hBarE i l φ


include h in
/-- A unital multiplicative endomorphism of the algebra that carries the covariant
  generators into the covariant subalgebra carries the whole subalgebra into itself. -/
lemma mapsTo_covAlgebra {f : B →ₗ[ℂ] B} (hone : f 1 = 1)
    (hmul : ∀ b₁ b₂ : B, f (b₁ * b₂) = f b₁ * f b₂)
    (hgen : ∀ x ∈ h.covGenerators, f x ∈ h.covAlgebra) {x : B} (hx : x ∈ h.covAlgebra) :
    f x ∈ h.covAlgebra := by
  induction hx using Algebra.adjoin_induction with
  | mem b hb => exact hgen b hb
  | algebraMap c =>
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hone]
    exact Subalgebra.smul_mem _ (one_mem _) c
  | add a b _ _ iha ihb => rw [map_add]; exact add_mem iha ihb
  | mul a b _ _ iha ihb => rw [hmul]; exact mul_mem iha ihb

include h in
/-- A Lorentz slot-mixing sum of covariant towers lies in the covariant subalgebra. -/
lemma sum_smul_mem_covAlgebra {n : ℕ} {c : (Fin n → (Fin 1 ⊕ Fin 3)) → ℂ}
    {G : (Fin n → (Fin 1 ⊕ Fin 3)) → B} (hG : ∀ p, G p ∈ h.covAlgebra) :
    ∑ p : Fin n → (Fin 1 ⊕ Fin 3), c p • G p ∈ h.covAlgebra :=
  Subalgebra.sum_mem _ fun p _ => Subalgebra.smul_mem _ (hG p) _

/-!

### B.1. The global gauge action

-/

include h in
/-- The global gauge action fixes the unit of the algebra. -/
lemma repGlobal_one (g : GaugeGroupI) : repGlobal repJet g (1 : B) = 1 := by
  simpa using h.repJet_algebraMap (JetGaugeGroupI.ofConstant g) 1

include h in
/-- The global gauge action preserves the covariant subalgebra: it carries each covariant
  tower to a tower of the same shape at a rotated value index, and it is multiplicative. -/
lemma repGlobal_mem_covAlgebra (g : GaugeGroupI) {x : B} (hx : x ∈ h.covAlgebra) :
    repGlobal repJet g x ∈ h.covAlgebra :=
  h.mapsTo_covAlgebra (h.repGlobal_one g) (h.repJet_A.gauge_mul _)
    (h.covGenerators_induction
    (fun l μ ν φ => by
      rw [h.repGlobal_covF]; exact h.covF_mem_covAlgebra _ _ _ _)
    (fun l φ => by rw [h.repGlobal_covDerivH]; exact h.covDerivH_mem_covAlgebra _ _)
    (fun l φ => by rw [h.repGlobal_covDerivBarH]; exact h.covDerivBarH_mem_covAlgebra _ _)
    (fun i {_n} l φ => by
      rw [h.repGlobal_covDerivD]; exact h.covDerivD_mem_covAlgebra _ _ _)
    (fun i {_n} l φ => by
      rw [h.repGlobal_covDerivBarD]; exact h.covDerivBarD_mem_covAlgebra _ _ _)
    (fun i {_n} l φ => by
      rw [h.repGlobal_covDerivU]; exact h.covDerivU_mem_covAlgebra _ _ _)
    (fun i {_n} l φ => by
      rw [h.repGlobal_covDerivBarU]; exact h.covDerivBarU_mem_covAlgebra _ _ _)
    (fun i {_n} l φ => by
      rw [h.repGlobal_covDerivQ]; exact h.covDerivQ_mem_covAlgebra _ _ _)
    (fun i {_n} l φ => by
      rw [h.repGlobal_covDerivBarQ]; exact h.covDerivBarQ_mem_covAlgebra _ _ _)
    (fun i {_n} l φ => by
      rw [h.repGlobal_covDerivL]; exact h.covDerivL_mem_covAlgebra _ _ _)
    (fun i {_n} l φ => by
      rw [h.repGlobal_covDerivBarL]; exact h.covDerivBarL_mem_covAlgebra _ _ _)
    (fun i {_n} l φ => by
      rw [h.repGlobal_covDerivE]; exact h.covDerivE_mem_covAlgebra _ _ _)
    (fun i {_n} l φ => by
      rw [h.repGlobal_covDerivBarE]; exact h.covDerivBarE_mem_covAlgebra _ _ _)) hx

/-!

### B.2. The Lorentz action

-/

include h in
/-- The Lorentz action fixes the unit of the algebra. -/
lemma repLorentz_one (Λ : SL(2,ℂ)) : repLorentz Λ (1 : B) = 1 := by
  obtain ⟨v, hv⟩ : ∃ v, repLorentz Λ v = 1 :=
    ⟨repLorentz Λ⁻¹ 1, by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one repLorentz,
        Module.End.one_apply]⟩
  have h1 := h.repLorentz_mul Λ v 1
  rw [mul_one, hv, one_mul] at h1
  exact h1.symm

include h in
/-- The Lorentz action preserves the covariant subalgebra: it carries each covariant tower
  to a slot-mixing sum of towers of the same shape, and it is multiplicative. -/
lemma repLorentz_mem_covAlgebra (Λ : SL(2,ℂ)) {x : B} (hx : x ∈ h.covAlgebra) :
    repLorentz Λ x ∈ h.covAlgebra :=
  h.mapsTo_covAlgebra (h.repLorentz_one Λ) (h.repLorentz_mul Λ)
    (h.covGenerators_induction
    (fun l μ ν φ => by
      rw [h.repLorentz_covF]
      exact Subalgebra.sum_mem _ fun p _ => Subalgebra.smul_mem _
        (Subalgebra.sum_mem _ fun a _ => Subalgebra.smul_mem _
          (Subalgebra.sum_mem _ fun b _ => Subalgebra.smul_mem _
            (h.covF_mem_covAlgebra _ _ _ _) _) _) _)
    (fun l φ => by
      rw [h.repLorentz_covDerivH]
      exact h.sum_smul_mem_covAlgebra fun p => h.covDerivH_mem_covAlgebra _ _)
    (fun l φ => by
      rw [h.repLorentz_covDerivBarH]
      exact h.sum_smul_mem_covAlgebra fun p => h.covDerivBarH_mem_covAlgebra _ _)
    (fun i {_n} l φ => by
      rw [h.repLorentz_covDerivD]
      exact h.sum_smul_mem_covAlgebra fun p => h.covDerivD_mem_covAlgebra _ _ _)
    (fun i {_n} l φ => by
      rw [h.repLorentz_covDerivBarD]
      exact h.sum_smul_mem_covAlgebra fun p => h.covDerivBarD_mem_covAlgebra _ _ _)
    (fun i {_n} l φ => by
      rw [h.repLorentz_covDerivU]
      exact h.sum_smul_mem_covAlgebra fun p => h.covDerivU_mem_covAlgebra _ _ _)
    (fun i {_n} l φ => by
      rw [h.repLorentz_covDerivBarU]
      exact h.sum_smul_mem_covAlgebra fun p => h.covDerivBarU_mem_covAlgebra _ _ _)
    (fun i {_n} l φ => by
      rw [h.repLorentz_covDerivQ]
      exact h.sum_smul_mem_covAlgebra fun p => h.covDerivQ_mem_covAlgebra _ _ _)
    (fun i {_n} l φ => by
      rw [h.repLorentz_covDerivBarQ]
      exact h.sum_smul_mem_covAlgebra fun p => h.covDerivBarQ_mem_covAlgebra _ _ _)
    (fun i {_n} l φ => by
      rw [h.repLorentz_covDerivL]
      exact h.sum_smul_mem_covAlgebra fun p => h.covDerivL_mem_covAlgebra _ _ _)
    (fun i {_n} l φ => by
      rw [h.repLorentz_covDerivBarL]
      exact h.sum_smul_mem_covAlgebra fun p => h.covDerivBarL_mem_covAlgebra _ _ _)
    (fun i {_n} l φ => by
      rw [h.repLorentz_covDerivE]
      exact h.sum_smul_mem_covAlgebra fun p => h.covDerivE_mem_covAlgebra _ _ _)
    (fun i {_n} l φ => by
      rw [h.repLorentz_covDerivBarE]
      exact h.sum_smul_mem_covAlgebra fun p => h.covDerivBarE_mem_covAlgebra _ _ _)) hx

/-!

### B.3. The mass-weight polynomial

-/

include h in
/-- A monomial with a coefficient in the covariant subalgebra is the image of a monomial
  over the covariant subalgebra. -/
private lemma monomial_mem_range {n : ℕ} {y : B} (hy : y ∈ h.covAlgebra) :
    Polynomial.monomial n y ∈ (Polynomial.mapAlgHom h.covAlgebra.val).range :=
  ⟨Polynomial.monomial n ⟨y, hy⟩, by simp⟩

include h in
/-- The mass-weight polynomial carries the covariant subalgebra into the polynomials with
  coefficients in it: each covariant tower is an eigenvector whose eigenvector is the tower
  itself, and the mass-weight polynomial is an algebra map. -/
lemma massWeightPoly_mem_range_mapAlgHom {x : B} (hx : x ∈ h.covAlgebra) :
    massWeightPoly x ∈ (Polynomial.mapAlgHom h.covAlgebra.val).range := by
  have hgen : ∀ y ∈ h.covGenerators,
      massWeightPoly y ∈ (Polynomial.mapAlgHom h.covAlgebra.val).range :=
    h.covGenerators_induction
    (fun l μ ν φ => by
      rw [h.massWeight_covF]
      exact h.monomial_mem_range (h.covF_mem_covAlgebra l μ ν φ))
    (fun l φ => by
      rw [h.massWeight_covDerivH]
      exact h.monomial_mem_range (h.covDerivH_mem_covAlgebra l φ))
    (fun l φ => by
      rw [h.massWeight_covDerivBarH]
      exact h.monomial_mem_range (h.covDerivBarH_mem_covAlgebra l φ))
    (fun i {_n} l φ => by
      rw [h.massWeight_covDerivD]
      exact h.monomial_mem_range (h.covDerivD_mem_covAlgebra i l φ))
    (fun i {_n} l φ => by
      rw [h.massWeight_covDerivBarD]
      exact h.monomial_mem_range (h.covDerivBarD_mem_covAlgebra i l φ))
    (fun i {_n} l φ => by
      rw [h.massWeight_covDerivU]
      exact h.monomial_mem_range (h.covDerivU_mem_covAlgebra i l φ))
    (fun i {_n} l φ => by
      rw [h.massWeight_covDerivBarU]
      exact h.monomial_mem_range (h.covDerivBarU_mem_covAlgebra i l φ))
    (fun i {_n} l φ => by
      rw [h.massWeight_covDerivQ]
      exact h.monomial_mem_range (h.covDerivQ_mem_covAlgebra i l φ))
    (fun i {_n} l φ => by
      rw [h.massWeight_covDerivBarQ]
      exact h.monomial_mem_range (h.covDerivBarQ_mem_covAlgebra i l φ))
    (fun i {_n} l φ => by
      rw [h.massWeight_covDerivL]
      exact h.monomial_mem_range (h.covDerivL_mem_covAlgebra i l φ))
    (fun i {_n} l φ => by
      rw [h.massWeight_covDerivBarL]
      exact h.monomial_mem_range (h.covDerivBarL_mem_covAlgebra i l φ))
    (fun i {_n} l φ => by
      rw [h.massWeight_covDerivE]
      exact h.monomial_mem_range (h.covDerivE_mem_covAlgebra i l φ))
    (fun i {_n} l φ => by
      rw [h.massWeight_covDerivBarE]
      exact h.monomial_mem_range (h.covDerivBarE_mem_covAlgebra i l φ))
  induction hx using Algebra.adjoin_induction with
  | mem b hb => exact hgen b hb
  | algebraMap c => exact ⟨algebraMap ℂ (Polynomial ↥h.covAlgebra) c, by simp⟩
  | add a b _ _ iha ihb => rw [map_add]; exact add_mem iha ihb
  | mul a b _ _ iha ihb => rw [map_mul]; exact mul_mem iha ihb

/-!

## C. The covariant subalgebra as an algebra in its own right

The three closure facts of section B let the covariant subalgebra carry a gauge action, a
Lorentz action and a mass-weight polynomial of its own: each is the ambient one restricted,
and each is recorded here together with the lemma identifying it with the ambient one on
underlying elements. The mass-weight polynomial takes a little more care than the two
actions, because its target is the polynomials over the subalgebra rather than the
subalgebra itself; the identification is through the injection
`Polynomial.mapAlgHom h.covAlgebra.val`.

-/

/-- The global gauge action on the covariant subalgebra: the ambient global gauge action,
  which section B shows preserves it. -/
noncomputable def covRepGauge : Representation ℂ GaugeGroupI ↥h.covAlgebra where
  toFun g := LinearMap.restrict (repGlobal repJet g) fun _ hx => h.repGlobal_mem_covAlgebra g hx
  map_one' := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    show repGlobal repJet 1 (x : B) = (x : B)
    rw [map_one]
    rfl
  map_mul' g₁ g₂ := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    show repGlobal repJet (g₁ * g₂) (x : B) = repGlobal repJet g₁ (repGlobal repJet g₂ (x : B))
    rw [map_mul]
    rfl

@[simp]
lemma coe_covRepGauge (g : GaugeGroupI) (x : ↥h.covAlgebra) :
    (h.covRepGauge g x : B) = repGlobal repJet g (x : B) := rfl

/-- The Lorentz action on the covariant subalgebra: the ambient Lorentz action, which
  section B shows preserves it. -/
noncomputable def covRepLorentz : Representation ℂ SL(2,ℂ) ↥h.covAlgebra where
  toFun Λ := LinearMap.restrict (repLorentz Λ) fun _ hx => h.repLorentz_mem_covAlgebra Λ hx
  map_one' := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    show repLorentz 1 (x : B) = (x : B)
    rw [map_one]
    rfl
  map_mul' Λ₁ Λ₂ := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    show repLorentz (Λ₁ * Λ₂) (x : B) = repLorentz Λ₁ (repLorentz Λ₂ (x : B))
    rw [map_mul]
    rfl

@[simp]
lemma coe_covRepLorentz (Λ : SL(2,ℂ)) (x : ↥h.covAlgebra) :
    (h.covRepLorentz Λ x : B) = repLorentz Λ (x : B) := rfl

include h in
/-- Polynomials over the covariant subalgebra inject into polynomials over the algebra. -/
lemma mapAlgHom_val_injective :
    Function.Injective (Polynomial.mapAlgHom h.covAlgebra.val) := by
  rw [Polynomial.coe_mapAlgHom]
  exact Polynomial.map_injective _ Subtype.val_injective

/-- The mass-weight polynomial of the covariant subalgebra: the ambient mass-weight
  polynomial, whose value on the subalgebra has all of its coefficients in the subalgebra
  by section B. -/
noncomputable def covMassWeightPoly : ↥h.covAlgebra →ₐ[ℂ] Polynomial ↥h.covAlgebra :=
  (AlgEquiv.ofInjective (Polynomial.mapAlgHom h.covAlgebra.val)
      h.mapAlgHom_val_injective).symm.toAlgHom.comp
    (AlgHom.codRestrict (massWeightPoly.comp h.covAlgebra.val) _
      fun x => h.massWeightPoly_mem_range_mapAlgHom x.2)

@[simp]
lemma mapAlgHom_covMassWeightPoly (x : ↥h.covAlgebra) :
    Polynomial.mapAlgHom h.covAlgebra.val (h.covMassWeightPoly x) = massWeightPoly (x : B) :=
  congrArg Subtype.val ((AlgEquiv.ofInjective (Polynomial.mapAlgHom h.covAlgebra.val)
    h.mapAlgHom_val_injective).apply_symm_apply
      ⟨massWeightPoly (x : B), h.massWeightPoly_mem_range_mapAlgHom x.2⟩)

/-- A mass-weight eigenvalue equation in the covariant subalgebra is the ambient one. -/
lemma covMassWeightPoly_eq_monomial_iff {n : ℕ} (x : ↥h.covAlgebra) :
    h.covMassWeightPoly x = Polynomial.monomial n x
      ↔ massWeightPoly (x : B) = Polynomial.monomial n (x : B) := by
  constructor
  · intro hx
    rw [← h.mapAlgHom_covMassWeightPoly, hx, Polynomial.mapAlgHom_monomial]
    rfl
  · intro hx
    refine h.mapAlgHom_val_injective ?_
    rw [h.mapAlgHom_covMassWeightPoly, hx, Polynomial.mapAlgHom_monomial]
    rfl


end AlgebraRealization

end StandardModel
