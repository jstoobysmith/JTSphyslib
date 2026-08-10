/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.Terms.ThetaTerm
/-!
# The fermion kinetic terms

The kinetic terms `i ψ̄ σ̄^μ (D_μ ψ)` and `-i (D̄_μ ψ̄) σ̄^μ ψ` of the charged
lepton. Gauge invariance is the cancellation of the hypercharge characters
between the lepton and its conjugate; Lorentz invariance is the intertwining
identity of the contraction matrices `σ̄^μ`. Both have mass weight eight.
-/

@[expose] public section

set_option maxHeartbeats 1000000

namespace LeptonGaugeSector
open TensorProduct StandardModel

namespace JetAlgebra

open scoped minkowskiMatrix PauliMatrix
open Matrix MatrixGroups

/-- The spinor contraction matrices of the right-handed kinetic term: the
  transposed covariant Pauli matrices `(σ̄^μ)ᵀ = (1, -σ1, σ2, -σ3)`. In the
  conventions of this repository the right-handed lepton field transforms by
  the entrywise conjugate of `Λ` and its jet coordinates by the contragredient
  dual, so the pairing of `ψ̄_α`, `(D_μ ψ)_β` and the derivative index `μ` is
  Lorentz invariant precisely through these matrices; this is the intertwining
  identity `sum_kineticPauli_contraction` below. -/
noncomputable def kineticPauli (μ : Fin 1 ⊕ Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((PauliMatrix.pauliSelfAdjoint' μ).1)ᵀ

/-- The fermion kinetic term `i ψ̄_α (σ̄^μ)ᵀ_{α β} (D_μ ψ)_β` of the
  right-handed charged-lepton singlet, with the covariant derivative on the
  lepton. Mass weight eight. -/
noncomputable def fermionKineticTerm : JetAlgebra :=
  Complex.I • ∑ μ, ∑ α, ∑ β, kineticPauli μ α β • (Dbarψ [] α * Dψ [μ] β)

/-- The conjugate fermion kinetic term `-i (D̄_μ ψ̄)_α (σ̄^μ)ᵀ_{α β} ψ_β`, with
  the covariant derivative on the conjugate lepton. Mass weight eight. -/
noncomputable def fermionKineticTermBar : JetAlgebra :=
  (-Complex.I) • ∑ μ, ∑ α, ∑ β, kineticPauli μ α β • (Dbarψ [μ] α * Dψ [] β)

/-- The hypercharge scalars of a lepton–conjugate-lepton pair cancel by
  unitarity. -/
lemma repJetGaugeGroupI_Dbarψ_mul_Dψ (U : JetGaugeGroupI)
    (l l' : List (Fin 1 ⊕ Fin 3)) (α β : Fin 2) :
    repJetGaugeGroupI U (Dbarψ l α * Dψ l' β) = Dbarψ l α * Dψ l' β := by
  have hz : star ((U.eval.2.2 : unitary ℂ) : ℂ) * ((U.eval.2.2 : unitary ℂ) : ℂ) = 1 :=
    (Unitary.mem_iff.mp (U.eval.2.2).2).1
  rw [repJetGaugeGroupI_mul', repJetGaugeGroupI_Dψ, repJetGaugeGroupI_Dbarψ,
    Submonoid.smul_def, Submonoid.smul_def, SubmonoidClass.coe_pow,
    SubmonoidClass.coe_pow, Unitary.coe_star, smul_mul_smul_comm, ← mul_pow, hz,
    one_pow, one_smul]

lemma repJetGaugeGroupI_fermionKineticTerm (U : JetGaugeGroupI) :
    repJetGaugeGroupI U fermionKineticTerm = fermionKineticTerm := by
  rw [fermionKineticTerm, map_smul]
  congr 1
  rw [map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul, repJetGaugeGroupI_Dbarψ_mul_Dψ]

lemma repJetGaugeGroupI_fermionKineticTermBar (U : JetGaugeGroupI) :
    repJetGaugeGroupI U fermionKineticTermBar = fermionKineticTermBar := by
  rw [fermionKineticTermBar, map_smul]
  congr 1
  rw [map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul, repJetGaugeGroupI_Dbarψ_mul_Dψ]

/-- The Lorentz intertwining identity of the kinetic contraction matrices:
  transporting the two spinor slots contragrediently and the derivative slot by
  the Lorentz matrix reproduces the contraction matrices. This is the identity
  `L(Λ) L(Λ⁻¹) = 1` transported through `L(M†) = L(M)ᵀ`. -/
lemma sum_kineticPauli_contraction (Λ : SL(2,ℂ)) (ν : Fin 1 ⊕ Fin 3)
    (α' β' : Fin 2) :
    ∑ μ, ∑ α, ∑ β, kineticPauli μ α β * ((Λ⁻¹).1 α α' *
      ((((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) *
        star ((Λ⁻¹).1 β β'))) = kineticPauli ν α' β' := by
  classical
  have hdet : Matrix.det ((Λ⁻¹).1ᴴ) = 1 := by
    rw [Matrix.det_conjTranspose, Matrix.SpecialLinearGroup.det_coe]
    exact star_one ℂ
  have hval : ∀ μ, (Λ⁻¹).1ᴴ * (PauliMatrix.pauliSelfAdjoint' μ).1 * (Λ⁻¹).1 =
      ∑ j, (Lorentz.SL2C.toLorentzGroup Λ⁻¹).1 μ j •
        (PauliMatrix.pauliSelfAdjoint' j).1 := by
    intro μ
    have h := congrArg Subtype.val
      (Lorentz.SL2C.toSelfAdjointMap_basis
        (M := (⟨(Λ⁻¹).1ᴴ, hdet⟩ : SL(2,ℂ))) μ)
    simp only [Lorentz.SL2C.toSelfAdjointMap_apply_coe, PauliMatrix.pauliBasis',
      Module.Basis.coe_mk, AddSubmonoidClass.coe_finsetSum,
      selfAdjoint.val_smul] at h
    calc (Λ⁻¹).1ᴴ * (PauliMatrix.pauliSelfAdjoint' μ).1 * (Λ⁻¹).1
        = ∑ j, (Lorentz.SL2C.toLorentzGroup
            (⟨(Λ⁻¹).1ᴴ, hdet⟩ : SL(2,ℂ))).1 j μ •
            (PauliMatrix.pauliSelfAdjoint' j).1 := by
          rw [← h]
          congr 1
          rw [show ((⟨(Λ⁻¹).1ᴴ, hdet⟩ : SL(2,ℂ)) :
              Matrix (Fin 2) (Fin 2) ℂ)ᴴ = (Λ⁻¹).1 from
            Matrix.conjTranspose_conjTranspose _]
      _ = ∑ j, (Lorentz.SL2C.toLorentzGroup Λ⁻¹).1 μ j •
            (PauliMatrix.pauliSelfAdjoint' j).1 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          congr 1
          rw [show (Lorentz.SL2C.toLorentzGroup
              (⟨(Λ⁻¹).1ᴴ, hdet⟩ : SL(2,ℂ))).1 =
            (Lorentz.SL2C.toLorentzGroup Λ⁻¹).1ᵀ from
            Lorentz.SL2C.toLorentzGroup_conjTranspose rfl,
            Matrix.transpose_apply]
  have hsand : ∀ μ, (∑ α, ∑ β, kineticPauli μ α β * ((Λ⁻¹).1 α α' *
      star ((Λ⁻¹).1 β β'))) =
      ∑ j, (((Lorentz.SL2C.toLorentzGroup Λ⁻¹).1 μ j : ℝ) : ℂ) *
        kineticPauli j α' β' := by
    intro μ
    have hentry := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A β' α') (hval μ)
    simp only [Matrix.sum_apply, Matrix.smul_apply] at hentry
    calc (∑ α, ∑ β, kineticPauli μ α β * ((Λ⁻¹).1 α α' * star ((Λ⁻¹).1 β β')))
        = ((Λ⁻¹).1ᴴ * (PauliMatrix.pauliSelfAdjoint' μ).1 * (Λ⁻¹).1) β' α' := by
          rw [Matrix.mul_apply]
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [Matrix.mul_apply, Finset.sum_mul]
          refine Finset.sum_congr rfl fun β _ => ?_
          rw [Matrix.conjTranspose_apply, kineticPauli, Matrix.transpose_apply]
          ring
      _ = ∑ j, (((Lorentz.SL2C.toLorentzGroup Λ⁻¹).1 μ j : ℝ) : ℂ) *
            kineticPauli j α' β' := by
          rw [hentry]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [kineticPauli, Matrix.transpose_apply, Complex.real_smul]
  calc ∑ μ, ∑ α, ∑ β, kineticPauli μ α β * ((Λ⁻¹).1 α α' *
      ((((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) *
        star ((Λ⁻¹).1 β β')))
      = ∑ μ, (((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) *
        ∑ α, ∑ β, kineticPauli μ α β * ((Λ⁻¹).1 α α' *
          star ((Λ⁻¹).1 β β')) := by
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun β _ => ?_
        ring
    _ = ∑ μ, ∑ j, (((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) *
          ((((Lorentz.SL2C.toLorentzGroup Λ⁻¹).1 μ j : ℝ) : ℂ) *
            kineticPauli j α' β') := by
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [hsand, Finset.mul_sum]
    _ = ∑ j, ((∑ μ, (Lorentz.SL2C.toLorentzGroup Λ).1 ν μ *
          (Lorentz.SL2C.toLorentzGroup Λ⁻¹).1 μ j : ℝ) : ℂ) *
          kineticPauli j α' β' := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Complex.ofReal_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [Complex.ofReal_mul]
        ring
    _ = kineticPauli ν α' β' := by
        have hmul : ∀ j, (∑ μ, (Lorentz.SL2C.toLorentzGroup Λ).1 ν μ *
            (Lorentz.SL2C.toLorentzGroup Λ⁻¹).1 μ j) =
            ((1 : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ)) ν j := by
          intro j
          rw [← Matrix.mul_apply,
            show ((Lorentz.SL2C.toLorentzGroup Λ).1 *
                (Lorentz.SL2C.toLorentzGroup Λ⁻¹).1 :
                Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ) =
              ((Lorentz.SL2C.toLorentzGroup Λ *
                Lorentz.SL2C.toLorentzGroup Λ⁻¹ : LorentzGroup 3) :
                Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ) from rfl,
            ← map_mul, mul_inv_cancel, map_one]
          rfl
        simp only [hmul, Matrix.one_apply]
        rw [Finset.sum_eq_single ν (fun j _ hj => by
            rw [if_neg (Ne.symm hj), Complex.ofReal_zero, zero_mul])
          (fun h => absurd (Finset.mem_univ ν) h), if_pos rfl,
          Complex.ofReal_one, one_mul]

set_option maxHeartbeats 4000000 in
/-- Lorentz invariance of the fermion kinetic term: the transformation of the
  two spinor slots and the derivative slot cancels through the intertwining
  identity of the contraction matrices. -/
lemma repLorentzGroup_fermionKineticTerm (Λ : SL(2,ℂ)) :
    repLorentzGroup Λ fermionKineticTerm = fermionKineticTerm := by
  have hsmF : ∀ (f : Fin 2 → JetAlgebra) (y : JetAlgebra),
      (∑ x, f x) * y = ∑ x, f x * y := fun f y => by
    rw [show (∑ x, f x) * y = LinearMap.mulRight ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hmsS : ∀ (f : (Fin 1 ⊕ Fin 3) → JetAlgebra) (y : JetAlgebra),
      y * (∑ x, f x) = ∑ x, y * f x := fun f y => by
    rw [show y * (∑ x, f x) = LinearMap.mulLeft ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hmsF : ∀ (f : Fin 2 → JetAlgebra) (y : JetAlgebra),
      y * (∑ x, f x) = ∑ x, y * f x := fun f y => by
    rw [show y * (∑ x, f x) = LinearMap.mulLeft ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hsmul : ∀ (c d : ℂ) (x y : JetAlgebra),
      (c • x) * (d • y) = (c * d) • (x * y) := fun c d x y => by
    rw [smul_mul_smul_comm]
  rw [fermionKineticTerm, map_smul]
  congr 1
  rw [map_sum]
  conv_lhs => enter [2, μ]; rw [map_sum]
  conv_lhs => enter [2, μ, 2, α]; rw [map_sum]
  conv_lhs =>
    enter [2, μ, 2, α, 2, β]
    rw [map_smul, repLorentzGroup_apply_mul, repLorentzGroup_Dbarψ_nil,
      repLorentzGroup_Dψ_singleton]
  simp only [hsmF, hmsS, hmsF, hsmul, Finset.smul_sum, smul_smul]
  -- move the primed sums out and the unprimed sums in
  conv_lhs => enter [2, μ, 2, α]; rw [Finset.sum_comm]
  conv_lhs => enter [2, μ, 2, α, 2, α']; rw [Finset.sum_comm]
  conv_lhs => enter [2, μ, 2, α, 2, α', 2, ν]; rw [Finset.sum_comm]
  conv_lhs => enter [2, μ]; rw [Finset.sum_comm]
  conv_lhs => enter [2, μ, 2, α']; rw [Finset.sum_comm]
  conv_lhs => enter [2, μ, 2, α', 2, ν]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, α']; rw [Finset.sum_comm]
  conv_lhs => enter [2, α', 2, ν]; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α' _ => Finset.sum_congr rfl fun ν _ =>
    Finset.sum_congr rfl fun β' _ => ?_
  conv_lhs => enter [2, μ, 2, α]; rw [← Finset.sum_smul]
  conv_lhs => enter [2, μ]; rw [← Finset.sum_smul]
  rw [← Finset.sum_smul]
  rw [show (∑ μ, ∑ α, ∑ β, kineticPauli μ α β *
      ((Λ⁻¹).1 α α' * ((((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) *
        star ((Λ⁻¹).1 β β')))) = kineticPauli ν α' β' from
    sum_kineticPauli_contraction Λ ν α' β']

set_option maxHeartbeats 4000000 in
/-- Lorentz invariance of the conjugate fermion kinetic term. -/
lemma repLorentzGroup_fermionKineticTermBar (Λ : SL(2,ℂ)) :
    repLorentzGroup Λ fermionKineticTermBar = fermionKineticTermBar := by
  have hsmS : ∀ (f : (Fin 1 ⊕ Fin 3) → JetAlgebra) (y : JetAlgebra),
      (∑ x, f x) * y = ∑ x, f x * y := fun f y => by
    rw [show (∑ x, f x) * y = LinearMap.mulRight ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hsmF : ∀ (f : Fin 2 → JetAlgebra) (y : JetAlgebra),
      (∑ x, f x) * y = ∑ x, f x * y := fun f y => by
    rw [show (∑ x, f x) * y = LinearMap.mulRight ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hmsF : ∀ (f : Fin 2 → JetAlgebra) (y : JetAlgebra),
      y * (∑ x, f x) = ∑ x, y * f x := fun f y => by
    rw [show y * (∑ x, f x) = LinearMap.mulLeft ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hsmul : ∀ (c d : ℂ) (x y : JetAlgebra),
      (c • x) * (d • y) = (c * d) • (x * y) := fun c d x y => by
    rw [smul_mul_smul_comm]
  rw [fermionKineticTermBar, map_smul]
  congr 1
  rw [map_sum]
  conv_lhs => enter [2, μ]; rw [map_sum]
  conv_lhs => enter [2, μ, 2, α]; rw [map_sum]
  conv_lhs =>
    enter [2, μ, 2, α, 2, β]
    rw [map_smul, repLorentzGroup_apply_mul, repLorentzGroup_Dbarψ_singleton,
      repLorentzGroup_Dψ_nil]
  simp only [hsmS, hsmF, hmsF, hsmul, Finset.smul_sum, smul_smul]
  -- move the transformed sums out and the original sums in
  conv_lhs => enter [2, μ, 2, α]; rw [Finset.sum_comm]
  conv_lhs => enter [2, μ, 2, α, 2, ν]; rw [Finset.sum_comm]
  conv_lhs => enter [2, μ, 2, α, 2, ν, 2, α']; rw [Finset.sum_comm]
  conv_lhs => enter [2, μ]; rw [Finset.sum_comm]
  conv_lhs => enter [2, μ, 2, ν]; rw [Finset.sum_comm]
  conv_lhs => enter [2, μ, 2, ν, 2, α']; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, ν]; rw [Finset.sum_comm]
  conv_lhs => enter [2, ν, 2, α']; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun α' _ =>
    Finset.sum_congr rfl fun β' _ => ?_
  conv_lhs => enter [2, μ, 2, α]; rw [← Finset.sum_smul]
  conv_lhs => enter [2, μ]; rw [← Finset.sum_smul]
  rw [← Finset.sum_smul]
  rw [show (∑ μ, ∑ α, ∑ β, kineticPauli μ α β *
      ((((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) * (Λ⁻¹).1 α α' *
        star ((Λ⁻¹).1 β β'))) = kineticPauli ν α' β' from by
    rw [← sum_kineticPauli_contraction Λ ν α' β']
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun α _ =>
      Finset.sum_congr rfl fun β _ => ?_
    ring]

lemma fermionKineticTerm_mem_massWeightLESubmodule :
    fermionKineticTerm ∈ MassWeightLESubmodule 8 := by
  rw [fermionKineticTerm]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun μ _ =>
    Submodule.sum_mem _ fun α _ => Submodule.sum_mem _ fun β _ =>
      Submodule.smul_mem _ _ ?_)
  refine mem_massWeightLESubmodule_of_mem (n := 8) (by simp)
    (mul_mem_massWeightSubmodule (Dbarψ_mem_massWeightSubmodule [] α)
      (Dψ_mem_massWeightSubmodule [μ] β))

lemma fermionKineticTermBar_mem_massWeightLESubmodule :
    fermionKineticTermBar ∈ MassWeightLESubmodule 8 := by
  rw [fermionKineticTermBar]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun μ _ =>
    Submodule.sum_mem _ fun α _ => Submodule.sum_mem _ fun β _ =>
      Submodule.smul_mem _ _ ?_)
  refine mem_massWeightLESubmodule_of_mem (n := 8) (by simp)
    (mul_mem_massWeightSubmodule (Dbarψ_mem_massWeightSubmodule [μ] α)
      (Dψ_mem_massWeightSubmodule [] β))

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
/-- The fermion kinetic term as an explicit combination of the eight
  `ψ̄ (D ψ)` monomials. -/
lemma fermionKineticTerm_eq : fermionKineticTerm =
    Complex.I • ((Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1)
      - (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0)
      - Complex.I • (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0)
      - (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1)) := by
  rw [fermionKineticTerm]
  congr 1
  simp only [Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three,
    Fin.sum_univ_two]
  norm_num [kineticPauli, PauliMatrix.pauliSelfAdjoint', PauliMatrix.pauliMatrix,
    Matrix.transpose_apply, Matrix.one_apply]
  module

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
/-- The conjugate fermion kinetic term as an explicit combination of the eight
  `(D̄ ψ̄) ψ` monomials. -/
lemma fermionKineticTermBar_eq : fermionKineticTermBar =
    (-Complex.I) • ((Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1)
      - (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0)
      - Complex.I • (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0)
      - (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1)) := by
  rw [fermionKineticTermBar]
  congr 1
  simp only [Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three,
    Fin.sum_univ_two]
  norm_num [kineticPauli, PauliMatrix.pauliSelfAdjoint', PauliMatrix.pauliMatrix,
    Matrix.transpose_apply, Matrix.one_apply]
  module

end JetAlgebra

end LeptonGaugeSector
