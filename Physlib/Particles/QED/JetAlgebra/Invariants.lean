/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.QED.JetAlgebra.MassDim
public import Physlib.Relativity.MinkowskiMatrix
public import Physlib.Relativity.PauliMatrices.Basic
/-!
# Mass dimension on the QED jet algebra

-/

@[expose] public section

set_option maxHeartbeats 1000000

namespace QED
open TensorProduct StandardModel

namespace JetAlgebra

/-!

## The renormalizable invariants

The gauge- and Lorentz-invariant elements of mass dimension at most four (mass
weight at most eight). Besides the constants these are kinetic terms alone: the
Maxwell term `F_{μν} F^{μν}`, the topological theta term
`ε^{μνρσ} F_{μν} F_{ρσ}`, and the two fermion kinetic terms
`i ψ̄ σ^μ (D_μ ψ)` and `-i (D̄_μ ψ̄) σ^μ ψ` (equal up to a total derivative).
No mass term exists: `ψψ` and `ψ̄ψ̄` carry hypercharge `±12`, and `ψ̄ψ` is not a
Lorentz scalar for a single Weyl fermion. All other candidate weights `≤ 8` are
excluded by charge balance or by the absence of a Lorentz invariant:
`∂^μ ∂^ν F_{μν} = 0` and `η^{μν} F_{μν} = 0` identically.

-/

open scoped minkowskiMatrix PauliMatrix
open Matrix MatrixGroups

/-- The Maxwell kinetic term `F_{μν} F^{μν}`: the field-strength square with
  both indices raised by the (diagonal) Minkowski metric. Mass weight eight. -/
noncomputable def maxwellTerm : JetAlgebra :=
  ∑ μ, ∑ ν, ((η μ μ * η ν ν : ℝ) : ℂ) •
    (fieldStrengthDeriv {} μ ν * fieldStrengthDeriv {} μ ν)

/-- The topological theta term `ε^{μνρσ} F_{μν} F_{ρσ}`, written as a sum over
  the permutations of the four spacetime indices weighted by their signs. Mass
  weight eight. -/
noncomputable def thetaTerm : JetAlgebra :=
  ∑ p : Equiv.Perm (Fin 4), (Equiv.Perm.sign p : ℤ) •
    (fieldStrengthDeriv {} ((finSumFinEquiv (m := 1) (n := 3)).symm (p 0))
        ((finSumFinEquiv (m := 1) (n := 3)).symm (p 1)) *
      fieldStrengthDeriv {} ((finSumFinEquiv (m := 1) (n := 3)).symm (p 2))
        ((finSumFinEquiv (m := 1) (n := 3)).symm (p 3)))

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

/-- The invariants of the QED jet algebra of mass dimension at most four: the
  constants and the four kinetic terms. These span
  `InvariantMassWeightSubmodule 8`, the renormalizable QED Lagrangian densities. -/
def massDimFourInvariants : Set JetAlgebra :=
  {1, maxwellTerm, thetaTerm, fermionKineticTerm, fermionKineticTermBar}


/-!

## Gauge invariance of the renormalizable terms

The hypercharge selection rule: a jet of gauge transformations acts on the
covariant generators only through `u(0)^{±6}`, so the field-strength squares are
exactly invariant and a product of one covariant lepton and one covariant
conjugate-lepton factor is invariant by unitarity.

-/

lemma repJetGaugeGroupI_maxwellTerm (U : JetGaugeGroupI) :
    repJetGaugeGroupI U maxwellTerm = maxwellTerm := by
  rw [maxwellTerm, map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [map_smul]
  congr 1
  rw [repJetGaugeGroupI_mul', repJetGaugeGroupI_fieldStrengthDeriv]

lemma repJetGaugeGroupI_thetaTerm (U : JetGaugeGroupI) :
    repJetGaugeGroupI U thetaTerm = thetaTerm := by
  rw [thetaTerm, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_zsmul]
  congr 1
  rw [repJetGaugeGroupI_mul', repJetGaugeGroupI_fieldStrengthDeriv,
    repJetGaugeGroupI_fieldStrengthDeriv]

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

/-!

## Lorentz invariance of the renormalizable terms

TODO: these require the transformation laws of the field strength (as an
antisymmetric two-tensor through `Λᵀ η Λ = η` and `det Λ = 1`) and of the
covariant derivatives (through the σ-matrix intertwining relation
`M σ^μ M† = Λ(M)^μ_ν σ^ν` defining `SL2C.toLorentzGroup`), which are not yet
available for the jet-algebra representations.

-/

/-- The component form of the Lorentz-group defining identity: contracting two
  Lorentz matrices with the (diagonal, involutive) Minkowski metric over their
  second indices reproduces the metric. -/
lemma toLorentzGroup_sum_η_mul_mul (Λ : SL(2,ℂ)) (a a' : Fin 1 ⊕ Fin 3) :
    ∑ ν, η ν ν * (Lorentz.SL2C.toLorentzGroup Λ).1 a ν *
      (Lorentz.SL2C.toLorentzGroup Λ).1 a' ν = η a a' := by
  have hsq : η a' a' * η a' a' = 1 := by
    rcases a' with i | i
    · rw [show i = (0 : Fin 1) from Subsingleton.elim i 0,
        minkowskiMatrix.inl_0_inl_0]
      norm_num
    · rw [minkowskiMatrix.inr_i_inr_i]
      norm_num
  have h := congrFun (congrFun ((LorentzGroup.mem_iff_self_mul_dual).mp
    (Lorentz.SL2C.toLorentzGroup Λ).2) a) a'
  rw [Matrix.mul_apply] at h
  simp only [minkowskiMatrix.dual_apply] at h
  have h2 := congrArg (fun t => t * η a' a') h
  simp only [Finset.sum_mul] at h2
  rw [show (∑ ν, (Lorentz.SL2C.toLorentzGroup Λ).1 a ν *
        (η ν ν * (Lorentz.SL2C.toLorentzGroup Λ).1 a' ν * η a' a') * η a' a') =
      ∑ ν, (η ν ν * (Lorentz.SL2C.toLorentzGroup Λ).1 a ν *
        (Lorentz.SL2C.toLorentzGroup Λ).1 a' ν) * (η a' a' * η a' a') from
      Finset.sum_congr rfl fun ν _ => by ring, hsq] at h2
  simp only [mul_one] at h2
  rw [h2, Matrix.one_apply]
  by_cases haa : a = a'
  · subst haa
    simp
  · rw [if_neg haa, minkowskiMatrix.as_diagonal, Matrix.diagonal_apply_ne _ haa]
    simp

/-- The transformation law of the embedded field strength: an antisymmetric
  two-tensor with both indices transforming by the Lorentz matrix. -/
lemma repLorentzGroup_fieldStrengthDeriv_nil (Λ : SL(2,ℂ)) (μ ν : Fin 1 ⊕ Fin 3) :
    repLorentzGroup Λ (fieldStrengthDeriv {} μ ν) =
      ∑ a, ∑ b, (((Lorentz.SL2C.toLorentzGroup Λ).1 a μ *
        (Lorentz.SL2C.toLorentzGroup Λ).1 b ν : ℝ) : ℂ) •
        fieldStrengthDeriv {} a b := by
  have hconv : ∀ (r : ℝ) (X : ℂ ⊗[ℝ] BBoson.JetAlgebra),
      (r • X) ⊗ₜ[ℂ] (1 : LeptonSinglet.JetAlgebra) = ((r : ℂ)) • (X ⊗ₜ[ℂ] 1) := by
    intro r X
    rw [← algebraMap_smul (R := ℝ) ℂ r X, ← TensorProduct.smul_tmul']
    rfl
  have happ : repLorentzGroup Λ (((1 : ℂ) ⊗ₜ[ℝ]
      BBoson.JetAlgebra.fieldStrengthDeriv {} μ ν) ⊗ₜ[ℂ]
        (1 : LeptonSinglet.JetAlgebra)) =
      (BBoson.JetAlgebra.complexRepLorentzGroup Λ ((1 : ℂ) ⊗ₜ[ℝ]
        BBoson.JetAlgebra.fieldStrengthDeriv {} μ ν)) ⊗ₜ[ℂ]
      (LeptonSinglet.JetAlgebra.repLorentzGroup Λ
        (1 : LeptonSinglet.JetAlgebra)) := rfl
  rw [fieldStrengthDeriv, happ,
    BBoson.JetAlgebra.complexRepLorentzGroup_one_tmul_fieldStrengthDeriv_nil,
    LeptonSinglet.JetAlgebra.repLorentzGroup_apply_one]
  simp only [TensorProduct.sum_tmul, hconv, fieldStrengthDeriv]

set_option maxHeartbeats 2000000 in
/-- Lorentz invariance of the Maxwell term, by the `η`-contraction identity. -/
lemma repLorentzGroup_maxwellTerm (Λ : SL(2,ℂ)) :
    repLorentzGroup Λ maxwellTerm = maxwellTerm := by
  have hscal : ∀ a b a' b' : Fin 1 ⊕ Fin 3,
      (∑ μ, ∑ ν, η μ μ * η ν ν *
        ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ *
          (Lorentz.SL2C.toLorentzGroup Λ).1 b ν *
          ((Lorentz.SL2C.toLorentzGroup Λ).1 a' μ *
            (Lorentz.SL2C.toLorentzGroup Λ).1 b' ν))) = η a a' * η b b' := by
    intro a b a' b'
    rw [show (∑ μ, ∑ ν, η μ μ * η ν ν *
        ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ *
          (Lorentz.SL2C.toLorentzGroup Λ).1 b ν *
          ((Lorentz.SL2C.toLorentzGroup Λ).1 a' μ *
            (Lorentz.SL2C.toLorentzGroup Λ).1 b' ν))) =
        ∑ μ, (η μ μ * (Lorentz.SL2C.toLorentzGroup Λ).1 a μ *
            (Lorentz.SL2C.toLorentzGroup Λ).1 a' μ) *
          ∑ ν, (η ν ν * (Lorentz.SL2C.toLorentzGroup Λ).1 b ν *
            (Lorentz.SL2C.toLorentzGroup Λ).1 b' ν) from
      Finset.sum_congr rfl fun μ _ => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun ν _ => by ring,
      ← Finset.sum_mul, toLorentzGroup_sum_η_mul_mul, toLorentzGroup_sum_η_mul_mul]
  have hFt : ∀ μ ν : Fin 1 ⊕ Fin 3, repLorentzGroup Λ
      (fieldStrengthDeriv {} μ ν * fieldStrengthDeriv {} μ ν) =
      ∑ a, ∑ b, ∑ a', ∑ b',
        ((((Lorentz.SL2C.toLorentzGroup Λ).1 a μ *
          (Lorentz.SL2C.toLorentzGroup Λ).1 b ν : ℝ) : ℂ) *
          (((Lorentz.SL2C.toLorentzGroup Λ).1 a' μ *
            (Lorentz.SL2C.toLorentzGroup Λ).1 b' ν : ℝ) : ℂ)) •
        (fieldStrengthDeriv {} a b * fieldStrengthDeriv {} a' b') := by
    intro μ ν
    rw [repLorentzGroup_apply_mul, repLorentzGroup_fieldStrengthDeriv_nil]
    have hsm : ∀ (f : (Fin 1 ⊕ Fin 3) → JetAlgebra) (y : JetAlgebra),
        (∑ x, f x) * y = ∑ x, f x * y := fun f y => by
      rw [show (∑ x, f x) * y = LinearMap.mulRight ℂ y (∑ x, f x) from rfl, map_sum]
      rfl
    have hms : ∀ (f : (Fin 1 ⊕ Fin 3) → JetAlgebra) (y : JetAlgebra),
        y * (∑ x, f x) = ∑ x, y * f x := fun f y => by
      rw [show y * (∑ x, f x) = LinearMap.mulLeft ℂ y (∑ x, f x) from rfl, map_sum]
      rfl
    have hsmul : ∀ (c d : ℂ) (x y : JetAlgebra),
        (c • x) * (d • y) = (c * d) • (x * y) := fun c d x y => by
      rw [smul_mul_smul_comm]
    simp only [hsm, hms, hsmul]
  rw [maxwellTerm, map_sum]
  conv_lhs => enter [2, μ]; rw [map_sum]
  conv_lhs => enter [2, μ, 2, ν]; rw [map_smul, hFt μ ν]
  simp only [Finset.smul_sum, smul_smul, ← Complex.ofReal_mul]
  conv_lhs => enter [2, μ]; rw [Finset.sum_comm]
  conv_lhs => enter [2, μ, 2, a]; rw [Finset.sum_comm]
  conv_lhs => enter [2, μ, 2, a, 2, b]; rw [Finset.sum_comm]
  conv_lhs => enter [2, μ, 2, a, 2, b, 2, a']; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a, 2, b]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a, 2, b, 2, a']; rw [Finset.sum_comm]
  conv_lhs => enter [2, a, 2, b, 2, a', 2, b', 2, μ]; rw [← Finset.sum_smul]
  conv_lhs => enter [2, a, 2, b, 2, a', 2, b']; rw [← Finset.sum_smul]
  simp only [← Complex.ofReal_sum, hscal]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single a (fun a'' _ ha'' => Finset.sum_eq_zero fun b'' _ => by
      rw [show η a a'' = 0 from by
          rw [minkowskiMatrix.as_diagonal, Matrix.diagonal_apply_ne _ (Ne.symm ha'')],
        zero_mul, Complex.ofReal_zero, zero_smul])
    (fun h => absurd (Finset.mem_univ a) h),
    Finset.sum_eq_single b (fun b'' _ hb'' => by
      rw [show η b b'' = 0 from by
          rw [minkowskiMatrix.as_diagonal, Matrix.diagonal_apply_ne _ (Ne.symm hb'')],
        mul_zero, Complex.ofReal_zero, zero_smul])
    (fun h => absurd (Finset.mem_univ b) h)]

/-- The transformation law of a product of two field strengths. -/
lemma repLorentzGroup_fieldStrengthDeriv_mul (Λ : SL(2,ℂ))
    (μ ν ρ τ : Fin 1 ⊕ Fin 3) :
    repLorentzGroup Λ (fieldStrengthDeriv {} μ ν * fieldStrengthDeriv {} ρ τ) =
      ∑ a, ∑ b, ∑ a', ∑ b',
        ((((Lorentz.SL2C.toLorentzGroup Λ).1 a μ *
          (Lorentz.SL2C.toLorentzGroup Λ).1 b ν : ℝ) : ℂ) *
          (((Lorentz.SL2C.toLorentzGroup Λ).1 a' ρ *
            (Lorentz.SL2C.toLorentzGroup Λ).1 b' τ : ℝ) : ℂ)) •
        (fieldStrengthDeriv {} a b * fieldStrengthDeriv {} a' b') := by
  rw [repLorentzGroup_apply_mul, repLorentzGroup_fieldStrengthDeriv_nil,
    repLorentzGroup_fieldStrengthDeriv_nil]
  have hsm : ∀ (f : (Fin 1 ⊕ Fin 3) → JetAlgebra) (y : JetAlgebra),
      (∑ x, f x) * y = ∑ x, f x * y := fun f y => by
    rw [show (∑ x, f x) * y = LinearMap.mulRight ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hms : ∀ (f : (Fin 1 ⊕ Fin 3) → JetAlgebra) (y : JetAlgebra),
      y * (∑ x, f x) = ∑ x, y * f x := fun f y => by
    rw [show y * (∑ x, f x) = LinearMap.mulLeft ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hsmul : ∀ (c d : ℂ) (x y : JetAlgebra),
      (c • x) * (d • y) = (c * d) • (x * y) := fun c d x y => by
    rw [smul_mul_smul_comm]
  simp only [hsm, hms, hsmul]

/-- The alternating four-fold contraction of Lorentz matrices is a determinant:
  the combinatorial identity behind the invariance of the theta term. -/
lemma sum_perm_sign_mul_prod_eq_det (Λ : SL(2,ℂ)) (v : Fin 4 → Fin 1 ⊕ Fin 3) :
    (∑ p : Equiv.Perm (Fin 4), ((Equiv.Perm.sign p : ℤ) : ℝ) *
      ∏ i, (Lorentz.SL2C.toLorentzGroup Λ).1 (v i)
        ((finSumFinEquiv (m := 1) (n := 3)).symm (p i))) =
    Matrix.det (Matrix.of fun i j : Fin 4 =>
      (Lorentz.SL2C.toLorentzGroup Λ).1 (v i)
        ((finSumFinEquiv (m := 1) (n := 3)).symm j)) := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  rfl

/-- The alternating contraction matrix of a non-injective index tuple has two
  equal rows, so its determinant vanishes. -/
lemma det_toLorentzGroup_of_not_injective (Λ : SL(2,ℂ)) {v : Fin 4 → Fin 1 ⊕ Fin 3}
    (hv : ¬ Function.Injective v) :
    Matrix.det (Matrix.of fun i j : Fin 4 =>
      (Lorentz.SL2C.toLorentzGroup Λ).1 (v i)
        ((finSumFinEquiv (m := 1) (n := 3)).symm j)) = 0 := by
  rw [Function.not_injective_iff] at hv
  obtain ⟨i, j, hij, hne⟩ := hv
  exact Matrix.det_zero_of_row_eq hne (funext fun k => by simp [hij])

/-- On an index tuple obtained by permuting the four spacetime indices, the
  alternating contraction matrix has determinant the sign of the permutation,
  by `det Λ = 1`. -/
lemma det_toLorentzGroup_comp_perm (Λ : SL(2,ℂ)) (q : Equiv.Perm (Fin 4)) :
    Matrix.det (Matrix.of fun i j : Fin 4 =>
      (Lorentz.SL2C.toLorentzGroup Λ).1
        ((finSumFinEquiv (m := 1) (n := 3)).symm (q i))
        ((finSumFinEquiv (m := 1) (n := 3)).symm j)) =
      ((Equiv.Perm.sign q : ℤ) : ℝ) := by
  have h1 : (Matrix.of fun i j : Fin 4 =>
      (Lorentz.SL2C.toLorentzGroup Λ).1
        ((finSumFinEquiv (m := 1) (n := 3)).symm (q i))
        ((finSumFinEquiv (m := 1) (n := 3)).symm j)) =
      ((Lorentz.SL2C.toLorentzGroup Λ).1.submatrix
        (finSumFinEquiv (m := 1) (n := 3)).symm
        (finSumFinEquiv (m := 1) (n := 3)).symm).submatrix q id := rfl
  rw [h1, Matrix.det_permute,
    Matrix.det_submatrix_equiv_self (finSumFinEquiv (m := 1) (n := 3)).symm,
    Lorentz.SL2C.toLorentzGroup_det_one, mul_one]

set_option maxHeartbeats 4000000 in
/-- Lorentz invariance of the theta term: the alternating contraction is the
  determinant of the Lorentz matrix, which is one. -/
lemma repLorentzGroup_thetaTerm (Λ : SL(2,ℂ)) :
    repLorentzGroup Λ thetaTerm = thetaTerm := by
  classical
  rw [thetaTerm, map_sum]
  conv_lhs => enter [2, p]; rw [map_zsmul, repLorentzGroup_fieldStrengthDeriv_mul]
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a, 2, b]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a, 2, b, 2, a']; rw [Finset.sum_comm]
  have hdet : ∀ a b a' b' : Fin 1 ⊕ Fin 3,
      (∑ p : Equiv.Perm (Fin 4), (Equiv.Perm.sign p : ℤ) •
        ((((Lorentz.SL2C.toLorentzGroup Λ).1 a
            ((finSumFinEquiv (m := 1) (n := 3)).symm (p 0)) *
          (Lorentz.SL2C.toLorentzGroup Λ).1 b
            ((finSumFinEquiv (m := 1) (n := 3)).symm (p 1)) : ℝ) : ℂ) *
          (((Lorentz.SL2C.toLorentzGroup Λ).1 a'
            ((finSumFinEquiv (m := 1) (n := 3)).symm (p 2)) *
          (Lorentz.SL2C.toLorentzGroup Λ).1 b'
            ((finSumFinEquiv (m := 1) (n := 3)).symm (p 3)) : ℝ) : ℂ)) •
          (fieldStrengthDeriv {} a b * fieldStrengthDeriv {} a' b')) =
      ((Matrix.det (Matrix.of fun i j : Fin 4 =>
        (Lorentz.SL2C.toLorentzGroup Λ).1 (![a, b, a', b'] i)
          ((finSumFinEquiv (m := 1) (n := 3)).symm j)) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} a b * fieldStrengthDeriv {} a' b') := by
    intro a b a' b'
    rw [← sum_perm_sign_mul_prod_eq_det Λ ![a, b, a', b'], Complex.ofReal_sum,
      Finset.sum_smul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Fin.prod_univ_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
    rw [← Int.cast_smul_eq_zsmul ℂ, smul_smul]
    congr 1
    push_cast
    ring
  conv_lhs => enter [2, a, 2, b, 2, a', 2, b']; rw [hdet a b a' b']
  have hflat : ∀ (G : (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) →
      (Fin 1 ⊕ Fin 3) → JetAlgebra),
      (∑ a, ∑ b, ∑ a', ∑ b', G a b a' b') =
      ∑ t : (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3),
        G t.1 t.2.1 t.2.2.1 t.2.2.2 := fun G => by
    symm
    simp only [Fintype.sum_prod_type]
  rw [hflat]
  rw [← Finset.sum_filter_of_ne
    (p := fun t : (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) ×
      (Fin 1 ⊕ Fin 3) => Function.Injective ![t.1, t.2.1, t.2.2.1, t.2.2.2])
    (fun t _ hne => by
      by_contra hni
      exact hne (by
        rw [det_toLorentzGroup_of_not_injective Λ hni, Complex.ofReal_zero,
          zero_smul]))]
  have hcard : Fintype.card (Fin 4) = Fintype.card (Fin 1 ⊕ Fin 3) := by simp
  refine Finset.sum_bij
    (i := fun t ht => (Equiv.ofBijective ![t.1, t.2.1, t.2.2.1, t.2.2.2]
      ((Fintype.bijective_iff_injective_and_card _).mpr
        ⟨(Finset.mem_filter.mp ht).2, hcard⟩)).trans
      (finSumFinEquiv (m := 1) (n := 3)))
    ?_ ?_ ?_ ?_
  · intro t ht
    exact Finset.mem_univ _
  · intro t₁ ht₁ t₂ ht₂ h
    have hv : ∀ i : Fin 4, ![t₁.1, t₁.2.1, t₁.2.2.1, t₁.2.2.2] i =
        ![t₂.1, t₂.2.1, t₂.2.2.1, t₂.2.2.2] i := by
      intro i
      have := congrArg (fun q : Equiv.Perm (Fin 4) =>
        (finSumFinEquiv (m := 1) (n := 3)).symm (q i)) h
      simpa using this
    have h0 := hv 0
    have h1 := hv 1
    have h2 := hv 2
    have h3 := hv 3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] at h0 h1 h2 h3
    exact Prod.ext h0 (Prod.ext h1 (Prod.ext h2 h3))
  · intro q _
    refine ⟨((finSumFinEquiv (m := 1) (n := 3)).symm (q 0),
      (finSumFinEquiv (m := 1) (n := 3)).symm (q 1),
      (finSumFinEquiv (m := 1) (n := 3)).symm (q 2),
      (finSumFinEquiv (m := 1) (n := 3)).symm (q 3)), ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hveq : ![(finSumFinEquiv (m := 1) (n := 3)).symm (q 0),
          (finSumFinEquiv (m := 1) (n := 3)).symm (q 1),
          (finSumFinEquiv (m := 1) (n := 3)).symm (q 2),
          (finSumFinEquiv (m := 1) (n := 3)).symm (q 3)] =
          fun i => (finSumFinEquiv (m := 1) (n := 3)).symm (q i) := by
        funext i
        fin_cases i <;> rfl
      rw [hveq]
      exact ((finSumFinEquiv (m := 1) (n := 3)).symm.injective).comp q.injective
    · refine Equiv.ext fun i => ?_
      show (finSumFinEquiv (m := 1) (n := 3))
        (![(finSumFinEquiv (m := 1) (n := 3)).symm (q 0),
          (finSumFinEquiv (m := 1) (n := 3)).symm (q 1),
          (finSumFinEquiv (m := 1) (n := 3)).symm (q 2),
          (finSumFinEquiv (m := 1) (n := 3)).symm (q 3)] i) = q i
      fin_cases i <;> simp
  · intro t ht
    have hq : ∀ i : Fin 4, (finSumFinEquiv (m := 1) (n := 3)).symm
        (((Equiv.ofBijective ![t.1, t.2.1, t.2.2.1, t.2.2.2]
          ((Fintype.bijective_iff_injective_and_card _).mpr
            ⟨(Finset.mem_filter.mp ht).2, hcard⟩)).trans
          (finSumFinEquiv (m := 1) (n := 3))) i) =
        ![t.1, t.2.1, t.2.2.1, t.2.2.2] i := by
      intro i
      simp [Equiv.ofBijective]
    have hmat : (Matrix.of fun i j : Fin 4 =>
        (Lorentz.SL2C.toLorentzGroup Λ).1 (![t.1, t.2.1, t.2.2.1, t.2.2.2] i)
          ((finSumFinEquiv (m := 1) (n := 3)).symm j)) =
        (Matrix.of fun i j : Fin 4 =>
        (Lorentz.SL2C.toLorentzGroup Λ).1
          ((finSumFinEquiv (m := 1) (n := 3)).symm
            (((Equiv.ofBijective ![t.1, t.2.1, t.2.2.1, t.2.2.2]
              ((Fintype.bijective_iff_injective_and_card _).mpr
                ⟨(Finset.mem_filter.mp ht).2, hcard⟩)).trans
              (finSumFinEquiv (m := 1) (n := 3))) i))
          ((finSumFinEquiv (m := 1) (n := 3)).symm j)) := by
      refine congrArg Matrix.of (funext fun i => funext fun j => ?_)
      rw [hq i]
    rw [hmat, det_toLorentzGroup_comp_perm]
    have h0 := hq 0
    have h1 := hq 1
    have h2 := hq 2
    have h3 := hq 3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] at h0 h1 h2 h3
    rw [h0, h1, h2, h3, ← Int.cast_smul_eq_zsmul ℂ]
    module

/-!

### Lorentz transformation laws of the fermionic generators

-/

/-- The Lorentz action on the zeroth-order lepton generator: the spinor index
  transforms contragrediently, by the conjugate inverse matrix. -/
lemma repLorentzGroup_ψ (Λ : SL(2,ℂ)) (α : Fin 2) :
    repLorentzGroup Λ [JetGenerators.dψ {} α]ₐ =
      ∑ β, star ((Λ⁻¹).1 α β) • [JetGenerators.dψ {} β]ₐ := by
  rw [show ([JetGenerators.dψ {} α]ₐ : JetAlgebra) =
      (1 : ℂ ⊗[ℝ] BBoson.JetAlgebra) ⊗ₜ[ℂ]
        LeptonSinglet.JetAlgebra.ofGenerator
          (LeptonSinglet.JetGenerators.dψ {} α) from rfl,
    repLorentzGroup_tmul, BBoson.JetAlgebra.complexRepLorentzGroup_apply_one,
    LeptonSinglet.JetAlgebra.repLorentzGroup_ofGenerator_ψ_nil,
    TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [TensorProduct.tmul_smul]
  rfl

/-- The Lorentz action on the first-order lepton generator. -/
lemma repLorentzGroup_dψ_singleton (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3)
    (α : Fin 2) :
    repLorentzGroup Λ [JetGenerators.dψ {μ} α]ₐ =
      ∑ ν, ∑ β, ((((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) *
        star ((Λ⁻¹).1 α β)) • [JetGenerators.dψ {ν} β]ₐ := by
  rw [show ([JetGenerators.dψ {μ} α]ₐ : JetAlgebra) =
      (1 : ℂ ⊗[ℝ] BBoson.JetAlgebra) ⊗ₜ[ℂ]
        LeptonSinglet.JetAlgebra.ofGenerator
          (LeptonSinglet.JetGenerators.dψ {μ} α) from rfl,
    repLorentzGroup_tmul, BBoson.JetAlgebra.complexRepLorentzGroup_apply_one,
    LeptonSinglet.JetAlgebra.repLorentzGroup_ofGenerator_ψ_singleton,
    TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [TensorProduct.tmul_smul]
  rfl

/-- The Lorentz action on the zeroth-order conjugate lepton generator: the
  spinor index transforms by the inverse matrix. -/
lemma repLorentzGroup_barψ (Λ : SL(2,ℂ)) (α : Fin 2) :
    repLorentzGroup Λ [JetGenerators.dbarψ {} α]ₐ =
      ∑ β, (Λ⁻¹).1 α β • [JetGenerators.dbarψ {} β]ₐ := by
  rw [show ([JetGenerators.dbarψ {} α]ₐ : JetAlgebra) =
      (1 : ℂ ⊗[ℝ] BBoson.JetAlgebra) ⊗ₜ[ℂ]
        LeptonSinglet.JetAlgebra.ofGenerator
          (LeptonSinglet.JetGenerators.dbarψ {} α) from rfl,
    repLorentzGroup_tmul, BBoson.JetAlgebra.complexRepLorentzGroup_apply_one,
    LeptonSinglet.JetAlgebra.repLorentzGroup_ofGenerator_barψ_nil,
    TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [TensorProduct.tmul_smul]
  rfl

/-- The Lorentz action on the first-order conjugate lepton generator. -/
lemma repLorentzGroup_dbarψ_singleton (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3)
    (α : Fin 2) :
    repLorentzGroup Λ [JetGenerators.dbarψ {μ} α]ₐ =
      ∑ ν, ∑ β, ((((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) *
        (Λ⁻¹).1 α β) • [JetGenerators.dbarψ {ν} β]ₐ := by
  rw [show ([JetGenerators.dbarψ {μ} α]ₐ : JetAlgebra) =
      (1 : ℂ ⊗[ℝ] BBoson.JetAlgebra) ⊗ₜ[ℂ]
        LeptonSinglet.JetAlgebra.ofGenerator
          (LeptonSinglet.JetGenerators.dbarψ {μ} α) from rfl,
    repLorentzGroup_tmul, BBoson.JetAlgebra.complexRepLorentzGroup_apply_one,
    LeptonSinglet.JetAlgebra.repLorentzGroup_ofGenerator_barψ_singleton,
    TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [TensorProduct.tmul_smul]
  rfl

/-- The Lorentz action on the zeroth-order B-boson generator of the QED jet
  algebra. -/
lemma repLorentzGroup_B (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) :
    repLorentzGroup Λ [JetGenerators.dB {} μ]ₐ =
      ∑ ν, (((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) •
        [JetGenerators.dB {} ν]ₐ := by
  have hconv : ∀ (r : ℝ) (X : ℂ ⊗[ℝ] BBoson.JetAlgebra),
      (r • X) ⊗ₜ[ℂ] (1 : LeptonSinglet.JetAlgebra) = ((r : ℂ)) • (X ⊗ₜ[ℂ] 1) := by
    intro r X
    rw [← algebraMap_smul (R := ℝ) ℂ r X, ← TensorProduct.smul_tmul']
    rfl
  rw [show ([JetGenerators.dB {} μ]ₐ : JetAlgebra) =
      ((1 : ℂ) ⊗ₜ[ℝ] BBoson.JetAlgebra.ofGenerator (BBoson.JetGenerators.dB {} μ))
        ⊗ₜ[ℂ] (1 : LeptonSinglet.JetAlgebra) from rfl,
    repLorentzGroup_tmul,
    show BBoson.JetAlgebra.complexRepLorentzGroup Λ ((1 : ℂ) ⊗ₜ[ℝ]
        BBoson.JetAlgebra.ofGenerator (BBoson.JetGenerators.dB {} μ)) =
      (1 : ℂ) ⊗ₜ[ℝ] BBoson.JetAlgebra.repLorentzGroup Λ
        (BBoson.JetAlgebra.ofGenerator (BBoson.JetGenerators.dB {} μ)) from rfl,
    BBoson.JetAlgebra.repLorentzGroup_ofGenerator_dB_nil,
    LeptonSinglet.JetAlgebra.repLorentzGroup_apply_one, TensorProduct.tmul_sum,
    TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [TensorProduct.tmul_smul, hconv]
  rfl

/-- The first conjugate covariant derivative:
  `D̄_μ ψ̄_α = ∂_μ ψ̄_α - 6 i B_μ ψ̄_α`. -/
lemma Dbarψ_singleton (μ : Fin 1 ⊕ Fin 3) (α : Fin 2) :
    Dbarψ [μ] α = [JetGenerators.dbarψ {μ} α]ₐ -
      ((6 : ℂ) * Complex.I) •
        ([JetGenerators.dB {} μ]ₐ * [JetGenerators.dbarψ {} α]ₐ) := by
  rw [Dbarψ_cons, Dbarψ_nil, covariantStepBar, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.mulLeft_apply]
  congr 1
  simp only [ofGenerator]
  rw [jetDeriv_tmul, LinearMap.baseChange_tmul]
  simp only [BBoson.JetAlgebra.jetDeriv_one, TensorProduct.tmul_zero,
    TensorProduct.zero_tmul, zero_add,
    LeptonSinglet.JetAlgebra.jetDeriv_ofGenerator,
    LeptonSinglet.JetGenerators.shift_dbarψ, Multiset.empty_eq_zero]

/-- Covariance of the zeroth covariant derivatives under the Lorentz group. -/
lemma repLorentzGroup_Dψ_nil (Λ : SL(2,ℂ)) (α : Fin 2) :
    repLorentzGroup Λ (Dψ [] α) = ∑ β, star ((Λ⁻¹).1 α β) • Dψ [] β := by
  rw [Dψ_nil, repLorentzGroup_ψ]
  simp only [Dψ_nil]

lemma repLorentzGroup_Dbarψ_nil (Λ : SL(2,ℂ)) (α : Fin 2) :
    repLorentzGroup Λ (Dbarψ [] α) = ∑ β, (Λ⁻¹).1 α β • Dbarψ [] β := by
  rw [Dbarψ_nil, repLorentzGroup_barψ]
  simp only [Dbarψ_nil]

set_option maxHeartbeats 2000000 in
/-- Covariance of the first covariant derivative under the Lorentz group: the
  gauge-field term transforms exactly as the derivative term. -/
lemma repLorentzGroup_Dψ_singleton (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3)
    (α : Fin 2) :
    repLorentzGroup Λ (Dψ [μ] α) =
      ∑ ν, ∑ β, ((((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) *
        star ((Λ⁻¹).1 α β)) • Dψ [ν] β := by
  have hsm : ∀ (f : (Fin 1 ⊕ Fin 3) → JetAlgebra) (y : JetAlgebra),
      (∑ x, f x) * y = ∑ x, f x * y := fun f y => by
    rw [show (∑ x, f x) * y = LinearMap.mulRight ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hms : ∀ (f : Fin 2 → JetAlgebra) (y : JetAlgebra),
      y * (∑ x, f x) = ∑ x, y * f x := fun f y => by
    rw [show y * (∑ x, f x) = LinearMap.mulLeft ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hsmul : ∀ (c d : ℂ) (x y : JetAlgebra),
      (c • x) * (d • y) = (c * d) • (x * y) := fun c d x y => by
    rw [smul_mul_smul_comm]
  rw [Dψ_singleton, map_add, map_smul, repLorentzGroup_apply_mul, repLorentzGroup_B,
    repLorentzGroup_ψ, repLorentzGroup_dψ_singleton]
  conv_rhs => enter [2, ν, 2, β]; rw [Dψ_singleton, smul_add]
  conv_rhs => enter [2, ν]; rw [Finset.sum_add_distrib]
  rw [Finset.sum_add_distrib]
  congr 1
  simp only [hsm, hms, hsmul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun β _ => ?_
  rw [smul_smul, smul_smul]
  congr 1
  ring

set_option maxHeartbeats 2000000 in
/-- Covariance of the first conjugate covariant derivative under the Lorentz
  group. -/
lemma repLorentzGroup_Dbarψ_singleton (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3)
    (α : Fin 2) :
    repLorentzGroup Λ (Dbarψ [μ] α) =
      ∑ ν, ∑ β, ((((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) *
        (Λ⁻¹).1 α β) • Dbarψ [ν] β := by
  have hsm : ∀ (f : (Fin 1 ⊕ Fin 3) → JetAlgebra) (y : JetAlgebra),
      (∑ x, f x) * y = ∑ x, f x * y := fun f y => by
    rw [show (∑ x, f x) * y = LinearMap.mulRight ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hms : ∀ (f : Fin 2 → JetAlgebra) (y : JetAlgebra),
      y * (∑ x, f x) = ∑ x, y * f x := fun f y => by
    rw [show y * (∑ x, f x) = LinearMap.mulLeft ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hsmul : ∀ (c d : ℂ) (x y : JetAlgebra),
      (c • x) * (d • y) = (c * d) • (x * y) := fun c d x y => by
    rw [smul_mul_smul_comm]
  rw [Dbarψ_singleton, map_sub, map_smul, repLorentzGroup_apply_mul, repLorentzGroup_B,
    repLorentzGroup_barψ, repLorentzGroup_dbarψ_singleton]
  conv_rhs => enter [2, ν, 2, β]; rw [Dbarψ_singleton, smul_sub]
  conv_rhs => enter [2, ν]; rw [Finset.sum_sub_distrib]
  rw [Finset.sum_sub_distrib]
  congr 1
  simp only [hsm, hms, hsmul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun β _ => ?_
  rw [smul_smul, smul_smul]
  congr 1
  ring

/-!

### The kinetic contraction identity and Lorentz invariance

-/

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

/-!

## The span inclusion

Every element of `massDimFourInvariants` is invariant and has mass weight at
most eight, so the span is contained in `InvariantMassWeightSubmodule 8`.

-/

/-- Eigenvectors of weight `m ≤ n` lie in the weight-`≤ n` submodule. -/
lemma mem_massWeightLESubmodule_of_forall_massWeightScale {x : JetAlgebra}
    {m n : ℕ} (hmn : m ≤ n)
    (hx : ∀ c : ℂ, massWeightScale c x = c ^ m • x) :
    x ∈ MassWeightLESubmodule n :=
  Submodule.subset_span ⟨m, hmn, hx⟩

/-- Products of homogeneous elements are homogeneous of the summed weight. -/
lemma massWeightScale_mul_eigen {x y : JetAlgebra} {m n : ℕ}
    (hx : ∀ c : ℂ, massWeightScale c x = c ^ m • x)
    (hy : ∀ c : ℂ, massWeightScale c y = c ^ n • y) (c : ℂ) :
    massWeightScale c (x * y) = c ^ (m + n) • (x * y) := by
  rw [map_mul, hx, hy, smul_mul_smul_comm, ← pow_add]

lemma maxwellTerm_mem_massWeightLESubmodule :
    maxwellTerm ∈ MassWeightLESubmodule 8 := by
  rw [maxwellTerm]
  refine Submodule.sum_mem _ fun μ _ => Submodule.sum_mem _ fun ν _ =>
    Submodule.smul_mem _ _ ?_
  exact mem_massWeightLESubmodule_of_forall_massWeightScale (m := 4 + 4) le_rfl
    (massWeightScale_mul_eigen (m := 4) (n := 4)
      (fun c => massWeightScale_fieldStrengthDeriv c {} μ ν)
      (fun c => massWeightScale_fieldStrengthDeriv c {} μ ν))

lemma thetaTerm_mem_massWeightLESubmodule :
    thetaTerm ∈ MassWeightLESubmodule 8 := by
  rw [thetaTerm]
  refine Submodule.sum_mem _ fun p _ => zsmul_mem ?_ _
  exact mem_massWeightLESubmodule_of_forall_massWeightScale (m := 4 + 4) le_rfl
    (massWeightScale_mul_eigen (m := 4) (n := 4)
      (fun c => massWeightScale_fieldStrengthDeriv c {} _ _)
      (fun c => massWeightScale_fieldStrengthDeriv c {} _ _))

lemma fermionKineticTerm_mem_massWeightLESubmodule :
    fermionKineticTerm ∈ MassWeightLESubmodule 8 := by
  rw [fermionKineticTerm]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun μ _ =>
    Submodule.sum_mem _ fun α _ => Submodule.sum_mem _ fun β _ =>
      Submodule.smul_mem _ _ ?_)
  exact mem_massWeightLESubmodule_of_forall_massWeightScale (m := 3 + 5) le_rfl
    (massWeightScale_mul_eigen (m := 3) (n := 5)
      (fun c => massWeightScale_Dbarψ c [] α)
      (fun c => massWeightScale_Dψ c [μ] β))

lemma fermionKineticTermBar_mem_massWeightLESubmodule :
    fermionKineticTermBar ∈ MassWeightLESubmodule 8 := by
  rw [fermionKineticTermBar]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun μ _ =>
    Submodule.sum_mem _ fun α _ => Submodule.sum_mem _ fun β _ =>
      Submodule.smul_mem _ _ ?_)
  exact mem_massWeightLESubmodule_of_forall_massWeightScale (m := 5 + 3) le_rfl
    (massWeightScale_mul_eigen (m := 5) (n := 3)
      (fun c => massWeightScale_Dbarψ c [μ] α)
      (fun c => massWeightScale_Dψ c [] β))

/-- The Lorentz action fixes the unit of the jet algebra. -/
lemma repLorentzGroup_one (Λ : SL(2,ℂ)) :
    repLorentzGroup Λ (1 : JetAlgebra) = 1 := by
  have h1 : BBoson.JetAlgebra.complexRepLorentzGroup Λ
      (1 : ℂ ⊗[ℝ] BBoson.JetAlgebra) = 1 := by
    rw [show (1 : ℂ ⊗[ℝ] BBoson.JetAlgebra) =
        (1 : ℂ) ⊗ₜ[ℝ] (1 : BBoson.JetAlgebra) from rfl,
      show BBoson.JetAlgebra.complexRepLorentzGroup Λ
          ((1 : ℂ) ⊗ₜ[ℝ] (1 : BBoson.JetAlgebra)) =
        (1 : ℂ) ⊗ₜ[ℝ] BBoson.JetAlgebra.repLorentzGroup Λ (1 : BBoson.JetAlgebra)
        from by rw [show BBoson.JetAlgebra.complexRepLorentzGroup Λ =
            LinearMap.baseChange ℂ (BBoson.JetAlgebra.repLorentzGroup Λ) from rfl,
          LinearMap.baseChange_tmul],
      show BBoson.JetAlgebra.repLorentzGroup Λ (1 : BBoson.JetAlgebra) = 1 from
        map_one (SymmetricAlgebra.lift (SymmetricAlgebra.ι ℝ _ ∘ₗ
          BBoson.JetComponentSpace.repLorentzGroup Λ))]
  rw [show (1 : JetAlgebra) = (1 : ℂ ⊗[ℝ] BBoson.JetAlgebra) ⊗ₜ[ℂ]
      (1 : LeptonSinglet.JetAlgebra) from rfl,
    show repLorentzGroup Λ ((1 : ℂ ⊗[ℝ] BBoson.JetAlgebra) ⊗ₜ[ℂ]
        (1 : LeptonSinglet.JetAlgebra)) =
      BBoson.JetAlgebra.complexRepLorentzGroup Λ (1 : ℂ ⊗[ℝ] BBoson.JetAlgebra) ⊗ₜ[ℂ]
        LeptonSinglet.JetAlgebra.repLorentzGroup Λ (1 : LeptonSinglet.JetAlgebra)
      from rfl,
    h1, LeptonSinglet.JetAlgebra.repLorentzGroup_apply_one]

/-- Every element of `massDimFourInvariants` is gauge and Lorentz invariant. -/
lemma isInvariant_of_mem_massDimFourInvariants {x : JetAlgebra}
    (hx : x ∈ massDimFourInvariants) : IsInvariant x := by
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact ⟨fun U => (repJetGaugeGroupI_eq_repAlgHom U 1).trans (repAlgHom U).map_one,
      repLorentzGroup_one⟩
  · exact ⟨repJetGaugeGroupI_maxwellTerm, repLorentzGroup_maxwellTerm⟩
  · exact ⟨repJetGaugeGroupI_thetaTerm, repLorentzGroup_thetaTerm⟩
  · exact ⟨repJetGaugeGroupI_fermionKineticTerm, repLorentzGroup_fermionKineticTerm⟩
  · exact ⟨repJetGaugeGroupI_fermionKineticTermBar,
      repLorentzGroup_fermionKineticTermBar⟩

lemma span_massDimFourInvariants_le :
    Submodule.span ℂ massDimFourInvariants ≤ InvariantMassWeightSubmodule 8 := by
  rw [Submodule.span_le]
  intro x hx
  refine Submodule.mem_inf.mpr ⟨?_, Submodule.subset_span
    (isInvariant_of_mem_massDimFourInvariants hx)⟩
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact mem_massWeightLESubmodule_of_forall_massWeightScale (m := 0) (Nat.zero_le 8)
      fun c => by rw [pow_zero, one_smul]; exact (massWeightScale c).map_one
  · exact maxwellTerm_mem_massWeightLESubmodule
  · exact thetaTerm_mem_massWeightLESubmodule
  · exact fermionKineticTerm_mem_massWeightLESubmodule
  · exact fermionKineticTermBar_mem_massWeightLESubmodule

/-!

## Towards completeness: graded decomposition

The powers `c ↦ c ^ w` are linearly independent functions of `c`, so the
weight components of an element are unique: a vanishing combination of
eigenvectors weighted by powers has vanishing components, and every element of
the weight-`≤ n` submodule decomposes into exact-weight eigenvectors.

-/

/-- If a finite combination of vectors weighted by powers of `c` vanishes for
  all `c`, each component vanishes. -/
lemma eq_zero_of_forall_sum_pow_smul_eq_zero (s : Finset ℕ) (v : ℕ → JetAlgebra)
    (h : ∀ c : ℂ, ∑ w ∈ s, c ^ w • v w = 0) {w : ℕ} (hw : w ∈ s) : v w = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  have hp : ∀ c : ℂ, Polynomial.eval c
      (∑ u ∈ s, Polynomial.monomial u (φ (v u))) = 0 := by
    intro c
    have h2 := congrArg φ (h c)
    rw [map_sum, map_zero] at h2
    rw [Polynomial.eval_finsetSum]
    simpa [Polynomial.eval_monomial, mul_comm] using h2
  have hzero : (∑ u ∈ s, Polynomial.monomial u (φ (v u))) = 0 :=
    Polynomial.funext fun c => by rw [hp c, Polynomial.eval_zero]
  have hcoeff := congrArg (fun p => Polynomial.coeff p w) hzero
  rw [Polynomial.finsetSum_coeff] at hcoeff
  simpa [Polynomial.coeff_monomial, Finset.sum_ite_eq', hw] using hcoeff

/-- Every element of the weight-`≤ n` submodule is a sum of exact-weight
  eigenvectors of the mass-dimension scaling. -/
lemma exists_eigen_decomp_of_mem_massWeightLESubmodule {n : ℕ} {x : JetAlgebra}
    (hx : x ∈ MassWeightLESubmodule n) :
    ∃ z : ℕ → JetAlgebra,
      (∀ m, ∀ c : ℂ, massWeightScale c (z m) = c ^ m • z m) ∧
      x = ∑ m ∈ Finset.range (n + 1), z m := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨m, hmn, hym⟩ := hy
    refine ⟨fun k => if k = m then y else 0, fun k c => ?_, ?_⟩
    · by_cases hk : k = m
      · subst hk
        simpa using hym c
      · simp [hk]
    · rw [Finset.sum_ite_eq' (Finset.range (n + 1)) m fun _ => y,
        if_pos (Finset.mem_range.mpr (Nat.lt_succ_of_le hmn))]
  | zero =>
    exact ⟨fun _ => 0, by simp, by simp⟩
  | add a b ha hb iha ihb =>
    obtain ⟨z₁, hz₁, rfl⟩ := iha
    obtain ⟨z₂, hz₂, rfl⟩ := ihb
    refine ⟨z₁ + z₂, fun m c => ?_, ?_⟩
    · simp only [Pi.add_apply, map_add, hz₁ m c, hz₂ m c, smul_add]
    · rw [← Finset.sum_add_distrib]
      rfl
  | smul c a ha iha =>
    obtain ⟨z, hz, rfl⟩ := iha
    refine ⟨c • z, fun m c' => ?_, ?_⟩
    · simp only [Pi.smul_apply, map_smul, hz m c', smul_comm c]
    · rw [Finset.smul_sum]
      rfl

/-- The span of the covariant monomials of exact mass weight `w`: products of
  field-strength derivatives and covariant derivatives of total weight `w`. -/
noncomputable def covMonomialSpan (w : ℕ) : Submodule ℂ JetAlgebra :=
  Submodule.span ℂ {y | y ∈ Submonoid.closure invariantGenerators ∧
    ∀ c : ℂ, massWeightScale c y = c ^ w • y}

/-- Every covariant monomial is homogeneous. -/
lemma exists_weight_of_mem_closure {y : JetAlgebra}
    (hy : y ∈ Submonoid.closure invariantGenerators) :
    ∃ w, ∀ c : ℂ, massWeightScale c y = c ^ w • y := by
  induction hy using Submonoid.closure_induction with
  | mem z hz =>
    rcases hz with (⟨p, rfl⟩ | ⟨p, rfl⟩) | ⟨p, rfl⟩
    · exact ⟨4 + 2 * Multiset.card p.1,
        fun c => massWeightScale_fieldStrengthDeriv c p.1 p.2.1 p.2.2⟩
    · exact ⟨3 + 2 * p.1.length, fun c => massWeightScale_Dψ c p.1 p.2⟩
    · exact ⟨3 + 2 * p.1.length, fun c => massWeightScale_Dbarψ c p.1 p.2⟩
  | one =>
    exact ⟨0, fun c => by rw [pow_zero, one_smul]; exact (massWeightScale c).map_one⟩
  | mul a b ha hb iha ihb =>
    obtain ⟨wa, hwa⟩ := iha
    obtain ⟨wb, hwb⟩ := ihb
    exact ⟨wa + wb, massWeightScale_mul_eigen hwa hwb⟩

/-- Elements of the weight-`w` covariant monomial span are eigenvectors. -/
lemma forall_massWeightScale_of_mem_covMonomialSpan {w : ℕ} {y : JetAlgebra}
    (hy : y ∈ covMonomialSpan w) (c : ℂ) :
    massWeightScale c y = c ^ w • y := by
  induction hy using Submodule.span_induction with
  | mem z hz => exact hz.2 c
  | zero => simp
  | add a b ha hb iha ihb => rw [map_add, iha, ihb, smul_add]
  | smul d a ha iha => rw [map_smul, iha, smul_comm]

/-- A vanishing tail extends a truncated sum. -/
lemma sum_range_succ_ext {N M : ℕ} (z : ℕ → JetAlgebra) (hNM : N ≤ M)
    (hz : ∀ m, N < m → z m = 0) :
    ∑ m ∈ Finset.range (N + 1), z m = ∑ m ∈ Finset.range (M + 1), z m := by
  refine Finset.sum_subset ?_ ?_
  · intro m hm
    simp only [Finset.mem_range] at hm ⊢
    omega
  intro m hm hms
  refine hz m ?_
  simp only [Finset.mem_range] at hm hms
  omega

/-- Every element of the algebra generated by the covariant generators
  decomposes into covariant monomial components of bounded weight. -/
lemma exists_bound_decomp_of_mem_adjoin {x : JetAlgebra}
    (hadj : x ∈ Algebra.adjoin ℂ invariantGenerators) :
    ∃ (N : ℕ) (z : ℕ → JetAlgebra), (∀ m, z m ∈ covMonomialSpan m) ∧
      (∀ m, N < m → z m = 0) ∧ x = ∑ m ∈ Finset.range (N + 1), z m := by
  have hx' : x ∈ Subalgebra.toSubmodule (Algebra.adjoin ℂ invariantGenerators) := hadj
  rw [Algebra.adjoin_eq_span] at hx'
  clear hadj
  induction hx' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw⟩ := exists_weight_of_mem_closure hy
    refine ⟨w, fun k => if k = w then y else 0, fun k => ?_, fun k hk => ?_, ?_⟩
    · by_cases hkw : k = w
      · subst hkw
        show (if k = k then y else 0) ∈ covMonomialSpan k
        rw [if_pos rfl]
        exact Submodule.subset_span ⟨hy, hw⟩
      · show (if k = w then y else 0) ∈ covMonomialSpan k
        rw [if_neg hkw]
        exact Submodule.zero_mem _
    · show (if k = w then y else 0) = 0
      rw [if_neg (show ¬ k = w by omega)]
    · show y = ∑ m ∈ Finset.range (w + 1), (if m = w then y else 0)
      rw [Finset.sum_ite_eq' (Finset.range (w + 1)) w fun _ => y,
        if_pos (Finset.mem_range.mpr (Nat.lt_succ_self w))]
  | zero =>
    exact ⟨0, fun _ => 0, fun m => Submodule.zero_mem _, fun _ _ => rfl, by simp⟩
  | add a b ha hb iha ihb =>
    obtain ⟨N₁, z₁, hz₁, hs₁, rfl⟩ := iha
    obtain ⟨N₂, z₂, hz₂, hs₂, rfl⟩ := ihb
    refine ⟨max N₁ N₂, z₁ + z₂, fun m => Submodule.add_mem _ (hz₁ m) (hz₂ m),
      fun m hm => ?_, ?_⟩
    · simp only [Pi.add_apply, hs₁ m (lt_of_le_of_lt (le_max_left _ _) hm),
        hs₂ m (lt_of_le_of_lt (le_max_right _ _) hm), add_zero]
    · rw [sum_range_succ_ext z₁ (le_max_left N₁ N₂) hs₁,
        sum_range_succ_ext z₂ (le_max_right N₁ N₂) hs₂,
        ← Finset.sum_add_distrib]
      rfl
  | smul c a ha iha =>
    obtain ⟨N, z, hz, hs, rfl⟩ := iha
    refine ⟨N, c • z, fun m => Submodule.smul_mem _ _ (hz m),
      fun m hm => ?_, ?_⟩
    · simp only [Pi.smul_apply, hs m hm, smul_zero]
    · rw [Finset.smul_sum]
      rfl

/-- The master decomposition: an element of the adjoin of the covariant
  generators of mass weight at most eight is a sum of nine covariant monomial
  components of weights `0, …, 8`. -/
lemma exists_covMonomialSpan_decomp {x : JetAlgebra}
    (hx : x ∈ MassWeightLESubmodule 8)
    (hadj : x ∈ Algebra.adjoin ℂ invariantGenerators) :
    ∃ z : ℕ → JetAlgebra, (∀ m, z m ∈ covMonomialSpan m) ∧
      x = ∑ m ∈ Finset.range 9, z m := by
  obtain ⟨N, z, hzmem, hzsupp, hzx⟩ := exists_bound_decomp_of_mem_adjoin hadj
  obtain ⟨z', hz'eig, hz'x⟩ := exists_eigen_decomp_of_mem_massWeightLESubmodule hx
  refine ⟨z, hzmem, ?_⟩
  set M := max N 8 with hM
  have h1 : x = ∑ m ∈ Finset.range (M + 1), z m :=
    hzx.trans (sum_range_succ_ext z (le_max_left N 8) hzsupp)
  have hz'supp : ∀ m, 8 < m → (fun k => if k < 9 then z' k else 0) m = 0 := by
    intro m hm
    show (if m < 9 then z' m else 0) = 0
    rw [if_neg (show ¬ m < 9 by omega)]
  have h2 : x = ∑ m ∈ Finset.range (M + 1), (fun k => if k < 9 then z' k else 0) m := by
    rw [hz'x, show (9 : ℕ) = 8 + 1 from rfl,
      ← sum_range_succ_ext _ (le_max_right N 8) hz'supp]
    exact Finset.sum_congr rfl fun m hm => by
      rw [if_pos (Finset.mem_range.mp hm)]
  have hdiff : ∀ c : ℂ, ∑ m ∈ Finset.range (M + 1),
      c ^ m • (z m - (fun k => if k < 9 then z' k else 0) m) = 0 := by
    intro c
    have e1 : massWeightScale c x = ∑ m ∈ Finset.range (M + 1), c ^ m • z m := by
      rw [h1, map_sum]
      exact Finset.sum_congr rfl fun m _ =>
        forall_massWeightScale_of_mem_covMonomialSpan (hzmem m) c
    have e2 : massWeightScale c x = ∑ m ∈ Finset.range (M + 1),
        c ^ m • (fun k => if k < 9 then z' k else 0) m := by
      rw [h2, map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      by_cases hm : m < 9
      · simp only [if_pos hm]
        exact hz'eig m c
      · simp only [if_neg hm, map_zero, smul_zero]
    calc ∑ m ∈ Finset.range (M + 1),
        c ^ m • (z m - (fun k => if k < 9 then z' k else 0) m)
        = (∑ m ∈ Finset.range (M + 1), c ^ m • z m) -
          ∑ m ∈ Finset.range (M + 1),
            c ^ m • (fun k => if k < 9 then z' k else 0) m := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun m _ => smul_sub _ _ _
      _ = massWeightScale c x - massWeightScale c x := by rw [← e1, ← e2]
      _ = 0 := sub_self _
  have hkill : ∀ m, 8 < m → z m = 0 := by
    intro m hm
    by_cases hmM : m ≤ M
    · have h0 : z m - (fun k => if k < 9 then z' k else 0) m = 0 :=
        eq_zero_of_forall_sum_pow_smul_eq_zero (Finset.range (M + 1)) _ hdiff
          (show m ∈ Finset.range (M + 1) from Finset.mem_range.mpr (by omega))
      simpa [if_neg (by omega : ¬ m < 9)] using h0
    · exact hzsupp m (by omega)
  rw [h1, show (9 : ℕ) = 8 + 1 from rfl, sum_range_succ_ext z (le_max_right N 8) hkill]

/-!

## Componentwise invariance

The scaling at real scalars commutes with the Lorentz action and (at all
scalars) with the constant gauge action, so the weight components of an
invariant element are themselves invariant.

-/

/-- The mass-dimension scaling at a real scalar commutes with the Lorentz
  action on the QED jet algebra. -/
lemma massWeightScale_ofReal_repLorentzGroup (r : ℝ) (Λ : SL(2,ℂ))
    (x : JetAlgebra) :
    massWeightScale (r : ℂ) (repLorentzGroup Λ x) =
      repLorentzGroup Λ (massWeightScale (r : ℂ) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul p l =>
    have hLS : LeptonSinglet.JetAlgebra.massWeightScale (r : ℂ)
        (LeptonSinglet.JetAlgebra.repLorentzGroup Λ l) =
        LeptonSinglet.JetAlgebra.repLorentzGroup Λ
          (LeptonSinglet.JetAlgebra.massWeightScale (r : ℂ) l) :=
      DFunLike.congr_fun
        (LeptonSinglet.JetAlgebra.massWeightScale_repLorentzGroup (r : ℂ) Λ) l
    have h1 : ∀ (p' : ℂ ⊗[ℝ] BBoson.JetAlgebra) (l' : LeptonSinglet.JetAlgebra),
        massWeightScale (r : ℂ) (p' ⊗ₜ[ℂ] l') =
          (BBoson.JetAlgebra.massWeightScale (r : ℂ) p') ⊗ₜ[ℂ]
            (LeptonSinglet.JetAlgebra.massWeightScale (r : ℂ) l') :=
      fun p' l' => rfl
    have h2 : ∀ (p' : ℂ ⊗[ℝ] BBoson.JetAlgebra) (l' : LeptonSinglet.JetAlgebra),
        repLorentzGroup Λ (p' ⊗ₜ[ℂ] l') =
          (BBoson.JetAlgebra.complexRepLorentzGroup Λ p') ⊗ₜ[ℂ]
            (LeptonSinglet.JetAlgebra.repLorentzGroup Λ l') := fun p' l' => rfl
    rw [h2, h1, BBoson.JetAlgebra.massWeightScale_ofReal_complexRepLorentzGroup,
      hLS, h1, h2]

/-- The mass-dimension scaling commutes with the constant gauge action on the
  QED jet algebra. -/
lemma massWeightScale_repJetGaugeGroupI_ofConstant (c : ℂ) (g : GaugeGroupI)
    (x : JetAlgebra) :
    massWeightScale c (repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) x) =
      repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) (massWeightScale c x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul p l =>
    have hLS : LeptonSinglet.JetAlgebra.massWeightScale c
        (LeptonSinglet.JetAlgebra.repJetGaugeGroupI
          (JetGaugeGroupI.ofConstant g) l) =
        LeptonSinglet.JetAlgebra.repJetGaugeGroupI (JetGaugeGroupI.ofConstant g)
          (LeptonSinglet.JetAlgebra.massWeightScale c l) :=
      DFunLike.congr_fun
        (LeptonSinglet.JetAlgebra.massWeightScale_repJetGaugeGroupI_ofConstant c g) l
    have h1 : ∀ (p' : ℂ ⊗[ℝ] BBoson.JetAlgebra) (l' : LeptonSinglet.JetAlgebra),
        massWeightScale c (p' ⊗ₜ[ℂ] l') =
          (BBoson.JetAlgebra.massWeightScale c p') ⊗ₜ[ℂ]
            (LeptonSinglet.JetAlgebra.massWeightScale c l') := fun p' l' => rfl
    have h2 : ∀ (p' : ℂ ⊗[ℝ] BBoson.JetAlgebra) (l' : LeptonSinglet.JetAlgebra),
        repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) (p' ⊗ₜ[ℂ] l') =
          (BBoson.JetAlgebra.complexRepJetGaugeGroupI
            (JetGaugeGroupI.ofConstant g) p') ⊗ₜ[ℂ]
            (LeptonSinglet.JetAlgebra.repJetGaugeGroupI
              (JetGaugeGroupI.ofConstant g) l') := fun p' l' => rfl
    rw [h2, BBoson.JetAlgebra.complexRepJetGaugeGroupI_ofConstant, h1, hLS, h1, h2,
      BBoson.JetAlgebra.complexRepJetGaugeGroupI_ofConstant]

/-- Real-scalar variant of the independence of powers. -/
lemma eq_zero_of_forall_ofReal_sum_pow_smul_eq_zero (s : Finset ℕ)
    (v : ℕ → JetAlgebra)
    (h : ∀ r : ℝ, ∑ w ∈ s, ((r : ℂ)) ^ w • v w = 0) {w : ℕ} (hw : w ∈ s) :
    v w = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  have hp : ∀ r : ℝ, Polynomial.eval ((r : ℂ))
      (∑ u ∈ s, Polynomial.monomial u (φ (v u))) = 0 := by
    intro r
    have h2 := congrArg φ (h r)
    rw [map_sum, map_zero] at h2
    rw [Polynomial.eval_finsetSum]
    simpa [Polynomial.eval_monomial, mul_comm] using h2
  have hzero : (∑ u ∈ s, Polynomial.monomial u (φ (v u))) = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot _ ?_
    refine Set.Infinite.mono ?_
      (Set.infinite_range_of_injective Complex.ofReal_injective)
    rintro z ⟨r, rfl⟩
    exact hp r
  have hcoeff := congrArg (fun p => Polynomial.coeff p w) hzero
  rw [Polynomial.finsetSum_coeff] at hcoeff
  simpa [Polynomial.coeff_monomial, Finset.sum_ite_eq', hw] using hcoeff

/-- The weight components of a Lorentz-invariant covariant decomposition are
  Lorentz invariant. -/
lemma repLorentzGroup_covComponent_eq {z : ℕ → JetAlgebra}
    (hz : ∀ m, z m ∈ covMonomialSpan m) (Λ : SL(2,ℂ))
    (hx : repLorentzGroup Λ (∑ m ∈ Finset.range 9, z m) =
      ∑ m ∈ Finset.range 9, z m)
    {m : ℕ} (hm : m ∈ Finset.range 9) :
    repLorentzGroup Λ (z m) = z m := by
  have hv : ∀ r : ℝ, ∑ k ∈ Finset.range 9,
      ((r : ℂ)) ^ k • (repLorentzGroup Λ (z k) - z k) = 0 := by
    intro r
    have e1 : massWeightScale ((r : ℂ))
        (repLorentzGroup Λ (∑ k ∈ Finset.range 9, z k) -
          ∑ k ∈ Finset.range 9, z k) = 0 := by
      rw [hx, sub_self, map_zero]
    rw [map_sum, map_sub, map_sum, map_sum] at e1
    calc ∑ k ∈ Finset.range 9, ((r : ℂ)) ^ k •
          (repLorentzGroup Λ (z k) - z k)
        = (∑ k ∈ Finset.range 9, massWeightScale ((r : ℂ))
            (repLorentzGroup Λ (z k))) -
          ∑ k ∈ Finset.range 9, massWeightScale ((r : ℂ)) (z k) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [massWeightScale_ofReal_repLorentzGroup,
            forall_massWeightScale_of_mem_covMonomialSpan (hz k), map_smul,
            smul_sub]
      _ = 0 := e1
  have h0 := eq_zero_of_forall_ofReal_sum_pow_smul_eq_zero _ _ hv hm
  rwa [sub_eq_zero] at h0

/-- The weight components of a constant-gauge-invariant covariant decomposition
  are constant-gauge invariant. -/
lemma repJetGaugeGroupI_ofConstant_covComponent_eq {z : ℕ → JetAlgebra}
    (hz : ∀ m, z m ∈ covMonomialSpan m) (g : GaugeGroupI)
    (hx : repJetGaugeGroupI (JetGaugeGroupI.ofConstant g)
        (∑ m ∈ Finset.range 9, z m) = ∑ m ∈ Finset.range 9, z m)
    {m : ℕ} (hm : m ∈ Finset.range 9) :
    repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) (z m) = z m := by
  have hv : ∀ r : ℝ, ∑ k ∈ Finset.range 9, ((r : ℂ)) ^ k •
      (repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) (z k) - z k) = 0 := by
    intro r
    have e1 : massWeightScale ((r : ℂ))
        (repJetGaugeGroupI (JetGaugeGroupI.ofConstant g)
          (∑ k ∈ Finset.range 9, z k) - ∑ k ∈ Finset.range 9, z k) = 0 := by
      rw [hx, sub_self, map_zero]
    rw [map_sum, map_sub, map_sum, map_sum] at e1
    calc ∑ k ∈ Finset.range 9, ((r : ℂ)) ^ k •
          (repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) (z k) - z k)
        = (∑ k ∈ Finset.range 9, massWeightScale ((r : ℂ))
            (repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) (z k))) -
          ∑ k ∈ Finset.range 9, massWeightScale ((r : ℂ)) (z k) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [massWeightScale_repJetGaugeGroupI_ofConstant,
            forall_massWeightScale_of_mem_covMonomialSpan (hz k), map_smul,
            smul_sub]
      _ = 0 := e1
  have h0 := eq_zero_of_forall_ofReal_sum_pow_smul_eq_zero _ _ hv hm
  rwa [sub_eq_zero] at h0

/-!

## The low-weight sectors

-/

/-- An element with two distinct exact weights vanishes. -/
lemma eq_zero_of_eigen_ne {y : JetAlgebra} {m n : ℕ}
    (hm : ∀ c : ℂ, massWeightScale c y = c ^ m • y)
    (hn : ∀ c : ℂ, massWeightScale c y = c ^ n • y) (hmn : m ≠ n) : y = 0 := by
  have h : ((2 : ℂ) ^ m) • y = ((2 : ℂ) ^ n) • y := (hm 2).symm.trans (hn 2)
  have h2 : ((2 : ℂ) ^ m - 2 ^ n) • y = 0 :=
    (sub_smul ((2 : ℂ) ^ m) ((2 : ℂ) ^ n) y).trans (by rw [h, sub_self])
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exfalso
    apply hmn
    rw [sub_eq_zero] at h3
    have h4 : ((2 ^ m : ℕ) : ℂ) = ((2 ^ n : ℕ) : ℂ) := by
      push_cast
      exact h3
    exact Nat.pow_right_injective (le_refl 2) (Nat.cast_injective h4)
  · exact h3

/-- Every covariant monomial is the unit or homogeneous of weight at least
  three. -/
lemma mem_closure_weight_cases {y : JetAlgebra}
    (hy : y ∈ Submonoid.closure invariantGenerators) :
    y = 1 ∨ ∃ w, 3 ≤ w ∧ ∀ c : ℂ, massWeightScale c y = c ^ w • y := by
  induction hy using Submonoid.closure_induction with
  | mem z hz =>
    rcases hz with (⟨p, rfl⟩ | ⟨p, rfl⟩) | ⟨p, rfl⟩
    · exact Or.inr ⟨4 + 2 * Multiset.card p.1, by omega,
        fun c => massWeightScale_fieldStrengthDeriv c p.1 p.2.1 p.2.2⟩
    · exact Or.inr ⟨3 + 2 * p.1.length, by omega,
        fun c => massWeightScale_Dψ c p.1 p.2⟩
    · exact Or.inr ⟨3 + 2 * p.1.length, by omega,
        fun c => massWeightScale_Dbarψ c p.1 p.2⟩
  | one => exact Or.inl rfl
  | mul a b ha hb iha ihb =>
    rcases iha with rfl | ⟨wa, hwa3, hwa⟩
    · rcases ihb with rfl | ⟨wb, hwb3, hwb⟩
      · exact Or.inl (one_mul (1 : JetAlgebra))
      · exact Or.inr ⟨wb, hwb3, fun c => by
          rw [show (1 : JetAlgebra) * b = b from one_mul b]
          exact hwb c⟩
    · rcases ihb with rfl | ⟨wb, hwb3, hwb⟩
      · exact Or.inr ⟨wa, hwa3, fun c => by
          rw [show a * (1 : JetAlgebra) = a from mul_one a]
          exact hwa c⟩
      · exact Or.inr ⟨wa + wb, by omega, massWeightScale_mul_eigen hwa hwb⟩

/-- The weight-zero covariant monomial span consists of the constants. -/
lemma covMonomialSpan_zero_le :
    covMonomialSpan 0 ≤ Submodule.span ℂ {(1 : JetAlgebra)} := by
  rw [covMonomialSpan, Submodule.span_le]
  rintro y ⟨hy, hy0⟩
  rcases mem_closure_weight_cases hy with rfl | ⟨w, hw3, hwe⟩
  · exact Submodule.subset_span rfl
  · rw [show y = 0 from eq_zero_of_eigen_ne hwe hy0 (by omega)]
    exact Submodule.zero_mem _

/-- There are no covariant monomials of weights one or two. -/
lemma covMonomialSpan_le_bot_of_lt_three {m : ℕ} (hm1 : 1 ≤ m) (hm2 : m < 3) :
    covMonomialSpan m ≤ ⊥ := by
  rw [covMonomialSpan, Submodule.span_le]
  rintro y ⟨hy, hym⟩
  rcases mem_closure_weight_cases hy with rfl | ⟨w, hw3, hwe⟩
  · have h1 : ∀ c : ℂ, massWeightScale c (1 : JetAlgebra) = c ^ 0 • 1 :=
      fun c => by rw [pow_zero, one_smul]; exact (massWeightScale c).map_one
    have := eq_zero_of_eigen_ne h1 hym (by omega)
    simp [this]
  · rw [show y = 0 from eq_zero_of_eigen_ne hwe hym (by omega)]
    simp

/-!

## The parity selection rule

Every covariant monomial is an eigenvector of the constant gauge action with a
hypercharge character whose parity equals that of its mass weight: bosonic
generators have even weight and charge zero, fermionic generators odd weight
and charge `±6`. The constant gauge transformation with `u(0) = i` therefore
acts on odd-weight monomials by `-1`, and no odd-weight sector contains a
gauge invariant.

-/

/-- Every covariant monomial is an eigenvector of the constant gauge action,
  with character exponent of the same parity as its mass weight. -/
lemma rep_ofConstant_eigen_of_mem_closure {y : JetAlgebra}
    (hy : y ∈ Submonoid.closure invariantGenerators) :
    ∃ (w : ℕ) (k : ℤ), k.natAbs ≤ w ∧ (w : ℤ) % 2 = k % 2 ∧
      (∀ c : ℂ, massWeightScale c y = c ^ w • y) ∧
      ∀ g : GaugeGroupI, repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) y =
        (((g.2.2 : ℂ)) ^ (6 * k)) • y := by
  have hz : ∀ g : GaugeGroupI, ((g.2.2 : ℂ)) ≠ 0 := by
    intro g h
    have h1 := (Unitary.mem_iff.mp (g.2.2).2).1
    rw [h, mul_zero] at h1
    exact zero_ne_one h1
  induction hy using Submonoid.closure_induction with
  | mem z hzz =>
    rcases hzz with (⟨p, rfl⟩ | ⟨p, rfl⟩) | ⟨p, rfl⟩
    · refine ⟨4 + 2 * Multiset.card p.1, 0, by simp, by omega,
        fun c => massWeightScale_fieldStrengthDeriv c p.1 p.2.1 p.2.2, fun g => ?_⟩
      rw [repJetGaugeGroupI_fieldStrengthDeriv, mul_zero, zpow_zero, one_smul]
    · refine ⟨3 + 2 * p.1.length, 1, by omega, by omega,
        fun c => massWeightScale_Dψ c p.1 p.2, fun g => ?_⟩
      rw [repJetGaugeGroupI_Dψ, JetGaugeGroupI.eval_ofConstant, Submonoid.smul_def,
        SubmonoidClass.coe_pow, mul_one,
        show ((g.2.2 : ℂ)) ^ (6 : ℤ) = ((g.2.2 : ℂ)) ^ (6 : ℕ) from zpow_natCast _ 6]
    · refine ⟨3 + 2 * p.1.length, -1, by omega, by omega,
        fun c => massWeightScale_Dbarψ c p.1 p.2, fun g => ?_⟩
      rw [repJetGaugeGroupI_Dbarψ, JetGaugeGroupI.eval_ofConstant,
        Submonoid.smul_def, SubmonoidClass.coe_pow, Unitary.coe_star]
      congr 1
      have hinv : star ((g.2.2 : ℂ)) = ((g.2.2 : ℂ))⁻¹ :=
        eq_inv_of_mul_eq_one_left (Unitary.mem_iff.mp (g.2.2).2).1
      rw [hinv, show (6 : ℤ) * (-1) = -(6 : ℤ) from by ring, _root_.zpow_neg,
        show ((g.2.2 : ℂ)) ^ (6 : ℤ) = ((g.2.2 : ℂ)) ^ (6 : ℕ) from zpow_natCast _ 6]
      exact inv_pow _ 6
  | one =>
    refine ⟨0, 0, by simp, rfl, fun c => by
        rw [pow_zero, one_smul]; exact (massWeightScale c).map_one, fun g => ?_⟩
    rw [mul_zero, zpow_zero, one_smul]
    exact (repJetGaugeGroupI_eq_repAlgHom _ 1).trans
      (repAlgHom (JetGaugeGroupI.ofConstant g)).map_one
  | mul a b ha hb iha ihb =>
    obtain ⟨wa, ka, hba, hpa, hea, hga⟩ := iha
    obtain ⟨wb, kb, hbb, hpb, heb, hgb⟩ := ihb
    refine ⟨wa + wb, ka + kb, by
        have := Int.natAbs_add_le ka kb
        omega, by omega, massWeightScale_mul_eigen hea heb, fun g => ?_⟩
    rw [repJetGaugeGroupI_mul', hga g, hgb g, smul_mul_smul_comm,
      show (6 : ℤ) * (ka + kb) = 6 * ka + 6 * kb from by ring,
      zpow_add₀ (hz g)]

/-- The constant gauge transformation with `u(0) = i`. -/
noncomputable def parityGauge : GaugeGroupI :=
  (1, 1, ⟨Complex.I, by
    rw [Unitary.mem_iff]
    constructor <;>
      simp [Complex.star_def, Complex.conj_I]⟩)

/-- The parity gauge transformation acts by `-1` on every odd-weight covariant
  monomial. -/
lemma rep_parityGauge_eq_neg_of_mem_covMonomialSpan {m : ℕ} (hm : m % 2 = 1)
    {y : JetAlgebra} (hy : y ∈ covMonomialSpan m) :
    repJetGaugeGroupI (JetGaugeGroupI.ofConstant parityGauge) y = -y := by
  induction hy using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨hu1, hu2⟩ := hu
    obtain ⟨w, k, hb, hp, he, hg⟩ := rep_ofConstant_eigen_of_mem_closure hu1
    by_cases hu0 : u = 0
    · rw [hu0, map_zero, neg_zero]
    · have hwm : w = m := by
        by_contra hne
        exact hu0 (eq_zero_of_eigen_ne he hu2 hne)
      have hkodd : Odd k := by
        rw [Int.odd_iff]
        omega
      rw [hg parityGauge,
        show ((parityGauge.2.2 : ℂ)) = Complex.I from rfl,
        show (6 : ℤ) * k = 2 * (3 * k) from by ring, _root_.zpow_mul,
        show Complex.I ^ (2 : ℤ) = -1 from by
          rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, Complex.I_sq],
        show (-1 : ℂ) ^ (3 * k) = -1 from Odd.neg_one_zpow (by
          rcases hkodd with ⟨j, hj⟩
          exact ⟨3 * j + 1, by omega⟩)]
      exact neg_one_smul ℂ u
  | zero => rw [map_zero, neg_zero]
  | add u v hu hv ihu ihv => rw [map_add, ihu, ihv, neg_add]
  | smul c u hu ihu => rw [map_smul, ihu, smul_neg]

/-- Odd-weight covariant monomial spans contain no constant-gauge
  invariants. -/
lemma eq_zero_of_mem_covMonomialSpan_odd {m : ℕ} (hm : m % 2 = 1)
    {y : JetAlgebra} (hy : y ∈ covMonomialSpan m)
    (hinv : repJetGaugeGroupI (JetGaugeGroupI.ofConstant parityGauge) y = y) :
    y = 0 := by
  have h := (rep_parityGauge_eq_neg_of_mem_covMonomialSpan hm hy).symm.trans hinv
  have h2 : (2 : ℂ) • y = 0 := by
    calc (2 : ℂ) • y = y + y := two_smul ℂ y
      _ = -y + y := congrArg (· + y) h.symm
      _ = 0 := neg_add_cancel y
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 two_ne_zero
  · exact h3

/-!

## The master selection rules

An invariant which is also an eigenvector with a nontrivial eigenvalue must
vanish. Specialized to the constant gauge action at a root of unity this is the
hypercharge selection rule; specialized to diagonal Lorentz transformations it
kills the non-scalar Lorentz components.

-/

/-- The master selection rule: an element that scales by a factor other than
  one vanishes. -/
lemma eq_zero_of_eq_smul_of_ne_one {y : JetAlgebra} {c : ℂ}
    (h1 : y = c • y) (hc : c ≠ 1) : y = 0 := by
  have h2 : (c - 1) • y = 0 :=
    (sub_smul c 1 y).trans (by rw [one_smul, ← h1, sub_self])
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) hc
  · exact h3

/-- The unit-circle exponential is unitary. -/
lemma exp_mul_I_mem_unitary (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) ∈ unitary ℂ := by
  have hstar : star (Complex.exp ((θ : ℂ) * Complex.I)) =
      Complex.exp (-((θ : ℂ) * Complex.I)) := by
    rw [show star (Complex.exp ((θ : ℂ) * Complex.I)) =
        (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I)) from rfl,
      ← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal]
  rw [Unitary.mem_iff]
  constructor
  · rw [hstar, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  · rw [hstar, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

/-- The constant `U(1)` gauge transformation at a unitary scalar. -/
noncomputable def u1Gauge (z : ℂ) (hz : z ∈ unitary ℂ) : GaugeGroupI :=
  (1, 1, ⟨z, hz⟩)

/-- The hypercharge selection rule: a constant-gauge eigenvector of nonzero
  charge admits no invariant. -/
lemma eq_zero_of_charge_ne_zero {y : JetAlgebra} {k : ℤ} (hk : k ≠ 0)
    (hy : ∀ g : GaugeGroupI, repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) y =
      ((g.2.2 : ℂ)) ^ (6 * k) • y)
    (hinv : ∀ g : GaugeGroupI,
      repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) y = y) : y = 0 := by
  have h6k : ((6 * k : ℤ) : ℝ) ≠ 0 := by
    simp only [ne_eq, Int.cast_eq_zero]
    omega
  set θ : ℝ := Real.pi / ((6 * k : ℤ) : ℝ) with hθ
  set g : GaugeGroupI := u1Gauge (Complex.exp ((θ : ℂ) * Complex.I))
    (exp_mul_I_mem_unitary θ) with hg
  have hval : ((g.2.2 : ℂ)) = Complex.exp ((θ : ℂ) * Complex.I) := rfl
  have hchar : ((g.2.2 : ℂ)) ^ (6 * k) = -1 := by
    rw [hval, ← Complex.exp_int_mul,
      show ((6 * k : ℤ) : ℂ) * ((θ : ℂ) * Complex.I) =
        (((6 * k : ℤ) : ℝ) * θ : ℝ) * Complex.I from by push_cast; ring,
      show ((6 * k : ℤ) : ℝ) * θ = Real.pi from mul_div_cancel₀ Real.pi h6k ▸ rfl]
    exact Complex.exp_pi_mul_I
  exact eq_zero_of_eq_smul_of_ne_one
    ((hinv g).symm.trans ((hy g).trans (by rw [hchar])))
    (by
      intro h
      norm_num at h)

/-!

## Charge decomposition

The constant gauge characters at distinct charges are linearly independent
along the unit circle, so every element of a weight sector decomposes into
charge components, and a constant-gauge invariant equals its neutral component.

-/

/-- The unit-circle exponentials are injective on `(0, 1)`. -/
lemma exp_mul_I_injOn :
    Set.InjOn (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I))
      (Set.Ioo (0 : ℝ) 1) := by
  intro a ha b hb hab
  rcases Complex.exp_eq_exp_iff_exists_int.mp hab with ⟨n, hn⟩
  have h2 : (a : ℂ) = (b : ℂ) + (n : ℂ) * (2 * (Real.pi : ℂ)) := by
    have h1 : (a : ℂ) * Complex.I =
        ((b : ℂ) + (n : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by
      rw [hn]
      ring
    exact mul_right_cancel₀ Complex.I_ne_zero h1
  have h3 : a = b + (n : ℝ) * (2 * Real.pi) := by exact_mod_cast h2
  have hn0 : n = 0 := by
    by_contra hne
    have h4 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hne
    have hπ : (2 : ℝ) ≤ Real.pi := Real.two_le_pi
    have h5 : |a - b| < 1 := by
      rw [abs_sub_lt_iff]
      constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]
    rw [h3] at h5
    simp only [add_sub_cancel_left] at h5
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h5
    nlinarith
  rw [hn0] at h3
  push_cast at h3
  linarith

/-- Independence of the circle characters: a finite Laurent combination
  vanishing on the unit circle has vanishing coefficients. -/
lemma eq_zero_of_forall_circle_sum_zpow_smul_eq_zero (s : Finset ℤ)
    (v : ℤ → JetAlgebra)
    (h : ∀ θ : ℝ, ∑ j ∈ s, (Complex.exp ((θ : ℂ) * Complex.I)) ^ j • v j = 0)
    {k : ℤ} (hk : k ∈ s) : v k = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  have hne : s.Nonempty := ⟨k, hk⟩
  set n₀ : ℤ := -s.min' hne with hn₀
  have hshift : ∀ j ∈ s, 0 ≤ j + n₀ := fun j hj => by
    have := s.min'_le j hj
    omega
  have heval : ∀ θ : ℝ, Polynomial.eval (Complex.exp ((θ : ℂ) * Complex.I))
      (∑ j ∈ s, Polynomial.monomial (j + n₀).toNat (φ (v j))) = 0 := by
    intro θ
    have hz0 : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    have h2 := congrArg φ (h θ)
    rw [map_sum, map_zero] at h2
    have h3 : ∑ j ∈ s, Complex.exp ((θ : ℂ) * Complex.I) ^ j * φ (v j) = 0 := by
      rw [← h2]
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul]; rfl
    have h4 : Complex.exp ((θ : ℂ) * Complex.I) ^ n₀ *
        ∑ j ∈ s, Complex.exp ((θ : ℂ) * Complex.I) ^ j * φ (v j) = 0 := by
      rw [h3, mul_zero]
    rw [Finset.mul_sum] at h4
    rw [Polynomial.eval_finsetSum, ← h4]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Polynomial.eval_monomial,
      show Complex.exp ((θ : ℂ) * Complex.I) ^ (j + n₀).toNat =
        Complex.exp ((θ : ℂ) * Complex.I) ^ ((j + n₀) : ℤ) from by
        rw [← zpow_natCast, Int.toNat_of_nonneg (hshift j hj)],
      zpow_add₀ hz0]
    ring
  have hzero : (∑ j ∈ s, Polynomial.monomial (j + n₀).toNat (φ (v j))) = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot _ ?_
    refine Set.Infinite.mono ?_
      ((Set.Ioo_infinite (by norm_num : (0 : ℝ) < 1)).image exp_mul_I_injOn)
    rintro z ⟨θ, _, rfl⟩
    exact heval θ
  have hcoeff := congrArg (fun p => Polynomial.coeff p (k + n₀).toNat) hzero
  rw [Polynomial.finsetSum_coeff] at hcoeff
  rw [Finset.sum_eq_single k
    (fun j hj hjk => by
      rw [Polynomial.coeff_monomial, if_neg (fun heq => hjk (by
        have h1 : j + n₀ = k + n₀ := by
          rw [← Int.toNat_of_nonneg (hshift j hj),
            ← Int.toNat_of_nonneg (hshift k hk), heq]
        omega))])
    (fun hks => absurd hk hks)] at hcoeff
  simpa [Polynomial.coeff_monomial] using hcoeff

/-- The charge-`6k` part of a weight sector: the span of the covariant
  monomials of weight `m` and hypercharge `6 k`. -/
noncomputable def chargeCovSpan (m : ℕ) (k : ℤ) : Submodule ℂ JetAlgebra :=
  Submodule.span ℂ {y | y ∈ Submonoid.closure invariantGenerators ∧
    (∀ c : ℂ, massWeightScale c y = c ^ m • y) ∧
    ∀ g : GaugeGroupI, repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) y =
      ((g.2.2 : ℂ)) ^ (6 * k) • y}

/-- Elements of the charge component are eigenvectors of the constant gauge
  action. -/
lemma forall_rep_ofConstant_of_mem_chargeCovSpan {m : ℕ} {k : ℤ}
    {y : JetAlgebra} (hy : y ∈ chargeCovSpan m k) (g : GaugeGroupI) :
    repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) y =
      ((g.2.2 : ℂ)) ^ (6 * k) • y := by
  induction hy using Submodule.span_induction with
  | mem u hu => exact hu.2.2 g
  | zero => simp
  | add a b ha hb iha ihb => rw [map_add, iha, ihb, smul_add]
  | smul c a ha iha => rw [map_smul, iha, smul_comm]

/-- The charge components sit inside the weight sector. -/
lemma chargeCovSpan_le_covMonomialSpan {m : ℕ} {k : ℤ} :
    chargeCovSpan m k ≤ covMonomialSpan m :=
  Submodule.span_mono fun y hy => ⟨hy.1, hy.2.1⟩

/-- Charge decomposition within a weight sector. -/
lemma exists_charge_decomp_of_mem_covMonomialSpan {m : ℕ} {y : JetAlgebra}
    (hy : y ∈ covMonomialSpan m) :
    ∃ v : ℤ → JetAlgebra, (∀ j, v j ∈ chargeCovSpan m j) ∧
      y = ∑ j ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), v j := by
  induction hy using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨hu1, hu2⟩ := hu
    obtain ⟨w, k, hb, hp, he, hg⟩ := rep_ofConstant_eigen_of_mem_closure hu1
    by_cases hu0 : u = 0
    · exact ⟨fun _ => 0, fun j => Submodule.zero_mem _, by simp [hu0]⟩
    · have hwm : w = m := by
        by_contra hne
        exact hu0 (eq_zero_of_eigen_ne he hu2 hne)
      have hkm : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) := by
        rw [Finset.mem_Icc]
        omega
      refine ⟨fun j => if j = k then u else 0, fun j => ?_, ?_⟩
      · show (if j = k then u else 0) ∈ chargeCovSpan m j
        by_cases hjk : j = k
        · subst hjk
          rw [if_pos rfl]
          exact Submodule.subset_span ⟨hu1, hu2, hg⟩
        · rw [if_neg hjk]
          exact Submodule.zero_mem _
      · rw [show (∑ j ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
            (fun j => if j = k then u else 0) j) =
            ∑ j ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), (if j = k then u else 0) from rfl,
          Finset.sum_ite_eq' _ k fun _ => u, if_pos hkm]
  | zero =>
    exact ⟨fun _ => 0, fun j => Submodule.zero_mem _, by simp⟩
  | add a b ha hb iha ihb =>
    obtain ⟨v₁, hv₁, rfl⟩ := iha
    obtain ⟨v₂, hv₂, rfl⟩ := ihb
    exact ⟨v₁ + v₂, fun j => Submodule.add_mem _ (hv₁ j) (hv₂ j),
      by rw [← Finset.sum_add_distrib]; rfl⟩
  | smul c a ha iha =>
    obtain ⟨v, hv, rfl⟩ := iha
    exact ⟨c • v, fun j => Submodule.smul_mem _ _ (hv j),
      by rw [Finset.smul_sum]; rfl⟩

/-- The neutral-charge selection rule: a constant-gauge-invariant element of a
  weight sector lies in the charge-zero component, since the characters
  `u ↦ u^{6j}` of distinct charges are linearly independent along the unit
  circle. -/
lemma mem_chargeCovSpan_zero_of_invariant {m : ℕ} {y : JetAlgebra}
    (hy : y ∈ covMonomialSpan m)
    (hinv : ∀ g : GaugeGroupI,
      repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) y = y) :
    y ∈ chargeCovSpan m 0 := by
  obtain ⟨v, hv, hyeq⟩ := exists_charge_decomp_of_mem_covMonomialSpan hy
  set S : Finset ℤ := Finset.Icc (-(m : ℤ)) (m : ℤ) with hS
  have hchar : ∀ θ : ℝ, ∑ j ∈ S, (Complex.exp ((θ : ℂ) * Complex.I)) ^ (6 * j) •
      v j = ∑ j ∈ S, v j := by
    intro θ
    have hval : (((u1Gauge (Complex.exp ((θ : ℂ) * Complex.I))
        (exp_mul_I_mem_unitary θ)).2.2 : ℂ)) =
        Complex.exp ((θ : ℂ) * Complex.I) := rfl
    have h1 := hinv (u1Gauge (Complex.exp ((θ : ℂ) * Complex.I))
      (exp_mul_I_mem_unitary θ))
    rw [hyeq, map_sum] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [forall_rep_ofConstant_of_mem_chargeCovSpan (hv j), hval]
  have hkill : ∀ j ∈ S, j ≠ 0 → v j = 0 := by
    intro j hj hj0
    have h6 : Function.Injective (fun k : ℤ => 6 * k) := fun a b hab => by
      simpa using hab
    set w : ℤ → JetAlgebra := fun k => v (k / 6) -
      (if k = 0 then ∑ i ∈ S, v i else 0) with hw
    have hzero : ∀ θ : ℝ, ∑ k ∈ S.image (fun j => 6 * j),
        (Complex.exp ((θ : ℂ) * Complex.I)) ^ k • w k = 0 := by
      intro θ
      rw [Finset.sum_image fun a _ b _ h => h6 h]
      have hterm : ∀ i ∈ S, (Complex.exp ((θ : ℂ) * Complex.I)) ^ (6 * i) •
          w (6 * i) = (Complex.exp ((θ : ℂ) * Complex.I)) ^ (6 * i) • v i -
          (if i = 0 then ∑ i ∈ S, v i else 0) := by
        intro i _
        rw [hw]
        simp only [Int.mul_ediv_cancel_left i (by norm_num : (6 : ℤ) ≠ 0),
          show 6 * i = 0 ↔ i = 0 from by omega]
        by_cases hi : i = 0
        · rw [if_pos hi, smul_sub, hi]
          norm_num
        · rw [if_neg hi]
          simp
      rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, hchar θ,
        Finset.sum_ite_eq' S (0 : ℤ) fun _ => ∑ i ∈ S, v i,
        if_pos (by simp [hS] : (0 : ℤ) ∈ S), sub_self]
    have h0 := eq_zero_of_forall_circle_sum_zpow_smul_eq_zero _ _ hzero
      (Finset.mem_image_of_mem (fun j => 6 * j) hj)
    rw [hw] at h0
    simpa [Int.mul_ediv_cancel_left j (by norm_num : (6 : ℤ) ≠ 0),
      show ¬ (6 * j = 0) from by omega] using h0
  have hy0 : y = v 0 := by
    rw [hyeq, Finset.sum_eq_single 0 (fun j hj hj0 => hkill j hj hj0)
      (fun h => absurd (by simp [hS] : (0 : ℤ) ∈ S) h)]
  rw [hy0]
  exact hv 0

/-!

## The Lorentz analysis of the neutral sectors

TODO: the remaining sector lemmas. The charge-zero covariant monomials of
weight four are the field strengths `F_{μν}`, of weight six the derivatives
`∂_ρ F_{μν}` and the fermion pairs `ψ̄_α ψ_β`, of weight eight the products
`F F`, the second derivatives `∂_ρ ∂_τ F_{μν}`, and the one-derivative fermion
pairs. Lorentz invariance kills the weight-four and weight-six sectors and
reduces the weight-eight sector to the span of the Maxwell term, the theta
term, and the two fermion kinetic terms.

-/

/-- Each invariant generator is a weight eigenvector of weight at least
  three. -/
lemma exists_weight_of_mem_invariantGenerators {g : JetAlgebra}
    (hg : g ∈ invariantGenerators) :
    ∃ w, 3 ≤ w ∧ ∀ c : ℂ, massWeightScale c g = c ^ w • g := by
  rcases hg with (⟨p, rfl⟩ | ⟨p, rfl⟩) | ⟨p, rfl⟩
  · exact ⟨4 + 2 * Multiset.card p.1, by omega,
      fun c => massWeightScale_fieldStrengthDeriv c p.1 p.2.1 p.2.2⟩
  · exact ⟨3 + 2 * p.1.length, by omega, fun c => massWeightScale_Dψ c p.1 p.2⟩
  · exact ⟨3 + 2 * p.1.length, by omega, fun c => massWeightScale_Dbarψ c p.1 p.2⟩

/-- The product of a list of invariant generators is a weight eigenvector of
  weight at least three times the length. -/
lemma exists_weight_of_list_prod {l : List JetAlgebra}
    (hl : ∀ g ∈ l, g ∈ invariantGenerators) :
    ∃ w, 3 * l.length ≤ w ∧
      ∀ c : ℂ, massWeightScale c l.prod = c ^ w • l.prod := by
  induction l with
  | nil =>
    exact ⟨0, by simp, fun c => by
      rw [List.prod_nil, pow_zero, one_smul]
      exact (massWeightScale c).map_one⟩
  | cons g l ih =>
    obtain ⟨wg, hwg3, hwg⟩ := exists_weight_of_mem_invariantGenerators
      (hl g List.mem_cons_self)
    obtain ⟨wl, hwl3, hwl⟩ := ih fun x hx => hl x (List.mem_cons_of_mem g hx)
    refine ⟨wg + wl, by simp only [List.length_cons]; omega, fun c => ?_⟩
    rw [List.prod_cons]
    exact massWeightScale_mul_eigen hwg hwl c

/-- The constant gauge character of a product of two lepton factors: charge
  two. -/
lemma rep_ofConstant_Dψ_mul_Dψ (g : GaugeGroupI) (l l' : List (Fin 1 ⊕ Fin 3))
    (α β : Fin 2) :
    repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) (Dψ l α * Dψ l' β) =
      ((g.2.2 : ℂ)) ^ (6 * (2 : ℤ)) • (Dψ l α * Dψ l' β) := by
  rw [repJetGaugeGroupI_mul', repJetGaugeGroupI_Dψ, repJetGaugeGroupI_Dψ,
    JetGaugeGroupI.eval_ofConstant, Submonoid.smul_def, Submonoid.smul_def,
    SubmonoidClass.coe_pow, smul_mul_smul_comm, ← pow_add,
    show (6 * (2 : ℤ)) = ((12 : ℕ) : ℤ) from rfl, zpow_natCast]

/-- The constant gauge character of a product of two conjugate lepton factors:
  charge minus two. -/
lemma rep_ofConstant_Dbarψ_mul_Dbarψ (g : GaugeGroupI)
    (l l' : List (Fin 1 ⊕ Fin 3)) (α β : Fin 2) :
    repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) (Dbarψ l α * Dbarψ l' β) =
      ((g.2.2 : ℂ)) ^ (6 * (-2 : ℤ)) • (Dbarψ l α * Dbarψ l' β) := by
  have hinv : star ((g.2.2 : ℂ)) = ((g.2.2 : ℂ))⁻¹ :=
    eq_inv_of_mul_eq_one_left (Unitary.mem_iff.mp (g.2.2).2).1
  rw [repJetGaugeGroupI_mul', repJetGaugeGroupI_Dbarψ, repJetGaugeGroupI_Dbarψ,
    JetGaugeGroupI.eval_ofConstant, Submonoid.smul_def, Submonoid.smul_def,
    SubmonoidClass.coe_pow, Unitary.coe_star, smul_mul_smul_comm, ← pow_add,
    hinv, inv_pow, show (6 + 6 : ℕ) = 12 from rfl,
    show (6 * (-2 : ℤ)) = -((12 : ℕ) : ℤ) from rfl, _root_.zpow_neg, zpow_natCast]

/-- The weight-four neutral sector: spanned by the embedded field strengths. -/
lemma chargeCovSpan_four_le :
    chargeCovSpan 4 0 ≤ Submodule.span ℂ
      (Set.range fun p : (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) =>
        fieldStrengthDeriv {} p.1 p.2) := by
  rw [chargeCovSpan, Submodule.span_le]
  rintro y ⟨hy1, hy2, -⟩
  obtain ⟨l, hl, hprod⟩ := Submonoid.exists_list_of_mem_closure hy1
  subst hprod
  rcases l with _ | ⟨g, _ | ⟨g', t⟩⟩
  · rw [List.prod_nil] at hy2 ⊢
    rw [eq_zero_of_eigen_ne (m := 0)
      (fun c => by rw [pow_zero, one_smul]; exact (massWeightScale c).map_one)
      hy2 (by omega)]
    exact Submodule.zero_mem _
  · rw [List.prod_cons, List.prod_nil, mul_one] at hy2 ⊢
    rcases hl g List.mem_cons_self with (⟨p, rfl⟩ | ⟨p, rfl⟩) | ⟨p, rfl⟩ <;>
      dsimp only at hy2 ⊢
    · by_cases hcard : Multiset.card p.1 = 0
      · rw [Multiset.card_eq_zero.mp hcard]
        exact Submodule.subset_span ⟨(p.2.1, p.2.2), rfl⟩
      · rw [eq_zero_of_eigen_ne
          (fun c => massWeightScale_fieldStrengthDeriv c p.1 p.2.1 p.2.2) hy2
          (by omega)]
        exact Submodule.zero_mem _
    · rw [eq_zero_of_eigen_ne (fun c => massWeightScale_Dψ c p.1 p.2) hy2
        (by omega)]
      exact Submodule.zero_mem _
    · rw [eq_zero_of_eigen_ne (fun c => massWeightScale_Dbarψ c p.1 p.2) hy2
        (by omega)]
      exact Submodule.zero_mem _
  · obtain ⟨w, hw, hweig⟩ := exists_weight_of_list_prod hl
    rw [eq_zero_of_eigen_ne hweig hy2 (by
      simp only [List.length_cons] at hw
      omega)]
    exact Submodule.zero_mem _

set_option maxHeartbeats 4000000 in
/-- The weight-six neutral sector: spanned by the first derivatives of the
  field strength and the zero-derivative lepton pairs. -/
lemma chargeCovSpan_six_le :
    chargeCovSpan 6 0 ≤ Submodule.span ℂ
      ((Set.range fun p : (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) =>
        fieldStrengthDeriv {p.1} p.2.1 p.2.2) ∪
      (Set.range fun p : Fin 2 × Fin 2 => Dbarψ [] p.1 * Dψ [] p.2) ∪
      (Set.range fun p : Fin 2 × Fin 2 => Dψ [] p.1 * Dbarψ [] p.2)) := by
  rw [chargeCovSpan, Submodule.span_le]
  rintro y ⟨hy1, hy2, hy3⟩
  simp only [mul_zero, zpow_zero, one_smul] at hy3
  obtain ⟨l, hl, hprod⟩ := Submonoid.exists_list_of_mem_closure hy1
  subst hprod
  rcases l with _ | ⟨g, _ | ⟨g', _ | ⟨g'', t⟩⟩⟩
  · rw [List.prod_nil] at hy2 ⊢
    rw [eq_zero_of_eigen_ne (m := 0)
      (fun c => by rw [pow_zero, one_smul]; exact (massWeightScale c).map_one)
      hy2 (by omega)]
    exact Submodule.zero_mem _
  · rw [List.prod_cons, List.prod_nil, mul_one] at hy2 ⊢
    rcases hl g List.mem_cons_self with (⟨p, rfl⟩ | ⟨p, rfl⟩) | ⟨p, rfl⟩ <;>
      dsimp only at hy2 ⊢
    · by_cases hcard : Multiset.card p.1 = 1
      · obtain ⟨ρ, hρ⟩ := Multiset.card_eq_one.mp hcard
        rw [hρ]
        exact Submodule.subset_span (Or.inl (Or.inl ⟨(ρ, p.2.1, p.2.2), rfl⟩))
      · rw [eq_zero_of_eigen_ne
          (fun c => massWeightScale_fieldStrengthDeriv c p.1 p.2.1 p.2.2) hy2
          (by omega)]
        exact Submodule.zero_mem _
    · rw [eq_zero_of_eigen_ne (fun c => massWeightScale_Dψ c p.1 p.2) hy2
        (by omega)]
      exact Submodule.zero_mem _
    · rw [eq_zero_of_eigen_ne (fun c => massWeightScale_Dbarψ c p.1 p.2) hy2
        (by omega)]
      exact Submodule.zero_mem _
  · rw [List.prod_cons, List.prod_cons, List.prod_nil, mul_one] at hy2 hy3 ⊢
    rcases hl g List.mem_cons_self with (⟨p, rfl⟩ | ⟨p, rfl⟩) | ⟨p, rfl⟩ <;>
      rcases hl g' (List.mem_cons_of_mem _ List.mem_cons_self) with
        (⟨q, rfl⟩ | ⟨q, rfl⟩) | ⟨q, rfl⟩ <;>
      dsimp only at hy2 hy3 ⊢
    · rw [eq_zero_of_eigen_ne (massWeightScale_mul_eigen
        (fun c => massWeightScale_fieldStrengthDeriv c p.1 p.2.1 p.2.2)
        (fun c => massWeightScale_fieldStrengthDeriv c q.1 q.2.1 q.2.2)) hy2
        (by omega)]
      exact Submodule.zero_mem _
    · rw [eq_zero_of_eigen_ne (massWeightScale_mul_eigen
        (fun c => massWeightScale_fieldStrengthDeriv c p.1 p.2.1 p.2.2)
        (fun c => massWeightScale_Dψ c q.1 q.2)) hy2 (by omega)]
      exact Submodule.zero_mem _
    · rw [eq_zero_of_eigen_ne (massWeightScale_mul_eigen
        (fun c => massWeightScale_fieldStrengthDeriv c p.1 p.2.1 p.2.2)
        (fun c => massWeightScale_Dbarψ c q.1 q.2)) hy2 (by omega)]
      exact Submodule.zero_mem _
    · rw [eq_zero_of_eigen_ne (massWeightScale_mul_eigen
        (fun c => massWeightScale_Dψ c p.1 p.2)
        (fun c => massWeightScale_fieldStrengthDeriv c q.1 q.2.1 q.2.2)) hy2
        (by omega)]
      exact Submodule.zero_mem _
    · rw [eq_zero_of_charge_ne_zero (k := 2) (by omega)
        (fun gc => rep_ofConstant_Dψ_mul_Dψ gc p.1 q.1 p.2 q.2) hy3]
      exact Submodule.zero_mem _
    · by_cases hlen : p.1.length = 0 ∧ q.1.length = 0
      · rw [List.length_eq_zero_iff.mp hlen.1, List.length_eq_zero_iff.mp hlen.2]
        exact Submodule.subset_span (Or.inr ⟨(p.2, q.2), rfl⟩)
      · rw [eq_zero_of_eigen_ne (massWeightScale_mul_eigen
          (fun c => massWeightScale_Dψ c p.1 p.2)
          (fun c => massWeightScale_Dbarψ c q.1 q.2)) hy2 (by omega)]
        exact Submodule.zero_mem _
    · rw [eq_zero_of_eigen_ne (massWeightScale_mul_eigen
        (fun c => massWeightScale_Dbarψ c p.1 p.2)
        (fun c => massWeightScale_fieldStrengthDeriv c q.1 q.2.1 q.2.2)) hy2
        (by omega)]
      exact Submodule.zero_mem _
    · by_cases hlen : p.1.length = 0 ∧ q.1.length = 0
      · rw [List.length_eq_zero_iff.mp hlen.1, List.length_eq_zero_iff.mp hlen.2]
        exact Submodule.subset_span (Or.inl (Or.inr ⟨(p.2, q.2), rfl⟩))
      · rw [eq_zero_of_eigen_ne (massWeightScale_mul_eigen
          (fun c => massWeightScale_Dbarψ c p.1 p.2)
          (fun c => massWeightScale_Dψ c q.1 q.2)) hy2 (by omega)]
        exact Submodule.zero_mem _
    · rw [eq_zero_of_charge_ne_zero (k := -2) (by omega)
        (fun gc => rep_ofConstant_Dbarψ_mul_Dbarψ gc p.1 q.1 p.2 q.2) hy3]
      exact Submodule.zero_mem _
  · obtain ⟨w, hw, hweig⟩ := exists_weight_of_list_prod hl
    rw [eq_zero_of_eigen_ne hweig hy2 (by
      simp only [List.length_cons] at hw
      omega)]
    exact Submodule.zero_mem _

set_option maxHeartbeats 4000000 in
/-- The weight-eight neutral sector: spanned by the field-strength squares, the
  second derivatives of the field strength, and the one-derivative lepton
  pairs. -/
lemma chargeCovSpan_eight_le :
    chargeCovSpan 8 0 ≤ Submodule.span ℂ
      ((Set.range fun p : ((Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)) ×
          (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) =>
        fieldStrengthDeriv {} p.1.1 p.1.2 * fieldStrengthDeriv {} p.2.1 p.2.2) ∪
      (Set.range fun p : ((Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)) ×
          (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) =>
        fieldStrengthDeriv {p.1.1, p.1.2} p.2.1 p.2.2) ∪
      (Set.range fun p : (Fin 2 × Fin 2) × (Fin 1 ⊕ Fin 3) =>
        Dbarψ [] p.1.1 * Dψ [p.2] p.1.2) ∪
      (Set.range fun p : (Fin 2 × Fin 2) × (Fin 1 ⊕ Fin 3) =>
        Dψ [p.2] p.1.2 * Dbarψ [] p.1.1) ∪
      (Set.range fun p : (Fin 2 × Fin 2) × (Fin 1 ⊕ Fin 3) =>
        Dψ [] p.1.1 * Dbarψ [p.2] p.1.2) ∪
      (Set.range fun p : (Fin 2 × Fin 2) × (Fin 1 ⊕ Fin 3) =>
        Dbarψ [p.2] p.1.2 * Dψ [] p.1.1)) := by
  rw [chargeCovSpan, Submodule.span_le]
  rintro y ⟨hy1, hy2, hy3⟩
  simp only [mul_zero, zpow_zero, one_smul] at hy3
  obtain ⟨l, hl, hprod⟩ := Submonoid.exists_list_of_mem_closure hy1
  subst hprod
  rcases l with _ | ⟨g, _ | ⟨g', _ | ⟨g'', t⟩⟩⟩
  · rw [List.prod_nil] at hy2 ⊢
    rw [eq_zero_of_eigen_ne (m := 0)
      (fun c => by rw [pow_zero, one_smul]; exact (massWeightScale c).map_one)
      hy2 (by omega)]
    exact Submodule.zero_mem _
  · rw [List.prod_cons, List.prod_nil, mul_one] at hy2 ⊢
    rcases hl g List.mem_cons_self with (⟨p, rfl⟩ | ⟨p, rfl⟩) | ⟨p, rfl⟩ <;>
      dsimp only at hy2 ⊢
    · by_cases hcard : Multiset.card p.1 = 2
      · obtain ⟨ρ, τ, hρτ⟩ := Multiset.card_eq_two.mp hcard
        rw [hρτ]
        exact Submodule.subset_span (Or.inl (Or.inl (Or.inl (Or.inl
          (Or.inr ⟨((ρ, τ), p.2.1, p.2.2), rfl⟩)))))
      · rw [eq_zero_of_eigen_ne
          (fun c => massWeightScale_fieldStrengthDeriv c p.1 p.2.1 p.2.2) hy2
          (by omega)]
        exact Submodule.zero_mem _
    · rw [eq_zero_of_eigen_ne (fun c => massWeightScale_Dψ c p.1 p.2) hy2
        (by omega)]
      exact Submodule.zero_mem _
    · rw [eq_zero_of_eigen_ne (fun c => massWeightScale_Dbarψ c p.1 p.2) hy2
        (by omega)]
      exact Submodule.zero_mem _
  · rw [List.prod_cons, List.prod_cons, List.prod_nil, mul_one] at hy2 hy3 ⊢
    rcases hl g List.mem_cons_self with (⟨p, rfl⟩ | ⟨p, rfl⟩) | ⟨p, rfl⟩ <;>
      rcases hl g' (List.mem_cons_of_mem _ List.mem_cons_self) with
        (⟨q, rfl⟩ | ⟨q, rfl⟩) | ⟨q, rfl⟩ <;>
      dsimp only at hy2 hy3 ⊢
    · by_cases hcard : Multiset.card p.1 = 0 ∧ Multiset.card q.1 = 0
      · rw [Multiset.card_eq_zero.mp hcard.1, Multiset.card_eq_zero.mp hcard.2]
        exact Submodule.subset_span (Or.inl (Or.inl (Or.inl (Or.inl
          (Or.inl ⟨((p.2.1, p.2.2), q.2.1, q.2.2), rfl⟩)))))
      · rw [eq_zero_of_eigen_ne (massWeightScale_mul_eigen
          (fun c => massWeightScale_fieldStrengthDeriv c p.1 p.2.1 p.2.2)
          (fun c => massWeightScale_fieldStrengthDeriv c q.1 q.2.1 q.2.2)) hy2
          (by omega)]
        exact Submodule.zero_mem _
    · rw [eq_zero_of_eigen_ne (massWeightScale_mul_eigen
        (fun c => massWeightScale_fieldStrengthDeriv c p.1 p.2.1 p.2.2)
        (fun c => massWeightScale_Dψ c q.1 q.2)) hy2 (by omega)]
      exact Submodule.zero_mem _
    · rw [eq_zero_of_eigen_ne (massWeightScale_mul_eigen
        (fun c => massWeightScale_fieldStrengthDeriv c p.1 p.2.1 p.2.2)
        (fun c => massWeightScale_Dbarψ c q.1 q.2)) hy2 (by omega)]
      exact Submodule.zero_mem _
    · rw [eq_zero_of_eigen_ne (massWeightScale_mul_eigen
        (fun c => massWeightScale_Dψ c p.1 p.2)
        (fun c => massWeightScale_fieldStrengthDeriv c q.1 q.2.1 q.2.2)) hy2
        (by omega)]
      exact Submodule.zero_mem _
    · rw [eq_zero_of_charge_ne_zero (k := 2) (by omega)
        (fun gc => rep_ofConstant_Dψ_mul_Dψ gc p.1 q.1 p.2 q.2) hy3]
      exact Submodule.zero_mem _
    · by_cases hlen : p.1.length = 0 ∧ q.1.length = 1
      · obtain ⟨μ, hμ⟩ := List.length_eq_one_iff.mp hlen.2
        rw [List.length_eq_zero_iff.mp hlen.1, hμ]
        exact Submodule.subset_span (Or.inl (Or.inr ⟨((p.2, q.2), μ), rfl⟩))
      · by_cases hlen' : p.1.length = 1 ∧ q.1.length = 0
        · obtain ⟨μ, hμ⟩ := List.length_eq_one_iff.mp hlen'.1
          rw [List.length_eq_zero_iff.mp hlen'.2, hμ]
          exact Submodule.subset_span (Or.inl (Or.inl (Or.inr
            ⟨((q.2, p.2), μ), rfl⟩)))
        · rw [eq_zero_of_eigen_ne (massWeightScale_mul_eigen
            (fun c => massWeightScale_Dψ c p.1 p.2)
            (fun c => massWeightScale_Dbarψ c q.1 q.2)) hy2 (by omega)]
          exact Submodule.zero_mem _
    · rw [eq_zero_of_eigen_ne (massWeightScale_mul_eigen
        (fun c => massWeightScale_Dbarψ c p.1 p.2)
        (fun c => massWeightScale_fieldStrengthDeriv c q.1 q.2.1 q.2.2)) hy2
        (by omega)]
      exact Submodule.zero_mem _
    · by_cases hlen : p.1.length = 0 ∧ q.1.length = 1
      · obtain ⟨μ, hμ⟩ := List.length_eq_one_iff.mp hlen.2
        rw [List.length_eq_zero_iff.mp hlen.1, hμ]
        exact Submodule.subset_span (Or.inl (Or.inl (Or.inl (Or.inr
          ⟨((p.2, q.2), μ), rfl⟩))))
      · by_cases hlen' : p.1.length = 1 ∧ q.1.length = 0
        · obtain ⟨μ, hμ⟩ := List.length_eq_one_iff.mp hlen'.1
          rw [List.length_eq_zero_iff.mp hlen'.2, hμ]
          exact Submodule.subset_span (Or.inr ⟨((q.2, p.2), μ), rfl⟩)
        · rw [eq_zero_of_eigen_ne (massWeightScale_mul_eigen
            (fun c => massWeightScale_Dbarψ c p.1 p.2)
            (fun c => massWeightScale_Dψ c q.1 q.2)) hy2 (by omega)]
          exact Submodule.zero_mem _
    · rw [eq_zero_of_charge_ne_zero (k := -2) (by omega)
        (fun gc => rep_ofConstant_Dbarψ_mul_Dbarψ gc p.1 q.1 p.2 q.2) hy3]
      exact Submodule.zero_mem _
  · have h0 : (g :: g' :: g'' :: t).prod = 0 := by
      obtain ⟨w, hw, hweig⟩ := exists_weight_of_list_prod hl
      exact eq_zero_of_eigen_ne hweig hy2 (by
        simp only [List.length_cons] at hw
        omega)
    exact Set.mem_of_eq_of_mem h0 (Submodule.zero_mem _)

/-!

### The parity rotations

The three rotations by `π` about the coordinate axes lift to `SL(2,ℂ)` as
`i σ_k`; their Lorentz matrices are the diagonal sign matrices fixing the time
axis and the rotation axis and reversing the two others. Averaging over this
Klein four-group kills every tensor component with an odd index pattern; since
every antisymmetric index pair is odd under exactly two of the three parities,
the weight-four sector admits no invariant.

-/

/-- The lift `diag(i, -i)` of the rotation by `π` about the `z`-axis. -/
noncomputable def parityZ : SL(2,ℂ) :=
  ⟨!![Complex.I, 0; 0, -Complex.I], by
    simp [Matrix.det_fin_two_of]⟩

/-- The lift `i σ1` of the rotation by `π` about the `x`-axis. -/
noncomputable def parityX : SL(2,ℂ) :=
  ⟨!![0, Complex.I; Complex.I, 0], by
    simp [Matrix.det_fin_two_of]⟩

/-- The lift `i σ2` of the rotation by `π` about the `y`-axis. -/
noncomputable def parityY : SL(2,ℂ) :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two_of]⟩

/-- The sign pattern of the rotation by `π` about the `z`-axis. -/
def paritySignZ : Fin 1 ⊕ Fin 3 → ℝ
  | Sum.inl _ => 1
  | Sum.inr 0 => -1
  | Sum.inr 1 => -1
  | Sum.inr 2 => 1

/-- The sign pattern of the rotation by `π` about the `x`-axis. -/
def paritySignX : Fin 1 ⊕ Fin 3 → ℝ
  | Sum.inl _ => 1
  | Sum.inr 0 => 1
  | Sum.inr 1 => -1
  | Sum.inr 2 => -1

/-- The sign pattern of the rotation by `π` about the `y`-axis. -/
def paritySignY : Fin 1 ⊕ Fin 3 → ℝ
  | Sum.inl _ => 1
  | Sum.inr 0 => -1
  | Sum.inr 1 => 1
  | Sum.inr 2 => -1

/-- The Lorentz matrix of the `z`-parity is the diagonal sign matrix. -/
lemma toLorentzGroup_parityZ (a b : Fin 1 ⊕ Fin 3) :
    (Lorentz.SL2C.toLorentzGroup parityZ).1 a b =
      if a = b then paritySignZ a else 0 := by
  refine Complex.ofReal_injective ?_
  rw [Lorentz.SL2C.toLorentzGroup_eq_trace]
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    · simp [parityZ, paritySignZ, PauliMatrix.pauliSelfAdjoint', PauliMatrix.pauliMatrix,
        Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose,
        Matrix.diag]
      simp [Matrix.vecMul, Matrix.vecHead, Matrix.vecTail]

/-- The Lorentz matrix of the `x`-parity is the diagonal sign matrix. -/
lemma toLorentzGroup_parityX (a b : Fin 1 ⊕ Fin 3) :
    (Lorentz.SL2C.toLorentzGroup parityX).1 a b =
      if a = b then paritySignX a else 0 := by
  refine Complex.ofReal_injective ?_
  rw [Lorentz.SL2C.toLorentzGroup_eq_trace]
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    · simp [parityX, paritySignX, PauliMatrix.pauliSelfAdjoint', PauliMatrix.pauliMatrix,
        Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose,
        Matrix.diag]
      simp [Matrix.vecMul, Matrix.vecHead, Matrix.vecTail]

/-- The Lorentz matrix of the `y`-parity is the diagonal sign matrix. -/
lemma toLorentzGroup_parityY (a b : Fin 1 ⊕ Fin 3) :
    (Lorentz.SL2C.toLorentzGroup parityY).1 a b =
      if a = b then paritySignY a else 0 := by
  refine Complex.ofReal_injective ?_
  rw [Lorentz.SL2C.toLorentzGroup_eq_trace]
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    · simp [parityY, paritySignY, PauliMatrix.pauliSelfAdjoint', PauliMatrix.pauliMatrix,
        Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose,
        Matrix.diag]
      simp [Matrix.vecMul, Matrix.vecHead, Matrix.vecTail]

/-- Under a diagonal Lorentz transformation the field strength scales by the
  product of the signs of its two indices. -/
lemma repLorentzGroup_diag_fieldStrengthDeriv {M : SL(2,ℂ)}
    {sgn : Fin 1 ⊕ Fin 3 → ℝ}
    (hM : ∀ a b, (Lorentz.SL2C.toLorentzGroup M).1 a b =
      if a = b then sgn a else 0) (μ ν : Fin 1 ⊕ Fin 3) :
    repLorentzGroup M (fieldStrengthDeriv {} μ ν) =
      ((sgn μ * sgn ν : ℝ) : ℂ) • fieldStrengthDeriv {} μ ν := by
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  rw [Finset.sum_eq_single μ (fun a _ ha => Finset.sum_eq_zero fun b _ => by
      rw [hM a μ, if_neg ha, zero_mul, Complex.ofReal_zero, zero_smul])
    (fun h => absurd (Finset.mem_univ μ) h)]
  rw [Finset.sum_eq_single ν (fun b _ hb => by
      rw [hM b ν, if_neg hb, mul_zero, Complex.ofReal_zero, zero_smul])
    (fun h => absurd (Finset.mem_univ ν) h)]
  rw [hM μ μ, if_pos rfl, hM ν ν, if_pos rfl]

/-- The field strength vanishes on a repeated index. -/
lemma fieldStrengthDeriv_self (s : Multiset (Fin 1 ⊕ Fin 3))
    (μ : Fin 1 ⊕ Fin 3) : fieldStrengthDeriv s μ μ = 0 := by
  have h : (fieldStrengthDeriv s μ μ : JetAlgebra) =
      [JetGenerators.dB (s + {μ}) μ]ₐ - [JetGenerators.dB (s + {μ}) μ]ₐ := by
    rw [fieldStrengthDeriv, BBoson.JetAlgebra.fieldStrengthDeriv,
      TensorProduct.tmul_sub, TensorProduct.sub_tmul]
    rfl
  rw [h, sub_self]

set_option maxHeartbeats 2000000 in
/-- No Lorentz invariant of mass weight four: an invariant combination of the
  field strengths `F_{μν}` vanishes, since every antisymmetric index pair is
  odd under two of the three parity rotations. -/
lemma eq_zero_of_mem_chargeCovSpan_four {y : JetAlgebra}
    (hy : y ∈ chargeCovSpan 4 0)
    (hinv : ∀ Λ : SL(2,ℂ), repLorentzGroup Λ y = y) : y = 0 := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp
    (chargeCovSpan_four_le hy)
  have h4 : ((4 : ℂ)⁻¹ • (y + repLorentzGroup parityZ y +
      repLorentzGroup parityY y + repLorentzGroup parityX y)) = y := by
    rw [hinv, hinv, hinv]
    module
  rw [← h4, ← hc, map_sum, map_sum, map_sum]
  simp only [map_smul, repLorentzGroup_diag_fieldStrengthDeriv
      toLorentzGroup_parityZ,
    repLorentzGroup_diag_fieldStrengthDeriv toLorentzGroup_parityY,
    repLorentzGroup_diag_fieldStrengthDeriv toLorentzGroup_parityX]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, Finset.smul_sum]
  refine Finset.sum_eq_zero fun p _ => ?_
  rcases eq_or_ne p.1 p.2 with hp | hp
  · rw [hp, fieldStrengthDeriv_self]
    simp
  · rw [smul_smul, smul_smul, smul_smul, ← add_smul, ← add_smul, ← add_smul,
      smul_smul]
    rw [show ((4 : ℂ)⁻¹ * (c p + c p * ((paritySignZ p.1 * paritySignZ p.2 : ℝ) : ℂ) +
        c p * ((paritySignY p.1 * paritySignY p.2 : ℝ) : ℂ) +
        c p * ((paritySignX p.1 * paritySignX p.2 : ℝ) : ℂ))) = 0 from by
      rcases p with ⟨μ, ν⟩
      rcases μ with μ | μ <;> rcases ν with ν | ν <;>
        first
          | (exact absurd rfl (by simpa using hp))
          | (fin_cases μ <;> fin_cases ν <;>
              simp_all [paritySignZ, paritySignY, paritySignX] <;>
              norm_num [Complex.ext_iff] <;> ring)]
    rw [zero_smul]

/-!

### The transformation law of the derivative field strength

-/

set_option maxHeartbeats 2000000 in
/-- The Lorentz action on the two-derivative-index B-boson jet coordinates:
  all three indices transform contravariantly, by the columns of the Lorentz
  matrix. -/
lemma _root_.StandardModel.BBoson.JetComponentSpace.repLorentzGroup_basis_dB_pair
    (Λ : SL(2,ℂ)) (ρ μ ν : Fin 1 ⊕ Fin 3) :
    BBoson.JetComponentSpace.repLorentzGroup Λ
      (BBoson.JetComponentSpace.basis (.dB {ρ, μ} ν)) =
      ∑ r, ∑ a, ∑ b, ((Lorentz.SL2C.toLorentzGroup Λ).1 r ρ *
        ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ *
          (Lorentz.SL2C.toLorentzGroup Λ).1 b ν)) •
        BBoson.JetComponentSpace.basis (.dB {r, a} b) := by
  have hpair : ∀ x y : Fin 1 ⊕ Fin 3,
      LagrangianTheory.dualRealJetAlgebraBasis ({x, y} : Multiset (Fin 1 ⊕ Fin 3)) =
        SymmetricAlgebra.ι ℝ (Module.Dual ℝ Lorentz.CoVector)
            (Lorentz.CoVector.basis.dualBasis x) *
          SymmetricAlgebra.ι ℝ (Module.Dual ℝ Lorentz.CoVector)
            (Lorentz.CoVector.basis.dualBasis y) := fun x y => by
    rw [← BBoson.dualRealJetAlgebraBasis_singleton,
      ← BBoson.dualRealJetAlgebraBasis_singleton,
      BBoson.dualRealJetAlgebraBasis_mul, Multiset.singleton_add,
      ← Multiset.insert_eq_cons]
  have hmul : ∀ x y : DerivAlgebraReal,
      DerivAlgebraReal.repLorentzGroup Λ (x * y) =
        DerivAlgebraReal.repLorentzGroup Λ x *
          DerivAlgebraReal.repLorentzGroup Λ y := fun x y =>
    map_mul (SymmetricAlgebra.lift (SymmetricAlgebra.ι ℝ _ ∘ₗ
      Lorentz.CoVector.sl2Rep.dual Λ)) x y
  have happ : BBoson.JetComponentSpace.repLorentzGroup Λ
      (LagrangianTheory.dualRealJetAlgebraBasis {ρ, μ} ⊗ₜ[ℝ]
        StandardModel.BBoson.basis.dualBasis ν) =
      (DerivAlgebraReal.repLorentzGroup Λ
        (LagrangianTheory.dualRealJetAlgebraBasis {ρ, μ})) ⊗ₜ[ℝ]
      (BBoson.repLorentzGroup.dual Λ
        (StandardModel.BBoson.basis.dualBasis ν)) := rfl
  rw [BBoson.jetComponentSpace_basis_dB, happ, hpair, hmul,
    DerivAlgebraReal.repLorentzGroup_apply_ι,
    DerivAlgebraReal.repLorentzGroup_apply_ι,
    Lorentz.CoVector.sl2Rep_dual_dualBasis, Lorentz.CoVector.sl2Rep_dual_dualBasis,
    BBoson.repLorentzGroup_dual_dualBasis]
  simp only [map_sum, map_smul, Finset.sum_mul, Finset.mul_sum,
    smul_mul_smul_comm, TensorProduct.sum_tmul, TensorProduct.tmul_sum,
    ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, Finset.smul_sum,
    smul_smul, BBoson.jetComponentSpace_basis_dB, hpair]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, j]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => ?_
  module

set_option maxHeartbeats 2000000 in
/-- The transformation law of the first-derivative field strength on the
  B-boson jet algebra: a three-index tensor. -/
lemma _root_.StandardModel.BBoson.JetAlgebra.repLorentzGroup_fieldStrengthDeriv_singleton
    (Λ : SL(2,ℂ)) (ρ μ ν : Fin 1 ⊕ Fin 3) :
    BBoson.JetAlgebra.repLorentzGroup Λ
      (BBoson.JetAlgebra.fieldStrengthDeriv {ρ} μ ν) =
      ∑ r, ∑ a, ∑ b, ((Lorentz.SL2C.toLorentzGroup Λ).1 r ρ *
        ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ *
          (Lorentz.SL2C.toLorentzGroup Λ).1 b ν)) •
        BBoson.JetAlgebra.fieldStrengthDeriv {r} a b := by
  have hFS : ∀ r a b : Fin 1 ⊕ Fin 3,
      BBoson.JetAlgebra.fieldStrengthDeriv ({r} : Multiset _) a b =
        BBoson.JetAlgebra.ofGenerator (.dB {r, a} b) -
          BBoson.JetAlgebra.ofGenerator (.dB {r, b} a) := fun r a b => by
    rw [BBoson.JetAlgebra.fieldStrengthDeriv,
      show ({r} : Multiset (Fin 1 ⊕ Fin 3)) + {a} = {r, a} from by
        rw [Multiset.singleton_add, ← Multiset.insert_eq_cons],
      show ({r} : Multiset (Fin 1 ⊕ Fin 3)) + {b} = {r, b} from by
        rw [Multiset.singleton_add, ← Multiset.insert_eq_cons]]
  simp only [hFS]
  rw [map_sub, BBoson.JetAlgebra.ofGenerator, BBoson.JetAlgebra.ofGenerator,
    BBoson.JetAlgebra.repLorentzGroup_apply_ι,
    BBoson.JetAlgebra.repLorentzGroup_apply_ι,
    BBoson.JetComponentSpace.repLorentzGroup_basis_dB_pair,
    BBoson.JetComponentSpace.repLorentzGroup_basis_dB_pair]
  simp only [map_sum, map_smul, smul_sub, Finset.sum_sub_distrib,
    BBoson.JetAlgebra.ofGenerator]
  rw [sub_right_inj]
  conv_rhs => enter [2, r]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => ?_
  congr 1
  ring

/-- The transformation of the complexified first-derivative field strength. -/
lemma _root_.StandardModel.BBoson.JetAlgebra.complexRepLorentzGroup_one_tmul_fieldStrengthDeriv_singleton
    (Λ : SL(2,ℂ)) (ρ μ ν : Fin 1 ⊕ Fin 3) :
    BBoson.JetAlgebra.complexRepLorentzGroup Λ
        ((1 : ℂ) ⊗ₜ[ℝ] BBoson.JetAlgebra.fieldStrengthDeriv {ρ} μ ν) =
      ∑ r, ∑ a, ∑ b, ((Lorentz.SL2C.toLorentzGroup Λ).1 r ρ *
        ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ *
          (Lorentz.SL2C.toLorentzGroup Λ).1 b ν)) •
        ((1 : ℂ) ⊗ₜ[ℝ] BBoson.JetAlgebra.fieldStrengthDeriv {r} a b) := by
  rw [show BBoson.JetAlgebra.complexRepLorentzGroup Λ
      ((1 : ℂ) ⊗ₜ[ℝ] BBoson.JetAlgebra.fieldStrengthDeriv {ρ} μ ν) =
      (1 : ℂ) ⊗ₜ[ℝ] BBoson.JetAlgebra.repLorentzGroup Λ
        (BBoson.JetAlgebra.fieldStrengthDeriv {ρ} μ ν) from rfl,
    BBoson.JetAlgebra.repLorentzGroup_fieldStrengthDeriv_singleton]
  simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul]

/-- The transformation law of the embedded first-derivative field strength:
  a three-index tensor, all indices transforming by the Lorentz matrix. -/
lemma repLorentzGroup_fieldStrengthDeriv_singleton (Λ : SL(2,ℂ))
    (ρ μ ν : Fin 1 ⊕ Fin 3) :
    repLorentzGroup Λ (fieldStrengthDeriv {ρ} μ ν) =
      ∑ r, ∑ a, ∑ b, ((((Lorentz.SL2C.toLorentzGroup Λ).1 r ρ *
        ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ *
          (Lorentz.SL2C.toLorentzGroup Λ).1 b ν) : ℝ)) : ℂ) •
        fieldStrengthDeriv {r} a b := by
  have hconv : ∀ (r : ℝ) (X : ℂ ⊗[ℝ] BBoson.JetAlgebra),
      (r • X) ⊗ₜ[ℂ] (1 : LeptonSinglet.JetAlgebra) = ((r : ℂ)) • (X ⊗ₜ[ℂ] 1) := by
    intro r X
    rw [← algebraMap_smul (R := ℝ) ℂ r X, ← TensorProduct.smul_tmul']
    rfl
  have happ : repLorentzGroup Λ (((1 : ℂ) ⊗ₜ[ℝ]
      BBoson.JetAlgebra.fieldStrengthDeriv {ρ} μ ν) ⊗ₜ[ℂ]
        (1 : LeptonSinglet.JetAlgebra)) =
      (BBoson.JetAlgebra.complexRepLorentzGroup Λ ((1 : ℂ) ⊗ₜ[ℝ]
        BBoson.JetAlgebra.fieldStrengthDeriv {ρ} μ ν)) ⊗ₜ[ℂ]
      (LeptonSinglet.JetAlgebra.repLorentzGroup Λ
        (1 : LeptonSinglet.JetAlgebra)) := rfl
  rw [fieldStrengthDeriv, happ,
    BBoson.JetAlgebra.complexRepLorentzGroup_one_tmul_fieldStrengthDeriv_singleton,
    LeptonSinglet.JetAlgebra.repLorentzGroup_apply_one]
  simp only [TensorProduct.sum_tmul, hconv, fieldStrengthDeriv]

/-- Under a diagonal Lorentz transformation the derivative field strength
  scales by the product of the signs of its three indices. -/
lemma repLorentzGroup_diag_fieldStrengthDeriv_singleton {M : SL(2,ℂ)}
    {sgn : Fin 1 ⊕ Fin 3 → ℝ}
    (hM : ∀ a b, (Lorentz.SL2C.toLorentzGroup M).1 a b =
      if a = b then sgn a else 0) (ρ μ ν : Fin 1 ⊕ Fin 3) :
    repLorentzGroup M (fieldStrengthDeriv {ρ} μ ν) =
      ((sgn ρ * (sgn μ * sgn ν) : ℝ) : ℂ) • fieldStrengthDeriv {ρ} μ ν := by
  rw [repLorentzGroup_fieldStrengthDeriv_singleton]
  rw [Finset.sum_eq_single ρ (fun r _ hr => Finset.sum_eq_zero fun a _ =>
      Finset.sum_eq_zero fun b _ => by
        rw [hM r ρ, if_neg hr, zero_mul, Complex.ofReal_zero, zero_smul])
    (fun h => absurd (Finset.mem_univ ρ) h)]
  rw [Finset.sum_eq_single μ (fun a _ ha => Finset.sum_eq_zero fun b _ => by
      rw [hM a μ, if_neg ha, zero_mul, mul_zero, Complex.ofReal_zero, zero_smul])
    (fun h => absurd (Finset.mem_univ μ) h)]
  rw [Finset.sum_eq_single ν (fun b _ hb => by
      rw [hM b ν, if_neg hb, mul_zero, mul_zero, Complex.ofReal_zero, zero_smul])
    (fun h => absurd (Finset.mem_univ ν) h)]
  rw [hM ρ ρ, if_pos rfl, hM μ μ, if_pos rfl, hM ν ν, if_pos rfl]

/-- Antisymmetry of the embedded field-strength derivatives in the two field
  indices. -/
lemma fieldStrengthDeriv_antisymm (s : Multiset (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) :
    fieldStrengthDeriv s ν μ = - fieldStrengthDeriv s μ ν := by
  have h : ∀ a b : Fin 1 ⊕ Fin 3, (fieldStrengthDeriv s a b : JetAlgebra) =
      [JetGenerators.dB (s + {a}) b]ₐ - [JetGenerators.dB (s + {b}) a]ₐ := by
    intro a b
    rw [fieldStrengthDeriv, BBoson.JetAlgebra.fieldStrengthDeriv,
      TensorProduct.tmul_sub, TensorProduct.sub_tmul]
    rfl
  rw [h, h, neg_sub]

/-- The canonical orientation of a mixed field-strength component: the time
  index first. -/
lemma fieldStrengthDeriv_inr_inl (s : Multiset (Fin 1 ⊕ Fin 3)) (i : Fin 3)
    (j : Fin 1) :
    fieldStrengthDeriv s (Sum.inr i) (Sum.inl j) =
      - fieldStrengthDeriv s (Sum.inl j) (Sum.inr i) :=
  fieldStrengthDeriv_antisymm s (Sum.inl j) (Sum.inr i)

/-!

### The boosts along the `z`-axis

Two diagonal boosts `diag(t, t⁻¹)` with `t = 2, 3`. Together with the Klein
four-group of parity rotations they suffice to kill the neutral weight-six
sector: the Klein average projects onto the twelve surviving field-strength
components and the diagonal fermion pairs, and a rational combination of the
two boosts (with weights summing to one) annihilates all of them.

-/

/-- The lift `diag(2, 1/2)` of the boost along the `z`-axis with rapidity
  `log 4`. -/
noncomputable def boostA : SL(2,ℂ) :=
  ⟨!![2, 0; 0, 2⁻¹], by norm_num [Matrix.det_fin_two_of]⟩

/-- The lift `diag(3, 1/3)` of the boost along the `z`-axis with rapidity
  `log 9`. -/
noncomputable def boostB : SL(2,ℂ) :=
  ⟨!![3, 0; 0, 3⁻¹], by norm_num [Matrix.det_fin_two_of]⟩

/-- The Lorentz matrix of `boostA`. -/
noncomputable def boostMatA : (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → ℝ
  | Sum.inl _, Sum.inl _ => 17/8
  | Sum.inl _, Sum.inr 2 => -(15/8)
  | Sum.inr 2, Sum.inl _ => -(15/8)
  | Sum.inr 0, Sum.inr 0 => 1
  | Sum.inr 1, Sum.inr 1 => 1
  | Sum.inr 2, Sum.inr 2 => 17/8
  | _, _ => 0

/-- The Lorentz matrix of `boostB`. -/
noncomputable def boostMatB : (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → ℝ
  | Sum.inl _, Sum.inl _ => 41/9
  | Sum.inl _, Sum.inr 2 => -(40/9)
  | Sum.inr 2, Sum.inl _ => -(40/9)
  | Sum.inr 0, Sum.inr 0 => 1
  | Sum.inr 1, Sum.inr 1 => 1
  | Sum.inr 2, Sum.inr 2 => 41/9
  | _, _ => 0

set_option maxHeartbeats 2000000 in
/-- The Lorentz matrix of the first boost. -/
lemma toLorentzGroup_boostA (a b : Fin 1 ⊕ Fin 3) :
    (Lorentz.SL2C.toLorentzGroup boostA).1 a b = boostMatA a b := by
  refine Complex.ofReal_injective ?_
  rw [Lorentz.SL2C.toLorentzGroup_eq_trace]
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    · try simp [boostA, boostMatA, PauliMatrix.pauliSelfAdjoint',
        PauliMatrix.pauliMatrix, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose, Matrix.diag]
      try simp [Matrix.vecMul, Matrix.vecHead, Matrix.vecTail]
      try norm_num [Complex.ext_iff]

set_option maxHeartbeats 2000000 in
/-- The Lorentz matrix of the second boost. -/
lemma toLorentzGroup_boostB (a b : Fin 1 ⊕ Fin 3) :
    (Lorentz.SL2C.toLorentzGroup boostB).1 a b = boostMatB a b := by
  refine Complex.ofReal_injective ?_
  rw [Lorentz.SL2C.toLorentzGroup_eq_trace]
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    · try simp [boostB, boostMatB, PauliMatrix.pauliSelfAdjoint',
        PauliMatrix.pauliMatrix, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose, Matrix.diag]
      try simp [Matrix.vecMul, Matrix.vecHead, Matrix.vecTail]
      try norm_num [Complex.ext_iff]

/-- The inverse of the `z`-parity, entrywise. -/
lemma parityZ_inv_coe :
    (parityZ⁻¹ : SL(2,ℂ)).1 = !![-Complex.I, 0; 0, Complex.I] := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [parityZ]

/-- The inverse of the `y`-parity, entrywise. -/
lemma parityY_inv_coe :
    (parityY⁻¹ : SL(2,ℂ)).1 = !![0, -1; 1, 0] := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [parityY]

/-- The inverse of the `x`-parity, entrywise. -/
lemma parityX_inv_coe :
    (parityX⁻¹ : SL(2,ℂ)).1 = !![0, -Complex.I; -Complex.I, 0] := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [parityX]

/-- The inverse of the first boost, entrywise, with real entries. -/
lemma boostA_inv_coe :
    (boostA⁻¹ : SL(2,ℂ)).1 = !![((2⁻¹ : ℝ) : ℂ), 0; 0, ((2 : ℝ) : ℂ)] := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boostA]

/-- The inverse of the second boost, entrywise, with real entries. -/
lemma boostB_inv_coe :
    (boostB⁻¹ : SL(2,ℂ)).1 = !![((3⁻¹ : ℝ) : ℂ), 0; 0, ((3 : ℝ) : ℂ)] := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boostB]

/-- The Lorentz action on a zero-derivative fermion pair `ψ̄_α ψ_β`. -/
lemma repLorentzGroup_Dbarψ_nil_mul_Dψ_nil (Λ : SL(2,ℂ)) (α β : Fin 2) :
    repLorentzGroup Λ (Dbarψ [] α * Dψ [] β) =
      ∑ γ, ∑ δ, ((Λ⁻¹).1 α γ * star ((Λ⁻¹).1 β δ)) •
        (Dbarψ [] γ * Dψ [] δ) := by
  have hsm : ∀ (f : Fin 2 → JetAlgebra) (y : JetAlgebra),
      (∑ x, f x) * y = ∑ x, f x * y := fun f y => by
    rw [show (∑ x, f x) * y = LinearMap.mulRight ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hms : ∀ (f : Fin 2 → JetAlgebra) (y : JetAlgebra),
      y * (∑ x, f x) = ∑ x, y * f x := fun f y => by
    rw [show y * (∑ x, f x) = LinearMap.mulLeft ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hsmul : ∀ (c d : ℂ) (x y : JetAlgebra),
      (c • x) * (d • y) = (c * d) • (x * y) := fun c d x y => by
    rw [smul_mul_smul_comm]
  rw [repLorentzGroup_apply_mul, repLorentzGroup_Dbarψ_nil, repLorentzGroup_Dψ_nil]
  simp only [hsm, hms, hsmul]

/-- The Lorentz action on a zero-derivative fermion pair `ψ_α ψ̄_β`. -/
lemma repLorentzGroup_Dψ_nil_mul_Dbarψ_nil (Λ : SL(2,ℂ)) (α β : Fin 2) :
    repLorentzGroup Λ (Dψ [] α * Dbarψ [] β) =
      ∑ γ, ∑ δ, (star ((Λ⁻¹).1 α γ) * (Λ⁻¹).1 β δ) •
        (Dψ [] γ * Dbarψ [] δ) := by
  have hsm : ∀ (f : Fin 2 → JetAlgebra) (y : JetAlgebra),
      (∑ x, f x) * y = ∑ x, f x * y := fun f y => by
    rw [show (∑ x, f x) * y = LinearMap.mulRight ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hms : ∀ (f : Fin 2 → JetAlgebra) (y : JetAlgebra),
      y * (∑ x, f x) = ∑ x, y * f x := fun f y => by
    rw [show y * (∑ x, f x) = LinearMap.mulLeft ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hsmul : ∀ (c d : ℂ) (x y : JetAlgebra),
      (c • x) * (d • y) = (c * d) • (x * y) := fun c d x y => by
    rw [smul_mul_smul_comm]
  rw [repLorentzGroup_apply_mul, repLorentzGroup_Dψ_nil, repLorentzGroup_Dbarψ_nil]
  simp only [hsm, hms, hsmul]

/-!

### The kill operator of the weight-six sector

-/

/-- The averaging operator over the Klein four-group of parity rotations. -/
noncomputable def kleinAvg : Module.End ℂ JetAlgebra :=
  (4 : ℂ)⁻¹ • (LinearMap.id + repLorentzGroup parityZ +
    repLorentzGroup parityY + repLorentzGroup parityX)

/-- The boost-weighted Klein average: an operator fixing every
  Lorentz-invariant vector and annihilating the neutral weight-six sector.
  The weights `-13/24, 8/3, -9/8` sum to one and are chosen so that
  `w₁ + w₂ t² + w₃ s² = 0` for `t² ∈ {4, 1/4}` and `s² ∈ {9, 1/9}`
  respectively, killing both eigendirections of the two boosts. -/
noncomputable def sixKill : Module.End ℂ JetAlgebra :=
  ((-13/24 : ℂ) • LinearMap.id + (8/3 : ℂ) • repLorentzGroup boostA +
    (-9/8 : ℂ) • repLorentzGroup boostB) ∘ₗ kleinAvg

/-- The Klein average, termwise. -/
lemma kleinAvg_apply (v : JetAlgebra) :
    kleinAvg v = (4 : ℂ)⁻¹ • (v + repLorentzGroup parityZ v +
      repLorentzGroup parityY v + repLorentzGroup parityX v) := by
  simp only [kleinAvg, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.id_apply]

/-- The kill operator, termwise. -/
lemma sixKill_apply (v : JetAlgebra) :
    sixKill v = (-13/24 : ℂ) • kleinAvg v +
      (8/3 : ℂ) • repLorentzGroup boostA (kleinAvg v) +
      (-9/8 : ℂ) • repLorentzGroup boostB (kleinAvg v) := by
  simp only [sixKill, LinearMap.comp_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.id_apply]

set_option maxHeartbeats 8000000 in
/-- The kill operator annihilates every embedded derivative field strength:
  the Klein average kills every component with an odd index pattern, and the
  boost combination kills the twelve surviving components. -/
lemma sixKill_fieldStrengthDeriv_singleton (ρ μ ν : Fin 1 ⊕ Fin 3) :
    sixKill (fieldStrengthDeriv {ρ} μ ν) = 0 := by
  rcases eq_or_ne μ ν with rfl | hμν
  · rw [fieldStrengthDeriv_self]
    exact map_zero _
  · have hK : kleinAvg (fieldStrengthDeriv {ρ} μ ν) =
        (((1 + paritySignZ ρ * (paritySignZ μ * paritySignZ ν) +
          paritySignY ρ * (paritySignY μ * paritySignY ν) +
          paritySignX ρ * (paritySignX μ * paritySignX ν)) / 4 : ℝ) : ℂ) •
          fieldStrengthDeriv {ρ} μ ν := by
      rw [kleinAvg_apply,
        repLorentzGroup_diag_fieldStrengthDeriv_singleton toLorentzGroup_parityZ,
        repLorentzGroup_diag_fieldStrengthDeriv_singleton toLorentzGroup_parityY,
        repLorentzGroup_diag_fieldStrengthDeriv_singleton toLorentzGroup_parityX]
      push_cast
      module
    rw [sixKill_apply, hK, map_smul, map_smul]
    rcases ρ with ρ | ρ <;> rcases μ with μ | μ <;> rcases ν with ν | ν <;>
      fin_cases ρ <;> fin_cases μ <;> fin_cases ν <;>
      first
      | (simp only [fieldStrengthDeriv_self, map_zero, smul_zero, add_zero]; done)
      | (norm_num [paritySignZ, paritySignY, paritySignX]; done)
      | (norm_num [paritySignZ, paritySignY, paritySignX]
         rw [repLorentzGroup_fieldStrengthDeriv_singleton boostA,
           repLorentzGroup_fieldStrengthDeriv_singleton boostB]
         simp only [Fintype.sum_sum_type, Fin.sum_univ_three, Fin.sum_univ_one,
           toLorentzGroup_boostA, toLorentzGroup_boostB]
         norm_num [boostMatA, boostMatB, fieldStrengthDeriv_self,
           fieldStrengthDeriv_inr_inl]
         push_cast
         module)

set_option maxHeartbeats 4000000 in
/-- The kill operator annihilates every zero-derivative pair `ψ̄_α ψ_β`: the
  Klein average kills the off-diagonal pairs and symmetrises the diagonal
  ones, which the boost combination then kills. -/
lemma sixKill_Dbarψ_mul_Dψ (α β : Fin 2) :
    sixKill (Dbarψ [] α * Dψ [] β) = 0 := by
  rw [sixKill_apply, kleinAvg_apply]
  fin_cases α <;> fin_cases β <;>
    · simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_nil, map_add, map_smul,
        map_sum, parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
        boostA_inv_coe, boostB_inv_coe, Fin.sum_univ_two, Fin.zero_eta,
        Fin.mk_one, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
        Matrix.cons_val_fin_one,
        star_zero, star_neg, star_one, Complex.star_def, Complex.conj_I,
        Complex.conj_ofReal, map_one, map_zero, map_neg, neg_mul, mul_neg,
        neg_neg,
        zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
        Complex.I_mul_I, one_mul, mul_one, smul_add, smul_smul, Finset.smul_sum]
      try push_cast
      try module

set_option maxHeartbeats 4000000 in
/-- The kill operator annihilates every zero-derivative pair `ψ_α ψ̄_β`. -/
lemma sixKill_Dψ_mul_Dbarψ (α β : Fin 2) :
    sixKill (Dψ [] α * Dbarψ [] β) = 0 := by
  rw [sixKill_apply, kleinAvg_apply]
  fin_cases α <;> fin_cases β <;>
    · simp only [repLorentzGroup_Dψ_nil_mul_Dbarψ_nil, map_add, map_smul,
        map_sum, parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
        boostA_inv_coe, boostB_inv_coe, Fin.sum_univ_two, Fin.zero_eta,
        Fin.mk_one, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
        Matrix.cons_val_fin_one,
        star_zero, star_neg, star_one, Complex.star_def, Complex.conj_I,
        Complex.conj_ofReal, map_one, map_zero, map_neg, neg_mul, mul_neg,
        neg_neg,
        zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
        Complex.I_mul_I, one_mul, mul_one, smul_add, smul_smul, Finset.smul_sum]
      try push_cast
      try module

/-- No Lorentz invariant of mass weight six: an invariant combination of the
  field-strength derivatives `∂_ρ F_{μν}` and the fermion pairs `ψ̄_α ψ_β`
  vanishes. -/
lemma eq_zero_of_mem_chargeCovSpan_six {y : JetAlgebra}
    (hy : y ∈ chargeCovSpan 6 0)
    (hinv : ∀ Λ : SL(2,ℂ), repLorentzGroup Λ y = y) : y = 0 := by
  have h := chargeCovSpan_six_le hy
  rw [Submodule.span_union, Submodule.span_union] at h
  obtain ⟨u, hu, w, hw, hy'⟩ := Submodule.mem_sup.mp h
  obtain ⟨u1, hu1, u2, hu2, hu'⟩ := Submodule.mem_sup.mp hu
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hu1
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hu2
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hw
  have hKy : kleinAvg y = y := by
    rw [kleinAvg_apply, hinv parityZ, hinv parityY, hinv parityX]
    module
  have hself : sixKill y = y := by
    rw [sixKill_apply, hKy, hinv boostA, hinv boostB]
    module
  have hkill : sixKill y = 0 := by
    rw [← hy', ← hu', ← ha, ← hd, ← he]
    simp only [map_add, map_sum, map_smul, sixKill_fieldStrengthDeriv_singleton,
      sixKill_Dbarψ_mul_Dψ, sixKill_Dψ_mul_Dbarψ, smul_zero,
      Finset.sum_const_zero, add_zero]
  exact hself.symm.trans hkill

/-!

### The transformation law of the second-derivative field strength

-/

set_option maxHeartbeats 2000000 in
/-- The Lorentz action on the three-derivative-index B-boson jet coordinates:
  all four indices transform contravariantly, by the columns of the Lorentz
  matrix. -/
lemma _root_.StandardModel.BBoson.JetComponentSpace.repLorentzGroup_basis_dB_triple
    (Λ : SL(2,ℂ)) (ρ τ μ ν : Fin 1 ⊕ Fin 3) :
    BBoson.JetComponentSpace.repLorentzGroup Λ
      (BBoson.JetComponentSpace.basis (.dB {ρ, τ, μ} ν)) =
      ∑ r, ∑ s, ∑ a, ∑ b, ((Lorentz.SL2C.toLorentzGroup Λ).1 r ρ *
        ((Lorentz.SL2C.toLorentzGroup Λ).1 s τ *
          ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ *
          (Lorentz.SL2C.toLorentzGroup Λ).1 b ν))) •
        BBoson.JetComponentSpace.basis (.dB {r, s, a} b) := by
  have htriple : ∀ x y z : Fin 1 ⊕ Fin 3,
      LagrangianTheory.dualRealJetAlgebraBasis ({x, y, z} : Multiset (Fin 1 ⊕ Fin 3)) =
        SymmetricAlgebra.ι ℝ (Module.Dual ℝ Lorentz.CoVector)
            (Lorentz.CoVector.basis.dualBasis x) *
          (SymmetricAlgebra.ι ℝ (Module.Dual ℝ Lorentz.CoVector)
            (Lorentz.CoVector.basis.dualBasis y) *
           SymmetricAlgebra.ι ℝ (Module.Dual ℝ Lorentz.CoVector)
            (Lorentz.CoVector.basis.dualBasis z)) := fun x y z => by
    rw [← BBoson.dualRealJetAlgebraBasis_singleton,
      ← BBoson.dualRealJetAlgebraBasis_singleton,
      ← BBoson.dualRealJetAlgebraBasis_singleton,
      BBoson.dualRealJetAlgebraBasis_mul, BBoson.dualRealJetAlgebraBasis_mul,
      Multiset.singleton_add, Multiset.singleton_add, ← Multiset.insert_eq_cons,
      ← Multiset.insert_eq_cons]
  have hmul : ∀ x y : DerivAlgebraReal,
      DerivAlgebraReal.repLorentzGroup Λ (x * y) =
        DerivAlgebraReal.repLorentzGroup Λ x *
          DerivAlgebraReal.repLorentzGroup Λ y := fun x y =>
    map_mul (SymmetricAlgebra.lift (SymmetricAlgebra.ι ℝ _ ∘ₗ
      Lorentz.CoVector.sl2Rep.dual Λ)) x y
  have happ : BBoson.JetComponentSpace.repLorentzGroup Λ
      (LagrangianTheory.dualRealJetAlgebraBasis {ρ, τ, μ} ⊗ₜ[ℝ]
        StandardModel.BBoson.basis.dualBasis ν) =
      (DerivAlgebraReal.repLorentzGroup Λ
        (LagrangianTheory.dualRealJetAlgebraBasis {ρ, τ, μ})) ⊗ₜ[ℝ]
      (BBoson.repLorentzGroup.dual Λ
        (StandardModel.BBoson.basis.dualBasis ν)) := rfl
  rw [BBoson.jetComponentSpace_basis_dB, happ, htriple, hmul, hmul,
    DerivAlgebraReal.repLorentzGroup_apply_ι,
    DerivAlgebraReal.repLorentzGroup_apply_ι,
    DerivAlgebraReal.repLorentzGroup_apply_ι,
    Lorentz.CoVector.sl2Rep_dual_dualBasis, Lorentz.CoVector.sl2Rep_dual_dualBasis,
    Lorentz.CoVector.sl2Rep_dual_dualBasis,
    BBoson.repLorentzGroup_dual_dualBasis]
  simp only [map_sum, map_smul, Finset.sum_mul, Finset.mul_sum,
    smul_mul_smul_comm, TensorProduct.sum_tmul, TensorProduct.tmul_sum,
    ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, Finset.smul_sum,
    smul_smul, BBoson.jetComponentSpace_basis_dB, htriple]
  conv_lhs => enter [2, i, 2, j]; rw [Finset.sum_comm]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, i, 2, j]; rw [Finset.sum_comm]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  conv_lhs => enter [2, i, 2, j]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  module

set_option maxHeartbeats 2000000 in
/-- The transformation law of the second-derivative field strength on the
  B-boson jet algebra: a four-index tensor. -/
lemma _root_.StandardModel.BBoson.JetAlgebra.repLorentzGroup_fieldStrengthDeriv_pair
    (Λ : SL(2,ℂ)) (ρ τ μ ν : Fin 1 ⊕ Fin 3) :
    BBoson.JetAlgebra.repLorentzGroup Λ
      (BBoson.JetAlgebra.fieldStrengthDeriv {ρ, τ} μ ν) =
      ∑ r, ∑ s, ∑ a, ∑ b, ((Lorentz.SL2C.toLorentzGroup Λ).1 r ρ *
        ((Lorentz.SL2C.toLorentzGroup Λ).1 s τ *
          ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ *
          (Lorentz.SL2C.toLorentzGroup Λ).1 b ν))) •
        BBoson.JetAlgebra.fieldStrengthDeriv {r, s} a b := by
  have hFS : ∀ r s a b : Fin 1 ⊕ Fin 3,
      BBoson.JetAlgebra.fieldStrengthDeriv ({r, s} : Multiset _) a b =
        BBoson.JetAlgebra.ofGenerator (.dB {r, s, a} b) -
          BBoson.JetAlgebra.ofGenerator (.dB {r, s, b} a) := fun r s a b => by
    rw [BBoson.JetAlgebra.fieldStrengthDeriv,
      show ({r, s} : Multiset (Fin 1 ⊕ Fin 3)) + {a} = {r, s, a} from by
        rw [Multiset.insert_eq_cons, Multiset.cons_add, Multiset.singleton_add,
          ← Multiset.insert_eq_cons, ← Multiset.insert_eq_cons],
      show ({r, s} : Multiset (Fin 1 ⊕ Fin 3)) + {b} = {r, s, b} from by
        rw [Multiset.insert_eq_cons, Multiset.cons_add, Multiset.singleton_add,
          ← Multiset.insert_eq_cons, ← Multiset.insert_eq_cons]]
  simp only [hFS]
  rw [map_sub, BBoson.JetAlgebra.ofGenerator, BBoson.JetAlgebra.ofGenerator,
    BBoson.JetAlgebra.repLorentzGroup_apply_ι,
    BBoson.JetAlgebra.repLorentzGroup_apply_ι,
    BBoson.JetComponentSpace.repLorentzGroup_basis_dB_triple,
    BBoson.JetComponentSpace.repLorentzGroup_basis_dB_triple]
  simp only [map_sum, map_smul, smul_sub, Finset.sum_sub_distrib,
    BBoson.JetAlgebra.ofGenerator]
  rw [sub_right_inj]
  conv_rhs => enter [2, r, 2, s]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  ring

/-- The transformation of the complexified second-derivative field strength. -/
lemma _root_.StandardModel.BBoson.JetAlgebra.complexRepLorentzGroup_one_tmul_fieldStrengthDeriv_pair
    (Λ : SL(2,ℂ)) (ρ τ μ ν : Fin 1 ⊕ Fin 3) :
    BBoson.JetAlgebra.complexRepLorentzGroup Λ
        ((1 : ℂ) ⊗ₜ[ℝ] BBoson.JetAlgebra.fieldStrengthDeriv {ρ, τ} μ ν) =
      ∑ r, ∑ s, ∑ a, ∑ b, ((Lorentz.SL2C.toLorentzGroup Λ).1 r ρ *
        ((Lorentz.SL2C.toLorentzGroup Λ).1 s τ *
          ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ *
          (Lorentz.SL2C.toLorentzGroup Λ).1 b ν))) •
        ((1 : ℂ) ⊗ₜ[ℝ] BBoson.JetAlgebra.fieldStrengthDeriv {r, s} a b) := by
  rw [show BBoson.JetAlgebra.complexRepLorentzGroup Λ
      ((1 : ℂ) ⊗ₜ[ℝ] BBoson.JetAlgebra.fieldStrengthDeriv {ρ, τ} μ ν) =
      (1 : ℂ) ⊗ₜ[ℝ] BBoson.JetAlgebra.repLorentzGroup Λ
        (BBoson.JetAlgebra.fieldStrengthDeriv {ρ, τ} μ ν) from rfl,
    BBoson.JetAlgebra.repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul]

set_option maxHeartbeats 2000000 in
/-- The transformation law of the embedded second-derivative field strength:
  a four-index tensor, all indices transforming by the Lorentz matrix. -/
lemma repLorentzGroup_fieldStrengthDeriv_pair (Λ : SL(2,ℂ))
    (ρ τ μ ν : Fin 1 ⊕ Fin 3) :
    repLorentzGroup Λ (fieldStrengthDeriv {ρ, τ} μ ν) =
      ∑ r, ∑ s, ∑ a, ∑ b, ((((Lorentz.SL2C.toLorentzGroup Λ).1 r ρ *
        ((Lorentz.SL2C.toLorentzGroup Λ).1 s τ *
          ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ *
          (Lorentz.SL2C.toLorentzGroup Λ).1 b ν)) : ℝ)) : ℂ) •
        fieldStrengthDeriv {r, s} a b := by
  have hconv : ∀ (r : ℝ) (X : ℂ ⊗[ℝ] BBoson.JetAlgebra),
      (r • X) ⊗ₜ[ℂ] (1 : LeptonSinglet.JetAlgebra) = ((r : ℂ)) • (X ⊗ₜ[ℂ] 1) := by
    intro r X
    rw [← algebraMap_smul (R := ℝ) ℂ r X, ← TensorProduct.smul_tmul']
    rfl
  have happ : repLorentzGroup Λ (((1 : ℂ) ⊗ₜ[ℝ]
      BBoson.JetAlgebra.fieldStrengthDeriv {ρ, τ} μ ν) ⊗ₜ[ℂ]
        (1 : LeptonSinglet.JetAlgebra)) =
      (BBoson.JetAlgebra.complexRepLorentzGroup Λ ((1 : ℂ) ⊗ₜ[ℝ]
        BBoson.JetAlgebra.fieldStrengthDeriv {ρ, τ} μ ν)) ⊗ₜ[ℂ]
      (LeptonSinglet.JetAlgebra.repLorentzGroup Λ
        (1 : LeptonSinglet.JetAlgebra)) := rfl
  rw [fieldStrengthDeriv, happ,
    BBoson.JetAlgebra.complexRepLorentzGroup_one_tmul_fieldStrengthDeriv_pair,
    LeptonSinglet.JetAlgebra.repLorentzGroup_apply_one]
  simp only [TensorProduct.sum_tmul, hconv, fieldStrengthDeriv]

/-!

### Commutation and anticommutation of the covariant factors

-/

/-- The embedded field-strength derivatives commute: they live in the
  commutative bosonic factor of the jet algebra. -/
lemma fieldStrengthDeriv_mul_comm (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (μ ν ρ τ : Fin 1 ⊕ Fin 3) :
    fieldStrengthDeriv s μ ν * fieldStrengthDeriv s' ρ τ =
      fieldStrengthDeriv s' ρ τ * fieldStrengthDeriv s μ ν := by
  rw [fieldStrengthDeriv, fieldStrengthDeriv, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul,
    mul_comm (BBoson.JetAlgebra.fieldStrengthDeriv s μ ν)]

set_option maxHeartbeats 16000000 in
/-- The embedded lepton-linear and conjugate-linear elements anticommute:
  both are odd elements of the exterior factor of the jet algebra. -/
lemma leptonLinearIncl_mul_conjLeptonLinearIncl_anticomm (x : LeptonLinear)
    (y : ConjLeptonLinear) :
    leptonLinearIncl x * conjLeptonLinearIncl y =
      -(conjLeptonLinearIncl y * leptonLinearIncl x) := by
  have hz₁ : ∀ z : JetAlgebra, 0 * z = 0 := fun z => zero_mul z
  have hz₂ : ∀ z : JetAlgebra, z * 0 = 0 := fun z => mul_zero z
  have hd₁ : ∀ u v w : JetAlgebra, (u + v) * w = u * w + v * w := by grind
  have hd₂ : ∀ u v w : JetAlgebra, u * (v + w) = u * v + u * w := by grind
  have hι : ∀ (a : LeptonComponent) (b : ConjLeptonComponent),
      leptonComponentIncl a * conjLeptonComponentIncl b =
        -(conjLeptonComponentIncl b * leptonComponentIncl a) := fun a b => by
    rw [leptonComponentIncl_apply, conjLeptonComponentIncl_apply]
    exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, hz₁, hz₂, neg_zero]
  | add a b ha hb => rw [map_add, hd₁, hd₂, ha, hb, neg_add]
  | tmul p a =>
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero, hz₂, hz₁, neg_zero]
    | add c d hc hd => rw [map_add, hd₂, hd₁, hc, hd, neg_add]
    | tmul q b =>
      rw [leptonLinearIncl_tmul, conjLeptonLinearIncl_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        hι a b, mul_comm q p, TensorProduct.tmul_neg]

/-- The covariant lepton derivatives anticommute with the conjugate covariant
  derivatives. -/
lemma Dψ_mul_Dbarψ_anticomm (l l' : List (Fin 1 ⊕ Fin 3)) (α β : Fin 2) :
    Dψ l α * Dbarψ l' β = -(Dbarψ l' β * Dψ l α) := by
  rw [Dψ_eq_leptonLinearIncl, Dbarψ_eq_conjLeptonLinearIncl,
    leptonLinearIncl_mul_conjLeptonLinearIncl_anticomm]

set_option maxHeartbeats 16000000 in
/-- Two embedded lepton-linear elements anticommute. -/
lemma leptonLinearIncl_mul_leptonLinearIncl_anticomm (x y : LeptonLinear) :
    leptonLinearIncl x * leptonLinearIncl y =
      -(leptonLinearIncl y * leptonLinearIncl x) := by
  have hz₁ : ∀ z : JetAlgebra, 0 * z = 0 := fun z => zero_mul z
  have hz₂ : ∀ z : JetAlgebra, z * 0 = 0 := fun z => mul_zero z
  have hd₁ : ∀ u v w : JetAlgebra, (u + v) * w = u * w + v * w := by grind
  have hd₂ : ∀ u v w : JetAlgebra, u * (v + w) = u * v + u * w := by grind
  have hι : ∀ a b : LeptonComponent,
      leptonComponentIncl a * leptonComponentIncl b =
        -(leptonComponentIncl b * leptonComponentIncl a) := fun a b => by
    rw [leptonComponentIncl_apply, leptonComponentIncl_apply]
    exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, hz₁, hz₂, neg_zero]
  | add a b ha hb => rw [map_add, hd₁, hd₂, ha, hb, neg_add]
  | tmul p a =>
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero, hz₂, hz₁, neg_zero]
    | add c d hc hd => rw [map_add, hd₂, hd₁, hc, hd, neg_add]
    | tmul q b =>
      rw [leptonLinearIncl_tmul, leptonLinearIncl_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        hι a b, mul_comm q p, TensorProduct.tmul_neg]

/-- Two covariant lepton derivatives anticommute. -/
lemma Dψ_mul_Dψ_anticomm (l l' : List (Fin 1 ⊕ Fin 3)) (α β : Fin 2) :
    Dψ l α * Dψ l' β = -(Dψ l' β * Dψ l α) := by
  rw [Dψ_eq_leptonLinearIncl, Dψ_eq_leptonLinearIncl,
    leptonLinearIncl_mul_leptonLinearIncl_anticomm]

/-!

### Parametric boosts along the three axes

The one-parameter families of boosts `diag(t, t⁻¹)` (along `z`) and their
conjugates along `x` and `y`, with symbolic Lorentz matrices in `t`.

-/

/-- The lift `diag(t, t⁻¹)` of the boost along the `z`-axis with rapidity
  `2 log t`. -/
noncomputable def boostZel (t : ℝ) (ht : t ≠ 0) : SL(2,ℂ) :=
  ⟨!![(t : ℂ), 0; 0, (t : ℂ)⁻¹], by
    have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
    rw [Matrix.det_fin_two_of]
    simp [mul_inv_cancel₀ htc]⟩

/-- The lift of the boost along the `x`-axis with rapidity `2 log t`. -/
noncomputable def boostXel (t : ℝ) (ht : t ≠ 0) : SL(2,ℂ) :=
  ⟨!![((t : ℂ) + (t : ℂ)⁻¹)/2, ((t : ℂ) - (t : ℂ)⁻¹)/2;
      ((t : ℂ) - (t : ℂ)⁻¹)/2, ((t : ℂ) + (t : ℂ)⁻¹)/2], by
    have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
    rw [Matrix.det_fin_two_of]
    field_simp
    ring⟩

/-- The lift of the boost along the `y`-axis with rapidity `2 log t`. -/
noncomputable def boostYel (t : ℝ) (ht : t ≠ 0) : SL(2,ℂ) :=
  ⟨!![((t : ℂ) + (t : ℂ)⁻¹)/2, -Complex.I * ((t : ℂ) - (t : ℂ)⁻¹)/2;
      Complex.I * ((t : ℂ) - (t : ℂ)⁻¹)/2, ((t : ℂ) + (t : ℂ)⁻¹)/2], by
    have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
    have h2 : -Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2 *
        (Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2) =
        ((t : ℂ) - (t : ℂ)⁻¹) / 2 * (((t : ℂ) - (t : ℂ)⁻¹) / 2) := by
      have hI : -Complex.I * Complex.I = 1 := by
        rw [neg_mul, Complex.I_mul_I, neg_neg]
      calc -Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2 *
            (Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2)
          = (-Complex.I * Complex.I) *
              (((t : ℂ) - (t : ℂ)⁻¹) / 2 * (((t : ℂ) - (t : ℂ)⁻¹) / 2)) := by
            ring
        _ = ((t : ℂ) - (t : ℂ)⁻¹) / 2 * (((t : ℂ) - (t : ℂ)⁻¹) / 2) := by
            rw [hI, one_mul]
    rw [Matrix.det_fin_two_of, h2]
    field_simp
    ring⟩

/-- The Lorentz matrix of `boostZel t`: `ch = (t² + t⁻²)/2` on the time-time
  and `zz` entries, `-sh = -(t² - t⁻²)/2` on the mixed entries. -/
noncomputable def boostMatZ (t : ℝ) : (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → ℝ
  | Sum.inl _, Sum.inl _ => (t^2 + (t⁻¹)^2)/2
  | Sum.inl _, Sum.inr 2 => -((t^2 - (t⁻¹)^2)/2)
  | Sum.inr 2, Sum.inl _ => -((t^2 - (t⁻¹)^2)/2)
  | Sum.inr 0, Sum.inr 0 => 1
  | Sum.inr 1, Sum.inr 1 => 1
  | Sum.inr 2, Sum.inr 2 => (t^2 + (t⁻¹)^2)/2
  | _, _ => 0

/-- The Lorentz matrix of `boostXel t`. -/
noncomputable def boostMatX (t : ℝ) : (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → ℝ
  | Sum.inl _, Sum.inl _ => (t^2 + (t⁻¹)^2)/2
  | Sum.inl _, Sum.inr 0 => -((t^2 - (t⁻¹)^2)/2)
  | Sum.inr 0, Sum.inl _ => -((t^2 - (t⁻¹)^2)/2)
  | Sum.inr 0, Sum.inr 0 => (t^2 + (t⁻¹)^2)/2
  | Sum.inr 1, Sum.inr 1 => 1
  | Sum.inr 2, Sum.inr 2 => 1
  | _, _ => 0

/-- The Lorentz matrix of `boostYel t`. -/
noncomputable def boostMatY (t : ℝ) : (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → ℝ
  | Sum.inl _, Sum.inl _ => (t^2 + (t⁻¹)^2)/2
  | Sum.inl _, Sum.inr 1 => -((t^2 - (t⁻¹)^2)/2)
  | Sum.inr 1, Sum.inl _ => -((t^2 - (t⁻¹)^2)/2)
  | Sum.inr 0, Sum.inr 0 => 1
  | Sum.inr 1, Sum.inr 1 => (t^2 + (t⁻¹)^2)/2
  | Sum.inr 2, Sum.inr 2 => 1
  | _, _ => 0

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- The Lorentz matrix of the parametric `z`-boost. -/
lemma toLorentzGroup_boostZel (t : ℝ) (ht : t ≠ 0) (a b : Fin 1 ⊕ Fin 3) :
    (Lorentz.SL2C.toLorentzGroup (boostZel t ht)).1 a b = boostMatZ t a b := by
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  refine Complex.ofReal_injective ?_
  rw [Lorentz.SL2C.toLorentzGroup_eq_trace]
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    · try simp [boostZel, boostMatZ, PauliMatrix.pauliSelfAdjoint',
        PauliMatrix.pauliMatrix, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose, Matrix.diag, Complex.conj_ofNat,
        Complex.conj_ofReal, Complex.conj_I, Complex.I_sq]
      try simp [Matrix.vecMul, Matrix.vecHead, Matrix.vecTail]
      try push_cast
      try field_simp
      try ring_nf
      try norm_num [Complex.I_sq, Complex.conj_ofNat]
      try ring

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- The Lorentz matrix of the parametric `x`-boost. -/
lemma toLorentzGroup_boostXel (t : ℝ) (ht : t ≠ 0) (a b : Fin 1 ⊕ Fin 3) :
    (Lorentz.SL2C.toLorentzGroup (boostXel t ht)).1 a b = boostMatX t a b := by
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  refine Complex.ofReal_injective ?_
  rw [Lorentz.SL2C.toLorentzGroup_eq_trace]
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    · try simp [boostXel, boostMatX, PauliMatrix.pauliSelfAdjoint',
        PauliMatrix.pauliMatrix, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose, Matrix.diag, Complex.conj_ofNat,
        Complex.conj_ofReal, Complex.conj_I, Complex.I_sq]
      try simp [Matrix.vecMul, Matrix.vecHead, Matrix.vecTail]
      try push_cast
      try field_simp
      try ring_nf
      try norm_num [Complex.I_sq, Complex.conj_ofNat]
      try ring

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- The Lorentz matrix of the parametric `y`-boost. -/
lemma toLorentzGroup_boostYel (t : ℝ) (ht : t ≠ 0) (a b : Fin 1 ⊕ Fin 3) :
    (Lorentz.SL2C.toLorentzGroup (boostYel t ht)).1 a b = boostMatY t a b := by
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  refine Complex.ofReal_injective ?_
  rw [Lorentz.SL2C.toLorentzGroup_eq_trace]
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    · try simp [boostYel, boostMatY, PauliMatrix.pauliSelfAdjoint',
        PauliMatrix.pauliMatrix, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose, Matrix.diag, Complex.conj_ofNat,
        Complex.conj_ofReal, Complex.conj_I, Complex.I_sq]
      try simp [Matrix.vecMul, Matrix.vecHead, Matrix.vecTail]
      try push_cast
      try field_simp
      try ring_nf
      try norm_num [Complex.I_sq, Complex.conj_ofNat]
      try ring

/-- The inverse of the parametric `z`-boost is the boost at the inverse
  parameter. -/
lemma boostZel_inv (t : ℝ) (ht : t ≠ 0) :
    (boostZel t ht)⁻¹ = boostZel t⁻¹ (inv_ne_zero ht) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  fin_cases i <;> fin_cases j <;>
    simp [boostZel, Complex.ofReal_inv, inv_inv]

/-- The inverse of the parametric `x`-boost is the boost at the inverse
  parameter. -/
lemma boostXel_inv (t : ℝ) (ht : t ≠ 0) :
    (boostXel t ht)⁻¹ = boostXel t⁻¹ (inv_ne_zero ht) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  fin_cases i <;> fin_cases j <;>
    · simp [boostXel, Complex.ofReal_inv, inv_inv]
      try ring

/-- The inverse of the parametric `y`-boost is the boost at the inverse
  parameter. -/
lemma boostYel_inv (t : ℝ) (ht : t ≠ 0) :
    (boostYel t ht)⁻¹ = boostYel t⁻¹ (inv_ne_zero ht) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  fin_cases i <;> fin_cases j <;>
    · simp [boostYel, Complex.ofReal_inv, inv_inv]
      try ring

/-- The inverse of the parametric `z`-boost, entrywise, with real entries. -/
lemma boostZel_inv_coe (t : ℝ) (ht : t ≠ 0) :
    ((boostZel t ht)⁻¹ : SL(2,ℂ)).1 =
      !![(((t⁻¹ : ℝ)) : ℂ), 0; 0, ((t : ℝ) : ℂ)] := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boostZel]

/-- The inverse of the parametric `x`-boost, entrywise. -/
lemma boostXel_inv_coe (t : ℝ) (ht : t ≠ 0) :
    ((boostXel t ht)⁻¹ : SL(2,ℂ)).1 =
      !![((t : ℂ) + (t : ℂ)⁻¹)/2, -(((t : ℂ) - (t : ℂ)⁻¹)/2);
         -(((t : ℂ) - (t : ℂ)⁻¹)/2), ((t : ℂ) + (t : ℂ)⁻¹)/2] := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boostXel]

/-- The inverse of the parametric `y`-boost, entrywise. -/
lemma boostYel_inv_coe (t : ℝ) (ht : t ≠ 0) :
    ((boostYel t ht)⁻¹ : SL(2,ℂ)).1 =
      !![((t : ℂ) + (t : ℂ)⁻¹)/2, Complex.I * ((t : ℂ) - (t : ℂ)⁻¹)/2;
         -(Complex.I * ((t : ℂ) - (t : ℂ)⁻¹)/2), ((t : ℂ) + (t : ℂ)⁻¹)/2] := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;> · simp [boostYel]; try ring

/-- The Lorentz matrix of the inverse `z`-boost: the boost matrix at the
  inverse parameter. -/
lemma toLorentzGroup_boostZel_inv (t : ℝ) (ht : t ≠ 0) (a b : Fin 1 ⊕ Fin 3) :
    (Lorentz.SL2C.toLorentzGroup (boostZel t ht)⁻¹).1 a b = boostMatZ t⁻¹ a b := by
  rw [boostZel_inv, toLorentzGroup_boostZel]

/-- The Lorentz matrix of the inverse `x`-boost. -/
lemma toLorentzGroup_boostXel_inv (t : ℝ) (ht : t ≠ 0) (a b : Fin 1 ⊕ Fin 3) :
    (Lorentz.SL2C.toLorentzGroup (boostXel t ht)⁻¹).1 a b = boostMatX t⁻¹ a b := by
  rw [boostXel_inv, toLorentzGroup_boostXel]

/-- The Lorentz matrix of the inverse `y`-boost. -/
lemma toLorentzGroup_boostYel_inv (t : ℝ) (ht : t ≠ 0) (a b : Fin 1 ⊕ Fin 3) :
    (Lorentz.SL2C.toLorentzGroup (boostYel t ht)⁻¹).1 a b = boostMatY t⁻¹ a b := by
  rw [boostYel_inv, toLorentzGroup_boostYel]

/-!

### The four invariants in monomial form

-/

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- The Maxwell term as an explicit combination of the six independent
  field-strength squares. -/
lemma maxwellTerm_eq : maxwellTerm =
    (-2 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0))
    + (-2 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1))
    + (-2 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2))
    + (2 : ℂ) • (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1))
    + (2 : ℂ) • (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2))
    + (2 : ℂ) • (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) := by
  have hz₁ : ∀ z : JetAlgebra, 0 * z = 0 := fun z => zero_mul z
  have hz₂ : ∀ z : JetAlgebra, z * 0 = 0 := fun z => mul_zero z
  have hnm : ∀ u v : JetAlgebra, (-u) * v = -(u * v) := by grind
  have hmn : ∀ u v : JetAlgebra, u * (-v) = -(u * v) := by grind
  rw [maxwellTerm]
  simp only [Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three,
    minkowskiMatrix.inl_0_inl_0, minkowskiMatrix.inr_i_inr_i,
    fieldStrengthDeriv_self, hz₁, hz₂, smul_zero, add_zero, zero_add]
  simp only [
    show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) =
      -fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) from
      fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 0),
    show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) =
      -fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) from
      fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 1),
    show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) =
      -fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) from
      fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 2),
    show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) =
      -fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) from
      fieldStrengthDeriv_antisymm {} (Sum.inr 0) (Sum.inr 1),
    show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) =
      -fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) from
      fieldStrengthDeriv_antisymm {} (Sum.inr 0) (Sum.inr 2),
    show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) =
      -fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) from
      fieldStrengthDeriv_antisymm {} (Sum.inr 1) (Sum.inr 2),
    hnm, hmn, neg_neg]
  push_cast
  module

set_option maxHeartbeats 8000000 in
set_option linter.unusedSimpArgs false in
/-- The theta term as an explicit combination of the three pair-partition
  products of field strengths. -/
lemma thetaTerm_eq : thetaTerm =
    (8 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2))
    + (-8 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2))
    + (8 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) := by
  have hnm : ∀ u v : JetAlgebra, (-u) * v = -(u * v) := by grind
  have hmn : ∀ u v : JetAlgebra, u * (-v) = -(u * v) := by grind
  rw [thetaTerm]
  conv_lhs =>
    enter [2, p]
    rw [show (1 : Fin 4) = (0 : Fin 3).succ from rfl,
      show (2 : Fin 4) = (1 : Fin 3).succ from rfl,
      show (3 : Fin 4) = (2 : Fin 3).succ from rfl]
  rw [Finset.univ_perm_fin_succ, Finset.sum_map, Fintype.sum_prod_type]
  conv_lhs =>
    enter [2, i]
    rw [Finset.univ_perm_fin_succ, Finset.sum_map, Fintype.sum_prod_type]
  conv_lhs =>
    enter [2, i, 2, j]
    rw [Finset.univ_perm_fin_succ, Finset.sum_map, Fintype.sum_prod_type]
  conv_lhs =>
    enter [2, i, 2, j, 2, k]
    rw [Fintype.sum_subsingleton _ (1 : Equiv.Perm (Fin 1))]
  simp only [Equiv.coe_toEmbedding, Fin.sum_univ_four, Fin.sum_univ_three,
    Fin.sum_univ_two,
    show ((1 : Fin 3)) = (0 : Fin 2).succ from rfl,
    show ((2 : Fin 3)) = (1 : Fin 2).succ from rfl,
    Equiv.Perm.decomposeFin_symm_of_one,
    Equiv.Perm.decomposeFin.symm_sign,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one,
    Equiv.Perm.decomposeFin_symm_apply_succ]
  simp only [show ((0 : Fin 2).succ) = (1 : Fin 3) from rfl,
    show ((1 : Fin 2).succ) = (2 : Fin 3) from rfl,
    show ((0 : Fin 3).succ) = (1 : Fin 4) from rfl,
    show ((1 : Fin 3).succ) = (2 : Fin 4) from rfl,
    show ((2 : Fin 3).succ) = (3 : Fin 4) from rfl,
    Equiv.swap_self, Equiv.Perm.sign_refl, Equiv.refl_apply, Equiv.Perm.sign_one,
    Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne,
    Equiv.Perm.sign_swap', Fin.reduceEq, reduceIte, ne_eq, not_false_iff,
    show ((finSumFinEquiv (m := 1) (n := 3)).symm 0) = Sum.inl 0 from rfl,
    show ((finSumFinEquiv (m := 1) (n := 3)).symm 1) = Sum.inr 0 from rfl,
    show ((finSumFinEquiv (m := 1) (n := 3)).symm 2) = Sum.inr 1 from rfl,
    show ((finSumFinEquiv (m := 1) (n := 3)).symm 3) = Sum.inr 2 from rfl,
    Units.val_one, Units.val_neg, one_smul, neg_smul, one_mul, mul_one]
  simp only [
    show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) =
      -fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) from
      fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 0),
    show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) =
      -fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) from
      fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 1),
    show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) =
      -fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) from
      fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 2),
    show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) =
      -fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) from
      fieldStrengthDeriv_antisymm {} (Sum.inr 0) (Sum.inr 1),
    show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) =
      -fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) from
      fieldStrengthDeriv_antisymm {} (Sum.inr 0) (Sum.inr 2),
    show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) =
      -fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) from
      fieldStrengthDeriv_antisymm {} (Sum.inr 1) (Sum.inr 2),
    hnm, hmn, neg_neg]
  simp only [
    show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) =
      fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) from
      fieldStrengthDeriv_mul_comm {} {} _ _ _ _,
    show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) =
      fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) from
      fieldStrengthDeriv_mul_comm {} {} _ _ _ _,
    show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) =
      fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) from
      fieldStrengthDeriv_mul_comm {} {} _ _ _ _]
  module

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

/-!

### The symmetrised boost average on the weight-eight sector

For each axis `T ∈ {Z, X, Y}` the paired boost actions `rep(boost) + rep(boost⁻¹)`
at `t` and `t⁻¹` act on the Klein-symmetric weight-eight basis vectors with
even coefficients in the boost parameter.  A rational combination of the
paired boosts at `t = 2, 3, 4` together with the identity (`boostProjZ/X/Y`)
realises the Klein-restricted single-axis averages, and their mean `opS`
fixes every Lorentz-invariant vector while acting on the weight-eight basis
by an explicit rational matrix (the `opS_*` stage lemmas below).

-/

section SectorEight

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-- Left distribution in the jet algebra, in a form usable by `simp`. -/
lemma mul_add_jet (x y z : JetAlgebra) : x * (y + z) = x * y + x * z := by grind

/-- Right distribution in the jet algebra, in a form usable by `simp`. -/
lemma add_mul_jet (x y z : JetAlgebra) : (x + y) * z = x * z + y * z := by grind

/-- Scalar rearrangement of a product of two scaled elements. -/
lemma smul_mul_smul_jet (c d : ℂ) (x y : JetAlgebra) :
    (c • x) * (d • y) = (c * d) • (x * y) := by
  rw [smul_mul_smul_comm]

/-- Scalars pull out of the left factor of a product. -/
lemma smul_mul_jet (c : ℂ) (x y : JetAlgebra) : (c • x) * y = c • (x * y) := by
  rw [smul_mul_assoc]

/-- Scalars pull out of the right factor of a product. -/
lemma mul_smul_jet (c : ℂ) (x y : JetAlgebra) : x * (c • y) = c • (x * y) := by
  rw [mul_smul_comm]

/-- Reordering the two derivative indices of a second-derivative field
  strength. -/
lemma fieldStrengthDeriv_pair_swap (r s a b : Fin 1 ⊕ Fin 3) :
    fieldStrengthDeriv {r, s} a b = fieldStrengthDeriv {s, r} a b := by
  have h : ({r, s} : Multiset (Fin 1 ⊕ Fin 3)) = {s, r} := Multiset.cons_swap r s 0
  rw [h]

lemma boostMatZ_00 (t : ℝ) : boostMatZ t (Sum.inl 0) (Sum.inl 0) = (t ^ 2 + t⁻¹ ^ 2) / 2 := rfl
lemma boostMatZ_01 (t : ℝ) : boostMatZ t (Sum.inl 0) (Sum.inr 0) = 0 := rfl
lemma boostMatZ_02 (t : ℝ) : boostMatZ t (Sum.inl 0) (Sum.inr 1) = 0 := rfl
lemma boostMatZ_03 (t : ℝ) : boostMatZ t (Sum.inl 0) (Sum.inr 2) = -((t ^ 2 - t⁻¹ ^ 2) / 2) := rfl
lemma boostMatZ_10 (t : ℝ) : boostMatZ t (Sum.inr 0) (Sum.inl 0) = 0 := rfl
lemma boostMatZ_11 (t : ℝ) : boostMatZ t (Sum.inr 0) (Sum.inr 0) = 1 := rfl
lemma boostMatZ_12 (t : ℝ) : boostMatZ t (Sum.inr 0) (Sum.inr 1) = 0 := rfl
lemma boostMatZ_13 (t : ℝ) : boostMatZ t (Sum.inr 0) (Sum.inr 2) = 0 := rfl
lemma boostMatZ_20 (t : ℝ) : boostMatZ t (Sum.inr 1) (Sum.inl 0) = 0 := rfl
lemma boostMatZ_21 (t : ℝ) : boostMatZ t (Sum.inr 1) (Sum.inr 0) = 0 := rfl
lemma boostMatZ_22 (t : ℝ) : boostMatZ t (Sum.inr 1) (Sum.inr 1) = 1 := rfl
lemma boostMatZ_23 (t : ℝ) : boostMatZ t (Sum.inr 1) (Sum.inr 2) = 0 := rfl
lemma boostMatZ_30 (t : ℝ) : boostMatZ t (Sum.inr 2) (Sum.inl 0) = -((t ^ 2 - t⁻¹ ^ 2) / 2) := rfl
lemma boostMatZ_31 (t : ℝ) : boostMatZ t (Sum.inr 2) (Sum.inr 0) = 0 := rfl
lemma boostMatZ_32 (t : ℝ) : boostMatZ t (Sum.inr 2) (Sum.inr 1) = 0 := rfl
lemma boostMatZ_33 (t : ℝ) : boostMatZ t (Sum.inr 2) (Sum.inr 2) = (t ^ 2 + t⁻¹ ^ 2) / 2 := rfl

lemma boostMatX_00 (t : ℝ) : boostMatX t (Sum.inl 0) (Sum.inl 0) = (t ^ 2 + t⁻¹ ^ 2) / 2 := rfl
lemma boostMatX_01 (t : ℝ) : boostMatX t (Sum.inl 0) (Sum.inr 0) = -((t ^ 2 - t⁻¹ ^ 2) / 2) := rfl
lemma boostMatX_02 (t : ℝ) : boostMatX t (Sum.inl 0) (Sum.inr 1) = 0 := rfl
lemma boostMatX_03 (t : ℝ) : boostMatX t (Sum.inl 0) (Sum.inr 2) = 0 := rfl
lemma boostMatX_10 (t : ℝ) : boostMatX t (Sum.inr 0) (Sum.inl 0) = -((t ^ 2 - t⁻¹ ^ 2) / 2) := rfl
lemma boostMatX_11 (t : ℝ) : boostMatX t (Sum.inr 0) (Sum.inr 0) = (t ^ 2 + t⁻¹ ^ 2) / 2 := rfl
lemma boostMatX_12 (t : ℝ) : boostMatX t (Sum.inr 0) (Sum.inr 1) = 0 := rfl
lemma boostMatX_13 (t : ℝ) : boostMatX t (Sum.inr 0) (Sum.inr 2) = 0 := rfl
lemma boostMatX_20 (t : ℝ) : boostMatX t (Sum.inr 1) (Sum.inl 0) = 0 := rfl
lemma boostMatX_21 (t : ℝ) : boostMatX t (Sum.inr 1) (Sum.inr 0) = 0 := rfl
lemma boostMatX_22 (t : ℝ) : boostMatX t (Sum.inr 1) (Sum.inr 1) = 1 := rfl
lemma boostMatX_23 (t : ℝ) : boostMatX t (Sum.inr 1) (Sum.inr 2) = 0 := rfl
lemma boostMatX_30 (t : ℝ) : boostMatX t (Sum.inr 2) (Sum.inl 0) = 0 := rfl
lemma boostMatX_31 (t : ℝ) : boostMatX t (Sum.inr 2) (Sum.inr 0) = 0 := rfl
lemma boostMatX_32 (t : ℝ) : boostMatX t (Sum.inr 2) (Sum.inr 1) = 0 := rfl
lemma boostMatX_33 (t : ℝ) : boostMatX t (Sum.inr 2) (Sum.inr 2) = 1 := rfl

lemma boostMatY_00 (t : ℝ) : boostMatY t (Sum.inl 0) (Sum.inl 0) = (t ^ 2 + t⁻¹ ^ 2) / 2 := rfl
lemma boostMatY_01 (t : ℝ) : boostMatY t (Sum.inl 0) (Sum.inr 0) = 0 := rfl
lemma boostMatY_02 (t : ℝ) : boostMatY t (Sum.inl 0) (Sum.inr 1) = -((t ^ 2 - t⁻¹ ^ 2) / 2) := rfl
lemma boostMatY_03 (t : ℝ) : boostMatY t (Sum.inl 0) (Sum.inr 2) = 0 := rfl
lemma boostMatY_10 (t : ℝ) : boostMatY t (Sum.inr 0) (Sum.inl 0) = 0 := rfl
lemma boostMatY_11 (t : ℝ) : boostMatY t (Sum.inr 0) (Sum.inr 0) = 1 := rfl
lemma boostMatY_12 (t : ℝ) : boostMatY t (Sum.inr 0) (Sum.inr 1) = 0 := rfl
lemma boostMatY_13 (t : ℝ) : boostMatY t (Sum.inr 0) (Sum.inr 2) = 0 := rfl
lemma boostMatY_20 (t : ℝ) : boostMatY t (Sum.inr 1) (Sum.inl 0) = -((t ^ 2 - t⁻¹ ^ 2) / 2) := rfl
lemma boostMatY_21 (t : ℝ) : boostMatY t (Sum.inr 1) (Sum.inr 0) = 0 := rfl
lemma boostMatY_22 (t : ℝ) : boostMatY t (Sum.inr 1) (Sum.inr 1) = (t ^ 2 + t⁻¹ ^ 2) / 2 := rfl
lemma boostMatY_23 (t : ℝ) : boostMatY t (Sum.inr 1) (Sum.inr 2) = 0 := rfl
lemma boostMatY_30 (t : ℝ) : boostMatY t (Sum.inr 2) (Sum.inl 0) = 0 := rfl
lemma boostMatY_31 (t : ℝ) : boostMatY t (Sum.inr 2) (Sum.inr 0) = 0 := rfl
lemma boostMatY_32 (t : ℝ) : boostMatY t (Sum.inr 2) (Sum.inr 1) = 0 := rfl
lemma boostMatY_33 (t : ℝ) : boostMatY t (Sum.inr 2) (Sum.inr 2) = 1 := rfl

set_option maxHeartbeats 2000000 in
/-- The Lorentz action on a fermion pair `ψ̄_α (Dψ_μ)_β` with one derivative on
  the unbarred factor. -/
lemma repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (Λ : SL(2,ℂ))
    (μ : Fin 1 ⊕ Fin 3) (α β : Fin 2) :
    repLorentzGroup Λ (Dbarψ [] α * Dψ [μ] β) =
      ∑ γ, ∑ ν, ∑ δ, ((Λ⁻¹).1 α γ *
        ((((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) *
          star ((Λ⁻¹).1 β δ))) • (Dbarψ [] γ * Dψ [ν] δ) := by
  have hsm : ∀ (f : Fin 2 → JetAlgebra) (y : JetAlgebra),
      (∑ x, f x) * y = ∑ x, f x * y := fun f y => by
    rw [show (∑ x, f x) * y = LinearMap.mulRight ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hms : ∀ (f : (Fin 1 ⊕ Fin 3) → JetAlgebra) (y : JetAlgebra),
      y * (∑ x, f x) = ∑ x, y * f x := fun f y => by
    rw [show y * (∑ x, f x) = LinearMap.mulLeft ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hms₂ : ∀ (f : Fin 2 → JetAlgebra) (y : JetAlgebra),
      y * (∑ x, f x) = ∑ x, y * f x := fun f y => by
    rw [show y * (∑ x, f x) = LinearMap.mulLeft ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hsmul : ∀ (c d : ℂ) (x y : JetAlgebra),
      (c • x) * (d • y) = (c * d) • (x * y) := fun c d x y => by
    rw [smul_mul_smul_comm]
  rw [repLorentzGroup_apply_mul, repLorentzGroup_Dbarψ_nil, repLorentzGroup_Dψ_singleton]
  simp only [hsm, hms, hms₂, hsmul]

set_option maxHeartbeats 2000000 in
/-- The Lorentz action on a fermion pair `(D̄ψ̄_μ)_α ψ_β` with one derivative on
  the barred factor. -/
lemma repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (Λ : SL(2,ℂ))
    (μ : Fin 1 ⊕ Fin 3) (α β : Fin 2) :
    repLorentzGroup Λ (Dbarψ [μ] α * Dψ [] β) =
      ∑ ν, ∑ γ, ∑ δ, (((((Lorentz.SL2C.toLorentzGroup Λ).1 ν μ : ℝ) : ℂ) *
        (Λ⁻¹).1 α γ) * star ((Λ⁻¹).1 β δ)) • (Dbarψ [ν] γ * Dψ [] δ) := by
  have hsm : ∀ (f : (Fin 1 ⊕ Fin 3) → JetAlgebra) (y : JetAlgebra),
      (∑ x, f x) * y = ∑ x, f x * y := fun f y => by
    rw [show (∑ x, f x) * y = LinearMap.mulRight ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hsm₂ : ∀ (f : Fin 2 → JetAlgebra) (y : JetAlgebra),
      (∑ x, f x) * y = ∑ x, f x * y := fun f y => by
    rw [show (∑ x, f x) * y = LinearMap.mulRight ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hms : ∀ (f : Fin 2 → JetAlgebra) (y : JetAlgebra),
      y * (∑ x, f x) = ∑ x, y * f x := fun f y => by
    rw [show y * (∑ x, f x) = LinearMap.mulLeft ℂ y (∑ x, f x) from rfl, map_sum]
    rfl
  have hsmul : ∀ (c d : ℂ) (x y : JetAlgebra),
      (c • x) * (d • y) = (c * d) • (x * y) := fun c d x y => by
    rw [smul_mul_smul_comm]
  rw [repLorentzGroup_apply_mul, repLorentzGroup_Dbarψ_singleton, repLorentzGroup_Dψ_nil]
  simp only [hsm, hsm₂, hms, hsmul]

set_option maxHeartbeats 2000000 in
/-- The `Z`-boost action on the field strength `F01`. -/
lemma genZ_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) =
      (((t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) +
      (((t ^ 4 - 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_antisymm {} (Sum.inr 0) (Sum.inr 2),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 2000000 in
/-- The `Z`-boost action on the field strength `F02`. -/
lemma genZ_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) +
      (((t ^ 4 - 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_antisymm {} (Sum.inr 1) (Sum.inr 2),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 2000000 in
/-- The `Z`-boost action on the field strength `F03`. -/
lemma genZ_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) =
      fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 2),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 2000000 in
/-- The `Z`-boost action on the field strength `F12`. -/
lemma genZ_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) =
      fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 2000000 in
/-- The `Z`-boost action on the field strength `F13`. -/
lemma genZ_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) +
      (((t ^ 4 - 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 0),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 2000000 in
/-- The `Z`-boost action on the field strength `F23`. -/
lemma genZ_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) =
      (((t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) +
      (((t ^ 4 - 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 1),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 2000000 in
/-- The `X`-boost action on the field strength `F01`. -/
lemma genX_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) =
      fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostXel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 0),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 2000000 in
/-- The `X`-boost action on the field strength `F02`. -/
lemma genX_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) +
      (((-t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostXel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    fieldStrengthDeriv_self,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 2000000 in
/-- The `X`-boost action on the field strength `F03`. -/
lemma genX_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) +
      (((-t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostXel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    fieldStrengthDeriv_self,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 2000000 in
/-- The `X`-boost action on the field strength `F12`. -/
lemma genX_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) +
      (((-t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostXel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    fieldStrengthDeriv_self,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 2000000 in
/-- The `X`-boost action on the field strength `F13`. -/
lemma genX_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) +
      (((-t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostXel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    fieldStrengthDeriv_self,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 2000000 in
/-- The `X`-boost action on the field strength `F23`. -/
lemma genX_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) =
      fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostXel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    fieldStrengthDeriv_self,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 2000000 in
/-- The `Y`-boost action on the field strength `F01`. -/
lemma genY_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) =
      (((t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) +
      (((t ^ 4 - 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_antisymm {} (Sum.inr 0) (Sum.inr 1),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 2000000 in
/-- The `Y`-boost action on the field strength `F02`. -/
lemma genY_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) =
      fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 1),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 2000000 in
/-- The `Y`-boost action on the field strength `F03`. -/
lemma genY_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) +
      (((-t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    fieldStrengthDeriv_self,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 2000000 in
/-- The `Y`-boost action on the field strength `F12`. -/
lemma genY_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) +
      (((t ^ 4 - 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 0),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 2000000 in
/-- The `Y`-boost action on the field strength `F13`. -/
lemma genY_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) =
      fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    fieldStrengthDeriv_self,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 2000000 in
/-- The `Y`-boost action on the field strength `F23`. -/
lemma genY_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) =
      (((t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) +
      (((-t ^ 4 + 1) / (2 * t ^ 2) : ℝ) : ℂ) •
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    fieldStrengthDeriv_self,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Z`-boost action on the derivative field strength
  `∂∂F01` with derivative indices `(0, 1)`. -/
lemma genZ_dd01_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0) +
      (((t ^ 8 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 0) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 0) +
      (((-t ^ 8 + 2 * t ^ 4 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inr 0),
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 0} (Sum.inr 0) (Sum.inr 2),
    fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Z`-boost action on the derivative field strength
  `∂∂F23` with derivative indices `(0, 1)`. -/
lemma genZ_dd01_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2) +
      (((t ^ 8 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 1) +
      (((-t ^ 8 + 2 * t ^ 4 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inr 0),
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 1),
    fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Z`-boost action on the derivative field strength
  `∂∂F02` with derivative indices `(0, 2)`. -/
lemma genZ_dd02_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1) +
      (((t ^ 8 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 1) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 1) +
      (((-t ^ 8 + 2 * t ^ 4 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inr 1),
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 1} (Sum.inr 1) (Sum.inr 2),
    fieldStrengthDeriv_antisymm {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Z`-boost action on the derivative field strength
  `∂∂F13` with derivative indices `(0, 2)`. -/
lemma genZ_dd02_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2) +
      (((t ^ 8 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 0) +
      (((-t ^ 8 + 2 * t ^ 4 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inr 1),
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 0),
    fieldStrengthDeriv_antisymm {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Z`-boost action on the derivative field strength
  `∂∂F03` with derivative indices `(0, 3)`. -/
lemma genZ_dd03_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) =
      (((t ^ 8 + 1) / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inl 0} (Sum.inl 0) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 2, Sum.inr 2} (Sum.inl 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inl 0),
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inl 0} (Sum.inl 0) (Sum.inr 2),
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2),
    fieldStrengthDeriv_antisymm {Sum.inr 2, Sum.inr 2} (Sum.inl 0) (Sum.inr 2),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Z`-boost action on the derivative field strength
  `∂∂F12` with derivative indices `(0, 3)`. -/
lemma genZ_dd03_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) =
      (((t ^ 8 + 1) / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inl 0} (Sum.inr 0) (Sum.inr 1) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 2, Sum.inr 2} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inl 0),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Z`-boost action on the derivative field strength
  `∂∂F03` with derivative indices `(1, 2)`. -/
lemma genZ_dd12_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) =
      fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Z`-boost action on the derivative field strength
  `∂∂F12` with derivative indices `(1, 2)`. -/
lemma genZ_dd12_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) =
      fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Z`-boost action on the derivative field strength
  `∂∂F02` with derivative indices `(1, 3)`. -/
lemma genZ_dd13_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 1) +
      (((-t ^ 8 + 2 * t ^ 4 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2) +
      (((t ^ 8 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 0) (Sum.inl 0),
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2),
    fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 2} (Sum.inr 1) (Sum.inr 2),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Z`-boost action on the derivative field strength
  `∂∂F13` with derivative indices `(1, 3)`. -/
lemma genZ_dd13_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2) +
      (((-t ^ 8 + 2 * t ^ 4 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 0) (Sum.inr 2) +
      (((t ^ 8 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 0) (Sum.inl 0),
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0),
    fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 0),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Z`-boost action on the derivative field strength
  `∂∂F01` with derivative indices `(2, 3)`. -/
lemma genZ_dd23_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 0) +
      (((-t ^ 8 + 2 * t ^ 4 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2) +
      (((t ^ 8 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inl 0),
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2),
    fieldStrengthDeriv_antisymm {Sum.inr 1, Sum.inr 2} (Sum.inr 0) (Sum.inr 2),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Z`-boost action on the derivative field strength
  `∂∂F23` with derivative indices `(2, 3)`. -/
lemma genZ_dd23_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2) +
      (((-t ^ 8 + 2 * t ^ 4 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 1) (Sum.inr 2) +
      (((t ^ 8 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inl 0),
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1),
    fieldStrengthDeriv_antisymm {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 1),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `X`-boost action on the derivative field strength
  `∂∂F01` with derivative indices `(0, 1)`. -/
lemma genX_dd01_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) =
      (((t ^ 8 + 1) / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inl 0} (Sum.inl 0) (Sum.inr 0) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostXel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 0) (Sum.inl 0),
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inl 0} (Sum.inl 0) (Sum.inr 0),
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0),
    fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `X`-boost action on the derivative field strength
  `∂∂F23` with derivative indices `(0, 1)`. -/
lemma genX_dd01_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) =
      (((t ^ 8 + 1) / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inl 0} (Sum.inr 1) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostXel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 0) (Sum.inl 0),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `X`-boost action on the derivative field strength
  `∂∂F02` with derivative indices `(0, 2)`. -/
lemma genX_dd02_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1) +
      (((t ^ 8 - 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostXel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    fieldStrengthDeriv_self,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `X`-boost action on the derivative field strength
  `∂∂F13` with derivative indices `(0, 2)`. -/
lemma genX_dd02_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2) +
      (((t ^ 8 - 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostXel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    fieldStrengthDeriv_self,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `X`-boost action on the derivative field strength
  `∂∂F03` with derivative indices `(0, 3)`. -/
lemma genX_dd03_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2) +
      (((t ^ 8 - 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostXel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    fieldStrengthDeriv_self,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `X`-boost action on the derivative field strength
  `∂∂F12` with derivative indices `(0, 3)`. -/
lemma genX_dd03_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1) +
      (((t ^ 8 - 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostXel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    fieldStrengthDeriv_self,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `X`-boost action on the derivative field strength
  `∂∂F03` with derivative indices `(1, 2)`. -/
lemma genX_dd12_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2) +
      (((t ^ 8 - 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostXel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    fieldStrengthDeriv_self,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `X`-boost action on the derivative field strength
  `∂∂F12` with derivative indices `(1, 2)`. -/
lemma genX_dd12_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1) +
      (((t ^ 8 - 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostXel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    fieldStrengthDeriv_self,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `X`-boost action on the derivative field strength
  `∂∂F02` with derivative indices `(1, 3)`. -/
lemma genX_dd13_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1) +
      (((t ^ 8 - 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostXel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    fieldStrengthDeriv_self,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `X`-boost action on the derivative field strength
  `∂∂F13` with derivative indices `(1, 3)`. -/
lemma genX_dd13_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2) +
      (((t ^ 8 - 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostXel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    fieldStrengthDeriv_self,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `X`-boost action on the derivative field strength
  `∂∂F01` with derivative indices `(2, 3)`. -/
lemma genX_dd23_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) =
      fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostXel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_antisymm {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `X`-boost action on the derivative field strength
  `∂∂F23` with derivative indices `(2, 3)`. -/
lemma genX_dd23_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) =
      fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostXel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    fieldStrengthDeriv_self,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Y`-boost action on the derivative field strength
  `∂∂F01` with derivative indices `(0, 1)`. -/
lemma genY_dd01_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0) +
      (((t ^ 8 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 0) (Sum.inr 1) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 0) +
      (((-t ^ 8 + 2 * t ^ 4 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inr 0),
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 0} (Sum.inr 0) (Sum.inr 1),
    fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Y`-boost action on the derivative field strength
  `∂∂F23` with derivative indices `(0, 1)`. -/
lemma genY_dd01_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 2) +
      (((t ^ 8 - 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inr 0),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Y`-boost action on the derivative field strength
  `∂∂F02` with derivative indices `(0, 2)`. -/
lemma genY_dd02_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) =
      (((t ^ 8 + 1) / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inl 0} (Sum.inl 0) (Sum.inr 1) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 1} (Sum.inl 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inl 0),
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inl 0} (Sum.inl 0) (Sum.inr 1),
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1),
    fieldStrengthDeriv_antisymm {Sum.inr 1, Sum.inr 1} (Sum.inl 0) (Sum.inr 1),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Y`-boost action on the derivative field strength
  `∂∂F13` with derivative indices `(0, 2)`. -/
lemma genY_dd02_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) =
      (((t ^ 8 + 1) / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inl 0} (Sum.inr 0) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 1} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inl 0),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Y`-boost action on the derivative field strength
  `∂∂F03` with derivative indices `(0, 3)`. -/
lemma genY_dd03_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 1) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 2) +
      (((t ^ 8 - 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    fieldStrengthDeriv_self,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Y`-boost action on the derivative field strength
  `∂∂F12` with derivative indices `(0, 3)`. -/
lemma genY_dd03_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1) +
      (((t ^ 8 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 0) +
      (((-t ^ 8 + 2 * t ^ 4 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 0),
    fieldStrengthDeriv_antisymm {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Y`-boost action on the derivative field strength
  `∂∂F03` with derivative indices `(1, 2)`. -/
lemma genY_dd12_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 2) +
      (((t ^ 8 - 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 0) (Sum.inl 0),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Y`-boost action on the derivative field strength
  `∂∂F12` with derivative indices `(1, 2)`. -/
lemma genY_dd12_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1) +
      (((-t ^ 8 + 2 * t ^ 4 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 0) (Sum.inr 1) +
      (((t ^ 8 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_pair_swap (Sum.inr 0) (Sum.inl 0),
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0),
    fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 0),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Y`-boost action on the derivative field strength
  `∂∂F02` with derivative indices `(1, 3)`. -/
lemma genY_dd13_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) =
      fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Y`-boost action on the derivative field strength
  `∂∂F13` with derivative indices `(1, 3)`. -/
lemma genY_dd13_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) =
      fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    fieldStrengthDeriv_self,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Y`-boost action on the derivative field strength
  `∂∂F01` with derivative indices `(2, 3)`. -/
lemma genY_dd23_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 0) +
      (((-t ^ 8 + 2 * t ^ 4 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1) +
      (((t ^ 8 - 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    fieldStrengthDeriv_self,
    fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1),
    fieldStrengthDeriv_antisymm {Sum.inr 1, Sum.inr 2} (Sum.inr 0) (Sum.inr 1),
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The `Y`-boost action on the derivative field strength
  `∂∂F23` with derivative indices `(2, 3)`. -/
lemma genY_dd23_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) =
      (((t ^ 8 + 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2) +
      (((t ^ 8 - 2 * t ^ 4 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 1) (Sum.inr 2) +
      (((-t ^ 8 + 1) / (4 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    fieldStrengthDeriv_self,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  try (match_scalars <;> (push_cast; try field_simp; try ring))

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Z`-boost on
  `F01 * F01`. -/
lemma pairZ_F01_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genZ_F01 t ht,
    genZ_F01 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul_jet, mul_add_jet, smul_mul_smul_jet, smul_mul_jet, mul_smul_jet,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 2) (Sum.inl 0) (Sum.inr 0)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Z`-boost on
  `F01 * F23`. -/
lemma pairZ_F01_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genZ_F01 t ht,
    genZ_F01 t⁻¹ (inv_ne_zero ht),
    genZ_F23 t ht,
    genZ_F23 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul_jet, mul_add_jet, smul_mul_smul_jet, smul_mul_jet, mul_smul_jet,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 2) (Sum.inl 0) (Sum.inr 1)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Z`-boost on
  `F02 * F02`. -/
lemma pairZ_F02_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genZ_F02 t ht,
    genZ_F02 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul_jet, mul_add_jet, smul_mul_smul_jet, smul_mul_jet, mul_smul_jet,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 1) (Sum.inr 2) (Sum.inl 0) (Sum.inr 1)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Z`-boost on
  `F02 * F13`. -/
lemma pairZ_F02_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genZ_F02 t ht,
    genZ_F02 t⁻¹ (inv_ne_zero ht),
    genZ_F13 t ht,
    genZ_F13 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul_jet, mul_add_jet, smul_mul_smul_jet, smul_mul_jet, mul_smul_jet,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inl 0) (Sum.inr 1) (Sum.inl 0) (Sum.inr 0),
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 1) (Sum.inr 2) (Sum.inl 0) (Sum.inr 0),
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 1) (Sum.inr 2) (Sum.inr 0) (Sum.inr 2)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Z`-boost on
  `F03 * F03`. -/
lemma pairZ_F03_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) =
      ((2 : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genZ_F03 t ht,
    genZ_F03 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Z`-boost on
  `F03 * F12`. -/
lemma pairZ_F03_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) =
      ((2 : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genZ_F03 t ht,
    genZ_F03 t⁻¹ (inv_ne_zero ht),
    genZ_F12 t ht,
    genZ_F12 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Z`-boost on
  `F12 * F12`. -/
lemma pairZ_F12_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) =
      ((2 : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genZ_F12 t ht,
    genZ_F12 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Z`-boost on
  `F13 * F13`. -/
lemma pairZ_F13_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genZ_F13 t ht,
    genZ_F13 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul_jet, mul_add_jet, smul_mul_smul_jet, smul_mul_jet, mul_smul_jet,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 2) (Sum.inl 0) (Sum.inr 0)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Z`-boost on
  `F23 * F23`. -/
lemma pairZ_F23_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genZ_F23 t ht,
    genZ_F23 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul_jet, mul_add_jet, smul_mul_smul_jet, smul_mul_jet, mul_smul_jet,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 1) (Sum.inr 2) (Sum.inl 0) (Sum.inr 1)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `X`-boost on
  `F01 * F01`. -/
lemma pairX_F01_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) =
      ((2 : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genX_F01 t ht,
    genX_F01 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `X`-boost on
  `F01 * F23`. -/
lemma pairX_F01_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) =
      ((2 : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genX_F01 t ht,
    genX_F01 t⁻¹ (inv_ne_zero ht),
    genX_F23 t ht,
    genX_F23 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `X`-boost on
  `F02 * F02`. -/
lemma pairX_F02_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genX_F02 t ht,
    genX_F02 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul_jet, mul_add_jet, smul_mul_smul_jet, smul_mul_jet, mul_smul_jet,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 1) (Sum.inl 0) (Sum.inr 1)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `X`-boost on
  `F02 * F13`. -/
lemma pairX_F02_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genX_F02 t ht,
    genX_F02 t⁻¹ (inv_ne_zero ht),
    genX_F13 t ht,
    genX_F13 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul_jet, mul_add_jet, smul_mul_smul_jet, smul_mul_jet, mul_smul_jet,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 1) (Sum.inl 0) (Sum.inr 2)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `X`-boost on
  `F03 * F03`. -/
lemma pairX_F03_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genX_F03 t ht,
    genX_F03 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul_jet, mul_add_jet, smul_mul_smul_jet, smul_mul_jet, mul_smul_jet,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 2) (Sum.inl 0) (Sum.inr 2)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `X`-boost on
  `F03 * F12`. -/
lemma pairX_F03_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genX_F03 t ht,
    genX_F03 t⁻¹ (inv_ne_zero ht),
    genX_F12 t ht,
    genX_F12 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul_jet, mul_add_jet, smul_mul_smul_jet, smul_mul_jet, mul_smul_jet,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inl 0) (Sum.inr 2) (Sum.inl 0) (Sum.inr 1),
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 2) (Sum.inl 0) (Sum.inr 1),
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 2) (Sum.inr 0) (Sum.inr 1)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `X`-boost on
  `F12 * F12`. -/
lemma pairX_F12_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genX_F12 t ht,
    genX_F12 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul_jet, mul_add_jet, smul_mul_smul_jet, smul_mul_jet, mul_smul_jet,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 1) (Sum.inl 0) (Sum.inr 1)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `X`-boost on
  `F13 * F13`. -/
lemma pairX_F13_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genX_F13 t ht,
    genX_F13 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul_jet, mul_add_jet, smul_mul_smul_jet, smul_mul_jet, mul_smul_jet,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 2) (Sum.inl 0) (Sum.inr 2)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `X`-boost on
  `F23 * F23`. -/
lemma pairX_F23_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) =
      ((2 : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genX_F23 t ht,
    genX_F23 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Y`-boost on
  `F01 * F01`. -/
lemma pairY_F01_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genY_F01 t ht,
    genY_F01 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul_jet, mul_add_jet, smul_mul_smul_jet, smul_mul_jet, mul_smul_jet,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 1) (Sum.inl 0) (Sum.inr 0)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Y`-boost on
  `F01 * F23`. -/
lemma pairY_F01_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) +
      ((-((t ^ 4 - 1) ^ 2 / (2 * t ^ 4)) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genY_F01 t ht,
    genY_F01 t⁻¹ (inv_ne_zero ht),
    genY_F23 t ht,
    genY_F23 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul_jet, mul_add_jet, smul_mul_smul_jet, smul_mul_jet, mul_smul_jet,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 1) (Sum.inl 0) (Sum.inr 2)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Y`-boost on
  `F02 * F02`. -/
lemma pairY_F02_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) =
      ((2 : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genY_F02 t ht,
    genY_F02 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Y`-boost on
  `F02 * F13`. -/
lemma pairY_F02_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) =
      ((2 : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genY_F02 t ht,
    genY_F02 t⁻¹ (inv_ne_zero ht),
    genY_F13 t ht,
    genY_F13 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Y`-boost on
  `F03 * F03`. -/
lemma pairY_F03_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genY_F03 t ht,
    genY_F03 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul_jet, mul_add_jet, smul_mul_smul_jet, smul_mul_jet, mul_smul_jet,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 1) (Sum.inr 2) (Sum.inl 0) (Sum.inr 2)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Y`-boost on
  `F03 * F12`. -/
lemma pairY_F03_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) +
      ((-((t ^ 4 - 1) ^ 2 / (2 * t ^ 4)) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genY_F03 t ht,
    genY_F03 t⁻¹ (inv_ne_zero ht),
    genY_F12 t ht,
    genY_F12 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul_jet, mul_add_jet, smul_mul_smul_jet, smul_mul_jet, mul_smul_jet,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inl 0) (Sum.inr 2) (Sum.inl 0) (Sum.inr 0),
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 1) (Sum.inr 2) (Sum.inl 0) (Sum.inr 0),
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 1) (Sum.inr 2) (Sum.inr 0) (Sum.inr 1)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Y`-boost on
  `F12 * F12`. -/
lemma pairY_F12_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genY_F12 t ht,
    genY_F12 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul_jet, mul_add_jet, smul_mul_smul_jet, smul_mul_jet, mul_smul_jet,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 1) (Sum.inl 0) (Sum.inr 0)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Y`-boost on
  `F13 * F13`. -/
lemma pairY_F13_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) =
      ((2 : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genY_F13 t ht,
    genY_F13 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action (`t` and `t⁻¹` together) of the `Y`-boost on
  `F23 * F23`. -/
lemma pairY_F23_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv, repLorentzGroup_apply_mul, repLorentzGroup_apply_mul]
  simp only [genY_F23 t ht,
    genY_F23 t⁻¹ (inv_ne_zero ht)]
  simp only [add_mul_jet, mul_add_jet, smul_mul_smul_jet, smul_mul_jet, mul_smul_jet,
    fieldStrengthDeriv_mul_comm {} {} (Sum.inr 1) (Sum.inr 2) (Sum.inl 0) (Sum.inr 2)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F01` with
  derivative indices `(0, 1)`. -/
lemma pairZ_dd01_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0) +
      ((-((t ^ 4 - 1) ^ 2 / (2 * t ^ 4)) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [genZ_dd01_F01 t ht, genZ_dd01_F01 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F23` with
  derivative indices `(0, 1)`. -/
lemma pairZ_dd01_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2) +
      ((-((t ^ 4 - 1) ^ 2 / (2 * t ^ 4)) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [genZ_dd01_F23 t ht, genZ_dd01_F23 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F02` with
  derivative indices `(0, 2)`. -/
lemma pairZ_dd02_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1) +
      ((-((t ^ 4 - 1) ^ 2 / (2 * t ^ 4)) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [genZ_dd02_F02 t ht, genZ_dd02_F02 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F13` with
  derivative indices `(0, 2)`. -/
lemma pairZ_dd02_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2) +
      ((-((t ^ 4 - 1) ^ 2 / (2 * t ^ 4)) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [genZ_dd02_F13 t ht, genZ_dd02_F13 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F03` with
  derivative indices `(0, 3)`. -/
lemma pairZ_dd03_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) =
      (((t ^ 8 + 1) / t ^ 4 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [genZ_dd03_F03 t ht, genZ_dd03_F03 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F12` with
  derivative indices `(0, 3)`. -/
lemma pairZ_dd03_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) =
      (((t ^ 8 + 1) / t ^ 4 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [genZ_dd03_F12 t ht, genZ_dd03_F12 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F03` with
  derivative indices `(1, 2)`. -/
lemma pairZ_dd12_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) =
      ((2 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [genZ_dd12_F03 t ht, genZ_dd12_F03 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F12` with
  derivative indices `(1, 2)`. -/
lemma pairZ_dd12_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) =
      ((2 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [genZ_dd12_F12 t ht, genZ_dd12_F12 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F02` with
  derivative indices `(1, 3)`. -/
lemma pairZ_dd13_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1) +
      ((-((t ^ 4 - 1) ^ 2 / (2 * t ^ 4)) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [genZ_dd13_F02 t ht, genZ_dd13_F02 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F13` with
  derivative indices `(1, 3)`. -/
lemma pairZ_dd13_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2) +
      ((-((t ^ 4 - 1) ^ 2 / (2 * t ^ 4)) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [genZ_dd13_F13 t ht, genZ_dd13_F13 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F01` with
  derivative indices `(2, 3)`. -/
lemma pairZ_dd23_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0) +
      ((-((t ^ 4 - 1) ^ 2 / (2 * t ^ 4)) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [genZ_dd23_F01 t ht, genZ_dd23_F01 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Z`-boost on `∂∂F23` with
  derivative indices `(2, 3)`. -/
lemma pairZ_dd23_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2) +
      ((-((t ^ 4 - 1) ^ 2 / (2 * t ^ 4)) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [genZ_dd23_F23 t ht, genZ_dd23_F23 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F01` with
  derivative indices `(0, 1)`. -/
lemma pairX_dd01_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) =
      (((t ^ 8 + 1) / t ^ 4 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [genX_dd01_F01 t ht, genX_dd01_F01 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F23` with
  derivative indices `(0, 1)`. -/
lemma pairX_dd01_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) =
      (((t ^ 8 + 1) / t ^ 4 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [genX_dd01_F23 t ht, genX_dd01_F23 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F02` with
  derivative indices `(0, 2)`. -/
lemma pairX_dd02_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [genX_dd02_F02 t ht, genX_dd02_F02 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F13` with
  derivative indices `(0, 2)`. -/
lemma pairX_dd02_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [genX_dd02_F13 t ht, genX_dd02_F13 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F03` with
  derivative indices `(0, 3)`. -/
lemma pairX_dd03_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [genX_dd03_F03 t ht, genX_dd03_F03 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F12` with
  derivative indices `(0, 3)`. -/
lemma pairX_dd03_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [genX_dd03_F12 t ht, genX_dd03_F12 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F03` with
  derivative indices `(1, 2)`. -/
lemma pairX_dd12_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [genX_dd12_F03 t ht, genX_dd12_F03 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F12` with
  derivative indices `(1, 2)`. -/
lemma pairX_dd12_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [genX_dd12_F12 t ht, genX_dd12_F12 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F02` with
  derivative indices `(1, 3)`. -/
lemma pairX_dd13_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [genX_dd13_F02 t ht, genX_dd13_F02 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F13` with
  derivative indices `(1, 3)`. -/
lemma pairX_dd13_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [genX_dd13_F13 t ht, genX_dd13_F13 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F01` with
  derivative indices `(2, 3)`. -/
lemma pairX_dd23_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) =
      ((2 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [genX_dd23_F01 t ht, genX_dd23_F01 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `X`-boost on `∂∂F23` with
  derivative indices `(2, 3)`. -/
lemma pairX_dd23_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) =
      ((2 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [genX_dd23_F23 t ht, genX_dd23_F23 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F01` with
  derivative indices `(0, 1)`. -/
lemma pairY_dd01_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0) +
      ((-((t ^ 4 - 1) ^ 2 / (2 * t ^ 4)) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [genY_dd01_F01 t ht, genY_dd01_F01 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F23` with
  derivative indices `(0, 1)`. -/
lemma pairY_dd01_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [genY_dd01_F23 t ht, genY_dd01_F23 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F02` with
  derivative indices `(0, 2)`. -/
lemma pairY_dd02_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) =
      (((t ^ 8 + 1) / t ^ 4 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [genY_dd02_F02 t ht, genY_dd02_F02 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F13` with
  derivative indices `(0, 2)`. -/
lemma pairY_dd02_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) =
      (((t ^ 8 + 1) / t ^ 4 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [genY_dd02_F13 t ht, genY_dd02_F13 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F03` with
  derivative indices `(0, 3)`. -/
lemma pairY_dd03_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [genY_dd03_F03 t ht, genY_dd03_F03 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F12` with
  derivative indices `(0, 3)`. -/
lemma pairY_dd03_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1) +
      ((-((t ^ 4 - 1) ^ 2 / (2 * t ^ 4)) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [genY_dd03_F12 t ht, genY_dd03_F12 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F03` with
  derivative indices `(1, 2)`. -/
lemma pairY_dd12_F03 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [genY_dd12_F03 t ht, genY_dd12_F03 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F12` with
  derivative indices `(1, 2)`. -/
lemma pairY_dd12_F12 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1) +
      ((-((t ^ 4 - 1) ^ 2 / (2 * t ^ 4)) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [genY_dd12_F12 t ht, genY_dd12_F12 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F02` with
  derivative indices `(1, 3)`. -/
lemma pairY_dd13_F02 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) =
      ((2 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [genY_dd13_F02 t ht, genY_dd13_F02 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F13` with
  derivative indices `(1, 3)`. -/
lemma pairY_dd13_F13 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) =
      ((2 : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [genY_dd13_F13 t ht, genY_dd13_F13 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F01` with
  derivative indices `(2, 3)`. -/
lemma pairY_dd23_F01 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0) +
      ((-((t ^ 4 - 1) ^ 2 / (2 * t ^ 4)) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [genY_dd23_F01 t ht, genY_dd23_F01 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 2000000 in
/-- The paired boost action of the `Y`-boost on `∂∂F23` with
  derivative indices `(2, 3)`. -/
lemma pairY_dd23_F23 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [genY_dd23_F23 t ht, genY_dd23_F23 t⁻¹ (inv_ne_zero ht)]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `Z`-boost on the σ-contracted fermion
  pair `u0`. -/
lemma pairZ_u0 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostZel t ht) (Sum.inl 0) 0 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostZel t ht) (Sum.inl 0) 1 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostZel t⁻¹ (inv_ne_zero ht)) (Sum.inl 0) 0 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostZel t⁻¹ (inv_ne_zero ht)) (Sum.inl 0) 1 1,
    toLorentzGroup_boostZel, boostZel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `Z`-boost on the σ-contracted fermion
  pair `u1`. -/
lemma pairZ_u1 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0) =
      ((2 : ℝ) : ℂ) •
        (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostZel t ht) (Sum.inr 0) 0 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostZel t ht) (Sum.inr 0) 1 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostZel t⁻¹ (inv_ne_zero ht)) (Sum.inr 0) 0 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostZel t⁻¹ (inv_ne_zero ht)) (Sum.inr 0) 1 0,
    toLorentzGroup_boostZel, boostZel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `Z`-boost on the σ-contracted fermion
  pair `u2`. -/
lemma pairZ_u2 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0) =
      ((2 : ℝ) : ℂ) •
        (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostZel t ht) (Sum.inr 1) 0 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostZel t ht) (Sum.inr 1) 1 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostZel t⁻¹ (inv_ne_zero ht)) (Sum.inr 1) 0 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostZel t⁻¹ (inv_ne_zero ht)) (Sum.inr 1) 1 0,
    toLorentzGroup_boostZel, boostZel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `Z`-boost on the σ-contracted fermion
  pair `u3`. -/
lemma pairZ_u3 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostZel t ht) (Sum.inr 2) 0 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostZel t ht) (Sum.inr 2) 1 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostZel t⁻¹ (inv_ne_zero ht)) (Sum.inr 2) 0 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostZel t⁻¹ (inv_ne_zero ht)) (Sum.inr 2) 1 1,
    toLorentzGroup_boostZel, boostZel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `X`-boost on the σ-contracted fermion
  pair `u0`. -/
lemma pairX_u0 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostXel t ht) (Sum.inl 0) 0 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostXel t ht) (Sum.inl 0) 1 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostXel t⁻¹ (inv_ne_zero ht)) (Sum.inl 0) 0 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostXel t⁻¹ (inv_ne_zero ht)) (Sum.inl 0) 1 1,
    toLorentzGroup_boostXel, boostXel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `X`-boost on the σ-contracted fermion
  pair `u1`. -/
lemma pairX_u1 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostXel t ht) (Sum.inr 0) 0 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostXel t ht) (Sum.inr 0) 1 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostXel t⁻¹ (inv_ne_zero ht)) (Sum.inr 0) 0 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostXel t⁻¹ (inv_ne_zero ht)) (Sum.inr 0) 1 0,
    toLorentzGroup_boostXel, boostXel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `X`-boost on the σ-contracted fermion
  pair `u2`. -/
lemma pairX_u2 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0) =
      ((2 : ℝ) : ℂ) •
        (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostXel t ht) (Sum.inr 1) 0 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostXel t ht) (Sum.inr 1) 1 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostXel t⁻¹ (inv_ne_zero ht)) (Sum.inr 1) 0 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostXel t⁻¹ (inv_ne_zero ht)) (Sum.inr 1) 1 0,
    toLorentzGroup_boostXel, boostXel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `X`-boost on the σ-contracted fermion
  pair `u3`. -/
lemma pairX_u3 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) =
      ((2 : ℝ) : ℂ) •
        (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostXel t ht) (Sum.inr 2) 0 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostXel t ht) (Sum.inr 2) 1 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostXel t⁻¹ (inv_ne_zero ht)) (Sum.inr 2) 0 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostXel t⁻¹ (inv_ne_zero ht)) (Sum.inr 2) 1 1,
    toLorentzGroup_boostXel, boostXel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `Y`-boost on the σ-contracted fermion
  pair `u0`. -/
lemma pairY_u0 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) +
      (Complex.I * (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ)) •
        (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostYel t ht) (Sum.inl 0) 0 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostYel t ht) (Sum.inl 0) 1 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostYel t⁻¹ (inv_ne_zero ht)) (Sum.inl 0) 0 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostYel t⁻¹ (inv_ne_zero ht)) (Sum.inl 0) 1 1,
    toLorentzGroup_boostYel, boostYel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring_nf; try simp only [Complex.I_sq]; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `Y`-boost on the σ-contracted fermion
  pair `u1`. -/
lemma pairY_u1 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0) =
      ((2 : ℝ) : ℂ) •
        (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostYel t ht) (Sum.inr 0) 0 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostYel t ht) (Sum.inr 0) 1 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostYel t⁻¹ (inv_ne_zero ht)) (Sum.inr 0) 0 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostYel t⁻¹ (inv_ne_zero ht)) (Sum.inr 0) 1 0,
    toLorentzGroup_boostYel, boostYel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring_nf; try simp only [Complex.I_sq]; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `Y`-boost on the σ-contracted fermion
  pair `u2`. -/
lemma pairY_u2 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0) +
      (-(Complex.I * (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ))) •
        (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostYel t ht) (Sum.inr 1) 0 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostYel t ht) (Sum.inr 1) 1 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostYel t⁻¹ (inv_ne_zero ht)) (Sum.inr 1) 0 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostYel t⁻¹ (inv_ne_zero ht)) (Sum.inr 1) 1 0,
    toLorentzGroup_boostYel, boostYel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring_nf; try simp only [Complex.I_sq]; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `Y`-boost on the σ-contracted fermion
  pair `u3`. -/
lemma pairY_u3 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) =
      ((2 : ℝ) : ℂ) •
        (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostYel t ht) (Sum.inr 2) 0 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostYel t ht) (Sum.inr 2) 1 1,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostYel t⁻¹ (inv_ne_zero ht)) (Sum.inr 2) 0 0,
    repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton (boostYel t⁻¹ (inv_ne_zero ht)) (Sum.inr 2) 1 1,
    toLorentzGroup_boostYel, boostYel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring_nf; try simp only [Complex.I_sq]; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `Z`-boost on the σ-contracted fermion
  pair `ubar0`. -/
lemma pairZ_ubar0 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostZel t ht) (Sum.inl 0) 0 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostZel t ht) (Sum.inl 0) 1 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostZel t⁻¹ (inv_ne_zero ht)) (Sum.inl 0) 0 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostZel t⁻¹ (inv_ne_zero ht)) (Sum.inl 0) 1 1,
    toLorentzGroup_boostZel, boostZel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `Z`-boost on the σ-contracted fermion
  pair `ubar1`. -/
lemma pairZ_ubar1 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0) =
      ((2 : ℝ) : ℂ) •
        (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostZel t ht) (Sum.inr 0) 0 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostZel t ht) (Sum.inr 0) 1 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostZel t⁻¹ (inv_ne_zero ht)) (Sum.inr 0) 0 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostZel t⁻¹ (inv_ne_zero ht)) (Sum.inr 0) 1 0,
    toLorentzGroup_boostZel, boostZel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `Z`-boost on the σ-contracted fermion
  pair `ubar2`. -/
lemma pairZ_ubar2 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0) =
      ((2 : ℝ) : ℂ) •
        (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostZel t ht) (Sum.inr 1) 0 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostZel t ht) (Sum.inr 1) 1 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostZel t⁻¹ (inv_ne_zero ht)) (Sum.inr 1) 0 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostZel t⁻¹ (inv_ne_zero ht)) (Sum.inr 1) 1 0,
    toLorentzGroup_boostZel, boostZel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `Z`-boost on the σ-contracted fermion
  pair `ubar3`. -/
lemma pairZ_ubar3 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostZel t ht)
        (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) +
      repLorentzGroup ((boostZel t ht)⁻¹)
        (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostZel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostZel t ht) (Sum.inr 2) 0 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostZel t ht) (Sum.inr 2) 1 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostZel t⁻¹ (inv_ne_zero ht)) (Sum.inr 2) 0 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostZel t⁻¹ (inv_ne_zero ht)) (Sum.inr 2) 1 1,
    toLorentzGroup_boostZel, boostZel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatZ_00, boostMatZ_01, boostMatZ_02, boostMatZ_03,
    boostMatZ_10, boostMatZ_11, boostMatZ_12, boostMatZ_13,
    boostMatZ_20, boostMatZ_21, boostMatZ_22, boostMatZ_23,
    boostMatZ_30, boostMatZ_31, boostMatZ_32, boostMatZ_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `X`-boost on the σ-contracted fermion
  pair `ubar0`. -/
lemma pairX_ubar0 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostXel t ht) (Sum.inl 0) 0 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostXel t ht) (Sum.inl 0) 1 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostXel t⁻¹ (inv_ne_zero ht)) (Sum.inl 0) 0 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostXel t⁻¹ (inv_ne_zero ht)) (Sum.inl 0) 1 1,
    toLorentzGroup_boostXel, boostXel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `X`-boost on the σ-contracted fermion
  pair `ubar1`. -/
lemma pairX_ubar1 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0) +
      (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostXel t ht) (Sum.inr 0) 0 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostXel t ht) (Sum.inr 0) 1 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostXel t⁻¹ (inv_ne_zero ht)) (Sum.inr 0) 0 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostXel t⁻¹ (inv_ne_zero ht)) (Sum.inr 0) 1 0,
    toLorentzGroup_boostXel, boostXel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `X`-boost on the σ-contracted fermion
  pair `ubar2`. -/
lemma pairX_ubar2 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0) =
      ((2 : ℝ) : ℂ) •
        (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostXel t ht) (Sum.inr 1) 0 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostXel t ht) (Sum.inr 1) 1 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostXel t⁻¹ (inv_ne_zero ht)) (Sum.inr 1) 0 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostXel t⁻¹ (inv_ne_zero ht)) (Sum.inr 1) 1 0,
    toLorentzGroup_boostXel, boostXel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `X`-boost on the σ-contracted fermion
  pair `ubar3`. -/
lemma pairX_ubar3 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostXel t ht)
        (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) +
      repLorentzGroup ((boostXel t ht)⁻¹)
        (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) =
      ((2 : ℝ) : ℂ) •
        (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostXel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostXel t ht) (Sum.inr 2) 0 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostXel t ht) (Sum.inr 2) 1 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostXel t⁻¹ (inv_ne_zero ht)) (Sum.inr 2) 0 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostXel t⁻¹ (inv_ne_zero ht)) (Sum.inr 2) 1 1,
    toLorentzGroup_boostXel, boostXel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatX_00, boostMatX_01, boostMatX_02, boostMatX_03,
    boostMatX_10, boostMatX_11, boostMatX_12, boostMatX_13,
    boostMatX_20, boostMatX_21, boostMatX_22, boostMatX_23,
    boostMatX_30, boostMatX_31, boostMatX_32, boostMatX_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `Y`-boost on the σ-contracted fermion
  pair `ubar0`. -/
lemma pairY_ubar0 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) +
      (Complex.I * (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ)) •
        (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostYel t ht) (Sum.inl 0) 0 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostYel t ht) (Sum.inl 0) 1 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostYel t⁻¹ (inv_ne_zero ht)) (Sum.inl 0) 0 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostYel t⁻¹ (inv_ne_zero ht)) (Sum.inl 0) 1 1,
    toLorentzGroup_boostYel, boostYel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring_nf; try simp only [Complex.I_sq]; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `Y`-boost on the σ-contracted fermion
  pair `ubar1`. -/
lemma pairY_ubar1 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0) =
      ((2 : ℝ) : ℂ) •
        (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostYel t ht) (Sum.inr 0) 0 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostYel t ht) (Sum.inr 0) 1 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostYel t⁻¹ (inv_ne_zero ht)) (Sum.inr 0) 0 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostYel t⁻¹ (inv_ne_zero ht)) (Sum.inr 0) 1 0,
    toLorentzGroup_boostYel, boostYel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring_nf; try simp only [Complex.I_sq]; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `Y`-boost on the σ-contracted fermion
  pair `ubar2`. -/
lemma pairY_ubar2 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0) =
      (((t ^ 4 + 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ) •
        (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0) +
      (-(Complex.I * (((t ^ 4 - 1) ^ 2 / (2 * t ^ 4) : ℝ) : ℂ))) •
        (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostYel t ht) (Sum.inr 1) 0 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostYel t ht) (Sum.inr 1) 1 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostYel t⁻¹ (inv_ne_zero ht)) (Sum.inr 1) 0 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostYel t⁻¹ (inv_ne_zero ht)) (Sum.inr 1) 1 0,
    toLorentzGroup_boostYel, boostYel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring_nf; try simp only [Complex.I_sq]; try ring)

set_option maxHeartbeats 4000000 in
/-- The paired boost action of the `Y`-boost on the σ-contracted fermion
  pair `ubar3`. -/
lemma pairY_ubar3 (t : ℝ) (ht : t ≠ 0) :
    repLorentzGroup (boostYel t ht)
        (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) +
      repLorentzGroup ((boostYel t ht)⁻¹)
        (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) =
      ((2 : ℝ) : ℂ) •
        (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [boostYel_inv]
  simp only [map_add, map_sub,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostYel t ht) (Sum.inr 2) 0 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostYel t ht) (Sum.inr 2) 1 1,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostYel t⁻¹ (inv_ne_zero ht)) (Sum.inr 2) 0 0,
    repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil (boostYel t⁻¹ (inv_ne_zero ht)) (Sum.inr 2) 1 1,
    toLorentzGroup_boostYel, boostYel_inv_coe,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    boostMatY_00, boostMatY_01, boostMatY_02, boostMatY_03,
    boostMatY_10, boostMatY_11, boostMatY_12, boostMatY_13,
    boostMatY_20, boostMatY_21, boostMatY_22, boostMatY_23,
    boostMatY_30, boostMatY_31, boostMatY_32, boostMatY_33,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_add, map_sub, map_mul, map_div₀, map_inv₀, map_ofNat,
    map_zero, map_one, map_neg, Complex.conj_ofReal, Complex.conj_I,
    star_zero, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_neg, zero_smul, smul_zero, smul_neg,
    neg_smul, add_zero, zero_add, neg_zero]
  match_scalars <;> (push_cast; try field_simp; try ring_nf; try simp only [Complex.I_sq]; try ring)

/-- The `Z`-axis boost-weighted average: the identity together with the
  paired boosts at `t = 2, 3, 4`, with weights chosen so that the operator
  fixes invariant vectors and acts as the Klein-restricted single-axis
  average on the weight-eight sector. -/
noncomputable def boostProjZ : Module.End ℂ JetAlgebra :=
  (65359/21600 : ℂ) • LinearMap.id
  + (-133264/99225 : ℂ) • (repLorentzGroup (boostZel 2 (by norm_num)) +
      repLorentzGroup ((boostZel 2 (by norm_num))⁻¹))
  + (384183/1019200 : ℂ) • (repLorentzGroup (boostZel 3 (by norm_num)) +
      repLorentzGroup ((boostZel 3 (by norm_num))⁻¹))
  + (-60416/1289925 : ℂ) • (repLorentzGroup (boostZel 4 (by norm_num)) +
      repLorentzGroup ((boostZel 4 (by norm_num))⁻¹))

/-- The `X`-axis boost-weighted average: the identity together with the
  paired boosts at `t = 2, 3, 4`, with weights chosen so that the operator
  fixes invariant vectors and acts as the Klein-restricted single-axis
  average on the weight-eight sector. -/
noncomputable def boostProjX : Module.End ℂ JetAlgebra :=
  (65359/21600 : ℂ) • LinearMap.id
  + (-133264/99225 : ℂ) • (repLorentzGroup (boostXel 2 (by norm_num)) +
      repLorentzGroup ((boostXel 2 (by norm_num))⁻¹))
  + (384183/1019200 : ℂ) • (repLorentzGroup (boostXel 3 (by norm_num)) +
      repLorentzGroup ((boostXel 3 (by norm_num))⁻¹))
  + (-60416/1289925 : ℂ) • (repLorentzGroup (boostXel 4 (by norm_num)) +
      repLorentzGroup ((boostXel 4 (by norm_num))⁻¹))

/-- The `Y`-axis boost-weighted average: the identity together with the
  paired boosts at `t = 2, 3, 4`, with weights chosen so that the operator
  fixes invariant vectors and acts as the Klein-restricted single-axis
  average on the weight-eight sector. -/
noncomputable def boostProjY : Module.End ℂ JetAlgebra :=
  (65359/21600 : ℂ) • LinearMap.id
  + (-133264/99225 : ℂ) • (repLorentzGroup (boostYel 2 (by norm_num)) +
      repLorentzGroup ((boostYel 2 (by norm_num))⁻¹))
  + (384183/1019200 : ℂ) • (repLorentzGroup (boostYel 3 (by norm_num)) +
      repLorentzGroup ((boostYel 3 (by norm_num))⁻¹))
  + (-60416/1289925 : ℂ) • (repLorentzGroup (boostYel 4 (by norm_num)) +
      repLorentzGroup ((boostYel 4 (by norm_num))⁻¹))

/-- The symmetrised boost average over the three axes. -/
noncomputable def opS : Module.End ℂ JetAlgebra :=
  (3⁻¹ : ℂ) • (boostProjZ + boostProjX + boostProjY)

/-- The operator `opS` fixes every Lorentz-invariant vector: each boost term
  fixes it and the weights sum to one. -/
lemma opS_apply_of_invariant {y : JetAlgebra}
    (hinv : ∀ Λ : SL(2,ℂ), repLorentzGroup Λ y = y) : opS y = y := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply, hinv]
  match_scalars
  norm_num

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `F01 * F01`. -/
lemma opS_F01_F01 :
    opS (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_F01_F01 2 (by norm_num),
    pairZ_F01_F01 3 (by norm_num),
    pairZ_F01_F01 4 (by norm_num),
    pairX_F01_F01 2 (by norm_num),
    pairX_F01_F01 3 (by norm_num),
    pairX_F01_F01 4 (by norm_num),
    pairY_F01_F01 2 (by norm_num),
    pairY_F01_F01 3 (by norm_num),
    pairY_F01_F01 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `F01 * F23`. -/
lemma opS_F01_F23 :
    opS (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2))
      + (1/6 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_F01_F23 2 (by norm_num),
    pairZ_F01_F23 3 (by norm_num),
    pairZ_F01_F23 4 (by norm_num),
    pairX_F01_F23 2 (by norm_num),
    pairX_F01_F23 3 (by norm_num),
    pairX_F01_F23 4 (by norm_num),
    pairY_F01_F23 2 (by norm_num),
    pairY_F01_F23 3 (by norm_num),
    pairY_F01_F23 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `F02 * F02`. -/
lemma opS_F02_F02 :
    opS (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_F02_F02 2 (by norm_num),
    pairZ_F02_F02 3 (by norm_num),
    pairZ_F02_F02 4 (by norm_num),
    pairX_F02_F02 2 (by norm_num),
    pairX_F02_F02 3 (by norm_num),
    pairX_F02_F02 4 (by norm_num),
    pairY_F02_F02 2 (by norm_num),
    pairY_F02_F02 3 (by norm_num),
    pairY_F02_F02 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `F02 * F13`. -/
lemma opS_F02_F13 :
    opS (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_F02_F13 2 (by norm_num),
    pairZ_F02_F13 3 (by norm_num),
    pairZ_F02_F13 4 (by norm_num),
    pairX_F02_F13 2 (by norm_num),
    pairX_F02_F13 3 (by norm_num),
    pairX_F02_F13 4 (by norm_num),
    pairY_F02_F13 2 (by norm_num),
    pairY_F02_F13 3 (by norm_num),
    pairY_F02_F13 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `F03 * F03`. -/
lemma opS_F03_F03 :
    opS (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_F03_F03 2 (by norm_num),
    pairZ_F03_F03 3 (by norm_num),
    pairZ_F03_F03 4 (by norm_num),
    pairX_F03_F03 2 (by norm_num),
    pairX_F03_F03 3 (by norm_num),
    pairX_F03_F03 4 (by norm_num),
    pairY_F03_F03 2 (by norm_num),
    pairY_F03_F03 3 (by norm_num),
    pairY_F03_F03 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `F03 * F12`. -/
lemma opS_F03_F12 :
    opS (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1))
      + (1/6 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_F03_F12 2 (by norm_num),
    pairZ_F03_F12 3 (by norm_num),
    pairZ_F03_F12 4 (by norm_num),
    pairX_F03_F12 2 (by norm_num),
    pairX_F03_F12 3 (by norm_num),
    pairX_F03_F12 4 (by norm_num),
    pairY_F03_F12 2 (by norm_num),
    pairY_F03_F12 3 (by norm_num),
    pairY_F03_F12 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `F12 * F12`. -/
lemma opS_F12_F12 :
    opS (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_F12_F12 2 (by norm_num),
    pairZ_F12_F12 3 (by norm_num),
    pairZ_F12_F12 4 (by norm_num),
    pairX_F12_F12 2 (by norm_num),
    pairX_F12_F12 3 (by norm_num),
    pairX_F12_F12 4 (by norm_num),
    pairY_F12_F12 2 (by norm_num),
    pairY_F12_F12 3 (by norm_num),
    pairY_F12_F12 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `F13 * F13`. -/
lemma opS_F13_F13 :
    opS (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_F13_F13 2 (by norm_num),
    pairZ_F13_F13 3 (by norm_num),
    pairZ_F13_F13 4 (by norm_num),
    pairX_F13_F13 2 (by norm_num),
    pairX_F13_F13 3 (by norm_num),
    pairX_F13_F13 4 (by norm_num),
    pairY_F13_F13 2 (by norm_num),
    pairY_F13_F13 3 (by norm_num),
    pairY_F13_F13 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `F23 * F23`. -/
lemma opS_F23_F23 :
    opS (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_F23_F23 2 (by norm_num),
    pairZ_F23_F23 3 (by norm_num),
    pairZ_F23_F23 4 (by norm_num),
    pairX_F23_F23 2 (by norm_num),
    pairX_F23_F23 3 (by norm_num),
    pairX_F23_F23 4 (by norm_num),
    pairY_F23_F23 2 (by norm_num),
    pairY_F23_F23 3 (by norm_num),
    pairY_F23_F23 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `∂∂F01` with derivative indices `(0, 1)`. -/
lemma opS_dd01_F01 :
    opS (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) =
      (1/3 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_dd01_F01 2 (by norm_num),
    pairZ_dd01_F01 3 (by norm_num),
    pairZ_dd01_F01 4 (by norm_num),
    pairX_dd01_F01 2 (by norm_num),
    pairX_dd01_F01 3 (by norm_num),
    pairX_dd01_F01 4 (by norm_num),
    pairY_dd01_F01 2 (by norm_num),
    pairY_dd01_F01 3 (by norm_num),
    pairY_dd01_F01 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `∂∂F23` with derivative indices `(0, 1)`. -/
lemma opS_dd01_F23 :
    opS (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) =
      (1/3 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_dd01_F23 2 (by norm_num),
    pairZ_dd01_F23 3 (by norm_num),
    pairZ_dd01_F23 4 (by norm_num),
    pairX_dd01_F23 2 (by norm_num),
    pairX_dd01_F23 3 (by norm_num),
    pairX_dd01_F23 4 (by norm_num),
    pairY_dd01_F23 2 (by norm_num),
    pairY_dd01_F23 3 (by norm_num),
    pairY_dd01_F23 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `∂∂F02` with derivative indices `(0, 2)`. -/
lemma opS_dd02_F02 :
    opS (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) =
      (1/3 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_dd02_F02 2 (by norm_num),
    pairZ_dd02_F02 3 (by norm_num),
    pairZ_dd02_F02 4 (by norm_num),
    pairX_dd02_F02 2 (by norm_num),
    pairX_dd02_F02 3 (by norm_num),
    pairX_dd02_F02 4 (by norm_num),
    pairY_dd02_F02 2 (by norm_num),
    pairY_dd02_F02 3 (by norm_num),
    pairY_dd02_F02 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `∂∂F13` with derivative indices `(0, 2)`. -/
lemma opS_dd02_F13 :
    opS (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) =
      (1/3 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_dd02_F13 2 (by norm_num),
    pairZ_dd02_F13 3 (by norm_num),
    pairZ_dd02_F13 4 (by norm_num),
    pairX_dd02_F13 2 (by norm_num),
    pairX_dd02_F13 3 (by norm_num),
    pairX_dd02_F13 4 (by norm_num),
    pairY_dd02_F13 2 (by norm_num),
    pairY_dd02_F13 3 (by norm_num),
    pairY_dd02_F13 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `∂∂F03` with derivative indices `(0, 3)`. -/
lemma opS_dd03_F03 :
    opS (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) =
      (1/3 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_dd03_F03 2 (by norm_num),
    pairZ_dd03_F03 3 (by norm_num),
    pairZ_dd03_F03 4 (by norm_num),
    pairX_dd03_F03 2 (by norm_num),
    pairX_dd03_F03 3 (by norm_num),
    pairX_dd03_F03 4 (by norm_num),
    pairY_dd03_F03 2 (by norm_num),
    pairY_dd03_F03 3 (by norm_num),
    pairY_dd03_F03 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `∂∂F12` with derivative indices `(0, 3)`. -/
lemma opS_dd03_F12 :
    opS (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) =
      (1/3 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_dd03_F12 2 (by norm_num),
    pairZ_dd03_F12 3 (by norm_num),
    pairZ_dd03_F12 4 (by norm_num),
    pairX_dd03_F12 2 (by norm_num),
    pairX_dd03_F12 3 (by norm_num),
    pairX_dd03_F12 4 (by norm_num),
    pairY_dd03_F12 2 (by norm_num),
    pairY_dd03_F12 3 (by norm_num),
    pairY_dd03_F12 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `∂∂F03` with derivative indices `(1, 2)`. -/
lemma opS_dd12_F03 :
    opS (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_dd12_F03 2 (by norm_num),
    pairZ_dd12_F03 3 (by norm_num),
    pairZ_dd12_F03 4 (by norm_num),
    pairX_dd12_F03 2 (by norm_num),
    pairX_dd12_F03 3 (by norm_num),
    pairX_dd12_F03 4 (by norm_num),
    pairY_dd12_F03 2 (by norm_num),
    pairY_dd12_F03 3 (by norm_num),
    pairY_dd12_F03 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `∂∂F12` with derivative indices `(1, 2)`. -/
lemma opS_dd12_F12 :
    opS (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_dd12_F12 2 (by norm_num),
    pairZ_dd12_F12 3 (by norm_num),
    pairZ_dd12_F12 4 (by norm_num),
    pairX_dd12_F12 2 (by norm_num),
    pairX_dd12_F12 3 (by norm_num),
    pairX_dd12_F12 4 (by norm_num),
    pairY_dd12_F12 2 (by norm_num),
    pairY_dd12_F12 3 (by norm_num),
    pairY_dd12_F12 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `∂∂F02` with derivative indices `(1, 3)`. -/
lemma opS_dd13_F02 :
    opS (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_dd13_F02 2 (by norm_num),
    pairZ_dd13_F02 3 (by norm_num),
    pairZ_dd13_F02 4 (by norm_num),
    pairX_dd13_F02 2 (by norm_num),
    pairX_dd13_F02 3 (by norm_num),
    pairX_dd13_F02 4 (by norm_num),
    pairY_dd13_F02 2 (by norm_num),
    pairY_dd13_F02 3 (by norm_num),
    pairY_dd13_F02 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `∂∂F13` with derivative indices `(1, 3)`. -/
lemma opS_dd13_F13 :
    opS (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_dd13_F13 2 (by norm_num),
    pairZ_dd13_F13 3 (by norm_num),
    pairZ_dd13_F13 4 (by norm_num),
    pairX_dd13_F13 2 (by norm_num),
    pairX_dd13_F13 3 (by norm_num),
    pairX_dd13_F13 4 (by norm_num),
    pairY_dd13_F13 2 (by norm_num),
    pairY_dd13_F13 3 (by norm_num),
    pairY_dd13_F13 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `∂∂F01` with derivative indices `(2, 3)`. -/
lemma opS_dd23_F01 :
    opS (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_dd23_F01 2 (by norm_num),
    pairZ_dd23_F01 3 (by norm_num),
    pairZ_dd23_F01 4 (by norm_num),
    pairX_dd23_F01 2 (by norm_num),
    pairX_dd23_F01 3 (by norm_num),
    pairX_dd23_F01 4 (by norm_num),
    pairY_dd23_F01 2 (by norm_num),
    pairY_dd23_F01 3 (by norm_num),
    pairY_dd23_F01 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on `∂∂F23` with derivative indices `(2, 3)`. -/
lemma opS_dd23_F23 :
    opS (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) =
      (2/3 : ℂ) • (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2))
      + (1/6 : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1))
      + (-(1/6) : ℂ) • (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_dd23_F23 2 (by norm_num),
    pairZ_dd23_F23 3 (by norm_num),
    pairZ_dd23_F23 4 (by norm_num),
    pairX_dd23_F23 2 (by norm_num),
    pairX_dd23_F23 3 (by norm_num),
    pairX_dd23_F23 4 (by norm_num),
    pairY_dd23_F23 2 (by norm_num),
    pairY_dd23_F23 3 (by norm_num),
    pairY_dd23_F23 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on the σ-contracted fermion pair `u0`. -/
lemma opS_u0 :
    opS (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) =
      (1/2 : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1)
      + (-(1/6) : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0)
      + (-(Complex.I/6)) • (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0)
      + (-(1/6) : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_u0 2 (by norm_num),
    pairZ_u0 3 (by norm_num),
    pairZ_u0 4 (by norm_num),
    pairX_u0 2 (by norm_num),
    pairX_u0 3 (by norm_num),
    pairX_u0 4 (by norm_num),
    pairY_u0 2 (by norm_num),
    pairY_u0 3 (by norm_num),
    pairY_u0 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on the σ-contracted fermion pair `u1`. -/
lemma opS_u1 :
    opS (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0) =
      (5/6 : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0)
      + (-(1/6) : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_u1 2 (by norm_num),
    pairZ_u1 3 (by norm_num),
    pairZ_u1 4 (by norm_num),
    pairX_u1 2 (by norm_num),
    pairX_u1 3 (by norm_num),
    pairX_u1 4 (by norm_num),
    pairY_u1 2 (by norm_num),
    pairY_u1 3 (by norm_num),
    pairY_u1 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on the σ-contracted fermion pair `u2`. -/
lemma opS_u2 :
    opS (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0) =
      (5/6 : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0)
      + (Complex.I/6) • (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_u2 2 (by norm_num),
    pairZ_u2 3 (by norm_num),
    pairZ_u2 4 (by norm_num),
    pairX_u2 2 (by norm_num),
    pairX_u2 3 (by norm_num),
    pairX_u2 4 (by norm_num),
    pairY_u2 2 (by norm_num),
    pairY_u2 3 (by norm_num),
    pairY_u2 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on the σ-contracted fermion pair `u3`. -/
lemma opS_u3 :
    opS (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) =
      (5/6 : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1)
      + (-(1/6) : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_u3 2 (by norm_num),
    pairZ_u3 3 (by norm_num),
    pairZ_u3 4 (by norm_num),
    pairX_u3 2 (by norm_num),
    pairX_u3 3 (by norm_num),
    pairX_u3 4 (by norm_num),
    pairY_u3 2 (by norm_num),
    pairY_u3 3 (by norm_num),
    pairY_u3 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on the σ-contracted fermion pair `ubar0`. -/
lemma opS_ubar0 :
    opS (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) =
      (1/2 : ℂ) • (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1)
      + (-(1/6) : ℂ) • (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0)
      + (-(Complex.I/6)) • (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0)
      + (-(1/6) : ℂ) • (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_ubar0 2 (by norm_num),
    pairZ_ubar0 3 (by norm_num),
    pairZ_ubar0 4 (by norm_num),
    pairX_ubar0 2 (by norm_num),
    pairX_ubar0 3 (by norm_num),
    pairX_ubar0 4 (by norm_num),
    pairY_ubar0 2 (by norm_num),
    pairY_ubar0 3 (by norm_num),
    pairY_ubar0 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on the σ-contracted fermion pair `ubar1`. -/
lemma opS_ubar1 :
    opS (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0) =
      (5/6 : ℂ) • (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0)
      + (-(1/6) : ℂ) • (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_ubar1 2 (by norm_num),
    pairZ_ubar1 3 (by norm_num),
    pairZ_ubar1 4 (by norm_num),
    pairX_ubar1 2 (by norm_num),
    pairX_ubar1 3 (by norm_num),
    pairX_ubar1 4 (by norm_num),
    pairY_ubar1 2 (by norm_num),
    pairY_ubar1 3 (by norm_num),
    pairY_ubar1 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on the σ-contracted fermion pair `ubar2`. -/
lemma opS_ubar2 :
    opS (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0) =
      (5/6 : ℂ) • (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0)
      + (Complex.I/6) • (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_ubar2 2 (by norm_num),
    pairZ_ubar2 3 (by norm_num),
    pairZ_ubar2 4 (by norm_num),
    pairX_ubar2 2 (by norm_num),
    pairX_ubar2 3 (by norm_num),
    pairX_ubar2 4 (by norm_num),
    pairY_ubar2 2 (by norm_num),
    pairY_ubar2 3 (by norm_num),
    pairY_ubar2 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

set_option maxHeartbeats 4000000 in
/-- The boost average `opS` on the σ-contracted fermion pair `ubar3`. -/
lemma opS_ubar3 :
    opS (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) =
      (5/6 : ℂ) • (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1)
      + (-(1/6) : ℂ) • (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) := by
  simp only [opS, boostProjZ, boostProjX, boostProjY, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  simp only [pairZ_ubar3 2 (by norm_num),
    pairZ_ubar3 3 (by norm_num),
    pairZ_ubar3 4 (by norm_num),
    pairX_ubar3 2 (by norm_num),
    pairX_ubar3 3 (by norm_num),
    pairX_ubar3 4 (by norm_num),
    pairY_ubar3 2 (by norm_num),
    pairY_ubar3 3 (by norm_num),
    pairY_ubar3 4 (by norm_num)]
  match_scalars <;> (push_cast; try ring_nf; try norm_num)

/-!

### The projector polynomial and the weight-eight endgame

-/

/-- Negation moves out of the left factor of a jet-algebra product. -/
lemma neg_mul_jet (x y : JetAlgebra) : -x * y = -(x * y) := by grind

/-- Negation moves out of the right factor of a jet-algebra product. -/
lemma mul_neg_jet (x y : JetAlgebra) : x * -y = -(x * y) := by grind

/-- The quintic projector polynomial in the symmetrised boost average `opS`:
  the unique degree-five polynomial with value one at the invariant eigenvalue
  and vanishing on the remaining boost eigenvalues of the weight-eight Klein
  sector. -/
noncomputable def opPi : Module.End ℂ JetAlgebra :=
  (-1 : ℂ) • (1 : Module.End ℂ JetAlgebra) + (137/10 : ℂ) • opS
    + (-(135/2) : ℂ) • (opS * opS) + (153 : ℂ) • (opS * opS * opS)
    + (-162 : ℂ) • (opS * opS * opS * opS)
    + (324/5 : ℂ) • (opS * opS * opS * opS * opS)

/-- The projector polynomial, termwise. -/
lemma opPi_apply (v : JetAlgebra) :
    opPi v = (-1 : ℂ) • v + (137/10 : ℂ) • opS v
      + (-(135/2) : ℂ) • opS (opS v) + (153 : ℂ) • opS (opS (opS v))
      + (-162 : ℂ) • opS (opS (opS (opS v)))
      + (324/5 : ℂ) • opS (opS (opS (opS (opS v)))) := by
  simp only [opPi, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    Module.End.mul_apply]

/-- The projector fixes every Lorentz-invariant vector: `opS` fixes it and the
  coefficients sum to one. -/
lemma opPi_apply_of_invariant {y : JetAlgebra}
    (hinv : ∀ Λ : SL(2,ℂ), repLorentzGroup Λ y = y) : opPi y = y := by
  have hS : opS y = y := opS_apply_of_invariant hinv
  rw [opPi_apply]
  simp only [hS]
  match_scalars
  norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 0 of the FF block. -/
lemma projFF0 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 : M}
    (h0 : T v0 = (2/3 : ℂ) • v0 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v7)
    (h1 : T v1 = (2/3 : ℂ) • v1 + (-(1/6) : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h2 : T v2 = (2/3 : ℂ) • v2 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v8)
    (h3 : T v3 = (2/3 : ℂ) • v3 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h4 : T v4 = (2/3 : ℂ) • v4 + (-(1/6) : ℂ) • v7 + (-(1/6) : ℂ) • v8)
    (h5 : T v5 = (2/3 : ℂ) • v5 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (-(1/6) : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v0 + (137/10 : ℂ) • T v0 + (-(135/2) : ℂ) • T (T v0)
      + (153 : ℂ) • T (T (T v0)) + (-162 : ℂ) • T (T (T (T v0)))
      + (324/5 : ℂ) • T (T (T (T (T v0)))) =
    (-(1/12) : ℂ) • ((-2 : ℂ) • v0 + (-2 : ℂ) • v2 + (-2 : ℂ) • v4 + (2 : ℂ) • v6 + (2 : ℂ) • v7 + (2 : ℂ) • v8) := by
  have i2 : T (T v0) =
      (1/2 : ℂ) • (v0)
      + (1/36 : ℂ) • (v2)
      + (1/36 : ℂ) • (v4)
      + (-(2/9) : ℂ) • (v6)
      + (-(2/9) : ℂ) • (v7) := by
    rw [h0]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i3 : T (T (T v0)) =
      (11/27 : ℂ) • (v0)
      + (1/18 : ℂ) • (v2)
      + (1/18 : ℂ) • (v4)
      + (-(17/72) : ℂ) • (v6)
      + (-(17/72) : ℂ) • (v7)
      + (-(1/108) : ℂ) • (v8) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v0))) =
      (227/648 : ℂ) • (v0)
      + (101/1296 : ℂ) • (v2)
      + (101/1296 : ℂ) • (v4)
      + (-(19/81) : ℂ) • (v6)
      + (-(19/81) : ℂ) • (v7)
      + (-(2/81) : ℂ) • (v8) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v0)))) =
      (101/324 : ℂ) • (v0)
      + (185/1944 : ℂ) • (v2)
      + (185/1944 : ℂ) • (v4)
      + (-(1771/7776) : ℂ) • (v6)
      + (-(1771/7776) : ℂ) • (v7)
      + (-(55/1296) : ℂ) • (v8) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h0]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 1 of the FF block. -/
lemma projFF1 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 : M}
    (h0 : T v0 = (2/3 : ℂ) • v0 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v7)
    (h1 : T v1 = (2/3 : ℂ) • v1 + (-(1/6) : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h2 : T v2 = (2/3 : ℂ) • v2 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v8)
    (h3 : T v3 = (2/3 : ℂ) • v3 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h4 : T v4 = (2/3 : ℂ) • v4 + (-(1/6) : ℂ) • v7 + (-(1/6) : ℂ) • v8)
    (h5 : T v5 = (2/3 : ℂ) • v5 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (-(1/6) : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v1 + (137/10 : ℂ) • T v1 + (-(135/2) : ℂ) • T (T v1)
      + (153 : ℂ) • T (T (T v1)) + (-162 : ℂ) • T (T (T (T v1)))
      + (324/5 : ℂ) • T (T (T (T (T v1)))) =
    (1/24 : ℂ) • ((8 : ℂ) • v1 + (-8 : ℂ) • v3 + (8 : ℂ) • v5) := by
  have i2 : T (T v1) =
      (1/2 : ℂ) • (v1)
      + (-(1/4) : ℂ) • (v3)
      + (1/4 : ℂ) • (v5) := by
    rw [h1]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i3 : T (T (T v1)) =
      (5/12 : ℂ) • (v1)
      + (-(7/24) : ℂ) • (v3)
      + (7/24 : ℂ) • (v5) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v1))) =
      (3/8 : ℂ) • (v1)
      + (-(5/16) : ℂ) • (v3)
      + (5/16 : ℂ) • (v5) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v1)))) =
      (17/48 : ℂ) • (v1)
      + (-(31/96) : ℂ) • (v3)
      + (31/96 : ℂ) • (v5) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h1]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 2 of the FF block. -/
lemma projFF2 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 : M}
    (h0 : T v0 = (2/3 : ℂ) • v0 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v7)
    (h1 : T v1 = (2/3 : ℂ) • v1 + (-(1/6) : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h2 : T v2 = (2/3 : ℂ) • v2 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v8)
    (h3 : T v3 = (2/3 : ℂ) • v3 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h4 : T v4 = (2/3 : ℂ) • v4 + (-(1/6) : ℂ) • v7 + (-(1/6) : ℂ) • v8)
    (h5 : T v5 = (2/3 : ℂ) • v5 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (-(1/6) : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v2 + (137/10 : ℂ) • T v2 + (-(135/2) : ℂ) • T (T v2)
      + (153 : ℂ) • T (T (T v2)) + (-162 : ℂ) • T (T (T (T v2)))
      + (324/5 : ℂ) • T (T (T (T (T v2)))) =
    (-(1/12) : ℂ) • ((-2 : ℂ) • v0 + (-2 : ℂ) • v2 + (-2 : ℂ) • v4 + (2 : ℂ) • v6 + (2 : ℂ) • v7 + (2 : ℂ) • v8) := by
  have i2 : T (T v2) =
      (1/36 : ℂ) • (v0)
      + (1/2 : ℂ) • (v2)
      + (1/36 : ℂ) • (v4)
      + (-(2/9) : ℂ) • (v6)
      + (-(2/9) : ℂ) • (v8) := by
    rw [h2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i3 : T (T (T v2)) =
      (1/18 : ℂ) • (v0)
      + (11/27 : ℂ) • (v2)
      + (1/18 : ℂ) • (v4)
      + (-(17/72) : ℂ) • (v6)
      + (-(1/108) : ℂ) • (v7)
      + (-(17/72) : ℂ) • (v8) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v2))) =
      (101/1296 : ℂ) • (v0)
      + (227/648 : ℂ) • (v2)
      + (101/1296 : ℂ) • (v4)
      + (-(19/81) : ℂ) • (v6)
      + (-(2/81) : ℂ) • (v7)
      + (-(19/81) : ℂ) • (v8) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v2)))) =
      (185/1944 : ℂ) • (v0)
      + (101/324 : ℂ) • (v2)
      + (185/1944 : ℂ) • (v4)
      + (-(1771/7776) : ℂ) • (v6)
      + (-(55/1296) : ℂ) • (v7)
      + (-(1771/7776) : ℂ) • (v8) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h2]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 3 of the FF block. -/
lemma projFF3 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 : M}
    (h0 : T v0 = (2/3 : ℂ) • v0 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v7)
    (h1 : T v1 = (2/3 : ℂ) • v1 + (-(1/6) : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h2 : T v2 = (2/3 : ℂ) • v2 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v8)
    (h3 : T v3 = (2/3 : ℂ) • v3 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h4 : T v4 = (2/3 : ℂ) • v4 + (-(1/6) : ℂ) • v7 + (-(1/6) : ℂ) • v8)
    (h5 : T v5 = (2/3 : ℂ) • v5 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (-(1/6) : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v3 + (137/10 : ℂ) • T v3 + (-(135/2) : ℂ) • T (T v3)
      + (153 : ℂ) • T (T (T v3)) + (-162 : ℂ) • T (T (T (T v3)))
      + (324/5 : ℂ) • T (T (T (T (T v3)))) =
    (-(1/24) : ℂ) • ((8 : ℂ) • v1 + (-8 : ℂ) • v3 + (8 : ℂ) • v5) := by
  have i2 : T (T v3) =
      (-(1/4) : ℂ) • (v1)
      + (1/2 : ℂ) • (v3)
      + (-(1/4) : ℂ) • (v5) := by
    rw [h3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i3 : T (T (T v3)) =
      (-(7/24) : ℂ) • (v1)
      + (5/12 : ℂ) • (v3)
      + (-(7/24) : ℂ) • (v5) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v3))) =
      (-(5/16) : ℂ) • (v1)
      + (3/8 : ℂ) • (v3)
      + (-(5/16) : ℂ) • (v5) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v3)))) =
      (-(31/96) : ℂ) • (v1)
      + (17/48 : ℂ) • (v3)
      + (-(31/96) : ℂ) • (v5) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h3]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 4 of the FF block. -/
lemma projFF4 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 : M}
    (h0 : T v0 = (2/3 : ℂ) • v0 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v7)
    (h1 : T v1 = (2/3 : ℂ) • v1 + (-(1/6) : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h2 : T v2 = (2/3 : ℂ) • v2 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v8)
    (h3 : T v3 = (2/3 : ℂ) • v3 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h4 : T v4 = (2/3 : ℂ) • v4 + (-(1/6) : ℂ) • v7 + (-(1/6) : ℂ) • v8)
    (h5 : T v5 = (2/3 : ℂ) • v5 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (-(1/6) : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v4 + (137/10 : ℂ) • T v4 + (-(135/2) : ℂ) • T (T v4)
      + (153 : ℂ) • T (T (T v4)) + (-162 : ℂ) • T (T (T (T v4)))
      + (324/5 : ℂ) • T (T (T (T (T v4)))) =
    (-(1/12) : ℂ) • ((-2 : ℂ) • v0 + (-2 : ℂ) • v2 + (-2 : ℂ) • v4 + (2 : ℂ) • v6 + (2 : ℂ) • v7 + (2 : ℂ) • v8) := by
  have i2 : T (T v4) =
      (1/36 : ℂ) • (v0)
      + (1/36 : ℂ) • (v2)
      + (1/2 : ℂ) • (v4)
      + (-(2/9) : ℂ) • (v7)
      + (-(2/9) : ℂ) • (v8) := by
    rw [h4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i3 : T (T (T v4)) =
      (1/18 : ℂ) • (v0)
      + (1/18 : ℂ) • (v2)
      + (11/27 : ℂ) • (v4)
      + (-(1/108) : ℂ) • (v6)
      + (-(17/72) : ℂ) • (v7)
      + (-(17/72) : ℂ) • (v8) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v4))) =
      (101/1296 : ℂ) • (v0)
      + (101/1296 : ℂ) • (v2)
      + (227/648 : ℂ) • (v4)
      + (-(2/81) : ℂ) • (v6)
      + (-(19/81) : ℂ) • (v7)
      + (-(19/81) : ℂ) • (v8) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v4)))) =
      (185/1944 : ℂ) • (v0)
      + (185/1944 : ℂ) • (v2)
      + (101/324 : ℂ) • (v4)
      + (-(55/1296) : ℂ) • (v6)
      + (-(1771/7776) : ℂ) • (v7)
      + (-(1771/7776) : ℂ) • (v8) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h4]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 5 of the FF block. -/
lemma projFF5 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 : M}
    (h0 : T v0 = (2/3 : ℂ) • v0 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v7)
    (h1 : T v1 = (2/3 : ℂ) • v1 + (-(1/6) : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h2 : T v2 = (2/3 : ℂ) • v2 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v8)
    (h3 : T v3 = (2/3 : ℂ) • v3 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h4 : T v4 = (2/3 : ℂ) • v4 + (-(1/6) : ℂ) • v7 + (-(1/6) : ℂ) • v8)
    (h5 : T v5 = (2/3 : ℂ) • v5 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (-(1/6) : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v5 + (137/10 : ℂ) • T v5 + (-(135/2) : ℂ) • T (T v5)
      + (153 : ℂ) • T (T (T v5)) + (-162 : ℂ) • T (T (T (T v5)))
      + (324/5 : ℂ) • T (T (T (T (T v5)))) =
    (1/24 : ℂ) • ((8 : ℂ) • v1 + (-8 : ℂ) • v3 + (8 : ℂ) • v5) := by
  have i2 : T (T v5) =
      (1/4 : ℂ) • (v1)
      + (-(1/4) : ℂ) • (v3)
      + (1/2 : ℂ) • (v5) := by
    rw [h5]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i3 : T (T (T v5)) =
      (7/24 : ℂ) • (v1)
      + (-(7/24) : ℂ) • (v3)
      + (5/12 : ℂ) • (v5) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v5))) =
      (5/16 : ℂ) • (v1)
      + (-(5/16) : ℂ) • (v3)
      + (3/8 : ℂ) • (v5) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v5)))) =
      (31/96 : ℂ) • (v1)
      + (-(31/96) : ℂ) • (v3)
      + (17/48 : ℂ) • (v5) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h5]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 6 of the FF block. -/
lemma projFF6 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 : M}
    (h0 : T v0 = (2/3 : ℂ) • v0 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v7)
    (h1 : T v1 = (2/3 : ℂ) • v1 + (-(1/6) : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h2 : T v2 = (2/3 : ℂ) • v2 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v8)
    (h3 : T v3 = (2/3 : ℂ) • v3 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h4 : T v4 = (2/3 : ℂ) • v4 + (-(1/6) : ℂ) • v7 + (-(1/6) : ℂ) • v8)
    (h5 : T v5 = (2/3 : ℂ) • v5 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (-(1/6) : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v6 + (137/10 : ℂ) • T v6 + (-(135/2) : ℂ) • T (T v6)
      + (153 : ℂ) • T (T (T v6)) + (-162 : ℂ) • T (T (T (T v6)))
      + (324/5 : ℂ) • T (T (T (T (T v6)))) =
    (1/12 : ℂ) • ((-2 : ℂ) • v0 + (-2 : ℂ) • v2 + (-2 : ℂ) • v4 + (2 : ℂ) • v6 + (2 : ℂ) • v7 + (2 : ℂ) • v8) := by
  have i2 : T (T v6) =
      (-(2/9) : ℂ) • (v0)
      + (-(2/9) : ℂ) • (v2)
      + (1/2 : ℂ) • (v6)
      + (1/36 : ℂ) • (v7)
      + (1/36 : ℂ) • (v8) := by
    rw [h6]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i3 : T (T (T v6)) =
      (-(17/72) : ℂ) • (v0)
      + (-(17/72) : ℂ) • (v2)
      + (-(1/108) : ℂ) • (v4)
      + (11/27 : ℂ) • (v6)
      + (1/18 : ℂ) • (v7)
      + (1/18 : ℂ) • (v8) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v6))) =
      (-(19/81) : ℂ) • (v0)
      + (-(19/81) : ℂ) • (v2)
      + (-(2/81) : ℂ) • (v4)
      + (227/648 : ℂ) • (v6)
      + (101/1296 : ℂ) • (v7)
      + (101/1296 : ℂ) • (v8) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v6)))) =
      (-(1771/7776) : ℂ) • (v0)
      + (-(1771/7776) : ℂ) • (v2)
      + (-(55/1296) : ℂ) • (v4)
      + (101/324 : ℂ) • (v6)
      + (185/1944 : ℂ) • (v7)
      + (185/1944 : ℂ) • (v8) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h6]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 7 of the FF block. -/
lemma projFF7 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 : M}
    (h0 : T v0 = (2/3 : ℂ) • v0 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v7)
    (h1 : T v1 = (2/3 : ℂ) • v1 + (-(1/6) : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h2 : T v2 = (2/3 : ℂ) • v2 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v8)
    (h3 : T v3 = (2/3 : ℂ) • v3 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h4 : T v4 = (2/3 : ℂ) • v4 + (-(1/6) : ℂ) • v7 + (-(1/6) : ℂ) • v8)
    (h5 : T v5 = (2/3 : ℂ) • v5 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (-(1/6) : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v7 + (137/10 : ℂ) • T v7 + (-(135/2) : ℂ) • T (T v7)
      + (153 : ℂ) • T (T (T v7)) + (-162 : ℂ) • T (T (T (T v7)))
      + (324/5 : ℂ) • T (T (T (T (T v7)))) =
    (1/12 : ℂ) • ((-2 : ℂ) • v0 + (-2 : ℂ) • v2 + (-2 : ℂ) • v4 + (2 : ℂ) • v6 + (2 : ℂ) • v7 + (2 : ℂ) • v8) := by
  have i2 : T (T v7) =
      (-(2/9) : ℂ) • (v0)
      + (-(2/9) : ℂ) • (v4)
      + (1/36 : ℂ) • (v6)
      + (1/2 : ℂ) • (v7)
      + (1/36 : ℂ) • (v8) := by
    rw [h7]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i3 : T (T (T v7)) =
      (-(17/72) : ℂ) • (v0)
      + (-(1/108) : ℂ) • (v2)
      + (-(17/72) : ℂ) • (v4)
      + (1/18 : ℂ) • (v6)
      + (11/27 : ℂ) • (v7)
      + (1/18 : ℂ) • (v8) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v7))) =
      (-(19/81) : ℂ) • (v0)
      + (-(2/81) : ℂ) • (v2)
      + (-(19/81) : ℂ) • (v4)
      + (101/1296 : ℂ) • (v6)
      + (227/648 : ℂ) • (v7)
      + (101/1296 : ℂ) • (v8) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v7)))) =
      (-(1771/7776) : ℂ) • (v0)
      + (-(55/1296) : ℂ) • (v2)
      + (-(1771/7776) : ℂ) • (v4)
      + (185/1944 : ℂ) • (v6)
      + (101/324 : ℂ) • (v7)
      + (185/1944 : ℂ) • (v8) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h7]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 8 of the FF block. -/
lemma projFF8 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 : M}
    (h0 : T v0 = (2/3 : ℂ) • v0 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v7)
    (h1 : T v1 = (2/3 : ℂ) • v1 + (-(1/6) : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h2 : T v2 = (2/3 : ℂ) • v2 + (-(1/6) : ℂ) • v6 + (-(1/6) : ℂ) • v8)
    (h3 : T v3 = (2/3 : ℂ) • v3 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h4 : T v4 = (2/3 : ℂ) • v4 + (-(1/6) : ℂ) • v7 + (-(1/6) : ℂ) • v8)
    (h5 : T v5 = (2/3 : ℂ) • v5 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (-(1/6) : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (-(1/6) : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v8 + (137/10 : ℂ) • T v8 + (-(135/2) : ℂ) • T (T v8)
      + (153 : ℂ) • T (T (T v8)) + (-162 : ℂ) • T (T (T (T v8)))
      + (324/5 : ℂ) • T (T (T (T (T v8)))) =
    (1/12 : ℂ) • ((-2 : ℂ) • v0 + (-2 : ℂ) • v2 + (-2 : ℂ) • v4 + (2 : ℂ) • v6 + (2 : ℂ) • v7 + (2 : ℂ) • v8) := by
  have i2 : T (T v8) =
      (-(2/9) : ℂ) • (v2)
      + (-(2/9) : ℂ) • (v4)
      + (1/36 : ℂ) • (v6)
      + (1/36 : ℂ) • (v7)
      + (1/2 : ℂ) • (v8) := by
    rw [h8]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i3 : T (T (T v8)) =
      (-(1/108) : ℂ) • (v0)
      + (-(17/72) : ℂ) • (v2)
      + (-(17/72) : ℂ) • (v4)
      + (1/18 : ℂ) • (v6)
      + (1/18 : ℂ) • (v7)
      + (11/27 : ℂ) • (v8) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v8))) =
      (-(2/81) : ℂ) • (v0)
      + (-(19/81) : ℂ) • (v2)
      + (-(19/81) : ℂ) • (v4)
      + (101/1296 : ℂ) • (v6)
      + (101/1296 : ℂ) • (v7)
      + (227/648 : ℂ) • (v8) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v8)))) =
      (-(55/1296) : ℂ) • (v0)
      + (-(1771/7776) : ℂ) • (v2)
      + (-(1771/7776) : ℂ) • (v4)
      + (185/1944 : ℂ) • (v6)
      + (185/1944 : ℂ) • (v7)
      + (101/324 : ℂ) • (v8) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h8]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 0 of the DDF block. -/
lemma projDDF0 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : M}
    (h0 : T v0 = (1/3 : ℂ) • v0 + (1/6 : ℂ) • v7 + (1/6 : ℂ) • v9)
    (h1 : T v1 = (1/3 : ℂ) • v1 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v8)
    (h2 : T v2 = (1/3 : ℂ) • v2 + (-(1/6) : ℂ) • v7 + (1/6 : ℂ) • v11)
    (h3 : T v3 = (1/3 : ℂ) • v3 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v10)
    (h4 : T v4 = (1/3 : ℂ) • v4 + (-(1/6) : ℂ) • v9 + (-(1/6) : ℂ) • v11)
    (h5 : T v5 = (1/3 : ℂ) • v5 + (-(1/6) : ℂ) • v8 + (1/6 : ℂ) • v10)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h9 : T v9 = (2/3 : ℂ) • v9 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h10 : T v10 = (2/3 : ℂ) • v10 + (1/6 : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h11 : T v11 = (2/3 : ℂ) • v11 + (1/6 : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v0 + (137/10 : ℂ) • T v0 + (-(135/2) : ℂ) • T (T v0)
      + (153 : ℂ) • T (T (T v0)) + (-162 : ℂ) • T (T (T (T v0)))
      + (324/5 : ℂ) • T (T (T (T (T v0)))) =
    (0 : M) := by
  have i2 : T (T v0) =
      (1/6 : ℂ) • (v0)
      + (-(1/36) : ℂ) • (v2)
      + (-(1/36) : ℂ) • (v4)
      + (1/6 : ℂ) • (v7)
      + (1/6 : ℂ) • (v9) := by
    rw [h0]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i3 : T (T (T v0)) =
      (1/9 : ℂ) • (v0)
      + (-(1/27) : ℂ) • (v2)
      + (-(1/27) : ℂ) • (v4)
      + (31/216 : ℂ) • (v7)
      + (31/216 : ℂ) • (v9) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v0))) =
      (55/648 : ℂ) • (v0)
      + (-(47/1296) : ℂ) • (v2)
      + (-(47/1296) : ℂ) • (v4)
      + (13/108 : ℂ) • (v7)
      + (13/108 : ℂ) • (v9) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v0)))) =
      (133/1944 : ℂ) • (v0)
      + (-(125/3888) : ℂ) • (v2)
      + (-(125/3888) : ℂ) • (v4)
      + (781/7776 : ℂ) • (v7)
      + (781/7776 : ℂ) • (v9) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h0]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 1 of the DDF block. -/
lemma projDDF1 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : M}
    (h0 : T v0 = (1/3 : ℂ) • v0 + (1/6 : ℂ) • v7 + (1/6 : ℂ) • v9)
    (h1 : T v1 = (1/3 : ℂ) • v1 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v8)
    (h2 : T v2 = (1/3 : ℂ) • v2 + (-(1/6) : ℂ) • v7 + (1/6 : ℂ) • v11)
    (h3 : T v3 = (1/3 : ℂ) • v3 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v10)
    (h4 : T v4 = (1/3 : ℂ) • v4 + (-(1/6) : ℂ) • v9 + (-(1/6) : ℂ) • v11)
    (h5 : T v5 = (1/3 : ℂ) • v5 + (-(1/6) : ℂ) • v8 + (1/6 : ℂ) • v10)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h9 : T v9 = (2/3 : ℂ) • v9 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h10 : T v10 = (2/3 : ℂ) • v10 + (1/6 : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h11 : T v11 = (2/3 : ℂ) • v11 + (1/6 : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v1 + (137/10 : ℂ) • T v1 + (-(135/2) : ℂ) • T (T v1)
      + (153 : ℂ) • T (T (T v1)) + (-162 : ℂ) • T (T (T (T v1)))
      + (324/5 : ℂ) • T (T (T (T (T v1)))) =
    (0 : M) := by
  have i2 : T (T v1) =
      (1/6 : ℂ) • (v1)
      + (1/36 : ℂ) • (v3)
      + (-(1/36) : ℂ) • (v5)
      + (-(1/6) : ℂ) • (v6)
      + (1/6 : ℂ) • (v8) := by
    rw [h1]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i3 : T (T (T v1)) =
      (1/9 : ℂ) • (v1)
      + (1/27 : ℂ) • (v3)
      + (-(1/27) : ℂ) • (v5)
      + (-(31/216) : ℂ) • (v6)
      + (31/216 : ℂ) • (v8) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v1))) =
      (55/648 : ℂ) • (v1)
      + (47/1296 : ℂ) • (v3)
      + (-(47/1296) : ℂ) • (v5)
      + (-(13/108) : ℂ) • (v6)
      + (13/108 : ℂ) • (v8) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v1)))) =
      (133/1944 : ℂ) • (v1)
      + (125/3888 : ℂ) • (v3)
      + (-(125/3888) : ℂ) • (v5)
      + (-(781/7776) : ℂ) • (v6)
      + (781/7776 : ℂ) • (v8) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h1]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 2 of the DDF block. -/
lemma projDDF2 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : M}
    (h0 : T v0 = (1/3 : ℂ) • v0 + (1/6 : ℂ) • v7 + (1/6 : ℂ) • v9)
    (h1 : T v1 = (1/3 : ℂ) • v1 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v8)
    (h2 : T v2 = (1/3 : ℂ) • v2 + (-(1/6) : ℂ) • v7 + (1/6 : ℂ) • v11)
    (h3 : T v3 = (1/3 : ℂ) • v3 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v10)
    (h4 : T v4 = (1/3 : ℂ) • v4 + (-(1/6) : ℂ) • v9 + (-(1/6) : ℂ) • v11)
    (h5 : T v5 = (1/3 : ℂ) • v5 + (-(1/6) : ℂ) • v8 + (1/6 : ℂ) • v10)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h9 : T v9 = (2/3 : ℂ) • v9 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h10 : T v10 = (2/3 : ℂ) • v10 + (1/6 : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h11 : T v11 = (2/3 : ℂ) • v11 + (1/6 : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v2 + (137/10 : ℂ) • T v2 + (-(135/2) : ℂ) • T (T v2)
      + (153 : ℂ) • T (T (T v2)) + (-162 : ℂ) • T (T (T (T v2)))
      + (324/5 : ℂ) • T (T (T (T (T v2)))) =
    (0 : M) := by
  have i2 : T (T v2) =
      (-(1/36) : ℂ) • (v0)
      + (1/6 : ℂ) • (v2)
      + (-(1/36) : ℂ) • (v4)
      + (-(1/6) : ℂ) • (v7)
      + (1/6 : ℂ) • (v11) := by
    rw [h2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i3 : T (T (T v2)) =
      (-(1/27) : ℂ) • (v0)
      + (1/9 : ℂ) • (v2)
      + (-(1/27) : ℂ) • (v4)
      + (-(31/216) : ℂ) • (v7)
      + (31/216 : ℂ) • (v11) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v2))) =
      (-(47/1296) : ℂ) • (v0)
      + (55/648 : ℂ) • (v2)
      + (-(47/1296) : ℂ) • (v4)
      + (-(13/108) : ℂ) • (v7)
      + (13/108 : ℂ) • (v11) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v2)))) =
      (-(125/3888) : ℂ) • (v0)
      + (133/1944 : ℂ) • (v2)
      + (-(125/3888) : ℂ) • (v4)
      + (-(781/7776) : ℂ) • (v7)
      + (781/7776 : ℂ) • (v11) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h2]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 3 of the DDF block. -/
lemma projDDF3 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : M}
    (h0 : T v0 = (1/3 : ℂ) • v0 + (1/6 : ℂ) • v7 + (1/6 : ℂ) • v9)
    (h1 : T v1 = (1/3 : ℂ) • v1 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v8)
    (h2 : T v2 = (1/3 : ℂ) • v2 + (-(1/6) : ℂ) • v7 + (1/6 : ℂ) • v11)
    (h3 : T v3 = (1/3 : ℂ) • v3 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v10)
    (h4 : T v4 = (1/3 : ℂ) • v4 + (-(1/6) : ℂ) • v9 + (-(1/6) : ℂ) • v11)
    (h5 : T v5 = (1/3 : ℂ) • v5 + (-(1/6) : ℂ) • v8 + (1/6 : ℂ) • v10)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h9 : T v9 = (2/3 : ℂ) • v9 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h10 : T v10 = (2/3 : ℂ) • v10 + (1/6 : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h11 : T v11 = (2/3 : ℂ) • v11 + (1/6 : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v3 + (137/10 : ℂ) • T v3 + (-(135/2) : ℂ) • T (T v3)
      + (153 : ℂ) • T (T (T v3)) + (-162 : ℂ) • T (T (T (T v3)))
      + (324/5 : ℂ) • T (T (T (T (T v3)))) =
    (0 : M) := by
  have i2 : T (T v3) =
      (1/36 : ℂ) • (v1)
      + (1/6 : ℂ) • (v3)
      + (1/36 : ℂ) • (v5)
      + (-(1/6) : ℂ) • (v6)
      + (1/6 : ℂ) • (v10) := by
    rw [h3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i3 : T (T (T v3)) =
      (1/27 : ℂ) • (v1)
      + (1/9 : ℂ) • (v3)
      + (1/27 : ℂ) • (v5)
      + (-(31/216) : ℂ) • (v6)
      + (31/216 : ℂ) • (v10) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v3))) =
      (47/1296 : ℂ) • (v1)
      + (55/648 : ℂ) • (v3)
      + (47/1296 : ℂ) • (v5)
      + (-(13/108) : ℂ) • (v6)
      + (13/108 : ℂ) • (v10) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v3)))) =
      (125/3888 : ℂ) • (v1)
      + (133/1944 : ℂ) • (v3)
      + (125/3888 : ℂ) • (v5)
      + (-(781/7776) : ℂ) • (v6)
      + (781/7776 : ℂ) • (v10) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h3]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 4 of the DDF block. -/
lemma projDDF4 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : M}
    (h0 : T v0 = (1/3 : ℂ) • v0 + (1/6 : ℂ) • v7 + (1/6 : ℂ) • v9)
    (h1 : T v1 = (1/3 : ℂ) • v1 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v8)
    (h2 : T v2 = (1/3 : ℂ) • v2 + (-(1/6) : ℂ) • v7 + (1/6 : ℂ) • v11)
    (h3 : T v3 = (1/3 : ℂ) • v3 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v10)
    (h4 : T v4 = (1/3 : ℂ) • v4 + (-(1/6) : ℂ) • v9 + (-(1/6) : ℂ) • v11)
    (h5 : T v5 = (1/3 : ℂ) • v5 + (-(1/6) : ℂ) • v8 + (1/6 : ℂ) • v10)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h9 : T v9 = (2/3 : ℂ) • v9 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h10 : T v10 = (2/3 : ℂ) • v10 + (1/6 : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h11 : T v11 = (2/3 : ℂ) • v11 + (1/6 : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v4 + (137/10 : ℂ) • T v4 + (-(135/2) : ℂ) • T (T v4)
      + (153 : ℂ) • T (T (T v4)) + (-162 : ℂ) • T (T (T (T v4)))
      + (324/5 : ℂ) • T (T (T (T (T v4)))) =
    (0 : M) := by
  have i2 : T (T v4) =
      (-(1/36) : ℂ) • (v0)
      + (-(1/36) : ℂ) • (v2)
      + (1/6 : ℂ) • (v4)
      + (-(1/6) : ℂ) • (v9)
      + (-(1/6) : ℂ) • (v11) := by
    rw [h4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i3 : T (T (T v4)) =
      (-(1/27) : ℂ) • (v0)
      + (-(1/27) : ℂ) • (v2)
      + (1/9 : ℂ) • (v4)
      + (-(31/216) : ℂ) • (v9)
      + (-(31/216) : ℂ) • (v11) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v4))) =
      (-(47/1296) : ℂ) • (v0)
      + (-(47/1296) : ℂ) • (v2)
      + (55/648 : ℂ) • (v4)
      + (-(13/108) : ℂ) • (v9)
      + (-(13/108) : ℂ) • (v11) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v4)))) =
      (-(125/3888) : ℂ) • (v0)
      + (-(125/3888) : ℂ) • (v2)
      + (133/1944 : ℂ) • (v4)
      + (-(781/7776) : ℂ) • (v9)
      + (-(781/7776) : ℂ) • (v11) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h4]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 5 of the DDF block. -/
lemma projDDF5 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : M}
    (h0 : T v0 = (1/3 : ℂ) • v0 + (1/6 : ℂ) • v7 + (1/6 : ℂ) • v9)
    (h1 : T v1 = (1/3 : ℂ) • v1 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v8)
    (h2 : T v2 = (1/3 : ℂ) • v2 + (-(1/6) : ℂ) • v7 + (1/6 : ℂ) • v11)
    (h3 : T v3 = (1/3 : ℂ) • v3 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v10)
    (h4 : T v4 = (1/3 : ℂ) • v4 + (-(1/6) : ℂ) • v9 + (-(1/6) : ℂ) • v11)
    (h5 : T v5 = (1/3 : ℂ) • v5 + (-(1/6) : ℂ) • v8 + (1/6 : ℂ) • v10)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h9 : T v9 = (2/3 : ℂ) • v9 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h10 : T v10 = (2/3 : ℂ) • v10 + (1/6 : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h11 : T v11 = (2/3 : ℂ) • v11 + (1/6 : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v5 + (137/10 : ℂ) • T v5 + (-(135/2) : ℂ) • T (T v5)
      + (153 : ℂ) • T (T (T v5)) + (-162 : ℂ) • T (T (T (T v5)))
      + (324/5 : ℂ) • T (T (T (T (T v5)))) =
    (0 : M) := by
  have i2 : T (T v5) =
      (-(1/36) : ℂ) • (v1)
      + (1/36 : ℂ) • (v3)
      + (1/6 : ℂ) • (v5)
      + (-(1/6) : ℂ) • (v8)
      + (1/6 : ℂ) • (v10) := by
    rw [h5]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i3 : T (T (T v5)) =
      (-(1/27) : ℂ) • (v1)
      + (1/27 : ℂ) • (v3)
      + (1/9 : ℂ) • (v5)
      + (-(31/216) : ℂ) • (v8)
      + (31/216 : ℂ) • (v10) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v5))) =
      (-(47/1296) : ℂ) • (v1)
      + (47/1296 : ℂ) • (v3)
      + (55/648 : ℂ) • (v5)
      + (-(13/108) : ℂ) • (v8)
      + (13/108 : ℂ) • (v10) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v5)))) =
      (-(125/3888) : ℂ) • (v1)
      + (125/3888 : ℂ) • (v3)
      + (133/1944 : ℂ) • (v5)
      + (-(781/7776) : ℂ) • (v8)
      + (781/7776 : ℂ) • (v10) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h5]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 6 of the DDF block. -/
lemma projDDF6 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : M}
    (h0 : T v0 = (1/3 : ℂ) • v0 + (1/6 : ℂ) • v7 + (1/6 : ℂ) • v9)
    (h1 : T v1 = (1/3 : ℂ) • v1 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v8)
    (h2 : T v2 = (1/3 : ℂ) • v2 + (-(1/6) : ℂ) • v7 + (1/6 : ℂ) • v11)
    (h3 : T v3 = (1/3 : ℂ) • v3 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v10)
    (h4 : T v4 = (1/3 : ℂ) • v4 + (-(1/6) : ℂ) • v9 + (-(1/6) : ℂ) • v11)
    (h5 : T v5 = (1/3 : ℂ) • v5 + (-(1/6) : ℂ) • v8 + (1/6 : ℂ) • v10)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h9 : T v9 = (2/3 : ℂ) • v9 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h10 : T v10 = (2/3 : ℂ) • v10 + (1/6 : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h11 : T v11 = (2/3 : ℂ) • v11 + (1/6 : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v6 + (137/10 : ℂ) • T v6 + (-(135/2) : ℂ) • T (T v6)
      + (153 : ℂ) • T (T (T v6)) + (-162 : ℂ) • T (T (T (T v6)))
      + (324/5 : ℂ) • T (T (T (T (T v6)))) =
    (0 : M) := by
  have i2 : T (T v6) =
      (-(1/6) : ℂ) • (v1)
      + (-(1/6) : ℂ) • (v3)
      + (1/2 : ℂ) • (v6)
      + (-(1/36) : ℂ) • (v8)
      + (-(1/36) : ℂ) • (v10) := by
    rw [h6]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i3 : T (T (T v6)) =
      (-(31/216) : ℂ) • (v1)
      + (-(31/216) : ℂ) • (v3)
      + (7/18 : ℂ) • (v6)
      + (-(5/108) : ℂ) • (v8)
      + (-(5/108) : ℂ) • (v10) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v6))) =
      (-(13/108) : ℂ) • (v1)
      + (-(13/108) : ℂ) • (v3)
      + (199/648 : ℂ) • (v6)
      + (-(71/1296) : ℂ) • (v8)
      + (-(71/1296) : ℂ) • (v10) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v6)))) =
      (-(781/7776) : ℂ) • (v1)
      + (-(781/7776) : ℂ) • (v3)
      + (119/486 : ℂ) • (v6)
      + (-(55/972) : ℂ) • (v8)
      + (-(55/972) : ℂ) • (v10) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h6]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 7 of the DDF block. -/
lemma projDDF7 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : M}
    (h0 : T v0 = (1/3 : ℂ) • v0 + (1/6 : ℂ) • v7 + (1/6 : ℂ) • v9)
    (h1 : T v1 = (1/3 : ℂ) • v1 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v8)
    (h2 : T v2 = (1/3 : ℂ) • v2 + (-(1/6) : ℂ) • v7 + (1/6 : ℂ) • v11)
    (h3 : T v3 = (1/3 : ℂ) • v3 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v10)
    (h4 : T v4 = (1/3 : ℂ) • v4 + (-(1/6) : ℂ) • v9 + (-(1/6) : ℂ) • v11)
    (h5 : T v5 = (1/3 : ℂ) • v5 + (-(1/6) : ℂ) • v8 + (1/6 : ℂ) • v10)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h9 : T v9 = (2/3 : ℂ) • v9 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h10 : T v10 = (2/3 : ℂ) • v10 + (1/6 : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h11 : T v11 = (2/3 : ℂ) • v11 + (1/6 : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v7 + (137/10 : ℂ) • T v7 + (-(135/2) : ℂ) • T (T v7)
      + (153 : ℂ) • T (T (T v7)) + (-162 : ℂ) • T (T (T (T v7)))
      + (324/5 : ℂ) • T (T (T (T (T v7)))) =
    (0 : M) := by
  have i2 : T (T v7) =
      (1/6 : ℂ) • (v0)
      + (-(1/6) : ℂ) • (v2)
      + (1/2 : ℂ) • (v7)
      + (1/36 : ℂ) • (v9)
      + (-(1/36) : ℂ) • (v11) := by
    rw [h7]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i3 : T (T (T v7)) =
      (31/216 : ℂ) • (v0)
      + (-(31/216) : ℂ) • (v2)
      + (7/18 : ℂ) • (v7)
      + (5/108 : ℂ) • (v9)
      + (-(5/108) : ℂ) • (v11) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v7))) =
      (13/108 : ℂ) • (v0)
      + (-(13/108) : ℂ) • (v2)
      + (199/648 : ℂ) • (v7)
      + (71/1296 : ℂ) • (v9)
      + (-(71/1296) : ℂ) • (v11) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v7)))) =
      (781/7776 : ℂ) • (v0)
      + (-(781/7776) : ℂ) • (v2)
      + (119/486 : ℂ) • (v7)
      + (55/972 : ℂ) • (v9)
      + (-(55/972) : ℂ) • (v11) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h7]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 8 of the DDF block. -/
lemma projDDF8 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : M}
    (h0 : T v0 = (1/3 : ℂ) • v0 + (1/6 : ℂ) • v7 + (1/6 : ℂ) • v9)
    (h1 : T v1 = (1/3 : ℂ) • v1 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v8)
    (h2 : T v2 = (1/3 : ℂ) • v2 + (-(1/6) : ℂ) • v7 + (1/6 : ℂ) • v11)
    (h3 : T v3 = (1/3 : ℂ) • v3 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v10)
    (h4 : T v4 = (1/3 : ℂ) • v4 + (-(1/6) : ℂ) • v9 + (-(1/6) : ℂ) • v11)
    (h5 : T v5 = (1/3 : ℂ) • v5 + (-(1/6) : ℂ) • v8 + (1/6 : ℂ) • v10)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h9 : T v9 = (2/3 : ℂ) • v9 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h10 : T v10 = (2/3 : ℂ) • v10 + (1/6 : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h11 : T v11 = (2/3 : ℂ) • v11 + (1/6 : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v8 + (137/10 : ℂ) • T v8 + (-(135/2) : ℂ) • T (T v8)
      + (153 : ℂ) • T (T (T v8)) + (-162 : ℂ) • T (T (T (T v8)))
      + (324/5 : ℂ) • T (T (T (T (T v8)))) =
    (0 : M) := by
  have i2 : T (T v8) =
      (1/6 : ℂ) • (v1)
      + (-(1/6) : ℂ) • (v5)
      + (-(1/36) : ℂ) • (v6)
      + (1/2 : ℂ) • (v8)
      + (-(1/36) : ℂ) • (v10) := by
    rw [h8]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i3 : T (T (T v8)) =
      (31/216 : ℂ) • (v1)
      + (-(31/216) : ℂ) • (v5)
      + (-(5/108) : ℂ) • (v6)
      + (7/18 : ℂ) • (v8)
      + (-(5/108) : ℂ) • (v10) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v8))) =
      (13/108 : ℂ) • (v1)
      + (-(13/108) : ℂ) • (v5)
      + (-(71/1296) : ℂ) • (v6)
      + (199/648 : ℂ) • (v8)
      + (-(71/1296) : ℂ) • (v10) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v8)))) =
      (781/7776 : ℂ) • (v1)
      + (-(781/7776) : ℂ) • (v5)
      + (-(55/972) : ℂ) • (v6)
      + (119/486 : ℂ) • (v8)
      + (-(55/972) : ℂ) • (v10) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h8]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 9 of the DDF block. -/
lemma projDDF9 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : M}
    (h0 : T v0 = (1/3 : ℂ) • v0 + (1/6 : ℂ) • v7 + (1/6 : ℂ) • v9)
    (h1 : T v1 = (1/3 : ℂ) • v1 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v8)
    (h2 : T v2 = (1/3 : ℂ) • v2 + (-(1/6) : ℂ) • v7 + (1/6 : ℂ) • v11)
    (h3 : T v3 = (1/3 : ℂ) • v3 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v10)
    (h4 : T v4 = (1/3 : ℂ) • v4 + (-(1/6) : ℂ) • v9 + (-(1/6) : ℂ) • v11)
    (h5 : T v5 = (1/3 : ℂ) • v5 + (-(1/6) : ℂ) • v8 + (1/6 : ℂ) • v10)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h9 : T v9 = (2/3 : ℂ) • v9 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h10 : T v10 = (2/3 : ℂ) • v10 + (1/6 : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h11 : T v11 = (2/3 : ℂ) • v11 + (1/6 : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v9 + (137/10 : ℂ) • T v9 + (-(135/2) : ℂ) • T (T v9)
      + (153 : ℂ) • T (T (T v9)) + (-162 : ℂ) • T (T (T (T v9)))
      + (324/5 : ℂ) • T (T (T (T (T v9)))) =
    (0 : M) := by
  have i2 : T (T v9) =
      (1/6 : ℂ) • (v0)
      + (-(1/6) : ℂ) • (v4)
      + (1/36 : ℂ) • (v7)
      + (1/2 : ℂ) • (v9)
      + (1/36 : ℂ) • (v11) := by
    rw [h9]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i3 : T (T (T v9)) =
      (31/216 : ℂ) • (v0)
      + (-(31/216) : ℂ) • (v4)
      + (5/108 : ℂ) • (v7)
      + (7/18 : ℂ) • (v9)
      + (5/108 : ℂ) • (v11) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v9))) =
      (13/108 : ℂ) • (v0)
      + (-(13/108) : ℂ) • (v4)
      + (71/1296 : ℂ) • (v7)
      + (199/648 : ℂ) • (v9)
      + (71/1296 : ℂ) • (v11) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v9)))) =
      (781/7776 : ℂ) • (v0)
      + (-(781/7776) : ℂ) • (v4)
      + (55/972 : ℂ) • (v7)
      + (119/486 : ℂ) • (v9)
      + (55/972 : ℂ) • (v11) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h9]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 10 of the DDF block. -/
lemma projDDF10 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : M}
    (h0 : T v0 = (1/3 : ℂ) • v0 + (1/6 : ℂ) • v7 + (1/6 : ℂ) • v9)
    (h1 : T v1 = (1/3 : ℂ) • v1 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v8)
    (h2 : T v2 = (1/3 : ℂ) • v2 + (-(1/6) : ℂ) • v7 + (1/6 : ℂ) • v11)
    (h3 : T v3 = (1/3 : ℂ) • v3 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v10)
    (h4 : T v4 = (1/3 : ℂ) • v4 + (-(1/6) : ℂ) • v9 + (-(1/6) : ℂ) • v11)
    (h5 : T v5 = (1/3 : ℂ) • v5 + (-(1/6) : ℂ) • v8 + (1/6 : ℂ) • v10)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h9 : T v9 = (2/3 : ℂ) • v9 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h10 : T v10 = (2/3 : ℂ) • v10 + (1/6 : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h11 : T v11 = (2/3 : ℂ) • v11 + (1/6 : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v10 + (137/10 : ℂ) • T v10 + (-(135/2) : ℂ) • T (T v10)
      + (153 : ℂ) • T (T (T v10)) + (-162 : ℂ) • T (T (T (T v10)))
      + (324/5 : ℂ) • T (T (T (T (T v10)))) =
    (0 : M) := by
  have i2 : T (T v10) =
      (1/6 : ℂ) • (v3)
      + (1/6 : ℂ) • (v5)
      + (-(1/36) : ℂ) • (v6)
      + (-(1/36) : ℂ) • (v8)
      + (1/2 : ℂ) • (v10) := by
    rw [h10]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i3 : T (T (T v10)) =
      (31/216 : ℂ) • (v3)
      + (31/216 : ℂ) • (v5)
      + (-(5/108) : ℂ) • (v6)
      + (-(5/108) : ℂ) • (v8)
      + (7/18 : ℂ) • (v10) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v10))) =
      (13/108 : ℂ) • (v3)
      + (13/108 : ℂ) • (v5)
      + (-(71/1296) : ℂ) • (v6)
      + (-(71/1296) : ℂ) • (v8)
      + (199/648 : ℂ) • (v10) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v10)))) =
      (781/7776 : ℂ) • (v3)
      + (781/7776 : ℂ) • (v5)
      + (-(55/972) : ℂ) • (v6)
      + (-(55/972) : ℂ) • (v8)
      + (119/486 : ℂ) • (v10) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h10]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 11 of the DDF block. -/
lemma projDDF11 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : M}
    (h0 : T v0 = (1/3 : ℂ) • v0 + (1/6 : ℂ) • v7 + (1/6 : ℂ) • v9)
    (h1 : T v1 = (1/3 : ℂ) • v1 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v8)
    (h2 : T v2 = (1/3 : ℂ) • v2 + (-(1/6) : ℂ) • v7 + (1/6 : ℂ) • v11)
    (h3 : T v3 = (1/3 : ℂ) • v3 + (-(1/6) : ℂ) • v6 + (1/6 : ℂ) • v10)
    (h4 : T v4 = (1/3 : ℂ) • v4 + (-(1/6) : ℂ) • v9 + (-(1/6) : ℂ) • v11)
    (h5 : T v5 = (1/3 : ℂ) • v5 + (-(1/6) : ℂ) • v8 + (1/6 : ℂ) • v10)
    (h6 : T v6 = (2/3 : ℂ) • v6 + (-(1/6) : ℂ) • v1 + (-(1/6) : ℂ) • v3)
    (h7 : T v7 = (2/3 : ℂ) • v7 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v2)
    (h8 : T v8 = (2/3 : ℂ) • v8 + (1/6 : ℂ) • v1 + (-(1/6) : ℂ) • v5)
    (h9 : T v9 = (2/3 : ℂ) • v9 + (1/6 : ℂ) • v0 + (-(1/6) : ℂ) • v4)
    (h10 : T v10 = (2/3 : ℂ) • v10 + (1/6 : ℂ) • v3 + (1/6 : ℂ) • v5)
    (h11 : T v11 = (2/3 : ℂ) • v11 + (1/6 : ℂ) • v2 + (-(1/6) : ℂ) • v4) :
    (-1 : ℂ) • v11 + (137/10 : ℂ) • T v11 + (-(135/2) : ℂ) • T (T v11)
      + (153 : ℂ) • T (T (T v11)) + (-162 : ℂ) • T (T (T (T v11)))
      + (324/5 : ℂ) • T (T (T (T (T v11)))) =
    (0 : M) := by
  have i2 : T (T v11) =
      (1/6 : ℂ) • (v2)
      + (-(1/6) : ℂ) • (v4)
      + (-(1/36) : ℂ) • (v7)
      + (1/36 : ℂ) • (v9)
      + (1/2 : ℂ) • (v11) := by
    rw [h11]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i3 : T (T (T v11)) =
      (31/216 : ℂ) • (v2)
      + (-(31/216) : ℂ) • (v4)
      + (-(5/108) : ℂ) • (v7)
      + (5/108 : ℂ) • (v9)
      + (7/18 : ℂ) • (v11) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i4 : T (T (T (T v11))) =
      (13/108 : ℂ) • (v2)
      + (-(13/108) : ℂ) • (v4)
      + (-(71/1296) : ℂ) • (v7)
      + (71/1296 : ℂ) • (v9)
      + (199/648 : ℂ) • (v11) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  have i5 : T (T (T (T (T v11)))) =
      (781/7776 : ℂ) • (v2)
      + (-(781/7776) : ℂ) • (v4)
      + (-(55/972) : ℂ) • (v7)
      + (55/972 : ℂ) • (v9)
      + (119/486 : ℂ) • (v11) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    match_scalars <;> norm_num
  rw [i5, i4, i3, i2, h11]
  match_scalars <;> norm_num

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 0 of the FMu block. -/
lemma projFMu0 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 : M}
    (h0 : T v0 = (1/2 : ℂ) • v0 + (-(1/6) : ℂ) • v1 + (-(Complex.I/6)) • v2 + (-(1/6) : ℂ) • v3)
    (h1 : T v1 = (5/6 : ℂ) • v1 + (-(1/6) : ℂ) • v0)
    (h2 : T v2 = (5/6 : ℂ) • v2 + (Complex.I/6) • v0)
    (h3 : T v3 = (5/6 : ℂ) • v3 + (-(1/6) : ℂ) • v0) :
    (-1 : ℂ) • v0 + (137/10 : ℂ) • T v0 + (-(135/2) : ℂ) • T (T v0)
      + (153 : ℂ) • T (T (T v0)) + (-162 : ℂ) • T (T (T (T v0)))
      + (324/5 : ℂ) • T (T (T (T (T v0)))) =
    (-(Complex.I/4)) • (Complex.I • (v0 - v1 - Complex.I • v2 - v3)) := by
  have i2 : T (T v0) =
      (1/3 : ℂ) • (v0)
      + (-(2/9) : ℂ) • (v1)
      + ((-(2/9) : ℂ) * Complex.I) • (v2)
      + (-(2/9) : ℂ) • (v3) := by
    rw [h0]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i3 : T (T (T v0)) =
      (5/18 : ℂ) • (v0)
      + (-(13/54) : ℂ) • (v1)
      + ((-(13/54) : ℂ) * Complex.I) • (v2)
      + (-(13/54) : ℂ) • (v3) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i4 : T (T (T (T v0))) =
      (7/27 : ℂ) • (v0)
      + (-(20/81) : ℂ) • (v1)
      + ((-(20/81) : ℂ) * Complex.I) • (v2)
      + (-(20/81) : ℂ) • (v3) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i5 : T (T (T (T (T v0)))) =
      (41/162 : ℂ) • (v0)
      + (-(121/486) : ℂ) • (v1)
      + ((-(121/486) : ℂ) * Complex.I) • (v2)
      + (-(121/486) : ℂ) • (v3) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  rw [i5, i4, i3, i2, h0]
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 1 of the FMu block. -/
lemma projFMu1 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 : M}
    (h0 : T v0 = (1/2 : ℂ) • v0 + (-(1/6) : ℂ) • v1 + (-(Complex.I/6)) • v2 + (-(1/6) : ℂ) • v3)
    (h1 : T v1 = (5/6 : ℂ) • v1 + (-(1/6) : ℂ) • v0)
    (h2 : T v2 = (5/6 : ℂ) • v2 + (Complex.I/6) • v0)
    (h3 : T v3 = (5/6 : ℂ) • v3 + (-(1/6) : ℂ) • v0) :
    (-1 : ℂ) • v1 + (137/10 : ℂ) • T v1 + (-(135/2) : ℂ) • T (T v1)
      + (153 : ℂ) • T (T (T v1)) + (-162 : ℂ) • T (T (T (T v1)))
      + (324/5 : ℂ) • T (T (T (T (T v1)))) =
    (Complex.I/4) • (Complex.I • (v0 - v1 - Complex.I • v2 - v3)) := by
  have i2 : T (T v1) =
      (-(2/9) : ℂ) • (v0)
      + (13/18 : ℂ) • (v1)
      + ((1/36 : ℂ) * Complex.I) • (v2)
      + (1/36 : ℂ) • (v3) := by
    rw [h1]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i3 : T (T (T v1)) =
      (-(13/54) : ℂ) • (v0)
      + (23/36 : ℂ) • (v1)
      + ((13/216 : ℂ) * Complex.I) • (v2)
      + (13/216 : ℂ) • (v3) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i4 : T (T (T (T v1))) =
      (-(20/81) : ℂ) • (v0)
      + (371/648 : ℂ) • (v1)
      + ((13/144 : ℂ) * Complex.I) • (v2)
      + (13/144 : ℂ) • (v3) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i5 : T (T (T (T (T v1)))) =
      (-(121/486) : ℂ) • (v0)
      + (2015/3888 : ℂ) • (v1)
      + ((905/7776 : ℂ) * Complex.I) • (v2)
      + (905/7776 : ℂ) • (v3) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  rw [i5, i4, i3, i2, h1]
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 2 of the FMu block. -/
lemma projFMu2 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 : M}
    (h0 : T v0 = (1/2 : ℂ) • v0 + (-(1/6) : ℂ) • v1 + (-(Complex.I/6)) • v2 + (-(1/6) : ℂ) • v3)
    (h1 : T v1 = (5/6 : ℂ) • v1 + (-(1/6) : ℂ) • v0)
    (h2 : T v2 = (5/6 : ℂ) • v2 + (Complex.I/6) • v0)
    (h3 : T v3 = (5/6 : ℂ) • v3 + (-(1/6) : ℂ) • v0) :
    (-1 : ℂ) • v2 + (137/10 : ℂ) • T v2 + (-(135/2) : ℂ) • T (T v2)
      + (153 : ℂ) • T (T (T v2)) + (-162 : ℂ) • T (T (T (T v2)))
      + (324/5 : ℂ) • T (T (T (T (T v2)))) =
    (1/4 : ℂ) • (Complex.I • (v0 - v1 - Complex.I • v2 - v3)) := by
  have i2 : T (T v2) =
      ((2/9 : ℂ) * Complex.I) • (v0)
      + ((-(1/36) : ℂ) * Complex.I) • (v1)
      + (13/18 : ℂ) • (v2)
      + ((-(1/36) : ℂ) * Complex.I) • (v3) := by
    rw [h2]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i3 : T (T (T v2)) =
      ((13/54 : ℂ) * Complex.I) • (v0)
      + ((-(13/216) : ℂ) * Complex.I) • (v1)
      + (23/36 : ℂ) • (v2)
      + ((-(13/216) : ℂ) * Complex.I) • (v3) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i4 : T (T (T (T v2))) =
      ((20/81 : ℂ) * Complex.I) • (v0)
      + ((-(13/144) : ℂ) * Complex.I) • (v1)
      + (371/648 : ℂ) • (v2)
      + ((-(13/144) : ℂ) * Complex.I) • (v3) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i5 : T (T (T (T (T v2)))) =
      ((121/486 : ℂ) * Complex.I) • (v0)
      + ((-(905/7776) : ℂ) * Complex.I) • (v1)
      + (2015/3888 : ℂ) • (v2)
      + ((-(905/7776) : ℂ) * Complex.I) • (v3) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  rw [i5, i4, i3, i2, h2]
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 3 of the FMu block. -/
lemma projFMu3 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 : M}
    (h0 : T v0 = (1/2 : ℂ) • v0 + (-(1/6) : ℂ) • v1 + (-(Complex.I/6)) • v2 + (-(1/6) : ℂ) • v3)
    (h1 : T v1 = (5/6 : ℂ) • v1 + (-(1/6) : ℂ) • v0)
    (h2 : T v2 = (5/6 : ℂ) • v2 + (Complex.I/6) • v0)
    (h3 : T v3 = (5/6 : ℂ) • v3 + (-(1/6) : ℂ) • v0) :
    (-1 : ℂ) • v3 + (137/10 : ℂ) • T v3 + (-(135/2) : ℂ) • T (T v3)
      + (153 : ℂ) • T (T (T v3)) + (-162 : ℂ) • T (T (T (T v3)))
      + (324/5 : ℂ) • T (T (T (T (T v3)))) =
    (Complex.I/4) • (Complex.I • (v0 - v1 - Complex.I • v2 - v3)) := by
  have i2 : T (T v3) =
      (-(2/9) : ℂ) • (v0)
      + (1/36 : ℂ) • (v1)
      + ((1/36 : ℂ) * Complex.I) • (v2)
      + (13/18 : ℂ) • (v3) := by
    rw [h3]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i3 : T (T (T v3)) =
      (-(13/54) : ℂ) • (v0)
      + (13/216 : ℂ) • (v1)
      + ((13/216 : ℂ) * Complex.I) • (v2)
      + (23/36 : ℂ) • (v3) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i4 : T (T (T (T v3))) =
      (-(20/81) : ℂ) • (v0)
      + (13/144 : ℂ) • (v1)
      + ((13/144 : ℂ) * Complex.I) • (v2)
      + (371/648 : ℂ) • (v3) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i5 : T (T (T (T (T v3)))) =
      (-(121/486) : ℂ) • (v0)
      + (905/7776 : ℂ) • (v1)
      + ((905/7776 : ℂ) * Complex.I) • (v2)
      + (2015/3888 : ℂ) • (v3) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  rw [i5, i4, i3, i2, h3]
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 0 of the FMubar block. -/
lemma projFMubar0 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 : M}
    (h0 : T v0 = (1/2 : ℂ) • v0 + (-(1/6) : ℂ) • v1 + (-(Complex.I/6)) • v2 + (-(1/6) : ℂ) • v3)
    (h1 : T v1 = (5/6 : ℂ) • v1 + (-(1/6) : ℂ) • v0)
    (h2 : T v2 = (5/6 : ℂ) • v2 + (Complex.I/6) • v0)
    (h3 : T v3 = (5/6 : ℂ) • v3 + (-(1/6) : ℂ) • v0) :
    (-1 : ℂ) • v0 + (137/10 : ℂ) • T v0 + (-(135/2) : ℂ) • T (T v0)
      + (153 : ℂ) • T (T (T v0)) + (-162 : ℂ) • T (T (T (T v0)))
      + (324/5 : ℂ) • T (T (T (T (T v0)))) =
    (Complex.I/4) • ((-Complex.I) • (v0 - v1 - Complex.I • v2 - v3)) := by
  have i2 : T (T v0) =
      (1/3 : ℂ) • (v0)
      + (-(2/9) : ℂ) • (v1)
      + ((-(2/9) : ℂ) * Complex.I) • (v2)
      + (-(2/9) : ℂ) • (v3) := by
    rw [h0]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i3 : T (T (T v0)) =
      (5/18 : ℂ) • (v0)
      + (-(13/54) : ℂ) • (v1)
      + ((-(13/54) : ℂ) * Complex.I) • (v2)
      + (-(13/54) : ℂ) • (v3) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i4 : T (T (T (T v0))) =
      (7/27 : ℂ) • (v0)
      + (-(20/81) : ℂ) • (v1)
      + ((-(20/81) : ℂ) * Complex.I) • (v2)
      + (-(20/81) : ℂ) • (v3) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i5 : T (T (T (T (T v0)))) =
      (41/162 : ℂ) • (v0)
      + (-(121/486) : ℂ) • (v1)
      + ((-(121/486) : ℂ) * Complex.I) • (v2)
      + (-(121/486) : ℂ) • (v3) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  rw [i5, i4, i3, i2, h0]
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 1 of the FMubar block. -/
lemma projFMubar1 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 : M}
    (h0 : T v0 = (1/2 : ℂ) • v0 + (-(1/6) : ℂ) • v1 + (-(Complex.I/6)) • v2 + (-(1/6) : ℂ) • v3)
    (h1 : T v1 = (5/6 : ℂ) • v1 + (-(1/6) : ℂ) • v0)
    (h2 : T v2 = (5/6 : ℂ) • v2 + (Complex.I/6) • v0)
    (h3 : T v3 = (5/6 : ℂ) • v3 + (-(1/6) : ℂ) • v0) :
    (-1 : ℂ) • v1 + (137/10 : ℂ) • T v1 + (-(135/2) : ℂ) • T (T v1)
      + (153 : ℂ) • T (T (T v1)) + (-162 : ℂ) • T (T (T (T v1)))
      + (324/5 : ℂ) • T (T (T (T (T v1)))) =
    (-(Complex.I/4)) • ((-Complex.I) • (v0 - v1 - Complex.I • v2 - v3)) := by
  have i2 : T (T v1) =
      (-(2/9) : ℂ) • (v0)
      + (13/18 : ℂ) • (v1)
      + ((1/36 : ℂ) * Complex.I) • (v2)
      + (1/36 : ℂ) • (v3) := by
    rw [h1]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i3 : T (T (T v1)) =
      (-(13/54) : ℂ) • (v0)
      + (23/36 : ℂ) • (v1)
      + ((13/216 : ℂ) * Complex.I) • (v2)
      + (13/216 : ℂ) • (v3) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i4 : T (T (T (T v1))) =
      (-(20/81) : ℂ) • (v0)
      + (371/648 : ℂ) • (v1)
      + ((13/144 : ℂ) * Complex.I) • (v2)
      + (13/144 : ℂ) • (v3) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i5 : T (T (T (T (T v1)))) =
      (-(121/486) : ℂ) • (v0)
      + (2015/3888 : ℂ) • (v1)
      + ((905/7776 : ℂ) * Complex.I) • (v2)
      + (905/7776 : ℂ) • (v3) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  rw [i5, i4, i3, i2, h1]
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 2 of the FMubar block. -/
lemma projFMubar2 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 : M}
    (h0 : T v0 = (1/2 : ℂ) • v0 + (-(1/6) : ℂ) • v1 + (-(Complex.I/6)) • v2 + (-(1/6) : ℂ) • v3)
    (h1 : T v1 = (5/6 : ℂ) • v1 + (-(1/6) : ℂ) • v0)
    (h2 : T v2 = (5/6 : ℂ) • v2 + (Complex.I/6) • v0)
    (h3 : T v3 = (5/6 : ℂ) • v3 + (-(1/6) : ℂ) • v0) :
    (-1 : ℂ) • v2 + (137/10 : ℂ) • T v2 + (-(135/2) : ℂ) • T (T v2)
      + (153 : ℂ) • T (T (T v2)) + (-162 : ℂ) • T (T (T (T v2)))
      + (324/5 : ℂ) • T (T (T (T (T v2)))) =
    (-(1/4) : ℂ) • ((-Complex.I) • (v0 - v1 - Complex.I • v2 - v3)) := by
  have i2 : T (T v2) =
      ((2/9 : ℂ) * Complex.I) • (v0)
      + ((-(1/36) : ℂ) * Complex.I) • (v1)
      + (13/18 : ℂ) • (v2)
      + ((-(1/36) : ℂ) * Complex.I) • (v3) := by
    rw [h2]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i3 : T (T (T v2)) =
      ((13/54 : ℂ) * Complex.I) • (v0)
      + ((-(13/216) : ℂ) * Complex.I) • (v1)
      + (23/36 : ℂ) • (v2)
      + ((-(13/216) : ℂ) * Complex.I) • (v3) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i4 : T (T (T (T v2))) =
      ((20/81 : ℂ) * Complex.I) • (v0)
      + ((-(13/144) : ℂ) * Complex.I) • (v1)
      + (371/648 : ℂ) • (v2)
      + ((-(13/144) : ℂ) * Complex.I) • (v3) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i5 : T (T (T (T (T v2)))) =
      ((121/486 : ℂ) * Complex.I) • (v0)
      + ((-(905/7776) : ℂ) * Complex.I) • (v1)
      + (2015/3888 : ℂ) • (v2)
      + ((-(905/7776) : ℂ) * Complex.I) • (v3) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  rw [i5, i4, i3, i2, h2]
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 2000000 in
/-- The abstract projector computation for column 3 of the FMubar block. -/
lemma projFMubar3 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) {v0 v1 v2 v3 : M}
    (h0 : T v0 = (1/2 : ℂ) • v0 + (-(1/6) : ℂ) • v1 + (-(Complex.I/6)) • v2 + (-(1/6) : ℂ) • v3)
    (h1 : T v1 = (5/6 : ℂ) • v1 + (-(1/6) : ℂ) • v0)
    (h2 : T v2 = (5/6 : ℂ) • v2 + (Complex.I/6) • v0)
    (h3 : T v3 = (5/6 : ℂ) • v3 + (-(1/6) : ℂ) • v0) :
    (-1 : ℂ) • v3 + (137/10 : ℂ) • T v3 + (-(135/2) : ℂ) • T (T v3)
      + (153 : ℂ) • T (T (T v3)) + (-162 : ℂ) • T (T (T (T v3)))
      + (324/5 : ℂ) • T (T (T (T (T v3)))) =
    (-(Complex.I/4)) • ((-Complex.I) • (v0 - v1 - Complex.I • v2 - v3)) := by
  have i2 : T (T v3) =
      (-(2/9) : ℂ) • (v0)
      + (1/36 : ℂ) • (v1)
      + ((1/36 : ℂ) * Complex.I) • (v2)
      + (13/18 : ℂ) • (v3) := by
    rw [h3]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i3 : T (T (T v3)) =
      (-(13/54) : ℂ) • (v0)
      + (13/216 : ℂ) • (v1)
      + ((13/216 : ℂ) * Complex.I) • (v2)
      + (23/36 : ℂ) • (v3) := by
    rw [i2]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i4 : T (T (T (T v3))) =
      (-(20/81) : ℂ) • (v0)
      + (13/144 : ℂ) • (v1)
      + ((13/144 : ℂ) * Complex.I) • (v2)
      + (371/648 : ℂ) • (v3) := by
    rw [i3]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  have i5 : T (T (T (T (T v3)))) =
      (-(121/486) : ℂ) • (v0)
      + (905/7776 : ℂ) • (v1)
      + ((905/7776 : ℂ) * Complex.I) • (v2)
      + (2015/3888 : ℂ) • (v3) := by
    rw [i4]
    simp only [map_add, map_smul, h0, h1, h2, h3]
    match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])
  rw [i5, i4, i3, i2, h3]
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` on the field-strength square `F01_F01`. -/
lemma opPi_F01_F01 :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) =
      (-(1/12) : ℂ) • maxwellTerm := by
  rw [opPi_apply,
    projFF0 opS opS_F01_F01 opS_F01_F23 opS_F02_F02 opS_F02_F13 opS_F03_F03 opS_F03_F12 opS_F12_F12 opS_F13_F13 opS_F23_F23,
    ← maxwellTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` on the field-strength square `F01_F23`. -/
lemma opPi_F01_F23 :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) =
      (1/24 : ℂ) • thetaTerm := by
  rw [opPi_apply,
    projFF1 opS opS_F01_F01 opS_F01_F23 opS_F02_F02 opS_F02_F13 opS_F03_F03 opS_F03_F12 opS_F12_F12 opS_F13_F13 opS_F23_F23,
    ← thetaTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` on the field-strength square `F02_F02`. -/
lemma opPi_F02_F02 :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) =
      (-(1/12) : ℂ) • maxwellTerm := by
  rw [opPi_apply,
    projFF2 opS opS_F01_F01 opS_F01_F23 opS_F02_F02 opS_F02_F13 opS_F03_F03 opS_F03_F12 opS_F12_F12 opS_F13_F13 opS_F23_F23,
    ← maxwellTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` on the field-strength square `F02_F13`. -/
lemma opPi_F02_F13 :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) =
      (-(1/24) : ℂ) • thetaTerm := by
  rw [opPi_apply,
    projFF3 opS opS_F01_F01 opS_F01_F23 opS_F02_F02 opS_F02_F13 opS_F03_F03 opS_F03_F12 opS_F12_F12 opS_F13_F13 opS_F23_F23,
    ← thetaTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` on the field-strength square `F03_F03`. -/
lemma opPi_F03_F03 :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) =
      (-(1/12) : ℂ) • maxwellTerm := by
  rw [opPi_apply,
    projFF4 opS opS_F01_F01 opS_F01_F23 opS_F02_F02 opS_F02_F13 opS_F03_F03 opS_F03_F12 opS_F12_F12 opS_F13_F13 opS_F23_F23,
    ← maxwellTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` on the field-strength square `F03_F12`. -/
lemma opPi_F03_F12 :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) =
      (1/24 : ℂ) • thetaTerm := by
  rw [opPi_apply,
    projFF5 opS opS_F01_F01 opS_F01_F23 opS_F02_F02 opS_F02_F13 opS_F03_F03 opS_F03_F12 opS_F12_F12 opS_F13_F13 opS_F23_F23,
    ← thetaTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` on the field-strength square `F12_F12`. -/
lemma opPi_F12_F12 :
    opPi (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) =
      (1/12 : ℂ) • maxwellTerm := by
  rw [opPi_apply,
    projFF6 opS opS_F01_F01 opS_F01_F23 opS_F02_F02 opS_F02_F13 opS_F03_F03 opS_F03_F12 opS_F12_F12 opS_F13_F13 opS_F23_F23,
    ← maxwellTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` on the field-strength square `F13_F13`. -/
lemma opPi_F13_F13 :
    opPi (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) =
      (1/12 : ℂ) • maxwellTerm := by
  rw [opPi_apply,
    projFF7 opS opS_F01_F01 opS_F01_F23 opS_F02_F02 opS_F02_F13 opS_F03_F03 opS_F03_F12 opS_F12_F12 opS_F13_F13 opS_F23_F23,
    ← maxwellTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` on the field-strength square `F23_F23`. -/
lemma opPi_F23_F23 :
    opPi (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) =
      (1/12 : ℂ) • maxwellTerm := by
  rw [opPi_apply,
    projFF8 opS opS_F01_F01 opS_F01_F23 opS_F02_F02 opS_F02_F13 opS_F03_F03 opS_F03_F12 opS_F12_F12 opS_F13_F13 opS_F23_F23,
    ← maxwellTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` annihilates the derivative monomial `dd01_F01`. -/
lemma opPi_dd01_F01 :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) =
      (0 : JetAlgebra) := by
  rw [opPi_apply,
    projDDF0 opS opS_dd01_F01 opS_dd01_F23 opS_dd02_F02 opS_dd02_F13 opS_dd03_F03 opS_dd03_F12 opS_dd12_F03 opS_dd12_F12 opS_dd13_F02 opS_dd13_F13 opS_dd23_F01 opS_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` annihilates the derivative monomial `dd01_F23`. -/
lemma opPi_dd01_F23 :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) =
      (0 : JetAlgebra) := by
  rw [opPi_apply,
    projDDF1 opS opS_dd01_F01 opS_dd01_F23 opS_dd02_F02 opS_dd02_F13 opS_dd03_F03 opS_dd03_F12 opS_dd12_F03 opS_dd12_F12 opS_dd13_F02 opS_dd13_F13 opS_dd23_F01 opS_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` annihilates the derivative monomial `dd02_F02`. -/
lemma opPi_dd02_F02 :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) =
      (0 : JetAlgebra) := by
  rw [opPi_apply,
    projDDF2 opS opS_dd01_F01 opS_dd01_F23 opS_dd02_F02 opS_dd02_F13 opS_dd03_F03 opS_dd03_F12 opS_dd12_F03 opS_dd12_F12 opS_dd13_F02 opS_dd13_F13 opS_dd23_F01 opS_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` annihilates the derivative monomial `dd02_F13`. -/
lemma opPi_dd02_F13 :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) =
      (0 : JetAlgebra) := by
  rw [opPi_apply,
    projDDF3 opS opS_dd01_F01 opS_dd01_F23 opS_dd02_F02 opS_dd02_F13 opS_dd03_F03 opS_dd03_F12 opS_dd12_F03 opS_dd12_F12 opS_dd13_F02 opS_dd13_F13 opS_dd23_F01 opS_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` annihilates the derivative monomial `dd03_F03`. -/
lemma opPi_dd03_F03 :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) =
      (0 : JetAlgebra) := by
  rw [opPi_apply,
    projDDF4 opS opS_dd01_F01 opS_dd01_F23 opS_dd02_F02 opS_dd02_F13 opS_dd03_F03 opS_dd03_F12 opS_dd12_F03 opS_dd12_F12 opS_dd13_F02 opS_dd13_F13 opS_dd23_F01 opS_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` annihilates the derivative monomial `dd03_F12`. -/
lemma opPi_dd03_F12 :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) =
      (0 : JetAlgebra) := by
  rw [opPi_apply,
    projDDF5 opS opS_dd01_F01 opS_dd01_F23 opS_dd02_F02 opS_dd02_F13 opS_dd03_F03 opS_dd03_F12 opS_dd12_F03 opS_dd12_F12 opS_dd13_F02 opS_dd13_F13 opS_dd23_F01 opS_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` annihilates the derivative monomial `dd12_F03`. -/
lemma opPi_dd12_F03 :
    opPi (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) =
      (0 : JetAlgebra) := by
  rw [opPi_apply,
    projDDF6 opS opS_dd01_F01 opS_dd01_F23 opS_dd02_F02 opS_dd02_F13 opS_dd03_F03 opS_dd03_F12 opS_dd12_F03 opS_dd12_F12 opS_dd13_F02 opS_dd13_F13 opS_dd23_F01 opS_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` annihilates the derivative monomial `dd12_F12`. -/
lemma opPi_dd12_F12 :
    opPi (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) =
      (0 : JetAlgebra) := by
  rw [opPi_apply,
    projDDF7 opS opS_dd01_F01 opS_dd01_F23 opS_dd02_F02 opS_dd02_F13 opS_dd03_F03 opS_dd03_F12 opS_dd12_F03 opS_dd12_F12 opS_dd13_F02 opS_dd13_F13 opS_dd23_F01 opS_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` annihilates the derivative monomial `dd13_F02`. -/
lemma opPi_dd13_F02 :
    opPi (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) =
      (0 : JetAlgebra) := by
  rw [opPi_apply,
    projDDF8 opS opS_dd01_F01 opS_dd01_F23 opS_dd02_F02 opS_dd02_F13 opS_dd03_F03 opS_dd03_F12 opS_dd12_F03 opS_dd12_F12 opS_dd13_F02 opS_dd13_F13 opS_dd23_F01 opS_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` annihilates the derivative monomial `dd13_F13`. -/
lemma opPi_dd13_F13 :
    opPi (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) =
      (0 : JetAlgebra) := by
  rw [opPi_apply,
    projDDF9 opS opS_dd01_F01 opS_dd01_F23 opS_dd02_F02 opS_dd02_F13 opS_dd03_F03 opS_dd03_F12 opS_dd12_F03 opS_dd12_F12 opS_dd13_F02 opS_dd13_F13 opS_dd23_F01 opS_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` annihilates the derivative monomial `dd23_F01`. -/
lemma opPi_dd23_F01 :
    opPi (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) =
      (0 : JetAlgebra) := by
  rw [opPi_apply,
    projDDF10 opS opS_dd01_F01 opS_dd01_F23 opS_dd02_F02 opS_dd02_F13 opS_dd03_F03 opS_dd03_F12 opS_dd12_F03 opS_dd12_F12 opS_dd13_F02 opS_dd13_F13 opS_dd23_F01 opS_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` annihilates the derivative monomial `dd23_F23`. -/
lemma opPi_dd23_F23 :
    opPi (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) =
      (0 : JetAlgebra) := by
  rw [opPi_apply,
    projDDF11 opS opS_dd01_F01 opS_dd01_F23 opS_dd02_F02 opS_dd02_F13 opS_dd03_F03 opS_dd03_F12 opS_dd12_F03 opS_dd12_F12 opS_dd13_F02 opS_dd13_F13 opS_dd23_F01 opS_dd23_F23]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` on the σ-contracted fermion pair `u0`. -/
lemma opPi_u0 :
    opPi (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) =
      (-(Complex.I/4)) • fermionKineticTerm := by
  rw [opPi_apply,
    projFMu0 opS opS_u0 opS_u1 opS_u2 opS_u3,
    ← fermionKineticTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` on the σ-contracted fermion pair `u1`. -/
lemma opPi_u1 :
    opPi (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0) =
      (Complex.I/4) • fermionKineticTerm := by
  rw [opPi_apply,
    projFMu1 opS opS_u0 opS_u1 opS_u2 opS_u3,
    ← fermionKineticTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` on the σ-contracted fermion pair `u2`. -/
lemma opPi_u2 :
    opPi (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0) =
      (1/4 : ℂ) • fermionKineticTerm := by
  rw [opPi_apply,
    projFMu2 opS opS_u0 opS_u1 opS_u2 opS_u3,
    ← fermionKineticTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` on the σ-contracted fermion pair `u3`. -/
lemma opPi_u3 :
    opPi (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) =
      (Complex.I/4) • fermionKineticTerm := by
  rw [opPi_apply,
    projFMu3 opS opS_u0 opS_u1 opS_u2 opS_u3,
    ← fermionKineticTerm_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` on the σ-contracted fermion pair `ubar0`. -/
lemma opPi_ubar0 :
    opPi (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) =
      (Complex.I/4) • fermionKineticTermBar := by
  rw [opPi_apply,
    projFMubar0 opS opS_ubar0 opS_ubar1 opS_ubar2 opS_ubar3,
    ← fermionKineticTermBar_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` on the σ-contracted fermion pair `ubar1`. -/
lemma opPi_ubar1 :
    opPi (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0) =
      (-(Complex.I/4)) • fermionKineticTermBar := by
  rw [opPi_apply,
    projFMubar1 opS opS_ubar0 opS_ubar1 opS_ubar2 opS_ubar3,
    ← fermionKineticTermBar_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` on the σ-contracted fermion pair `ubar2`. -/
lemma opPi_ubar2 :
    opPi (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0) =
      (-(1/4) : ℂ) • fermionKineticTermBar := by
  rw [opPi_apply,
    projFMubar2 opS opS_ubar0 opS_ubar1 opS_ubar2 opS_ubar3,
    ← fermionKineticTermBar_eq]

set_option maxHeartbeats 2000000 in
/-- The projector `opPi` on the σ-contracted fermion pair `ubar3`. -/
lemma opPi_ubar3 :
    opPi (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) =
      (-(Complex.I/4)) • fermionKineticTermBar := by
  rw [opPi_apply,
    projFMubar3 opS opS_ubar0 opS_ubar1 opS_ubar2 opS_ubar3,
    ← fermionKineticTermBar_eq]

/-- Entries of the Lorentz matrix of `parityZ`. -/
lemma parityMatZ_00 :
    (Lorentz.SL2C.toLorentzGroup parityZ).1 (Sum.inl 0) (Sum.inl 0) = 1 := by
  rw [toLorentzGroup_parityZ]
  norm_num [paritySignZ]
  all_goals decide

lemma parityMatZ_01 :
    (Lorentz.SL2C.toLorentzGroup parityZ).1 (Sum.inl 0) (Sum.inr 0) = 0 := by
  rw [toLorentzGroup_parityZ]
  norm_num [paritySignZ]
  all_goals decide

lemma parityMatZ_02 :
    (Lorentz.SL2C.toLorentzGroup parityZ).1 (Sum.inl 0) (Sum.inr 1) = 0 := by
  rw [toLorentzGroup_parityZ]
  norm_num [paritySignZ]
  all_goals decide

lemma parityMatZ_03 :
    (Lorentz.SL2C.toLorentzGroup parityZ).1 (Sum.inl 0) (Sum.inr 2) = 0 := by
  rw [toLorentzGroup_parityZ]
  norm_num [paritySignZ]
  all_goals decide

lemma parityMatZ_10 :
    (Lorentz.SL2C.toLorentzGroup parityZ).1 (Sum.inr 0) (Sum.inl 0) = 0 := by
  rw [toLorentzGroup_parityZ]
  norm_num [paritySignZ]
  all_goals decide

lemma parityMatZ_11 :
    (Lorentz.SL2C.toLorentzGroup parityZ).1 (Sum.inr 0) (Sum.inr 0) = -1 := by
  rw [toLorentzGroup_parityZ]
  norm_num [paritySignZ]
  all_goals decide

lemma parityMatZ_12 :
    (Lorentz.SL2C.toLorentzGroup parityZ).1 (Sum.inr 0) (Sum.inr 1) = 0 := by
  rw [toLorentzGroup_parityZ]
  norm_num [paritySignZ]
  all_goals decide

lemma parityMatZ_13 :
    (Lorentz.SL2C.toLorentzGroup parityZ).1 (Sum.inr 0) (Sum.inr 2) = 0 := by
  rw [toLorentzGroup_parityZ]
  norm_num [paritySignZ]
  all_goals decide

lemma parityMatZ_20 :
    (Lorentz.SL2C.toLorentzGroup parityZ).1 (Sum.inr 1) (Sum.inl 0) = 0 := by
  rw [toLorentzGroup_parityZ]
  norm_num [paritySignZ]
  all_goals decide

lemma parityMatZ_21 :
    (Lorentz.SL2C.toLorentzGroup parityZ).1 (Sum.inr 1) (Sum.inr 0) = 0 := by
  rw [toLorentzGroup_parityZ]
  norm_num [paritySignZ]
  all_goals decide

lemma parityMatZ_22 :
    (Lorentz.SL2C.toLorentzGroup parityZ).1 (Sum.inr 1) (Sum.inr 1) = -1 := by
  rw [toLorentzGroup_parityZ]
  norm_num [paritySignZ]
  all_goals decide

lemma parityMatZ_23 :
    (Lorentz.SL2C.toLorentzGroup parityZ).1 (Sum.inr 1) (Sum.inr 2) = 0 := by
  rw [toLorentzGroup_parityZ]
  norm_num [paritySignZ]
  all_goals decide

lemma parityMatZ_30 :
    (Lorentz.SL2C.toLorentzGroup parityZ).1 (Sum.inr 2) (Sum.inl 0) = 0 := by
  rw [toLorentzGroup_parityZ]
  norm_num [paritySignZ]
  all_goals decide

lemma parityMatZ_31 :
    (Lorentz.SL2C.toLorentzGroup parityZ).1 (Sum.inr 2) (Sum.inr 0) = 0 := by
  rw [toLorentzGroup_parityZ]
  norm_num [paritySignZ]
  all_goals decide

lemma parityMatZ_32 :
    (Lorentz.SL2C.toLorentzGroup parityZ).1 (Sum.inr 2) (Sum.inr 1) = 0 := by
  rw [toLorentzGroup_parityZ]
  norm_num [paritySignZ]
  all_goals decide

lemma parityMatZ_33 :
    (Lorentz.SL2C.toLorentzGroup parityZ).1 (Sum.inr 2) (Sum.inr 2) = 1 := by
  rw [toLorentzGroup_parityZ]
  norm_num [paritySignZ]
  all_goals decide

/-- Entries of the Lorentz matrix of `parityX`. -/
lemma parityMatX_00 :
    (Lorentz.SL2C.toLorentzGroup parityX).1 (Sum.inl 0) (Sum.inl 0) = 1 := by
  rw [toLorentzGroup_parityX]
  norm_num [paritySignX]
  all_goals decide

lemma parityMatX_01 :
    (Lorentz.SL2C.toLorentzGroup parityX).1 (Sum.inl 0) (Sum.inr 0) = 0 := by
  rw [toLorentzGroup_parityX]
  norm_num [paritySignX]
  all_goals decide

lemma parityMatX_02 :
    (Lorentz.SL2C.toLorentzGroup parityX).1 (Sum.inl 0) (Sum.inr 1) = 0 := by
  rw [toLorentzGroup_parityX]
  norm_num [paritySignX]
  all_goals decide

lemma parityMatX_03 :
    (Lorentz.SL2C.toLorentzGroup parityX).1 (Sum.inl 0) (Sum.inr 2) = 0 := by
  rw [toLorentzGroup_parityX]
  norm_num [paritySignX]
  all_goals decide

lemma parityMatX_10 :
    (Lorentz.SL2C.toLorentzGroup parityX).1 (Sum.inr 0) (Sum.inl 0) = 0 := by
  rw [toLorentzGroup_parityX]
  norm_num [paritySignX]
  all_goals decide

lemma parityMatX_11 :
    (Lorentz.SL2C.toLorentzGroup parityX).1 (Sum.inr 0) (Sum.inr 0) = 1 := by
  rw [toLorentzGroup_parityX]
  norm_num [paritySignX]
  all_goals decide

lemma parityMatX_12 :
    (Lorentz.SL2C.toLorentzGroup parityX).1 (Sum.inr 0) (Sum.inr 1) = 0 := by
  rw [toLorentzGroup_parityX]
  norm_num [paritySignX]
  all_goals decide

lemma parityMatX_13 :
    (Lorentz.SL2C.toLorentzGroup parityX).1 (Sum.inr 0) (Sum.inr 2) = 0 := by
  rw [toLorentzGroup_parityX]
  norm_num [paritySignX]
  all_goals decide

lemma parityMatX_20 :
    (Lorentz.SL2C.toLorentzGroup parityX).1 (Sum.inr 1) (Sum.inl 0) = 0 := by
  rw [toLorentzGroup_parityX]
  norm_num [paritySignX]
  all_goals decide

lemma parityMatX_21 :
    (Lorentz.SL2C.toLorentzGroup parityX).1 (Sum.inr 1) (Sum.inr 0) = 0 := by
  rw [toLorentzGroup_parityX]
  norm_num [paritySignX]
  all_goals decide

lemma parityMatX_22 :
    (Lorentz.SL2C.toLorentzGroup parityX).1 (Sum.inr 1) (Sum.inr 1) = -1 := by
  rw [toLorentzGroup_parityX]
  norm_num [paritySignX]
  all_goals decide

lemma parityMatX_23 :
    (Lorentz.SL2C.toLorentzGroup parityX).1 (Sum.inr 1) (Sum.inr 2) = 0 := by
  rw [toLorentzGroup_parityX]
  norm_num [paritySignX]
  all_goals decide

lemma parityMatX_30 :
    (Lorentz.SL2C.toLorentzGroup parityX).1 (Sum.inr 2) (Sum.inl 0) = 0 := by
  rw [toLorentzGroup_parityX]
  norm_num [paritySignX]
  all_goals decide

lemma parityMatX_31 :
    (Lorentz.SL2C.toLorentzGroup parityX).1 (Sum.inr 2) (Sum.inr 0) = 0 := by
  rw [toLorentzGroup_parityX]
  norm_num [paritySignX]
  all_goals decide

lemma parityMatX_32 :
    (Lorentz.SL2C.toLorentzGroup parityX).1 (Sum.inr 2) (Sum.inr 1) = 0 := by
  rw [toLorentzGroup_parityX]
  norm_num [paritySignX]
  all_goals decide

lemma parityMatX_33 :
    (Lorentz.SL2C.toLorentzGroup parityX).1 (Sum.inr 2) (Sum.inr 2) = -1 := by
  rw [toLorentzGroup_parityX]
  norm_num [paritySignX]
  all_goals decide

/-- Entries of the Lorentz matrix of `parityY`. -/
lemma parityMatY_00 :
    (Lorentz.SL2C.toLorentzGroup parityY).1 (Sum.inl 0) (Sum.inl 0) = 1 := by
  rw [toLorentzGroup_parityY]
  norm_num [paritySignY]
  all_goals decide

lemma parityMatY_01 :
    (Lorentz.SL2C.toLorentzGroup parityY).1 (Sum.inl 0) (Sum.inr 0) = 0 := by
  rw [toLorentzGroup_parityY]
  norm_num [paritySignY]
  all_goals decide

lemma parityMatY_02 :
    (Lorentz.SL2C.toLorentzGroup parityY).1 (Sum.inl 0) (Sum.inr 1) = 0 := by
  rw [toLorentzGroup_parityY]
  norm_num [paritySignY]
  all_goals decide

lemma parityMatY_03 :
    (Lorentz.SL2C.toLorentzGroup parityY).1 (Sum.inl 0) (Sum.inr 2) = 0 := by
  rw [toLorentzGroup_parityY]
  norm_num [paritySignY]
  all_goals decide

lemma parityMatY_10 :
    (Lorentz.SL2C.toLorentzGroup parityY).1 (Sum.inr 0) (Sum.inl 0) = 0 := by
  rw [toLorentzGroup_parityY]
  norm_num [paritySignY]
  all_goals decide

lemma parityMatY_11 :
    (Lorentz.SL2C.toLorentzGroup parityY).1 (Sum.inr 0) (Sum.inr 0) = -1 := by
  rw [toLorentzGroup_parityY]
  norm_num [paritySignY]
  all_goals decide

lemma parityMatY_12 :
    (Lorentz.SL2C.toLorentzGroup parityY).1 (Sum.inr 0) (Sum.inr 1) = 0 := by
  rw [toLorentzGroup_parityY]
  norm_num [paritySignY]
  all_goals decide

lemma parityMatY_13 :
    (Lorentz.SL2C.toLorentzGroup parityY).1 (Sum.inr 0) (Sum.inr 2) = 0 := by
  rw [toLorentzGroup_parityY]
  norm_num [paritySignY]
  all_goals decide

lemma parityMatY_20 :
    (Lorentz.SL2C.toLorentzGroup parityY).1 (Sum.inr 1) (Sum.inl 0) = 0 := by
  rw [toLorentzGroup_parityY]
  norm_num [paritySignY]
  all_goals decide

lemma parityMatY_21 :
    (Lorentz.SL2C.toLorentzGroup parityY).1 (Sum.inr 1) (Sum.inr 0) = 0 := by
  rw [toLorentzGroup_parityY]
  norm_num [paritySignY]
  all_goals decide

lemma parityMatY_22 :
    (Lorentz.SL2C.toLorentzGroup parityY).1 (Sum.inr 1) (Sum.inr 1) = 1 := by
  rw [toLorentzGroup_parityY]
  norm_num [paritySignY]
  all_goals decide

lemma parityMatY_23 :
    (Lorentz.SL2C.toLorentzGroup parityY).1 (Sum.inr 1) (Sum.inr 2) = 0 := by
  rw [toLorentzGroup_parityY]
  norm_num [paritySignY]
  all_goals decide

lemma parityMatY_30 :
    (Lorentz.SL2C.toLorentzGroup parityY).1 (Sum.inr 2) (Sum.inl 0) = 0 := by
  rw [toLorentzGroup_parityY]
  norm_num [paritySignY]
  all_goals decide

lemma parityMatY_31 :
    (Lorentz.SL2C.toLorentzGroup parityY).1 (Sum.inr 2) (Sum.inr 0) = 0 := by
  rw [toLorentzGroup_parityY]
  norm_num [paritySignY]
  all_goals decide

lemma parityMatY_32 :
    (Lorentz.SL2C.toLorentzGroup parityY).1 (Sum.inr 2) (Sum.inr 1) = 0 := by
  rw [toLorentzGroup_parityY]
  norm_num [paritySignY]
  all_goals decide

lemma parityMatY_33 :
    (Lorentz.SL2C.toLorentzGroup parityY).1 (Sum.inr 2) (Sum.inr 2) = -1 := by
  rw [toLorentzGroup_parityY]
  norm_num [paritySignY]
  all_goals decide

set_option maxHeartbeats 2000000 in
/-- The Klein average acts diagonally on products of two field strengths, by
  the average of the four parity signs. -/
lemma kleinAvg_fieldStrengthDeriv_nil_mul (a b c d : Fin 1 ⊕ Fin 3) :
    kleinAvg (fieldStrengthDeriv {} a b * fieldStrengthDeriv {} c d) =
      (((1 + paritySignZ a * paritySignZ b * (paritySignZ c * paritySignZ d) +
        paritySignY a * paritySignY b * (paritySignY c * paritySignY d) +
        paritySignX a * paritySignX b * (paritySignX c * paritySignX d)) / 4 : ℝ) : ℂ) •
        (fieldStrengthDeriv {} a b * fieldStrengthDeriv {} c d) := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_apply_mul,
    repLorentzGroup_diag_fieldStrengthDeriv toLorentzGroup_parityZ,
    repLorentzGroup_diag_fieldStrengthDeriv toLorentzGroup_parityY,
    repLorentzGroup_diag_fieldStrengthDeriv toLorentzGroup_parityX,
    smul_mul_smul_jet]
  push_cast
  module

/-- Under a diagonal Lorentz transformation the second-derivative field
  strength scales by the product of the signs of its four indices. -/
lemma repLorentzGroup_diag_fieldStrengthDeriv_pair {M : SL(2,ℂ)}
    {sgn : Fin 1 ⊕ Fin 3 → ℝ}
    (hM : ∀ a b, (Lorentz.SL2C.toLorentzGroup M).1 a b =
      if a = b then sgn a else 0) (ρ τ μ ν : Fin 1 ⊕ Fin 3) :
    repLorentzGroup M (fieldStrengthDeriv {ρ, τ} μ ν) =
      ((sgn ρ * (sgn τ * (sgn μ * sgn ν)) : ℝ) : ℂ) •
        fieldStrengthDeriv {ρ, τ} μ ν := by
  rw [repLorentzGroup_fieldStrengthDeriv_pair]
  rw [Finset.sum_eq_single ρ (fun r _ hr => Finset.sum_eq_zero fun s _ =>
      Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => by
        rw [hM r ρ, if_neg hr, zero_mul, Complex.ofReal_zero, zero_smul])
    (fun h => absurd (Finset.mem_univ ρ) h)]
  rw [Finset.sum_eq_single τ (fun s _ hs => Finset.sum_eq_zero fun a _ =>
      Finset.sum_eq_zero fun b _ => by
        rw [hM s τ, if_neg hs, zero_mul, mul_zero, Complex.ofReal_zero, zero_smul])
    (fun h => absurd (Finset.mem_univ τ) h)]
  rw [Finset.sum_eq_single μ (fun a _ ha => Finset.sum_eq_zero fun b _ => by
      rw [hM a μ, if_neg ha, zero_mul, mul_zero, mul_zero, Complex.ofReal_zero,
        zero_smul])
    (fun h => absurd (Finset.mem_univ μ) h)]
  rw [Finset.sum_eq_single ν (fun b _ hb => by
      rw [hM b ν, if_neg hb, mul_zero, mul_zero, mul_zero, Complex.ofReal_zero,
        zero_smul])
    (fun h => absurd (Finset.mem_univ ν) h)]
  rw [hM ρ ρ, if_pos rfl, hM τ τ, if_pos rfl, hM μ μ, if_pos rfl, hM ν ν,
    if_pos rfl]

/-- The Klein average acts diagonally on the second-derivative field
  strengths. -/
lemma kleinAvg_fieldStrengthDeriv_pair (r t a b : Fin 1 ⊕ Fin 3) :
    kleinAvg (fieldStrengthDeriv {r, t} a b) =
      (((1 + paritySignZ r * (paritySignZ t * (paritySignZ a * paritySignZ b)) +
        paritySignY r * (paritySignY t * (paritySignY a * paritySignY b)) +
        paritySignX r * (paritySignX t * (paritySignX a * paritySignX b))) / 4 : ℝ) : ℂ) •
        fieldStrengthDeriv {r, t} a b := by
  rw [kleinAvg_apply,
    repLorentzGroup_diag_fieldStrengthDeriv_pair toLorentzGroup_parityZ,
    repLorentzGroup_diag_fieldStrengthDeriv_pair toLorentzGroup_parityY,
    repLorentzGroup_diag_fieldStrengthDeriv_pair toLorentzGroup_parityX]
  push_cast
  module

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[0,0,0]` (u-family). -/
lemma kleinAvg_u_e000 :
    kleinAvg (Dbarψ [] 0 * Dψ [Sum.inl 0] 0) =
      (1/2 : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11, parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23, parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01, parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13, parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31, parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03, parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21, parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 : JetAlgebra) = X0, (Dbarψ [] 1 * Dψ [Sum.inl 0] 1 : JetAlgebra) = X1, (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 : JetAlgebra) = X2, (Dbarψ [] 1 * Dψ [Sum.inr 0] 0 : JetAlgebra) = X3, (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 : JetAlgebra) = X4, (Dbarψ [] 1 * Dψ [Sum.inr 1] 0 : JetAlgebra) = X5, (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 : JetAlgebra) = X6, (Dbarψ [] 1 * Dψ [Sum.inr 2] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[0,0,1]` (u-family). -/
lemma kleinAvg_u_e001 :
    kleinAvg (Dbarψ [] 0 * Dψ [Sum.inl 0] 1) =
      0 := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11, parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23, parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01, parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13, parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31, parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03, parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21, parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 : JetAlgebra) = X0, (Dbarψ [] 1 * Dψ [Sum.inl 0] 1 : JetAlgebra) = X1, (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 : JetAlgebra) = X2, (Dbarψ [] 1 * Dψ [Sum.inr 0] 0 : JetAlgebra) = X3, (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 : JetAlgebra) = X4, (Dbarψ [] 1 * Dψ [Sum.inr 1] 0 : JetAlgebra) = X5, (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 : JetAlgebra) = X6, (Dbarψ [] 1 * Dψ [Sum.inr 2] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[0,1,0]` (u-family). -/
lemma kleinAvg_u_e010 :
    kleinAvg (Dbarψ [] 1 * Dψ [Sum.inl 0] 0) =
      0 := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11, parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23, parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01, parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13, parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31, parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03, parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21, parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 : JetAlgebra) = X0, (Dbarψ [] 1 * Dψ [Sum.inl 0] 1 : JetAlgebra) = X1, (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 : JetAlgebra) = X2, (Dbarψ [] 1 * Dψ [Sum.inr 0] 0 : JetAlgebra) = X3, (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 : JetAlgebra) = X4, (Dbarψ [] 1 * Dψ [Sum.inr 1] 0 : JetAlgebra) = X5, (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 : JetAlgebra) = X6, (Dbarψ [] 1 * Dψ [Sum.inr 2] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[0,1,1]` (u-family). -/
lemma kleinAvg_u_e011 :
    kleinAvg (Dbarψ [] 1 * Dψ [Sum.inl 0] 1) =
      (1/2 : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1) := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11, parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23, parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01, parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13, parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31, parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03, parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21, parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 : JetAlgebra) = X0, (Dbarψ [] 1 * Dψ [Sum.inl 0] 1 : JetAlgebra) = X1, (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 : JetAlgebra) = X2, (Dbarψ [] 1 * Dψ [Sum.inr 0] 0 : JetAlgebra) = X3, (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 : JetAlgebra) = X4, (Dbarψ [] 1 * Dψ [Sum.inr 1] 0 : JetAlgebra) = X5, (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 : JetAlgebra) = X6, (Dbarψ [] 1 * Dψ [Sum.inr 2] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[1,0,0]` (u-family). -/
lemma kleinAvg_u_e100 :
    kleinAvg (Dbarψ [] 0 * Dψ [Sum.inr 0] 0) =
      0 := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11, parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23, parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01, parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13, parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31, parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03, parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21, parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 : JetAlgebra) = X0, (Dbarψ [] 1 * Dψ [Sum.inl 0] 1 : JetAlgebra) = X1, (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 : JetAlgebra) = X2, (Dbarψ [] 1 * Dψ [Sum.inr 0] 0 : JetAlgebra) = X3, (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 : JetAlgebra) = X4, (Dbarψ [] 1 * Dψ [Sum.inr 1] 0 : JetAlgebra) = X5, (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 : JetAlgebra) = X6, (Dbarψ [] 1 * Dψ [Sum.inr 2] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[1,0,1]` (u-family). -/
lemma kleinAvg_u_e101 :
    kleinAvg (Dbarψ [] 0 * Dψ [Sum.inr 0] 1) =
      (1/2 : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0) := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11, parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23, parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01, parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13, parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31, parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03, parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21, parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 : JetAlgebra) = X0, (Dbarψ [] 1 * Dψ [Sum.inl 0] 1 : JetAlgebra) = X1, (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 : JetAlgebra) = X2, (Dbarψ [] 1 * Dψ [Sum.inr 0] 0 : JetAlgebra) = X3, (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 : JetAlgebra) = X4, (Dbarψ [] 1 * Dψ [Sum.inr 1] 0 : JetAlgebra) = X5, (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 : JetAlgebra) = X6, (Dbarψ [] 1 * Dψ [Sum.inr 2] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[1,1,0]` (u-family). -/
lemma kleinAvg_u_e110 :
    kleinAvg (Dbarψ [] 1 * Dψ [Sum.inr 0] 0) =
      (1/2 : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0) := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11, parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23, parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01, parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13, parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31, parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03, parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21, parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 : JetAlgebra) = X0, (Dbarψ [] 1 * Dψ [Sum.inl 0] 1 : JetAlgebra) = X1, (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 : JetAlgebra) = X2, (Dbarψ [] 1 * Dψ [Sum.inr 0] 0 : JetAlgebra) = X3, (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 : JetAlgebra) = X4, (Dbarψ [] 1 * Dψ [Sum.inr 1] 0 : JetAlgebra) = X5, (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 : JetAlgebra) = X6, (Dbarψ [] 1 * Dψ [Sum.inr 2] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[1,1,1]` (u-family). -/
lemma kleinAvg_u_e111 :
    kleinAvg (Dbarψ [] 1 * Dψ [Sum.inr 0] 1) =
      0 := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11, parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23, parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01, parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13, parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31, parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03, parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21, parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 : JetAlgebra) = X0, (Dbarψ [] 1 * Dψ [Sum.inl 0] 1 : JetAlgebra) = X1, (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 : JetAlgebra) = X2, (Dbarψ [] 1 * Dψ [Sum.inr 0] 0 : JetAlgebra) = X3, (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 : JetAlgebra) = X4, (Dbarψ [] 1 * Dψ [Sum.inr 1] 0 : JetAlgebra) = X5, (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 : JetAlgebra) = X6, (Dbarψ [] 1 * Dψ [Sum.inr 2] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[2,0,0]` (u-family). -/
lemma kleinAvg_u_e200 :
    kleinAvg (Dbarψ [] 0 * Dψ [Sum.inr 1] 0) =
      0 := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11, parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23, parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01, parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13, parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31, parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03, parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21, parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 : JetAlgebra) = X0, (Dbarψ [] 1 * Dψ [Sum.inl 0] 1 : JetAlgebra) = X1, (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 : JetAlgebra) = X2, (Dbarψ [] 1 * Dψ [Sum.inr 0] 0 : JetAlgebra) = X3, (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 : JetAlgebra) = X4, (Dbarψ [] 1 * Dψ [Sum.inr 1] 0 : JetAlgebra) = X5, (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 : JetAlgebra) = X6, (Dbarψ [] 1 * Dψ [Sum.inr 2] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[2,0,1]` (u-family). -/
lemma kleinAvg_u_e201 :
    kleinAvg (Dbarψ [] 0 * Dψ [Sum.inr 1] 1) =
      (1/2 : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0) := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11, parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23, parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01, parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13, parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31, parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03, parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21, parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 : JetAlgebra) = X0, (Dbarψ [] 1 * Dψ [Sum.inl 0] 1 : JetAlgebra) = X1, (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 : JetAlgebra) = X2, (Dbarψ [] 1 * Dψ [Sum.inr 0] 0 : JetAlgebra) = X3, (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 : JetAlgebra) = X4, (Dbarψ [] 1 * Dψ [Sum.inr 1] 0 : JetAlgebra) = X5, (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 : JetAlgebra) = X6, (Dbarψ [] 1 * Dψ [Sum.inr 2] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[2,1,0]` (u-family). -/
lemma kleinAvg_u_e210 :
    kleinAvg (Dbarψ [] 1 * Dψ [Sum.inr 1] 0) =
      (-(1/2) : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0) := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11, parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23, parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01, parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13, parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31, parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03, parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21, parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 : JetAlgebra) = X0, (Dbarψ [] 1 * Dψ [Sum.inl 0] 1 : JetAlgebra) = X1, (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 : JetAlgebra) = X2, (Dbarψ [] 1 * Dψ [Sum.inr 0] 0 : JetAlgebra) = X3, (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 : JetAlgebra) = X4, (Dbarψ [] 1 * Dψ [Sum.inr 1] 0 : JetAlgebra) = X5, (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 : JetAlgebra) = X6, (Dbarψ [] 1 * Dψ [Sum.inr 2] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[2,1,1]` (u-family). -/
lemma kleinAvg_u_e211 :
    kleinAvg (Dbarψ [] 1 * Dψ [Sum.inr 1] 1) =
      0 := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11, parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23, parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01, parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13, parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31, parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03, parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21, parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 : JetAlgebra) = X0, (Dbarψ [] 1 * Dψ [Sum.inl 0] 1 : JetAlgebra) = X1, (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 : JetAlgebra) = X2, (Dbarψ [] 1 * Dψ [Sum.inr 0] 0 : JetAlgebra) = X3, (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 : JetAlgebra) = X4, (Dbarψ [] 1 * Dψ [Sum.inr 1] 0 : JetAlgebra) = X5, (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 : JetAlgebra) = X6, (Dbarψ [] 1 * Dψ [Sum.inr 2] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[3,0,0]` (u-family). -/
lemma kleinAvg_u_e300 :
    kleinAvg (Dbarψ [] 0 * Dψ [Sum.inr 2] 0) =
      (1/2 : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11, parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23, parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01, parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13, parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31, parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03, parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21, parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 : JetAlgebra) = X0, (Dbarψ [] 1 * Dψ [Sum.inl 0] 1 : JetAlgebra) = X1, (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 : JetAlgebra) = X2, (Dbarψ [] 1 * Dψ [Sum.inr 0] 0 : JetAlgebra) = X3, (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 : JetAlgebra) = X4, (Dbarψ [] 1 * Dψ [Sum.inr 1] 0 : JetAlgebra) = X5, (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 : JetAlgebra) = X6, (Dbarψ [] 1 * Dψ [Sum.inr 2] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[3,0,1]` (u-family). -/
lemma kleinAvg_u_e301 :
    kleinAvg (Dbarψ [] 0 * Dψ [Sum.inr 2] 1) =
      0 := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11, parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23, parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01, parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13, parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31, parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03, parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21, parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 : JetAlgebra) = X0, (Dbarψ [] 1 * Dψ [Sum.inl 0] 1 : JetAlgebra) = X1, (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 : JetAlgebra) = X2, (Dbarψ [] 1 * Dψ [Sum.inr 0] 0 : JetAlgebra) = X3, (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 : JetAlgebra) = X4, (Dbarψ [] 1 * Dψ [Sum.inr 1] 0 : JetAlgebra) = X5, (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 : JetAlgebra) = X6, (Dbarψ [] 1 * Dψ [Sum.inr 2] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[3,1,0]` (u-family). -/
lemma kleinAvg_u_e310 :
    kleinAvg (Dbarψ [] 1 * Dψ [Sum.inr 2] 0) =
      0 := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11, parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23, parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01, parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13, parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31, parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03, parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21, parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 : JetAlgebra) = X0, (Dbarψ [] 1 * Dψ [Sum.inl 0] 1 : JetAlgebra) = X1, (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 : JetAlgebra) = X2, (Dbarψ [] 1 * Dψ [Sum.inr 0] 0 : JetAlgebra) = X3, (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 : JetAlgebra) = X4, (Dbarψ [] 1 * Dψ [Sum.inr 1] 0 : JetAlgebra) = X5, (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 : JetAlgebra) = X6, (Dbarψ [] 1 * Dψ [Sum.inr 2] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[3,1,1]` (u-family). -/
lemma kleinAvg_u_e311 :
    kleinAvg (Dbarψ [] 1 * Dψ [Sum.inr 2] 1) =
      (-(1/2) : ℂ) • (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1) := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_nil_mul_Dψ_singleton,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11, parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23, parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01, parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13, parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31, parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03, parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21, parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [] 0 * Dψ [Sum.inl 0] 0 : JetAlgebra) = X0, (Dbarψ [] 1 * Dψ [Sum.inl 0] 1 : JetAlgebra) = X1, (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 : JetAlgebra) = X2, (Dbarψ [] 1 * Dψ [Sum.inr 0] 0 : JetAlgebra) = X3, (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 : JetAlgebra) = X4, (Dbarψ [] 1 * Dψ [Sum.inr 1] 0 : JetAlgebra) = X5, (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 : JetAlgebra) = X6, (Dbarψ [] 1 * Dψ [Sum.inr 2] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[0,0,0]` (ubar-family). -/
lemma kleinAvg_ubar_e000 :
    kleinAvg (Dbarψ [Sum.inl 0] 0 * Dψ [] 0) =
      (1/2 : ℂ) • (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11, parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23, parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01, parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13, parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31, parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03, parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21, parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 : JetAlgebra) = X0, (Dbarψ [Sum.inl 0] 1 * Dψ [] 1 : JetAlgebra) = X1, (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 : JetAlgebra) = X2, (Dbarψ [Sum.inr 0] 1 * Dψ [] 0 : JetAlgebra) = X3, (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 : JetAlgebra) = X4, (Dbarψ [Sum.inr 1] 1 * Dψ [] 0 : JetAlgebra) = X5, (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 : JetAlgebra) = X6, (Dbarψ [Sum.inr 2] 1 * Dψ [] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[0,0,1]` (ubar-family). -/
lemma kleinAvg_ubar_e001 :
    kleinAvg (Dbarψ [Sum.inl 0] 0 * Dψ [] 1) =
      0 := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11, parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23, parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01, parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13, parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31, parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03, parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21, parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 : JetAlgebra) = X0, (Dbarψ [Sum.inl 0] 1 * Dψ [] 1 : JetAlgebra) = X1, (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 : JetAlgebra) = X2, (Dbarψ [Sum.inr 0] 1 * Dψ [] 0 : JetAlgebra) = X3, (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 : JetAlgebra) = X4, (Dbarψ [Sum.inr 1] 1 * Dψ [] 0 : JetAlgebra) = X5, (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 : JetAlgebra) = X6, (Dbarψ [Sum.inr 2] 1 * Dψ [] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[0,1,0]` (ubar-family). -/
lemma kleinAvg_ubar_e010 :
    kleinAvg (Dbarψ [Sum.inl 0] 1 * Dψ [] 0) =
      0 := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11, parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23, parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01, parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13, parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31, parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03, parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21, parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 : JetAlgebra) = X0, (Dbarψ [Sum.inl 0] 1 * Dψ [] 1 : JetAlgebra) = X1, (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 : JetAlgebra) = X2, (Dbarψ [Sum.inr 0] 1 * Dψ [] 0 : JetAlgebra) = X3, (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 : JetAlgebra) = X4, (Dbarψ [Sum.inr 1] 1 * Dψ [] 0 : JetAlgebra) = X5, (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 : JetAlgebra) = X6, (Dbarψ [Sum.inr 2] 1 * Dψ [] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[0,1,1]` (ubar-family). -/
lemma kleinAvg_ubar_e011 :
    kleinAvg (Dbarψ [Sum.inl 0] 1 * Dψ [] 1) =
      (1/2 : ℂ) • (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1) := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11, parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23, parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01, parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13, parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31, parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03, parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21, parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 : JetAlgebra) = X0, (Dbarψ [Sum.inl 0] 1 * Dψ [] 1 : JetAlgebra) = X1, (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 : JetAlgebra) = X2, (Dbarψ [Sum.inr 0] 1 * Dψ [] 0 : JetAlgebra) = X3, (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 : JetAlgebra) = X4, (Dbarψ [Sum.inr 1] 1 * Dψ [] 0 : JetAlgebra) = X5, (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 : JetAlgebra) = X6, (Dbarψ [Sum.inr 2] 1 * Dψ [] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[1,0,0]` (ubar-family). -/
lemma kleinAvg_ubar_e100 :
    kleinAvg (Dbarψ [Sum.inr 0] 0 * Dψ [] 0) =
      0 := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11, parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23, parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01, parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13, parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31, parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03, parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21, parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 : JetAlgebra) = X0, (Dbarψ [Sum.inl 0] 1 * Dψ [] 1 : JetAlgebra) = X1, (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 : JetAlgebra) = X2, (Dbarψ [Sum.inr 0] 1 * Dψ [] 0 : JetAlgebra) = X3, (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 : JetAlgebra) = X4, (Dbarψ [Sum.inr 1] 1 * Dψ [] 0 : JetAlgebra) = X5, (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 : JetAlgebra) = X6, (Dbarψ [Sum.inr 2] 1 * Dψ [] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[1,0,1]` (ubar-family). -/
lemma kleinAvg_ubar_e101 :
    kleinAvg (Dbarψ [Sum.inr 0] 0 * Dψ [] 1) =
      (1/2 : ℂ) • (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0) := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11, parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23, parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01, parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13, parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31, parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03, parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21, parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 : JetAlgebra) = X0, (Dbarψ [Sum.inl 0] 1 * Dψ [] 1 : JetAlgebra) = X1, (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 : JetAlgebra) = X2, (Dbarψ [Sum.inr 0] 1 * Dψ [] 0 : JetAlgebra) = X3, (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 : JetAlgebra) = X4, (Dbarψ [Sum.inr 1] 1 * Dψ [] 0 : JetAlgebra) = X5, (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 : JetAlgebra) = X6, (Dbarψ [Sum.inr 2] 1 * Dψ [] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[1,1,0]` (ubar-family). -/
lemma kleinAvg_ubar_e110 :
    kleinAvg (Dbarψ [Sum.inr 0] 1 * Dψ [] 0) =
      (1/2 : ℂ) • (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0) := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11, parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23, parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01, parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13, parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31, parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03, parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21, parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 : JetAlgebra) = X0, (Dbarψ [Sum.inl 0] 1 * Dψ [] 1 : JetAlgebra) = X1, (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 : JetAlgebra) = X2, (Dbarψ [Sum.inr 0] 1 * Dψ [] 0 : JetAlgebra) = X3, (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 : JetAlgebra) = X4, (Dbarψ [Sum.inr 1] 1 * Dψ [] 0 : JetAlgebra) = X5, (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 : JetAlgebra) = X6, (Dbarψ [Sum.inr 2] 1 * Dψ [] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[1,1,1]` (ubar-family). -/
lemma kleinAvg_ubar_e111 :
    kleinAvg (Dbarψ [Sum.inr 0] 1 * Dψ [] 1) =
      0 := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11, parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23, parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01, parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13, parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31, parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03, parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21, parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 : JetAlgebra) = X0, (Dbarψ [Sum.inl 0] 1 * Dψ [] 1 : JetAlgebra) = X1, (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 : JetAlgebra) = X2, (Dbarψ [Sum.inr 0] 1 * Dψ [] 0 : JetAlgebra) = X3, (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 : JetAlgebra) = X4, (Dbarψ [Sum.inr 1] 1 * Dψ [] 0 : JetAlgebra) = X5, (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 : JetAlgebra) = X6, (Dbarψ [Sum.inr 2] 1 * Dψ [] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[2,0,0]` (ubar-family). -/
lemma kleinAvg_ubar_e200 :
    kleinAvg (Dbarψ [Sum.inr 1] 0 * Dψ [] 0) =
      0 := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11, parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23, parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01, parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13, parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31, parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03, parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21, parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 : JetAlgebra) = X0, (Dbarψ [Sum.inl 0] 1 * Dψ [] 1 : JetAlgebra) = X1, (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 : JetAlgebra) = X2, (Dbarψ [Sum.inr 0] 1 * Dψ [] 0 : JetAlgebra) = X3, (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 : JetAlgebra) = X4, (Dbarψ [Sum.inr 1] 1 * Dψ [] 0 : JetAlgebra) = X5, (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 : JetAlgebra) = X6, (Dbarψ [Sum.inr 2] 1 * Dψ [] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[2,0,1]` (ubar-family). -/
lemma kleinAvg_ubar_e201 :
    kleinAvg (Dbarψ [Sum.inr 1] 0 * Dψ [] 1) =
      (1/2 : ℂ) • (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0) := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11, parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23, parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01, parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13, parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31, parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03, parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21, parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 : JetAlgebra) = X0, (Dbarψ [Sum.inl 0] 1 * Dψ [] 1 : JetAlgebra) = X1, (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 : JetAlgebra) = X2, (Dbarψ [Sum.inr 0] 1 * Dψ [] 0 : JetAlgebra) = X3, (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 : JetAlgebra) = X4, (Dbarψ [Sum.inr 1] 1 * Dψ [] 0 : JetAlgebra) = X5, (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 : JetAlgebra) = X6, (Dbarψ [Sum.inr 2] 1 * Dψ [] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[2,1,0]` (ubar-family). -/
lemma kleinAvg_ubar_e210 :
    kleinAvg (Dbarψ [Sum.inr 1] 1 * Dψ [] 0) =
      (-(1/2) : ℂ) • (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0) := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11, parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23, parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01, parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13, parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31, parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03, parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21, parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 : JetAlgebra) = X0, (Dbarψ [Sum.inl 0] 1 * Dψ [] 1 : JetAlgebra) = X1, (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 : JetAlgebra) = X2, (Dbarψ [Sum.inr 0] 1 * Dψ [] 0 : JetAlgebra) = X3, (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 : JetAlgebra) = X4, (Dbarψ [Sum.inr 1] 1 * Dψ [] 0 : JetAlgebra) = X5, (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 : JetAlgebra) = X6, (Dbarψ [Sum.inr 2] 1 * Dψ [] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[2,1,1]` (ubar-family). -/
lemma kleinAvg_ubar_e211 :
    kleinAvg (Dbarψ [Sum.inr 1] 1 * Dψ [] 1) =
      0 := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11, parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23, parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01, parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13, parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31, parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03, parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21, parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 : JetAlgebra) = X0, (Dbarψ [Sum.inl 0] 1 * Dψ [] 1 : JetAlgebra) = X1, (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 : JetAlgebra) = X2, (Dbarψ [Sum.inr 0] 1 * Dψ [] 0 : JetAlgebra) = X3, (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 : JetAlgebra) = X4, (Dbarψ [Sum.inr 1] 1 * Dψ [] 0 : JetAlgebra) = X5, (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 : JetAlgebra) = X6, (Dbarψ [Sum.inr 2] 1 * Dψ [] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[3,0,0]` (ubar-family). -/
lemma kleinAvg_ubar_e300 :
    kleinAvg (Dbarψ [Sum.inr 2] 0 * Dψ [] 0) =
      (1/2 : ℂ) • (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11, parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23, parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01, parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13, parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31, parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03, parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21, parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 : JetAlgebra) = X0, (Dbarψ [Sum.inl 0] 1 * Dψ [] 1 : JetAlgebra) = X1, (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 : JetAlgebra) = X2, (Dbarψ [Sum.inr 0] 1 * Dψ [] 0 : JetAlgebra) = X3, (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 : JetAlgebra) = X4, (Dbarψ [Sum.inr 1] 1 * Dψ [] 0 : JetAlgebra) = X5, (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 : JetAlgebra) = X6, (Dbarψ [Sum.inr 2] 1 * Dψ [] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[3,0,1]` (ubar-family). -/
lemma kleinAvg_ubar_e301 :
    kleinAvg (Dbarψ [Sum.inr 2] 0 * Dψ [] 1) =
      0 := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11, parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23, parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01, parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13, parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31, parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03, parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21, parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 : JetAlgebra) = X0, (Dbarψ [Sum.inl 0] 1 * Dψ [] 1 : JetAlgebra) = X1, (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 : JetAlgebra) = X2, (Dbarψ [Sum.inr 0] 1 * Dψ [] 0 : JetAlgebra) = X3, (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 : JetAlgebra) = X4, (Dbarψ [Sum.inr 1] 1 * Dψ [] 0 : JetAlgebra) = X5, (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 : JetAlgebra) = X6, (Dbarψ [Sum.inr 2] 1 * Dψ [] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[3,1,0]` (ubar-family). -/
lemma kleinAvg_ubar_e310 :
    kleinAvg (Dbarψ [Sum.inr 2] 1 * Dψ [] 0) =
      0 := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11, parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23, parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01, parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13, parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31, parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03, parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21, parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 : JetAlgebra) = X0, (Dbarψ [Sum.inl 0] 1 * Dψ [] 1 : JetAlgebra) = X1, (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 : JetAlgebra) = X2, (Dbarψ [Sum.inr 0] 1 * Dψ [] 0 : JetAlgebra) = X3, (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 : JetAlgebra) = X4, (Dbarψ [Sum.inr 1] 1 * Dψ [] 0 : JetAlgebra) = X5, (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 : JetAlgebra) = X6, (Dbarψ [Sum.inr 2] 1 * Dψ [] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

set_option maxHeartbeats 4000000 in
/-- The Klein average of the fermion pair monomial `e[3,1,1]` (ubar-family). -/
lemma kleinAvg_ubar_e311 :
    kleinAvg (Dbarψ [Sum.inr 2] 1 * Dψ [] 1) =
      (-(1/2) : ℂ) • (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1) := by
  rw [kleinAvg_apply]
  simp only [repLorentzGroup_Dbarψ_singleton_mul_Dψ_nil,
    parityZ_inv_coe, parityY_inv_coe, parityX_inv_coe,
    parityMatZ_00, parityMatZ_01, parityMatZ_02, parityMatZ_03, parityMatZ_10, parityMatZ_11, parityMatZ_12, parityMatZ_13, parityMatZ_20, parityMatZ_21, parityMatZ_22, parityMatZ_23, parityMatZ_30, parityMatZ_31, parityMatZ_32, parityMatZ_33, parityMatX_00, parityMatX_01, parityMatX_02, parityMatX_03, parityMatX_10, parityMatX_11, parityMatX_12, parityMatX_13, parityMatX_20, parityMatX_21, parityMatX_22, parityMatX_23, parityMatX_30, parityMatX_31, parityMatX_32, parityMatX_33, parityMatY_00, parityMatY_01, parityMatY_02, parityMatY_03, parityMatY_10, parityMatY_11, parityMatY_12, parityMatY_13, parityMatY_20, parityMatY_21, parityMatY_22, parityMatY_23, parityMatY_30, parityMatY_31, parityMatY_32, parityMatY_33,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
    Complex.star_def, map_zero, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, star_zero, star_neg, star_one,
    mul_zero, zero_mul, mul_one, one_mul, neg_mul, mul_neg, neg_neg,
    Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
    zero_smul, smul_zero, smul_neg, neg_smul, add_zero, zero_add, neg_zero,
    Complex.I_mul_I]
  generalize (Dbarψ [Sum.inl 0] 0 * Dψ [] 0 : JetAlgebra) = X0, (Dbarψ [Sum.inl 0] 1 * Dψ [] 1 : JetAlgebra) = X1, (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 : JetAlgebra) = X2, (Dbarψ [Sum.inr 0] 1 * Dψ [] 0 : JetAlgebra) = X3, (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 : JetAlgebra) = X4, (Dbarψ [Sum.inr 1] 1 * Dψ [] 0 : JetAlgebra) = X5, (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 : JetAlgebra) = X6, (Dbarψ [Sum.inr 2] 1 * Dψ [] 1 : JetAlgebra) = X7
  match_scalars <;> (try norm_num; try ring_nf; try norm_num [Complex.I_sq])

/-- The Maxwell term lies in the span of the invariants. -/
lemma maxwellTerm_mem_span :
    maxwellTerm ∈ Submodule.span ℂ massDimFourInvariants :=
  Submodule.subset_span (by simp [massDimFourInvariants])

/-- The theta term lies in the span of the invariants. -/
lemma thetaTerm_mem_span :
    thetaTerm ∈ Submodule.span ℂ massDimFourInvariants :=
  Submodule.subset_span (by simp [massDimFourInvariants])

/-- The fermion kinetic term lies in the span of the invariants. -/
lemma fermionKineticTerm_mem_span :
    fermionKineticTerm ∈ Submodule.span ℂ massDimFourInvariants :=
  Submodule.subset_span (by simp [massDimFourInvariants])

/-- The conjugate fermion kinetic term lies in the span of the invariants. -/
lemma fermionKineticTermBar_mem_span :
    fermionKineticTermBar ∈ Submodule.span ℂ massDimFourInvariants :=
  Submodule.subset_span (by simp [massDimFourInvariants])

/-- Projector membership for the ordered square `F01 * F01`. -/
lemma opPi_FF_c0101_mem :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_F01_F01]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered square `F01 * F10`. -/
lemma opPi_FF_c0110_mem :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [opPi_F01_F01]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F10 * F01`. -/
lemma opPi_FF_c1001_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [opPi_F01_F01]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F10 * F10`. -/
lemma opPi_FF_c1010_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [opPi_F01_F01]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered square `F01 * F23`. -/
lemma opPi_FF_c0123_mem :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_F01_F23]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F01 * F32`. -/
lemma opPi_FF_c0132_mem :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) =
        -(fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [opPi_F01_F23]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F10 * F23`. -/
lemma opPi_FF_c1023_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [opPi_F01_F23]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F10 * F32`. -/
lemma opPi_FF_c1032_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) from fieldStrengthDeriv_antisymm {} _ _,
    show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) =
        -(fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [opPi_F01_F23]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F23 * F01`. -/
lemma opPi_FF_c2301_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_mul_comm]
  rw [opPi_F01_F23]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F23 * F10`. -/
lemma opPi_FF_c2310_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [fieldStrengthDeriv_mul_comm]
  rw [opPi_F01_F23]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F32 * F01`. -/
lemma opPi_FF_c3201_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) =
        -(fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [fieldStrengthDeriv_mul_comm]
  rw [opPi_F01_F23]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F32 * F10`. -/
lemma opPi_FF_c3210_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) =
        -(fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [fieldStrengthDeriv_mul_comm]
  rw [opPi_F01_F23]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F23 * F23`. -/
lemma opPi_FF_c2323_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_F23_F23]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered square `F23 * F32`. -/
lemma opPi_FF_c2332_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) =
        -(fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [opPi_F23_F23]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F32 * F23`. -/
lemma opPi_FF_c3223_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) =
        -(fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [opPi_F23_F23]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F32 * F32`. -/
lemma opPi_FF_c3232_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) =
        -(fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [opPi_F23_F23]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered square `F02 * F02`. -/
lemma opPi_FF_c0202_mem :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_F02_F02]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered square `F02 * F20`. -/
lemma opPi_FF_c0220_mem :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [opPi_F02_F02]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F20 * F02`. -/
lemma opPi_FF_c2002_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [opPi_F02_F02]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F20 * F20`. -/
lemma opPi_FF_c2020_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [opPi_F02_F02]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered square `F02 * F13`. -/
lemma opPi_FF_c0213_mem :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_F02_F13]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F02 * F31`. -/
lemma opPi_FF_c0231_mem :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [opPi_F02_F13]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F20 * F13`. -/
lemma opPi_FF_c2013_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [opPi_F02_F13]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F20 * F31`. -/
lemma opPi_FF_c2031_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [opPi_F02_F13]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F13 * F02`. -/
lemma opPi_FF_c1302_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_mul_comm]
  rw [opPi_F02_F13]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F13 * F20`. -/
lemma opPi_FF_c1320_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [fieldStrengthDeriv_mul_comm]
  rw [opPi_F02_F13]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F31 * F02`. -/
lemma opPi_FF_c3102_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [fieldStrengthDeriv_mul_comm]
  rw [opPi_F02_F13]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F31 * F20`. -/
lemma opPi_FF_c3120_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [fieldStrengthDeriv_mul_comm]
  rw [opPi_F02_F13]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F13 * F13`. -/
lemma opPi_FF_c1313_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_F13_F13]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered square `F13 * F31`. -/
lemma opPi_FF_c1331_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [opPi_F13_F13]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F31 * F13`. -/
lemma opPi_FF_c3113_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [opPi_F13_F13]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F31 * F31`. -/
lemma opPi_FF_c3131_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [opPi_F13_F13]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered square `F03 * F03`. -/
lemma opPi_FF_c0303_mem :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_F03_F03]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered square `F03 * F30`. -/
lemma opPi_FF_c0330_mem :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [opPi_F03_F03]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F30 * F03`. -/
lemma opPi_FF_c3003_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [opPi_F03_F03]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F30 * F30`. -/
lemma opPi_FF_c3030_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [opPi_F03_F03]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered square `F03 * F12`. -/
lemma opPi_FF_c0312_mem :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_F03_F12]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F03 * F21`. -/
lemma opPi_FF_c0321_mem :
    opPi (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [opPi_F03_F12]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F30 * F12`. -/
lemma opPi_FF_c3012_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [opPi_F03_F12]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F30 * F21`. -/
lemma opPi_FF_c3021_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [opPi_F03_F12]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F12 * F03`. -/
lemma opPi_FF_c1203_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_mul_comm]
  rw [opPi_F03_F12]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F12 * F30`. -/
lemma opPi_FF_c1230_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [fieldStrengthDeriv_mul_comm]
  rw [opPi_F03_F12]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F21 * F03`. -/
lemma opPi_FF_c2103_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [fieldStrengthDeriv_mul_comm]
  rw [opPi_F03_F12]
  exact neg_mem (Submodule.smul_mem _ _ thetaTerm_mem_span)

/-- Projector membership for the ordered square `F21 * F30`. -/
lemma opPi_FF_c2130_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) =
        -(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [fieldStrengthDeriv_mul_comm]
  rw [opPi_F03_F12]
  exact Submodule.smul_mem _ _ thetaTerm_mem_span

/-- Projector membership for the ordered square `F12 * F12`. -/
lemma opPi_FF_c1212_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_F12_F12]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered square `F12 * F21`. -/
lemma opPi_FF_c1221_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [opPi_F12_F12]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F21 * F12`. -/
lemma opPi_FF_c2112_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [opPi_F12_F12]
  exact neg_mem (Submodule.smul_mem _ _ maxwellTerm_mem_span)

/-- Projector membership for the ordered square `F21 * F21`. -/
lemma opPi_FF_c2121_mem :
    opPi (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  simp only [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) =
        -(fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {} _ _,
    neg_mul_jet, mul_neg_jet, neg_neg, map_neg]
  rw [opPi_F12_F12]
  exact Submodule.smul_mem _ _ maxwellTerm_mem_span

/-- Projector membership for the ordered derivative monomial `dd01 F01`. -/
lemma opPi_DDF_c0101_mem :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_dd01_F01]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd01 F10`. -/
lemma opPi_DDF_c0110_mem :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 0) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 0) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) from fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 0} _ _]
  rw [map_neg, opPi_dd01_F01, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd10 F01`. -/
lemma opPi_DDF_c1001_mem :
    opPi (fieldStrengthDeriv {Sum.inr 0, Sum.inl 0} (Sum.inl 0) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 0) (Sum.inl 0)]
  rw [opPi_dd01_F01]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd10 F10`. -/
lemma opPi_DDF_c1010_mem :
    opPi (fieldStrengthDeriv {Sum.inr 0, Sum.inl 0} (Sum.inr 0) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 0) (Sum.inl 0)]
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 0) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inl 0) (Sum.inr 0)) from fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 0} _ _]
  rw [map_neg, opPi_dd01_F01, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd01 F23`. -/
lemma opPi_DDF_c0123_mem :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_dd01_F23]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd01 F32`. -/
lemma opPi_DDF_c0132_mem :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 2) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 2) (Sum.inr 1) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 0} _ _]
  rw [map_neg, opPi_dd01_F23, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd10 F23`. -/
lemma opPi_DDF_c1023_mem :
    opPi (fieldStrengthDeriv {Sum.inr 0, Sum.inl 0} (Sum.inr 1) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 0) (Sum.inl 0)]
  rw [opPi_dd01_F23]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd10 F32`. -/
lemma opPi_DDF_c1032_mem :
    opPi (fieldStrengthDeriv {Sum.inr 0, Sum.inl 0} (Sum.inr 2) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 0) (Sum.inl 0)]
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 2) (Sum.inr 1) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 0} (Sum.inr 1) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 0} _ _]
  rw [map_neg, opPi_dd01_F23, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd02 F02`. -/
lemma opPi_DDF_c0202_mem :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_dd02_F02]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd02 F20`. -/
lemma opPi_DDF_c0220_mem :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 1) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 1) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 1} _ _]
  rw [map_neg, opPi_dd02_F02, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd20 F02`. -/
lemma opPi_DDF_c2002_mem :
    opPi (fieldStrengthDeriv {Sum.inr 1, Sum.inl 0} (Sum.inl 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inl 0)]
  rw [opPi_dd02_F02]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd20 F20`. -/
lemma opPi_DDF_c2020_mem :
    opPi (fieldStrengthDeriv {Sum.inr 1, Sum.inl 0} (Sum.inr 1) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inl 0)]
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 1) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 1} _ _]
  rw [map_neg, opPi_dd02_F02, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd02 F13`. -/
lemma opPi_DDF_c0213_mem :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_dd02_F13]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd02 F31`. -/
lemma opPi_DDF_c0231_mem :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 2) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 2) (Sum.inr 0) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 1} _ _]
  rw [map_neg, opPi_dd02_F13, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd20 F13`. -/
lemma opPi_DDF_c2013_mem :
    opPi (fieldStrengthDeriv {Sum.inr 1, Sum.inl 0} (Sum.inr 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inl 0)]
  rw [opPi_dd02_F13]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd20 F31`. -/
lemma opPi_DDF_c2031_mem :
    opPi (fieldStrengthDeriv {Sum.inr 1, Sum.inl 0} (Sum.inr 2) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inl 0)]
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 2) (Sum.inr 0) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 1} _ _]
  rw [map_neg, opPi_dd02_F13, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd03 F03`. -/
lemma opPi_DDF_c0303_mem :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_dd03_F03]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd03 F30`. -/
lemma opPi_DDF_c0330_mem :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 2) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 2) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 2} _ _]
  rw [map_neg, opPi_dd03_F03, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd30 F03`. -/
lemma opPi_DDF_c3003_mem :
    opPi (fieldStrengthDeriv {Sum.inr 2, Sum.inl 0} (Sum.inl 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inl 0)]
  rw [opPi_dd03_F03]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd30 F30`. -/
lemma opPi_DDF_c3030_mem :
    opPi (fieldStrengthDeriv {Sum.inr 2, Sum.inl 0} (Sum.inr 2) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inl 0)]
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 2) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 2} _ _]
  rw [map_neg, opPi_dd03_F03, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd03 F12`. -/
lemma opPi_DDF_c0312_mem :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_dd03_F12]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd03 F21`. -/
lemma opPi_DDF_c0321_mem :
    opPi (fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 1) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 1) (Sum.inr 0) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 2} _ _]
  rw [map_neg, opPi_dd03_F12, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd30 F12`. -/
lemma opPi_DDF_c3012_mem :
    opPi (fieldStrengthDeriv {Sum.inr 2, Sum.inl 0} (Sum.inr 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inl 0)]
  rw [opPi_dd03_F12]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd30 F21`. -/
lemma opPi_DDF_c3021_mem :
    opPi (fieldStrengthDeriv {Sum.inr 2, Sum.inl 0} (Sum.inr 1) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inl 0)]
  rw [show fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 1) (Sum.inr 0) =
        -(fieldStrengthDeriv {Sum.inl 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {Sum.inl 0, Sum.inr 2} _ _]
  rw [map_neg, opPi_dd03_F12, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd12 F03`. -/
lemma opPi_DDF_c1203_mem :
    opPi (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_dd12_F03]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd12 F30`. -/
lemma opPi_DDF_c1230_mem :
    opPi (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 2) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 2) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 1} _ _]
  rw [map_neg, opPi_dd12_F03, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd21 F03`. -/
lemma opPi_DDF_c2103_mem :
    opPi (fieldStrengthDeriv {Sum.inr 1, Sum.inr 0} (Sum.inl 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inr 0)]
  rw [opPi_dd12_F03]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd21 F30`. -/
lemma opPi_DDF_c2130_mem :
    opPi (fieldStrengthDeriv {Sum.inr 1, Sum.inr 0} (Sum.inr 2) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inr 0)]
  rw [show fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 2) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inl 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 1} _ _]
  rw [map_neg, opPi_dd12_F03, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd12 F12`. -/
lemma opPi_DDF_c1212_mem :
    opPi (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_dd12_F12]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd12 F21`. -/
lemma opPi_DDF_c1221_mem :
    opPi (fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 1) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 1) (Sum.inr 0) =
        -(fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 1} _ _]
  rw [map_neg, opPi_dd12_F12, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd21 F12`. -/
lemma opPi_DDF_c2112_mem :
    opPi (fieldStrengthDeriv {Sum.inr 1, Sum.inr 0} (Sum.inr 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inr 0)]
  rw [opPi_dd12_F12]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd21 F21`. -/
lemma opPi_DDF_c2121_mem :
    opPi (fieldStrengthDeriv {Sum.inr 1, Sum.inr 0} (Sum.inr 1) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 1) (Sum.inr 0)]
  rw [show fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 1) (Sum.inr 0) =
        -(fieldStrengthDeriv {Sum.inr 0, Sum.inr 1} (Sum.inr 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 1} _ _]
  rw [map_neg, opPi_dd12_F12, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd13 F02`. -/
lemma opPi_DDF_c1302_mem :
    opPi (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_dd13_F02]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd13 F20`. -/
lemma opPi_DDF_c1320_mem :
    opPi (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 1) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 1) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 2} _ _]
  rw [map_neg, opPi_dd13_F02, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd31 F02`. -/
lemma opPi_DDF_c3102_mem :
    opPi (fieldStrengthDeriv {Sum.inr 2, Sum.inr 0} (Sum.inl 0) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inr 0)]
  rw [opPi_dd13_F02]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd31 F20`. -/
lemma opPi_DDF_c3120_mem :
    opPi (fieldStrengthDeriv {Sum.inr 2, Sum.inr 0} (Sum.inr 1) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inr 0)]
  rw [show fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 1) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inl 0) (Sum.inr 1)) from fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 2} _ _]
  rw [map_neg, opPi_dd13_F02, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd13 F13`. -/
lemma opPi_DDF_c1313_mem :
    opPi (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_dd13_F13]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd13 F31`. -/
lemma opPi_DDF_c1331_mem :
    opPi (fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 2) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 2) (Sum.inr 0) =
        -(fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 2} _ _]
  rw [map_neg, opPi_dd13_F13, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd31 F13`. -/
lemma opPi_DDF_c3113_mem :
    opPi (fieldStrengthDeriv {Sum.inr 2, Sum.inr 0} (Sum.inr 0) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inr 0)]
  rw [opPi_dd13_F13]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd31 F31`. -/
lemma opPi_DDF_c3131_mem :
    opPi (fieldStrengthDeriv {Sum.inr 2, Sum.inr 0} (Sum.inr 2) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inr 0)]
  rw [show fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 2) (Sum.inr 0) =
        -(fieldStrengthDeriv {Sum.inr 0, Sum.inr 2} (Sum.inr 0) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {Sum.inr 0, Sum.inr 2} _ _]
  rw [map_neg, opPi_dd13_F13, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd23 F01`. -/
lemma opPi_DDF_c2301_mem :
    opPi (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_dd23_F01]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd23 F10`. -/
lemma opPi_DDF_c2310_mem :
    opPi (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 0) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 0) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) from fieldStrengthDeriv_antisymm {Sum.inr 1, Sum.inr 2} _ _]
  rw [map_neg, opPi_dd23_F01, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd32 F01`. -/
lemma opPi_DDF_c3201_mem :
    opPi (fieldStrengthDeriv {Sum.inr 2, Sum.inr 1} (Sum.inl 0) (Sum.inr 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inr 1)]
  rw [opPi_dd23_F01]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd32 F10`. -/
lemma opPi_DDF_c3210_mem :
    opPi (fieldStrengthDeriv {Sum.inr 2, Sum.inr 1} (Sum.inr 0) (Sum.inl 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inr 1)]
  rw [show fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 0) (Sum.inl 0) =
        -(fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inl 0) (Sum.inr 0)) from fieldStrengthDeriv_antisymm {Sum.inr 1, Sum.inr 2} _ _]
  rw [map_neg, opPi_dd23_F01, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd23 F23`. -/
lemma opPi_DDF_c2323_mem :
    opPi (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [opPi_dd23_F23]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd23 F32`. -/
lemma opPi_DDF_c2332_mem :
    opPi (fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 2) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [show fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 2) (Sum.inr 1) =
        -(fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {Sum.inr 1, Sum.inr 2} _ _]
  rw [map_neg, opPi_dd23_F23, neg_zero]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd32 F23`. -/
lemma opPi_DDF_c3223_mem :
    opPi (fieldStrengthDeriv {Sum.inr 2, Sum.inr 1} (Sum.inr 1) (Sum.inr 2)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inr 1)]
  rw [opPi_dd23_F23]
  exact Submodule.zero_mem _

/-- Projector membership for the ordered derivative monomial `dd32 F32`. -/
lemma opPi_DDF_c3232_mem :
    opPi (fieldStrengthDeriv {Sum.inr 2, Sum.inr 1} (Sum.inr 2) (Sum.inr 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [fieldStrengthDeriv_pair_swap (Sum.inr 2) (Sum.inr 1)]
  rw [show fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 2) (Sum.inr 1) =
        -(fieldStrengthDeriv {Sum.inr 1, Sum.inr 2} (Sum.inr 1) (Sum.inr 2)) from fieldStrengthDeriv_antisymm {Sum.inr 1, Sum.inr 2} _ _]
  rw [map_neg, opPi_dd23_F23, neg_zero]
  exact Submodule.zero_mem _

/-- Projected Klein average of `e[0,0,0]` (u-family) lies in the span. -/
lemma opPi_kA_u000_mem :
    opPi (kleinAvg (Dbarψ [] 0 * Dψ [Sum.inl 0] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_u_e000, map_smul, opPi_u0]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTerm_mem_span)

/-- Projected Klein average of `e[0,0,1]` (u-family) lies in the span. -/
lemma opPi_kA_u001_mem :
    opPi (kleinAvg (Dbarψ [] 0 * Dψ [Sum.inl 0] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_u_e001, map_zero]
  exact Submodule.zero_mem _

/-- Projected Klein average of `e[0,1,0]` (u-family) lies in the span. -/
lemma opPi_kA_u010_mem :
    opPi (kleinAvg (Dbarψ [] 1 * Dψ [Sum.inl 0] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_u_e010, map_zero]
  exact Submodule.zero_mem _

/-- Projected Klein average of `e[0,1,1]` (u-family) lies in the span. -/
lemma opPi_kA_u011_mem :
    opPi (kleinAvg (Dbarψ [] 1 * Dψ [Sum.inl 0] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_u_e011, map_smul, opPi_u0]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTerm_mem_span)

/-- Projected Klein average of `e[1,0,0]` (u-family) lies in the span. -/
lemma opPi_kA_u100_mem :
    opPi (kleinAvg (Dbarψ [] 0 * Dψ [Sum.inr 0] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_u_e100, map_zero]
  exact Submodule.zero_mem _

/-- Projected Klein average of `e[1,0,1]` (u-family) lies in the span. -/
lemma opPi_kA_u101_mem :
    opPi (kleinAvg (Dbarψ [] 0 * Dψ [Sum.inr 0] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_u_e101, map_smul, opPi_u1]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTerm_mem_span)

/-- Projected Klein average of `e[1,1,0]` (u-family) lies in the span. -/
lemma opPi_kA_u110_mem :
    opPi (kleinAvg (Dbarψ [] 1 * Dψ [Sum.inr 0] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_u_e110, map_smul, opPi_u1]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTerm_mem_span)

/-- Projected Klein average of `e[1,1,1]` (u-family) lies in the span. -/
lemma opPi_kA_u111_mem :
    opPi (kleinAvg (Dbarψ [] 1 * Dψ [Sum.inr 0] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_u_e111, map_zero]
  exact Submodule.zero_mem _

/-- Projected Klein average of `e[2,0,0]` (u-family) lies in the span. -/
lemma opPi_kA_u200_mem :
    opPi (kleinAvg (Dbarψ [] 0 * Dψ [Sum.inr 1] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_u_e200, map_zero]
  exact Submodule.zero_mem _

/-- Projected Klein average of `e[2,0,1]` (u-family) lies in the span. -/
lemma opPi_kA_u201_mem :
    opPi (kleinAvg (Dbarψ [] 0 * Dψ [Sum.inr 1] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_u_e201, map_smul, opPi_u2]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTerm_mem_span)

/-- Projected Klein average of `e[2,1,0]` (u-family) lies in the span. -/
lemma opPi_kA_u210_mem :
    opPi (kleinAvg (Dbarψ [] 1 * Dψ [Sum.inr 1] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_u_e210, map_smul, opPi_u2]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTerm_mem_span)

/-- Projected Klein average of `e[2,1,1]` (u-family) lies in the span. -/
lemma opPi_kA_u211_mem :
    opPi (kleinAvg (Dbarψ [] 1 * Dψ [Sum.inr 1] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_u_e211, map_zero]
  exact Submodule.zero_mem _

/-- Projected Klein average of `e[3,0,0]` (u-family) lies in the span. -/
lemma opPi_kA_u300_mem :
    opPi (kleinAvg (Dbarψ [] 0 * Dψ [Sum.inr 2] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_u_e300, map_smul, opPi_u3]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTerm_mem_span)

/-- Projected Klein average of `e[3,0,1]` (u-family) lies in the span. -/
lemma opPi_kA_u301_mem :
    opPi (kleinAvg (Dbarψ [] 0 * Dψ [Sum.inr 2] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_u_e301, map_zero]
  exact Submodule.zero_mem _

/-- Projected Klein average of `e[3,1,0]` (u-family) lies in the span. -/
lemma opPi_kA_u310_mem :
    opPi (kleinAvg (Dbarψ [] 1 * Dψ [Sum.inr 2] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_u_e310, map_zero]
  exact Submodule.zero_mem _

/-- Projected Klein average of `e[3,1,1]` (u-family) lies in the span. -/
lemma opPi_kA_u311_mem :
    opPi (kleinAvg (Dbarψ [] 1 * Dψ [Sum.inr 2] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_u_e311, map_smul, opPi_u3]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTerm_mem_span)

/-- Projected Klein average of `e[0,0,0]` (ubar-family) lies in the span. -/
lemma opPi_kA_ubar000_mem :
    opPi (kleinAvg (Dbarψ [Sum.inl 0] 0 * Dψ [] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_ubar_e000, map_smul, opPi_ubar0]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTermBar_mem_span)

/-- Projected Klein average of `e[0,0,1]` (ubar-family) lies in the span. -/
lemma opPi_kA_ubar001_mem :
    opPi (kleinAvg (Dbarψ [Sum.inl 0] 0 * Dψ [] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_ubar_e001, map_zero]
  exact Submodule.zero_mem _

/-- Projected Klein average of `e[0,1,0]` (ubar-family) lies in the span. -/
lemma opPi_kA_ubar010_mem :
    opPi (kleinAvg (Dbarψ [Sum.inl 0] 1 * Dψ [] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_ubar_e010, map_zero]
  exact Submodule.zero_mem _

/-- Projected Klein average of `e[0,1,1]` (ubar-family) lies in the span. -/
lemma opPi_kA_ubar011_mem :
    opPi (kleinAvg (Dbarψ [Sum.inl 0] 1 * Dψ [] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_ubar_e011, map_smul, opPi_ubar0]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTermBar_mem_span)

/-- Projected Klein average of `e[1,0,0]` (ubar-family) lies in the span. -/
lemma opPi_kA_ubar100_mem :
    opPi (kleinAvg (Dbarψ [Sum.inr 0] 0 * Dψ [] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_ubar_e100, map_zero]
  exact Submodule.zero_mem _

/-- Projected Klein average of `e[1,0,1]` (ubar-family) lies in the span. -/
lemma opPi_kA_ubar101_mem :
    opPi (kleinAvg (Dbarψ [Sum.inr 0] 0 * Dψ [] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_ubar_e101, map_smul, opPi_ubar1]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTermBar_mem_span)

/-- Projected Klein average of `e[1,1,0]` (ubar-family) lies in the span. -/
lemma opPi_kA_ubar110_mem :
    opPi (kleinAvg (Dbarψ [Sum.inr 0] 1 * Dψ [] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_ubar_e110, map_smul, opPi_ubar1]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTermBar_mem_span)

/-- Projected Klein average of `e[1,1,1]` (ubar-family) lies in the span. -/
lemma opPi_kA_ubar111_mem :
    opPi (kleinAvg (Dbarψ [Sum.inr 0] 1 * Dψ [] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_ubar_e111, map_zero]
  exact Submodule.zero_mem _

/-- Projected Klein average of `e[2,0,0]` (ubar-family) lies in the span. -/
lemma opPi_kA_ubar200_mem :
    opPi (kleinAvg (Dbarψ [Sum.inr 1] 0 * Dψ [] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_ubar_e200, map_zero]
  exact Submodule.zero_mem _

/-- Projected Klein average of `e[2,0,1]` (ubar-family) lies in the span. -/
lemma opPi_kA_ubar201_mem :
    opPi (kleinAvg (Dbarψ [Sum.inr 1] 0 * Dψ [] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_ubar_e201, map_smul, opPi_ubar2]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTermBar_mem_span)

/-- Projected Klein average of `e[2,1,0]` (ubar-family) lies in the span. -/
lemma opPi_kA_ubar210_mem :
    opPi (kleinAvg (Dbarψ [Sum.inr 1] 1 * Dψ [] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_ubar_e210, map_smul, opPi_ubar2]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTermBar_mem_span)

/-- Projected Klein average of `e[2,1,1]` (ubar-family) lies in the span. -/
lemma opPi_kA_ubar211_mem :
    opPi (kleinAvg (Dbarψ [Sum.inr 1] 1 * Dψ [] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_ubar_e211, map_zero]
  exact Submodule.zero_mem _

/-- Projected Klein average of `e[3,0,0]` (ubar-family) lies in the span. -/
lemma opPi_kA_ubar300_mem :
    opPi (kleinAvg (Dbarψ [Sum.inr 2] 0 * Dψ [] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_ubar_e300, map_smul, opPi_ubar3]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTermBar_mem_span)

/-- Projected Klein average of `e[3,0,1]` (ubar-family) lies in the span. -/
lemma opPi_kA_ubar301_mem :
    opPi (kleinAvg (Dbarψ [Sum.inr 2] 0 * Dψ [] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_ubar_e301, map_zero]
  exact Submodule.zero_mem _

/-- Projected Klein average of `e[3,1,0]` (ubar-family) lies in the span. -/
lemma opPi_kA_ubar310_mem :
    opPi (kleinAvg (Dbarψ [Sum.inr 2] 1 * Dψ [] 0)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_ubar_e310, map_zero]
  exact Submodule.zero_mem _

/-- Projected Klein average of `e[3,1,1]` (ubar-family) lies in the span. -/
lemma opPi_kA_ubar311_mem :
    opPi (kleinAvg (Dbarψ [Sum.inr 2] 1 * Dψ [] 1)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_ubar_e311, map_smul, opPi_ubar3]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ fermionKineticTermBar_mem_span)

attribute [local irreducible] Dψ Dbarψ fieldStrengthDeriv

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 8192 in
/-- The projected Klein average of any product of two field strengths lies in
  the span of the invariants. -/
lemma opPi_kleinAvg_FF_mem (a b c d : Fin 1 ⊕ Fin 3) :
    opPi (kleinAvg (fieldStrengthDeriv {} a b * fieldStrengthDeriv {} c d)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_fieldStrengthDeriv_nil_mul, map_smul]
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
    rcases d with d | d <;> fin_cases a <;> fin_cases b <;> fin_cases c <;>
    fin_cases d <;>
    (try simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]) <;>
    first
    | (rw [fieldStrengthDeriv_self]
       simp only [zero_mul, mul_zero, map_zero, smul_zero]
       exact Submodule.zero_mem _)
    | (refine Submodule.smul_mem _ _ ?_
       first
       | exact opPi_FF_c0101_mem
       | exact opPi_FF_c0110_mem
       | exact opPi_FF_c1001_mem
       | exact opPi_FF_c1010_mem
       | exact opPi_FF_c0123_mem
       | exact opPi_FF_c0132_mem
       | exact opPi_FF_c1023_mem
       | exact opPi_FF_c1032_mem
       | exact opPi_FF_c2301_mem
       | exact opPi_FF_c2310_mem
       | exact opPi_FF_c3201_mem
       | exact opPi_FF_c3210_mem
       | exact opPi_FF_c2323_mem
       | exact opPi_FF_c2332_mem
       | exact opPi_FF_c3223_mem
       | exact opPi_FF_c3232_mem
       | exact opPi_FF_c0202_mem
       | exact opPi_FF_c0220_mem
       | exact opPi_FF_c2002_mem
       | exact opPi_FF_c2020_mem
       | exact opPi_FF_c0213_mem
       | exact opPi_FF_c0231_mem
       | exact opPi_FF_c2013_mem
       | exact opPi_FF_c2031_mem
       | exact opPi_FF_c1302_mem
       | exact opPi_FF_c1320_mem
       | exact opPi_FF_c3102_mem
       | exact opPi_FF_c3120_mem
       | exact opPi_FF_c1313_mem
       | exact opPi_FF_c1331_mem
       | exact opPi_FF_c3113_mem
       | exact opPi_FF_c3131_mem
       | exact opPi_FF_c0303_mem
       | exact opPi_FF_c0330_mem
       | exact opPi_FF_c3003_mem
       | exact opPi_FF_c3030_mem
       | exact opPi_FF_c0312_mem
       | exact opPi_FF_c0321_mem
       | exact opPi_FF_c3012_mem
       | exact opPi_FF_c3021_mem
       | exact opPi_FF_c1203_mem
       | exact opPi_FF_c1230_mem
       | exact opPi_FF_c2103_mem
       | exact opPi_FF_c2130_mem
       | exact opPi_FF_c1212_mem
       | exact opPi_FF_c1221_mem
       | exact opPi_FF_c2112_mem
       | exact opPi_FF_c2121_mem)
    | (norm_num [paritySignZ, paritySignY, paritySignX]
       first
       | done
       | exact Submodule.zero_mem _)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 8192 in
/-- The projected Klein average of any second-derivative field strength lies
  in the span of the invariants. -/
lemma opPi_kleinAvg_DDF_mem (r t a b : Fin 1 ⊕ Fin 3) :
    opPi (kleinAvg (fieldStrengthDeriv {r, t} a b)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [kleinAvg_fieldStrengthDeriv_pair, map_smul]
  rcases r with r | r <;> rcases t with t | t <;> rcases a with a | a <;>
    rcases b with b | b <;> fin_cases r <;> fin_cases t <;> fin_cases a <;>
    fin_cases b <;>
    (try simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]) <;>
    first
    | (rw [fieldStrengthDeriv_self]
       simp only [map_zero, smul_zero]
       exact Submodule.zero_mem _)
    | (refine Submodule.smul_mem _ _ ?_
       first
       | exact opPi_DDF_c0101_mem
       | exact opPi_DDF_c0110_mem
       | exact opPi_DDF_c1001_mem
       | exact opPi_DDF_c1010_mem
       | exact opPi_DDF_c0123_mem
       | exact opPi_DDF_c0132_mem
       | exact opPi_DDF_c1023_mem
       | exact opPi_DDF_c1032_mem
       | exact opPi_DDF_c0202_mem
       | exact opPi_DDF_c0220_mem
       | exact opPi_DDF_c2002_mem
       | exact opPi_DDF_c2020_mem
       | exact opPi_DDF_c0213_mem
       | exact opPi_DDF_c0231_mem
       | exact opPi_DDF_c2013_mem
       | exact opPi_DDF_c2031_mem
       | exact opPi_DDF_c0303_mem
       | exact opPi_DDF_c0330_mem
       | exact opPi_DDF_c3003_mem
       | exact opPi_DDF_c3030_mem
       | exact opPi_DDF_c0312_mem
       | exact opPi_DDF_c0321_mem
       | exact opPi_DDF_c3012_mem
       | exact opPi_DDF_c3021_mem
       | exact opPi_DDF_c1203_mem
       | exact opPi_DDF_c1230_mem
       | exact opPi_DDF_c2103_mem
       | exact opPi_DDF_c2130_mem
       | exact opPi_DDF_c1212_mem
       | exact opPi_DDF_c1221_mem
       | exact opPi_DDF_c2112_mem
       | exact opPi_DDF_c2121_mem
       | exact opPi_DDF_c1302_mem
       | exact opPi_DDF_c1320_mem
       | exact opPi_DDF_c3102_mem
       | exact opPi_DDF_c3120_mem
       | exact opPi_DDF_c1313_mem
       | exact opPi_DDF_c1331_mem
       | exact opPi_DDF_c3113_mem
       | exact opPi_DDF_c3131_mem
       | exact opPi_DDF_c2301_mem
       | exact opPi_DDF_c2310_mem
       | exact opPi_DDF_c3201_mem
       | exact opPi_DDF_c3210_mem
       | exact opPi_DDF_c2323_mem
       | exact opPi_DDF_c2332_mem
       | exact opPi_DDF_c3223_mem
       | exact opPi_DDF_c3232_mem)
    | (norm_num [paritySignZ, paritySignY, paritySignX]
       first
       | done
       | exact Submodule.zero_mem _)

set_option maxRecDepth 8192 in
/-- The projected Klein average of any `ψ̄ (Dψ)` pair lies in the span. -/
lemma opPi_kleinAvg_FM1_mem (μ : Fin 1 ⊕ Fin 3) (α β : Fin 2) :
    opPi (kleinAvg (Dbarψ [] α * Dψ [μ] β)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rcases μ with m | m <;> fin_cases m <;> fin_cases α <;> fin_cases β <;>
    (try simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]) <;>
    first
    | exact opPi_kA_u000_mem
    | exact opPi_kA_u001_mem
    | exact opPi_kA_u010_mem
    | exact opPi_kA_u011_mem
    | exact opPi_kA_u100_mem
    | exact opPi_kA_u101_mem
    | exact opPi_kA_u110_mem
    | exact opPi_kA_u111_mem
    | exact opPi_kA_u200_mem
    | exact opPi_kA_u201_mem
    | exact opPi_kA_u210_mem
    | exact opPi_kA_u211_mem
    | exact opPi_kA_u300_mem
    | exact opPi_kA_u301_mem
    | exact opPi_kA_u310_mem
    | exact opPi_kA_u311_mem

set_option maxRecDepth 8192 in
/-- The projected Klein average of any `(D̄ψ̄) ψ` pair lies in the span. -/
lemma opPi_kleinAvg_FM2_mem (μ : Fin 1 ⊕ Fin 3) (α β : Fin 2) :
    opPi (kleinAvg (Dbarψ [μ] α * Dψ [] β)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rcases μ with m | m <;> fin_cases m <;> fin_cases α <;> fin_cases β <;>
    (try simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]) <;>
    first
    | exact opPi_kA_ubar000_mem
    | exact opPi_kA_ubar001_mem
    | exact opPi_kA_ubar010_mem
    | exact opPi_kA_ubar011_mem
    | exact opPi_kA_ubar100_mem
    | exact opPi_kA_ubar101_mem
    | exact opPi_kA_ubar110_mem
    | exact opPi_kA_ubar111_mem
    | exact opPi_kA_ubar200_mem
    | exact opPi_kA_ubar201_mem
    | exact opPi_kA_ubar210_mem
    | exact opPi_kA_ubar211_mem
    | exact opPi_kA_ubar300_mem
    | exact opPi_kA_ubar301_mem
    | exact opPi_kA_ubar310_mem
    | exact opPi_kA_ubar311_mem

/-- The reversed pair `(Dψ) ψ̄`, via anticommutation. -/
lemma opPi_kleinAvg_FM1r_mem (μ : Fin 1 ⊕ Fin 3) (α β : Fin 2) :
    opPi (kleinAvg (Dψ [μ] β * Dbarψ [] α)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [Dψ_mul_Dbarψ_anticomm, map_neg, map_neg]
  exact neg_mem (opPi_kleinAvg_FM1_mem μ α β)

/-- The reversed pair `ψ (D̄ψ̄)`, via anticommutation. -/
lemma opPi_kleinAvg_FM2r_mem (μ : Fin 1 ⊕ Fin 3) (α β : Fin 2) :
    opPi (kleinAvg (Dψ [] α * Dbarψ [μ] β)) ∈
      Submodule.span ℂ massDimFourInvariants := by
  rw [Dψ_mul_Dbarψ_anticomm, map_neg, map_neg]
  exact neg_mem (opPi_kleinAvg_FM2_mem μ β α)

end SectorEight

set_option maxHeartbeats 4000000 in
/-- The weight-eight classification: a Lorentz-invariant neutral element of
  mass weight eight is a combination of the Maxwell term, the theta term, and
  the two fermion kinetic terms. -/
lemma mem_span_of_mem_chargeCovSpan_eight {y : JetAlgebra}
    (hy : y ∈ chargeCovSpan 8 0)
    (hinv : ∀ Λ : SL(2,ℂ), repLorentzGroup Λ y = y) :
    y ∈ Submodule.span ℂ massDimFourInvariants := by
  have h := chargeCovSpan_eight_le hy
  rw [Submodule.span_union, Submodule.span_union, Submodule.span_union,
    Submodule.span_union, Submodule.span_union] at h
  obtain ⟨u5, hu5, w6, hw6, hE6⟩ := Submodule.mem_sup.mp h
  obtain ⟨u4, hu4, w5, hw5, hE5⟩ := Submodule.mem_sup.mp hu5
  obtain ⟨u3, hu3, w4, hw4, hE4⟩ := Submodule.mem_sup.mp hu4
  obtain ⟨u2, hu2, w3, hw3, hE3⟩ := Submodule.mem_sup.mp hu3
  obtain ⟨w1, hw1, w2, hw2, hE2⟩ := Submodule.mem_sup.mp hu2
  obtain ⟨c1, hc1⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hw1
  obtain ⟨c2, hc2⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hw2
  obtain ⟨c3, hc3⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hw3
  obtain ⟨c4, hc4⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hw4
  obtain ⟨c5, hc5⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hw5
  obtain ⟨c6, hc6⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hw6
  have hKy : kleinAvg y = y := by
    rw [kleinAvg_apply, hinv parityZ, hinv parityY, hinv parityX]
    module
  have hself : opPi (kleinAvg y) = y := by
    rw [hKy]
    exact opPi_apply_of_invariant hinv
  rw [← hself, ← hE6, ← hE5, ← hE4, ← hE3, ← hE2, ← hc1, ← hc2, ← hc3, ← hc4,
    ← hc5, ← hc6]
  simp only [map_add, map_sum, map_smul]
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_) ?_) ?_
  · exact Submodule.sum_mem _ fun p _ =>
      Submodule.smul_mem _ _ (opPi_kleinAvg_FF_mem p.1.1 p.1.2 p.2.1 p.2.2)
  · exact Submodule.sum_mem _ fun p _ =>
      Submodule.smul_mem _ _ (opPi_kleinAvg_DDF_mem p.1.1 p.1.2 p.2.1 p.2.2)
  · exact Submodule.sum_mem _ fun p _ =>
      Submodule.smul_mem _ _ (opPi_kleinAvg_FM1_mem p.2 p.1.1 p.1.2)
  · exact Submodule.sum_mem _ fun p _ =>
      Submodule.smul_mem _ _ (opPi_kleinAvg_FM1r_mem p.2 p.1.1 p.1.2)
  · exact Submodule.sum_mem _ fun p _ =>
      Submodule.smul_mem _ _ (opPi_kleinAvg_FM2r_mem p.2 p.1.1 p.1.2)
  · exact Submodule.sum_mem _ fun p _ =>
      Submodule.smul_mem _ _ (opPi_kleinAvg_FM2_mem p.2 p.1.2 p.1.1)

/-- The classification of the renormalizable QED Lagrangian densities: the
  gauge- and Lorentz-invariant elements of mass weight at most eight are spanned
  by the constants, the Maxwell term, the theta term, and the two fermion
  kinetic terms.

  The inclusion `⊇` is `span_massDimFourInvariants_le`: each of the five
  elements is invariant and of weight at most eight.

  The completeness direction `⊆` is proved as follows.
  1. By `InvariantSubmodule.mem_iff_isInvariant` and
     `isInvariant_iff_mem_adjoin_invariantGenerators`, an invariant `x` of
     weight at most eight lies in the algebra generated by the covariant
     generators, is fixed by the jets of constant gauge transformations, and is
     Lorentz invariant.
  2. Graded decomposition (`exists_covMonomialSpan_decomp`): `x` is a sum of
     nine components `z m ∈ covMonomialSpan m` of exact weights `0, …, 8`,
     using the homogeneity of the covariant monomials and the linear
     independence of the powers `c ↦ c ^ m`
     (`eq_zero_of_forall_sum_pow_smul_eq_zero`).
  3. Componentwise invariance: the mass-dimension scaling commutes with the
     Lorentz action and with the constant gauge action, so each component
     `z m` inherits both invariances, again by independence of powers.
  4. Sector analysis. `m = 0`: the weight-zero monomial span is the constants.
     `m = 1, 2`: there are no covariant monomials of these weights, since the
     generators have weights at least three. Odd `m = 3, 5, 7`: odd weight
     forces an odd number of fermionic factors, and the constant gauge
     transformation with `u(0) = i` acts on such a monomial by
     `(i⁶)^{n_ψ} ((-i)⁶)^{n_ψ̄} = (-1)^{n_ψ + n_ψ̄} = -1`, so invariance forces
     `z m = 0`. `m = 4, 6`: after splitting off the hypercharge `±12` sectors
     with a further root of unity, the surviving monomials (`F_{μν}`;
     `∂_ρ F_{μν}` and the zero-derivative fermion pairs `ψ̄_α ψ_β`) admit no
     Lorentz invariant. `m = 8`: the charge-balanced monomials are `F · F`,
     `∂∂F`, and the one-derivative fermion pairs; their Lorentz invariants are
     spanned by the Maxwell term, the theta term, and the two σ-contracted
     kinetic terms.

  Steps 3–4 remain to be formalized: they require the commutation of the
  scaling with the two group actions at the QED level, the linear independence
  of the covariant monomials, and the invariant theory of `SL(2,ℂ)` on the
  finite-dimensional weight sectors. -/
lemma invariantMassWeightSubmodule_eight_eq_span_massDimFourInvariants :
    InvariantMassWeightSubmodule 8 = Submodule.span ℂ massDimFourInvariants := by
  refine le_antisymm ?_ span_massDimFourInvariants_le
  intro x hx
  obtain ⟨hxw, hxinv⟩ := Submodule.mem_inf.mp hx
  rw [InvariantSubmodule.mem_iff_isInvariant] at hxinv
  obtain ⟨hadj, hconst, hlor⟩ :=
    (isInvariant_iff_mem_adjoin_invariantGenerators x).mp hxinv
  obtain ⟨z, hzmem, hxeq⟩ := exists_covMonomialSpan_decomp hxw hadj
  rw [hxeq]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hzlor : ∀ Λ : SL(2,ℂ), repLorentzGroup Λ (z m) = z m := fun Λ =>
    repLorentzGroup_covComponent_eq hzmem Λ (by rw [← hxeq]; exact hlor Λ) hm
  have hzconst : ∀ g : GaugeGroupI,
      repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) (z m) = z m := fun g =>
    repJetGaugeGroupI_ofConstant_covComponent_eq hzmem g
      (by rw [← hxeq]; exact hconst g) hm
  have hm9 := Finset.mem_range.mp hm
  interval_cases m
  · exact Submodule.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
      (covMonomialSpan_zero_le (hzmem 0))
  · rw [show z 1 = 0 from (Submodule.mem_bot ℂ).mp
      (covMonomialSpan_le_bot_of_lt_three le_rfl (by omega) (hzmem 1))]
    exact Submodule.zero_mem _
  · rw [show z 2 = 0 from (Submodule.mem_bot ℂ).mp
      (covMonomialSpan_le_bot_of_lt_three (by omega) (by omega) (hzmem 2))]
    exact Submodule.zero_mem _
  · rw [eq_zero_of_mem_covMonomialSpan_odd (by norm_num) (hzmem 3)
      (hzconst parityGauge)]
    exact Submodule.zero_mem _
  · rw [eq_zero_of_mem_chargeCovSpan_four
      (mem_chargeCovSpan_zero_of_invariant (hzmem 4) hzconst) hzlor]
    exact Submodule.zero_mem _
  · rw [eq_zero_of_mem_covMonomialSpan_odd (by norm_num) (hzmem 5)
      (hzconst parityGauge)]
    exact Submodule.zero_mem _
  · rw [eq_zero_of_mem_chargeCovSpan_six
      (mem_chargeCovSpan_zero_of_invariant (hzmem 6) hzconst) hzlor]
    exact Submodule.zero_mem _
  · rw [eq_zero_of_mem_covMonomialSpan_odd (by norm_num) (hzmem 7)
      (hzconst parityGauge)]
    exact Submodule.zero_mem _
  · exact mem_span_of_mem_chargeCovSpan_eight
      (mem_chargeCovSpan_zero_of_invariant (hzmem 8) hzconst) hzlor

end JetAlgebra

end QED
