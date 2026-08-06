/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.QED.JetAlgebra.MassDim
/-!
# The renormalizable invariants of the QED jet algebra

The four gauge- and Lorentz-invariant elements of mass dimension at most four
(mass weight at most eight): the Maxwell term `F_{μν} F^{μν}`, the topological
theta term `ε^{μνρσ} F_{μν} F_{ρσ}`, and the two fermion kinetic terms
`i ψ̄ σ̄^μ (D_μ ψ)` and `-i (D̄_μ ψ̄) σ̄^μ ψ`.

This file defines them, proves each is invariant under the jet gauge group and
under `SL(2,ℂ)`, and deduces the easy half of the classification: their span is
contained in `InvariantMassWeightSubmodule 8`.
-/

@[expose] public section

set_option maxHeartbeats 1000000

namespace QED
open TensorProduct StandardModel

namespace JetAlgebra

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
end JetAlgebra

end QED
