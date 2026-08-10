/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.LorentzAction
public import Physlib.Relativity.MinkowskiMatrix
public import Physlib.Relativity.PauliMatrices.Basic
public import Physlib.Particles.StandardModel.GaugeBosons.BBoson.MassDim
/-!
# Mass dimension on the lepton–gauge-sector jet algebra

*Note*: In this file we use the notion 'mass weight'. The idea been that the
'mass weight' is twice the mass dimension. This is because it is easier to work exclusively with
integers, and the mass dimension of the fermion fields is 3/2.

-/

@[expose] public section

namespace LeptonGaugeSector
open TensorProduct StandardModel Matrix MatrixGroups

/-- We define the mass weight of a term as two times its mass dimnesion. -/
def MassWeight : JetGenerators → ℕ
  | JetGenerators.dB s _ => 2 * (1 + s.card)
  | JetGenerators.dψ s _ => 3 + 2 * s.card
  | JetGenerators.dbarψ s _ => 3 + 2 * s.card

namespace JetAlgebra

/-!

## A. The massWeightScaling algebra homomorphism

-/
/-- The mass-dimension scaling on the lepton–gauge-sector jet algebra: the algebra map
  multiplying each generator by `c ^ w`, where `w` is twice its mass dimension.
  It is the tensor product of the scalings on the B-boson and charged-lepton
  jet algebras. -/
noncomputable def massWeightScale (c : ℂ) : JetAlgebra →ₐ[ℂ] JetAlgebra :=
  Algebra.TensorProduct.map (BBoson.JetAlgebra.massWeightScale c)
    (LeptonSinglet.JetAlgebra.massWeightScale c)

/-- The mass-dimension scaling on a pure tensor. -/
lemma massWeightScale_tmul (c : ℂ) (p : ℂ ⊗[ℝ] BBoson.JetAlgebra)
    (l : LeptonSinglet.JetAlgebra) :
    massWeightScale c (p ⊗ₜ[ℂ] l) =
      (BBoson.JetAlgebra.massWeightScale c p) ⊗ₜ[ℂ]
        (LeptonSinglet.JetAlgebra.massWeightScale c l) :=
  Algebra.TensorProduct.map_tmul _ _ _ _

/-- Each generator scales by `c` to the power of its mass weight. -/
lemma massWeightScale_ofGenerator (c : ℂ) (j : JetGenerators) :
    massWeightScale c [j]ₐ = c ^ MassWeight j • [j]ₐ := by
  cases j with
  | dB s μ =>
    simp only [ofGenerator, massWeightScale, Algebra.TensorProduct.map_tmul, map_one,
      BBoson.JetAlgebra.massWeightScale_tmul_ofGenerator, ← TensorProduct.smul_tmul']
    rfl
  | dψ s α =>
    simp only [ofGenerator, massWeightScale, Algebra.TensorProduct.map_tmul,
      ← Algebra.TensorProduct.one_def, map_one,
      LeptonSinglet.JetAlgebra.massWeightScale_ofGenerator, TensorProduct.tmul_smul]
    rfl
  | dbarψ s α =>
    simp only [ofGenerator, massWeightScale, Algebra.TensorProduct.map_tmul,
      ← Algebra.TensorProduct.one_def, map_one,
      LeptonSinglet.JetAlgebra.massWeightScale_ofGenerator, TensorProduct.tmul_smul]
    rfl

lemma massWeightScale_dB_nil (c : ℂ) (μ : Fin 1 ⊕ Fin 3) :
    massWeightScale c [JetGenerators.dB 0 μ]ₐ = c ^ 2 • [JetGenerators.dB 0 μ]ₐ := by
  rw [massWeightScale_ofGenerator, MassWeight]
  norm_num

/-- The total derivative raises the mass weight by two. -/
lemma massWeightScale_jetDeriv (c : ℂ) (μ : Fin 1 ⊕ Fin 3) (x : JetAlgebra) :
    massWeightScale c (jetDeriv μ x) = c ^ 2 • jetDeriv μ (massWeightScale c x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb, smul_add]
  | tmul p l =>
    simp only [jetDeriv_tmul, map_add, massWeightScale, Algebra.TensorProduct.map_tmul,
      BBoson.JetAlgebra.massWeightScale_jetDeriv_baseChange,
      LeptonSinglet.JetAlgebra.massWeightScale_jetDeriv, TensorProduct.smul_tmul',
      TensorProduct.tmul_smul, smul_add]

/-- The covariant step raises the mass weight by two: the gauge-field term
  `6 i B_μ ·` carries the same weight as the derivative. -/
lemma massWeightScale_covariantStep (c : ℂ) (μ : Fin 1 ⊕ Fin 3) (x : JetAlgebra) :
    massWeightScale c (covariantStep μ x) =
      c ^ 2 • covariantStep μ (massWeightScale c x) := by
  simp only [covariantStep_apply, Multiset.empty_eq_zero, map_sub, massWeightScale_jetDeriv,
    map_smul, map_mul, massWeightScale_dB_nil, smul_mul_assoc]
  module

/-- The conjugate covariant step raises the mass weight by two. -/
lemma massWeightScale_covariantStepBar (c : ℂ) (μ : Fin 1 ⊕ Fin 3) (x : JetAlgebra) :
    massWeightScale c (covariantStepBar μ x) =
      c ^ 2 • covariantStepBar μ (massWeightScale c x) := by
  simp only [covariantStepBar_apply, Multiset.empty_eq_zero, map_add, massWeightScale_jetDeriv,
    map_smul, map_mul, massWeightScale_dB_nil, smul_mul_assoc, smul_add, add_right_inj]
  module

/-- Homogeneity of the covariant derivative: `D_l ψ_α` has mass weight
  `3 + 2 |l|`. -/
lemma massWeightScale_Dψ (c : ℂ) (l : List (Fin 1 ⊕ Fin 3)) (α : Fin 2) :
    massWeightScale c (Dψ l α) = c ^ (3 + 2 * l.length) • Dψ l α := by
  induction l with
  | nil =>
    rw [Dψ_nil, massWeightScale_ofGenerator,
      show MassWeight (JetGenerators.dψ {} α) = 3 from rfl]
    norm_num
  | cons μ l ih =>
    rw [Dψ_cons, massWeightScale_covariantStep c μ (Dψ l α), ih]
    simp only [map_smul, smul_smul, List.length_cons]
    ring_nf

/-- Homogeneity of the conjugate covariant derivative: `D̄_l ψ̄_α` has mass
  weight `3 + 2 |l|`. -/
lemma massWeightScale_Dbarψ (c : ℂ) (l : List (Fin 1 ⊕ Fin 3)) (α : Fin 2) :
    massWeightScale c (Dbarψ l α) = c ^ (3 + 2 * l.length) • Dbarψ l α := by
  induction l with
  | nil =>
    rw [Dbarψ_nil, massWeightScale_ofGenerator,
      show MassWeight (JetGenerators.dbarψ {} α) = 3 from rfl]
    norm_num
  | cons μ l ih =>
    rw [Dbarψ_cons, massWeightScale_covariantStepBar c μ (Dbarψ l α), ih]
    simp only [map_smul, smul_smul, List.length_cons]
    ring_nf

/-- Homogeneity of the field-strength derivatives: `∂_s F_{μν}` has mass weight
  `4 + 2 |s|`. -/
lemma massWeightScale_fieldStrengthDeriv (c : ℂ) (s : Multiset (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) :
    massWeightScale c (fieldStrengthDeriv s μ ν) =
      c ^ (4 + 2 * Multiset.card s) • fieldStrengthDeriv s μ ν := by
  have h : (fieldStrengthDeriv s μ ν : JetAlgebra) =
      [JetGenerators.dB (s + {μ}) ν]ₐ - [JetGenerators.dB (s + {ν}) μ]ₐ := by
    rw [fieldStrengthDeriv, BBoson.JetAlgebra.fieldStrengthDeriv,
      TensorProduct.tmul_sub, TensorProduct.sub_tmul]
    rfl
  rw [h, map_sub, massWeightScale_ofGenerator, massWeightScale_ofGenerator,
    show MassWeight (JetGenerators.dB (s + {μ}) ν) = 4 + 2 * Multiset.card s from by
      simp only [MassWeight, Multiset.card_add, Multiset.card_singleton]; omega,
    show MassWeight (JetGenerators.dB (s + {ν}) μ) = 4 + 2 * Multiset.card s from by
      simp only [MassWeight, Multiset.card_add, Multiset.card_singleton]; omega,
    smul_sub]

/-- Products of homogeneous elements are homogeneous of the summed weight. -/
lemma massWeightScale_mul_eigen {x y : JetAlgebra} {m n : ℕ}
    (hx : ∀ c : ℂ, massWeightScale c x = c ^ m • x)
    (hy : ∀ c : ℂ, massWeightScale c y = c ^ n • y) (c : ℂ) :
    massWeightScale c (x * y) = c ^ (m + n) • (x * y) := by
  simp only [map_mul, hx, hy]
  noncomm_ring [smul_smul]
  ring_nf


/-- The mass-dimension scaling at a real scalar commutes with the Lorentz
  action on the lepton–gauge-sector jet algebra. -/
lemma massWeightScale_ofReal_repLorentzGroup (r : ℝ) (Λ : SL(2,ℂ))
    (x : JetAlgebra) :
    massWeightScale (r : ℂ) (repLorentzGroup Λ x) =
      repLorentzGroup Λ (massWeightScale (r : ℂ) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul p l =>
    simp only [repLorentzGroup_tmul, massWeightScale_tmul,
      BBoson.JetAlgebra.massWeightScale_ofReal_complexRepLorentzGroup,
      LeptonSinglet.JetAlgebra.massWeightScale_repLorentzGroup_apply]


/-- The mass-dimension scaling commutes with the constant gauge action on the
  lepton–gauge-sector jet algebra. -/
lemma massWeightScale_repJetGaugeGroupI_ofConstant (c : ℂ) (g : GaugeGroupI)
    (x : JetAlgebra) :
    massWeightScale c (repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) x) =
      repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) (massWeightScale c x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul p l =>
    simp only [repJetGaugeGroupI_tmul', massWeightScale_tmul,
      BBoson.JetAlgebra.complexRepJetGaugeGroupI_ofConstant,
      LeptonSinglet.JetAlgebra.massWeightScale_repJetGaugeGroupI_ofConstant_apply]


/-!

## A. The mass-weight submodules

-/
noncomputable def MassDimSubmodule (n : ℕ) : Submodule ℂ JetAlgebra :=
    Submodule.span ℂ { x | ∀ c : ℂ, massWeightScale c x = c ^ n • x }


noncomputable def MassWeightLESubmodule (n : ℕ) : Submodule ℂ JetAlgebra :=
  Submodule.span ℂ {x | ∃ m ≤ n, ∀ c : ℂ, massWeightScale c x = c ^ m • x}

noncomputable def InvariantMassWeightSubmodule (n : ℕ) : Submodule ℂ JetAlgebra :=
  MassWeightLESubmodule n ⊓ InvariantSubmodule

/-- Eigenvectors of weight `m ≤ n` lie in the weight-`≤ n` submodule. -/
lemma mem_massWeightLESubmodule_of_forall_massWeightScale {x : JetAlgebra}
    {m n : ℕ} (hmn : m ≤ n)
    (hx : ∀ c : ℂ, massWeightScale c x = c ^ m • x) :
    x ∈ MassWeightLESubmodule n :=
  Submodule.subset_span ⟨m, hmn, hx⟩

/-- Independence of the powers `c ↦ c ^ w`: if a finite combination
  `∑ c ^ w • v w` vanishes for every scalar `c`, then every `v w` vanishes. This
  is what separates the mass-weight components of an element. -/
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
  eigenvectors of the mass-weight scaling. -/
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

/-!

## D. The mass dimension polynomial.

The lepton–gauge-sector jet algebra is the tensor product of the two factors, and mass weights
add under that product, so the mass-weight polynomial of the whole is assembled
from the two factor polynomials: push each into `Polynomial JetAlgebra` along the
tensor inclusions and multiply. On monomials this is exactly
`X ^ a * b ⊗ X ^ c * l ↦ X ^ (a + c) * (b ⊗ l)`.

-/

/-- The mass-weight polynomial on the lepton–gauge-sector jet algebra, assembled from the
  mass-weight polynomials of the two factors. -/
noncomputable def massWeightPoly : JetAlgebra →ₐ[ℂ] Polynomial JetAlgebra :=
  (Algebra.TensorProduct.lift (Polynomial.mapAlgHom inclB)
      (Polynomial.mapAlgHom inclL) commute_mapAlgHom_inclB_inclL).comp
    (Algebra.TensorProduct.map BBoson.JetAlgebra.massWeightPoly
      LeptonSinglet.JetAlgebra.massWeightPoly)

@[simp]
lemma massWeightPoly_tmul (b : ℂ ⊗[ℝ] BBoson.JetAlgebra) (l : LeptonSinglet.JetAlgebra) :
    massWeightPoly (b ⊗ₜ[ℂ] l) =
      Polynomial.mapAlgHom inclB (BBoson.JetAlgebra.massWeightPoly b) *
        Polynomial.mapAlgHom inclL (LeptonSinglet.JetAlgebra.massWeightPoly l) := rfl

end JetAlgebra

end LeptonGaugeSector
