/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.QED.JetAlgebra.LorentzGroup
public import Physlib.Relativity.MinkowskiMatrix
public import Physlib.Relativity.PauliMatrices.Basic
/-!
# Mass dimension on the QED jet algebra

-/

@[expose] public section

namespace QED
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
/-- The mass-dimension scaling on the QED jet algebra: the algebra map
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
@[simp]
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
  have hm : ∀ a b : JetAlgebra, massWeightScale c (a * b) =
      massWeightScale c a * massWeightScale c b := fun a b => map_mul _ a b
  have hgen : massWeightScale c [JetGenerators.dB {} μ]ₐ =
      c ^ 2 • [JetGenerators.dB {} μ]ₐ := by
    rw [massWeightScale_ofGenerator,
      show MassWeight (JetGenerators.dB {} μ) = 2 from rfl]
  simp only [covariantStep, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.mulLeft_apply, map_add, map_smul, massWeightScale_jetDeriv, hm, hgen,
    smul_mul_assoc]
  module

/-- The conjugate covariant step raises the mass weight by two. -/
lemma massWeightScale_covariantStepBar (c : ℂ) (μ : Fin 1 ⊕ Fin 3) (x : JetAlgebra) :
    massWeightScale c (covariantStepBar μ x) =
      c ^ 2 • covariantStepBar μ (massWeightScale c x) := by
  have hm : ∀ a b : JetAlgebra, massWeightScale c (a * b) =
      massWeightScale c a * massWeightScale c b := fun a b => map_mul _ a b
  have hgen : massWeightScale c [JetGenerators.dB {} μ]ₐ =
      c ^ 2 • [JetGenerators.dB {} μ]ₐ := by
    rw [massWeightScale_ofGenerator,
      show MassWeight (JetGenerators.dB {} μ) = 2 from rfl]
  simp only [covariantStepBar, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.mulLeft_apply, map_sub, map_smul, massWeightScale_jetDeriv, hm, hgen,
    smul_mul_assoc]
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
  action on the QED jet algebra. -/
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
  QED jet algebra. -/
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

instance : GradedAlgebra (R := ℂ) (A := JetAlgebra) MassDimSubmodule := sorry

noncomputable def MassWeightLESubmodule (n : ℕ) : Submodule ℂ JetAlgebra :=
  Submodule.span ℂ {x | ∃ m ≤ n, ∀ c : ℂ, massWeightScale c x = c ^ m • x}

noncomputable def InvariantMassWeightSubmodule (n : ℕ) : Submodule ℂ JetAlgebra :=
  MassWeightLESubmodule n ⊓ InvariantSubmodule

end JetAlgebra

end QED
