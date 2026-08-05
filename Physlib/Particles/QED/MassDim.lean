/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.QED.JetAlgebra
public import Physlib.Relativity.MinkowskiMatrix
public import Physlib.Relativity.PauliMatrices.Basic
/-!
# Mass dimension on the QED jet algebra

-/

@[expose] public section

set_option maxHeartbeats 1000000

namespace QED
open TensorProduct StandardModel

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
    rw [Dψ_cons, massWeightScale_covariantStep, ih, map_smul, smul_smul, ← pow_add,
      List.length_cons, show 3 + 2 * (l.length + 1) = 2 + (3 + 2 * l.length) from by
        omega]

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
    rw [Dbarψ_cons, massWeightScale_covariantStepBar, ih, map_smul, smul_smul,
      ← pow_add, List.length_cons,
      show 3 + 2 * (l.length + 1) = 2 + (3 + 2 * l.length) from by omega]

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


noncomputable def MassDimSubmodule (n : ℕ) : Submodule ℂ JetAlgebra :=
    Submodule.span ℂ { x | ∀ c : ℂ, massWeightScale c x = c ^ n • x }

noncomputable def MassWeightLESubmodule (n : ℕ) : Submodule ℂ JetAlgebra :=
  Submodule.span ℂ {x | ∃ m ≤ n, ∀ c : ℂ, massWeightScale c x = c ^ m • x}

noncomputable def InvariantMassWeightSubmodule (n : ℕ) : Submodule ℂ JetAlgebra :=
  MassWeightLESubmodule n ⊓ InvariantSubmodule

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

/-- The fermion kinetic term `i ψ̄_α (σ^μ)_{α β} (D_μ ψ)_β` of the right-handed
  charged-lepton singlet, with the covariant derivative on the lepton. Mass
  weight eight. -/
noncomputable def fermionKineticTerm : JetAlgebra :=
  Complex.I • ∑ μ, ∑ α, ∑ β, σ μ α β • (Dbarψ [] α * Dψ [μ] β)

/-- The conjugate fermion kinetic term `-i (D̄_μ ψ̄)_α (σ^μ)_{α β} ψ_β`, with the
  covariant derivative on the conjugate lepton. Mass weight eight. -/
noncomputable def fermionKineticTermBar : JetAlgebra :=
  (-Complex.I) • ∑ μ, ∑ α, ∑ β, σ μ α β • (Dbarψ [μ] α * Dψ [] β)

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

set_option maxHeartbeats 4000000 in
/-- The Lorentz action on the QED jet algebra is multiplicative (term-level
  form). -/
lemma repLorentzGroup_mul' (Λ : SL(2,ℂ)) (a b : JetAlgebra) :
    repLorentzGroup Λ (a * b) = repLorentzGroup Λ a * repLorentzGroup Λ b := by
  have happ : ∀ (p : ℂ ⊗[ℝ] BBoson.JetAlgebra) (l : LeptonSinglet.JetAlgebra),
      repLorentzGroup Λ (p ⊗ₜ[ℂ] l) =
        (BBoson.JetAlgebra.complexRepLorentzGroup Λ p) ⊗ₜ[ℂ]
          (LeptonSinglet.JetAlgebra.repLorentzGroup Λ l) := fun p l => rfl
  have hd₁ : ∀ x y z : JetAlgebra, (x + y) * z = x * z + y * z := by grind
  have hd₂ : ∀ x y z : JetAlgebra, x * (y + z) = x * y + x * z := by grind
  have hz₁ : ∀ x : JetAlgebra, 0 * x = 0 := fun x => zero_mul x
  have hz₂ : ∀ x : JetAlgebra, x * 0 = 0 := fun x => mul_zero x
  induction a using TensorProduct.induction_on with
  | zero => rw [hz₁, map_zero, hz₁]
  | add x y hx hy => rw [hd₁, map_add, map_add, hx, hy, hd₁]
  | tmul p l =>
    induction b using TensorProduct.induction_on with
    | zero => rw [hz₂, map_zero, hz₂]
    | add x y hx hy => rw [hd₂, map_add, map_add, hx, hy, hd₂]
    | tmul p' l' =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, happ, happ, happ,
        Algebra.TensorProduct.tmul_mul_tmul,
        BBoson.JetAlgebra.complexRepLorentzGroup_mul,
        LeptonSinglet.JetAlgebra.repLorentzGroup_apply_mul]

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
    rw [repLorentzGroup_mul', repLorentzGroup_fieldStrengthDeriv_nil]
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
  rw [repLorentzGroup_mul', repLorentzGroup_fieldStrengthDeriv_nil,
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

lemma repLorentzGroup_thetaTerm (Λ : SL(2,ℂ)) :
    repLorentzGroup Λ thetaTerm = thetaTerm := by
  -- TODO: expand with `repLorentzGroup_fieldStrengthDeriv_mul`, exchange the
  -- permutation sum with the four index sums, evaluate the alternating
  -- contraction with `sum_perm_sign_mul_prod_eq_det`: it vanishes on
  -- non-injective index tuples (equal rows) and gives `sign q · det Λ = sign q`
  -- on injective ones (`Matrix.det_permute`, `toLorentzGroup_det_one`),
  -- reindexing the surviving tuples by permutations.
  sorry

lemma repLorentzGroup_fermionKineticTerm (Λ : SL(2,ℂ)) :
    repLorentzGroup Λ fermionKineticTerm = fermionKineticTerm := by
  sorry

lemma repLorentzGroup_fermionKineticTermBar (Λ : SL(2,ℂ)) :
    repLorentzGroup Λ fermionKineticTermBar = fermionKineticTermBar := by
  sorry

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
      · by_cases hjk : j = k
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
  -- Completeness: every invariant of mass weight at most eight is a combination
  -- of the four kinetic terms and the constants. TODO: requires (i) the weight
  -- and hypercharge selection rules to reduce to the finite-dimensional space of
  -- weight-`≤ 8`, charge-balanced covariant monomials, via the characterization
  -- `isInvariant_iff_mem_adjoin_invariantGenerators`, and (ii) the classical
  -- invariant theory of the Lorentz group on that space.
  sorry

end JetAlgebra

end QED
