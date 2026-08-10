/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.MassDim
public import Physlib.Relativity.LorentzGroup.FermionicParity
/-!
# Fermionic parity on the lepton–gauge-sector jet algebra

Fermionic parity `-1 ∈ SL(2, ℂ)` projects to the identity Lorentz transformation, so it acts
trivially on everything built from Lorentz vectors — the B-boson factor and the derivative
symbols — and by `-1` on the Weyl spinor of the charged lepton. On the jet algebra it therefore
negates each fermionic generator and fixes each bosonic one.

Since the mass weight of a bosonic generator `∂_s B_μ` is even, `2(1 + |s|)`, and that of a
fermionic generator `∂_s ψ_α` or `∂_s ψ̄_α` is odd, `3 + 2|s|`, fermionic parity acts on a
generator by `(-1)` raised to its mass weight.

-/

@[expose] public section

set_option maxHeartbeats 400000

namespace LeptonGaugeSector
open TensorProduct StandardModel Matrix MatrixGroups LorentzGroup

namespace JetAlgebra

/-!

## A. Fermionic parity on the derivative symbols and the two factors

-/

private lemma fermionicParity_inv : fermionicParity⁻¹ = fermionicParity :=
  inv_eq_of_mul_eq_one_right (by rw [← sq]; exact fermionicParity_sq)

/-- Fermionic parity acts trivially on the dual complex Lorentz covectors. -/
lemma coℂModule_SL2CRep_dual_fermionicParity :
    Lorentz.CoℂModule.SL2CRep.dual fermionicParity = LinearMap.id := by
  rw [Representation.dual_apply, fermionicParity_inv, coℂModule_SL2CRep_fermionicParity]
  ext f x
  simp [Module.Dual.transpose]

/-- Fermionic parity acts trivially on the complex algebra of derivative symbols. -/
lemma derivAlgebraComplex_repLorentzGroup_fermionicParity :
    DerivAlgebraComplex.repLorentzGroup fermionicParity = LinearMap.id := by
  show (SymmetricAlgebra.lift (SymmetricAlgebra.ι ℂ _ ∘ₗ
    Lorentz.CoℂModule.SL2CRep.dual fermionicParity)).toLinearMap = _
  rw [coℂModule_SL2CRep_dual_fermionicParity,
    LinearMap.comp_id (SymmetricAlgebra.ι ℂ (Module.Dual ℂ Lorentz.CoℂModule))]
  refine LinearMap.ext fun x => ?_
  show SymmetricAlgebra.lift (SymmetricAlgebra.ι ℂ _) x = x
  rw [show SymmetricAlgebra.lift (SymmetricAlgebra.ι ℂ (Module.Dual ℂ Lorentz.CoℂModule)) =
    AlgHom.id ℂ _ from SymmetricAlgebra.algHom_ext (by ext y; simp)]
  rfl

/-- Fermionic parity acts trivially on the real Lorentz covectors. -/
lemma coVector_sl2Rep_fermionicParity :
    Lorentz.CoVector.sl2Rep fermionicParity = LinearMap.id := by
  show (Lorentz.CoVector.rep (Lorentz.SL2C.toLorentzGroup fermionicParity)) = _
  rw [toLorentzGroup_fermionicParity, map_one]
  rfl

lemma coVector_sl2Rep_dual_fermionicParity :
    Lorentz.CoVector.sl2Rep.dual fermionicParity = LinearMap.id := by
  rw [Representation.dual_apply, fermionicParity_inv, coVector_sl2Rep_fermionicParity]
  ext f x
  simp [Module.Dual.transpose]

/-- Fermionic parity acts trivially on the real algebra of derivative symbols. -/
lemma derivAlgebraReal_repLorentzGroup_fermionicParity :
    DerivAlgebraReal.repLorentzGroup fermionicParity = LinearMap.id := by
  show (SymmetricAlgebra.lift (SymmetricAlgebra.ι ℝ _ ∘ₗ
    Lorentz.CoVector.sl2Rep.dual fermionicParity)).toLinearMap = _
  rw [coVector_sl2Rep_dual_fermionicParity,
    LinearMap.comp_id (SymmetricAlgebra.ι ℝ (Module.Dual ℝ Lorentz.CoVector))]
  refine LinearMap.ext fun x => ?_
  show SymmetricAlgebra.lift (SymmetricAlgebra.ι ℝ _) x = x
  rw [show SymmetricAlgebra.lift (SymmetricAlgebra.ι ℝ (Module.Dual ℝ Lorentz.CoVector)) =
    AlgHom.id ℝ _ from SymmetricAlgebra.algHom_ext (by ext y; simp)]
  rfl

/-!

## B. Fermionic parity on the B-boson factor

The B boson is a Lorentz vector, so fermionic parity leaves the whole bosonic factor alone.

-/

lemma bBoson_repLorentzGroup_fermionicParity :
    BBoson.repLorentzGroup fermionicParity = LinearMap.id := by
  show (BBoson.valLinEquiv.symm.toLinearMap ∘ₗ
    TensorProduct.map (Lorentz.CoVector.rep (Lorentz.SL2C.toLorentzGroup fermionicParity))
      (Representation.trivial ℝ (SL(2,ℂ)) (selfAdjoint ℂ) fermionicParity) ∘ₗ
    BBoson.valLinEquiv.toLinearMap) = _
  rw [toLorentzGroup_fermionicParity, map_one]
  ext F
  simp [Module.End.one_eq_id, TensorProduct.map_id]

lemma bBoson_repLorentzGroup_dual_fermionicParity :
    BBoson.repLorentzGroup.dual fermionicParity = LinearMap.id := by
  rw [Representation.dual_apply, fermionicParity_inv, bBoson_repLorentzGroup_fermionicParity]
  ext f x
  simp [Module.Dual.transpose]

lemma bBoson_jetComponentSpace_repLorentzGroup_fermionicParity :
    BBoson.JetComponentSpace.repLorentzGroup fermionicParity = LinearMap.id := by
  show (TensorProduct.map (DerivAlgebraReal.repLorentzGroup fermionicParity)
    (BBoson.repLorentzGroup.dual fermionicParity)) = _
  rw [derivAlgebraReal_repLorentzGroup_fermionicParity,
    bBoson_repLorentzGroup_dual_fermionicParity, TensorProduct.map_id]

/-!

## C. Fermionic parity on the charged-lepton factor

The lepton is a Weyl spinor, so fermionic parity acts on the component space by `-1`, and hence
negates each fermionic generator of the exterior algebra.

-/

lemma leptonSinglet_repLorentzGroup_fermionicParity :
    LeptonSinglet.repLorentzGroup fermionicParity = -LinearMap.id := by
  show (LeptonSinglet.valLinEquiv.symm.toLinearMap ∘ₗ
    Fermion.RightHandedWeyl.rep fermionicParity ∘ₗ
      LeptonSinglet.valLinEquiv.toLinearMap) = _
  rw [rightHandedWeyl_rep_fermionicParity]
  ext l
  simp

lemma leptonSinglet_repLorentzGroup_dual_fermionicParity :
    LeptonSinglet.repLorentzGroup.dual fermionicParity = -LinearMap.id := by
  rw [Representation.dual_apply, fermionicParity_inv,
    leptonSinglet_repLorentzGroup_fermionicParity]
  ext f x
  simp [Module.Dual.transpose]

lemma leptonSinglet_repLorentzGroup_conj_fermionicParity :
    LeptonSinglet.repLorentzGroup.conj fermionicParity = -LinearMap.id := by
  ext m
  rw [Representation.conj_apply, leptonSinglet_repLorentzGroup_fermionicParity]
  simp

lemma leptonSinglet_repLorentzGroup_conj_dual_fermionicParity :
    LeptonSinglet.repLorentzGroup.conj.dual fermionicParity = -LinearMap.id := by
  rw [Representation.dual_apply, fermionicParity_inv,
    leptonSinglet_repLorentzGroup_conj_fermionicParity]
  ext f x
  simp [Module.Dual.transpose]

/-- Fermionic parity acts by `-1` on every lepton component function, at every derivative
  order at once: the derivative symbols are inert and the spinor index carries the sign. -/
lemma leptonSinglet_jetComponentSpace_repLorentzGroup_fermionicParity :
    LeptonSinglet.JetComponentSpace.repLorentzGroup fermionicParity = -LinearMap.id := by
  show LinearMap.prodMap
      (TensorProduct.map (DerivAlgebraComplex.repLorentzGroup fermionicParity)
        (LeptonSinglet.repLorentzGroup.dual fermionicParity))
      (TensorProduct.map (DerivAlgebraComplex.repLorentzGroup fermionicParity)
        (LeptonSinglet.repLorentzGroup.conj.dual fermionicParity)) = _
  rw [derivAlgebraComplex_repLorentzGroup_fermionicParity,
    leptonSinglet_repLorentzGroup_dual_fermionicParity,
    leptonSinglet_repLorentzGroup_conj_dual_fermionicParity]
  have h1 : TensorProduct.map (LinearMap.id : DerivAlgebraComplex →ₗ[ℂ] DerivAlgebraComplex)
      (-LinearMap.id : Module.Dual ℂ LeptonSinglet →ₗ[ℂ] Module.Dual ℂ LeptonSinglet) =
      -LinearMap.id := by
    refine TensorProduct.ext' fun a b => ?_
    simp [TensorProduct.tmul_neg]
  have h2 : TensorProduct.map (LinearMap.id : DerivAlgebraComplex →ₗ[ℂ] DerivAlgebraComplex)
      (-LinearMap.id : Module.Dual ℂ (ConjModule LeptonSinglet) →ₗ[ℂ]
        Module.Dual ℂ (ConjModule LeptonSinglet)) = -LinearMap.id := by
    refine TensorProduct.ext' fun a b => ?_
    simp [TensorProduct.tmul_neg]
  rw [h1, h2]
  refine LinearMap.ext fun x => Prod.ext ?_ ?_ <;> simp


/-!

## D. Checking algebra maps on the generators

Two algebra maps out of the jet algebra that agree on every generator are equal. The bosonic
factor is a symmetric algebra and the fermionic one an exterior algebra, both on spaces with a
distinguished basis indexed by the generators, so each factor is handled by its own induction
principle. `Algebra.TensorProduct.ext` is not usable here: the bosonic factor is itself an
`ℝ`-tensor product, so that lemma demands an `IsScalarTower ℝ ℂ A` on the target.

-/

/-- Two algebra maps out of the jet algebra agreeing on the bosonic factor. -/
private lemma algHom_eq_on_inclB {A : Type} [Ring A] [Algebra ℂ A]
    {f g : JetAlgebra →ₐ[ℂ] A} (h : ∀ j : JetGenerators, f [j]ₐ = g [j]ₐ)
    (a : ℂ ⊗[ℝ] BBoson.JetAlgebra) : f (inclB a) = g (inclB a) := by
  have hone : ∀ c : BBoson.JetAlgebra,
      f (inclB ((1 : ℂ) ⊗ₜ[ℝ] c)) = g (inclB ((1 : ℂ) ⊗ₜ[ℝ] c)) := by
    intro c
    induction c using SymmetricAlgebra.induction with
    | algebraMap r =>
      rw [show ((1 : ℂ) ⊗ₜ[ℝ] (algebraMap ℝ BBoson.JetAlgebra r) :
            ℂ ⊗[ℝ] BBoson.JetAlgebra) =
          algebraMap ℂ (ℂ ⊗[ℝ] BBoson.JetAlgebra) (algebraMap ℝ ℂ r) from by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
          TensorProduct.tmul_smul, TensorProduct.smul_tmul']
        rfl, AlgHom.commutes, AlgHom.commutes, AlgHom.commutes]
    | ι v =>
      have hv : v ∈ Submodule.span ℝ (Set.range BBoson.JetComponentSpace.basis) := by
        rw [BBoson.JetComponentSpace.basis.span_eq]
        trivial
      induction hv using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        obtain ⟨s, μ⟩ := j
        exact h (JetGenerators.dB s μ)
      | zero => simp
      | add u w _ _ ihu ihw =>
        simp only [map_add, TensorProduct.tmul_add]
        rw [ihu, ihw]
      | smul r u _ ihu =>
        have hs : ((1 : ℂ) ⊗ₜ[ℝ]
            (SymmetricAlgebra.ι ℝ BBoson.JetComponentSpace (r • u)) :
            ℂ ⊗[ℝ] BBoson.JetAlgebra) =
            (algebraMap ℝ ℂ r) • ((1 : ℂ) ⊗ₜ[ℝ]
              SymmetricAlgebra.ι ℝ BBoson.JetComponentSpace u) := by
          rw [map_smul, TensorProduct.tmul_smul, ← algebraMap_smul ℂ r]
        rw [hs]
        simp only [map_smul]
        rw [ihu]
    | mul u v ihu ihv =>
      rw [show ((1 : ℂ) ⊗ₜ[ℝ] (u * v) : ℂ ⊗[ℝ] BBoson.JetAlgebra) =
          ((1 : ℂ) ⊗ₜ[ℝ] u) * ((1 : ℂ) ⊗ₜ[ℝ] v) from by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]]
      simp only [map_mul]
      rw [ihu, ihv]
    | add u v ihu ihv =>
      simp only [TensorProduct.tmul_add, map_add]
      rw [ihu, ihv]
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]
  | tmul z c =>
    rw [show (z ⊗ₜ[ℝ] c : ℂ ⊗[ℝ] BBoson.JetAlgebra) = z • ((1 : ℂ) ⊗ₜ[ℝ] c) from by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, map_smul, map_smul,
      hone c]

/-- Two algebra maps out of the jet algebra agreeing on the fermionic factor. -/
private lemma algHom_eq_on_inclL {A : Type} [Ring A] [Algebra ℂ A]
    {f g : JetAlgebra →ₐ[ℂ] A} (h : ∀ j : JetGenerators, f [j]ₐ = g [j]ₐ)
    (b : LeptonSinglet.JetAlgebra) : f (inclL b) = g (inclL b) := by
  have hcomp : f.comp inclL = g.comp inclL := by
    refine ExteriorAlgebra.hom_ext (LinearMap.ext fun m => ?_)
    have hm : m ∈ Submodule.span ℂ (Set.range LeptonSinglet.JetComponentSpace.basis) := by
      rw [LeptonSinglet.JetComponentSpace.basis.span_eq]
      trivial
    induction hm using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      cases j with
      | dψ s α => exact h (JetGenerators.dψ s α)
      | dbarψ s α => exact h (JetGenerators.dbarψ s α)
    | zero => simp
    | add u v _ _ ihu ihv =>
      simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
        map_add] at ihu ihv ⊢
      rw [ihu, ihv]
    | smul c u _ ihu =>
      simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
        map_smul] at ihu ⊢
      rw [ihu]
  exact AlgHom.congr_fun hcomp b

/-- Two algebra maps out of the jet algebra agreeing on every generator are equal. -/
lemma algHom_ext {A : Type} [Ring A] [Algebra ℂ A] {f g : JetAlgebra →ₐ[ℂ] A}
    (h : ∀ j : JetGenerators, f [j]ₐ = g [j]ₐ) : f = g := by
  refine AlgHom.ext fun x => ?_
  induction x using JetAlgebra.induction_on with
  | zero => simp
  | add u v hu hv => rw [map_add, map_add, hu, hv]
  | tmul a b =>
    rw [tmul_eq_inclB_mul_inclL, map_mul, map_mul, algHom_eq_on_inclB h,
      algHom_eq_on_inclL h]


/-!

## E. Fermionic parity acts by `(-1)` to the mass weight

-/

private lemma tmul_neg' (a : ℂ ⊗[ℝ] BBoson.JetAlgebra) (b : LeptonSinglet.JetAlgebra) :
    a ⊗ⱼ (-b) = -(a ⊗ⱼ b) := TensorProduct.tmul_neg a b

lemma bBoson_jetAlgebra_repLorentzGroup_fermionicParity :
    BBoson.JetAlgebra.repLorentzGroup fermionicParity = LinearMap.id := by
  show (SymmetricAlgebra.lift (SymmetricAlgebra.ι ℝ _ ∘ₗ
    BBoson.JetComponentSpace.repLorentzGroup fermionicParity)).toLinearMap = _
  rw [bBoson_jetComponentSpace_repLorentzGroup_fermionicParity,
    LinearMap.comp_id (SymmetricAlgebra.ι ℝ BBoson.JetComponentSpace)]
  refine LinearMap.ext fun x => ?_
  show SymmetricAlgebra.lift (SymmetricAlgebra.ι ℝ _) x = x
  rw [show SymmetricAlgebra.lift (SymmetricAlgebra.ι ℝ BBoson.JetComponentSpace) =
    AlgHom.id ℝ _ from SymmetricAlgebra.algHom_ext (by ext y; simp)]
  rfl

lemma bBoson_jetAlgebra_complexRepLorentzGroup_fermionicParity :
    BBoson.JetAlgebra.complexRepLorentzGroup fermionicParity = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => rw [map_add, hu, hv]; simp
  | tmul z b =>
    show z ⊗ₜ[ℝ] BBoson.JetAlgebra.repLorentzGroup fermionicParity b = _
    rw [bBoson_jetAlgebra_repLorentzGroup_fermionicParity]
    rfl

/-- Fermionic parity negates every fermionic generator. -/
lemma leptonSinglet_jetAlgebra_repLorentzGroup_fermionicParity_ofGenerator
    (j : LeptonSinglet.JetGenerators) :
    LeptonSinglet.JetAlgebra.repLorentzGroup fermionicParity
        (LeptonSinglet.JetAlgebra.ofGenerator j) =
      -LeptonSinglet.JetAlgebra.ofGenerator j := by
  rw [LeptonSinglet.JetAlgebra.repLorentzGroup_ofGenerator,
    leptonSinglet_jetComponentSpace_repLorentzGroup_fermionicParity]
  simp [LeptonSinglet.JetAlgebra.ofGenerator]

/-- Fermionic parity acts on each generator by `(-1)` raised to its mass weight: bosonic
  generators have even weight and are fixed, fermionic generators have odd weight and are
  negated. -/
lemma repLorentzGroup_fermionicParity_ofGenerator (j : JetGenerators) :
    repLorentzGroup fermionicParity [j]ₐ = (-1 : ℂ) ^ MassWeight j • [j]ₐ := by
  cases j with
  | dB s μ =>
    rw [ofGenerator_B_eq, repLorentzGroup_tmul,
      bBoson_jetAlgebra_complexRepLorentzGroup_fermionicParity,
      show LeptonSinglet.JetAlgebra.repLorentzGroup fermionicParity
        (1 : LeptonSinglet.JetAlgebra) = 1 from
        LeptonSinglet.JetAlgebra.repLorentzGroup_apply_one fermionicParity,
      show MassWeight (JetGenerators.dB s μ) = 2 * (1 + Multiset.card s) from rfl,
      Even.neg_one_pow ⟨1 + Multiset.card s, by ring⟩, one_smul]
    rfl
  | dψ s α =>
    rw [ofGenerator_dψ_eq, repLorentzGroup_tmul,
      leptonSinglet_jetAlgebra_repLorentzGroup_fermionicParity_ofGenerator,
      show MassWeight (JetGenerators.dψ s α) = 3 + 2 * Multiset.card s from rfl,
      Odd.neg_one_pow ⟨1 + Multiset.card s, by ring⟩, neg_one_smul]
    rw [show (BBoson.JetAlgebra.complexRepLorentzGroup fermionicParity)
        ((1 : ℂ) ⊗ₜ[ℝ] (1 : BBoson.JetAlgebra)) = (1 : ℂ) ⊗ₜ[ℝ] (1 : BBoson.JetAlgebra) from by
      rw [bBoson_jetAlgebra_complexRepLorentzGroup_fermionicParity]; rfl, tmul_neg']
  | dbarψ s α =>
    rw [ofGenerator_dbarψ_eq, repLorentzGroup_tmul,
      leptonSinglet_jetAlgebra_repLorentzGroup_fermionicParity_ofGenerator,
      show MassWeight (JetGenerators.dbarψ s α) = 3 + 2 * Multiset.card s from rfl,
      Odd.neg_one_pow ⟨1 + Multiset.card s, by ring⟩, neg_one_smul]
    rw [show (BBoson.JetAlgebra.complexRepLorentzGroup fermionicParity)
        ((1 : ℂ) ⊗ₜ[ℝ] (1 : BBoson.JetAlgebra)) = (1 : ℂ) ⊗ₜ[ℝ] (1 : BBoson.JetAlgebra) from by
      rw [bBoson_jetAlgebra_complexRepLorentzGroup_fermionicParity]; rfl, tmul_neg']

/-- Evaluation of a mass-weight polynomial at a scalar. -/
private noncomputable def evalAt (c : ℂ) : Polynomial JetAlgebra →ₐ[ℂ] JetAlgebra :=
  Polynomial.eval₂AlgHom (AlgHom.id ℂ JetAlgebra) (algebraMap ℂ JetAlgebra c)
    fun a => (Algebra.commutes c a).symm

private lemma evalAt_monomial (c : ℂ) (n : ℕ) (y : JetAlgebra) :
    evalAt c (Polynomial.monomial n y) = c ^ n • y := by
  show Polynomial.eval₂ (AlgHom.id ℂ JetAlgebra).toRingHom
    (algebraMap ℂ JetAlgebra c) (Polynomial.monomial n y) = _
  rw [Polynomial.eval₂_monomial, ← map_pow, ← Algebra.commutes, ← Algebra.smul_def]
  rfl

/-- Fermionic parity is the mass-weight polynomial evaluated at `-1`. -/
private lemma repLorentzGroupAlgHom_fermionicParity :
    repLorentzGroupAlgHom fermionicParity = (evalAt (-1)).comp massWeightPoly := by
  refine algHom_ext fun j => ?_
  show repLorentzGroup fermionicParity [j]ₐ = evalAt (-1) (massWeightPoly [j]ₐ)
  rw [repLorentzGroup_fermionicParity_ofGenerator, massWeightPoly_ofGenerator,
    evalAt_monomial]

/-- On an element of mass weight `n`, fermionic parity acts by `(-1) ^ n`. -/
lemma repLorentzGroup_fermionicParity_of_mem_massWeightSubmodule {n : ℕ} {x : JetAlgebra}
    (hx : x ∈ massWeightSubmodule n) :
    repLorentzGroup fermionicParity x = (-1 : ℂ) ^ n • x := by
  have h := AlgHom.congr_fun repLorentzGroupAlgHom_fermionicParity x
  show repLorentzGroup fermionicParity x = _
  rw [show repLorentzGroup fermionicParity x = repLorentzGroupAlgHom fermionicParity x from rfl,
    h, AlgHom.comp_apply, mem_massWeightSubmodule.mp hx, evalAt_monomial]

/-!

## F. The selection rule

-/

/-- **No invariant has odd mass weight.** An element of odd mass weight that is invariant under
  the Lorentz group vanishes: fermionic parity fixes it, being a Lorentz transformation, while
  acting on it by `-1`, since its mass weight is odd. Physically: a Lagrangian term must contain
  an even number of fermions. -/
theorem eq_zero_of_odd_massWeight_of_forall_repLorentzGroup_eq {n : ℕ} (hn : Odd n)
    {x : JetAlgebra} (hx : x ∈ massWeightSubmodule n)
    (hinv : ∀ Λ : SL(2,ℂ), repLorentzGroup Λ x = x) : x = 0 := by
  have h1 : x = (-1 : ℂ) ^ n • x := by
    rw [← repLorentzGroup_fermionicParity_of_mem_massWeightSubmodule hx, hinv]
  rw [hn.neg_one_pow, neg_one_smul] at h1
  have h2 : (2 : ℂ) • x = 0 := by
    calc (2 : ℂ) • x = x + x := two_smul ℂ x
      _ = -x + x := congrArg (· + x) h1
      _ = 0 := neg_add_cancel x
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 two_ne_zero
  · exact h3

/-- An invariant element of odd mass weight vanishes. -/
theorem eq_zero_of_odd_massWeight_of_isInvariant {n : ℕ} (hn : Odd n) {x : JetAlgebra}
    (hx : x ∈ massWeightSubmodule n) (hinv : IsInvariant x) : x = 0 :=
  eq_zero_of_odd_massWeight_of_forall_repLorentzGroup_eq hn hx hinv.2

end JetAlgebra

end LeptonGaugeSector


