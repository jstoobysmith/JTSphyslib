/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.Jet
public import Physlib.Relativity.Tensors.ComplexTensor.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Representation
public import Physlib.Relativity.SL2C.Basic
public import Physlib.Mathematics.ConjModule
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Physlib.Particles.LagrangianTheory.Basic
public import Physlib.Mathematics.MvPowerSeriesDerivative
/-!
# The B boson

The hypercharge gauge boson field `B_μ`: the gauge boson of the `U(1)` factor of
the Standard Model gauge group, with one Lorentz index, valued in the
one-dimensional adjoint of `U(1)`, modelled as the real vector space of hermitian
complex numbers.

The physical Z boson and photon are the electroweak-mixed combinations of this
field with the neutral `SU(2)` boson; before mixing, the `U(1)` factor's gauge
boson is the B boson formalized here.

-/

@[expose] public section

/-!

## Aa. The formal partial derivative and the coefficientwise star

The Maurer–Cartan jet series is built from the formal partial derivative
`MvPowerSeries.pderiv`; its hermiticity rests on the fact that the derivative
commutes with the coefficientwise star.

-/

namespace MvPowerSeries

variable {σ R : Type*}

/-- The formal partial derivative commutes with the coefficientwise star. -/
lemma pderiv_star [CommSemiring R] [StarRing R] (ν : σ) (f : MvPowerSeries σ R) :
    pderiv R ν (star f) = star (pderiv R ν f) := by
  ext s
  rw [coeff_pderiv, coeff_star, coeff_star, coeff_pderiv, star_mul']
  congr 1
  simp

end MvPowerSeries

namespace StandardModel

open TensorProduct

/-!

## A. The B-boson field
-/

/-- The target vector space of the B-boson field `B_μ`. It carries one Lorentz
  index, and is valued in the real vector space of hermitian complex numbers,
  corresponding to the adjoint of `U(1)`. -/
@[ext]
structure BBoson where
  /-- The Lorentz index together with the adjoint (hermitian) factor. -/
  val : Lorentz.Vector ⊗[ℝ] selfAdjoint ℂ

namespace BBoson

/-!

## B. Linear structure
-/

def valEquiv : BBoson ≃ Lorentz.Vector ⊗[ℝ] selfAdjoint ℂ where
  toFun := val
  invFun := fun m => ⟨m⟩

noncomputable instance : AddCommGroup BBoson := Equiv.addCommGroup valEquiv

noncomputable instance : Module ℝ BBoson := Equiv.module ℝ valEquiv

/-- The linear identification with the underlying tensor product. -/
def valLinEquiv : BBoson ≃ₗ[ℝ] Lorentz.Vector ⊗[ℝ] selfAdjoint ℂ where
  toFun := val
  invFun := fun m => ⟨m⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp]
lemma valLinEquiv_apply (d : BBoson) : valLinEquiv d = d.val := rfl

lemma valLinEquiv_symm_apply (m : Lorentz.Vector ⊗[ℝ] selfAdjoint ℂ) :
    valLinEquiv.symm m = ⟨m⟩ := rfl

@[simp]
lemma val_add (d₁ d₂ : BBoson) : (d₁ + d₂).val = d₁.val + d₂.val := rfl

@[simp]
lemma val_smul (r : ℝ) (d : BBoson) : (r • d).val = r • d.val := rfl

@[simp]
lemma val_zero : (0 : BBoson).val = 0 := rfl

/-!

## C. Lorentz action

The Lorentz group acts on the Lorentz index and leaves the adjoint factor fixed.
-/

open Matrix MatrixGroups

/-- The Lorentz representation on the B-boson field: the vector action, through the
  covering map `SL(2,ℂ) →* LorentzGroup 3`, on the Lorentz index, and the trivial
  action on the adjoint factor. -/
noncomputable def repLorentzGroup : Representation ℝ (SL(2,ℂ)) BBoson where
  toFun Λ := valLinEquiv.symm.toLinearMap ∘ₗ
    TensorProduct.map (Lorentz.Vector.rep (Lorentz.SL2C.toLorentzGroup Λ))
      (Representation.trivial ℝ (SL(2,ℂ)) (selfAdjoint ℂ) Λ) ∘ₗ
    valLinEquiv.toLinearMap
  map_one' := by
    ext F
    simp [Module.End.one_eq_id]
  map_mul' Λ₁ Λ₂ := by
    ext1 F
    simp [TensorProduct.map_map, Module.End.mul_eq_comp, map_mul]

/-!

## D. Gauge action

The B boson is neutral: the `SU(3)` and `SU(2)` components do not act on it, and
the adjoint action of the abelian `U(1)` component is `A ↦ u * A * ū = A`, which is
trivial. The global gauge group therefore acts trivially.
-/

/-- The (trivial) adjoint action of the unquotiented Standard Model gauge group on
  the B-boson field. -/
noncomputable def repGaugeGroupI : Representation ℝ GaugeGroupI BBoson :=
  Representation.trivial ℝ GaugeGroupI BBoson

@[simp]
lemma repGaugeGroupI_apply (g : GaugeGroupI) (B : BBoson) :
    repGaugeGroupI g B = B := rfl

/-!

## E. Local gauge action through jets

A local gauge transformation acts on the B-boson field through its first-order jet.
Because the adjoint action is trivial, only the inhomogeneous Maurer–Cartan term
survives: `B_μ ↦ B_μ + i (∂_μ u)(0) ū(0)`, where `u` is the `U(1)` power-series
component of the jet. The Maurer–Cartan coefficient is hermitian by unitarity, and
since the group is abelian the cocycle identity degenerates to additivity. The
resulting action of `JetGaugeGroupI` on `BBoson` is by translations.
-/

open MvPowerSeries

/-- The Maurer–Cartan coefficient of a jet of a `U(1)` gauge transformation in the
  spacetime direction `μ`: `i (∂_μ u)(0) ū(0)`, which is hermitian by unitarity. -/
noncomputable def mcCoeff (u : unitary JetRing) (μ : Fin 1 ⊕ Fin 3) : selfAdjoint ℂ :=
  ⟨Complex.I * coeff (Finsupp.single μ 1) (u : JetRing) *
      star (constantCoeff (u : JetRing)), by
    have h := congrArg (coeff (Finsupp.single μ 1)) (Unitary.mem_iff.mp u.2).2
    rw [coeff_single_one_mul, coeff_star, constantCoeff_star,
      show coeff (Finsupp.single μ 1) (1 : JetRing) = 0 by
        rw [coeff_one, if_neg (by simp [Finsupp.single_eq_zero])]] at h
    have hI : (star Complex.I) = -Complex.I := by
      simp [Complex.conj_I]
    rw [selfAdjoint.mem_iff, star_mul', star_mul', star_star, hI]
    linear_combination (-Complex.I) * h⟩

@[simp]
lemma mcCoeff_one (μ : Fin 1 ⊕ Fin 3) : mcCoeff 1 μ = 0 := by
  apply Subtype.ext
  have h : coeff (Finsupp.single μ 1) (1 : JetRing) = 0 := by
    rw [coeff_one, if_neg (by simp [Finsupp.single_eq_zero])]
  simp [mcCoeff, h]

/-- The abelian cocycle identity: the Maurer–Cartan coefficient is additive. -/
lemma mcCoeff_mul (u₁ u₂ : unitary JetRing) (μ : Fin 1 ⊕ Fin 3) :
    mcCoeff (u₁ * u₂) μ = mcCoeff u₁ μ + mcCoeff u₂ μ := by
  have h₁ : constantCoeff (u₁ : JetRing) * star (constantCoeff (u₁ : JetRing)) = 1 := by
    have h := congrArg constantCoeff (Unitary.mem_iff.mp u₁.2).2
    rwa [map_mul, constantCoeff_star, map_one] at h
  have h₂ : constantCoeff (u₂ : JetRing) * star (constantCoeff (u₂ : JetRing)) = 1 := by
    have h := congrArg constantCoeff (Unitary.mem_iff.mp u₂.2).2
    rwa [map_mul, constantCoeff_star, map_one] at h
  apply Subtype.ext
  simp only [mcCoeff, MulMemClass.coe_mul, AddSubgroup.coe_add]
  rw [coeff_single_one_mul, map_mul, star_mul]
  linear_combination (Complex.I * coeff (Finsupp.single μ 1) (u₁ : JetRing) *
      star (constantCoeff (u₁ : JetRing))) * h₂ +
    (Complex.I * coeff (Finsupp.single μ 1) (u₂ : JetRing) *
      star (constantCoeff (u₂ : JetRing))) * h₁

/-- The first-order Taylor coefficient of a hypercharge power of a `U(1)` jet is
  the charge times the Maurer–Cartan coefficient times the value of the character:
  `(∂_μ (ū^q))(0) = q · i (∂_μu)(0)ū(0) · (ū(0))^q`. The abelian connection shift
  controls the first-order transformation of every charged field. -/
lemma coeff_single_star_pow (u : unitary JetRing) (μ : Fin 1 ⊕ Fin 3) (q : ℕ) :
    coeff (Finsupp.single μ 1) ((star (u : JetRing)) ^ q) =
      (q : ℂ) * Complex.I * (mcCoeff u μ : ℂ) *
        constantCoeff ((star (u : JetRing)) ^ q) := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    rw [pow_zero, show coeff (Finsupp.single μ 1) (1 : JetRing) = 0 by
      rw [coeff_one, if_neg (by simp [Finsupp.single_eq_zero])]]
    simp
  · have h := congrArg (coeff (Finsupp.single μ 1)) (Unitary.mem_iff.mp u.2).2
    rw [coeff_single_one_mul, coeff_star, constantCoeff_star,
      show coeff (Finsupp.single μ 1) (1 : JetRing) = 0 by
        rw [coeff_one, if_neg (by simp [Finsupp.single_eq_zero])]] at h
    have hB : constantCoeff (u : JetRing) * star (constantCoeff (u : JetRing)) = 1 := by
      have h' := congrArg constantCoeff (Unitary.mem_iff.mp u.2).2
      rwa [map_mul, constantCoeff_star, map_one] at h'
    have hσA : star (coeff (Finsupp.single μ 1) (u : JetRing)) =
        -(coeff (Finsupp.single μ 1) (u : JetRing) *
          star (constantCoeff (u : JetRing)) * star (constantCoeff (u : JetRing))) := by
      linear_combination star (constantCoeff (u : JetRing)) * h -
        star (coeff (Finsupp.single μ 1) (u : JetRing)) * hB
    have hpow : star (constantCoeff (u : JetRing)) ^ (q - 1) *
        star (constantCoeff (u : JetRing)) = star (constantCoeff (u : JetRing)) ^ q := by
      rw [← pow_succ, Nat.sub_add_cancel hq]
    rw [coeff_single_one_pow, coeff_star, constantCoeff_star, map_pow, constantCoeff_star,
      hσA, show ((mcCoeff u μ : ℂ)) = Complex.I *
        coeff (Finsupp.single μ 1) (u : JetRing) *
        star (constantCoeff (u : JetRing)) from rfl,
      show (q : ℂ) * star (constantCoeff (u : JetRing)) ^ (q - 1) *
        -(coeff (Finsupp.single μ 1) (u : JetRing) *
          star (constantCoeff (u : JetRing)) * star (constantCoeff (u : JetRing))) =
        -((q : ℂ) * coeff (Finsupp.single μ 1) (u : JetRing) *
          ((star (constantCoeff (u : JetRing)) ^ (q - 1) *
            star (constantCoeff (u : JetRing))) * star (constantCoeff (u : JetRing))))
        from by ring, hpow]
    ring_nf
    rw [Complex.I_sq]
    ring

/-- The Maurer–Cartan term of a jet of a `U(1)` gauge transformation, as a B-boson:
  the translation part of the local gauge action, with components
  `i (∂_μ u)(0) ū(0)`. -/
noncomputable def mcBBoson (u : unitary JetRing) : BBoson :=
  ⟨∑ μ, Lorentz.Vector.basis μ ⊗ₜ[ℝ] mcCoeff u μ⟩

@[simp]
lemma mcBBoson_one : mcBBoson 1 = 0 := by
  apply BBoson.ext
  simp [mcBBoson]

/-- The Maurer–Cartan term is additive in the jet. -/
lemma mcBBoson_mul (u₁ u₂ : unitary JetRing) :
    mcBBoson (u₁ * u₂) = mcBBoson u₁ + mcBBoson u₂ := by
  apply BBoson.ext
  simp [mcBBoson, mcCoeff_mul, TensorProduct.tmul_add, Finset.sum_add_distrib]

/-- The action of the jet gauge group on the B-boson field: the adjoint action is
  trivial, so a jet of gauge transformations acts purely by the Maurer–Cartan
  translation `B_μ ↦ B_μ + i (∂_μ u)(0) ū(0)` of its `U(1)` component. The action
  is affine rather than linear, which is why it is a `MulAction` and not a
  `Representation`. -/
noncomputable instance : MulAction JetGaugeGroupI BBoson where
  smul U B := B + mcBBoson U.2.2
  one_smul B := by
    show B + mcBBoson (1 : JetGaugeGroupI).2.2 = B
    simp
  mul_smul U V B := by
    show B + mcBBoson (U * V).2.2 = (B + mcBBoson V.2.2) + mcBBoson U.2.2
    rw [show (U * V).2.2 = U.2.2 * V.2.2 from rfl, mcBBoson_mul]
    abel

lemma smul_def (U : JetGaugeGroupI) (B : BBoson) : U • B = B + mcBBoson U.2.2 := rfl

/-- The jets of constant (global) gauge transformations act trivially on the B
  boson, in agreement with the trivial adjoint representation `repGaugeGroupI`: the
  Maurer–Cartan term vanishes on constant jets. -/
@[simp]
lemma ofConstant_smul (g : GaugeGroupI) (B : BBoson) :
    JetGaugeGroupI.ofConstant g • B = B := by
  rw [smul_def]
  have hmc : ∀ μ, mcCoeff (JetGaugeGroupI.ofConstant g).2.2 μ = 0 := by
    intro μ
    apply Subtype.ext
    have h : coeff (Finsupp.single μ 1)
        (((JetGaugeGroupI.ofConstant g).2.2 : unitary JetRing) : JetRing) = 0 := by
      rw [show (((JetGaugeGroupI.ofConstant g).2.2 : unitary JetRing) : JetRing) =
          MvPowerSeries.C ((g.2.2 : ℂ)) from rfl,
        coeff_C, if_neg (by simp [Finsupp.single_eq_zero])]
    simp [mcCoeff, h]
  have h0 : mcBBoson (JetGaugeGroupI.ofConstant g).2.2 = 0 := by
    apply BBoson.ext
    simp [mcBBoson, hmc]
  rw [h0, add_zero]

/-!

## The Maurer–Cartan jet series

The local gauge transformation of the B-boson field is the translation
`B_μ ↦ B_μ + i (∂_μ u) ū`, so a jet of gauge transformations shifts every
derivative coordinate `∂_s B_μ` of the field by the corresponding derivative
`∂_s (i ∂_μ u ū)(0)` of the Maurer–Cartan form at the base point. The
Maurer–Cartan coefficient `mcCoeff` records only the zeroth of these shifts —
enough for the action on the field itself, but not for the action on its jets.

To express the shift of every derivative coordinate uniformly we define here the
full jet of the Maurer–Cartan form of a `U(1)` jet: the formal power series
`i (∂_ν u) ū`, whose value at the base point is `mcCoeff` and whose higher Taylor
coefficients are the higher shifts. Its coefficients are hermitian, and it is
additive in the jet; these two facts make the induced shift of the B-boson
component functions a real-valued cocycle, which is what turns the substitution
`B ↦ B + i (∂u) ū` into a representation of the jet gauge group on the jet
algebra below.

-/

/-- The Maurer–Cartan power series of a jet of a `U(1)` gauge transformation in
  the spacetime direction `ν`: the formal power series `i (∂_ν u) ū`, whose
  constant coefficient is the Maurer–Cartan coefficient `mcCoeff`. -/
noncomputable def mcSeries (u : unitary JetRing) (ν : Fin 1 ⊕ Fin 3) : JetRing :=
  (MvPowerSeries.C Complex.I : JetRing) * (pderiv ℂ ν (u : JetRing) * star (u : JetRing))

@[simp]
lemma mcSeries_one (ν : Fin 1 ⊕ Fin 3) : mcSeries 1 ν = 0 := by
  simp [mcSeries]

/-- The Maurer–Cartan series is additive in the jet: the abelian cocycle identity
  at the level of full jets. -/
lemma mcSeries_mul (u v : unitary JetRing) (ν : Fin 1 ⊕ Fin 3) :
    mcSeries (u * v) ν = mcSeries u ν + mcSeries v ν := by
  have hu : (u : JetRing) * star (u : JetRing) = 1 := (Unitary.mem_iff.mp u.2).2
  have hv : (v : JetRing) * star (v : JetRing) = 1 := (Unitary.mem_iff.mp v.2).2
  simp only [mcSeries, MulMemClass.coe_mul, Derivation.leibniz, smul_eq_mul, star_mul',
    ← mul_add]
  congr 1
  linear_combination (pderiv ℂ ν (u : JetRing) * star (u : JetRing)) * hv +
    (pderiv ℂ ν (v : JetRing) * star (v : JetRing)) * hu

/-- The Maurer–Cartan series is hermitian: `star (i (∂_ν u) ū) = i (∂_ν u) ū`,
  by differentiating the unitarity relation `u ū = 1`. All its Taylor
  coefficients are therefore real. -/
lemma star_mcSeries (u : unitary JetRing) (ν : Fin 1 ⊕ Fin 3) :
    star (mcSeries u ν) = mcSeries u ν := by
  have hu : (u : JetRing) * star (u : JetRing) = 1 := (Unitary.mem_iff.mp u.2).2
  have h0 : pderiv ℂ ν ((u : JetRing) * star (u : JetRing)) = 0 := by
    rw [hu, pderiv_one]
  rw [Derivation.leibniz] at h0
  simp only [smul_eq_mul] at h0
  have hq : pderiv ℂ ν (star (u : JetRing)) * (u : JetRing) =
      -(pderiv ℂ ν (u : JetRing) * star (u : JetRing)) := by
    linear_combination h0
  rw [mcSeries, star_mul', star_C, star_mul', star_star, ← pderiv_star, hq,
    show (star Complex.I) = -Complex.I by simp, map_neg, neg_mul, mul_neg, neg_neg]

/-- The Taylor coefficients of the Maurer–Cartan series, as hermitian scalars. -/
noncomputable def mcSeriesCoeff (u : unitary JetRing) (ν : Fin 1 ⊕ Fin 3)
    (m : (Fin 1 ⊕ Fin 3) →₀ ℕ) : selfAdjoint ℂ :=
  ⟨coeff m (mcSeries u ν), by
    rw [selfAdjoint.mem_iff, ← coeff_star, star_mcSeries]⟩

@[simp]
lemma mcSeriesCoeff_one (ν : Fin 1 ⊕ Fin 3) (m : (Fin 1 ⊕ Fin 3) →₀ ℕ) :
    mcSeriesCoeff 1 ν m = 0 := by
  apply Subtype.ext
  simp [mcSeriesCoeff]

/-- The Taylor coefficients of the Maurer–Cartan series are additive in the jet. -/
lemma mcSeriesCoeff_mul (u v : unitary JetRing) (ν : Fin 1 ⊕ Fin 3)
    (m : (Fin 1 ⊕ Fin 3) →₀ ℕ) :
    mcSeriesCoeff (u * v) ν m = mcSeriesCoeff u ν m + mcSeriesCoeff v ν m := by
  apply Subtype.ext
  simp [mcSeriesCoeff, mcSeries_mul]

/-- The zeroth Taylor coefficient of the Maurer–Cartan series is the
  Maurer–Cartan coefficient. -/
lemma mcSeriesCoeff_zero (u : unitary JetRing) (ν : Fin 1 ⊕ Fin 3) :
    mcSeriesCoeff u ν 0 = mcCoeff u ν := by
  apply Subtype.ext
  show coeff 0 (mcSeries u ν) = _
  rw [mcSeries, coeff_zero_eq_constantCoeff, map_mul, map_mul, constantCoeff_C,
    show constantCoeff (pderiv ℂ ν (u : JetRing)) =
      coeff (Finsupp.single ν (1 : ℕ)) (u : JetRing) from by
      rw [← coeff_zero_eq_constantCoeff, coeff_pderiv]
      simp,
    constantCoeff_star, ← mul_assoc]
  rfl

/-!

## The Jet component vector space

-/

abbrev JetComponentSpace :=
  SymmetricAlgebra ℝ (Module.Dual ℝ Lorentz.CoVector) ⊗[ℝ] Module.Dual ℝ BBoson

/-!

## The Maurer–Cartan shift of the component functions

-/

open LagrangianTheory

/-- The Maurer–Cartan jet of a `U(1)` jet evaluated on the derivative symbols:
  the basis monomial of dual derivative symbols at the multi-index `m` is sent to
  the B-boson-valued `m`-th derivative of the Maurer–Cartan series at the base
  point. This is the amount by which the corresponding derivative coordinate of
  the B boson is shifted under the jet gauge transformation. -/
noncomputable def mcJet (u : unitary JetRing) :
    SymmetricAlgebra ℝ (Module.Dual ℝ Lorentz.CoVector) →ₗ[ℝ] BBoson :=
  Lorentz.CoVector.basis.dualBasis.symmetricAlgebra.constr ℝ fun m =>
    ⟨∑ ν, Lorentz.Vector.basis ν ⊗ₜ[ℝ]
      ((∏ μ, Nat.factorial (m μ)) • mcSeriesCoeff u ν m)⟩

@[simp]
lemma mcJet_one : mcJet 1 = 0 := by
  refine Lorentz.CoVector.basis.dualBasis.symmetricAlgebra.ext fun m => ?_
  rw [mcJet, Module.Basis.constr_basis]
  apply BBoson.ext
  simp

/-- The Maurer–Cartan jet is additive in the jet: the abelian cocycle identity
  for the shift of the component functions. -/
lemma mcJet_mul (u v : unitary JetRing) : mcJet (u * v) = mcJet u + mcJet v := by
  refine Lorentz.CoVector.basis.dualBasis.symmetricAlgebra.ext fun m => ?_
  rw [LinearMap.add_apply, mcJet, mcJet, mcJet, Module.Basis.constr_basis,
    Module.Basis.constr_basis, Module.Basis.constr_basis]
  apply BBoson.ext
  simp [mcSeriesCoeff_mul, smul_add, TensorProduct.tmul_add, Finset.sum_add_distrib]

/-- The Maurer–Cartan pairing: the amount by which a component function of the
  B-boson jet is shifted under a jet gauge transformation, i.e. the evaluation of
  the component function against the Maurer–Cartan jet. -/
noncomputable def mcPairing (u : unitary JetRing) : JetComponentSpace →ₗ[ℝ] ℝ :=
  TensorProduct.lift ((Module.Dual.eval ℝ BBoson).comp (mcJet u))

@[simp]
lemma mcPairing_tmul (u : unitary JetRing)
    (p : SymmetricAlgebra ℝ (Module.Dual ℝ Lorentz.CoVector))
    (φ : Module.Dual ℝ BBoson) :
    mcPairing u (p ⊗ₜ[ℝ] φ) = φ (mcJet u p) := rfl

@[simp]
lemma mcPairing_one : mcPairing 1 = 0 := by
  refine TensorProduct.ext' fun p φ => ?_
  simp

/-- The Maurer–Cartan pairing is additive in the jet. -/
lemma mcPairing_mul (u v : unitary JetRing) :
    mcPairing (u * v) = mcPairing u + mcPairing v := by
  refine TensorProduct.ext' fun p φ => ?_
  simp [mcJet_mul]

/-!

## The jet algebra and the jet gauge action

-/

/-- The jet algebra of the B boson: the commutative algebra generated by the
  component functions of the B-boson field and its derivative coordinates. -/
abbrev JetAlgebra : Type := SymmetricAlgebra ℝ JetComponentSpace

namespace JetAlgebra

/-- The action of the jet gauge group on the jet algebra of the B boson. The
  adjoint action is trivial and the local gauge action is the Maurer–Cartan
  translation, whose linear part is the identity; consequently no information is
  carried by a linear action on the component space itself, and the action lives
  on the unital algebra: a jet of gauge transformations acts as the substitution
  automorphism sending each generator `x` to `x + ⟨mc, x⟩ 1`, the pullback of the
  translation `B ↦ B + i (∂u) ū` on polynomial functions of the jet
  coordinates. On jets of constant gauge transformations the shift vanishes and
  the action is trivial, in agreement with `repGaugeGroupI`. -/
noncomputable def repJetGaugeGroupI : Representation ℝ JetGaugeGroupI JetAlgebra where
  toFun U := (SymmetricAlgebra.lift
    ((SymmetricAlgebra.ι ℝ JetComponentSpace) +
      (Algebra.linearMap ℝ JetAlgebra) ∘ₗ mcPairing U.2.2)).toLinearMap
  map_one' := by
    rw [show mcPairing (1 : JetGaugeGroupI).2.2 = 0 from mcPairing_one]
    suffices hs : SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℝ JetComponentSpace) +
        (Algebra.linearMap ℝ JetAlgebra) ∘ₗ (0 : JetComponentSpace →ₗ[ℝ] ℝ)) =
        AlgHom.id ℝ JetAlgebra by
      rw [hs]
      rfl
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
    simp
  map_mul' U V := by
    rw [show mcPairing (U * V : JetGaugeGroupI).2.2 =
        mcPairing U.2.2 + mcPairing V.2.2 from mcPairing_mul U.2.2 V.2.2]
    suffices hs : SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℝ JetComponentSpace) +
        (Algebra.linearMap ℝ JetAlgebra) ∘ₗ (mcPairing U.2.2 + mcPairing V.2.2)) =
        (SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℝ JetComponentSpace) +
          (Algebra.linearMap ℝ JetAlgebra) ∘ₗ mcPairing U.2.2)).comp
        (SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℝ JetComponentSpace) +
          (Algebra.linearMap ℝ JetAlgebra) ∘ₗ mcPairing V.2.2)) by
      rw [hs, AlgHom.comp_toLinearMap, Module.End.mul_eq_comp]
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
    simp [add_assoc]

/-- The jet gauge action on a generator of the jet algebra: the Maurer–Cartan
  shift by the pairing of the component function with the Maurer–Cartan jet. -/
@[simp]
lemma repJetGaugeGroupI_ι (U : JetGaugeGroupI) (x : JetComponentSpace) :
    repJetGaugeGroupI U (SymmetricAlgebra.ι ℝ JetComponentSpace x) =
      SymmetricAlgebra.ι ℝ JetComponentSpace x +
        algebraMap ℝ JetAlgebra (mcPairing U.2.2 x) := by
  simp [repJetGaugeGroupI, SymmetricAlgebra.lift_ι_apply, AlgHom.toLinearMap_apply,
    Algebra.linearMap_apply]

end JetAlgebra

end BBoson

end StandardModel
