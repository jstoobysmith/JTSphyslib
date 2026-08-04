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
open Module
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

/-- The basis of the B-boson field indexed by the Lorentz index: the standard
  Lorentz-vector basis tensored with the hermitian unit of the one-dimensional
  adjoint factor. -/
noncomputable def basis : Basis (Fin 1 ⊕ Fin 3) ℝ BBoson :=
  ((Lorentz.Vector.basis.tensorProduct
      ((Module.Basis.singleton Unit ℝ).map Complex.selfAdjointEquiv.symm)).map
    valLinEquiv.symm).reindex (Equiv.prodPUnit (Fin 1 ⊕ Fin 3))

/-- The B-boson basis vector as an explicit tensor: the Lorentz basis vector paired
  with the hermitian unit. -/
lemma basis_apply (ν : Fin 1 ⊕ Fin 3) :
    (basis ν : BBoson) =
      ⟨Lorentz.Vector.basis ν ⊗ₜ[ℝ] Complex.selfAdjointEquiv.symm 1⟩ := by
  rw [basis, Module.Basis.reindex_apply, Module.Basis.map_apply,
    Module.Basis.tensorProduct_apply', Module.Basis.map_apply,
    Module.Basis.singleton_apply, valLinEquiv_symm_apply]
  rfl

/-- A pure tensor of a Lorentz basis vector with a hermitian value is a multiple of
  the corresponding B-boson basis vector. -/
lemma mk_tmul_eq_smul_basis (ν : Fin 1 ⊕ Fin 3) (x : selfAdjoint ℂ) :
    (⟨Lorentz.Vector.basis ν ⊗ₜ[ℝ] x⟩ : BBoson) =
      Complex.selfAdjointEquiv x • basis ν := by
  apply BBoson.ext
  rw [val_smul, basis_apply,
    show ((⟨Lorentz.Vector.basis ν ⊗ₜ[ℝ] Complex.selfAdjointEquiv.symm 1⟩ : BBoson)).val =
      Lorentz.Vector.basis ν ⊗ₜ[ℝ] Complex.selfAdjointEquiv.symm 1 from rfl,
    ← TensorProduct.tmul_smul]
  congr 1
  rw [show (Complex.selfAdjointEquiv x) • (Complex.selfAdjointEquiv.symm 1) =
      Complex.selfAdjointEquiv.symm (Complex.selfAdjointEquiv x • 1) from
      (map_smul _ _ _).symm, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
  rfl
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

/-- The first-order Taylor coefficients of the Maurer–Cartan series are symmetric
  in the two spacetime directions: the shift of `∂_μ B_ν` equals the shift of
  `∂_ν B_μ`. This is the gauge invariance of the abelian field strength, and rests
  on unitarity: the antisymmetric part `∂_νu ∂_μū - ∂_μu ∂_νū` vanishes because
  `∂ū = -ū (∂u) ū`. -/
lemma mcSeriesCoeff_single_symm (u : unitary JetRing) (μ ν : Fin 1 ⊕ Fin 3) :
    mcSeriesCoeff u ν (Finsupp.single μ 1) = mcSeriesCoeff u μ (Finsupp.single ν 1) := by
  rcases eq_or_ne μ ν with rfl | hμν
  · rfl
  apply Subtype.ext
  show coeff (Finsupp.single μ 1) (mcSeries u ν) = coeff (Finsupp.single ν 1) (mcSeries u μ)
  have hb : constantCoeff (u : JetRing) * star (constantCoeff (u : JetRing)) = 1 := by
    have h := congrArg constantCoeff (Unitary.mem_iff.mp u.2).2
    rwa [map_mul, constantCoeff_star, map_one] at h
  have hμ := congrArg (coeff (Finsupp.single μ 1)) (Unitary.mem_iff.mp u.2).2
  rw [coeff_single_one_mul, coeff_star, constantCoeff_star,
    show coeff (Finsupp.single μ 1) (1 : JetRing) = 0 by
      rw [coeff_one, if_neg (by simp [Finsupp.single_eq_zero])]] at hμ
  have hν := congrArg (coeff (Finsupp.single ν 1)) (Unitary.mem_iff.mp u.2).2
  rw [coeff_single_one_mul, coeff_star, constantCoeff_star,
    show coeff (Finsupp.single ν 1) (1 : JetRing) = 0 by
      rw [coeff_one, if_neg (by simp [Finsupp.single_eq_zero])]] at hν
  have hσμ : star (coeff (Finsupp.single μ 1) (u : JetRing)) =
      -(coeff (Finsupp.single μ 1) (u : JetRing) * star (constantCoeff (u : JetRing)) *
        star (constantCoeff (u : JetRing))) := by
    linear_combination star (constantCoeff (u : JetRing)) * hμ -
      star (coeff (Finsupp.single μ 1) (u : JetRing)) * hb
  have hσν : star (coeff (Finsupp.single ν 1) (u : JetRing)) =
      -(coeff (Finsupp.single ν 1) (u : JetRing) * star (constantCoeff (u : JetRing)) *
        star (constantCoeff (u : JetRing))) := by
    linear_combination star (constantCoeff (u : JetRing)) * hν -
      star (coeff (Finsupp.single ν 1) (u : JetRing)) * hb
  rw [mcSeries, mcSeries,
    show ((C Complex.I : JetRing)) = algebraMap ℂ JetRing Complex.I from rfl,
    ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
    coeff_single_one_mul, coeff_single_one_mul, coeff_pderiv, coeff_pderiv,
    coeff_star, coeff_star, constantCoeff_star,
    show constantCoeff (pderiv ℂ ν (u : JetRing)) =
      coeff (Finsupp.single ν (1 : ℕ)) (u : JetRing) from by
      rw [← coeff_zero_eq_constantCoeff, coeff_pderiv]
      simp,
    show constantCoeff (pderiv ℂ μ (u : JetRing)) =
      coeff (Finsupp.single μ (1 : ℕ)) (u : JetRing) from by
      rw [← coeff_zero_eq_constantCoeff, coeff_pderiv]
      simp,
    show (Finsupp.single μ 1) ν = 0 from Finsupp.single_eq_of_ne hμν.symm,
    show (Finsupp.single ν 1) μ = 0 from Finsupp.single_eq_of_ne hμν,
    show Finsupp.single ν (1 : ℕ) + Finsupp.single μ 1 =
      Finsupp.single μ 1 + Finsupp.single ν 1 from add_comm _ _,
    hσμ, hσν]
  push_cast
  ring

/-!

## The Jet component vector space

-/

open Module
inductive JetGenerators where
  | dB (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3): JetGenerators
deriving DecidableEq

def JetGenerators.equiv : JetGenerators ≃ Multiset (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) where
  toFun
    | JetGenerators.dB s μ => (s, μ)
  invFun
    | (s, μ) => JetGenerators.dB s μ
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    cases x
    rfl

abbrev JetComponentSpace :=
  SymmetricAlgebra ℝ (Module.Dual ℝ Lorentz.CoVector) ⊗[ℝ] Module.Dual ℝ BBoson

/-- The basis of the B-boson jet component space indexed by the jet generators
  `∂_s B_μ`: the multiset basis of the dual derivative symbols tensored with the
  dual of the B-boson basis. -/
noncomputable def JetComponentSpace.basis : Basis JetGenerators ℝ JetComponentSpace :=
  (LagrangianTheory.dualRealJetAlgebraBasis.tensorProduct
    BBoson.basis.dualBasis).reindex JetGenerators.equiv.symm
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

/-- The multiset basis of the dual derivative symbols at a singleton, as a basis
  vector of the symmetric algebra at a single multi-index. -/
lemma dualRealJetAlgebraBasis_singleton (μ : Fin 1 ⊕ Fin 3) :
    LagrangianTheory.dualRealJetAlgebraBasis ({μ} : Multiset (Fin 1 ⊕ Fin 3)) =
      Lorentz.CoVector.basis.dualBasis.symmetricAlgebra (Finsupp.single μ 1) := by
  rw [LagrangianTheory.dualRealJetAlgebraBasis, Module.Basis.reindex_apply, Equiv.symm_symm]
  congr 1
  exact Multiset.toFinsupp_singleton μ

/-- The Maurer–Cartan jet on a first-order derivative symbol: the B boson whose
  `ν`-th component is the first-order Taylor coefficient of the Maurer–Cartan
  series. -/
lemma mcJet_singleton (u : unitary JetRing) (μ : Fin 1 ⊕ Fin 3) :
    mcJet u (LagrangianTheory.dualRealJetAlgebraBasis ({μ} : Multiset (Fin 1 ⊕ Fin 3))) =
      ⟨∑ ν, Lorentz.Vector.basis ν ⊗ₜ[ℝ]
        (mcSeriesCoeff u ν (Finsupp.single μ 1) : selfAdjoint ℂ)⟩ := by
  rw [dualRealJetAlgebraBasis_singleton, mcJet, Module.Basis.constr_basis]
  apply BBoson.ext
  show (∑ ν, Lorentz.Vector.basis ν ⊗ₜ[ℝ]
      ((∏ ρ, Nat.factorial ((Finsupp.single μ 1) ρ)) •
        mcSeriesCoeff u ν (Finsupp.single μ 1))) = _
  rw [show (∏ ρ, Nat.factorial ((Finsupp.single μ 1) ρ)) = 1 from
    Finset.prod_eq_one fun ρ _ => by
      rcases eq_or_ne μ ρ with rfl | h
      · simp
      · rw [Finsupp.single_eq_of_ne h.symm]
        rfl]
  simp

/-- The jet component basis vector at a generator, as a pure tensor. -/
lemma jetComponentSpace_basis_dB (s : Multiset (Fin 1 ⊕ Fin 3)) (ρ : Fin 1 ⊕ Fin 3) :
    JetComponentSpace.basis (.dB s ρ) =
      LagrangianTheory.dualRealJetAlgebraBasis s ⊗ₜ[ℝ] BBoson.basis.dualBasis ρ := by
  rw [JetComponentSpace.basis, Module.Basis.reindex_apply, Equiv.symm_symm]
  exact Module.Basis.tensorProduct_apply' _ _ _

/-- The Maurer–Cartan pairing on first-order generators: the shift of the component
  function `∂_μ B_ν` is the first-order Taylor coefficient of the Maurer–Cartan
  series. -/
lemma mcPairing_basis_dB (u : unitary JetRing) (μ ν : Fin 1 ⊕ Fin 3) :
    mcPairing u (JetComponentSpace.basis (.dB {μ} ν)) =
      Complex.selfAdjointEquiv (mcSeriesCoeff u ν (Finsupp.single μ 1)) := by
  rw [jetComponentSpace_basis_dB, mcPairing_tmul, mcJet_singleton,
    show (⟨∑ ν', Lorentz.Vector.basis ν' ⊗ₜ[ℝ]
        (mcSeriesCoeff u ν' (Finsupp.single μ 1) : selfAdjoint ℂ)⟩ : BBoson) =
      ∑ ν', Complex.selfAdjointEquiv (mcSeriesCoeff u ν' (Finsupp.single μ 1)) •
        basis ν' from by
      rw [show (⟨∑ ν', Lorentz.Vector.basis ν' ⊗ₜ[ℝ]
          (mcSeriesCoeff u ν' (Finsupp.single μ 1) : selfAdjoint ℂ)⟩ : BBoson) =
        valLinEquiv.symm (∑ ν', Lorentz.Vector.basis ν' ⊗ₜ[ℝ]
          (mcSeriesCoeff u ν' (Finsupp.single μ 1) : selfAdjoint ℂ)) from rfl, map_sum]
      exact Finset.sum_congr rfl fun ν' _ => by
        rw [valLinEquiv_symm_apply, mk_tmul_eq_smul_basis],
    map_sum]
  simp only [map_smul, Module.Basis.dualBasis_apply_self, smul_eq_mul, mul_ite,
    mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ ν]
  simp

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


/-- The action of the jet gauge group on the complexified B-boson jet algebra,
  obtained from the real representation by extension of scalars. -/
noncomputable def complexRepJetGaugeGroupI :
    Representation ℂ JetGaugeGroupI (ℂ ⊗[ℝ] BBoson.JetAlgebra) where
  toFun U := LinearMap.baseChange ℂ (BBoson.JetAlgebra.repJetGaugeGroupI U)
  map_one' := by
    ext x
    simp [Module.End.one_eq_id]
  map_mul' U V := by
    ext x
    simp [map_mul, Module.End.mul_eq_comp, LinearMap.baseChange_comp]

/-!

## Constructing elements of the jet algebra from the generators

-/

noncomputable def ofGenerator (x : JetGenerators) : BBoson.JetAlgebra :=
   SymmetricAlgebra.ι ℝ JetComponentSpace (BBoson.JetComponentSpace.basis x)

/-!

## The field strength of the B boson

-/

/-- The field strength of the B boson: the antisymmetrized derivative of the
  component functions, which is gauge-invariant. -/
noncomputable def fieldStrength (μ ν : Fin 1 ⊕ Fin 3) : BBoson.JetAlgebra :=
  ofGenerator (JetGenerators.dB {μ} ν) - ofGenerator (JetGenerators.dB {ν} μ)

lemma fieldStrength_antisymm (μ ν : Fin 1 ⊕ Fin 3) :
    fieldStrength μ ν = -fieldStrength ν μ := by
  simp [fieldStrength]

lemma repJetGaugeGroupI_fieldStrength (U : JetGaugeGroupI) (μ ν : Fin 1 ⊕ Fin 3) :
    repJetGaugeGroupI U (fieldStrength μ ν) = fieldStrength μ ν := by
  simp only [fieldStrength, map_sub, ofGenerator, repJetGaugeGroupI_ι, mcPairing_basis_dB]
  rw [mcSeriesCoeff_single_symm]
  abel

/-!

## Invariance under the gauge group

-/

lemma repJetGaugeGroupI_apply_eq_self_iff_mem (V : JetAlgebra) :

end JetAlgebra

end BBoson

end StandardModel
