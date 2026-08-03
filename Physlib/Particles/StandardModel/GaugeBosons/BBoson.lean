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

end BBoson

end StandardModel
