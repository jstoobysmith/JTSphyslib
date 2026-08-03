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
# Gluons

-/

@[expose] public section

namespace StandardModel

open TensorProduct

/-!

## A. The gluon field
-/

/-- The target vector space of the gluon field strength `G_{μ}`. It carries one
  Lorentz index, and is valued in the real vector space of `3 × 3` hermitian
  matrices, corresponding to the adjoint of `SU(3)`. -/
@[ext]
structure Gluon where
  /-- The Lorentz index together with the adjoint (hermitian-matrix) colour
    factor. -/
  val : Lorentz.Vector ⊗[ℝ] selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ)

namespace Gluon

/-!

## B. Linear structure
-/

def valEquiv : Gluon ≃ Lorentz.Vector ⊗[ℝ] selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ) where
  toFun := val
  invFun := fun m => ⟨m⟩

noncomputable instance : AddCommGroup Gluon := Equiv.addCommGroup valEquiv

noncomputable instance : Module ℝ Gluon := Equiv.module ℝ valEquiv

/-- The linear identification with the underlying tensor product. -/
def valLinEquiv : Gluon ≃ₗ[ℝ]
    Lorentz.Vector ⊗[ℝ] selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ) where
  toFun := val
  invFun := fun m => ⟨m⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp]
lemma valLinEquiv_apply (d : Gluon) : valLinEquiv d = d.val := rfl

lemma valLinEquiv_symm_apply
    (m : Lorentz.Vector ⊗[ℝ] selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ)) :
    valLinEquiv.symm m = ⟨m⟩ := rfl

@[simp]
lemma val_add (d₁ d₂ : Gluon) : (d₁ + d₂).val = d₁.val + d₂.val := rfl

@[simp]
lemma val_smul (r : ℝ) (d : Gluon) : (r • d).val = r • d.val := rfl


/-!

## C. Lorentz action

The Lorentz group acts on the Lorentz index and leaves the colour index fixed.
-/

open Matrix MatrixGroups

/-- The Lorentz representation on the gluon field: the action on the Lorentz
  index, trivial on the colour (adjoint) factor. -/
noncomputable def repLorentzGroup : Representation ℝ (SL(2,ℂ)) Gluon where
  toFun Λ := valLinEquiv.symm.toLinearMap ∘ₗ
    TensorProduct.map (Lorentz.Vector.rep (Lorentz.SL2C.toLorentzGroup Λ))
      (Representation.trivial ℝ (SL(2,ℂ)) (selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ)) Λ) ∘ₗ
    valLinEquiv.toLinearMap
  map_one' := by
    ext F
    simp [Module.End.one_eq_id]
  map_mul' Λ₁ Λ₂ := by
    ext1 F
    simp [TensorProduct.map_map,
      Module.End.mul_eq_comp, map_mul]

/-!

## D. Gauge action

The gluon field transforms in the adjoint representation of the gauge group:
the `SU(3)` component acts on the colour factor by conjugation `A ↦ u * A * uᴴ`, while
the `SU(2)` and `U(1)` components act trivially, as does the Lorentz index.
-/

/-- The adjoint action of an element of `SU(3)` on the real vector space of `3 × 3`
  hermitian matrices, `A ↦ u * A * uᴴ`. -/
@[simps!]
noncomputable def adjointAction (u : specialUnitaryGroup (Fin 3) ℂ) :
    selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ) →ₗ[ℝ] selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ) where
  toFun A := ⟨u.1 * A.1 * (u.1)ᴴ,
    by
      noncomm_ring [selfAdjoint.mem_iff, star_eq_conjTranspose,
        conjTranspose_mul, conjTranspose_conjTranspose,
        (star_eq_conjTranspose A.1).symm.trans <| selfAdjoint.mem_iff.mp A.2]⟩
  map_add' A B := by
    simp only [AddSubgroup.coe_add, AddMemClass.mk_add_mk, Subtype.mk.injEq]
    noncomm_ring
  map_smul' r A := by
    noncomm_ring [selfAdjoint.val_smul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
      RingHom.id_apply]

@[simp]
lemma adjointAction_one : adjointAction 1 = LinearMap.id := by
  refine LinearMap.ext fun A => Subtype.ext ?_
  simp [adjointAction]

lemma adjointAction_mul (u₁ u₂ : specialUnitaryGroup (Fin 3) ℂ) :
    adjointAction (u₁ * u₂) = adjointAction u₁ ∘ₗ adjointAction u₂ := by
  refine LinearMap.ext fun A => Subtype.ext ?_
  simp [adjointAction, conjTranspose_mul, mul_assoc]

/-- The adjoint action of the unquotiented Standard Model gauge group on the gluon
  field. -/
noncomputable def repGaugeGroupI : Representation ℝ GaugeGroupI Gluon where
  toFun g := valLinEquiv.symm.toLinearMap ∘ₗ
    TensorProduct.map LinearMap.id (adjointAction g.toSU3) ∘ₗ
    valLinEquiv.toLinearMap
  map_one' := by
    ext F
    simp
  map_mul' g₁ g₂ := by
    ext1 F
    simp [map_mul, adjointAction_mul, TensorProduct.map_map,
      Module.End.mul_eq_comp]

/-!

## E. Local gauge action through jets

A local gauge transformation acts on the gluon field through its first-order jet:
`G ↦ u G u† + i (∂_μ U)(0) u†`, where `u` is the value of the jet `U` at the base
point. The inhomogeneous Maurer–Cartan term `i (∂_μ U)(0) u†` is hermitian by
unitarity of `U`, and satisfies a cocycle identity by the Leibniz rule; together
these make the assignment an action. The action is affine rather than linear, so it
is realised as a `MulAction` of the jet gauge group `JetGaugeGroupI` on `Gluon`
rather than as a `Representation`. The `SU(2)` and `U(1)` jets act trivially, and
the jets of constant gauge transformations recover the adjoint representation
`repGaugeGroupI`.

-/

open MvPowerSeries

/-- The matrix of first-order Taylor coefficients, in the spacetime direction `μ`,
  of a matrix of jets. -/
noncomputable def jetDeriv (μ : Fin 1 ⊕ Fin 3) (A : Matrix (Fin 3) (Fin 3) JetRing) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  A.map (coeff (Finsupp.single μ 1))

/-- The value at the base point of a matrix of jets: the entrywise constant
  coefficient. -/
noncomputable def jetValue (A : Matrix (Fin 3) (Fin 3) JetRing) : Matrix (Fin 3) (Fin 3) ℂ :=
  A.map constantCoeff

@[simp]
lemma jetDeriv_one (μ : Fin 1 ⊕ Fin 3) :
    jetDeriv μ (1 : Matrix (Fin 3) (Fin 3) JetRing) = 0 := by
  ext i j
  by_cases h : i = j <;>
    simp [jetDeriv, Matrix.map_apply, h, coeff_one, Finsupp.single_eq_zero]

/-- The Leibniz rule for the first-order Taylor coefficients of a matrix of jets. -/
lemma jetDeriv_mul (μ : Fin 1 ⊕ Fin 3) (A B : Matrix (Fin 3) (Fin 3) JetRing) :
    jetDeriv μ (A * B) = jetDeriv μ A * jetValue B + jetValue A * jetDeriv μ B := by
  ext i j
  simp [jetDeriv, jetValue, Matrix.mul_apply, Matrix.map_apply, Matrix.add_apply,
    coeff_single_one_mul, Finset.sum_add_distrib]

lemma jetDeriv_star (μ : Fin 1 ⊕ Fin 3) (A : Matrix (Fin 3) (Fin 3) JetRing) :
    jetDeriv μ (star A) = star (jetDeriv μ A) := by
  ext i j
  simp [jetDeriv, Matrix.map_apply, Matrix.star_apply]

/-- The first-order Taylor coefficients of a constant jet vanish. -/
@[simp]
lemma jetDeriv_map_C (μ : Fin 1 ⊕ Fin 3) (A : Matrix (Fin 3) (Fin 3) ℂ) :
    jetDeriv μ (A.map (C : ℂ →+* JetRing)) = 0 := by
  ext i j
  simp [jetDeriv, Matrix.map_apply, coeff_C, Finsupp.single_eq_zero]

@[simp]
lemma jetValue_one : jetValue (1 : Matrix (Fin 3) (Fin 3) JetRing) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

lemma jetValue_mul (A B : Matrix (Fin 3) (Fin 3) JetRing) :
    jetValue (A * B) = jetValue A * jetValue B :=
  Matrix.map_mul

lemma jetValue_star (A : Matrix (Fin 3) (Fin 3) JetRing) :
    jetValue (star A) = star (jetValue A) := by
  simpa [jetValue, RingHom.mapMatrix_apply] using
    JetGaugeGroupI.mapMatrix_constantCoeff_star A

/-- The unitarity of a jet of a special-unitary gauge transformation, as a matrix
  identity over the jet ring. -/
lemma coe_mul_star_self (U : specialUnitaryGroup (Fin 3) JetRing) :
    (U : Matrix (Fin 3) (Fin 3) JetRing) * star (U : Matrix (Fin 3) (Fin 3) JetRing) = 1 :=
  mem_unitaryGroup_iff.mp (mem_specialUnitaryGroup_iff.mp U.2).1

/-- The value at the base point of a jet of a special-unitary gauge transformation
  is unitary. -/
lemma jetValue_mul_star_self (U : specialUnitaryGroup (Fin 3) JetRing) :
    jetValue U.1 * star (jetValue U.1) = 1 := by
  have h := congrArg jetValue (coe_mul_star_self U)
  rwa [jetValue_mul, jetValue_star, jetValue_one] at h

/-- The value at the base point of a jet of a special-unitary gauge transformation,
  as computed by `JetGaugeGroupI.evalSU`. -/
lemma evalSU_coe (U : specialUnitaryGroup (Fin 3) JetRing) :
    (JetGaugeGroupI.evalSU (Fin 3) U : Matrix (Fin 3) (Fin 3) ℂ) = jetValue U.1 := rfl

/-!

### E.1. The Maurer–Cartan term

-/

/-- The Maurer–Cartan matrix of a matrix of jets in the spacetime direction `μ`:
  `i (∂_μ A)(0) * (A(0))†`. For a unitary jet this matrix is hermitian; see
  `mcMatrix_mem_selfAdjoint`. -/
noncomputable def mcMatrix (μ : Fin 1 ⊕ Fin 3) (A : Matrix (Fin 3) (Fin 3) JetRing) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  Complex.I • (jetDeriv μ A * star (jetValue A))

/-- The Maurer–Cartan matrix of a unitary jet is hermitian: differentiating
  `A * A† = 1` shows `(∂_μ A)(0) * (A(0))†` is anti-hermitian, and multiplication
  by `i` makes it hermitian. -/
lemma mcMatrix_mem_selfAdjoint {A : Matrix (Fin 3) (Fin 3) JetRing}
    (hA : A * star A = 1) (μ : Fin 1 ⊕ Fin 3) :
    mcMatrix μ A ∈ selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ) := by
  have h := congrArg (jetDeriv μ) hA
  rw [jetDeriv_mul, jetDeriv_star, jetDeriv_one, jetValue_star] at h
  rw [selfAdjoint.mem_iff, mcMatrix, star_smul,
    show star (jetDeriv μ A * star (jetValue A)) = jetValue A * star (jetDeriv μ A) by
      rw [star_mul, star_star],
    eq_neg_of_add_eq_zero_left h]
  simp [Complex.conj_I]

/-- The cocycle identity for the Maurer–Cartan matrix: for jets `A`, `B` with `B`
  unitary at the base point, `mc(A * B) = mc(A) + A(0) mc(B) (A(0))†`. -/
lemma mcMatrix_mul (μ : Fin 1 ⊕ Fin 3) {A B : Matrix (Fin 3) (Fin 3) JetRing}
    (hB : jetValue B * star (jetValue B) = 1) :
    mcMatrix μ (A * B) = mcMatrix μ A + jetValue A * mcMatrix μ B * star (jetValue A) := by
  rw [mcMatrix, mcMatrix, mcMatrix, jetDeriv_mul, jetValue_mul, star_mul, add_mul,
    show jetDeriv μ A * jetValue B * (star (jetValue B) * star (jetValue A)) =
        jetDeriv μ A * star (jetValue A) by
      rw [mul_assoc, ← mul_assoc (jetValue B), hB, one_mul],
    show jetValue A * jetDeriv μ B * (star (jetValue B) * star (jetValue A)) =
        jetValue A * (jetDeriv μ B * star (jetValue B)) * star (jetValue A) by
      rw [mul_assoc, mul_assoc, mul_assoc],
    smul_add, Matrix.mul_smul, Matrix.smul_mul]

/-- The Maurer–Cartan coefficient of a jet of a special-unitary gauge
  transformation in the spacetime direction `μ`, as a hermitian matrix. -/
noncomputable def mcCoeff (U : specialUnitaryGroup (Fin 3) JetRing) (μ : Fin 1 ⊕ Fin 3) :
    selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ) :=
  ⟨mcMatrix μ U.1, mcMatrix_mem_selfAdjoint (coe_mul_star_self U) μ⟩

@[simp]
lemma mcCoeff_one (μ : Fin 1 ⊕ Fin 3) : mcCoeff 1 μ = 0 := by
  apply Subtype.ext
  simp [mcCoeff, mcMatrix]

/-- The cocycle identity for the Maurer–Cartan coefficient. -/
lemma mcCoeff_mul (U V : specialUnitaryGroup (Fin 3) JetRing) (μ : Fin 1 ⊕ Fin 3) :
    mcCoeff (U * V) μ =
      mcCoeff U μ + adjointAction (JetGaugeGroupI.evalSU (Fin 3) U) (mcCoeff V μ) := by
  apply Subtype.ext
  simp only [mcCoeff, AddSubgroup.coe_add, adjointAction_apply_coe, MulMemClass.coe_mul]
  rw [mcMatrix_mul μ (jetValue_mul_star_self V)]
  rfl

/-- The Maurer–Cartan term of a jet of a special-unitary gauge transformation, as a
  gluon: the translation part of the local gauge action, with components
  `i (∂_μ U)(0) u†`. -/
noncomputable def mcGluon (U : specialUnitaryGroup (Fin 3) JetRing) : Gluon :=
  ⟨∑ μ, Lorentz.Vector.basis μ ⊗ₜ[ℝ] mcCoeff U μ⟩

@[simp]
lemma val_zero : (0 : Gluon).val = 0 := rfl

@[simp]
lemma mcGluon_one : mcGluon 1 = 0 := by
  apply Gluon.ext
  simp [mcGluon]

/-!

### E.2. The action

-/

/-- The adjoint action of an element of `SU(3)` on the gluon field, trivial on the
  Lorentz index: the linear part of the local gauge action. -/
noncomputable def adAction (u : specialUnitaryGroup (Fin 3) ℂ) : Gluon →ₗ[ℝ] Gluon :=
  valLinEquiv.symm.toLinearMap ∘ₗ
    TensorProduct.map LinearMap.id (adjointAction u) ∘ₗ valLinEquiv.toLinearMap

@[simp]
lemma adAction_one : adAction 1 = LinearMap.id := by
  rw [adAction, adjointAction_one, TensorProduct.map_id]
  ext F
  simp

lemma adAction_mul (u₁ u₂ : specialUnitaryGroup (Fin 3) ℂ) :
    adAction (u₁ * u₂) = adAction u₁ ∘ₗ adAction u₂ := by
  ext1 F
  simp [adAction, adjointAction_mul, TensorProduct.map_map]

lemma repGaugeGroupI_eq_adAction (g : GaugeGroupI) : repGaugeGroupI g = adAction g.toSU3 := rfl

/-- The cocycle identity for the Maurer–Cartan term of the gluon. -/
lemma mcGluon_mul (U V : specialUnitaryGroup (Fin 3) JetRing) :
    mcGluon (U * V) =
      mcGluon U + adAction (JetGaugeGroupI.evalSU (Fin 3) U) (mcGluon V) := by
  apply Gluon.ext
  simp [mcGluon, mcCoeff_mul, adAction, TensorProduct.tmul_add, Finset.sum_add_distrib,
    valLinEquiv_symm_apply, map_sum]

/-- The action of the jet gauge group on the gluon field: the value of the jet acts
  through the adjoint representation on the colour factor, and the first-order part
  of the jet contributes the Maurer–Cartan translation `i (∂_μ U)(0) u†`. The
  action is affine rather than linear, which is why it is a `MulAction` and not a
  `Representation`. The `SU(2)` and `U(1)` jets act trivially. -/
noncomputable instance : MulAction JetGaugeGroupI Gluon where
  smul U A := adAction (JetGaugeGroupI.evalSU (Fin 3) U.1) A + mcGluon U.1
  one_smul A := by
    show adAction (JetGaugeGroupI.evalSU (Fin 3) (1 : JetGaugeGroupI).1) A +
      mcGluon (1 : JetGaugeGroupI).1 = A
    simp
  mul_smul U V A := by
    show adAction (JetGaugeGroupI.evalSU (Fin 3) (U * V).1) A + mcGluon (U * V).1 =
      adAction (JetGaugeGroupI.evalSU (Fin 3) U.1)
        (adAction (JetGaugeGroupI.evalSU (Fin 3) V.1) A + mcGluon V.1) + mcGluon U.1
    rw [Prod.fst_mul, map_mul, adAction_mul, mcGluon_mul, map_add]
    simp only [LinearMap.coe_comp, Function.comp_apply]
    abel

lemma smul_def (U : JetGaugeGroupI) (A : Gluon) :
    U • A = adAction (JetGaugeGroupI.evalSU (Fin 3) U.1) A + mcGluon U.1 := rfl

/-- The jets of constant (global) gauge transformations act on the gluon through the
  adjoint representation of the gauge group: the Maurer–Cartan term vanishes on
  constant jets. -/
@[simp]
lemma ofConstant_smul (g : GaugeGroupI) (A : Gluon) :
    JetGaugeGroupI.ofConstant g • A = repGaugeGroupI g A := by
  rw [smul_def]
  have h1 : JetGaugeGroupI.evalSU (Fin 3) (JetGaugeGroupI.ofConstant g).1 = g.1 := by
    apply Subtype.ext
    ext i j
    simp [JetGaugeGroupI.evalSU, JetGaugeGroupI.ofConstant, JetGaugeGroupI.ofConstantSU,
      RingHom.mapMatrix_apply, Matrix.map_apply]
  have h2 : mcGluon (JetGaugeGroupI.ofConstant g).1 = 0 := by
    apply Gluon.ext
    have hmc : ∀ μ, mcCoeff (JetGaugeGroupI.ofConstant g).1 μ = 0 := by
      intro μ
      apply Subtype.ext
      show mcMatrix μ ((JetGaugeGroupI.ofConstantSU (Fin 3) g.1) :
        Matrix (Fin 3) (Fin 3) JetRing) = _
      rw [show ((JetGaugeGroupI.ofConstantSU (Fin 3) g.1) :
          Matrix (Fin 3) (Fin 3) JetRing) = g.1.1.map (C : ℂ →+* JetRing) from rfl]
      simp [mcMatrix]
    simp [mcGluon, hmc]
  rw [h1, h2, add_zero, repGaugeGroupI_eq_adAction]
  rfl

end Gluon

end StandardModel
