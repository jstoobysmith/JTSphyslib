/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.SpaceTime.Derivatives
public import Physlib.SpaceAndTime.Space.Derivatives.Curl
public import Physlib.Mathematics.VariationalCalculus.HasVarAdjDeriv
public import Physlib.Relativity.Tensors.Elab
public import Physlib.SpaceAndTime.SpaceTime.TimeSlice

/-!

# The Electromagnetic Potential

## i. Overview

The electromagnetic potential `A^μ` is the fundamental objects in
electromagnetism. Mathematically it is related to a connection
on a `U(1)`-bundle.

We define the electromagnetic potential as a function from
spacetime to contravariant Lorentz vectors.

## ii. Key results

- `ElectromagneticPotential` : is the type of electromagnetic potentials.
- `ElectromagneticPotential.deriv` : the derivative tensor `∂_μ A^ν`.

## iii. Table of contents

- A. The electromagnetic potential
  - A.1. Basic instances on the type of electromagnetic potentials
  - A.2. Basic constructors of the electromagnetic potential
  - A.3. The group action on the ElectromagneticPotential
  - A.4. Differentiability
  - A.5. The action on the space-time derivatives
  - A.6. Variational adjoint derivative of component
  - A.7. Variational adjoint derivative of derivatives of the potential
- B. The derivative tensor of the electromagnetic potential
  - B.1. Equivariance of the derivative tensor
  - B.2. The elements of the derivative tensor in terms of the basis

## iv. References

- https://quantummechanics.ucsd.edu/ph130a/130_notes/node452.html
- https://ph.qmul.ac.uk/sites/default/files/EMT10new.pdf

-/

@[expose] public section

namespace Electromagnetism
open Module realLorentzTensor
open IndexNotation
open TensorSpecies
open Tensor

/-!

## A. The electromagnetic potential

We define the electromagnetic potential as a function from spacetime to
contravariant Lorentz vectors, and prove some simple results about it.

-/
/-- The electromagnetic potential is a tensor `A^μ`. -/
structure ElectromagneticPotential (d : ℕ := 3) where
  /-- The underlying map from `SpaceTime d` to `Lorentz.Vector d` associated
    with an electromagnetic potential. -/
  val : SpaceTime d → Lorentz.Vector d

namespace ElectromagneticPotential

open TensorSpecies
open Tensor
open SpaceTime
open TensorProduct
open minkowskiMatrix
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

@[ext]
lemma eq_of_val_eq (A B : ElectromagneticPotential d) (h : A.val = B.val) : A = B := by
  cases A; cases B
  simp at h
  rw [h]

/-!

## A.1. Basic instances on the type of electromagnetic potentials

-/

instance {d} : CoeFun (ElectromagneticPotential d)
    (fun _ => SpaceTime d → Lorentz.Vector d) where
  coe A := A.val

instance {d} : Add (ElectromagneticPotential d) where
  add A B := ⟨fun x => A x + B x⟩

@[simp]
lemma add_val {d} (A B : ElectromagneticPotential d) :
    (A + B).val = A.val + B.val := rfl

lemma add_apply {d} (A B : ElectromagneticPotential d) (x : SpaceTime d) :
    (A + B) x = A x + B x := by simp

noncomputable instance {d} : SMul ℝ (ElectromagneticPotential d) where
  smul r A := ⟨fun x => r • A x⟩

@[simp]
lemma smul_val {d} (r : ℝ) (A : ElectromagneticPotential d) :
    (r • A).val = r • A.val := rfl

lemma smul_apply {d} (r : ℝ) (A : ElectromagneticPotential d) (x : SpaceTime d) :
    (r • A) x = r • A x := by simp

/-!

## A.2. Basic constructors of the electromagnetic potential

-/

/-- The electromagnetic potential from a scalar potential, where
  the vector potential is set to zero. -/
noncomputable def ofScalarPotential {d} (c : SpeedOfLight)
    (ϕ : Time → Space d → ℝ) : ElectromagneticPotential d where
  val x μ :=
    match μ with
    | Sum.inl 0 => ((timeSlice c).symm ϕ x) / c
    | Sum.inr _ => 0

/-- The creation of an electromagnetic potential from a static scalar potential. -/
noncomputable def ofStaticScalarPotential {d} (c : SpeedOfLight)
    (ϕ : Space d → ℝ) : ElectromagneticPotential d :=
  ofScalarPotential c (fun _ => ϕ)

/-- The electromagnetic potential from a vector potential, where
  the scalar potential is set equal to zero. -/
noncomputable def ofVectorPotential {d} (c : SpeedOfLight)
    (A : Time → Space d → EuclideanSpace ℝ (Fin d)) :
    ElectromagneticPotential d where
  val x μ :=
    match μ with
    | Sum.inl 0 => 0
    | Sum.inr i => (timeSlice c).symm A x i

/-- The creation of an electromagnetic potential from a static vector potential. -/
noncomputable def ofStaticVectorPotential {d} (c : SpeedOfLight)
    (A : Space d → EuclideanSpace ℝ (Fin d)) : ElectromagneticPotential d :=
  ofVectorPotential c (fun _ => A)

/-- The creation of an electromagnetic potential from the non-relativistic potentials. -/
noncomputable def ofPotentials {d} (c : SpeedOfLight) (ϕ : Time → Space d → ℝ)
    (A : Time → Space d → EuclideanSpace ℝ (Fin d)) :
    ElectromagneticPotential d where
  val x μ :=
    match μ with
    | Sum.inl 0 => ((timeSlice c).symm ϕ x) / c
    | Sum.inr i => (timeSlice c).symm A x i

lemma ofPotentials_eq_add {d} (c : SpeedOfLight) (ϕ : Time → Space d → ℝ)
    (A : Time → Space d → EuclideanSpace ℝ (Fin d)) :
    ofPotentials c ϕ A = ofScalarPotential c ϕ + ofVectorPotential c A := by
  ext x
  refine Lorentz.Vector.ext_of_apply (fun i => ?_)
  match i with
  | Sum.inl 0 =>
    simp only [ofPotentials, Fin.isValue, add_val, Pi.add_apply, Lorentz.Vector.apply_add]
    simp only [ofScalarPotential, Fin.isValue, ofVectorPotential, add_zero]
  | Sum.inr i =>
    simp only [ofPotentials, add_val, Pi.add_apply, Lorentz.Vector.apply_add]
    simp [ofScalarPotential, ofVectorPotential]

/-- The creation of of an electromagnetic potential from static potentials. -/
noncomputable def ofStaticPotentials {d} (c : SpeedOfLight) (ϕ : Space d → ℝ)
    (A : Space d → EuclideanSpace ℝ (Fin d)) : ElectromagneticPotential d :=
  ofStaticScalarPotential c ϕ + ofStaticVectorPotential c A

lemma ofStaticPotentials_eq_ofPotentials {d} (c : SpeedOfLight) (ϕ : Space d → ℝ)
    (A : Space d → EuclideanSpace ℝ (Fin d)) :
    ofStaticPotentials c ϕ A = ofPotentials c (fun _ => ϕ) (fun _ => A) := by
  rw [ofPotentials_eq_add]
  rfl

/-- The electromagnetic potential from a static electric and a static magnetic field.
  There is no canonical choice here, so this depends on choice. -/
noncomputable def ofStaticElectricMagneticField (c : SpeedOfLight)
    (E : Space 3 → EuclideanSpace ℝ (Fin 3))
    (B : Space 3 → EuclideanSpace ℝ (Fin 3))
    (hE : Differentiable ℝ E) (hB : ContDiff ℝ 1 B)
    (E_curl : Space.curl E = 0) (B_div : Space.div B = 0) :
    ElectromagneticPotential 3 :=
  have φ : Space 3 → ℝ := - Classical.choose (Space.exists_grad_of_curl_zero E hE E_curl)
  have A : Space 3 → EuclideanSpace ℝ (Fin 3) :=
    Classical.choose (Space.exists_curl_of_div_zero B hB B_div)
  ofStaticPotentials c φ A

TODO "Add a constructor of the electromagnetic potential from non-static electric and
  magnetic fields."

TODO "Prove differentiability conditions with respect to the constructors of
  the electromagnetic potential."

TODO "Write lemmas for the various properties (e.g. the electric field) of
  the electromagnetic potential from the various constructors."

TODO "Define constructors for the distributional electromagnetic potential, similar
  to e.g. `ofScalarPotential` and `ofVectorPotential` for `ElectromagneticPotential`."

/-!

## A.3. The group action on the ElectromagneticPotential

-/

noncomputable instance {d} : SMul (LorentzGroup d) (ElectromagneticPotential d) where
  smul Λ A := ⟨fun x => Λ • A (Λ⁻¹ • x)⟩

lemma action_val {d} (Λ : LorentzGroup d) (A : ElectromagneticPotential d) :
    (Λ • A).val = fun x => Λ • A (Λ⁻¹ • x) := rfl

noncomputable instance {d} : MulAction (LorentzGroup d) (ElectromagneticPotential d) where
  mul_smul Λ₁ Λ₂ A := by
    ext i
    simp [action_val, mul_smul]
  one_smul A := by
    ext i
    simp [action_val, one_smul]

TODO "Lift the action on `ElectromagneticPotential d` to a `DistribMulAction`."

/-!

### A.4. Differentiability

We show that the components of field strength tensor are differentiable if the potential is.
-/

open ContDiff

@[fun_prop]
lemma differentiable_component {d : ℕ}
    (A : ElectromagneticPotential d) (hA : Differentiable ℝ A) (μ : Fin 1 ⊕ Fin d) :
    Differentiable ℝ (fun x => A x μ) := by
  revert μ
  rw [SpaceTime.differentiable_vector]
  exact hA

@[fun_prop]
lemma differentiable_action {d} (Λ : LorentzGroup d) (A : ElectromagneticPotential d)
    (hA : Differentiable ℝ A) : Differentiable ℝ (fun x => Λ • A (Λ⁻¹ • x)) := by
  apply Differentiable.comp
  · exact ContinuousLinearMap.differentiable (Lorentz.Vector.actionCLM Λ)
  · apply Differentiable.comp
    · exact hA
    · exact ContinuousLinearMap.differentiable (Lorentz.Vector.actionCLM Λ⁻¹)

@[fun_prop]
lemma contDiff_action {d} (Λ : LorentzGroup d) (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ n A) : ContDiff ℝ n (fun x => Λ • A (Λ⁻¹ • x)) := by
  apply ContDiff.comp
  · exact ContinuousLinearMap.contDiff (Lorentz.Vector.actionCLM Λ)
  · apply ContDiff.comp
    · exact hA
    · exact ContinuousLinearMap.contDiff (Lorentz.Vector.actionCLM Λ⁻¹)

@[fun_prop]
lemma differentiable_deriv {d} {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ 2 A) (μ ν : Fin 1 ⊕ Fin d) :
    Differentiable ℝ (fun x => ∂_ μ A x ν) := by
  have diff_partial (μ) :
      ∀ ν, Differentiable ℝ fun x => (fderiv ℝ A x) (Lorentz.Vector.basis μ) ν := by
    rw [SpaceTime.differentiable_vector]
    fun_prop
  exact diff_partial μ ν

@[fun_prop]
lemma differentiable_deriv_of_smooth {d} {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ ∞ A) (μ ν : Fin 1 ⊕ Fin d) :
    Differentiable ℝ (fun x => ∂_ μ A x ν) := by
  apply differentiable_deriv (hA.of_le (ENat.LEInfty.out)) μ ν

@[fun_prop]
lemma contDiff_deriv {n} {d} {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ (n + 1) A) (μ ν : Fin 1 ⊕ Fin d) :
    ContDiff ℝ n (fun x => ∂_ μ A x ν) := by
  have diff_partial (μ) :
      ∀ ν, ContDiff ℝ n fun x => (fderiv ℝ A x) (Lorentz.Vector.basis μ) ν := by
    rw [SpaceTime.contDiff_vector]
    fun_prop
  exact diff_partial μ ν

TODO "Add results related to the differentiability of the
  derivative of the Electromagnetic potential."

/-!

### A.5. The action on the space-time derivatives

Given a ElectromagneticPotential `A^μ`, we can consider its derivative `∂_μ A^ν`.
Under a Lorentz transformation `Λ`, this transforms as
`∂_ μ (Λ • A)`, we write an expression for this in terms of the tensor.
`∂_ ρ A (Λ⁻¹ • x) κ`.

-/

set_option backward.isDefEq.respectTransparency false in
lemma spaceTime_deriv_action_eq_sum {d} {μ ν : Fin 1 ⊕ Fin d} {x : SpaceTime d}
    (Λ : LorentzGroup d) (A : ElectromagneticPotential d) (hA : Differentiable ℝ A) :
    ∂_ μ (Λ • A) x ν = ∑ κ, ∑ ρ, (Λ.1 ν κ * Λ⁻¹.1 ρ μ) * ∂_ ρ A (Λ⁻¹ • x) κ := by
  calc _
    _ = ((Λ • (∂_ μ (fun x => A (Λ⁻¹ • x)) x)) ν) := by
      have hdif : ∀ i, DifferentiableAt ℝ (fun x => A (Λ⁻¹ • x) i) x := by
          intro i
          apply Differentiable.differentiableAt
          revert i
          rw [SpaceTime.differentiable_vector]
          conv =>
            enter [2, x]; rw [← Lorentz.Vector.actionCLM_apply]
          apply Differentiable.fun_comp hA
          exact ContinuousLinearMap.differentiable (Lorentz.Vector.actionCLM Λ⁻¹)
      trans ∂_ μ (fun x => (Λ • A (Λ⁻¹ • x)) ν) x
      · rw [SpaceTime.deriv_eq, SpaceTime.deriv_eq, SpaceTime.fderiv_vector]
        simp only [action_val]
        fun_prop
      conv_lhs =>
        enter [2, x]
        rw [Lorentz.Vector.smul_eq_sum]
      rw [SpaceTime.deriv_eq]
      rw [fderiv_fun_sum (𝕜 := ℝ)]
      conv_lhs =>
        enter [1, 2, i]
        rw [fderiv_const_mul (hdif i)]
      simp only [ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_smul',
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Lorentz.Vector.smul_eq_sum]
      congr
      funext κ
      congr
      rw [SpaceTime.deriv_eq, SpaceTime.fderiv_vector]
      · exact hA.comp (Lorentz.Vector.actionCLM Λ⁻¹).differentiable
      · intro i _
        apply DifferentiableAt.const_mul
        exact hdif i
    _ = (((Λ • (∑ ρ, Λ⁻¹.1 ρ μ • ∂_ ρ A (Λ⁻¹ • x)))) ν) := by
      rw [SpaceTime.deriv_comp_lorentz_action]
      · exact hA
    _ = (∑ κ, Λ.1 ν κ * (∑ ρ, Λ⁻¹.1 ρ μ • ∂_ ρ A (Λ⁻¹ • x) κ)) := by
      rw [Lorentz.Vector.smul_eq_sum]
      congr
      funext j
      congr
      rw [Lorentz.Vector.apply_sum]
      rfl
  apply Finset.sum_congr rfl (fun κ _ => ?_)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl (fun ρ _ => ?_)
  simp only [smul_eq_mul]
  ring

/-!

### A.6. Variational adjoint derivative of component

We find the variational adjoint derivative of the components of the potential.
This will be used to find e.g. the variational derivative of the kinetic term,
and derive the equations of motion.

-/

open ContDiff
set_option backward.isDefEq.respectTransparency false in
lemma hasVarAdjDerivAt_component {d : ℕ} (μ : Fin 1 ⊕ Fin d) (A : SpaceTime d → Lorentz.Vector d)
    (hA : ContDiff ℝ ∞ A) :
        HasVarAdjDerivAt (fun (A' : SpaceTime d → Lorentz.Vector d) x => A' x μ)
          (fun (A' : SpaceTime d → ℝ) x => A' x • Lorentz.Vector.basis μ) A := by
  let f : SpaceTime d → Lorentz.Vector d → ℝ := fun x v => v μ
  let f' : SpaceTime d → Lorentz.Vector d → ℝ → Lorentz.Vector d := fun x _ c =>
    c • Lorentz.Vector.basis μ
  change HasVarAdjDerivAt (fun A' x => f x (A' x)) (fun ψ x => f' x (A x) (ψ x)) A
  apply HasVarAdjDerivAt.fmap
  · fun_prop
  · fun_prop
  intro x A
  refine { differentiableAt := ?_, hasAdjoint_fderiv := ?_ }
  · fun_prop
  refine { adjoint_inner_left := ?_ }
  intro u v
  simp [f,f']
  simp [inner_smul_left, Lorentz.Vector.basis_inner]
  ring_nf
  rfl

/-!

### A.7. Variational adjoint derivative of derivatives of the potential

We find the variational adjoint derivative of the derivatives of the components of the potential.
This will again be used to find the variational derivative of the kinetic term,
and derive the equations of motion (Maxwell's equations).

-/

lemma deriv_hasVarAdjDerivAt {d} (μ ν : Fin 1 ⊕ Fin d) (A : SpaceTime d → Lorentz.Vector d)
    (hA : ContDiff ℝ ∞ A) :
    HasVarAdjDerivAt (fun (A : SpaceTime d → Lorentz.Vector d) x => ∂_ μ A x ν)
      (fun ψ x => - (fderiv ℝ ψ x) (Lorentz.Vector.basis μ) • Lorentz.Vector.basis ν) A := by
  have h0' := HasVarAdjDerivAt.fderiv' _ _
        (hF := hasVarAdjDerivAt_component ν A hA) A (Lorentz.Vector.basis μ)
  refine HasVarAdjDerivAt.congr (G := (fun (A : SpaceTime d →
    Lorentz.Vector d) x => ∂_ μ A x ν)) h0' ?_
  intro φ hφ
  funext x
  simp only
  rw [deriv_apply_eq μ ν φ]
  exact hφ.differentiable (by simp)

/-!

## B. The derivative tensor of the electromagnetic potential

We define the derivative as a tensor in `Lorentz.CoVector ⊗[ℝ] Lorentz.Vector` for the
electromagnetic potential `A^μ`. We then prove that this tensor transforms correctly
under Lorentz transformations.

-/

/-- The derivative of the electric potential, `∂_μ A^ν`. -/
noncomputable def deriv {d} (A : ElectromagneticPotential d) :
    SpaceTime d → Lorentz.CoVector d ⊗[ℝ] Lorentz.Vector d := fun x =>
  ∑ μ, ∑ ν, (∂_ μ A x ν) • Lorentz.CoVector.basis μ ⊗ₜ[ℝ] Lorentz.Vector.basis ν

lemma deriv_eq_tensorDeriv {d} (A : ElectromagneticPotential d)
    (hA : Differentiable ℝ A) (x : SpaceTime d) :
    A.deriv x = tensorDeriv A.val x := by
  rw [deriv, tensorDeriv_eq_sum_tensor_basis (by fun_prop)]
  /- Match the basis sum. -/
  let e : ComponentIdx (Fin.append ![Color.down] ![Color.up])
      ≃ (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d) := ComponentIdx.prod.trans <|
    Lorentz.CoVector.indexEquiv.prodCongr Lorentz.Vector.indexEquiv
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  /- Getting rid of the sums -/
  refine Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun ν _ => ?_))
  congr
  /- The coefficients. -/
  · simp [e]
    rw [deriv_apply_eq _ _ _ (by fun_prop)]
    congr
    simp [Lorentz.Vector.tensor_basis_repr_toTensor_apply]
  /- The basis elements. -/
  · change _ = ((Tensor.basis (S := realLorentzTensor d) (Fin.append ![Color.down] ![Color.up])).map
      (Tensorial.toTensor (M := (Lorentz.CoVector d) ⊗[ℝ] (Lorentz.Vector d))).symm) (e.symm (μ, ν))
    rw [Tensorial.basis_map_prod, ← Lorentz.Vector.toTensor_symm_basis,
      ← Lorentz.CoVector.toTensor_symm_basis]
    simp [e]

/-!

### B.1. Equivariance of the derivative tensor

We show that the derivative tensor is equivariant under the action of the Lorentz group.
That is, `∂_μ (fun x => Λ • A (Λ⁻¹ • x)) = Λ • (∂_μ A (Λ⁻¹ • x))`, or in words:
applying the Lorentz transformation to the potential and then taking the derivative is the same
as taking the derivative and then applying the Lorentz transformation to the resulting tensor.

-/
lemma deriv_equivariant {d} {x : SpaceTime d} (A : ElectromagneticPotential d)
    (Λ : LorentzGroup d)
    (hf : Differentiable ℝ A) : deriv (Λ • A) x = Λ • (deriv A (Λ⁻¹ • x)) := by
  rw [deriv_eq_tensorDeriv, deriv_eq_tensorDeriv]
  rw [action_val, tensorDeriv_equivariant]
  all_goals fun_prop

/-!

### B.2. The elements of the derivative tensor in terms of the basis

We show that in the standard basis, the elements of the derivative tensor
are just equal to `∂_ μ A x ν`.

-/

open Tensorial
/-- Evaluation of the tensor components of `∂_ μ A x ν`. -/
lemma tensorDeriv_eval_eq {d} {A : ElectromagneticPotential d} (hA : Differentiable ℝ A)
    (x : SpaceTime d) (μ ν : Fin 1 ⊕ Fin d) :
    toField {tensorDeriv A.val x | [μ] [ν]}ᵀ = ∂_ μ A x ν := by
  trans  (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr (deriv A x) (μ, ν); swap
  · simp [deriv, Basis.tensorProduct_repr_tmul_apply, Finsupp.single_apply]
  rw [deriv_eq_tensorDeriv _ hA]
  generalize (tensorDeriv A.val x) = t
  obtain ⟨t, rfl⟩ := toTensor.symm.surjective t
  induction' t using Tensor.induction_on_basis with b a t h t1 t2 h1 h2
  · simp only [LinearEquiv.apply_symm_apply, basis_apply, evalT_pure, Pure.evalP, map_smul,
      toField_pure, smul_eq_mul, mul_one, Pure.evalPCoeff]

    change _ * (Lorentz.contrBasis d).repr (Lorentz.contrBasis d (b 1)) ν = _
    /- Transforming the basis -/
    let e : ComponentIdx (Fin.append ![Color.down] ![Color.up])
      ≃ (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d) := ComponentIdx.prod.trans <|
      Lorentz.CoVector.indexEquiv.prodCongr Lorentz.Vector.indexEquiv
    have h1 :  Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis =
        (((Tensor.basis (Fin.append ![Color.down] ![Color.up]))).map toTensor.symm).reindex e := by
      ext ⟨i, j⟩
      simp_rw [Tensorial.basis_map_prod, Basis.tensorProduct_apply,
        ← Lorentz.Vector.toTensor_symm_basis, ← Lorentz.CoVector.toTensor_symm_basis, e]
      simp
    simp [Pure.basisVector, h1, Finsupp.single_apply]
    grind [show e b = (b 0,  b 1) from rfl]
  · simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  · simp only [map_smul, h, smul_eq_mul, Finsupp.coe_smul, Pi.smul_apply]
  · simp only [map_add, h1, h2, Finsupp.coe_add, Pi.add_apply]

@[simp]
lemma deriv_basis_repr_apply {d} {μν : (Fin 1 ⊕ Fin d) × (Fin 1 ⊕ Fin d)}
    (A : ElectromagneticPotential d)
    (x : SpaceTime d) :
    (Lorentz.CoVector.basis.tensorProduct Lorentz.Vector.basis).repr (deriv A x) μν =
    ∂_ μν.1 A x μν.2 := by
  rcases μν  with ⟨μ, ν⟩
  simp [deriv, Basis.tensorProduct_repr_tmul_apply, Finsupp.single_apply]

lemma toTensor_deriv_basis_repr_apply {d} (A : ElectromagneticPotential d)
    (x : SpaceTime d) (b : ComponentIdx (S := realLorentzTensor d)
      (Fin.append ![Color.down] ![Color.up])) :
    (Tensor.basis _).repr (Tensorial.toTensor (deriv A x)) b =
    ∂_ (b 0) A x (b 1) := by
  rw [Tensorial.basis_toTensor_apply]
  rw [Tensorial.basis_map_prod]
  simp only [Nat.reduceSucc, Nat.reduceAdd, Basis.repr_reindex, Finsupp.mapDomain_equiv_apply,
    Equiv.symm_symm, Fin.isValue]
  rw [Lorentz.Vector.tensor_basis_map_eq_basis_reindex,
    Lorentz.CoVector.tensor_basis_map_eq_basis_reindex]
  have hb : (((Lorentz.CoVector.basis (d := d)).reindex
      Lorentz.CoVector.indexEquiv.symm).tensorProduct
      (Lorentz.Vector.basis.reindex Lorentz.Vector.indexEquiv.symm)) =
      ((Lorentz.CoVector.basis (d := d)).tensorProduct (Lorentz.Vector.basis (d := d))).reindex
      (Lorentz.CoVector.indexEquiv.symm.prodCongr Lorentz.Vector.indexEquiv.symm) := by
    ext b
    match b with
    | ⟨i, j⟩ =>
    simp
  rw [hb]
  rw [Module.Basis.repr_reindex_apply, deriv_basis_repr_apply]
  rfl

end ElectromagneticPotential

end Electromagnetism
