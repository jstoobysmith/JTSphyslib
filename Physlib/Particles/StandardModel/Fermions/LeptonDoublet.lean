/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.Jet
public import Physlib.Relativity.Tensors.ComplexTensor.Basic
/-!
# Lepton doublets

## i. Overview

The Standard Model lepton doublet is a left-handed Weyl spinor in the `(1, 2)_{-3}`
representation. Here charges are normalized as `6Y`, so `-3` is the usual hypercharge
`Y = -1/2`.

`LeptonDoublet` is the target vector space of one lepton multiplet. Its Weyl factor
carries the Lorentz index and its two-dimensional factor carries the weak index.
The absence of a colour factor makes it an `SU(3)` singlet.

The Lorentz and gauge actions are first defined separately. The gauge action is then
computed on a basis, used to identify its kernel, and descended to each supported global
form of the Standard Model gauge group.

## ii. Key results

- `LeptonDoublet` : the target space of the `(1, 2)_{-3}` multiplet.
- `repLorentzGroup` : the left-handed Lorentz action.
- `repGaugeGroupI` : the action of the unquotiented gauge group.
- `repGaugeGroupI_tmul_basis_eq_sum` : the gauge action in a tensor-product basis.
- `mem_repGaugeGroupI_ker_iff_eq` : the kernel of the full-group action.
- `gaugeGroup_subgroup_ℤ₆_le_ker_repGaugeGroupI` : triviality of the central `ℤ₆`.
- `repGaugeGroup` : the action descended to every supported gauge-group quotient.

## iii. Table of contents

- A. The lepton-doublet space
- B. Linear structure
- C. Lorentz action
- D. Gauge action
- E. Kernel of the gauge action
- F. Descent to quotient gauge groups
- G. Jet gauge action

-/

@[expose] public section

namespace StandardModel

open TensorProduct

/-!

## A. The lepton-doublet space

The Weyl factor carries the left-handed Lorentz index, while
`EuclideanSpace ℂ (Fin 2)` carries the weak index.
-/

/-- The target vector space of one Standard Model lepton doublet.
  It carries the `(1, 2)_{-3}` representation of the gauge group. -/
@[ext]
structure LeptonDoublet where
  /-- The left-handed Weyl spinor with its weak-doublet index. -/
  val : Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 2)

namespace LeptonDoublet

/-!

## B. Linear structure

The wrapper distinguishes lepton doublets from other isomorphic vector spaces.
The following equivalences transfer the linear structure of the tensor product and expose
that model when defining representations.
-/

/-- Identifies a lepton doublet with its underlying tensor-product value. -/
def valEquiv : LeptonDoublet ≃ Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun := val
  invFun := fun m => ⟨m⟩

instance : AddCommGroup LeptonDoublet := Equiv.addCommGroup valEquiv

instance : Module ℂ LeptonDoublet := Equiv.module ℂ valEquiv

/-- The linear identification with the underlying tensor product. -/
def valLinEquiv : LeptonDoublet ≃ₗ[ℂ]
    Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun := val
  invFun := fun m => ⟨m⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp]
lemma valLinEquiv_apply (l : LeptonDoublet) : valLinEquiv l = l.val := rfl

lemma valLinEquiv_symm_apply
    (m : Fermion.LeftHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 2)) :
    valLinEquiv.symm m = ⟨m⟩ := rfl

@[simp]
lemma val_add (l₁ l₂ : LeptonDoublet) : (l₁ + l₂).val = l₁.val + l₂.val := rfl

@[simp]
lemma val_smul (r : ℂ) (l : LeptonDoublet) : (r • l).val = r • l.val := rfl

/-!

## The basis of the lepton-doublet space

-/

/-- A basis on the lepton doublets. -/
noncomputable def basis : Module.Basis (Fin 2 × Fin 2) ℂ LeptonDoublet :=
  (Fermion.LeftHandedWeyl.basis.tensorProduct
    (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis).map valLinEquiv.symm

/-!

## C. Lorentz action

The Lorentz group acts on the left-handed Weyl factor and leaves the weak index fixed.
-/

open Matrix MatrixGroups

open Representation in
/-- The left-handed Lorentz representation on lepton doublets. -/
noncomputable def repLorentzGroup : Representation ℂ (SL(2,ℂ)) LeptonDoublet where
  toFun Λ := valLinEquiv.symm ∘ₗ
      (TensorProduct.map (Fermion.LeftHandedWeyl.rep Λ)
        (trivial ℂ (SL(2,ℂ)) (EuclideanSpace ℂ (Fin 2)) Λ))
      ∘ₗ valLinEquiv
  map_one' := by
    ext l
    simp [Module.End.one_eq_id]
  map_mul' Λ₁ Λ₂ := by
    ext1 l
    simp [TensorProduct.map_map, Module.End.mul_eq_comp]

/-!

## D. Gauge action

The colour factor acts trivially, while `SU(2)` acts on the weak index. The `U(1)` action
is `star z ^ 3`; since `z` is unitary, `star z = z⁻¹`, so this represents charge `-3`.

The tensor and basis formulas below expose the coefficients used to compare actions and
compute the kernel.
-/

/-- The `(1, 2)_{-3}` action of the unquotiented Standard Model gauge group. -/
noncomputable def repGaugeGroupI : Representation ℂ GaugeGroupI LeptonDoublet where
  toFun g := valLinEquiv.symm ∘ₗ
        (TensorProduct.map
        (LinearMap.id (M := Fermion.LeftHandedWeyl))
        g.toSU2.1.toEuclideanLin)
      ∘ₗ LinearMap.lsmul ℂ _ (star g.toU1.1 ^ 3 : ℂ)
      ∘ₗ valLinEquiv
  map_one' := by
    ext l
    simp [valLinEquiv_symm_apply]
  map_mul' g₁ g₂ := by
    ext l
    simp [smul_smul, mul_comm, TensorProduct.map_map, valLinEquiv_symm_apply]
    ring_nf

/-- The gauge action on a pure spinor–weak tensor. -/
lemma repGaugeGroupI_tmul (g : GaugeGroupI) (v : Fermion.LeftHandedWeyl)
    (w : EuclideanSpace ℂ (Fin 2)) :
    repGaugeGroupI g ⟨v ⊗ₜ w⟩ =
      ⟨(star g.toU1.1 ^ 3) • v ⊗ₜ (g.toSU2.1.toEuclideanLin w)⟩ := rfl

open Fermion in
/-- Expands the gauge action in the spinor–weak basis. -/
lemma repGaugeGroupI_tmul_basis_eq_sum (g : GaugeGroupI) (k j : Fin 2) :
    repGaugeGroupI g ⟨LeftHandedWeyl.basis k ⊗ₜ[ℂ]
      EuclideanSpace.basisFun (Fin 2) ℂ j⟩ =
      ∑ j' : Fin 2, (star g.toU1.1 ^ 3 * g.toSU2.1 j' j)
      • (⟨LeftHandedWeyl.basis k ⊗ₜ[ℂ]
          EuclideanSpace.basisFun (Fin 2) ℂ j'⟩ : LeptonDoublet) := by
  apply valLinEquiv.injective
  apply (((LeftHandedWeyl.basis).tensorProduct
    (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis)).repr.injective
  ext ⟨⟨k, l⟩, m⟩
  simp only [EuclideanSpace.basisFun_apply, repGaugeGroupI_tmul, valLinEquiv_apply, map_smul,
    Finsupp.coe_smul, Pi.smul_apply,
    Module.Basis.tensorProduct_repr_tmul_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr, ofLp_toLpLin, PiLp.ofLp_single, toLin'_apply, mulVec_single,
    MulOpposite.op_one, col_apply, one_smul, Module.Basis.repr_self, smul_eq_mul, map_sum,
    Finsupp.coe_finsetSum, Finset.sum_apply, PiLp.single_apply, ite_mul, one_mul, zero_mul,
    mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  ring

open Fermion in
/-- Two gauge elements induce the same action exactly when their weak-basis coefficients agree. -/
lemma repGaugeGroupI_eq_iff_mul_eq {g₁ g₂ : GaugeGroupI} :
    repGaugeGroupI g₁ = repGaugeGroupI g₂ ↔ ∀ j j',
    star g₁.toU1.1 ^ 3 * g₁.toSU2.1 j' j =
      star g₂.toU1.1 ^ 3 * g₂.toSU2.1 j' j := by
  let b := (LeftHandedWeyl.basis).tensorProduct
    (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis
  constructor
  · intro h j j'
    have h' := congrFun (congrArg (fun f => f.1) h)
      ⟨LeftHandedWeyl.basis 0 ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 2) ℂ j⟩
    simp only [Fin.isValue, LinearMap.coe_toAddHom, repGaugeGroupI_tmul_basis_eq_sum] at h'
    replace h' := congrArg b.repr (congrArg valLinEquiv h')
    simpa [Module.Basis.tensorProduct_repr_tmul_apply, -Fin.sum_univ_two, b] using
      congrArg (fun f => f (0, j')) h'
  · intro h
    apply (valLinEquiv.symm.eq_comp_toLinearMap_iff
      (repGaugeGroupI g₁) (repGaugeGroupI g₂)).mp
    apply b.ext
    rintro ⟨k, j⟩
    have h₁ := repGaugeGroupI_tmul_basis_eq_sum g₁ k j
    have h₂ := repGaugeGroupI_tmul_basis_eq_sum g₂ k j
    simp only [EuclideanSpace.basisFun_apply] at h₁ h₂
    have hj₀ : (starRingEnd ℂ) g₁.toU1.1 ^ 3 * g₁.toSU2.1 0 j =
        (starRingEnd ℂ) g₂.toU1.1 ^ 3 * g₂.toSU2.1 0 j := h j 0
    have hj₁ : (starRingEnd ℂ) g₁.toU1.1 ^ 3 * g₁.toSU2.1 1 j =
        (starRingEnd ℂ) g₂.toU1.1 ^ 3 * g₂.toSU2.1 1 j := h j 1
    simp [valLinEquiv_symm_apply, h₁, h₂, b, hj₀, hj₁]

/-!

## E. Kernel of the gauge action

An element acts trivially when its weak action is scalar and that scalar cancels its
`U(1)` phase. Its colour component is unrestricted because the lepton doublet is an
`SU(3)` singlet.
-/

/-- Characterizes the full-group elements acting trivially on the lepton doublet. -/
lemma mem_repGaugeGroupI_ker_iff_eq {g : GaugeGroupI} :
    g ∈ repGaugeGroupI.ker ↔ ∃ a : ℂ, g.toSU2.1 = a • 1 ∧
      a * star g.toU1.1 ^ 3 = 1 := by
  rw [MonoidHom.mem_ker, ← MonoidHom.map_one repGaugeGroupI, repGaugeGroupI_eq_iff_mul_eq]
  constructor; swap
  · rintro ⟨a, h₁, h₂⟩ j j'
    simp only [Matrix.smul_apply, smul_eq_mul, h₁, map_one, OneMemClass.coe_one,
      star_one, one_pow, one_mul]
    linear_combination h₂ * (1 : Matrix _ _ ℂ) j' j
  · intro h
    have hc : star g.toU1.1 ^ 3 ≠ 0 := by
      apply pow_ne_zero
      rw [star_ne_zero]
      intro hzero
      have hu := Unitary.star_mul_self_of_mem g.toU1.2
      simp [hzero] at hu
    use g.toSU2.1 0 0
    simp only [map_one, OneMemClass.coe_one, Fin.forall_fin_succ, Fin.isValue,
      Fin.succ_zero_eq_one, IsEmpty.forall_iff, and_true, one_apply_eq, ne_eq,
      one_ne_zero, not_false_eq_true, one_apply_ne, mul_eq_zero, zero_ne_one,
      star_one, one_pow, one_mul] at h
    rcases h with ⟨⟨h₀₀, h₁₀⟩, h₀₁, h₁₁⟩
    have h₁₀' := h₁₀.resolve_left hc
    have h₀₁' := h₀₁.resolve_left hc
    have hdiag : g.toSU2.1 1 1 = g.toSU2.1 0 0 := by
      apply mul_left_cancel₀ hc
      rw [h₁₁, h₀₀]
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [h₁₀', h₀₁', hdiag]
    · simpa [mul_comm] using h₀₀

/-!

## F. Descent to quotient gauge groups

A representation descends through a quotient when the quotient subgroup lies in its
kernel. For the central `ℤ₆`, the weak central phase and charge `-3` phase combine to a
sixth power and therefore act trivially.
-/

/-- The central `ℤ₆` subgroup acts trivially on `(1, 2)_{-3}`. -/
lemma gaugeGroup_subgroup_ℤ₆_le_ker_repGaugeGroupI :
    GaugeGroupQuot.subgroup .ℤ₆ ≤ repGaugeGroupI.ker := by
  simp only [GaugeGroupQuot.subgroup, gaugeGroupℤ₆SubGroup, SetLike.le_def,
    MonoidHom.mem_range, gaugeGroupℤ₆Hom_apply, Subtype.exists,
    mem_repGaugeGroupI_ker_iff_eq, forall_exists_index]
  rintro g x hx ⟨rfl⟩
  use starRingEnd ℂ (x ^ 3)
  simp only [gaugeGroupℤ₆OfRoot_toSU2, gaugeGroupℤ₆SU2OfRoot_eq_mul_id,
    RCLike.star_def, Complex.conj_rootsOfUnity hx, Units.val_inv_eq_inv_val, inv_pow,
    map_pow, gaugeGroupℤ₆OfRoot_toU1, gaugeGroupℤ₆UnitaryOfRoot_coe, true_and]
  field_simp
  exact ((mem_rootsOfUnity' 6 x).mp hx).symm

/-- Every supported quotient subgroup acts trivially on the lepton doublet. -/
lemma gaugeGroup_subgroup_le_ker_repGaugeGroupI (Q : GaugeGroupQuot) :
    Q.subgroup ≤ repGaugeGroupI.ker := Q.subgroup_le_subgroup_ℤ₆.trans
  gaugeGroup_subgroup_ℤ₆_le_ker_repGaugeGroupI

/-- The `(1, 2)_{-3}` representation for every supported global form of the
  Standard Model gauge group. -/
noncomputable def repGaugeGroup : (Q : GaugeGroupQuot) →
    Representation ℂ (GaugeGroup Q) LeptonDoublet
  | .I => repGaugeGroupI
  | .ℤ₆ => QuotientGroup.lift _ repGaugeGroupI (gaugeGroup_subgroup_le_ker_repGaugeGroupI .ℤ₆)
  | .ℤ₂ => QuotientGroup.lift _ repGaugeGroupI (gaugeGroup_subgroup_le_ker_repGaugeGroupI .ℤ₂)
  | .ℤ₃ => QuotientGroup.lift _ repGaugeGroupI (gaugeGroup_subgroup_le_ker_repGaugeGroupI .ℤ₃)

/-!

## G. Jet gauge action

The `(1, 2)_{-3}` representation extends verbatim to jets: the hypercharge power
series `star u ^ 3` and the `SU(2)` power-series matrix of a jet of gauge
transformations combine into a matrix of jets, `jetGaugeMatrix`. This matrix acts
on the polynomial jet space
`SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ] LeptonDoublet` through the entrywise
derivative action `DerivAlgebraComplex.jetRingAction` on the derivative symbols, moving the weak index
and leaving the Weyl factor fixed: the value of the jet acts by the gauge matrix,
while its derivative coordinates lower derivative symbols by the Leibniz rule. On
jets of constant gauge transformations the action reduces to the global gauge
action, trivial on the derivative symbols.

-/

/-- The matrix of jets through which a jet of gauge transformations acts on the
  lepton doublet: the `SU(2)` power-series matrix scaled by the hypercharge power
  series `star u ^ 3`. -/
noncomputable def jetGaugeMatrix (U : JetGaugeGroupI) : Matrix (Fin 2) (Fin 2) JetRing :=
  ((star ((U.2.2 : unitary JetRing) : JetRing)) ^ 3) •
    ((U.2.1 : specialUnitaryGroup (Fin 2) JetRing) : Matrix (Fin 2) (Fin 2) JetRing)

lemma jetGaugeMatrix_one : jetGaugeMatrix 1 = 1 := by
  simp [jetGaugeMatrix]

lemma jetGaugeMatrix_mul (U₁ U₂ : JetGaugeGroupI) :
    jetGaugeMatrix (U₁ * U₂) = jetGaugeMatrix U₁ * jetGaugeMatrix U₂ := by
  rw [jetGaugeMatrix, jetGaugeMatrix, jetGaugeMatrix,
    show (((U₁ * U₂).2.2 : unitary JetRing) : JetRing) =
      ((U₁.2.2 : unitary JetRing) : JetRing) * ((U₂.2.2 : unitary JetRing) : JetRing) from rfl,
    show (((U₁ * U₂).2.1 : specialUnitaryGroup (Fin 2) JetRing) :
        Matrix (Fin 2) (Fin 2) JetRing) =
      ((U₁.2.1 : specialUnitaryGroup (Fin 2) JetRing) : Matrix (Fin 2) (Fin 2) JetRing) *
        ((U₂.2.1 : specialUnitaryGroup (Fin 2) JetRing) : Matrix (Fin 2) (Fin 2) JetRing)
      from rfl,
    star_mul', mul_pow, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

@[simp]
lemma mk_zero : (⟨0⟩ : LeptonDoublet) = 0 := rfl

/-- The evaluation of the `SU(2)` matrix unit on a weak basis vector. -/
lemma toEuclideanLin_single_single (i j j' : Fin 2) :
    (Matrix.single i j' (1 : ℂ)).toEuclideanLin (EuclideanSpace.single j (1 : ℂ)) =
      if j' = j then EuclideanSpace.single i (1 : ℂ) else 0 := by
  ext i'
  rcases eq_or_ne j' j with h | h
  · subst h
    simp [Matrix.toEuclideanLin, Matrix.single_apply, eq_comm]
  · simp [Matrix.toEuclideanLin, h]

/-- The action of a matrix of jets on the jet space of the lepton doublet: each
  entry acts through the derivative action `DerivAlgebraComplex.jetRingAction` on the derivative symbols
  while moving the weak index; the Weyl factor is fixed. -/
noncomputable def jetMatrixAction (A : Matrix (Fin 2) (Fin 2) JetRing) :
    SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ] LeptonDoublet →ₗ[ℂ]
      SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ] LeptonDoublet :=
  ∑ i, ∑ j,
    TensorProduct.map (DerivAlgebraComplex.jetRingAction (A i j))
      (valLinEquiv.symm.toLinearMap ∘ₗ
        TensorProduct.map LinearMap.id ((Matrix.single i j (1 : ℂ)).toEuclideanLin) ∘ₗ
        valLinEquiv.toLinearMap)

/-- The action of a matrix of jets on a generator of the jet space. -/
lemma jetMatrixAction_tmul (A : Matrix (Fin 2) (Fin 2) JetRing)
    (p : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule)) (w : Fermion.LeftHandedWeyl) (j : Fin 2) :
    jetMatrixAction A (p ⊗ₜ[ℂ] ⟨w ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 2) ℂ j⟩) =
      ∑ i, DerivAlgebraComplex.jetRingAction (A i j) p ⊗ₜ[ℂ]
        (⟨w ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 2) ℂ i⟩ : LeptonDoublet) := by
  rw [jetMatrixAction, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.sum_apply, Finset.sum_eq_single j]
  · simp [valLinEquiv_symm_apply, toEuclideanLin_single_single]
  · intro j' _ hj'
    simp [valLinEquiv_symm_apply, toEuclideanLin_single_single, hj']
  · simp

/-- The lepton-doublet basis as explicit spinor–weak tensors. -/
lemma basis_apply (k j : Fin 2) :
    (basis (k, j) : LeptonDoublet) =
      ⟨Fermion.LeftHandedWeyl.basis k ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 2) ℂ j⟩ := by
  simp [basis, Module.Basis.tensorProduct_apply, valLinEquiv_symm_apply]

lemma jetMatrixAction_one : jetMatrixAction 1 = LinearMap.id := by
  apply (Lorentz.complexCoBasis.dualBasis.symmetricAlgebra.tensorProduct basis).ext
  rintro ⟨m, k, j⟩
  rw [Module.Basis.tensorProduct_apply', basis_apply, jetMatrixAction_tmul]
  fin_cases j <;> simp [Matrix.one_apply, apply_ite DerivAlgebraComplex.jetRingAction]

lemma jetMatrixAction_mul (A B : Matrix (Fin 2) (Fin 2) JetRing) :
    jetMatrixAction (A * B) = jetMatrixAction A ∘ₗ jetMatrixAction B := by
  apply (Lorentz.complexCoBasis.dualBasis.symmetricAlgebra.tensorProduct basis).ext
  rintro ⟨m, k, j⟩
  rw [Module.Basis.tensorProduct_apply', basis_apply]
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [jetMatrixAction_tmul, jetMatrixAction_tmul, map_sum]
  simp only [jetMatrixAction_tmul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← TensorProduct.sum_tmul]
  congr 1
  have h : DerivAlgebraComplex.jetRingAction ((A * B) i j) = ∑ l, DerivAlgebraComplex.jetRingAction (A i l) * DerivAlgebraComplex.jetRingAction (B l j) := by
    rw [Matrix.mul_apply,
      show DerivAlgebraComplex.jetRingAction (∑ l, A i l * B l j) = DerivAlgebraComplex.jetRingActionHom (∑ l, A i l * B l j) from rfl,
      map_sum]
    exact Finset.sum_congr rfl fun l _ => map_mul DerivAlgebraComplex.jetRingActionHom _ _
  rw [h, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun l _ => rfl

/-- The `(1, 2)_{-3}` action of the jet gauge group on the polynomial jet space of
  the lepton doublet: a jet of gauge transformations acts through the entrywise
  derivative action of its gauge matrix of power series on the derivative symbols,
  moving the weak index and fixing the Weyl factor. Its value acts by the gauge
  matrix, and its derivative coordinates act by the Leibniz rule. -/
noncomputable def repJetGaugeGroupI :
    Representation ℂ JetGaugeGroupI
      (SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ] LeptonDoublet) where
  toFun U := jetMatrixAction (jetGaugeMatrix U)
  map_one' := by
    rw [jetGaugeMatrix_one, jetMatrixAction_one]
    rfl
  map_mul' U₁ U₂ := by
    rw [jetGaugeMatrix_mul, jetMatrixAction_mul]
    rfl

@[simp]
lemma repJetGaugeGroupI_apply (U : JetGaugeGroupI)
    (x : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ] LeptonDoublet) :
    repJetGaugeGroupI U x = jetMatrixAction (jetGaugeMatrix U) x := rfl

/-- The entries of the gauge matrix of a jet of a constant gauge transformation are
  the constant power series with the global gauge coefficients. -/
lemma jetGaugeMatrix_ofConstant (g : GaugeGroupI) (i j : Fin 2) :
    jetGaugeMatrix (JetGaugeGroupI.ofConstant g) i j =
      MvPowerSeries.C ((star (g.toU1.1 : ℂ)) ^ 3 * g.toSU2.1 i j) := by
  rw [jetGaugeMatrix, Matrix.smul_apply,
    show (((JetGaugeGroupI.ofConstant g).2.2 : unitary JetRing) : JetRing) =
      MvPowerSeries.C ((g.toU1.1 : ℂ)) from rfl,
    show (((JetGaugeGroupI.ofConstant g).2.1 : specialUnitaryGroup (Fin 2) JetRing) :
        Matrix (Fin 2) (Fin 2) JetRing) i j =
      MvPowerSeries.C (g.toSU2.1 i j) from rfl,
    JetRing.star_C, ← map_pow, smul_eq_mul, ← map_mul]

/-- On jets of constant gauge transformations the jet action reduces to the global
  gauge action on the jet space: the `(1, 2)_{-3}` action on the target factor and
  the trivial action on the derivative symbols. -/
lemma repJetGaugeGroupI_ofConstant (g : GaugeGroupI) :
    repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) =
      TensorProduct.map LinearMap.id (repGaugeGroupI g) := by
  apply (Lorentz.complexCoBasis.dualBasis.symmetricAlgebra.tensorProduct basis).ext
  rintro ⟨m, k, j⟩
  rw [Module.Basis.tensorProduct_apply', basis_apply, repJetGaugeGroupI_apply,
    jetMatrixAction_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
    repGaugeGroupI_tmul_basis_eq_sum, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [jetGaugeMatrix_ofConstant, DerivAlgebraComplex.jetRingAction_C, LinearMap.smul_apply, LinearMap.id_apply]
  exact TensorProduct.smul_tmul _ _ _

/-- The jet action on a first-order derivative symbol is the Leibniz rule: the
  value of the gauge matrix multiplies the first-derivative symbol, and its first
  derivative feeds the field symbol, `∂_μ ψ_j ↦ ∑ i, A(0)_{ij} ∂_μ ψ_i +
  (∂_μ A)(0)_{ij} ψ_i` for `A = jetGaugeMatrix U`. -/
lemma repJetGaugeGroupI_ι_tmul (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3)
    (w : Fermion.LeftHandedWeyl) (j : Fin 2) :
    repJetGaugeGroupI U
        (SymmetricAlgebra.ι ℂ (Module.Dual ℂ Lorentz.CoℂModule) (Lorentz.complexCoBasis.dualBasis μ) ⊗ₜ[ℂ]
          ⟨w ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 2) ℂ j⟩) =
      ∑ i,
        (MvPowerSeries.constantCoeff (jetGaugeMatrix U i j) •
          (SymmetricAlgebra.ι ℂ (Module.Dual ℂ Lorentz.CoℂModule) (Lorentz.complexCoBasis.dualBasis μ) ⊗ₜ[ℂ]
            (⟨w ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 2) ℂ i⟩ : LeptonDoublet)) +
          MvPowerSeries.coeff (Finsupp.single μ 1) (jetGaugeMatrix U i j) •
            ((1 : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule)) ⊗ₜ[ℂ]
              (⟨w ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 2) ℂ i⟩ : LeptonDoublet))) := by
  rw [repJetGaugeGroupI_apply, jetMatrixAction_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [DerivAlgebraComplex.jetRingAction_apply_ι, TensorProduct.add_tmul, TensorProduct.smul_tmul',
    TensorProduct.smul_tmul']

end LeptonDoublet

end StandardModel
