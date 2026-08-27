/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.Jet.Basic
public import Physlib.Particles.StandardModel.Matter.JetComponentSpace.CovariantDeriv
public import Physlib.Particles.StandardModel.GaugeAlgebra.InfinitesimalAction
public import Physlib.Particles.StandardModel.Matter.JetComponentSpace.Basic
public import Physlib.Particles.StandardModel.GaugeBosons.GaugeJetAlgebra.GaugeAction
public import Physlib.Relativity.Tensors.ComplexTensor.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Analysis.Normed.Lp.Matrix
public import Mathlib.RingTheory.TensorProduct.Maps
/-!
# Down-type singlets

## i. Overview

The Standard Model down-type singlet is a right-handed Weyl spinor in the `(3, 1)_{-2}`
representation. Here charges are normalized as `6Y`, so `-2` is the usual hypercharge
`Y = -1/3`.

`DownSinglet` is the target vector space of one down-type quark multiplet. Its Weyl factor
carries the Lorentz index and its three-dimensional factor carries the colour index. The absence
of a weak factor makes it an `SU(2)` singlet.

The Lorentz and gauge actions are first defined separately. The gauge action is then computed on a
basis, used to identify its kernel, and descended to each supported global form of the Standard
Model gauge group.

## ii. Key results

- `DownSinglet` : the target space of the `(3, 1)_{-2}` multiplet.
- `repLorentzGroup` : the right-handed Lorentz action.
- `repGaugeGroupI` : the action of the unquotiented gauge group.
- `repGaugeGroupI_tmul_basis_eq_sum` : the gauge action in a tensor-product basis.
- `mem_repGaugeGroupI_ker_iff_eq` : the kernel of the full-group action.
- `gaugeGroup_subgroup_ℤ₆_le_ker_repGaugeGroupI` : triviality of the central `ℤ₆`.
- `repGaugeGroup` : the action descended to every supported gauge-group quotient.
- `gaugeAlgebraAction` : the infinitesimal `(3, 1)_{-2}` action of the gauge algebra.
- `repJetGaugeGroupI` : the jet gauge action on jets of the down singlet.
- `isInfinitesimalActionOf` : the gauge-algebra action is the infinitesimal action
  underlying the jet gauge action.

## iii. Table of contents

- A. The down-singlet space
- B. Linear structure
- C. Lorentz action
- D. Gauge action
- E. Kernel of the gauge action
- F. Descent to quotient gauge groups
- G. The action of the gauge algebra
- H. The representation of the jet gauge group
- I. The infinitesimal action underlies the jet gauge action

-/

@[expose] public section

namespace StandardModel

open TensorProduct

/-!

## A. The down-singlet space

The Weyl factor carries the right-handed Lorentz index, while
`EuclideanSpace ℂ (Fin 3)` carries the colour index.
-/

/-- The target vector space of one Standard Model down-type singlet quark.
It carries the `(3, 1)_{-2}` representation of the gauge group. -/
@[ext]
structure DownSinglet where
  /-- The right-handed Weyl spinor with its colour index. -/
  val : Fermion.RightHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3)

namespace DownSinglet

/-!

## B. Linear structure

`DownSinglet` wraps its tensor-product carrier as a distinct type. The equivalences below identify
the two types and transport the additive and complex module structures to `DownSinglet`.
-/

/-- Identifies a down-type singlet with its underlying tensor-product value. -/
def valEquiv : DownSinglet ≃ Fermion.RightHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3) where
  toFun := val
  invFun := fun m => ⟨m⟩

instance : AddCommGroup DownSinglet := Equiv.addCommGroup valEquiv

instance : Module ℂ DownSinglet := Equiv.module ℂ valEquiv

/-- The linear identification with the underlying tensor product. -/
def valLinEquiv : DownSinglet ≃ₗ[ℂ]
    Fermion.RightHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3) where
  toFun := val
  invFun := fun m => ⟨m⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp]
lemma valLinEquiv_apply (d : DownSinglet) : valLinEquiv d = d.val := rfl

lemma valLinEquiv_symm_apply
    (m : Fermion.RightHandedWeyl ⊗[ℂ] EuclideanSpace ℂ (Fin 3)) :
    valLinEquiv.symm m = ⟨m⟩ := rfl

@[simp]
lemma val_add (d₁ d₂ : DownSinglet) : (d₁ + d₂).val = d₁.val + d₂.val := rfl

@[simp]
lemma val_smul (r : ℂ) (d : DownSinglet) : (r • d).val = r • d.val := rfl

/-!

## The basis of the down-singlet space

-/

/-- A basis on the down singlets. -/
noncomputable def basis : Module.Basis (Fin 2 × Fin 3) ℂ DownSinglet :=
  (Fermion.RightHandedWeyl.basis.tensorProduct
    (EuclideanSpace.basisFun (Fin 3) ℂ).toBasis).map valLinEquiv.symm

instance : Module.Finite ℂ DownSinglet := Module.Finite.of_basis basis

instance : Module.Free ℂ DownSinglet := Module.Free.of_basis basis

/-!

## C. Lorentz action

The Lorentz group acts on the right-handed Weyl factor and leaves the colour index fixed.
-/

open Matrix MatrixGroups

open Representation in
/-- The right-handed Lorentz representation on down-type singlet quarks. -/
noncomputable def repLorentzGroup : Representation ℂ (SL(2,ℂ)) DownSinglet where
  toFun Λ := valLinEquiv.symm ∘ₗ
      TensorProduct.map (Fermion.RightHandedWeyl.rep Λ)
        (trivial ℂ (SL(2,ℂ)) (EuclideanSpace ℂ (Fin 3)) Λ) ∘ₗ
      valLinEquiv
  map_one' := by
    ext d
    simp [Module.End.one_eq_id]
  map_mul' Λ₁ Λ₂ := by
    ext1 d
    simp [TensorProduct.map_map, Module.End.mul_eq_comp]

/-!

## D. Gauge action

The `SU(3)` component acts on the colour index, while the `SU(2)` component acts trivially. The
`U(1)` action is `star z ^ 2`; since `z` is unitary, `star z = z⁻¹`, so this represents charge
`-2`.

The tensor and basis formulas below expose the coefficients used to compare actions and compute the
kernel.
-/

/-- The `(3, 1)_{-2}` action of the unquotiented Standard Model gauge group. -/
noncomputable def repGaugeGroupI : Representation ℂ GaugeGroupI DownSinglet where
  toFun g := valLinEquiv.symm ∘ₗ
      TensorProduct.map
        (LinearMap.id (M := Fermion.RightHandedWeyl))
        g.toSU3.1.toEuclideanLin ∘ₗ
      LinearMap.lsmul ℂ _ (star g.toU1.1 ^ 2 : ℂ) ∘ₗ
      valLinEquiv
  map_one' := by
    ext d
    simp [valLinEquiv_symm_apply]
  map_mul' g₁ g₂ := by
    ext d
    simp [smul_smul, mul_comm, TensorProduct.map_map, valLinEquiv_symm_apply]
    ring_nf

/-- The gauge action on a pure spinor–colour tensor. -/
lemma repGaugeGroupI_tmul (g : GaugeGroupI) (ψ : Fermion.RightHandedWeyl)
    (v : EuclideanSpace ℂ (Fin 3)) :
    repGaugeGroupI g ⟨ψ ⊗ₜ v⟩ =
      ⟨(star g.toU1.1 ^ 2) • ψ ⊗ₜ g.toSU3.1.toEuclideanLin v⟩ := rfl

open Fermion in
/-- Expands the gauge action in the spinor–colour basis. -/
lemma repGaugeGroupI_tmul_basis_eq_sum (g : GaugeGroupI) (k : Fin 2) (i : Fin 3) :
    repGaugeGroupI g
      ⟨RightHandedWeyl.basis k ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 3) ℂ i⟩ =
      ∑ i' : Fin 3, (star g.toU1.1 ^ 2 * g.toSU3.1 i' i) •
        (⟨RightHandedWeyl.basis k ⊗ₜ[ℂ]
          EuclideanSpace.basisFun (Fin 3) ℂ i'⟩ : DownSinglet) := by
  apply valLinEquiv.injective
  apply (((RightHandedWeyl.basis).tensorProduct
    (EuclideanSpace.basisFun (Fin 3) ℂ).toBasis)).repr.injective
  ext ⟨⟨k, l⟩, m⟩
  simp only [EuclideanSpace.basisFun_apply, repGaugeGroupI_tmul, valLinEquiv_apply, map_smul,
    Finsupp.coe_smul, Pi.smul_apply, Module.Basis.tensorProduct_repr_tmul_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr, ofLp_toLpLin,
    PiLp.ofLp_single, toLin'_apply, mulVec_single, MulOpposite.op_one, col_apply, one_smul,
    Module.Basis.repr_self, smul_eq_mul, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply,
    PiLp.single_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]
  ring

open Fermion in
/-- Two gauge elements induce the same action exactly when their hypercharge–colour coefficients
agree. -/
lemma repGaugeGroupI_eq_iff_mul_eq {g₁ g₂ : GaugeGroupI} :
    repGaugeGroupI g₁ = repGaugeGroupI g₂ ↔ ∀ i i',
      star g₁.toU1.1 ^ 2 * g₁.toSU3.1 i' i =
        star g₂.toU1.1 ^ 2 * g₂.toSU3.1 i' i := by
  let b := RightHandedWeyl.basis.tensorProduct
    (EuclideanSpace.basisFun (Fin 3) ℂ).toBasis
  constructor
  · intro h i i'
    have h' := congrFun (congrArg (fun f => f.1) h)
      ⟨RightHandedWeyl.basis 0 ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 3) ℂ i⟩
    simp only [Fin.isValue, LinearMap.coe_toAddHom, repGaugeGroupI_tmul_basis_eq_sum] at h'
    replace h' := congrArg b.repr (congrArg valLinEquiv h')
    simpa [Module.Basis.tensorProduct_repr_tmul_apply, -Fin.sum_univ_two, b] using
      congrArg (fun f => f (0, i')) h'
  · intro h
    apply (valLinEquiv.symm.eq_comp_toLinearMap_iff
      (repGaugeGroupI g₁) (repGaugeGroupI g₂)).mp
    apply b.ext
    rintro ⟨k, i⟩
    have h₁ := repGaugeGroupI_tmul_basis_eq_sum g₁ k i
    have h₂ := repGaugeGroupI_tmul_basis_eq_sum g₂ k i
    simp only [EuclideanSpace.basisFun_apply] at h₁ h₂
    simp [valLinEquiv_symm_apply, h₁, h₂, b]
    apply Finset.sum_congr rfl
    intro i' _
    have hi' : (starRingEnd ℂ) g₁.toU1.1 ^ 2 * g₁.toSU3.1 i' i =
        (starRingEnd ℂ) g₂.toU1.1 ^ 2 * g₂.toSU3.1 i' i := h i i'
    rw [hi']

/-!

## E. Kernel of the gauge action

An element acts trivially when its colour action is scalar and that scalar cancels its `U(1)`
phase. Its weak component is unrestricted because the down-type singlet is an `SU(2)` singlet.
-/

/-- Characterizes the full-group elements acting trivially on the down-type singlet. -/
lemma mem_repGaugeGroupI_ker_iff_eq {g : GaugeGroupI} :
    g ∈ repGaugeGroupI.ker ↔ ∃ a : ℂ,
      g.toSU3.1 = a • 1 ∧ a * star g.toU1.1 ^ 2 = 1 := by
  rw [MonoidHom.mem_ker, ← MonoidHom.map_one repGaugeGroupI, repGaugeGroupI_eq_iff_mul_eq]
  constructor
  · intro h
    have hc : star g.toU1.1 ^ 2 ≠ 0 := by
      apply pow_ne_zero
      rw [star_ne_zero]
      intro hzero
      have hu := Unitary.star_mul_self_of_mem g.toU1.2
      simp [hzero] at hu
    use g.toSU3.1 0 0
    simp only [map_one, OneMemClass.coe_one, Fin.forall_fin_succ, Fin.isValue,
      Fin.succ_zero_eq_one, IsEmpty.forall_iff, and_true, one_apply_eq, ne_eq,
      one_ne_zero, not_false_eq_true, one_apply_ne, mul_eq_zero, zero_ne_one,
      Fin.succ_one_eq_two, Fin.reduceEq, star_one, one_pow, one_mul] at h
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp <;> grind
    · grind
  · rintro ⟨a, h₁, h₂⟩ i i'
    simp only [Matrix.smul_apply, smul_eq_mul, h₁, map_one, OneMemClass.coe_one,
      star_one, one_pow, one_mul]
    linear_combination h₂ * (1 : Matrix _ _ ℂ) i' i

/-!

## F. Descent to quotient gauge groups

A representation descends through a quotient when the quotient subgroup lies in its kernel. For
the central `ℤ₆`, the colour phase is `x²` while the charge `-2` phase is `(star x)² = x⁻²`, so
their product is one.
-/

/-- The central `ℤ₆` subgroup acts trivially on `(3, 1)_{-2}`. -/
lemma gaugeGroup_subgroup_ℤ₆_le_ker_repGaugeGroupI :
    GaugeGroupQuot.subgroup .ℤ₆ ≤ repGaugeGroupI.ker := by
  simp only [GaugeGroupQuot.subgroup, gaugeGroupℤ₆SubGroup, SetLike.le_def,
    MonoidHom.mem_range, gaugeGroupℤ₆Hom_apply, Subtype.exists,
    mem_repGaugeGroupI_ker_iff_eq, forall_exists_index]
  rintro g x hx ⟨rfl⟩
  use x ^ 2
  simp only [gaugeGroupℤ₆OfRoot_toSU3, gaugeGroupℤ₆SU3OfRoot_eq_mul_id,
    gaugeGroupℤ₆OfRoot_toU1, gaugeGroupℤ₆UnitaryOfRoot_coe, true_and, RCLike.star_def,
    Complex.conj_rootsOfUnity hx, Units.val_inv_eq_inv_val, inv_pow]
  field_simp

/-- Every supported quotient subgroup acts trivially on the down-type singlet. -/
lemma gaugeGroup_subgroup_le_ker_repGaugeGroupI (Q : GaugeGroupQuot) :
    Q.subgroup ≤ repGaugeGroupI.ker := Q.subgroup_le_subgroup_ℤ₆.trans
  gaugeGroup_subgroup_ℤ₆_le_ker_repGaugeGroupI

/-- The `(3, 1)_{-2}` representation for every supported global form of the
Standard Model gauge group. -/
noncomputable def repGaugeGroup : (Q : GaugeGroupQuot) →
    Representation ℂ (GaugeGroup Q) DownSinglet
  | .I => repGaugeGroupI
  | .ℤ₆ => QuotientGroup.lift _ repGaugeGroupI (gaugeGroup_subgroup_le_ker_repGaugeGroupI .ℤ₆)
  | .ℤ₂ => QuotientGroup.lift _ repGaugeGroupI (gaugeGroup_subgroup_le_ker_repGaugeGroupI .ℤ₂)
  | .ℤ₃ => QuotientGroup.lift _ repGaugeGroupI (gaugeGroup_subgroup_le_ker_repGaugeGroupI .ℤ₃)

/-!

## The action of the gauge algebra

The infinitesimal `(3, 1)_{-2}` action of the gauge algebra on the down-type singlet:
the colour part of the algebra element acts on the colour index and the hypercharge
part scales, both through the physicists' factor of `i`, matching the group action
`(star u) ^ 2 • U₃` infinitesimally. The compatibility with the jet gauge action —
`GaugeAlgebra.IsInfinitesimalActionOf` — is proved at the end of this file.

-/

/-- The endomorphism of the down singlet defined by a `3 × 3` complex matrix acting on
  the colour index, with the Weyl factor untouched. -/
noncomputable def colourEnd (A : Matrix (Fin 3) (Fin 3) ℂ) :
    DownSinglet →ₗ[ℂ] DownSinglet :=
  valLinEquiv.symm.toLinearMap ∘ₗ
    Module.End.lTensorAlgHom ℂ (EuclideanSpace ℂ (Fin 3)) Fermion.RightHandedWeyl
      (Matrix.toLpLinAlgEquiv 2 A) ∘ₗ valLinEquiv.toLinearMap

lemma colourEnd_apply_mk (A : Matrix (Fin 3) (Fin 3) ℂ) (v : DownSinglet) :
    colourEnd A v
      = valLinEquiv.symm
          (Module.End.lTensorAlgHom ℂ (EuclideanSpace ℂ (Fin 3)) Fermion.RightHandedWeyl
            (Matrix.toLpLinAlgEquiv 2 A) (valLinEquiv v)) := rfl

lemma colourEnd_add (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    colourEnd (A + B) = colourEnd A + colourEnd B := by
  rw [colourEnd, colourEnd, colourEnd, map_add, map_add, LinearMap.add_comp,
    LinearMap.comp_add]

lemma colourEnd_smul (z : ℂ) (A : Matrix (Fin 3) (Fin 3) ℂ) :
    colourEnd (z • A) = z • colourEnd A := by
  rw [colourEnd, colourEnd, map_smul, map_smul, LinearMap.smul_comp,
    LinearMap.comp_smul]

lemma colourEnd_zero : colourEnd 0 = 0 := by
  rw [colourEnd, map_zero, map_zero, LinearMap.zero_comp, LinearMap.comp_zero]

lemma colourEnd_neg (A : Matrix (Fin 3) (Fin 3) ℂ) : colourEnd (-A) = -colourEnd A := by
  rw [show (-A : Matrix (Fin 3) (Fin 3) ℂ) = (-1 : ℂ) • A from by rw [neg_one_smul],
    colourEnd_smul, neg_one_smul]

lemma colourEnd_multiset_sum (m : Multiset (Matrix (Fin 3) (Fin 3) ℂ)) :
    colourEnd m.sum = (m.map colourEnd).sum := by
  induction m using Multiset.induction_on with
  | empty => simp [colourEnd_zero]
  | cons A t ih => rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons,
      colourEnd_add, ih]

/-- The colour endomorphisms compose through matrix multiplication. -/
lemma colourEnd_mul (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    colourEnd (A * B) = colourEnd A ∘ₗ colourEnd B := by
  refine LinearMap.ext fun v => ?_
  rw [colourEnd_apply_mk, map_mul, map_mul, LinearMap.comp_apply, colourEnd_apply_mk,
    colourEnd_apply_mk, LinearEquiv.apply_symm_apply]
  rfl

/-- The matrix of the infinitesimal `(3, 1)_{-2}` action of a gauge algebra element on
  the colour index: `i` times the colour part, shifted by `i` times `-2` the
  hypercharge. -/
noncomputable def actionMatrix (c : GaugeAlgebra) : Matrix (Fin 3) (Fin 3) ℂ :=
  Complex.I • (c.toSU3Matrix - ((2 : ℂ) • c.toU1Value) • 1)

/-- **The infinitesimal action of the gauge algebra on the down-type singlet**: the
  derivative of the `(3, 1)_{-2}` action of the gauge group, real-linear in the
  algebra slot and complex-linear in the value slot — the form consumed by the
  covariant derivative `IsGaugeField.covDerivIter` and by
  `GaugeAlgebra.IsInfinitesimalActionOf`. -/
noncomputable def gaugeAlgebraAction :
    GaugeAlgebra →ₗ[ℝ] DownSinglet →ₗ[ℂ] DownSinglet where
  toFun c := colourEnd (actionMatrix c)
  map_add' c₁ c₂ := by
    rw [show actionMatrix (c₁ + c₂) = actionMatrix c₁ + actionMatrix c₂ from by
      rw [actionMatrix, actionMatrix, actionMatrix, GaugeAlgebra.add_toSU3Matrix,
        GaugeAlgebra.add_toU1Value]
      module]
    rw [colourEnd_add]
  map_smul' r c := by
    rw [show actionMatrix (r • c) = (r : ℂ) • actionMatrix c from by
      rw [actionMatrix, actionMatrix, GaugeAlgebra.smul_toSU3Matrix,
        GaugeAlgebra.smul_toU1Value,
        show (r • c.toSU3Matrix : Matrix (Fin 3) (Fin 3) ℂ)
          = (r : ℂ) • c.toSU3Matrix from by
        rw [← algebraMap_smul ℂ r c.toSU3Matrix]; rfl,
        show r • c.toU1Value = (r : ℂ) • c.toU1Value from by
        rw [← algebraMap_smul ℂ r c.toU1Value]; rfl]
      module,
      colourEnd_smul]
    refine LinearMap.ext fun v => ?_
    rw [RingHom.id_apply]
    show (r : ℂ) • colourEnd (actionMatrix c) v = r • colourEnd (actionMatrix c) v
    rw [show ((r : ℝ) : ℂ) = algebraMap ℝ ℂ r from rfl, algebraMap_smul]

/-!

## The representation of the jet gauge group
-/

/-- Absorbs the jet ring into the colour index: a jet of a down-type singlet is the
same thing as a right-handed Weyl spinor tensored with a `JetRing`-valued colour
vector,

  `JetRing ⊗[ℂ] DownSinglet ≃ RightHandedWeyl ⊗[ℂ] EuclideanSpace JetRing (Fin 3)`.

-/
noncomputable def jetValLinEquiv :
    JetRing ⊗[ℂ] DownSinglet ≃ₗ[ℂ]
      Fermion.RightHandedWeyl ⊗[ℂ] EuclideanSpace JetRing (Fin 3) :=
  (TensorProduct.congr (LinearEquiv.refl ℂ JetRing) valLinEquiv).trans <|
    (TensorProduct.leftComm ℂ JetRing Fermion.RightHandedWeyl
        (EuclideanSpace ℂ (Fin 3))).trans <|
      TensorProduct.congr (LinearEquiv.refl ℂ Fermion.RightHandedWeyl) <|
        (TensorProduct.congr (LinearEquiv.refl ℂ JetRing)
            (WithLp.linearEquiv 2 ℂ (Fin 3 → ℂ))).trans <|
          ((TensorProduct.piScalarRight ℂ JetRing JetRing (Fin 3)).trans
            (WithLp.linearEquiv 2 JetRing (Fin 3 → JetRing)).symm).restrictScalars ℂ

/-- The `(3, 1)_{-2}` action of the jet gauge group on the jet space of the down-type
singlet. Through `jetValLinEquiv` the colour matrix of the gauge jet, carrying the
`-2` hypercharge phase `(star u) ^ 2`, acts `JetRing`-linearly on the colour factor by
matrix-vector multiplication, while the Weyl factor is untouched.

Both monoid laws come from bundled algebra maps — `Matrix.toLpLinAlgEquiv` and
`Module.End.lTensorAlgHom` are morphisms of algebras — so only the multiplicativity of
the colour-times-hypercharge matrix itself is checked. Note `Matrix.toLpLinAlgEquiv 2`
is the same map as the `Matrix.toEuclideanLin` used by `repGaugeGroupI`, which is an
abbreviation for `Matrix.toLpLin 2 2`, taken at the `CommRing` generality that
`JetRing` needs. -/
noncomputable def repJetGaugeGroupI :
    Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] DownSinglet) where
  toFun U :=
    jetValLinEquiv.symm.toLinearMap ∘ₗ
      Module.End.lTensorAlgHom ℂ (EuclideanSpace JetRing (Fin 3)) Fermion.RightHandedWeyl
        ((Matrix.toLpLinAlgEquiv 2
            (((star ((U.2.2 : unitary JetRing) : JetRing)) ^ 2) •
              ((U.1 : specialUnitaryGroup (Fin 3) JetRing) :
                Matrix (Fin 3) (Fin 3) JetRing))).restrictScalars ℂ) ∘ₗ
      jetValLinEquiv.toLinearMap
  map_one' := by
    have hres : (1 : Module.End JetRing (EuclideanSpace JetRing (Fin 3))).restrictScalars ℂ
        = 1 := rfl
    rw [show (((star (((1 : JetGaugeGroupI).2.2 : unitary JetRing) : JetRing)) ^ 2) •
          (((1 : JetGaugeGroupI).1 : specialUnitaryGroup (Fin 3) JetRing) :
            Matrix (Fin 3) (Fin 3) JetRing)) = 1 from by simp,
      map_one, hres, map_one]
    ext d x
    simp [-valLinEquiv_apply]
  map_mul' U₁ U₂ := by
    have hres : ∀ f g : Module.End JetRing (EuclideanSpace JetRing (Fin 3)),
        (f * g).restrictScalars ℂ = f.restrictScalars ℂ * g.restrictScalars ℂ :=
      fun _ _ => rfl
    have hM : (((star (((U₁ * U₂).2.2 : unitary JetRing) : JetRing)) ^ 2) •
          (((U₁ * U₂).1 : specialUnitaryGroup (Fin 3) JetRing) :
            Matrix (Fin 3) (Fin 3) JetRing)) =
        (((star ((U₁.2.2 : unitary JetRing) : JetRing)) ^ 2) •
            ((U₁.1 : specialUnitaryGroup (Fin 3) JetRing) :
              Matrix (Fin 3) (Fin 3) JetRing)) *
          (((star ((U₂.2.2 : unitary JetRing) : JetRing)) ^ 2) •
            ((U₂.1 : specialUnitaryGroup (Fin 3) JetRing) :
              Matrix (Fin 3) (Fin 3) JetRing)) := by
      rw [show (((U₁ * U₂).2.2 : unitary JetRing) : JetRing) =
            ((U₁.2.2 : unitary JetRing) : JetRing) * ((U₂.2.2 : unitary JetRing) : JetRing)
            from rfl,
        show (((U₁ * U₂).1 : specialUnitaryGroup (Fin 3) JetRing) :
              Matrix (Fin 3) (Fin 3) JetRing) =
            ((U₁.1 : specialUnitaryGroup (Fin 3) JetRing) : Matrix (Fin 3) (Fin 3) JetRing) *
              ((U₂.1 : specialUnitaryGroup (Fin 3) JetRing) : Matrix (Fin 3) (Fin 3) JetRing)
            from rfl,
        star_mul', mul_pow, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hM, map_mul, hres, map_mul]
    ext d x
    simp

/-- The identification of the jets of the down-type singlet intertwines multiplication by
a scalar jet with the `JetRing`-scalar action on the colour coordinates. -/
lemma jetValLinEquiv_smul (χ : JetRing) (z : JetRing ⊗[ℂ] DownSinglet) :
    jetValLinEquiv (χ • z)
      = Module.End.lTensorAlgHom ℂ (EuclideanSpace JetRing (Fin 3))
          Fermion.RightHandedWeyl
          ((LinearMap.lsmul JetRing (EuclideanSpace JetRing (Fin 3)) χ).restrictScalars ℂ)
          (jetValLinEquiv z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [smul_add, map_add, ha, hb, map_add, map_add]
  | tmul f x =>
    obtain ⟨v⟩ := x
    induction v using TensorProduct.induction_on with
    | zero =>
      rw [show ({ val := 0 } : DownSinglet) = 0 from rfl, TensorProduct.tmul_zero,
        smul_zero, map_zero, map_zero]
    | tmul ψ c =>
      rw [TensorProduct.smul_tmul', smul_eq_mul,
        show jetValLinEquiv ((χ * f) ⊗ₜ[ℂ] (⟨ψ ⊗ₜ[ℂ] c⟩ : DownSinglet))
          = ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun i => c.ofLp i • (χ * f)) from rfl,
        show jetValLinEquiv (f ⊗ₜ[ℂ] (⟨ψ ⊗ₜ[ℂ] c⟩ : DownSinglet))
          = ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun i => c.ofLp i • f) from rfl,
        show Module.End.lTensorAlgHom ℂ (EuclideanSpace JetRing (Fin 3))
            Fermion.RightHandedWeyl
            ((LinearMap.lsmul JetRing (EuclideanSpace JetRing (Fin 3)) χ).restrictScalars ℂ)
            (ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun i => c.ofLp i • f))
          = ψ ⊗ₜ[ℂ] (χ • WithLp.toLp 2 fun i => c.ofLp i • f) from rfl]
      congr 1
      refine WithLp.ofLp_injective 2 ?_
      funext i
      show c.ofLp i • (χ * f) = χ * (c.ofLp i • f)
      rw [Algebra.mul_smul_comm]
    | add a b ha hb =>
      rw [show ({ val := a + b } : DownSinglet) = ⟨a⟩ + ⟨b⟩ from rfl,
        TensorProduct.tmul_add, smul_add, map_add, ha, hb, map_add, map_add]

/-- **The jet gauge action on the jets of the down-type singlet is fibrewise**: it
commutes with multiplication by scalar jets, acting on the values of the field over the
identity on spacetime. -/
lemma repJetGaugeGroupI_smul (U : JetGaugeGroupI) (χ : JetRing)
    (z : JetRing ⊗[ℂ] DownSinglet) :
    repJetGaugeGroupI U (χ • z) = χ • repJetGaugeGroupI U z := by
  set S : Module.End JetRing (EuclideanSpace JetRing (Fin 3)) :=
    LinearMap.lsmul JetRing (EuclideanSpace JetRing (Fin 3)) χ with hS
  set M : Module.End JetRing (EuclideanSpace JetRing (Fin 3)) :=
    (Matrix.toLpLinAlgEquiv 2
      (((star ((U.2.2 : unitary JetRing) : JetRing)) ^ 2) •
        ((U.1 : specialUnitaryGroup (Fin 3) JetRing) :
          Matrix (Fin 3) (Fin 3) JetRing)) :
      Module.End JetRing (EuclideanSpace JetRing (Fin 3))) with hM
  have hMS : M * S = S * M := LinearMap.ext fun e => by
    simp only [Module.End.mul_apply, hS, LinearMap.lsmul_apply, map_smul]
  apply jetValLinEquiv.injective
  rw [show repJetGaugeGroupI U (χ • z)
      = jetValLinEquiv.symm (Module.End.lTensorAlgHom ℂ _ Fermion.RightHandedWeyl
          (M.restrictScalars ℂ) (jetValLinEquiv (χ • z))) from rfl,
    LinearEquiv.apply_symm_apply, jetValLinEquiv_smul,
    show repJetGaugeGroupI U z
      = jetValLinEquiv.symm (Module.End.lTensorAlgHom ℂ _ Fermion.RightHandedWeyl
          (M.restrictScalars ℂ) (jetValLinEquiv z)) from rfl,
    jetValLinEquiv_smul, LinearEquiv.apply_symm_apply, ← Module.End.mul_apply,
    ← Module.End.mul_apply, ← map_mul, ← map_mul,
    show M.restrictScalars ℂ * S.restrictScalars ℂ = (M * S).restrictScalars ℂ from rfl,
    show S.restrictScalars ℂ * M.restrictScalars ℂ = (S * M).restrictScalars ℂ from rfl,
    hMS]

/-- On jets of constant gauge transformations the jet action reduces to the global
gauge action on the fibre: the `(3, 1)_{-2}` action on the down-singlet factor, and the
trivial action on the jet ring. -/
lemma repJetGaugeGroupI_ofConstant (g : GaugeGroupI) :
    repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) =
      TensorProduct.map LinearMap.id (repGaugeGroupI g) := by
  ext d x
  obtain ⟨v⟩ := x
  induction v using TensorProduct.induction_on with
  | zero => simp [show ({ val := 0 } : DownSinglet) = 0 from rfl]
  | tmul psi c =>
      apply jetValLinEquiv.injective
      simp [repJetGaugeGroupI, jetValLinEquiv, repGaugeGroupI]
      have hu : star (((JetGaugeGroupI.ofConstant g).2.2 : unitary JetRing) : JetRing)
          = MvPowerSeries.C ((starRingEnd ℂ) (g.toU1.1 : ℂ)) := by
        rw [show (((JetGaugeGroupI.ofConstant g).2.2 : unitary JetRing) : JetRing)
          = MvPowerSeries.C ((g.toU1.1 : ℂ)) from rfl, JetRing.star_C]
        rfl
      have hM : ∀ i j, (((JetGaugeGroupI.ofConstant g).1 :
            specialUnitaryGroup (Fin 3) JetRing) : Matrix (Fin 3) (Fin 3) JetRing) i j
          = MvPowerSeries.C (g.toSU3.1 i j) := fun _ _ => rfl
      have halg : ∀ A : Matrix (Fin 3) (Fin 3) JetRing,
          (Matrix.toLpLinAlgEquiv 2 A :
              Module.End JetRing (EuclideanSpace JetRing (Fin 3)))
            = Matrix.toLpLin 2 2 A := fun _ => rfl
      have hvec : ∀ i : Fin 3,
          (∑ x, MvPowerSeries.C ((g.toSU3.1) i x) * (MvPowerSeries.C (c.ofLp x) * d))
            = MvPowerSeries.C (∑ x, (g.toSU3.1) i x * c.ofLp x) * d := by
        intro i
        rw [map_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun x _ => by rw [← mul_assoc, ← map_mul]
      rw [TensorProduct.liftAux_tmul, ← TensorProduct.tmul_smul]
      simp only [LinearMap.compl₂_apply, TensorProduct.mk_apply, LinearMap.smul_apply,
        LinearMap.restrictScalars_apply, halg, Matrix.toLpLin_toLp]
      congr 1
      refine WithLp.ofLp_injective 2 ?_
      funext i
      simp only [WithLp.ofLp_smul, Pi.smul_apply, Matrix.toLin'_apply,
        Matrix.mulVec_apply_eq_sum, hM, Algebra.smul_def, MvPowerSeries.algebraMap_apply,
        hu, map_pow, Algebra.algebraMap_self_apply]
      rw [hvec i]
  | add a b ha hb =>
      simp only [show ({ val := a + b } : DownSinglet) = ⟨a⟩ + ⟨b⟩ from rfl,
        map_add, ha, hb]

/-!

## The infinitesimal action underlies the jet gauge action

The `(3, 1)_{-2}` action of the gauge algebra is the infinitesimal action underlying the
jet gauge action, in the sense of `GaugeAlgebra.IsInfinitesimalActionOf`: the base-point
Taylor coefficients of the jet action satisfy the Maurer–Cartan Leibniz law and
intertwine the action with the adjoint transports. The proofs work through the colour
matrix of the jet action and the all-orders matrix Leibniz rule at the base point.

-/

section InfinitesimalAction

open MvPowerSeries

/-- A single formal derivative commutes with the iterated one. -/
private lemma pderiv_foldl (μ : Fin 1 ⊕ Fin 3) (x : Multiset (Fin 1 ⊕ Fin 3))
    (f : JetRing) :
    pderiv ℂ μ (x.foldl (fun h ρ => pderiv ℂ ρ h) f)
      = x.foldl (fun h ρ => pderiv ℂ ρ h) (pderiv ℂ μ f) := by
  induction x using Multiset.induction_on generalizing f with
  | empty => rfl
  | cons ν t ih =>
    rw [Multiset.foldl_cons, Multiset.foldl_cons, ih, JetRing.pderiv_comm]

/-- The iterated formal derivative is `ℂ`-homogeneous. -/
private lemma foldl_pderiv_smul (x : Multiset (Fin 1 ⊕ Fin 3)) (z : ℂ) (f : JetRing) :
    x.foldl (fun h ρ => pderiv ℂ ρ h) (z • f)
      = z • x.foldl (fun h ρ => pderiv ℂ ρ h) f := by
  induction x using Multiset.induction_on generalizing f with
  | empty => rfl
  | cons ν t ih => rw [Multiset.foldl_cons, Derivation.map_smul, ih, Multiset.foldl_cons]

/-- The iterated formal derivative of a difference. -/
private lemma foldl_pderiv_sub (x : Multiset (Fin 1 ⊕ Fin 3)) (f g : JetRing) :
    x.foldl (fun h ρ => pderiv ℂ ρ h) (f - g)
      = x.foldl (fun h ρ => pderiv ℂ ρ h) f - x.foldl (fun h ρ => pderiv ℂ ρ h) g := by
  induction x using Multiset.induction_on generalizing f g with
  | empty => rfl
  | cons ν t ih => rw [Multiset.foldl_cons, map_sub, ih, Multiset.foldl_cons,
      Multiset.foldl_cons]

/-- The jet-valued matrix of the infinitesimal `(3, 1)_{-2}` action of a jet of gauge
  algebra elements: the jet analogue of `actionMatrix`. -/
noncomputable def jetActionMatrix (a : JetGaugeAlgebra) : Matrix (Fin 3) (Fin 3) JetRing :=
  Complex.I • (a.toSU3Matrix - ((2 : ℂ) • a.toU1Value) • 1)

/-- The base-point Taylor coefficients of the jet action matrix are the action matrices
  of the base-point Taylor coefficients. -/
lemma jetActionMatrix_map_cc_foldl (p : Multiset (Fin 1 ⊕ Fin 3)) (a : JetGaugeAlgebra) :
    ((jetActionMatrix a).map fun f =>
        constantCoeff (p.foldl (fun h ρ => pderiv ℂ ρ h) f))
      = actionMatrix (JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv p a)) := by
  ext i j
  rw [Matrix.map_apply, jetActionMatrix, actionMatrix, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.smul_apply, foldl_pderiv_smul, constantCoeff_smul, foldl_pderiv_sub,
    map_sub, JetGaugeAlgebra.eval_iteratedDeriv_toSU3Matrix, Matrix.map_apply]
  congr 2
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, smul_eq_mul, mul_one, smul_eq_mul,
      mul_one, foldl_pderiv_smul, constantCoeff_smul,
      JetGaugeAlgebra.eval_iteratedDeriv_toU1Value]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, smul_zero, smul_zero,
      JetRing.foldl_pderiv_zero, map_zero]

/-- The `JetRing`-valued colour matrix of the jet gauge action on the down singlet: the
  colour matrix of the gauge jet carrying the `-2` hypercharge phase. -/
noncomputable def downMatrix (U : JetGaugeGroupI) : Matrix (Fin 3) (Fin 3) JetRing :=
  ((star ((U.2.2 : unitary JetRing) : JetRing)) ^ 2) •
    ((U.1 : specialUnitaryGroup (Fin 3) JetRing) : Matrix (Fin 3) (Fin 3) JetRing)

lemma repJetGaugeGroupI_eq_downMatrix (U : JetGaugeGroupI)
    (z : JetRing ⊗[ℂ] DownSinglet) :
    repJetGaugeGroupI U z
      = jetValLinEquiv.symm
          (Module.End.lTensorAlgHom ℂ (EuclideanSpace JetRing (Fin 3))
            Fermion.RightHandedWeyl
            ((Matrix.toLpLinAlgEquiv 2 (downMatrix U)).restrictScalars ℂ)
            (jetValLinEquiv z)) := rfl

/-- The entrywise formal derivative on the colour coordinates, as a `ℂ`-linear map. -/
private noncomputable def pderivColour (μ : Fin 1 ⊕ Fin 3) :
    EuclideanSpace JetRing (Fin 3) →ₗ[ℂ] EuclideanSpace JetRing (Fin 3) where
  toFun v := WithLp.toLp 2 fun i => pderiv ℂ μ (v.ofLp i)
  map_add' v w := by
    refine WithLp.ofLp_injective 2 ?_
    funext i
    exact map_add _ _ _
  map_smul' z v := by
    refine WithLp.ofLp_injective 2 ?_
    funext i
    exact Derivation.map_smul _ _ _

/-- The entrywise iterated formal derivative on the colour coordinates. -/
private noncomputable def foldColour (x : Multiset (Fin 1 ⊕ Fin 3)) :
    EuclideanSpace JetRing (Fin 3) →ₗ[ℂ] EuclideanSpace JetRing (Fin 3) where
  toFun v := WithLp.toLp 2 fun i => x.foldl (fun h ρ => pderiv ℂ ρ h) (v.ofLp i)
  map_add' v w := by
    refine WithLp.ofLp_injective 2 ?_
    funext i
    exact JetRing.foldl_pderiv_add x _ _
  map_smul' z v := by
    refine WithLp.ofLp_injective 2 ?_
    funext i
    exact foldl_pderiv_smul x z _

/-- The entrywise base-point evaluation on the colour coordinates. -/
private noncomputable def ccColour :
    EuclideanSpace JetRing (Fin 3) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3) where
  toFun v := WithLp.toLp 2 fun i => constantCoeff (v.ofLp i)
  map_add' v w := by
    refine WithLp.ofLp_injective 2 ?_
    funext i
    exact map_add _ _ _
  map_smul' z v := by
    refine WithLp.ofLp_injective 2 ?_
    funext i
    exact constantCoeff_smul _ _

private lemma pderivColour_comp_foldColour (μ : Fin 1 ⊕ Fin 3)
    (x : Multiset (Fin 1 ⊕ Fin 3)) :
    pderivColour μ ∘ₗ foldColour x = foldColour (μ ::ₘ x) := by
  refine LinearMap.ext fun v => ?_
  refine WithLp.ofLp_injective 2 ?_
  funext i
  show pderiv ℂ μ (x.foldl (fun h ρ => pderiv ℂ ρ h) (v.ofLp i))
    = (μ ::ₘ x).foldl (fun h ρ => pderiv ℂ ρ h) (v.ofLp i)
  rw [Multiset.foldl_cons, pderiv_foldl]

/-- The identification of down-singlet jets intertwines the formal derivative with the
  entrywise derivative on the colour coordinates. -/
private lemma jetValLinEquiv_jetDeriv (μ : Fin 1 ⊕ Fin 3)
    (z : JetRing ⊗[ℂ] DownSinglet) :
    jetValLinEquiv (StandardModel.jetDeriv μ z)
      = (TensorProduct.map LinearMap.id (pderivColour μ)) (jetValLinEquiv z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  | tmul f d =>
    obtain ⟨w⟩ := d
    induction w using TensorProduct.induction_on with
    | zero =>
      rw [show ({ val := 0 } : DownSinglet) = 0 from rfl, TensorProduct.tmul_zero,
        map_zero, map_zero, map_zero]
    | tmul ψ c =>
      rw [show StandardModel.jetDeriv μ (f ⊗ₜ[ℂ] (⟨ψ ⊗ₜ[ℂ] c⟩ : DownSinglet))
          = (pderiv ℂ μ f) ⊗ₜ[ℂ] (⟨ψ ⊗ₜ[ℂ] c⟩ : DownSinglet) from rfl,
        show jetValLinEquiv ((pderiv ℂ μ f) ⊗ₜ[ℂ] (⟨ψ ⊗ₜ[ℂ] c⟩ : DownSinglet))
          = ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun i => c.ofLp i • pderiv ℂ μ f) from rfl,
        show jetValLinEquiv (f ⊗ₜ[ℂ] (⟨ψ ⊗ₜ[ℂ] c⟩ : DownSinglet))
          = ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun i => c.ofLp i • f) from rfl,
        TensorProduct.map_tmul, LinearMap.id_apply]
      congr 1
      refine WithLp.ofLp_injective 2 ?_
      funext i
      exact (Derivation.map_smul (pderiv ℂ μ) (c.ofLp i) f).symm
    | add a b ha hb =>
      rw [show ({ val := a + b } : DownSinglet) = ⟨a⟩ + ⟨b⟩ from rfl,
        TensorProduct.tmul_add, map_add, map_add, ha, hb, map_add, map_add]

/-- The identification of down-singlet jets intertwines the iterated formal derivative
  with the entrywise iterated derivative on the colour coordinates. -/
private lemma jetValLinEquiv_jetIteratedDeriv (x : Multiset (Fin 1 ⊕ Fin 3))
    (z : JetRing ⊗[ℂ] DownSinglet) :
    jetValLinEquiv (StandardModel.jetIteratedDeriv x z)
      = (TensorProduct.map LinearMap.id (foldColour x)) (jetValLinEquiv z) := by
  induction x using Multiset.induction_on with
  | empty =>
    rw [StandardModel.jetIteratedDeriv_zero, LinearMap.id_apply,
      show foldColour 0 = LinearMap.id from LinearMap.ext fun v =>
        WithLp.ofLp_injective 2 rfl,
      TensorProduct.map_id, LinearMap.id_apply]
  | cons μ t ih =>
    rw [StandardModel.jetIteratedDeriv_cons, LinearMap.comp_apply,
      jetValLinEquiv_jetDeriv, ih, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
      LinearMap.id_comp, pderivColour_comp_foldColour]

/-- The base-point evaluation of a down-singlet jet through the colour coordinates. -/
private lemma valLinEquiv_jetEval (z : JetRing ⊗[ℂ] DownSinglet) :
    valLinEquiv (StandardModel.jetEval z)
      = (TensorProduct.map LinearMap.id ccColour) (jetValLinEquiv z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp; rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  | tmul f d =>
    obtain ⟨w⟩ := d
    induction w using TensorProduct.induction_on with
    | zero =>
      rw [show ({ val := 0 } : DownSinglet) = 0 from rfl, TensorProduct.tmul_zero]
      simp
      rfl
    | tmul ψ c =>
      rw [StandardModel.jetEval_tmul, map_smul,
        show valLinEquiv (⟨ψ ⊗ₜ[ℂ] c⟩ : DownSinglet) = ψ ⊗ₜ[ℂ] c from rfl,
        show jetValLinEquiv (f ⊗ₜ[ℂ] (⟨ψ ⊗ₜ[ℂ] c⟩ : DownSinglet))
          = ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun i => c.ofLp i • f) from rfl,
        TensorProduct.map_tmul, LinearMap.id_apply, ← TensorProduct.tmul_smul]
      congr 1
      refine WithLp.ofLp_injective 2 ?_
      funext i
      show (constantCoeff f • c).ofLp i = constantCoeff (c.ofLp i • f)
      simp [constantCoeff_smul, mul_comm]
    | add a b ha hb =>
      rw [show ({ val := a + b } : DownSinglet) = ⟨a⟩ + ⟨b⟩ from rfl,
        TensorProduct.tmul_add, map_add, map_add, ha, hb, map_add, map_add]

set_option maxHeartbeats 1000000 in
/-- **The derivative identity** for the colour matrix of the jet gauge action: the
  formal derivative of the colour matrix is minus the jet action matrix of the
  Maurer–Cartan form times the colour matrix. -/
lemma downMatrix_map_pderiv (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) :
    (downMatrix U).map (fun f => pderiv ℂ μ f)
      = -(jetActionMatrix (maurerCartanForm U μ) * downMatrix U) := by
  have hleib : ∀ f g : JetRing,
      pderiv ℂ μ (f * g) = pderiv ℂ μ f * g + f * pderiv ℂ μ g := fun f g => by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, add_comm, mul_comm g]
  have huu : ((U.2.2 : unitary JetRing) : JetRing)
      * star ((U.2.2 : unitary JetRing) : JetRing) = 1 :=
    Unitary.mul_star_self_of_mem (U.2.2 : unitary JetRing).2
  have hU₃u : star U.1.1 * U.1.1 = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp U.1.2).1
  have h0 : pderiv ℂ μ ((U.2.2 : unitary JetRing) : JetRing)
        * star ((U.2.2 : unitary JetRing) : JetRing)
      + ((U.2.2 : unitary JetRing) : JetRing)
        * pderiv ℂ μ (star ((U.2.2 : unitary JetRing) : JetRing)) = 0 := by
    have h := congrArg (pderiv ℂ μ) huu
    rw [hleib, Derivation.map_one_eq_zero] at h
    exact h
  have hsu : pderiv ℂ μ (star ((U.2.2 : unitary JetRing) : JetRing))
      = -(pderiv ℂ μ ((U.2.2 : unitary JetRing) : JetRing)
          * (star ((U.2.2 : unitary JetRing) : JetRing)
            * star ((U.2.2 : unitary JetRing) : JetRing))) := by
    have h1 : star ((U.2.2 : unitary JetRing) : JetRing)
        * (pderiv ℂ μ ((U.2.2 : unitary JetRing) : JetRing)
            * star ((U.2.2 : unitary JetRing) : JetRing)
          + ((U.2.2 : unitary JetRing) : JetRing)
            * pderiv ℂ μ (star ((U.2.2 : unitary JetRing) : JetRing))) = 0 := by
      rw [h0, mul_zero]
    linear_combination h1
      - pderiv ℂ μ (star ((U.2.2 : unitary JetRing) : JetRing)) * huu
  have hm₃U₃ : (maurerCartanForm U μ).toSU3Matrix * U.1.1
      = Complex.I • U.1.1.map (pderiv ℂ μ) := by
    rw [maurerCartanForm_toSU3Matrix, Matrix.smul_mul, Matrix.mul_assoc, hU₃u,
      Matrix.mul_one]
  have hiC : (algebraMap ℂ JetRing) Complex.I * (algebraMap ℂ JetRing) Complex.I
      = -1 := by
    rw [← map_mul, Complex.I_mul_I, map_neg, map_one]
  have hmap : ((((star ((U.2.2 : unitary JetRing) : JetRing)) ^ 2) •
        ((U.1 : specialUnitaryGroup (Fin 3) JetRing) :
          Matrix (Fin 3) (Fin 3) JetRing)).map fun f => pderiv ℂ μ f)
      = (pderiv ℂ μ ((star ((U.2.2 : unitary JetRing) : JetRing)) ^ 2)) • U.1.1
        + ((star ((U.2.2 : unitary JetRing) : JetRing)) ^ 2)
          • (U.1.1.map (pderiv ℂ μ)) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    exact hleib _ _
  rw [downMatrix, jetActionMatrix, hmap, Matrix.smul_mul, Matrix.sub_mul,
    Matrix.mul_smul, hm₃U₃, Matrix.smul_mul, Matrix.one_mul,
    smul_comm ((star ((U.2.2 : unitary JetRing) : JetRing)) ^ 2) Complex.I,
    smul_sub, smul_smul Complex.I Complex.I, Complex.I_mul_I, neg_one_smul,
    ← smul_assoc, neg_sub, sub_neg_eq_add, smul_smul]
  congr 1
  congr 1
  rw [maurerCartanForm_toU1Value, sq, hleib, hsu, Algebra.smul_def,
    Algebra.smul_def, Algebra.smul_def, map_ofNat]
  linear_combination (-(2 * pderiv ℂ μ ((U.2.2 : unitary JetRing) : JetRing)
    * star ((U.2.2 : unitary JetRing) : JetRing)
    * star ((U.2.2 : unitary JetRing) : JetRing)
    * star ((U.2.2 : unitary JetRing) : JetRing))) * hiC

/-- **The equivariance identity** for the colour matrix of the jet gauge action: the
  colour matrix intertwines the constant jet action matrix with its adjoint
  transform. -/
lemma downMatrix_mul_jetActionMatrix (U : JetGaugeGroupI) (c : GaugeAlgebra) :
    downMatrix U * jetActionMatrix (JetGaugeAlgebra.ofConstant c)
      = jetActionMatrix (JetGaugeAlgebra.adjointMap U (JetGaugeAlgebra.ofConstant c))
        * downMatrix U := by
  have hU₃u : star U.1.1 * U.1.1 = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp U.1.2).1
  rw [downMatrix, jetActionMatrix, jetActionMatrix,
    JetGaugeAlgebra.adjointMap_toSU3Matrix, JetGaugeAlgebra.adjointMap_toU1Value]
  conv_lhs => rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.mul_smul,
    Matrix.mul_one]
  conv_rhs => rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc, hU₃u, Matrix.mul_one]
  rw [smul_sub, smul_comm ((star ((U.2.2 : unitary JetRing) : JetRing)) ^ 2)
    ((2 : ℂ) • (JetGaugeAlgebra.ofConstant c).toU1Value)]

/-- The iterated formal derivative of a negation. -/
private lemma foldl_pderiv_neg (x : Multiset (Fin 1 ⊕ Fin 3)) (f : JetRing) :
    x.foldl (fun h ρ => pderiv ℂ ρ h) (-f)
      = -(x.foldl (fun h ρ => pderiv ℂ ρ h) f) := by
  induction x using Multiset.induction_on generalizing f with
  | empty => rfl
  | cons ν t ih => rw [Multiset.foldl_cons, map_neg, ih, Multiset.foldl_cons]

set_option maxHeartbeats 1000000 in
/-- **The base-point Taylor coefficients of the jet gauge action** on the down-type
  singlet are the colour endomorphisms of the base-point Taylor coefficients of the
  colour matrix. -/
lemma repCoeff_eq (U : JetGaugeGroupI) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    IsGaugeField.repCoeff repJetGaugeGroupI U x
      = colourEnd ((downMatrix U).map fun f =>
          constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f)) := by
  refine LinearMap.ext fun d => ?_
  apply valLinEquiv.injective
  rw [show IsGaugeField.repCoeff repJetGaugeGroupI U x d
      = StandardModel.jetEval (StandardModel.jetIteratedDeriv x
          (repJetGaugeGroupI U (StandardModel.jetOfConstant d))) from rfl,
    valLinEquiv_jetEval, jetValLinEquiv_jetIteratedDeriv,
    colourEnd_apply_mk, LinearEquiv.apply_symm_apply,
    repJetGaugeGroupI_eq_downMatrix, LinearEquiv.apply_symm_apply,
    StandardModel.jetOfConstant_apply]
  obtain ⟨w⟩ := d
  induction w using TensorProduct.induction_on with
  | zero =>
    rw [show ({ val := 0 } : DownSinglet) = 0 from rfl, TensorProduct.tmul_zero]
    simp
    rw [show (0 : DownSinglet).val = 0 from rfl, map_zero]
  | add a b ha hb =>
    rw [show ({ val := a + b } : DownSinglet) = ⟨a⟩ + ⟨b⟩ from rfl,
      TensorProduct.tmul_add, map_add, map_add, map_add, map_add, ha, hb, map_add,
      map_add]
  | tmul ψ c =>
    rw [show jetValLinEquiv ((1 : JetRing) ⊗ₜ[ℂ] (⟨ψ ⊗ₜ[ℂ] c⟩ : DownSinglet))
        = ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun i => c.ofLp i • (1 : JetRing)) from rfl,
      show (Module.End.lTensorAlgHom ℂ (EuclideanSpace JetRing (Fin 3))
          Fermion.RightHandedWeyl
          ((Matrix.toLpLinAlgEquiv 2 (downMatrix U)).restrictScalars ℂ))
          (ψ ⊗ₜ[ℂ] (WithLp.toLp 2 fun i => c.ofLp i • (1 : JetRing)))
        = ψ ⊗ₜ[ℂ] ((Matrix.toLpLinAlgEquiv 2 (downMatrix U))
            (WithLp.toLp 2 fun i => c.ofLp i • (1 : JetRing))) from rfl,
      TensorProduct.map_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
      LinearMap.id_apply,
      show valLinEquiv (⟨ψ ⊗ₜ[ℂ] c⟩ : DownSinglet) = ψ ⊗ₜ[ℂ] c from rfl,
      show (Module.End.lTensorAlgHom ℂ (EuclideanSpace ℂ (Fin 3))
          Fermion.RightHandedWeyl
          (Matrix.toLpLinAlgEquiv 2 ((downMatrix U).map fun f =>
            constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f)))) (ψ ⊗ₜ[ℂ] c)
        = ψ ⊗ₜ[ℂ] ((Matrix.toLpLinAlgEquiv 2 ((downMatrix U).map fun f =>
            constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f))) c) from rfl]
    congr 1
    refine WithLp.ofLp_injective 2 ?_
    funext j
    show constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h)
        (((Matrix.toLpLinAlgEquiv 2 (downMatrix U))
          (WithLp.toLp 2 fun i => c.ofLp i • (1 : JetRing))).ofLp j))
      = ((Matrix.toLpLinAlgEquiv 2 ((downMatrix U).map fun f =>
          constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f))) c).ofLp j
    rw [show ((Matrix.toLpLinAlgEquiv 2 (downMatrix U))
          (WithLp.toLp 2 fun i => c.ofLp i • (1 : JetRing))).ofLp j
        = ∑ k, downMatrix U j k * (c.ofLp k • (1 : JetRing)) from by
        simp [Matrix.toLpLin_toLp, Matrix.toLin'_apply, Matrix.mulVec_eq_sum,
          Finset.sum_apply, mul_comm],
      show ((Matrix.toLpLinAlgEquiv 2 ((downMatrix U).map fun f =>
          constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f))) c).ofLp j
        = ∑ k, constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) (downMatrix U j k))
            * c.ofLp k from by
        simp [Matrix.toLpLin_toLp, Matrix.toLin'_apply, Matrix.mulVec_eq_sum,
          Finset.sum_apply, mul_comm],
      JetRing.foldl_pderiv_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_smul_comm, mul_one, foldl_pderiv_smul, constantCoeff_smul, smul_eq_mul,
      mul_comm]

set_option maxHeartbeats 1000000 in
/-- **The `(3, 1)_{-2}` action of the gauge algebra is the infinitesimal action
  underlying the jet gauge action on the down-type singlet**: its base-point Taylor
  coefficients obey the Maurer–Cartan Leibniz law and intertwine the action with the
  adjoint transports. -/
theorem isInfinitesimalActionOf :
    GaugeAlgebra.IsInfinitesimalActionOf gaugeAlgebraAction repJetGaugeGroupI := by
  constructor
  · intro U μ x
    have hMcons : ((downMatrix U).map fun f =>
        constantCoeff ((μ ::ₘ x).foldl (fun h ρ => pderiv ℂ ρ h) f))
        = -((x.antidiagonal.map fun p =>
            actionMatrix (JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv p.1
              (maurerCartanForm U μ)))
            * ((downMatrix U).map fun f =>
                constantCoeff (p.2.foldl (fun h ρ => pderiv ℂ ρ h) f))).sum) := by
      rw [show ((downMatrix U).map fun f =>
            constantCoeff ((μ ::ₘ x).foldl (fun h ρ => pderiv ℂ ρ h) f))
          = (((downMatrix U).map fun f => pderiv ℂ μ f).map fun f =>
              constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f)) from
          Matrix.ext fun i j => by
            rw [Matrix.map_apply, Matrix.map_apply, Matrix.map_apply,
              Multiset.foldl_cons],
        downMatrix_map_pderiv,
        show ((-(jetActionMatrix (maurerCartanForm U μ) * downMatrix U)).map fun f =>
            constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f))
          = -(((jetActionMatrix (maurerCartanForm U μ) * downMatrix U)).map fun f =>
              constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f)) from
          Matrix.ext fun i j => by
            rw [Matrix.map_apply, Matrix.neg_apply, Matrix.neg_apply,
              Matrix.map_apply, foldl_pderiv_neg, map_neg],
        matrix_constantCoeff_foldl_pderiv_mul]
      exact congrArg Neg.neg (congrArg Multiset.sum (Multiset.map_congr rfl
        fun p hp => by rw [jetActionMatrix_map_cc_foldl]))
    rw [repCoeff_eq, hMcons, colourEnd_neg, colourEnd_multiset_sum, Multiset.map_map]
    refine congrArg Neg.neg (congrArg Multiset.sum (Multiset.map_congr rfl
      fun p hp => ?_))
    rw [Function.comp_apply, colourEnd_mul, repCoeff_eq]
    rfl
  · intro U x c
    have hCsmul : ∀ z w : ℂ, (z • (C w : JetRing)) = C (z * w) := fun z w => by
      rw [Algebra.smul_def, MvPowerSeries.algebraMap_apply,
        Algebra.algebraMap_self_apply, ← map_mul]
    have hconst : jetActionMatrix (JetGaugeAlgebra.ofConstant c)
        = (actionMatrix c).map (C : ℂ → JetRing) := by
      refine Matrix.ext fun i j => ?_
      rw [jetActionMatrix, actionMatrix, JetGaugeAlgebra.ofConstant_toSU3Matrix,
        JetGaugeAlgebra.ofConstant_toU1Value, Matrix.map_apply, Matrix.smul_apply,
        Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply,
        Matrix.sub_apply, Matrix.smul_apply]
      by_cases hij : i = j
      · subst hij
        rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
        simp only [smul_eq_mul, mul_one]
        rw [hCsmul, ← map_sub, hCsmul]
      · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, smul_zero, smul_zero,
          sub_zero, sub_zero, hCsmul]
        exact congrArg C (by ring)
    have hcollapse : ∀ (m : Multiset (Fin 1 ⊕ Fin 3)),
        (((actionMatrix c).map (C : ℂ → JetRing)).map fun f =>
          constantCoeff (m.foldl (fun h ρ => pderiv ℂ ρ h) f))
        = if m = 0 then actionMatrix c else 0 := by
      intro m
      rcases eq_or_ne m 0 with rfl | hm
      · refine Matrix.ext fun i j => ?_
        simp [Matrix.map_apply, constantCoeff_C]
      · refine Matrix.ext fun i j => ?_
        simp [Matrix.map_apply, JetRing.foldl_pderiv_C_of_ne_zero hm, hm]
    have hMact : ((downMatrix U).map fun f =>
          constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f)) * actionMatrix c
        = (x.antidiagonal.map fun p =>
            actionMatrix (IsGaugeField.adjointCoeff U p.1 c)
            * ((downMatrix U).map fun f =>
                constantCoeff (p.2.foldl (fun h ρ => pderiv ℂ ρ h) f))).sum := by
      have h1 : ((downMatrix U * jetActionMatrix (JetGaugeAlgebra.ofConstant c)).map
            fun f => constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f))
          = ((downMatrix U).map fun f =>
              constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f))
            * actionMatrix c := by
        rw [hconst, matrix_constantCoeff_foldl_pderiv_mul,
          Multiset.map_congr rfl (fun p hp => by rw [hcollapse p.2]),
          Multiset.sum_antidiagonal_eq_of_snd_ne_zero x
            (fun p => ((downMatrix U).map fun f =>
              constantCoeff (p.1.foldl (fun h ρ => pderiv ℂ ρ h) f)) *
                (if p.2 = 0 then actionMatrix c else 0))
            (fun p hp => by rw [if_neg hp, Matrix.mul_zero]),
          if_pos rfl]
      rw [← h1, downMatrix_mul_jetActionMatrix, matrix_constantCoeff_foldl_pderiv_mul]
      exact congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => by
        rw [jetActionMatrix_map_cc_foldl,
          show JetGaugeAlgebra.eval (JetGaugeAlgebra.iteratedDeriv p.1
              (JetGaugeAlgebra.adjointMap U (JetGaugeAlgebra.ofConstant c)))
            = IsGaugeField.adjointCoeff U p.1 c from rfl])
    rw [repCoeff_eq,
      show (colourEnd ((downMatrix U).map fun f =>
            constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f)))
          ∘ₗ gaugeAlgebraAction c
        = colourEnd (((downMatrix U).map fun f =>
            constantCoeff (x.foldl (fun h ρ => pderiv ℂ ρ h) f))
              * actionMatrix c) from by
        rw [colourEnd_mul]; rfl,
      hMact, colourEnd_multiset_sum, Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [Function.comp_apply, colourEnd_mul, repCoeff_eq]
    rfl

end InfinitesimalAction

end DownSinglet

end StandardModel
