/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.Jet
public import Physlib.Particles.StandardModel.GaugeBosons.BBoson
public import Mathlib.RingTheory.TensorProduct.Basic
public import Physlib.Relativity.Tensors.ComplexTensor.Basic
/-!
# Charged-lepton singlets

## i. Overview

The Standard Model charged-lepton singlet is a right-handed Weyl spinor in the `(1, 1)_{-6}`
representation. Here charges are normalized as `6Y`, so `-6` is the usual hypercharge
`Y = -1`.

`LeptonSinglet` is the target vector space of one charged-lepton singlet. Its only index is
the Lorentz index carried by the Weyl spinor.

The Lorentz and gauge actions are first defined separately. The gauge action is then computed
on an arbitrary spinor, used to identify its kernel, and descended to each supported global
form of the Standard Model gauge group.

## ii. Key results

- `LeptonSinglet` : the target space of the `(1, 1)_{-6}` multiplet.
- `repLorentzGroup` : the right-handed Lorentz action.
- `repGaugeGroupI` : the action of the unquotiented gauge group.
- `repGaugeGroupI_apply` : the gauge action on a spinor.
- `mem_repGaugeGroupI_ker_iff_eq` : the kernel of the full-group action.
- `gaugeGroup_subgroup_ℤ₆_le_ker_repGaugeGroupI` : triviality of the central `ℤ₆`.
- `repGaugeGroup` : the action descended to every supported gauge-group quotient.

## iii. Table of contents

- A. The charged-lepton-singlet space
- B. Linear structure
- C. Lorentz action
- D. Gauge action
- E. Kernel of the gauge action
- F. Descent to quotient gauge groups
- G. Jet gauge action

-/

@[expose] public section

namespace StandardModel

/-!

## A. The charged-lepton-singlet space

The Weyl spinor carries the right-handed Lorentz index, and it is the whole of the multiplet:
a charged-lepton singlet has no colour index and no weak-isospin index.
-/

/-- The target vector space of one Standard Model charged-lepton singlet.
  It carries the `(1, 1)_{-6}` representation of the gauge group. -/
@[ext]
structure LeptonSinglet where
  /-- The right-handed Weyl spinor. -/
  val : Fermion.RightHandedWeyl

namespace LeptonSinglet

/-!

## B. Linear structure

The wrapper distinguishes charged-lepton singlets from other isomorphic vector spaces.
The following equivalences transfer the linear structure of the Weyl-spinor space and expose
that model when defining representations.
-/

/-- Identifies a charged-lepton singlet with its underlying Weyl spinor. -/
def valEquiv : LeptonSinglet ≃ Fermion.RightHandedWeyl where
  toFun := val
  invFun := fun m => ⟨m⟩

instance : AddCommGroup LeptonSinglet := Equiv.addCommGroup valEquiv

instance : Module ℂ LeptonSinglet := Equiv.module ℂ valEquiv

/-- The linear identification with the underlying Weyl-spinor space. -/
def valLinEquiv : LeptonSinglet ≃ₗ[ℂ] Fermion.RightHandedWeyl where
  toFun := val
  invFun := fun m => ⟨m⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp]
lemma valLinEquiv_apply (l : LeptonSinglet) : valLinEquiv l = l.val := rfl

lemma valLinEquiv_symm_apply (m : Fermion.RightHandedWeyl) :
    valLinEquiv.symm m = ⟨m⟩ := rfl

@[simp]
lemma val_add (l₁ l₂ : LeptonSinglet) : (l₁ + l₂).val = l₁.val + l₂.val := rfl

@[simp]
lemma val_smul (r : ℂ) (l : LeptonSinglet) : (r • l).val = r • l.val := rfl

/-!

## The basis of the charged-lepton-singlet space

-/

/-- A basis on the charged-lepton singlets. -/
noncomputable def basis : Module.Basis (Fin 2) ℂ LeptonSinglet :=
  Fermion.RightHandedWeyl.basis.map valLinEquiv.symm

/-!

## C. Lorentz action

The Lorentz group acts through the right-handed Weyl representation, transported along the
identification of a charged-lepton singlet with its spinor.
-/

open Matrix MatrixGroups

/-- The right-handed Lorentz representation on charged-lepton singlets. -/
noncomputable def repLorentzGroup : Representation ℂ (SL(2,ℂ)) LeptonSinglet where
  toFun Λ := valLinEquiv.symm ∘ₗ Fermion.RightHandedWeyl.rep Λ ∘ₗ valLinEquiv
  map_one' := by
    ext l
    simp [Module.End.one_eq_id]
  map_mul' Λ₁ Λ₂ := by
    ext1 l
    simp [Module.End.mul_eq_comp]

/-!

## D. Gauge action

The colour and weak factors act trivially, so the gauge group acts only through hypercharge.
The `U(1)` action is `star z ^ 6`; since `z` is unitary, `star z = z⁻¹`, so this represents
charge `-6`.

The formulas below expose the scalar used to compare actions and compute the kernel.
-/

/-- The `(1, 1)_{-6}` action of the unquotiented Standard Model gauge group. -/
noncomputable def repGaugeGroupI : Representation ℂ GaugeGroupI LeptonSinglet where
  toFun g := valLinEquiv.symm ∘ₗ
      LinearMap.lsmul ℂ Fermion.RightHandedWeyl (star g.toU1.1 ^ 6 : ℂ)
      ∘ₗ valLinEquiv
  map_one' := by
    ext l
    simp [valLinEquiv_symm_apply]
  map_mul' g₁ g₂ := by
    ext l
    simp [smul_smul, mul_comm, valLinEquiv_symm_apply]
    ring_nf

/-- The gauge group acts on a charged-lepton singlet by the hypercharge scalar alone. -/
lemma repGaugeGroupI_apply (g : GaugeGroupI) (ψ : Fermion.RightHandedWeyl) :
    repGaugeGroupI g ⟨ψ⟩ = ⟨(star g.toU1.1 ^ 6) • ψ⟩ := rfl

open Fermion in
/-- The gauge action is diagonal in the standard Weyl basis. -/
lemma repGaugeGroupI_basis (g : GaugeGroupI) (k : Fin 2) :
    repGaugeGroupI g ⟨RightHandedWeyl.basis k⟩ =
      (star g.toU1.1 ^ 6) • (⟨RightHandedWeyl.basis k⟩ : LeptonSinglet) := rfl

open Fermion in
/-- Two gauge elements induce the same action exactly when their hypercharge scalars agree. -/
lemma repGaugeGroupI_eq_iff {g₁ g₂ : GaugeGroupI} :
    repGaugeGroupI g₁ = repGaugeGroupI g₂ ↔
      star g₁.toU1.1 ^ 6 = star g₂.toU1.1 ^ 6 := by
  constructor
  · intro h
    have h' := congrFun (congrArg (fun f => f.1) h)
      (⟨RightHandedWeyl.basis 0⟩ : LeptonSinglet)
    simp only [LinearMap.coe_toAddHom, repGaugeGroupI_apply] at h'
    have h'' := congrArg (fun v => RightHandedWeyl.basis.repr (LeptonSinglet.val v) 0) h'
    simpa using h''
  · intro h
    have h' : (starRingEnd ℂ) g₁.toU1.1 ^ 6 = (starRingEnd ℂ) g₂.toU1.1 ^ 6 := h
    ext l
    simp [repGaugeGroupI, h']

/-!

## E. Kernel of the gauge action

An element acts trivially exactly when its hypercharge scalar is one. Its colour and weak
components are unrestricted, since neither appears in the action.
-/

/-- Characterizes the full-group elements acting trivially on the charged-lepton singlet. -/
lemma mem_repGaugeGroupI_ker_iff_eq {g : GaugeGroupI} :
    g ∈ repGaugeGroupI.ker ↔ star g.toU1.1 ^ 6 = 1 := by
  rw [MonoidHom.mem_ker, ← MonoidHom.map_one repGaugeGroupI, repGaugeGroupI_eq_iff]
  simp

/-!

## F. Descent to quotient gauge groups

A representation descends through a quotient when the quotient subgroup lies in its kernel.
The `U(1)` component of a central element is a sixth root of unity, so conjugating and raising
to the sixth power gives one, and charge `-6` therefore acts trivially.
-/

/-- The central `ℤ₆` subgroup acts trivially on `(1, 1)_{-6}`. -/
lemma gaugeGroup_subgroup_ℤ₆_le_ker_repGaugeGroupI :
    GaugeGroupQuot.subgroup .ℤ₆ ≤ repGaugeGroupI.ker := by
  simp only [GaugeGroupQuot.subgroup, gaugeGroupℤ₆SubGroup, SetLike.le_def,
    MonoidHom.mem_range, gaugeGroupℤ₆Hom_apply, Subtype.exists,
    mem_repGaugeGroupI_ker_iff_eq, forall_exists_index]
  rintro g x hx ⟨rfl⟩
  simp only [gaugeGroupℤ₆OfRoot_toU1, gaugeGroupℤ₆UnitaryOfRoot_coe]
  have hx6 : (((x : ℂˣ) : ℂ)) ^ 6 = 1 := (mem_rootsOfUnity' 6 x).mp hx
  simpa [map_pow] using congrArg (starRingEnd ℂ) hx6

/-- Every supported quotient subgroup acts trivially on the charged-lepton singlet. -/
lemma gaugeGroup_subgroup_le_ker_repGaugeGroupI (Q : GaugeGroupQuot) :
    Q.subgroup ≤ repGaugeGroupI.ker := Q.subgroup_le_subgroup_ℤ₆.trans
  gaugeGroup_subgroup_ℤ₆_le_ker_repGaugeGroupI

/-- The `(1, 1)_{-6}` representation for every supported global form of the
  Standard Model gauge group. -/
noncomputable def repGaugeGroup : (Q : GaugeGroupQuot) →
    Representation ℂ (GaugeGroup Q) LeptonSinglet
  | .I => repGaugeGroupI
  | .ℤ₆ => QuotientGroup.lift _ repGaugeGroupI (gaugeGroup_subgroup_le_ker_repGaugeGroupI .ℤ₆)
  | .ℤ₂ => QuotientGroup.lift _ repGaugeGroupI (gaugeGroup_subgroup_le_ker_repGaugeGroupI .ℤ₂)
  | .ℤ₃ => QuotientGroup.lift _ repGaugeGroupI (gaugeGroup_subgroup_le_ker_repGaugeGroupI .ℤ₃)

/-!

## G. Jet gauge action

The hypercharge character extends verbatim to jets: the jet ring carries a star
operation and powers, so `star u ^ 6` makes sense for the `U(1)` power-series
component `u` of a jet of gauge transformations.

A jet acts on the polynomial jet space
`SymmetricAlgebra ℂ Lorentz.CoℂModule ⊗[ℂ] LeptonSinglet` — the commuting
derivative symbols of the field tensored with its target space — through the
derivative action `derivAction` of its hypercharge power series on the symbols:
the value of the jet multiplies each symbol, while its derivative coordinates
lower derivative symbols by the Leibniz rule, e.g.
`∂_μ ψ ↦ χ(0) ∂_μ ψ + (∂_μ χ)(0) ψ` with `χ = star u ^ 6`. On jets of constant
gauge transformations the action reduces to the global gauge action, trivial on
the derivative symbols.

-/

open TensorProduct

/-- The `(1, 1)_{-6}` action of the jet gauge group on the polynomial jet space of
  the charged-lepton singlet: a jet of gauge transformations acts through the
  derivative action of its hypercharge power series `star u ^ 6` on the derivative
  symbols. Its value multiplies each symbol, and its derivative coordinates act by
  the Leibniz rule. -/
noncomputable def repJetGaugeGroupI :
    Representation ℂ JetGaugeGroupI
      (SymmetricAlgebra ℂ Lorentz.CoℂModule ⊗[ℂ] LeptonSinglet) where
  toFun U := TensorProduct.map (derivAction ((star (U.2.2 : JetRing)) ^ 6)) LinearMap.id
  map_one' := by
    rw [show ((star (((1 : JetGaugeGroupI).2.2 : unitary JetRing) : JetRing)) ^ 6) =
        (1 : JetRing) by simp, derivAction_one, TensorProduct.map_id]
    rfl
  map_mul' U₁ U₂ := by
    rw [show ((star (((U₁ * U₂ : JetGaugeGroupI).2.2 : unitary JetRing) : JetRing)) ^ 6) =
        ((star ((U₁.2.2 : unitary JetRing) : JetRing)) ^ 6) *
          ((star ((U₂.2.2 : unitary JetRing) : JetRing)) ^ 6) by
      rw [show (((U₁ * U₂ : JetGaugeGroupI).2.2 : unitary JetRing) : JetRing) =
          ((U₁.2.2 : unitary JetRing) : JetRing) * ((U₂.2.2 : unitary JetRing) : JetRing)
          from rfl, star_mul', mul_pow],
      derivAction_mul, Module.End.mul_eq_comp, ← TensorProduct.map_comp, LinearMap.id_comp]

@[simp]
lemma repJetGaugeGroupI_apply (U : JetGaugeGroupI)
    (x : SymmetricAlgebra ℂ Lorentz.CoℂModule ⊗[ℂ] LeptonSinglet) :
    repJetGaugeGroupI U x =
      TensorProduct.map (derivAction ((star (U.2.2 : JetRing)) ^ 6)) LinearMap.id x := rfl

/-- The jet action on the zeroth-order (field) symbol: the value of the jet acts by
  its hypercharge scalar, with no derivative contributions. -/
lemma repJetGaugeGroupI_one_tmul (U : JetGaugeGroupI) (l : LeptonSinglet) :
    repJetGaugeGroupI U ((1 : SymmetricAlgebra ℂ Lorentz.CoℂModule) ⊗ₜ[ℂ] l) =
      MvPowerSeries.constantCoeff ((star (U.2.2 : JetRing)) ^ 6) •
        ((1 : SymmetricAlgebra ℂ Lorentz.CoℂModule) ⊗ₜ[ℂ] l) := by
  rw [repJetGaugeGroupI_apply, TensorProduct.map_tmul, derivAction_apply_one,
    TensorProduct.smul_tmul']
  rfl

/-- The jet action on a first-order derivative symbol is the Leibniz rule:
  `∂_μ ψ ↦ χ(0) • ∂_μ ψ + (∂_μ χ)(0) • ψ`, where `χ = star u ^ 6` is the
  hypercharge power series of the jet. The value of the gauge transformation
  multiplies the first-derivative symbol, and its first derivative feeds the field
  symbol: this is `∂_μ(g ψ) = g ∂_μ ψ + (∂_μ g) ψ` for the `(1, 1)_{-6}`
  character. -/
lemma repJetGaugeGroupI_ι_tmul (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3)
    (l : LeptonSinglet) :
    repJetGaugeGroupI U (SymmetricAlgebra.ι ℂ Lorentz.CoℂModule (Lorentz.complexCoBasis μ) ⊗ₜ[ℂ] l) =
      MvPowerSeries.constantCoeff ((star (U.2.2 : JetRing)) ^ 6) •
        (SymmetricAlgebra.ι ℂ Lorentz.CoℂModule (Lorentz.complexCoBasis μ) ⊗ₜ[ℂ] l) +
        MvPowerSeries.coeff (Finsupp.single μ 1) ((star (U.2.2 : JetRing)) ^ 6) •
          ((1 : SymmetricAlgebra ℂ Lorentz.CoℂModule) ⊗ₜ[ℂ] l) := by
  rw [repJetGaugeGroupI_apply, TensorProduct.map_tmul, derivAction_apply_ι,
    TensorProduct.add_tmul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
  rfl

/-- The first-order Leibniz rule expressed through the B-boson Maurer–Cartan
  coefficient: the inhomogeneous term of the charged-lepton-singlet jet is the
  hypercharge `6` times the abelian connection shift `i (∂_μ u)(0) ū(0)` of the
  `U(1)` jet, times the value of the character. This is the structure of the
  covariant derivative: the derivative coordinates of a charged field transform
  through the same Maurer–Cartan term that shifts the B boson. -/
lemma repJetGaugeGroupI_ι_tmul_mcCoeff (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3)
    (l : LeptonSinglet) :
    repJetGaugeGroupI U
        (SymmetricAlgebra.ι ℂ Lorentz.CoℂModule (Lorentz.complexCoBasis μ) ⊗ₜ[ℂ] l) =
      MvPowerSeries.constantCoeff ((star (U.2.2 : JetRing)) ^ 6) •
        (SymmetricAlgebra.ι ℂ Lorentz.CoℂModule (Lorentz.complexCoBasis μ) ⊗ₜ[ℂ] l) +
        ((6 : ℂ) * Complex.I * (BBoson.mcCoeff U.2.2 μ : ℂ) *
          MvPowerSeries.constantCoeff ((star (U.2.2 : JetRing)) ^ 6)) •
          ((1 : SymmetricAlgebra ℂ Lorentz.CoℂModule) ⊗ₜ[ℂ] l) := by
  rw [repJetGaugeGroupI_ι_tmul, BBoson.coeff_single_star_pow]
  norm_num

/-- On jets of constant gauge transformations the jet action reduces to the global
  gauge action on the jet space: the `(1, 1)_{-6}` scalar on the target factor and
  the trivial action on the derivative symbols. -/
lemma repJetGaugeGroupI_ofConstant (g : GaugeGroupI) :
    repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) =
      TensorProduct.map LinearMap.id (repGaugeGroupI g) := by
  have hχ : ((star (((JetGaugeGroupI.ofConstant g).2.2 : unitary JetRing) : JetRing)) ^ 6) =
      MvPowerSeries.C ((star (g.2.2 : ℂ)) ^ 6) := by
    rw [show (((JetGaugeGroupI.ofConstant g).2.2 : unitary JetRing) : JetRing) =
        MvPowerSeries.C ((g.2.2 : ℂ)) from rfl, MvPowerSeries.star_C, ← map_pow]
  show TensorProduct.map (derivAction _) LinearMap.id = _
  rw [hχ, derivAction_C]
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p l =>
      simp only [TensorProduct.map_tmul, LinearMap.smul_apply, LinearMap.id_apply]
      rw [show repGaugeGroupI g l = ((star (g.2.2 : ℂ)) ^ 6) • l from rfl,
        TensorProduct.smul_tmul]
  | add x y hx hy => simp only [map_add]; rw [hx, hy]

end LeptonSinglet

end StandardModel
