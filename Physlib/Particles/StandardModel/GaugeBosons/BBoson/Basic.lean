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
public import Physlib.Mathematics.MvPolynomialTranslation
public import Mathlib.Algebra.MvPolynomial.Derivation
public import Physlib.Particles.StandardModel.GaugeGroup.MaurerCartan
/-!
# The B boson

The hypercharge gauge boson field `B_μ`: the gauge boson of the `U(1)` factor of
the Standard Model gauge group, with one Lorentz index, valued in the
one-dimensional adjoint of `U(1)`, modelled as the real vector space of hermitian
complex numbers.

The physical Z boson and photon are the electroweak-mixed combinations of this
field with the neutral `SU(2)` boson; before mixing, the `U(1)` factor's gauge
boson is the B boson formalized here.

## A note on the general case

Let us consider the general case of a gauge field which should help elcuidate the
theory here. Let `A_μ^a` be the gauge boson field for the general gauge group `G`,
with `a` an index in the adjoint representation of `G`. Then the gauge transformation on `A`
takes the form `A_μ^a ↦ (Ad_g A_μ)^a + mc(g)_μ^a`, where `mc(g)` is the Maurer–Cartan form
of the gauge transformation. In this file `BBoson` is the
vector space of the `B` boson fields, and the transformation of the
`B` boson is given by (`SMul JetGaugeGroupI BBoson`):

`repGaugeGroupI U.eval B + ⟨∑ μ, Lorentz.CoVector.basis μ ⊗ₜ[ℝ] maurerCartanU1Coeff U μ 0⟩`

where here `repGaugeGroupI U.eval` is the adjoint action and the second term is
the Maurer–Cartan term.

In general we will write `g • A_μ^a = M(g)^a_b A_μ^b + mc(g)_μ^a`, where `M(g)^a_b`
is the adjoint action of `g` evaluated at the base point.  With this it is easy to say
how the gauge transformation acts on the derivatives of the gauge field.  We have

`∂_s A_μ^a ↦ ∂_s (g • A_μ^a) =`
`∑ (x + y = s), C(x,y) (∂_x g₀^a_b) ∂_y A_μ^b + ∂_s mc(g)_μ^a`
where `C(x,y)` is the usual binomial coefficient.

What we actually want to work with (and what our Lagrangian is written in
terms of is) `[∂_s A_μ^a]`. These are the component functions of the gauge fields.
They are functions on the space of field configurations, so the induced left
action is the pullback along `g⁻¹`, `(g • f)(A) = f (g⁻¹ • A)`: one substitutes
`g⁻¹` — not `g` — into the field law above. Writing `M⁻¹ := M(g⁻¹) = M(g)⁻¹`,

`g • [∂_s A_μ^a] = ∑ (x + y = s), C(x,y) (∂_x (M(g₀⁻¹))^a_b) [∂_y A_μ^b]`
`  + ∂_s mc(g⁻¹)_μ^a`

The inverse on `M` is essential: pulling back along `g` instead would give a
right action, since `(f ∘ g₁) ∘ g₂ = f ∘ (g₁g₂)` composes in the wrong order.
The Maurer–Cartan cocycle identity `mc(g₁g₂) = Ad_{g₁} mc(g₂) + mc(g₁)` gives
`mc(g⁻¹) = -Ad_{g⁻¹} mc(g)`, so the inhomogeneous term is minus the field-level
one, transported by `M⁻¹`.

For the abelian case formalized here the adjoint action is trivial, `M ≡ 1`, so
the first sum collapses to `[∂_s B_μ]` and the shift is simply `-∂_s mc(g)_μ`:

`g • [∂_s B_μ] = [∂_s B_μ] - ∂_s mc(g)_μ`

This is `mcShift`, and it is the sign used by `repJetGaugeGroupI`.

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
  val : Lorentz.CoVector ⊗[ℝ] selfAdjoint ℂ

namespace BBoson
open Module
/-!

## B. Linear structure
-/

def valEquiv : BBoson ≃ Lorentz.CoVector ⊗[ℝ] selfAdjoint ℂ where
  toFun := val
  invFun := fun m => ⟨m⟩

noncomputable instance : AddCommGroup BBoson := Equiv.addCommGroup valEquiv

noncomputable instance : Module ℝ BBoson := Equiv.module ℝ valEquiv

/-- The linear identification with the underlying tensor product. -/
def valLinEquiv : BBoson ≃ₗ[ℝ] Lorentz.CoVector ⊗[ℝ] selfAdjoint ℂ where
  toFun := val
  invFun := fun m => ⟨m⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp]
lemma valLinEquiv_apply (d : BBoson) : valLinEquiv d = d.val := rfl

lemma valLinEquiv_symm_apply (m : Lorentz.CoVector ⊗[ℝ] selfAdjoint ℂ) :
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
  ((Lorentz.CoVector.basis.tensorProduct
      ((Module.Basis.singleton Unit ℝ).map Complex.selfAdjointEquiv.symm)).map
    valLinEquiv.symm).reindex (Equiv.prodPUnit (Fin 1 ⊕ Fin 3))

/-- The B-boson basis vector as an explicit tensor: the Lorentz basis vector paired
  with the hermitian unit. -/
lemma basis_apply (ν : Fin 1 ⊕ Fin 3) :
    (basis ν : BBoson) =
      ⟨Lorentz.CoVector.basis ν ⊗ₜ[ℝ] Complex.selfAdjointEquiv.symm 1⟩ := by
  rw [basis, Module.Basis.reindex_apply, Module.Basis.map_apply,
    Module.Basis.tensorProduct_apply', Module.Basis.map_apply,
    Module.Basis.singleton_apply, valLinEquiv_symm_apply]
  rfl

/-- A pure tensor of a Lorentz basis vector with a hermitian value is a multiple of
  the corresponding B-boson basis vector. -/
lemma mk_tmul_eq_smul_basis (ν : Fin 1 ⊕ Fin 3) (x : selfAdjoint ℂ) :
    (⟨Lorentz.CoVector.basis ν ⊗ₜ[ℝ] x⟩ : BBoson) =
      Complex.selfAdjointEquiv x • basis ν := by
  apply BBoson.ext
  rw [val_smul, basis_apply,
    show ((⟨Lorentz.CoVector.basis ν ⊗ₜ[ℝ] Complex.selfAdjointEquiv.symm 1⟩ : BBoson)).val =
      Lorentz.CoVector.basis ν ⊗ₜ[ℝ] Complex.selfAdjointEquiv.symm 1 from rfl,
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
    TensorProduct.map (Lorentz.CoVector.rep (Lorentz.SL2C.toLorentzGroup Λ))
      (Representation.trivial ℝ (SL(2,ℂ)) (selfAdjoint ℂ) Λ) ∘ₗ
    valLinEquiv.toLinearMap
  map_one' := by
    ext F
    simp [Module.End.one_eq_id]
  map_mul' Λ₁ Λ₂ := by
    ext1 F
    simp [TensorProduct.map_map, Module.End.mul_eq_comp, map_mul]


/-- The Lorentz action on the B-boson basis: the covector transformation. -/
lemma repLorentzGroup_basis (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) :
    repLorentzGroup Λ (basis μ) =
      ∑ j, (Lorentz.SL2C.toLorentzGroup Λ).1⁻¹ μ j • basis j := by
  have happ : repLorentzGroup Λ (basis μ) = valLinEquiv.symm.toLinearMap
      (TensorProduct.map (Lorentz.CoVector.rep (Lorentz.SL2C.toLorentzGroup Λ))
        (Representation.trivial ℝ (SL(2,ℂ)) (selfAdjoint ℂ) Λ)
        (valLinEquiv.toLinearMap (basis μ))) := rfl
  rw [happ, show valLinEquiv.toLinearMap (basis μ) =
      Lorentz.CoVector.basis μ ⊗ₜ[ℝ] Complex.selfAdjointEquiv.symm 1 from by
      rw [basis_apply]; rfl,
    TensorProduct.map_tmul, Lorentz.CoVector.rep_apply_basis,
    Representation.trivial_apply, TensorProduct.sum_tmul, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← TensorProduct.smul_tmul', map_smul]
  congr 1
  rw [show valLinEquiv.symm.toLinearMap (Lorentz.CoVector.basis j ⊗ₜ[ℝ]
      Complex.selfAdjointEquiv.symm 1) = (⟨Lorentz.CoVector.basis j ⊗ₜ[ℝ]
      Complex.selfAdjointEquiv.symm 1⟩ : BBoson) from rfl, ← basis_apply]

/-- The jet coordinates of the B boson transform contravariantly on the target
  index, by the columns of the Lorentz matrix, matching the derivative slots. -/
lemma repLorentzGroup_dual_dualBasis (Λ : SL(2,ℂ)) (ν : Fin 1 ⊕ Fin 3) :
    repLorentzGroup.dual Λ (basis.dualBasis ν) =
      ∑ j, (Lorentz.SL2C.toLorentzGroup Λ).1 j ν • basis.dualBasis j := by
  refine Representation.dual_apply_dualBasis _ _ _ _
    (Matrix.of fun l j => (Lorentz.SL2C.toLorentzGroup Λ).1 j l) (fun j => ?_)
  rw [repLorentzGroup_basis, ← LorentzGroup.coe_inv, map_inv, inv_inv]
  rfl

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

open MvPowerSeries JetRing

/-- The action of the jet gauge group on the B-boson field: the adjoint action is
  trivial, so a jet of gauge transformations acts purely by the Maurer–Cartan
  translation `B_μ ↦ B_μ + i (∂_μ u)(0) ū(0)` of its `U(1)` component. The action
  is affine rather than linear, which is why it is a `MulAction` and not a
  `Representation`. -/
noncomputable instance : SMul JetGaugeGroupI BBoson where
  smul U B := repGaugeGroupI U.eval B +
    ⟨∑ μ, Lorentz.CoVector.basis μ ⊗ₜ[ℝ] maurerCartanU1Coeff U μ 0⟩

lemma smul_eq (U : JetGaugeGroupI) (B : BBoson) : U • B = B +
   ⟨∑ μ, Lorentz.CoVector.basis μ ⊗ₜ[ℝ] maurerCartanU1Coeff U μ 0⟩ := rfl

lemma smul_val (U : JetGaugeGroupI) (B : BBoson) :
    (U • B).val = B.val + ∑ μ, Lorentz.CoVector.basis μ ⊗ₜ[ℝ] maurerCartanU1Coeff U μ 0 := by
  rfl

/-- The jets of constant (global) gauge transformations act trivially on the B
  boson, in agreement with the trivial adjoint representation `repGaugeGroupI`: the
  Maurer–Cartan term vanishes on constant jets. -/
@[simp]
lemma ofConstant_smul (g : GaugeGroupI) (B : BBoson) :
    JetGaugeGroupI.ofConstant g • B = B := by
  ext
  simp [smul_val]

attribute [-simp] Fintype.sum_sum_type

noncomputable instance : MulAction JetGaugeGroupI BBoson where
  one_smul B := by
    simp [smul_eq, maurerCartanU1Coeff_one]
    rfl
  mul_smul U V B := by
    ext
    simp [smul_val, maurerCartanU1Coeff_mul, TensorProduct.tmul_add, Finset.sum_add_distrib]
    abel

/-!

## A. The Jet generators

-/

open Module
inductive JetGenerators where
  | dB (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3): JetGenerators
deriving DecidableEq

def JetGenerators.massWeight : JetGenerators → ℕ
  | JetGenerators.dB s _ => 2 * (1 + s.card)

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


namespace JetGenerators

/-- The total symmetrized multi-index of a jet generator: the derivative
  multi-index together with the Lorentz index of the field. The Maurer–Cartan
  shift of a component function depends only on its total multi-index. -/
def total : JetGenerators → Multiset (Fin 1 ⊕ Fin 3)
  | .dB s ν => s + {ν}

@[simp]
lemma total_dB (s : Multiset (Fin 1 ⊕ Fin 3)) (ν : Fin 1 ⊕ Fin 3) :
    total (dB s ν) = s + {ν} := rfl

lemma total_ne_zero (g : JetGenerators) : total g ≠ 0 := by
  cases g with
  | dB s ν => simp [total]

/-- A choice of element of a multiset, used to pick the canonical representative
  of each total multi-index. -/
noncomputable def pick (t : Multiset (Fin 1 ⊕ Fin 3)) : Fin 1 ⊕ Fin 3 :=
  if h : ∃ ν, ν ∈ t then h.choose else Sum.inl 0

lemma pick_mem {t : Multiset (Fin 1 ⊕ Fin 3)} (ht : t ≠ 0) : pick t ∈ t := by
  have h : ∃ ν, ν ∈ t := Multiset.exists_mem_of_ne_zero ht
  rw [pick, dif_pos h]
  exact h.choose_spec

/-- The canonical representative of a jet generator: the generator with the same
  total multi-index whose field index is the chosen element of the total. -/
noncomputable def canon (g : JetGenerators) : JetGenerators :=
  .dB ((total g).erase (pick (total g))) (pick (total g))

/-- The canonical representative has the same total multi-index. -/
@[simp]
lemma total_canon (g : JetGenerators) : total (canon g) = total g := by
  rw [canon]
  show ((total g).erase (pick (total g))) + {pick (total g)} = total g
  rw [add_comm, Multiset.singleton_add]
  exact Multiset.cons_erase (pick_mem (total_ne_zero g))

/-- Taking canonical representatives is idempotent. -/
@[simp]
lemma canon_canon (g : JetGenerators) : canon (canon g) = canon g := by
  rw [show canon (canon g) =
    JetGenerators.dB ((total (canon g)).erase (pick (total (canon g))))
      (pick (total (canon g))) from rfl, total_canon]
  rfl

/-- Two jet generators have the same canonical representative if and only if they
  have the same total multi-index. -/
lemma canon_eq_canon_iff (g g' : JetGenerators) :
    canon g = canon g' ↔ total g = total g' := by
  constructor
  · intro h
    rw [← total_canon g, ← total_canon g', h]
  · intro h
    rw [canon, canon, h]

/-- The jet generator with one further derivative in the direction `μ`. -/
def shift (μ : Fin 1 ⊕ Fin 3) : JetGenerators → JetGenerators
  | dB s ν => dB (s + {μ}) ν

@[simp]
lemma shift_dB (μ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3)) (ν : Fin 1 ⊕ Fin 3) :
    shift μ (dB s ν) = dB (s + {μ}) ν := rfl

/-- Appending derivative indices commutes: the indices form a multiset. -/
lemma shift_comm (μ ν : Fin 1 ⊕ Fin 3) (g : JetGenerators) :
    shift μ (shift ν g) = shift ν (shift μ g) := by
  cases g with
  | dB s ρ =>
    show dB (s + {ν} + {μ}) ρ = dB (s + {μ} + {ν}) ρ
    rw [add_right_comm]

/-- Appending a derivative index raises the mass weight by two: a derivative has
  mass dimension one. -/
@[simp]
lemma massWeight_shift (μ : Fin 1 ⊕ Fin 3) (g : JetGenerators) :
    (shift μ g).massWeight = g.massWeight + 2 := by
  cases g
  simp [shift, massWeight]
  omega

/-- The jet generator with further derivatives appended from a multiset. -/
def shiftMulti (t : Multiset (Fin 1 ⊕ Fin 3)) : JetGenerators → JetGenerators
  | dB s ν => dB (s + t) ν

@[simp]
lemma shiftMulti_dB (t s : Multiset (Fin 1 ⊕ Fin 3)) (ν : Fin 1 ⊕ Fin 3) :
    shiftMulti t (dB s ν) = dB (s + t) ν := rfl

lemma shiftMulti_singleton (ν : Fin 1 ⊕ Fin 3) (g : JetGenerators) :
    shiftMulti {ν} g = shift ν g := by
  cases g with
  | dB s ρ => rfl

lemma shiftMulti_shift (t : Multiset (Fin 1 ⊕ Fin 3)) (ν : Fin 1 ⊕ Fin 3)
    (g : JetGenerators) :
    shiftMulti t (shift ν g) = shiftMulti (t + {ν}) g := by
  cases g with
  | dB s ρ =>
    simp only [shift_dB, shiftMulti_dB]
    congr 1
    rw [add_comm t ({ν} : Multiset (Fin 1 ⊕ Fin 3)), ← add_assoc]

end JetGenerators

/-!

## A. The Jet component vector space

-/

abbrev JetComponentSpace :=
  SymmetricAlgebra ℝ (Module.Dual ℝ Lorentz.CoVector) ⊗[ℝ] Module.Dual ℝ BBoson

/-- The basis of the B-boson jet component space indexed by the jet generators
  `∂_s B_μ`: the multiset basis of the dual derivative symbols tensored with the
  dual of the B-boson basis. -/
noncomputable def JetComponentSpace.basis : Basis JetGenerators ℝ JetComponentSpace :=
  (LagrangianTheory.dualRealJetAlgebraBasis.tensorProduct
    BBoson.basis.dualBasis).reindex JetGenerators.equiv.symm


/-!

### A.1. The mass dimension on the component space

-/

/-- The mass-dimension scaling on the space of component functions of the
  B boson: the diagonal map multiplying each component function `∂_s B_μ` by
  `c ^ w`, where `w` is twice its mass dimension. -/
noncomputable def JetComponentSpace.massWeightScale (c : ℝ) :
    JetComponentSpace →ₗ[ℝ] JetComponentSpace :=
  JetComponentSpace.basis.constr ℝ fun j =>
    c ^ j.massWeight • JetComponentSpace.basis j

@[simp]
lemma JetComponentSpace.massWeightScale_basis (c : ℝ) (j : JetGenerators) :
    JetComponentSpace.massWeightScale c (JetComponentSpace.basis j) =
      c ^ j.massWeight • JetComponentSpace.basis j := by
  rw [JetComponentSpace.massWeightScale, Module.Basis.constr_basis]

/-!

### A.2. The action of the Lorentz group

-/
/-- The representation of the Lorentz group on the space of component functions
  of the B boson: the derivative symbols transform through the real dual covector
  action and the target factor through the dual of the B-boson representation. -/
noncomputable def JetComponentSpace.repLorentzGroup :
    Representation ℝ (SL(2,ℂ)) JetComponentSpace :=
  DerivAlgebraReal.repLorentzGroup.tprod BBoson.repLorentzGroup.dual


/-!

### A.1. The action of the gauge group on the jet component space

The jet gauge group does not act linearly on the B-boson fields.

For a general gauge theory (potentially non-abelian),

`∂_s B_μ ↦ ∂_s (g • B_μ) = ∂_s (Ad_g B_μ + mc(g)_μ) = ∂_s (Ad_g B_μ) + ∂_s mc(g)_μ`

The last term in this expression is a real number.

-/

open LagrangianTheory

/-- The Maurer–Cartan pairing `⟨mc, ∂_s B_ν⟩`: the component function evaluated
  against the B-boson whose components are the factorial-weighted Taylor
  coefficients — the `s`-th derivatives at the base point — of the Maurer–Cartan
  series. This is the shift of the *field* `∂_s B_ν` under the gauge action; the
  component functions shift by its negative, `mcShift`. -/
noncomputable def mcPairing (U : JetGaugeGroupI) : JetComponentSpace →ₗ[ℝ] ℝ :=
  TensorProduct.lift ((Module.Dual.eval ℝ BBoson).comp
  (Lorentz.CoVector.basis.dualBasis.symmetricAlgebra.constr ℝ fun m =>
    ⟨∑ ν, Lorentz.CoVector.basis ν ⊗ₜ[ℝ] ((∏ μ, Nat.factorial (m μ)) • maurerCartanU1Coeff U ν m)⟩))

/-- The multiset basis of the dual derivative symbols, as a basis vector of the
  symmetric algebra at the corresponding multi-index. -/
lemma dualRealJetAlgebraBasis_apply' (s : Multiset (Fin 1 ⊕ Fin 3)) :
    LagrangianTheory.dualRealJetAlgebraBasis s =
      Lorentz.CoVector.basis.dualBasis.symmetricAlgebra (Multiset.toFinsupp s) := by
  rw [LagrangianTheory.dualRealJetAlgebraBasis, Module.Basis.reindex_apply, Equiv.symm_symm]
  rfl

/-- The jet component basis vector at a generator, as a pure tensor. -/
lemma jetComponentSpace_basis_dB (s : Multiset (Fin 1 ⊕ Fin 3)) (ρ : Fin 1 ⊕ Fin 3) :
    JetComponentSpace.basis (.dB s ρ) =
      LagrangianTheory.dualRealJetAlgebraBasis s ⊗ₜ[ℝ] BBoson.basis.dualBasis ρ := by
  rw [JetComponentSpace.basis, Module.Basis.reindex_apply, Equiv.symm_symm]
  exact Module.Basis.tensorProduct_apply' _ _ _

/-- The Maurer–Cartan pairing on a pure tensor over a derivative-symbol basis
  vector: the component function evaluated on the B boson of factorial-weighted
  Taylor coefficients of the Maurer–Cartan series. -/
lemma mcPairing_tmul_basis (U : JetGaugeGroupI) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℝ BBoson) :
    mcPairing U (LagrangianTheory.dualRealJetAlgebraBasis s ⊗ₜ[ℝ] φ) =
      φ ⟨∑ ν, Lorentz.CoVector.basis ν ⊗ₜ[ℝ]
        ((∏ ρ, Nat.factorial ((Multiset.toFinsupp s) ρ)) •
          maurerCartanU1Coeff U ν (Multiset.toFinsupp s))⟩ := by
  rw [dualRealJetAlgebraBasis_apply', mcPairing]
  show φ ((Lorentz.CoVector.basis.dualBasis.symmetricAlgebra.constr ℝ _)
    (Lorentz.CoVector.basis.dualBasis.symmetricAlgebra (Multiset.toFinsupp s))) = _
  rw [Module.Basis.constr_basis]

/-- The Maurer–Cartan pairing on a general generator: the factorial-weighted
  Taylor coefficient of the Maurer–Cartan series. -/
lemma mcPairing_basis_dB' (U : JetGaugeGroupI) (s : Multiset (Fin 1 ⊕ Fin 3))
    (ν : Fin 1 ⊕ Fin 3) :
    mcPairing U (JetComponentSpace.basis (.dB s ν)) =
      (∏ ρ, Nat.factorial ((Multiset.toFinsupp s) ρ)) •
        Complex.selfAdjointEquiv (maurerCartanU1Coeff U ν (Multiset.toFinsupp s)) := by
  rw [jetComponentSpace_basis_dB, mcPairing_tmul_basis,
    show (⟨∑ ν', Lorentz.CoVector.basis ν' ⊗ₜ[ℝ]
        ((∏ ρ, Nat.factorial ((Multiset.toFinsupp s) ρ)) •
          maurerCartanU1Coeff U ν' (Multiset.toFinsupp s))⟩ : BBoson) =
      ∑ ν', ((∏ ρ, Nat.factorial ((Multiset.toFinsupp s) ρ)) •
        Complex.selfAdjointEquiv (maurerCartanU1Coeff U ν' (Multiset.toFinsupp s))) • basis ν' from by
      rw [show (⟨∑ ν', Lorentz.CoVector.basis ν' ⊗ₜ[ℝ]
          ((∏ ρ, Nat.factorial ((Multiset.toFinsupp s) ρ)) •
            maurerCartanU1Coeff U ν' (Multiset.toFinsupp s))⟩ : BBoson) =
        valLinEquiv.symm (∑ ν', Lorentz.CoVector.basis ν' ⊗ₜ[ℝ]
          ((∏ ρ, Nat.factorial ((Multiset.toFinsupp s) ρ)) •
            maurerCartanU1Coeff U ν' (Multiset.toFinsupp s))) from rfl, map_sum]
      refine Finset.sum_congr rfl fun ν' _ => ?_
      rw [valLinEquiv_symm_apply, mk_tmul_eq_smul_basis, map_nsmul],
    map_sum]
  simp only [map_smul, Module.Basis.dualBasis_apply_self, smul_eq_mul, mul_ite,
    mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ ν]
  simp

/-- The Maurer–Cartan pairing on first-order generators: the shift of the component
  function `∂_μ B_ν` is the first-order Taylor coefficient of the Maurer–Cartan
  series. -/
lemma mcPairing_basis_dB (U : JetGaugeGroupI) (μ ν : Fin 1 ⊕ Fin 3) :
    mcPairing U (JetComponentSpace.basis (.dB {μ} ν)) =
      Complex.selfAdjointEquiv (maurerCartanU1Coeff U ν (Finsupp.single μ 1)) := by
  rw [mcPairing_basis_dB', Multiset.toFinsupp_singleton,
    show (∏ ρ, Nat.factorial ((Finsupp.single μ 1) ρ)) = 1 from
      Finset.prod_eq_one fun ρ _ => by
        rcases eq_or_ne μ ρ with rfl | h
        · simp
        · rw [Finsupp.single_eq_of_ne h.symm]
          rfl,
    one_smul]

@[simp]
lemma mcPairing_one : mcPairing 1 = 0 := by
  refine JetComponentSpace.basis.ext fun g => ?_
  obtain ⟨s, ν⟩ := g
  simp [mcPairing_basis_dB']

/-- The Maurer–Cartan pairing is additive in the jet. -/
lemma mcPairing_mul (U V : JetGaugeGroupI) :
    mcPairing (U * V) = mcPairing U + mcPairing V := by
  refine JetComponentSpace.basis.ext fun g => ?_
  obtain ⟨s, ν⟩ := g
  simp [mcPairing_basis_dB', maurerCartanU1Coeff_mul, smul_add]

/-- The Maurer–Cartan pairing of a jet of constant gauge transformations
  vanishes. -/
lemma mcPairing_ofConstant (g : GaugeGroupI) :
    mcPairing (JetGaugeGroupI.ofConstant g) = 0 := by
  refine JetComponentSpace.basis.ext fun j => ?_
  obtain ⟨s, ν⟩ := j
  simp [mcPairing_basis_dB']

/-- The factorial weight of a multi-index augmented by one derivative: the
  multiplicity of the new index times the original weight. -/
lemma prod_factorial_add_single (m : (Fin 1 ⊕ Fin 3) →₀ ℕ) (κ : Fin 1 ⊕ Fin 3) :
    (∏ ρ : Fin 1 ⊕ Fin 3, Nat.factorial (((m + Finsupp.single κ 1) : (Fin 1 ⊕ Fin 3) →₀ ℕ) ρ)) =
      (m κ + 1) * ∏ ρ, Nat.factorial (m ρ) := by
  rw [show (∏ ρ : Fin 1 ⊕ Fin 3, Nat.factorial (((m + Finsupp.single κ 1) : (Fin 1 ⊕ Fin 3) →₀ ℕ) ρ)) =
      ∏ ρ, ((if ρ = κ then m κ + 1 else 1) * Nat.factorial (m ρ)) from
    Finset.prod_congr rfl fun ρ _ => by
      rcases eq_or_ne ρ κ with rfl | h
      · rw [Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ, if_pos rfl]
      · rw [Finsupp.add_apply, Finsupp.single_eq_of_ne h, add_zero, if_neg h, one_mul],
    Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ κ]
  simp

/-- Exchanging the field index with a derivative index leaves the Maurer–Cartan
  shift of the component functions unchanged: the shift is the jet of a gradient,
  whose Taylor coefficients depend only on the total multi-index. -/
lemma mcPairing_basis_dB_symm (U : JetGaugeGroupI) (s : Multiset (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) :
    mcPairing U (JetComponentSpace.basis (.dB (s + {μ}) ν)) =
      mcPairing U (JetComponentSpace.basis (.dB (s + {ν}) μ)) := by
  rw [mcPairing_basis_dB', mcPairing_basis_dB',
    show Multiset.toFinsupp (s + {μ}) = Multiset.toFinsupp s + Finsupp.single μ 1 from by
      rw [map_add, Multiset.toFinsupp_singleton],
    show Multiset.toFinsupp (s + {ν}) = Multiset.toFinsupp s + Finsupp.single ν 1 from by
      rw [map_add, Multiset.toFinsupp_singleton],
    prod_factorial_add_single, prod_factorial_add_single, mul_smul, mul_smul,
    smul_comm (Multiset.toFinsupp s μ + 1), smul_comm (Multiset.toFinsupp s ν + 1)]
  congr 1
  have h := congrArg Complex.selfAdjointEquiv
    (maurerCartanU1Coeff_succ_symm U μ ν (Multiset.toFinsupp s))
  rw [map_nsmul, map_nsmul] at h
  exact h

/-!

## Iterated derivatives of the Maurer–Cartan series

The covariance of the covariant derivatives of charged fields rests on the
higher Maurer–Cartan anomalies: the iterated formal derivatives of the
Maurer–Cartan series. Their constant coefficients are the Maurer–Cartan
pairings of the corresponding B-boson component functions.

-/

/-- The iterated formal derivatives of the Maurer–Cartan series along an ordered
  list of directions: `mc_{s,μ} = ∂_s mc_μ`. -/
noncomputable def maurerCartanU1Deriv (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) :
    List (Fin 1 ⊕ Fin 3) → JetRing
  | [] => maurerCartanU1 U μ
  | ν :: s => pderiv ℂ ν (maurerCartanU1Deriv U μ s)

@[simp]
lemma maurerCartanU1Deriv_nil (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) :
    maurerCartanU1Deriv U μ [] = maurerCartanU1 U μ := rfl

@[simp]
lemma maurerCartanU1Deriv_cons (U : JetGaugeGroupI) (μ ν : Fin 1 ⊕ Fin 3)
    (s : List (Fin 1 ⊕ Fin 3)) :
    maurerCartanU1Deriv U μ (ν :: s) = pderiv ℂ ν (maurerCartanU1Deriv U μ s) := rfl

/-- The factorial-weighted Taylor coefficients of the iterated derivatives of the
  Maurer–Cartan series: differentiating shifts the multi-index inside the
  factorial weight. -/
lemma factorial_coeff_maurerCartanU1Deriv (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3)
    (s : List (Fin 1 ⊕ Fin 3)) (m : (Fin 1 ⊕ Fin 3) →₀ ℕ) :
    ((∏ ρ, Nat.factorial (m ρ) : ℕ) : ℂ) * coeff m (maurerCartanU1Deriv U μ s) =
      ((∏ ρ, Nat.factorial (((m + Multiset.toFinsupp ↑s) :
          (Fin 1 ⊕ Fin 3) →₀ ℕ) ρ) : ℕ) : ℂ) *
        coeff (m + Multiset.toFinsupp ↑s) (maurerCartanU1 U μ) := by
  induction s generalizing m with
  | nil => simp
  | cons ν s ih =>
    rw [maurerCartanU1Deriv_cons, coeff_pderiv]
    have hT : Multiset.toFinsupp (↑(ν :: s) : Multiset (Fin 1 ⊕ Fin 3)) =
        Finsupp.single ν 1 + Multiset.toFinsupp (↑s : Multiset (Fin 1 ⊕ Fin 3)) := by
      rw [show (↑(ν :: s) : Multiset (Fin 1 ⊕ Fin 3)) = {ν} + ↑s from by
          rw [Multiset.singleton_add, Multiset.cons_coe],
        map_add, Multiset.toFinsupp_singleton]
    have hcast : ((∏ ρ, Nat.factorial (((m + Finsupp.single ν 1) :
          (Fin 1 ⊕ Fin 3) →₀ ℕ) ρ) : ℕ) : ℂ) =
        ((m ν + 1 : ℕ) : ℂ) * ((∏ ρ, Nat.factorial (m ρ) : ℕ) : ℂ) := by
      rw [← Nat.cast_mul, prod_factorial_add_single]
    rw [hT, show m + (Finsupp.single ν 1 + Multiset.toFinsupp (↑s : Multiset _)) =
        m + Finsupp.single ν 1 + Multiset.toFinsupp (↑s : Multiset _) from
        (add_assoc _ _ _).symm, ← ih (m + Finsupp.single ν 1), hcast]
    push_cast
    ring

/-- The constant coefficient of the iterated derivative of the Maurer–Cartan
  series is the Maurer–Cartan pairing of the corresponding B-boson component
  function. -/
lemma constantCoeff_maurerCartanU1Deriv (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3)
    (s : List (Fin 1 ⊕ Fin 3)) :
    MvPowerSeries.constantCoeff (maurerCartanU1Deriv U μ s) =
      ((mcPairing U (JetComponentSpace.basis (JetGenerators.dB ↑s μ)) : ℝ) : ℂ) := by
  have h := factorial_coeff_maurerCartanU1Deriv U μ s 0
  simp only [Finsupp.coe_zero, Pi.zero_apply, Nat.factorial_zero, Finset.prod_const_one,
    Nat.cast_one, one_mul, zero_add] at h
  rw [← coeff_zero_eq_constantCoeff_apply, h, mcPairing_basis_dB', nsmul_eq_mul]
  push_cast
  rw [Complex.coe_selfAdjointEquiv]
  rfl

/-!

### The Maurer–Cartan shift on component functions

The jet gauge group acts on the *fields* by the translation `B_μ ↦ B_μ + mc(g)_μ`
(`SMul JetGaugeGroupI BBoson`). The jet algebra is the algebra of polynomial
*functions* of the jet coordinates, on which the induced left action is the
pullback along `g⁻¹`:

`(g · f)(B) = f (g⁻¹ • B)`.

Component functions therefore shift contragrediently to the fields, by
`mc(g⁻¹) = -mc(g)` rather than by `+mc(g)`:

`g • [∂_s B_ν] = [∂_s B_ν] - ⟨mc(g), ∂_s B_ν⟩ · 1`.

Taking the pullback along `g` instead would give a right action; it is a
representation here only because the `U(1)` translations are abelian, and would
fail to be one for the `SU(2)` and `SU(3)` factors, whose Maurer–Cartan cocycle
satisfies `mc(g₁g₂) = Ad_{g₁} mc(g₂) + mc(g₁)`.

-/

/-- The Maurer–Cartan shift of the component functions: minus the Maurer–Cartan
  pairing, this being the pairing of the *inverse* jet, `⟨mc(U⁻¹), ·⟩`. This is
  the shift appearing in the contragredient gauge action `repJetGaugeGroupI`. -/
noncomputable def mcShift (U : JetGaugeGroupI) : JetComponentSpace →ₗ[ℝ] ℝ :=
  - mcPairing U

lemma mcShift_apply (U : JetGaugeGroupI) (x : JetComponentSpace) :
    mcShift U x = - mcPairing U x := rfl

/-- The Maurer–Cartan shift on a general generator: minus the factorial-weighted
  Taylor coefficient of the Maurer–Cartan series. -/
lemma mcShift_basis_dB' (U : JetGaugeGroupI) (s : Multiset (Fin 1 ⊕ Fin 3))
    (ν : Fin 1 ⊕ Fin 3) :
    mcShift U (JetComponentSpace.basis (.dB s ν)) =
      - ((∏ ρ, Nat.factorial ((Multiset.toFinsupp s) ρ)) •
        Complex.selfAdjointEquiv (maurerCartanU1Coeff U ν (Multiset.toFinsupp s))) := by
  rw [mcShift_apply, mcPairing_basis_dB']

/-- The Maurer–Cartan shift on first-order generators. -/
lemma mcShift_basis_dB (U : JetGaugeGroupI) (μ ν : Fin 1 ⊕ Fin 3) :
    mcShift U (JetComponentSpace.basis (.dB {μ} ν)) =
      - Complex.selfAdjointEquiv (maurerCartanU1Coeff U ν (Finsupp.single μ 1)) := by
  rw [mcShift_apply, mcPairing_basis_dB]

@[simp]
lemma mcShift_one : mcShift 1 = 0 := by
  rw [mcShift, mcPairing_one, neg_zero]

/-- The Maurer–Cartan shift is additive in the jet. -/
lemma mcShift_mul (U V : JetGaugeGroupI) :
    mcShift (U * V) = mcShift U + mcShift V := by
  rw [mcShift, mcShift, mcShift, mcPairing_mul, neg_add]

/-- The Maurer–Cartan shift of a jet of constant gauge transformations
  vanishes. -/
lemma mcShift_ofConstant (g : GaugeGroupI) :
    mcShift (JetGaugeGroupI.ofConstant g) = 0 := by
  rw [mcShift, mcPairing_ofConstant, neg_zero]

/-- The Maurer–Cartan shift inherits the symmetry of the first-order
  Maurer–Cartan coefficients: the shift of `∂_{s+μ} B_ν` equals that of
  `∂_{s+ν} B_μ`. This is the gauge invariance of the abelian field strength. -/
lemma mcShift_basis_dB_symm (U : JetGaugeGroupI) (s : Multiset (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) :
    mcShift U (JetComponentSpace.basis (.dB (s + {μ}) ν)) =
      mcShift U (JetComponentSpace.basis (.dB (s + {ν}) μ)) := by
  rw [mcShift_apply, mcShift_apply, mcPairing_basis_dB_symm]

/-- The constant coefficient of the iterated derivative of the Maurer–Cartan
  series is minus the Maurer–Cartan shift of the corresponding B-boson component
  function. -/
lemma constantCoeff_maurerCartanU1Deriv_mcShift (U : JetGaugeGroupI)
    (μ : Fin 1 ⊕ Fin 3) (s : List (Fin 1 ⊕ Fin 3)) :
    MvPowerSeries.constantCoeff (maurerCartanU1Deriv U μ s) =
      - ((mcShift U (JetComponentSpace.basis (JetGenerators.dB ↑s μ)) : ℝ) : ℂ) := by
  rw [constantCoeff_maurerCartanU1Deriv, mcShift_apply]
  push_cast
  ring

/-!

## The Maurer–Cartan jet series

The local gauge transformation of the B-boson field is the translation
`B_μ ↦ B_μ + i (∂_μ u) ū`, so a jet of gauge transformations shifts every
derivative coordinate `∂_s B_μ` of the field by the corresponding derivative
`∂_s (i ∂_μ u ū)(0)` of the Maurer–Cartan form at the base point. The zeroth
Taylor coefficient `maurerCartanU1Coeff U μ 0` records only the zeroth of these
shifts — enough for the action on the field itself, but not for the action on
its jets.

To express the shift of every derivative coordinate uniformly we use the `U(1)`
Maurer–Cartan form `maurerCartanU1` of the jet gauge group: the formal power
series `i (∂_ν u) ū`, whose Taylor coefficients `maurerCartanU1Coeff` are the
shifts at every order. Its coefficients are hermitian, and it is
additive in the jet; these two facts make the induced shift of the B-boson
component functions a real-valued cocycle, which is what turns the substitution
`B ↦ B + i (∂u) ū` into a representation of the jet gauge group on the jet
algebra below.

-/

/-- The derivative of a hypercharge power of a `U(1)` jet:
  `∂_ν (u^q) = -q i mc_ν u^q`, the all-orders form of the first-order Taylor
  coefficient formula for the contragredient character. -/
lemma pderiv_pow_unitary (U : JetGaugeGroupI) (ν : Fin 1 ⊕ Fin 3) (q : ℕ) :
    pderiv ℂ ν ((U.2.2 : JetRing) ^ q) =
      MvPowerSeries.C (-(q : ℂ) * Complex.I) * (maurerCartanU1 U ν * (U.2.2 : JetRing) ^ q) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · have h1 : star (U.2.2 : JetRing) * (U.2.2 : JetRing) = 1 := (Unitary.mem_iff.mp U.2.2.2).1
    have hpow : (U.2.2 : JetRing) ^ q = (U.2.2 : JetRing) * (U.2.2 : JetRing) ^ (q - 1) := by
      conv_lhs => rw [show q = 1 + (q - 1) by omega, pow_add, pow_one]
    have hC : (MvPowerSeries.C (-(q : ℂ) * Complex.I) : JetRing) *
        MvPowerSeries.C Complex.I = MvPowerSeries.C ((q : ℕ) : ℂ) := by
      rw [← map_mul]
      congr 1
      ring_nf
      rw [Complex.I_sq]
      ring
    have hN : (MvPowerSeries.C ((q : ℕ) : ℂ) : JetRing) = ((q : ℕ) : JetRing) :=
      map_natCast _ _
    rw [MvPowerSeries.pderiv_pow, maurerCartanU1, hpow]
    linear_combination
      (-((U.2.2 : JetRing) * (U.2.2 : JetRing) ^ (q - 1) * pderiv ℂ ν (U.2.2 : JetRing) *
        star (U.2.2 : JetRing))) * hC +
      (-((U.2.2 : JetRing) ^ (q - 1) * pderiv ℂ ν (U.2.2 : JetRing) *
        MvPowerSeries.C ((q : ℕ) : ℂ))) * h1 +
      (-((U.2.2 : JetRing) ^ (q - 1) * pderiv ℂ ν (U.2.2 : JetRing))) * hN

/-- The derivative of a hypercharge power of the conjugate `U(1)` jet:
  `∂_ν (ū^q) = q i mc_ν ū^q`, the conjugate-contragredient counterpart of
  `pderiv_pow_unitary`. -/
lemma pderiv_pow_unitary_star (U : JetGaugeGroupI) (ν : Fin 1 ⊕ Fin 3) (q : ℕ) :
    pderiv ℂ ν (star (U.2.2 : JetRing) ^ q) =
      MvPowerSeries.C ((q : ℂ) * Complex.I) *
        (maurerCartanU1 U ν * star (U.2.2 : JetRing) ^ q) := by
  have h := pderiv_pow_unitary U⁻¹ ν q
  have hcoe : ((U⁻¹.2.2 : unitary JetRing) : JetRing) =
      star ((U.2.2 : unitary JetRing) : JetRing) := by
    rw [show (U⁻¹.2.2 : unitary JetRing) = (U.2.2)⁻¹ from rfl, ← Unitary.star_eq_inv,
      Unitary.coe_star]
  rw [hcoe, maurerCartanU1_inv, neg_mul, map_neg] at h
  linear_combination h

/-!

## The jet algebra and the jet gauge action

-/

/-- The jet algebra of the B boson: the commutative algebra generated by the
  component functions of the B-boson field and its derivative coordinates. -/
abbrev JetAlgebra : Type := SymmetricAlgebra ℝ JetComponentSpace

namespace JetAlgebra


/-!

## Constructing elements of the jet algebra from the generators

-/

noncomputable def ofGenerator (x : JetGenerators) : BBoson.JetAlgebra :=
   SymmetricAlgebra.ι ℝ JetComponentSpace (BBoson.JetComponentSpace.basis x)

/-!

## A. Representation of the Lorentz group

-/


/-!

### A.1. The real Lorentz representation

-/


noncomputable def repLorentzGroup :
    Representation ℝ SL(2,ℂ) JetAlgebra where
  toFun Λ := (SymmetricAlgebra.lift
    (SymmetricAlgebra.ι ℝ _ ∘ₗ JetComponentSpace.repLorentzGroup Λ)).toLinearMap
  map_one' := by
    simp [End.one_eq_id]
  map_mul' Λ1 Λ2 := by
    suffices h : SymmetricAlgebra.lift
        (SymmetricAlgebra.ι ℝ _ ∘ₗ JetComponentSpace.repLorentzGroup (Λ1 * Λ2)) =
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι ℝ _ ∘ₗ JetComponentSpace.repLorentzGroup Λ1)).comp
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.ι ℝ _ ∘ₗ JetComponentSpace.repLorentzGroup Λ2)) by
      rw [h]; rfl
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
    simp [map_mul, Module.End.mul_apply]

lemma repLorentzGroup_apply (Λ : SL(2,ℂ)) (a : JetAlgebra) :
    repLorentzGroup Λ a =
      (SymmetricAlgebra.lift
        (SymmetricAlgebra.ι ℝ _ ∘ₗ JetComponentSpace.repLorentzGroup Λ)) a := rfl

lemma repLorentzGroup_apply_mul (Λ : SL(2,ℂ)) (a b : JetAlgebra) :
    repLorentzGroup Λ (a * b) = repLorentzGroup Λ a * repLorentzGroup Λ b := by
  simp [repLorentzGroup_apply]

lemma repLorentzGroup_apply_one (Λ : SL(2,ℂ)) :
    repLorentzGroup Λ (1 : JetAlgebra) = 1 := by
  simp [repLorentzGroup_apply]

/-- The Lorentz action on a jet-algebra generator. -/
@[simp]
lemma repLorentzGroup_apply_ι (Λ : SL(2,ℂ)) (x : JetComponentSpace) :
    repLorentzGroup Λ (SymmetricAlgebra.ι ℝ JetComponentSpace x) =
      SymmetricAlgebra.ι ℝ JetComponentSpace
        (JetComponentSpace.repLorentzGroup Λ x) := by
  simp [repLorentzGroup_apply]



/-- The multiset basis of the real dual derivative slots at the empty index. -/
lemma _root_.StandardModel.BBoson.dualRealJetAlgebraBasis_nil :
    LagrangianTheory.dualRealJetAlgebraBasis ({} : Multiset (Fin 1 ⊕ Fin 3)) = 1 := by
  have h : (MvPolynomial.basisMonomials (Fin 1 ⊕ Fin 3) ℝ)
      ((0 : (Fin 1 ⊕ Fin 3) →₀ ℕ)) = 1 := by
    rw [MvPolynomial.coe_basisMonomials]
    simp [MvPolynomial.monomial_zero']
  rw [LagrangianTheory.dualRealJetAlgebraBasis, Module.Basis.reindex_apply,
    Equiv.symm_symm,
    show Multiset.toFinsupp.toEquiv ({} : Multiset (Fin 1 ⊕ Fin 3)) = 0 by simp,
    Module.Basis.symmetricAlgebra, Module.Basis.map_apply, h]
  simp

/-- The multiset basis vectors of the real dual derivative slots multiply by
  adding the multisets. -/
lemma _root_.StandardModel.BBoson.dualRealJetAlgebraBasis_mul (s t : Multiset (Fin 1 ⊕ Fin 3)) :
    LagrangianTheory.dualRealJetAlgebraBasis s *
      LagrangianTheory.dualRealJetAlgebraBasis t =
      LagrangianTheory.dualRealJetAlgebraBasis (s + t) := by
  rw [dualRealJetAlgebraBasis_apply', dualRealJetAlgebraBasis_apply',
    dualRealJetAlgebraBasis_apply', map_add]
  simp only [Module.Basis.symmetricAlgebra, Module.Basis.map_apply,
    show ∀ p, (SymmetricAlgebra.equivMvPolynomial
        Lorentz.CoVector.basis.dualBasis).symm.toLinearEquiv p =
      (SymmetricAlgebra.equivMvPolynomial Lorentz.CoVector.basis.dualBasis).symm p
      from fun _ => rfl,
    ← map_mul, MvPolynomial.coe_basisMonomials]
  simp only [MvPolynomial.monomial_mul, mul_one]


/-- The Lorentz action on the zeroth-order B-boson generator of the B-boson
  jet algebra: the covector transformation. -/
lemma repLorentzGroup_ofGenerator_dB_nil (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3) :
    BBoson.JetAlgebra.repLorentzGroup Λ
      (BBoson.JetAlgebra.ofGenerator (BBoson.JetGenerators.dB {} μ)) =
      ∑ ν, (Lorentz.SL2C.toLorentzGroup Λ).1 ν μ •
        BBoson.JetAlgebra.ofGenerator (BBoson.JetGenerators.dB {} ν) := by
  rw [BBoson.JetAlgebra.ofGenerator, BBoson.JetAlgebra.repLorentzGroup_apply_ι,
    BBoson.jetComponentSpace_basis_dB,
    show BBoson.JetComponentSpace.repLorentzGroup Λ
        (LagrangianTheory.dualRealJetAlgebraBasis {} ⊗ₜ[ℝ]
          StandardModel.BBoson.basis.dualBasis μ) =
      (DerivAlgebraReal.repLorentzGroup Λ
        (LagrangianTheory.dualRealJetAlgebraBasis {})) ⊗ₜ[ℝ]
        (BBoson.repLorentzGroup.dual Λ (StandardModel.BBoson.basis.dualBasis μ))
      from rfl,
    BBoson.dualRealJetAlgebraBasis_nil,
    show DerivAlgebraReal.repLorentzGroup Λ (1 : DerivAlgebraReal) = 1 from
      map_one (SymmetricAlgebra.lift (SymmetricAlgebra.ι ℝ _ ∘ₗ
        Lorentz.CoVector.sl2Rep.dual Λ)),
    BBoson.repLorentzGroup_dual_dualBasis, TensorProduct.tmul_sum, map_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [TensorProduct.tmul_smul, map_smul, BBoson.JetAlgebra.ofGenerator,
    BBoson.jetComponentSpace_basis_dB, BBoson.dualRealJetAlgebraBasis_nil]

/-!

### A.2. The complexified Lorentz representation

-/

noncomputable def complexRepLorentzGroup : Representation ℂ SL(2,ℂ) (ℂ ⊗[ℝ] JetAlgebra) where
  toFun U := LinearMap.baseChange ℂ (BBoson.JetAlgebra.repLorentzGroup U)
  map_one' := by
    ext x
    simp [Module.End.one_eq_id]
  map_mul' U V := by
    ext x
    simp [map_mul, Module.End.mul_eq_comp, LinearMap.baseChange_comp]

/-- The complexified Lorentz action agrees with the algebra homomorphism
  obtained by tensoring the multiplicative lift defining the real action with
  the identity of `ℂ`. -/
lemma complexRepLorentzGroup_eq_algHom (Λ : SL(2,ℂ)) (x : ℂ ⊗[ℝ] JetAlgebra) :
    complexRepLorentzGroup Λ x =
      Algebra.TensorProduct.map (AlgHom.id ℂ ℂ)
        (SymmetricAlgebra.lift (SymmetricAlgebra.ι ℝ _ ∘ₗ
          JetComponentSpace.repLorentzGroup Λ)) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul c b => rfl

/-- The complexified B-boson Lorentz action fixes the unit. -/
lemma complexRepLorentzGroup_apply_one (Λ : SL(2,ℂ)) :
    complexRepLorentzGroup Λ (1 : ℂ ⊗[ℝ] BBoson.JetAlgebra) = 1 := by
  simp [complexRepLorentzGroup_eq_algHom]

lemma complexRepLorentzGroup_apply_mul (Λ : SL(2,ℂ)) (a b : ℂ ⊗[ℝ] BBoson.JetAlgebra) :
    complexRepLorentzGroup Λ (a * b) =
      complexRepLorentzGroup Λ a * complexRepLorentzGroup Λ b := by
  simp [complexRepLorentzGroup_eq_algHom]

noncomputable def complexRepLorentzGroupAlgHom (Λ : SL(2,ℂ)) :
    AlgHom ℂ (ℂ ⊗[ℝ] BBoson.JetAlgebra) (ℂ ⊗[ℝ] BBoson.JetAlgebra) where
  toFun := complexRepLorentzGroup Λ
  map_add' := LinearMap.map_add _
  map_zero' := LinearMap.map_zero _
  map_one' := complexRepLorentzGroup_apply_one Λ
  map_mul' := complexRepLorentzGroup_apply_mul Λ
  commutes' r := by simp [complexRepLorentzGroup_eq_algHom]


/-!

## A. Representation of the jet Gauge group

-/


/-!

## A.1 The real version

-/

/-- The action of the jet gauge group on the jet algebra of the B boson. The
  adjoint action is trivial and the local gauge action is the Maurer–Cartan
  translation, whose linear part is the identity; consequently no information is
  carried by a linear action on the component space itself, and the action lives
  on the unital algebra: a jet of gauge transformations acts as the substitution
  automorphism sending each generator `x` to `x + mcShift U x • 1`, i.e. to
  `x - ⟨mc, x⟩ 1`. This is the pullback along `U⁻¹` of the field translation
  `B ↦ B + i (∂u) ū`, the contragredient action, which is what makes this a left
  action rather than a right one. On jets of constant gauge transformations the
  shift vanishes and the action is trivial, in agreement with
  `repGaugeGroupI`. -/
noncomputable def repJetGaugeGroupI : Representation ℝ JetGaugeGroupI JetAlgebra where
  toFun U := (SymmetricAlgebra.lift
    ((SymmetricAlgebra.ι ℝ JetComponentSpace) +
      (Algebra.linearMap ℝ JetAlgebra) ∘ₗ mcShift U)).toLinearMap
  map_one' := by
    rw [show mcShift (1 : JetGaugeGroupI) = 0 from mcShift_one]
    suffices hs : SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℝ JetComponentSpace) +
        (Algebra.linearMap ℝ JetAlgebra) ∘ₗ (0 : JetComponentSpace →ₗ[ℝ] ℝ)) =
        AlgHom.id ℝ JetAlgebra by
      rw [hs]
      rfl
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
    simp
  map_mul' U V := by
    rw [show mcShift (U * V : JetGaugeGroupI) =
        mcShift U + mcShift V from mcShift_mul U V]
    suffices hs : SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℝ JetComponentSpace) +
        (Algebra.linearMap ℝ JetAlgebra) ∘ₗ (mcShift U + mcShift V)) =
        (SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℝ JetComponentSpace) +
          (Algebra.linearMap ℝ JetAlgebra) ∘ₗ mcShift U)).comp
        (SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℝ JetComponentSpace) +
          (Algebra.linearMap ℝ JetAlgebra) ∘ₗ mcShift V)) by
      rw [hs, AlgHom.comp_toLinearMap, Module.End.mul_eq_comp]
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
    simp [add_assoc]

/-- The jet gauge action on a generator of the jet algebra: the Maurer–Cartan
  shift by the pairing of the component function with the Maurer–Cartan jet. -/
@[simp]
lemma repJetGaugeGroupI_ι (U : JetGaugeGroupI) (x : JetComponentSpace) :
    repJetGaugeGroupI U (SymmetricAlgebra.ι ℝ JetComponentSpace x) =
      SymmetricAlgebra.ι ℝ JetComponentSpace x +
        algebraMap ℝ JetAlgebra (mcShift U x) := by
  simp [repJetGaugeGroupI, SymmetricAlgebra.lift_ι_apply, AlgHom.toLinearMap_apply,
    Algebra.linearMap_apply]


lemma repJetGaugeGroupI_mul (U : JetGaugeGroupI) (x y : JetAlgebra) :
    repJetGaugeGroupI U (x * y) = repJetGaugeGroupI U x * repJetGaugeGroupI U y :=
  map_mul (SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℝ JetComponentSpace) +
    (Algebra.linearMap ℝ JetAlgebra) ∘ₗ mcShift U)) x y

lemma repJetGaugeGroupI_algebraMap (U : JetGaugeGroupI) (r : ℝ) :
    repJetGaugeGroupI U (algebraMap ℝ JetAlgebra r) = algebraMap ℝ JetAlgebra r :=
  AlgHom.commutes (SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℝ JetComponentSpace) +
    (Algebra.linearMap ℝ JetAlgebra) ∘ₗ mcShift U)) r

lemma repJetGaugeGroupI_one (U : JetGaugeGroupI) :
    repJetGaugeGroupI U (1 : JetAlgebra) = 1 := by
  have h := repJetGaugeGroupI_algebraMap U 1
  simpa using h

/-- Conjugating the jet gauge action by the polynomial coordinates of the jet
  algebra: under `SymmetricAlgebra.equivMvPolynomial` the substitution
  automorphism `x ↦ x + ⟨mc, x⟩ 1` becomes the translation of every polynomial
  variable by the Maurer–Cartan pairing of the corresponding component
  function. -/
lemma equivMvPolynomial_repJetGaugeGroupI (U : JetGaugeGroupI) (V : JetAlgebra) :
    SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis (repJetGaugeGroupI U V) =
      MvPolynomial.aeval (fun g => MvPolynomial.X g +
          MvPolynomial.C (mcShift U (JetComponentSpace.basis g)))
        (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis V) := by
  have h : (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis).toAlgHom.comp
      (SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℝ JetComponentSpace) +
        (Algebra.linearMap ℝ JetAlgebra) ∘ₗ mcShift U)) =
      (MvPolynomial.aeval (fun g => MvPolynomial.X g +
          MvPolynomial.C (mcShift U (JetComponentSpace.basis g)))).comp
        (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis).toAlgHom := by
    refine SymmetricAlgebra.algHom_ext (JetComponentSpace.basis.ext fun g => ?_)
    show (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis)
        (SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℝ JetComponentSpace) +
          (Algebra.linearMap ℝ JetAlgebra) ∘ₗ mcShift U)
          (SymmetricAlgebra.ι ℝ JetComponentSpace (JetComponentSpace.basis g))) =
      MvPolynomial.aeval (fun g => MvPolynomial.X g +
          MvPolynomial.C (mcShift U (JetComponentSpace.basis g)))
        ((SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis)
          (SymmetricAlgebra.ι ℝ JetComponentSpace (JetComponentSpace.basis g)))
    rw [SymmetricAlgebra.lift_ι_apply]
    simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
      Algebra.linearMap_apply, map_add, AlgEquiv.commutes,
      SymmetricAlgebra.equivMvPolynomial_ι_apply, MvPolynomial.aeval_X,
      MvPolynomial.algebraMap_eq]
  exact DFunLike.congr_fun h V


/-- Jets of constant gauge transformations act trivially on the B-boson jet
  algebra: the Maurer–Cartan shift vanishes. -/
lemma repJetGaugeGroupI_ofConstant (g : GaugeGroupI) (x : JetAlgebra) :
    repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) x = x := by
  rw [show repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) x =
      (SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℝ JetComponentSpace) +
        (Algebra.linearMap ℝ JetAlgebra) ∘ₗ
          mcShift (JetGaugeGroupI.ofConstant g))) x from rfl,
    mcShift_ofConstant]
  have h2 : SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℝ JetComponentSpace) +
      (Algebra.linearMap ℝ JetAlgebra) ∘ₗ (0 : JetComponentSpace →ₗ[ℝ] ℝ)) =
      AlgHom.id ℝ JetAlgebra := by
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun v => ?_)
    simp
  rw [h2]
  rfl

noncomputable def repJetGaugeGroupIAlgHom (U : JetGaugeGroupI) :
    AlgHom ℝ JetAlgebra JetAlgebra where
  toFun := repJetGaugeGroupI U
  map_add' := LinearMap.map_add _
  map_zero' := LinearMap.map_zero _
  map_one' := repJetGaugeGroupI_one U
  map_mul' := repJetGaugeGroupI_mul U
  commutes' r := by simp [repJetGaugeGroupI_algebraMap]

lemma repJetGaugeGroupIAlgHom_apply (U : JetGaugeGroupI) (x : JetAlgebra) :
    repJetGaugeGroupIAlgHom U x = repJetGaugeGroupI U x := rfl

/-!

## A.2 The complexified version

-/


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

lemma complexRepJetGaugeGroupI_eq_algHom (U : JetGaugeGroupI)
    (x : ℂ ⊗[ℝ] JetAlgebra) :
    complexRepJetGaugeGroupI U x =
      Algebra.TensorProduct.map (AlgHom.id ℂ ℂ) (repJetGaugeGroupIAlgHom U) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul c b => rfl

lemma complexRepJetGaugeGroupI_tmul (U : JetGaugeGroupI) (c : ℂ) (b : JetAlgebra) :
    complexRepJetGaugeGroupI U (c ⊗ₜ[ℝ] b) = c ⊗ₜ[ℝ] repJetGaugeGroupI U b := rfl

/-- The complexified gauge action is multiplicative. -/
lemma complexRepJetGaugeGroupI_mul (U : JetGaugeGroupI) (x y : ℂ ⊗[ℝ] JetAlgebra) :
    complexRepJetGaugeGroupI U (x * y) =
      complexRepJetGaugeGroupI U x * complexRepJetGaugeGroupI U y := by
  simp [complexRepJetGaugeGroupI_eq_algHom]

lemma complexRepJetGaugeGroupI_one (U : JetGaugeGroupI) :
    complexRepJetGaugeGroupI U (1 : ℂ ⊗[ℝ] JetAlgebra) = 1 := by
  simp [complexRepJetGaugeGroupI_eq_algHom]

lemma complexRepJetGaugeGroupI_one_tmul_one (U : JetGaugeGroupI) :
    complexRepJetGaugeGroupI U ((1 : ℂ) ⊗ₜ[ℝ] (1 : JetAlgebra)) =
      (1 : ℂ) ⊗ₜ[ℝ] (1 : JetAlgebra) := by
  rw [complexRepJetGaugeGroupI_tmul, repJetGaugeGroupI_one]

/-- The complexified gauge action on a jet-algebra generator: the Maurer–Cartan
  shift of the component function. -/
lemma complexRepJetGaugeGroupI_ofGenerator (U : JetGaugeGroupI) (g : JetGenerators) :
    complexRepJetGaugeGroupI U ((1 : ℂ) ⊗ₜ[ℝ] ofGenerator g) =
      (1 : ℂ) ⊗ₜ[ℝ] ofGenerator g +
        ((mcShift U (JetComponentSpace.basis g) : ℝ) : ℂ) •
          ((1 : ℂ) ⊗ₜ[ℝ] (1 : JetAlgebra)) := by
  rw [complexRepJetGaugeGroupI_tmul, ofGenerator, repJetGaugeGroupI_ι,
    TensorProduct.tmul_add, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
    show ((mcShift U (JetComponentSpace.basis g) : ℝ) : ℂ) =
      algebraMap ℝ ℂ (mcShift U (JetComponentSpace.basis g)) from rfl,
    algebraMap_smul]

/-- Jets of constant gauge transformations act trivially on the complexified
  B-boson jet algebra. -/
lemma complexRepJetGaugeGroupI_ofConstant (g : GaugeGroupI)
    (x : ℂ ⊗[ℝ] JetAlgebra) :
    complexRepJetGaugeGroupI (JetGaugeGroupI.ofConstant g) x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, ha, hb]
  | tmul z b => rw [complexRepJetGaugeGroupI_tmul, repJetGaugeGroupI_ofConstant]

noncomputable def complexRepJetGaugeGroupIAlgHom (U : JetGaugeGroupI) :
    AlgHom ℂ (ℂ ⊗[ℝ] JetAlgebra) (ℂ ⊗[ℝ] JetAlgebra) where
  toFun := complexRepJetGaugeGroupI U
  map_add' := LinearMap.map_add _
  map_zero' := LinearMap.map_zero _
  map_one' := complexRepJetGaugeGroupI_one U
  map_mul' := complexRepJetGaugeGroupI_mul U
  commutes' r := by simp [complexRepJetGaugeGroupI_eq_algHom]

/-!

## The formal total derivative on the jet algebra

The formal total spacetime derivative `∂_μ` acts on the component functions of
the B-boson jet by appending the derivative index, `∂_s B_ν ↦ ∂_{s + {μ}} B_ν`,
and extends to the jet algebra as a derivation. It is constructed through the
polynomial coordinates of the jet algebra.

-/

/-- The formal total spacetime derivative on the B-boson jet algebra in the
  direction `μ`: the derivation sending each component function `∂_s B_ν` to
  `∂_{s + {μ}} B_ν`. -/
noncomputable def jetDeriv (μ : Fin 1 ⊕ Fin 3) : JetAlgebra →ₗ[ℝ] JetAlgebra :=
  (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis).symm.toLinearMap ∘ₗ
    (MvPolynomial.mkDerivation ℝ fun g : JetGenerators =>
      (MvPolynomial.X (JetGenerators.shift μ g) :
        MvPolynomial JetGenerators ℝ)).toLinearMap ∘ₗ
    (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis).toLinearMap

/-- The total derivative appends the derivative index to each component
  function. -/
@[simp]
lemma jetDeriv_ofGenerator (μ : Fin 1 ⊕ Fin 3) (g : JetGenerators) :
    jetDeriv μ (ofGenerator g) = ofGenerator (JetGenerators.shift μ g) := by
  simp only [jetDeriv, ofGenerator, LinearMap.coe_comp, Function.comp_apply,
    AlgEquiv.toLinearMap_apply, Derivation.coeFn_coe]
  rw [SymmetricAlgebra.equivMvPolynomial_ι_apply, MvPolynomial.mkDerivation_X,
    SymmetricAlgebra.equivMvPolynomial_symm_X]

@[simp]
lemma jetDeriv_one (μ : Fin 1 ⊕ Fin 3) : jetDeriv μ (1 : JetAlgebra) = 0 := by
  simp [jetDeriv]

/-- The total derivative is a derivation: the Leibniz rule on the jet algebra. -/
lemma jetDeriv_mul (μ : Fin 1 ⊕ Fin 3) (x y : JetAlgebra) :
    jetDeriv μ (x * y) = jetDeriv μ x * y + x * jetDeriv μ y := by
  simp only [jetDeriv, LinearMap.coe_comp, Function.comp_apply,
    AlgEquiv.toLinearMap_apply, map_mul, Derivation.coeFn_coe, Derivation.leibniz,
    smul_eq_mul, map_add, AlgEquiv.symm_apply_apply]
  ring

lemma jetDeriv_comm (μ ν : Fin 1 ⊕ Fin 3) (x : JetAlgebra) :
    jetDeriv μ (jetDeriv ν x) = jetDeriv ν (jetDeriv μ x) := by
  induction x using SymmetricAlgebra.induction with
  | algebraMap r => simp [Algebra.algebraMap_eq_smul_one]
  | ι v =>
    have key : (jetDeriv μ) ∘ₗ (jetDeriv ν) ∘ₗ
          (SymmetricAlgebra.ι ℝ JetComponentSpace) =
        (jetDeriv ν) ∘ₗ (jetDeriv μ) ∘ₗ
          (SymmetricAlgebra.ι ℝ JetComponentSpace) := by
      refine JetComponentSpace.basis.ext fun g => ?_
      simp only [LinearMap.coe_comp, Function.comp_apply,
        show ∀ h : JetGenerators,
          SymmetricAlgebra.ι ℝ JetComponentSpace (JetComponentSpace.basis h) =
            ofGenerator h from fun _ => rfl,
        jetDeriv_ofGenerator, JetGenerators.shift_comm]
    exact DFunLike.congr_fun key v
  | mul a b ha hb =>
    simp only [jetDeriv_mul, map_add, ha, hb]
    abel
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The Leibniz rule for the complexified total derivative on the complexified
  jet algebra. -/
lemma jetDeriv_baseChange_mul (μ : Fin 1 ⊕ Fin 3) (x y : ℂ ⊗[ℝ] JetAlgebra) :
    LinearMap.baseChange ℂ (jetDeriv μ) (x * y) =
      LinearMap.baseChange ℂ (jetDeriv μ) x * y +
        x * LinearMap.baseChange ℂ (jetDeriv μ) y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    simp only [add_mul, map_add, ha, hb]
    ring
  | tmul c b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a' b' ha' hb' =>
      simp only [mul_add, map_add, ha', hb']
      ring
    | tmul c' b' =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.baseChange_tmul,
        jetDeriv_mul, TensorProduct.tmul_add]

lemma jetDeriv_baseChange_comm (μ ν : Fin 1 ⊕ Fin 3) (x : ℂ ⊗[ℝ] JetAlgebra) :
    LinearMap.baseChange ℂ (jetDeriv μ) (LinearMap.baseChange ℂ (jetDeriv ν) x) =
      LinearMap.baseChange ℂ (jetDeriv ν) (LinearMap.baseChange ℂ (jetDeriv μ) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add, ha, hb]
  | tmul c b =>
    simp only [LinearMap.baseChange_tmul, jetDeriv_comm]

/-- The complexified total derivative on a jet-algebra generator. -/
lemma jetDeriv_baseChange_ofGenerator (ν : Fin 1 ⊕ Fin 3) (g : JetGenerators) :
    LinearMap.baseChange ℂ (jetDeriv ν) ((1 : ℂ) ⊗ₜ[ℝ] ofGenerator g) =
      (1 : ℂ) ⊗ₜ[ℝ] ofGenerator (JetGenerators.shift ν g) := by
  rw [LinearMap.baseChange_tmul, jetDeriv_ofGenerator]

/-- The polynomial coordinates of the total derivative. -/
lemma equivMvPolynomial_jetDeriv (ν : Fin 1 ⊕ Fin 3) (x : JetAlgebra) :
    SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis (jetDeriv ν x) =
      (MvPolynomial.mkDerivation ℝ fun g : JetGenerators =>
        (MvPolynomial.X (JetGenerators.shift ν g) : MvPolynomial JetGenerators ℝ))
        (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis x) := by
  simp only [jetDeriv, LinearMap.coe_comp, Function.comp_apply,
    AlgEquiv.toLinearMap_apply, AlgEquiv.apply_symm_apply, Derivation.coeFn_coe]

/-!

## The Maurer–Cartan correction derivations

A local gauge transformation changes the B boson by a gradient, `δB_μ = ∂_μλ`
with `λ` the phase of the `U(1)` jet (the Maurer–Cartan form is closed,
`pderiv_maurerCartanU1_symm`). On genuine field configurations this variation
commutes with differentiation, since `δ(∂_s B_μ) = ∂_s ∂_μ λ`. The jet algebra,
however, remembers of `λ` only its Taylor coefficients at the base point: the
gauge action shifts each coordinate `∂_s B_μ` by the frozen constant
`⟨mc, ∂_s B_μ⟩ = (∂_s ∂_μ λ)(0)`, and the formal total derivative annihilates
constants while sending `∂_s B_μ` to `∂_{s+ν} B_μ`. Differentiating after
transforming therefore drops exactly the term that, on fields, would come from
the derivative hitting the gauge parameter.

The correction derivation `mcDeriv U t` reinstates that term as an operator:
"differentiation acting on the gauge parameter instead of the field", the
derivation sending each component function `∂_s B_ν` to the constant
`⟨mc, ∂_{s+t} B_ν⟩`. The commutator of the gauge action with the total
derivative is the gauge action composed with the weight-`{ν}` correction
(`repJetGaugeGroupI_jetDeriv`), and commuting a correction past a further
derivative raises its weight (`mcDeriv_jetDeriv`), so the corrections close
into an algebra.

This algebra is what makes covariant derivatives of charged fields covariant:
in `D_μψ = ∂_μψ - i q B_μ ψ` the gauge shift of `B_μ` must cancel the
derivative of the hypercharge character produced by `∂_μ` acting on the
transformed `ψ`, and at higher orders the iterated derivatives of the gauge
parameter on both sides are matched precisely by the anomaly operators built
from `mcDeriv`, which annihilate the covariant derivatives (see
`QED.JetAlgebra`).

-/

/-- The Maurer–Cartan correction derivation of weight `t` of a `U(1)` jet: the
  derivation of the B-boson jet algebra sending the component function `∂_s B_ν`
  to the constant `⟨mc, ∂_{s+t} B_ν⟩`. -/
noncomputable def mcDeriv (U : JetGaugeGroupI) (t : Multiset (Fin 1 ⊕ Fin 3)) :
    JetAlgebra →ₗ[ℝ] JetAlgebra :=
  (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis).symm.toLinearMap ∘ₗ
    (MvPolynomial.mkDerivation ℝ fun g : JetGenerators =>
      (MvPolynomial.C (mcShift U (JetComponentSpace.basis
        (JetGenerators.shiftMulti t g))) : MvPolynomial JetGenerators ℝ)).toLinearMap ∘ₗ
    (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis).toLinearMap

@[simp]
lemma mcDeriv_ofGenerator (U : JetGaugeGroupI) (t : Multiset (Fin 1 ⊕ Fin 3))
    (g : JetGenerators) :
    mcDeriv U t (ofGenerator g) = algebraMap ℝ JetAlgebra
      (mcShift U (JetComponentSpace.basis (JetGenerators.shiftMulti t g))) := by
  simp only [mcDeriv, ofGenerator, LinearMap.coe_comp, Function.comp_apply,
    AlgEquiv.toLinearMap_apply, Derivation.coeFn_coe]
  rw [SymmetricAlgebra.equivMvPolynomial_ι_apply, MvPolynomial.mkDerivation_X,
    ← MvPolynomial.algebraMap_eq]
  exact AlgEquiv.commutes _ _

@[simp]
lemma mcDeriv_one (U : JetGaugeGroupI) (t : Multiset (Fin 1 ⊕ Fin 3)) :
    mcDeriv U t (1 : JetAlgebra) = 0 := by
  simp [mcDeriv]

/-- The correction derivations satisfy the Leibniz rule. -/
lemma mcDeriv_mul (U : JetGaugeGroupI) (t : Multiset (Fin 1 ⊕ Fin 3))
    (x y : JetAlgebra) :
    mcDeriv U t (x * y) = mcDeriv U t x * y + x * mcDeriv U t y := by
  simp only [mcDeriv, LinearMap.coe_comp, Function.comp_apply,
    AlgEquiv.toLinearMap_apply, map_mul, Derivation.coeFn_coe, Derivation.leibniz,
    smul_eq_mul, map_add, AlgEquiv.symm_apply_apply]
  ring

/-- The complexified Leibniz rule for the correction derivations. -/
lemma mcDeriv_baseChange_mul (U : JetGaugeGroupI) (t : Multiset (Fin 1 ⊕ Fin 3))
    (x y : ℂ ⊗[ℝ] JetAlgebra) :
    LinearMap.baseChange ℂ (mcDeriv U t) (x * y) =
      LinearMap.baseChange ℂ (mcDeriv U t) x * y +
        x * LinearMap.baseChange ℂ (mcDeriv U t) y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    simp only [add_mul, map_add, ha, hb]
    ring
  | tmul c b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a' b' ha' hb' =>
      simp only [mul_add, map_add, ha', hb']
      ring
    | tmul c' b' =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.baseChange_tmul,
        mcDeriv_mul, TensorProduct.tmul_add]

/-- The polynomial coordinates of the correction derivations. -/
lemma equivMvPolynomial_mcDeriv (U : JetGaugeGroupI) (t : Multiset (Fin 1 ⊕ Fin 3))
    (x : JetAlgebra) :
    SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis (mcDeriv U t x) =
      (MvPolynomial.mkDerivation ℝ fun g : JetGenerators =>
        (MvPolynomial.C (mcShift U (JetComponentSpace.basis
          (JetGenerators.shiftMulti t g))) : MvPolynomial JetGenerators ℝ))
        (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis x) := by
  simp only [mcDeriv, LinearMap.coe_comp, Function.comp_apply,
    AlgEquiv.toLinearMap_apply, AlgEquiv.apply_symm_apply, Derivation.coeFn_coe]

/-- Commutation of the correction derivations with the total derivative: the
  weight of the correction absorbs the derivative index. -/
lemma mcDeriv_jetDeriv (U : JetGaugeGroupI) (t : Multiset (Fin 1 ⊕ Fin 3))
    (ν : Fin 1 ⊕ Fin 3) (x : JetAlgebra) :
    mcDeriv U t (jetDeriv ν x) =
      jetDeriv ν (mcDeriv U t x) + mcDeriv U (t + {ν}) x := by
  have key : ∀ p : MvPolynomial JetGenerators ℝ,
      (MvPolynomial.mkDerivation ℝ fun g : JetGenerators =>
        (MvPolynomial.C (mcShift U (JetComponentSpace.basis
          (JetGenerators.shiftMulti t g))) : MvPolynomial JetGenerators ℝ))
        ((MvPolynomial.mkDerivation ℝ fun g : JetGenerators =>
          (MvPolynomial.X (JetGenerators.shift ν g) : MvPolynomial JetGenerators ℝ)) p) =
      (MvPolynomial.mkDerivation ℝ fun g : JetGenerators =>
        (MvPolynomial.X (JetGenerators.shift ν g) : MvPolynomial JetGenerators ℝ))
        ((MvPolynomial.mkDerivation ℝ fun g : JetGenerators =>
          (MvPolynomial.C (mcShift U (JetComponentSpace.basis
            (JetGenerators.shiftMulti t g))) : MvPolynomial JetGenerators ℝ)) p) +
      (MvPolynomial.mkDerivation ℝ fun g : JetGenerators =>
        (MvPolynomial.C (mcShift U (JetComponentSpace.basis
          (JetGenerators.shiftMulti (t + {ν}) g))) : MvPolynomial JetGenerators ℝ)) p := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      simp [MvPolynomial.derivation_C]
    | add p q hp hq =>
      simp only [map_add, hp, hq]
      ring
    | mul_X p g ih =>
      have hlam : mcShift U (JetComponentSpace.basis
          (JetGenerators.shiftMulti t (JetGenerators.shift ν g))) =
          mcShift U (JetComponentSpace.basis
            (JetGenerators.shiftMulti (t + {ν}) g)) := by
        rw [JetGenerators.shiftMulti_shift]
      simp only [Derivation.leibniz, smul_eq_mul, MvPolynomial.mkDerivation_X,
        MvPolynomial.derivation_C, map_add, mul_zero, zero_add]
      rw [ih, hlam]
      ring
  rw [show mcDeriv U t (jetDeriv ν x) =
      (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis).symm
        (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis
          (mcDeriv U t (jetDeriv ν x))) from
      (AlgEquiv.symm_apply_apply _ _).symm,
    equivMvPolynomial_mcDeriv, equivMvPolynomial_jetDeriv, key, map_add,
    ← equivMvPolynomial_mcDeriv U t x, ← equivMvPolynomial_jetDeriv ν (mcDeriv U t x),
    AlgEquiv.symm_apply_apply, ← equivMvPolynomial_mcDeriv U (t + {ν}) x,
    AlgEquiv.symm_apply_apply]

/-- Commutation of the jet gauge action with the total derivative: the
  substitution action commutes with `∂_ν` up to the Maurer–Cartan correction
  derivation of weight `{ν}`. -/
lemma repJetGaugeGroupI_jetDeriv (U : JetGaugeGroupI) (ν : Fin 1 ⊕ Fin 3)
    (x : JetAlgebra) : repJetGaugeGroupI U (jetDeriv ν x) =
      jetDeriv ν (repJetGaugeGroupI U x) + repJetGaugeGroupI U (mcDeriv U {ν} x) := by
  have key : ∀ p : MvPolynomial JetGenerators ℝ,
      MvPolynomial.aeval (fun g => MvPolynomial.X g +
          MvPolynomial.C (mcShift U (JetComponentSpace.basis g)))
        ((MvPolynomial.mkDerivation ℝ fun g : JetGenerators =>
          (MvPolynomial.X (JetGenerators.shift ν g) : MvPolynomial JetGenerators ℝ)) p) =
      (MvPolynomial.mkDerivation ℝ fun g : JetGenerators =>
        (MvPolynomial.X (JetGenerators.shift ν g) : MvPolynomial JetGenerators ℝ))
        (MvPolynomial.aeval (fun g => MvPolynomial.X g +
          MvPolynomial.C (mcShift U (JetComponentSpace.basis g))) p) +
      MvPolynomial.aeval (fun g => MvPolynomial.X g +
          MvPolynomial.C (mcShift U (JetComponentSpace.basis g)))
        ((MvPolynomial.mkDerivation ℝ fun g : JetGenerators =>
          (MvPolynomial.C (mcShift U (JetComponentSpace.basis
            (JetGenerators.shiftMulti {ν} g))) : MvPolynomial JetGenerators ℝ)) p) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      simp [MvPolynomial.derivation_C, MvPolynomial.algebraMap_eq]
    | add p q hp hq =>
      simp only [map_add, hp, hq]
      ring
    | mul_X p g ih =>
      have hlam : mcShift U (JetComponentSpace.basis (JetGenerators.shift ν g)) =
          mcShift U (JetComponentSpace.basis
            (JetGenerators.shiftMulti {ν} g)) := by
        rw [JetGenerators.shiftMulti_singleton]
      simp only [Derivation.leibniz, smul_eq_mul, MvPolynomial.mkDerivation_X,
        MvPolynomial.derivation_C, map_add, map_mul, add_zero,
        MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
      rw [ih, hlam]
      ring
  rw [show repJetGaugeGroupI U (jetDeriv ν x) =
      (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis).symm
        (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis
          (repJetGaugeGroupI U (jetDeriv ν x))) from
      (AlgEquiv.symm_apply_apply _ _).symm,
    equivMvPolynomial_repJetGaugeGroupI, equivMvPolynomial_jetDeriv, key, map_add,
    ← equivMvPolynomial_repJetGaugeGroupI U x,
    ← equivMvPolynomial_jetDeriv ν (repJetGaugeGroupI U x),
    ← equivMvPolynomial_mcDeriv U {ν} x,
    ← equivMvPolynomial_repJetGaugeGroupI U (mcDeriv U {ν} x),
    AlgEquiv.symm_apply_apply]
  congr 1
  exact AlgEquiv.symm_apply_apply _ _

/-- The complexified commutation of the gauge action with the total
  derivative. -/
lemma complexRepJetGaugeGroupI_baseChange_jetDeriv (U : JetGaugeGroupI)
    (ν : Fin 1 ⊕ Fin 3) (y : ℂ ⊗[ℝ] JetAlgebra) :
    complexRepJetGaugeGroupI U (LinearMap.baseChange ℂ (jetDeriv ν) y) =
      LinearMap.baseChange ℂ (jetDeriv ν) (complexRepJetGaugeGroupI U y) +
        complexRepJetGaugeGroupI U
          (LinearMap.baseChange ℂ (mcDeriv U {ν}) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add, ha, hb]
    abel
  | tmul c b =>
    simp only [LinearMap.baseChange_tmul, complexRepJetGaugeGroupI_tmul,
      repJetGaugeGroupI_jetDeriv, TensorProduct.tmul_add]

/-- The complexified commutation of the correction derivations with the total
  derivative. -/
lemma mcDeriv_baseChange_jetDeriv (U : JetGaugeGroupI)
    (t : Multiset (Fin 1 ⊕ Fin 3)) (ν : Fin 1 ⊕ Fin 3) (y : ℂ ⊗[ℝ] JetAlgebra) :
    LinearMap.baseChange ℂ (mcDeriv U t) (LinearMap.baseChange ℂ (jetDeriv ν) y) =
      LinearMap.baseChange ℂ (jetDeriv ν)
          (LinearMap.baseChange ℂ (mcDeriv U t) y) +
        LinearMap.baseChange ℂ (mcDeriv U (t + {ν})) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add, ha, hb]
    abel
  | tmul c b =>
    simp only [LinearMap.baseChange_tmul, mcDeriv_jetDeriv, TensorProduct.tmul_add]


/-- The complexified correction derivation on a jet-algebra generator. -/
lemma mcDeriv_baseChange_ofGenerator (U : JetGaugeGroupI)
    (t : Multiset (Fin 1 ⊕ Fin 3)) (g : JetGenerators) :
    LinearMap.baseChange ℂ (mcDeriv U t) ((1 : ℂ) ⊗ₜ[ℝ] ofGenerator g) =
      ((mcShift U (JetComponentSpace.basis (JetGenerators.shiftMulti t g)) : ℝ) : ℂ) •
        ((1 : ℂ) ⊗ₜ[ℝ] (1 : JetAlgebra)) := by
  rw [LinearMap.baseChange_tmul, mcDeriv_ofGenerator, Algebra.algebraMap_eq_smul_one,
    TensorProduct.tmul_smul,
    show ((mcShift U (JetComponentSpace.basis (JetGenerators.shiftMulti t g)) : ℝ) : ℂ) =
      algebraMap ℝ ℂ (mcShift U (JetComponentSpace.basis
        (JetGenerators.shiftMulti t g))) from rfl,
    algebraMap_smul]

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
  simp only [fieldStrength, map_sub, ofGenerator, repJetGaugeGroupI_ι, mcShift_basis_dB]
  rw [maurerCartanU1Coeff_single_symm]
  abel

noncomputable def fieldStrengthDeriv (s : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) :
    BBoson.JetAlgebra :=
  ofGenerator (JetGenerators.dB (s + {μ}) ν) - ofGenerator (JetGenerators.dB (s + {ν}) μ)

lemma fieldStrengthDeriv_antisymm (s : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) :
    fieldStrengthDeriv s μ ν = -fieldStrengthDeriv s ν μ := by
  simp [fieldStrengthDeriv]

lemma repJetGaugeGroupI_fieldStrengthDeriv (U : JetGaugeGroupI) (s : Multiset (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) :
    repJetGaugeGroupI U (fieldStrengthDeriv s μ ν) = fieldStrengthDeriv s μ ν := by
  simp only [fieldStrengthDeriv, map_sub, ofGenerator, repJetGaugeGroupI_ι]
  rw [mcShift_basis_dB_symm]
  abel

lemma fieldStrengthDeriv_bianchi_identity (s : Multiset (Fin 1 ⊕ Fin 3)) (μ ν ρ : Fin 1 ⊕ Fin 3) :
    fieldStrengthDeriv (s + {μ}) ν ρ + fieldStrengthDeriv (s + {ν}) ρ μ +
      fieldStrengthDeriv (s + {ρ}) μ ν = 0 := by
  simp only [fieldStrengthDeriv]
  grind


/-!

## A. Invariance under the gauge group

We now want to show that the if an element of the jet algebra is invariant under
the action of the jet gauge group, then it is a polynomial
in the field strength and its derivatives.

-/


/-!

### A.1 Gauge realization of translations of the jet coordinates

The gauge invariants of the B-boson jet algebra are computed below by realizing
arbitrary translations of the jet coordinates through explicit local `U(1)` gauge
transformations: the jets `exp(-i a X^w)` of exponentials of a single spacetime
monomial, embedded in the jet gauge group with trivial colour and weak factors.
The exponential property `exp(c X^w) exp(c' X^w) = exp((c + c') X^w)` of the
underlying series gives unitarity, and the chain rule gives the Maurer–Cartan
form: the jet of the gradient `a ∂_ν X^w`. For every nonzero symmetrized
multi-index `t` and every real `r`, the transformation `exp(-i a X^t)` with
`a = r / t!` shifts every component function with total multi-index `t` by
exactly `r`, and all others by nothing.

-/

open Classical in
/-- The jet of the local `U(1)` gauge transformation `exp(-i a X^w)`: the
  exponential of an imaginary multiple of a spacetime monomial — the power series
  `∑ₙ ((-i a)ⁿ/n!) X^{n w}`, defined coefficientwise, unitary by the exponential
  property — embedded in the jet gauge group with trivial colour and weak
  factors. -/
noncomputable def expUnitary (a : ℝ) (w : (Fin 1 ⊕ Fin 3) →₀ ℕ) (hw : w ≠ 0) :
    JetGaugeGroupI :=
  let F : ℂ → JetRing := fun c k => if h : ∃ n : ℕ, k = n • w then
    c ^ h.choose / (h.choose.factorial : ℂ) else 0
  (1, 1, ⟨F (-(a : ℂ) * Complex.I), by
    classical
    have hex : ∃ ρ, w ρ ≠ 0 := (Finsupp.ne_iff.mp hw).imp fun _ h => by simpa using h
    have hcancel : ∀ {n m : ℕ}, n • w = m • w → n = m := by
      intro n m h
      obtain ⟨ρ, hρ⟩ := hex
      exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hρ)
        (by simpa using DFunLike.congr_fun h ρ)
    have hnsmul : ∀ (c : ℂ) (n : ℕ), coeff (n • w) (F c) = c ^ n / (n.factorial : ℂ) := by
      intro c n
      have h : ∃ m : ℕ, n • w = m • w := ⟨n, rfl⟩
      show (if h : ∃ m : ℕ, n • w = m • w then c ^ h.choose / (h.choose.factorial : ℂ)
        else 0) = _
      rw [dif_pos h, show h.choose = n from (hcancel h.choose_spec).symm]
    have hne : ∀ (c : ℂ) {k : (Fin 1 ⊕ Fin 3) →₀ ℕ}, (∀ n : ℕ, k ≠ n • w) →
        coeff k (F c) = 0 := by
      intro c k hk
      show (if h : ∃ n : ℕ, k = n • w then c ^ h.choose / (h.choose.factorial : ℂ)
        else 0) = 0
      rw [dif_neg (not_exists.mpr hk)]
    have hmul : ∀ c c' : ℂ, F c * F c' = F (c + c') := by
      intro c c'
      ext k
      by_cases hk : ∃ n : ℕ, k = n • w
      · obtain ⟨N, rfl⟩ := hk
        rw [coeff_mul, hnsmul]
        have hsub : (Finset.range (N + 1)).image (fun n => (n • w, (N - n) • w)) ⊆
            Finset.antidiagonal (N • w) := by
          intro p hp
          obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hp
          rw [Finset.mem_antidiagonal, ← add_smul,
            Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))]
        have hvanish : ∀ p ∈ Finset.antidiagonal (N • w),
            p ∉ (Finset.range (N + 1)).image (fun n => (n • w, (N - n) • w)) →
            coeff p.1 (F c) * coeff p.2 (F c') = 0 := by
          intro p hp hpn
          by_cases h1 : ∃ n : ℕ, p.1 = n • w
          · obtain ⟨n₁, h1⟩ := h1
            exfalso
            apply hpn
            have hsum : p.1 + p.2 = N • w := Finset.mem_antidiagonal.mp hp
            obtain ⟨ρ, hρ⟩ := hex
            have hcoords : ∀ ρ', n₁ * w ρ' + p.2 ρ' = N * w ρ' := by
              intro ρ'
              have h' := DFunLike.congr_fun hsum ρ'
              simpa [h1, Finsupp.smul_apply] using h'
            have hle : n₁ ≤ N :=
              Nat.le_of_mul_le_mul_right (by have := hcoords ρ; omega)
                (Nat.pos_of_ne_zero hρ)
            have h2 : p.2 = (N - n₁) • w := by
              ext ρ'
              rw [Finsupp.smul_apply, smul_eq_mul, Nat.sub_mul]
              have := hcoords ρ'
              omega
            exact Finset.mem_image.mpr
              ⟨n₁, Finset.mem_range.mpr (Nat.lt_succ_of_le hle), by rw [← h1, ← h2]⟩
          · rw [hne c (not_exists.mp h1), zero_mul]
        rw [← Finset.sum_subset hsub hvanish,
          Finset.sum_image (fun n _ m _ h => hcancel (congrArg Prod.fst h)),
          add_pow, Finset.sum_div]
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [hnsmul, hnsmul]
        have hle : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
        have hfact : ((N.choose n : ℂ)) * (n.factorial : ℂ) * ((N - n).factorial : ℂ) =
            (N.factorial : ℂ) := by
          exact_mod_cast congrArg (Nat.cast : ℕ → ℂ)
            (Nat.choose_mul_factorial_mul_factorial hle)
        have h1 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
        have h2 : ((N - n).factorial : ℂ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (N - n).factorial_ne_zero
        have h3 : (N.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr N.factorial_ne_zero
        rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero h1 h2) h3]
        linear_combination (-(c ^ n * c' ^ (N - n))) * hfact
      · rw [hne _ (not_exists.mp hk), coeff_mul]
        refine Finset.sum_eq_zero fun p hp => ?_
        by_cases h1 : ∃ n : ℕ, p.1 = n • w
        · by_cases h2 : ∃ n : ℕ, p.2 = n • w
          · exfalso
            obtain ⟨n₁, h1⟩ := h1
            obtain ⟨n₂, h2⟩ := h2
            exact hk ⟨n₁ + n₂, by rw [← Finset.mem_antidiagonal.mp hp, h1, h2, add_smul]⟩
          · rw [hne _ (not_exists.mp h2), mul_zero]
        · rw [hne _ (not_exists.mp h1), zero_mul]
    have hstar : ∀ c : ℂ, star (F c) = F (star c) := by
      intro c
      ext k
      rw [JetRing.coeff_star]
      by_cases hk : ∃ n : ℕ, k = n • w
      · obtain ⟨n, rfl⟩ := hk
        rw [hnsmul, hnsmul, star_div₀, star_pow, star_natCast]
      · rw [hne _ (not_exists.mp hk), hne _ (not_exists.mp hk), star_zero]
    have hzero : F 0 = 1 := by
      ext k
      by_cases hk : ∃ n : ℕ, k = n • w
      · obtain ⟨n, rfl⟩ := hk
        rw [hnsmul, coeff_one]
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp
        · rw [zero_pow (Nat.pos_iff_ne_zero.mp hn), zero_div, if_neg fun h0 =>
            Nat.pos_iff_ne_zero.mp hn (hcancel (h0.trans (zero_smul ℕ w).symm))]
      · rw [hne _ (not_exists.mp hk), coeff_one,
          if_neg (fun h => hk ⟨0, by rw [h, zero_smul]⟩)]
    have hsc : star (-(a : ℂ) * Complex.I) = -(-(a : ℂ) * Complex.I) := by
      rw [star_mul', Complex.star_def, Complex.conj_I, map_neg, Complex.conj_ofReal]
      ring
    rw [Unitary.mem_iff, hstar, hsc, hmul, hmul, neg_add_cancel, add_neg_cancel, hzero]
    exact ⟨rfl, rfl⟩⟩)

/-- The Taylor coefficient of the exponential gauge jet at a multiple of the
  exponent. -/
lemma coeff_expUnitary_nsmul (a : ℝ) {w : (Fin 1 ⊕ Fin 3) →₀ ℕ} (hw : w ≠ 0) (n : ℕ) :
    coeff (n • w) (((expUnitary a w hw).2.2 : unitary JetRing) : JetRing) =
      (-(a : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) := by
  classical
  have h : ∃ m : ℕ, n • w = m • w := ⟨n, rfl⟩
  have hch : h.choose = n := by
    obtain ⟨ρ, hρ⟩ := Finsupp.ne_iff.mp hw
    exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (by simpa using hρ))
      (by simpa using DFunLike.congr_fun h.choose_spec ρ)).symm
  show (if h : ∃ m : ℕ, n • w = m • w then
      (-(a : ℂ) * Complex.I) ^ h.choose / (h.choose.factorial : ℂ) else 0) = _
  rw [dif_pos h, hch]

/-- The Taylor coefficients of the exponential gauge jet vanish away from the
  multiples of the exponent. -/
lemma coeff_expUnitary_of_forall_ne (a : ℝ) {w : (Fin 1 ⊕ Fin 3) →₀ ℕ} (hw : w ≠ 0)
    {k : (Fin 1 ⊕ Fin 3) →₀ ℕ} (hk : ∀ n : ℕ, k ≠ n • w) :
    coeff k (((expUnitary a w hw).2.2 : unitary JetRing) : JetRing) = 0 := by
  classical
  show (if h : ∃ n : ℕ, k = n • w then
      (-(a : ℂ) * Complex.I) ^ h.choose / (h.choose.factorial : ℂ) else 0) = 0
  rw [dif_neg (not_exists.mpr hk)]

/-- The chain rule for the exponential gauge jet:
  `∂_ν exp(-i a X^w) = -i a w_ν X^{w - e_ν} exp(-i a X^w)`. -/
lemma pderiv_expUnitary (a : ℝ) {w : (Fin 1 ⊕ Fin 3) →₀ ℕ} (hw : w ≠ 0)
    (ν : Fin 1 ⊕ Fin 3) :
    pderiv ℂ ν (((expUnitary a w hw).2.2 : unitary JetRing) : JetRing) =
      ((-(a : ℂ) * Complex.I) * (w ν : ℂ)) •
        (monomial (w - Finsupp.single ν 1) 1 *
          (((expUnitary a w hw).2.2 : unitary JetRing) : JetRing)) := by
  classical
  ext k
  rw [coeff_pderiv, map_smul, smul_eq_mul, coeff_monomial_mul]
  by_cases hA : ∃ n : ℕ, k + Finsupp.single ν 1 = n • w
  · obtain ⟨n, hn⟩ := hA
    have hcoords : ∀ ρ, k ρ + (Finsupp.single ν 1) ρ = n * w ρ := by
      intro ρ
      have h' := DFunLike.congr_fun hn ρ
      simpa [Finsupp.smul_apply] using h'
    have hkν : k ν + 1 = n * w ν := by
      have := hcoords ν
      rwa [Finsupp.single_eq_same] at this
    have hnpos : 0 < n := Nat.pos_of_ne_zero fun h => by simp [h] at hkν
    have hwνpos : 0 < w ν := Nat.pos_of_ne_zero fun h => by simp [h] at hkν
    have hdk : w - Finsupp.single ν 1 ≤ k := by
      rw [Finsupp.le_def]
      intro ρ
      rw [Finsupp.tsub_apply]
      have h1 := hcoords ρ
      have h2 : w ρ ≤ n * w ρ := Nat.le_mul_of_pos_left _ hnpos
      by_cases hρν : ρ = ν
      · subst hρν
        rw [Finsupp.single_eq_same] at h1 ⊢
        omega
      · have hsρ : (Finsupp.single ν 1) ρ = 0 :=
          Finsupp.single_eq_of_ne hρν
        rw [hsρ] at h1 ⊢
        omega
    have hkd : k - (w - Finsupp.single ν 1) = (n - 1) • w := by
      ext ρ
      rw [Finsupp.tsub_apply, Finsupp.tsub_apply, Finsupp.smul_apply, smul_eq_mul,
        Nat.sub_mul, one_mul]
      have h1 := hcoords ρ
      have h2 : w ρ ≤ n * w ρ := Nat.le_mul_of_pos_left _ hnpos
      by_cases hρν : ρ = ν
      · subst hρν
        rw [Finsupp.single_eq_same] at h1 ⊢
        omega
      · have hsρ : (Finsupp.single ν 1) ρ = 0 :=
          Finsupp.single_eq_of_ne hρν
        rw [hsρ] at h1 ⊢
        omega
    rw [if_pos hdk, one_mul, hkd, hn, coeff_expUnitary_nsmul a hw,
      coeff_expUnitary_nsmul a hw]
    have hcast : ((k ν : ℂ) + 1) = (n : ℂ) * (w ν : ℂ) := by exact_mod_cast hkν
    rw [hcast]
    have hfac : (n.factorial : ℂ) = (n : ℂ) * ((n - 1).factorial : ℂ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℂ)
        (Nat.mul_factorial_pred (Nat.pos_iff_ne_zero.mp hnpos)).symm
    have hpow : (-(a : ℂ) * Complex.I) ^ n =
        (-(a : ℂ) * Complex.I) * (-(a : ℂ) * Complex.I) ^ (n - 1) := by
      conv_lhs => rw [show n = 1 + (n - 1) by omega, pow_add, pow_one]
    rw [hfac, hpow]
    have h1 : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hnpos)
    have h2 : (((n - 1).factorial : ℂ)) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
  · rw [coeff_expUnitary_of_forall_ne a hw (not_exists.mp hA), zero_mul]
    by_cases hwv : w ν = 0
    · rw [hwv]
      simp
    · have hzero : (if w - Finsupp.single ν 1 ≤ k then
          1 * coeff (k - (w - Finsupp.single ν 1))
            (((expUnitary a w hw).2.2 : unitary JetRing) : JetRing) else 0) = 0 := by
        split_ifs with hdk
        · rw [one_mul]
          refine coeff_expUnitary_of_forall_ne a hw fun m hm => ?_
          apply hA
          refine ⟨m + 1, ?_⟩
          have hle : Finsupp.single ν 1 ≤ w :=
            Finsupp.single_le_iff.mpr (Nat.pos_of_ne_zero hwv)
          have h1 : k - (w - Finsupp.single ν 1) + (w - Finsupp.single ν 1) = k :=
            tsub_add_cancel_of_le hdk
          have h2 : (w - Finsupp.single ν 1) + Finsupp.single ν 1 = w :=
            tsub_add_cancel_of_le hle
          calc k + Finsupp.single ν 1
              = k - (w - Finsupp.single ν 1) + (w - Finsupp.single ν 1) +
                Finsupp.single ν 1 := by rw [h1]
            _ = m • w + w := by rw [hm, add_assoc, h2]
            _ = (m + 1) • w := by rw [add_smul, one_smul]
        · rfl
      rw [hzero, mul_zero]

/-- The Maurer–Cartan series of the exponential gauge jet: the monomial
  `a w_ν X^{w - e_ν}`, which is the jet of the gradient `a ∂_ν X^w`. The star of
  the series is eliminated by the unitarity relation, so only the chain rule
  enters. -/
lemma maurerCartanU1_expUnitary (a : ℝ) (w : (Fin 1 ⊕ Fin 3) →₀ ℕ) (hw : w ≠ 0)
    (ν : Fin 1 ⊕ Fin 3) :
    maurerCartanU1 (expUnitary a w hw) ν =
      monomial (w - Finsupp.single ν 1) ((a : ℂ) * ((w ν : ℕ) : ℂ)) := by
  have hu : (((expUnitary a w hw).2.2 : unitary JetRing) : JetRing) *
      star (((expUnitary a w hw).2.2 : unitary JetRing) : JetRing) = 1 :=
    (Unitary.mem_iff.mp (expUnitary a w hw).2.2.2).2
  rw [maurerCartanU1, pderiv_expUnitary a hw ν, smul_mul_assoc,
    mul_assoc (monomial (w - Finsupp.single ν 1) 1), hu, mul_one, mul_smul_comm,
    ← monomial_zero_eq_C_apply, monomial_mul_monomial, zero_add, ← map_smul, smul_eq_mul]
  congr 1
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The Maurer–Cartan pairing of the exponential gauge jet `exp(-i a X^t)` with
  `a = r / t!`: it shifts precisely the component functions whose total
  symmetrized multi-index is `t`, and shifts them all by `r`. -/
lemma mcPairing_expUnitary (t : Multiset (Fin 1 ⊕ Fin 3))
    (ht : Multiset.toFinsupp t ≠ 0) (r : ℝ) (s : Multiset (Fin 1 ⊕ Fin 3))
    (ν : Fin 1 ⊕ Fin 3) :
    mcPairing (expUnitary (r / (∏ ρ, Nat.factorial (Multiset.toFinsupp t ρ)))
        (Multiset.toFinsupp t) ht) (JetComponentSpace.basis (.dB s ν)) =
      if s + {ν} = t then r else 0 := by
  rw [mcPairing_basis_dB', Complex.selfAdjointEquiv_apply,
    show ((maurerCartanU1Coeff (expUnitary (r / (∏ ρ, Nat.factorial (Multiset.toFinsupp t ρ)))
        (Multiset.toFinsupp t) ht) ν (Multiset.toFinsupp s) : selfAdjoint ℂ) : ℂ) =
      coeff (Multiset.toFinsupp s) (maurerCartanU1 (expUnitary
        (r / (∏ ρ, Nat.factorial (Multiset.toFinsupp t ρ)))
        (Multiset.toFinsupp t) ht) ν) from rfl,
    maurerCartanU1_expUnitary, coeff_monomial]
  by_cases hcase : s + {ν} = t
  · rw [if_pos hcase]
    have hmw : Multiset.toFinsupp s + Finsupp.single ν 1 = Multiset.toFinsupp t := by
      rw [← Multiset.toFinsupp_singleton, ← map_add]
      exact congrArg _ hcase
    have hwv : Multiset.toFinsupp t ν = Multiset.toFinsupp s ν + 1 := by
      rw [← hmw]
      simp
    have hm : Multiset.toFinsupp s = Multiset.toFinsupp t - Finsupp.single ν 1 :=
      eq_tsub_of_add_eq hmw
    have hF : (∏ ρ, Nat.factorial ((Multiset.toFinsupp t) ρ)) =
        ((Multiset.toFinsupp s) ν + 1) *
          ∏ ρ, Nat.factorial ((Multiset.toFinsupp s) ρ) := by
      rw [← hmw]
      exact prod_factorial_add_single (Multiset.toFinsupp s) ν
    rw [if_pos hm, nsmul_eq_mul, hwv, hF]
    have h1 : (((Multiset.toFinsupp s) ν + 1 : ℕ) : ℝ) ≠ 0 := by
      positivity
    have h2 : ((∏ ρ, Nat.factorial ((Multiset.toFinsupp s) ρ) : ℕ) : ℝ) ≠ 0 := by
      rw [Nat.cast_ne_zero]
      exact Finset.prod_ne_zero_iff.mpr fun ρ _ => Nat.factorial_ne_zero _
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re,
      Complex.natCast_im, mul_zero, sub_zero]
    push_cast
    field_simp
  · rw [if_neg hcase]
    by_cases hm : Multiset.toFinsupp s = Multiset.toFinsupp t - Finsupp.single ν 1
    · by_cases hwv : Multiset.toFinsupp t ν = 0
      · rw [if_pos hm, hwv]
        simp
      · exfalso
        apply hcase
        have hle : Finsupp.single ν 1 ≤ Multiset.toFinsupp t :=
          Finsupp.single_le_iff.mpr (Nat.pos_of_ne_zero hwv)
        have hmw : Multiset.toFinsupp s + Finsupp.single ν 1 = Multiset.toFinsupp t := by
          rw [hm, tsub_add_cancel_of_le hle]
        refine Multiset.toFinsupp.injective ?_
        rw [map_add, Multiset.toFinsupp_singleton]
        exact hmw
    · rw [if_neg hm]
      simp

/-- The Maurer–Cartan shift of the exponential gauge jet `exp(-i a X^t)` with
  `a = r / t!`: it shifts precisely the component functions whose total
  symmetrized multi-index is `t`, and shifts them all by `-r`. -/
lemma mcShift_expUnitary (t : Multiset (Fin 1 ⊕ Fin 3))
    (ht : Multiset.toFinsupp t ≠ 0) (r : ℝ) (s : Multiset (Fin 1 ⊕ Fin 3))
    (ν : Fin 1 ⊕ Fin 3) :
    mcShift (expUnitary (r / (∏ ρ, Nat.factorial (Multiset.toFinsupp t ρ)))
        (Multiset.toFinsupp t) ht) (JetComponentSpace.basis (.dB s ν)) =
      if s + {ν} = t then -r else 0 := by
  rw [mcShift_apply, mcPairing_expUnitary]
  split <;> simp

/-- The difference between a jet-algebra generator and its canonical
  representative is a derivative of the field strength, or zero. -/
lemma ofGenerator_sub_ofGenerator_canon_mem (g : JetGenerators) :
    ofGenerator g - ofGenerator (JetGenerators.canon g) ∈
      Algebra.adjoin ℝ (fieldStrengthDeriv.uncurry.uncurry '' Set.univ) := by
  obtain ⟨s, ν⟩ := g
  set p := JetGenerators.pick (JetGenerators.total (JetGenerators.dB s ν)) with hp
  by_cases hpν : p = ν
  · have hcanon : JetGenerators.canon (JetGenerators.dB s ν) = JetGenerators.dB s ν := by
      rw [JetGenerators.canon, ← hp, hpν]
      congr 1
      show (s + {ν}).erase ν = s
      rw [add_comm, Multiset.singleton_add, Multiset.erase_cons_head]
    rw [hcanon, sub_self]
    exact Subalgebra.zero_mem _
  · have hmem : p ∈ s + {ν} :=
      JetGenerators.pick_mem (JetGenerators.total_ne_zero (JetGenerators.dB s ν))
    have hps : p ∈ s := by
      rcases Multiset.mem_add.mp hmem with h | h
      · exact h
      · exact absurd (Multiset.mem_singleton.mp h) hpν
    have h2 : JetGenerators.canon (JetGenerators.dB s ν) =
        JetGenerators.dB (s.erase p + {ν}) p := by
      rw [JetGenerators.canon, ← hp]
      congr 1
      show (s + {ν}).erase p = s.erase p + {ν}
      exact Multiset.erase_add_left_pos _ hps
    have h1 : JetGenerators.dB s ν = JetGenerators.dB (s.erase p + {p}) ν := by
      congr 1
      rw [add_comm, Multiset.singleton_add]
      exact (Multiset.cons_erase hps).symm
    rw [h2, h1]
    exact Algebra.subset_adjoin ⟨((s.erase p, p), ν), Set.mem_univ _, rfl⟩

/-- The value of a translation gauge jet at the base point is one: the
  exponential series has constant coefficient `1`. -/
lemma constantCoeff_expUnitary (a : ℝ) (w : (Fin 1 ⊕ Fin 3) →₀ ℕ) (hw : w ≠ 0) :
    MvPowerSeries.constantCoeff
      (((expUnitary a w hw).2.2 : unitary JetRing) : JetRing) = 1 := by
  classical
  have hex : ∃ ρ, w ρ ≠ 0 := (Finsupp.ne_iff.mp hw).imp fun _ h => by simpa using h
  have h₀ : ∃ n : ℕ, (0 : (Fin 1 ⊕ Fin 3) →₀ ℕ) = n • w := ⟨0, by simp⟩
  show (if h : ∃ n : ℕ, (0 : (Fin 1 ⊕ Fin 3) →₀ ℕ) = n • w then
      (-(a : ℂ) * Complex.I) ^ h.choose / (h.choose.factorial : ℂ) else 0) = 1
  rw [dif_pos h₀]
  obtain ⟨ρ, hρ⟩ := hex
  have hch : h₀.choose = 0 := by
    by_contra hn
    have h := DFunLike.congr_fun h₀.choose_spec ρ
    simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.smul_apply, smul_eq_mul] at h
    exact absurd h.symm (Nat.mul_ne_zero hn hρ)
  rw [hch]
  simp

/-- The value of a translation gauge jet at the base point is the identity of the
  gauge group. -/
lemma eval_expUnitary_u1 (a : ℝ) (w : (Fin 1 ⊕ Fin 3) →₀ ℕ) (hw : w ≠ 0) :
    (expUnitary a w hw).eval.2.2 = 1 :=
  Subtype.ext (constantCoeff_expUnitary a w hw)

/-- The invariance direction of `repJetGaugeGroupI_apply_eq_self_iff_mem` from
  invariance under the `expUnitary` translation family alone: every element fixed
  by all the translation gauge transformations lies in the field-strength
  subalgebra. -/
lemma mem_adjoin_of_forall_expUnitary (V : JetAlgebra)
    (hV : ∀ (a : ℝ) (w : (Fin 1 ⊕ Fin 3) →₀ ℕ) (hw : w ≠ 0),
      repJetGaugeGroupI (expUnitary a w hw) V = V) :
    V ∈ Algebra.adjoin ℝ (fieldStrengthDeriv.uncurry.uncurry '' Set.univ) := by
  have htrans : ∀ (g₀ : JetGenerators) (r : ℝ),
      MvPolynomial.aeval (fun g => MvPolynomial.X g +
        MvPolynomial.C (if JetGenerators.canon g = JetGenerators.canon g₀ then r
          else (0 : ℝ)))
        (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis V) =
        SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis V := by
    intro g₀ r
    obtain ⟨s₀, ν₀⟩ := g₀
    have hne : Multiset.toFinsupp (s₀ + {ν₀}) ≠ 0 := by
      intro h
      have h0 : s₀ + {ν₀} = 0 :=
        Multiset.toFinsupp.injective (by rw [h, Multiset.toFinsupp_zero])
      simp at h0
    have hconj := equivMvPolynomial_repJetGaugeGroupI
      (expUnitary (-r / (∏ ρ, Nat.factorial ((Multiset.toFinsupp (s₀ + {ν₀})) ρ)))
        (Multiset.toFinsupp (s₀ + {ν₀})) hne) V
    rw [hV _ _ _] at hconj
    have hfun : (fun g => MvPolynomial.X g + MvPolynomial.C
        (mcShift (expUnitary
            (-r / (∏ ρ, Nat.factorial ((Multiset.toFinsupp (s₀ + {ν₀})) ρ)))
            (Multiset.toFinsupp (s₀ + {ν₀})) hne)
          (JetComponentSpace.basis g))) =
        fun g => MvPolynomial.X g + MvPolynomial.C
          (if JetGenerators.canon g = JetGenerators.canon (JetGenerators.dB s₀ ν₀)
            then r else (0 : ℝ)) := by
      funext g
      obtain ⟨s, ν⟩ := g
      rw [mcShift_expUnitary (s₀ + {ν₀}) hne (-r) s ν, neg_neg]
      have hiff : (s + {ν} = s₀ + {ν₀}) ↔
          (JetGenerators.canon (JetGenerators.dB s ν) =
            JetGenerators.canon (JetGenerators.dB s₀ ν₀)) := by
        rw [JetGenerators.canon_eq_canon_iff]
        simp
      rw [if_congr hiff rfl rfl]
    rw [hfun] at hconj
    exact hconj.symm
  have hmem := MvPolynomial.mem_adjoin_range_X_sub_X_of_forall_aeval_add_eq
    JetGenerators.canon JetGenerators.canon_canon
    (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis V) htrans
  have hVmem : V ∈ (Algebra.adjoin ℝ (Set.range fun g =>
      (MvPolynomial.X g - MvPolynomial.X (JetGenerators.canon g) :
        MvPolynomial JetGenerators ℝ))).map
      (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis).symm.toAlgHom :=
    Subalgebra.mem_map.mpr ⟨_, hmem, AlgEquiv.symm_apply_apply _ _⟩
  rw [AlgHom.map_adjoin] at hVmem
  refine Algebra.adjoin_le ?_ hVmem
  rintro x ⟨_, ⟨g, rfl⟩, rfl⟩
  have hsymm : (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis).symm.toAlgHom
      (MvPolynomial.X g - MvPolynomial.X (JetGenerators.canon g)) =
      ofGenerator g - ofGenerator (JetGenerators.canon g) := by
    show (SymmetricAlgebra.equivMvPolynomial JetComponentSpace.basis).symm
      (MvPolynomial.X g - MvPolynomial.X (JetGenerators.canon g)) = _
    rw [map_sub, SymmetricAlgebra.equivMvPolynomial_symm_X,
      SymmetricAlgebra.equivMvPolynomial_symm_X]
    rfl
  rw [hsymm]
  exact ofGenerator_sub_ofGenerator_canon_mem g

/-- The coordinate retractions of the complexified jet algebra along the real
  basis `{1, I}` of `ℂ`. -/
private noncomputable def complexCoordAux (i : Fin 2) :
    ℂ ⊗[ℝ] JetAlgebra →ₗ[ℝ] JetAlgebra :=
  TensorProduct.lift ((LinearMap.lsmul ℝ JetAlgebra).comp (Complex.basisOneI.coord i))

private lemma complexCoordAux_tmul (i : Fin 2) (z : ℂ) (b : JetAlgebra) :
    complexCoordAux i (z ⊗ₜ[ℝ] b) = Complex.basisOneI.repr z i • b := by
  simp [complexCoordAux, Module.Basis.coord_apply]

set_option maxHeartbeats 1000000 in
/-- The complexified invariance direction: an element of the complexified B-boson
  jet algebra fixed by the complexified action of the `expUnitary` translation
  family lies in the complexified field-strength subalgebra. -/
lemma mem_adjoin_of_forall_expUnitary_complex (x : ℂ ⊗[ℝ] JetAlgebra)
    (hx : ∀ (a : ℝ) (w : (Fin 1 ⊕ Fin 3) →₀ ℕ) (hw : w ≠ 0),
      complexRepJetGaugeGroupI (expUnitary a w hw) x = x) :
    x ∈ Algebra.adjoin ℂ (Set.range fun p :
        Multiset (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) =>
      ((1 : ℂ) ⊗ₜ[ℝ] fieldStrengthDeriv p.1 p.2.1 p.2.2 : ℂ ⊗[ℝ] JetAlgebra)) := by
  classical
  have hrtmul : ∀ (i : Fin 2) (z : ℂ) (b : JetAlgebra),
      complexCoordAux i (z ⊗ₜ[ℝ] b) = Complex.basisOneI.repr z i • b :=
    complexCoordAux_tmul
  have h1 : ∀ y : ℂ ⊗[ℝ] JetAlgebra,
      y = (1 : ℂ) ⊗ₜ[ℝ] complexCoordAux 0 y + Complex.I ⊗ₜ[ℝ] complexCoordAux 1 y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb =>
      rw [map_add, map_add, TensorProduct.tmul_add, TensorProduct.tmul_add]
      calc a + b = ((1 : ℂ) ⊗ₜ[ℝ] complexCoordAux 0 a + Complex.I ⊗ₜ[ℝ] complexCoordAux 1 a) +
            ((1 : ℂ) ⊗ₜ[ℝ] complexCoordAux 0 b + Complex.I ⊗ₜ[ℝ] complexCoordAux 1 b) := by rw [← ha, ← hb]
        _ = _ := by abel
    | tmul z b =>
      rw [hrtmul, hrtmul, TensorProduct.tmul_smul, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', TensorProduct.smul_tmul', ← TensorProduct.add_tmul]
      congr 1
      have hz := Complex.re_add_im z
      simp only [Complex.coe_basisOneI_repr, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [show z.re • (1 : ℂ) = (z.re : ℂ) from by simp [Complex.real_smul],
        show z.im • Complex.I = (z.im : ℂ) * Complex.I from by rw [Complex.real_smul]]
      exact hz.symm
  have h2 : ∀ (U : JetGaugeGroupI) (i : Fin 2) (y : ℂ ⊗[ℝ] JetAlgebra),
      complexCoordAux i (complexRepJetGaugeGroupI U y) =
        repJetGaugeGroupI U (complexCoordAux i y) := by
    intro U i y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul z b =>
      simp only [complexRepJetGaugeGroupI_tmul]
      rw [hrtmul, hrtmul]
      exact ((repJetGaugeGroupI U).map_smul _ _).symm
  have hmem : ∀ i : Fin 2, complexCoordAux i x ∈ Algebra.adjoin ℝ
      (fieldStrengthDeriv.uncurry.uncurry '' Set.univ) := by
    intro i
    refine mem_adjoin_of_forall_expUnitary (complexCoordAux i x) fun a w hw => ?_
    rw [← h2, hx a w hw]
  have hinc : ∀ b ∈ Algebra.adjoin ℝ (fieldStrengthDeriv.uncurry.uncurry '' Set.univ),
      ((1 : ℂ) ⊗ₜ[ℝ] b : ℂ ⊗[ℝ] JetAlgebra) ∈ Algebra.adjoin ℂ (Set.range fun p :
          Multiset (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) =>
        ((1 : ℂ) ⊗ₜ[ℝ] fieldStrengthDeriv p.1 p.2.1 p.2.2 : ℂ ⊗[ℝ] JetAlgebra)) := by
    intro b hb
    induction hb using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨⟨⟨s, μ⟩, ν⟩, -, rfl⟩ := hy
      exact Algebra.subset_adjoin ⟨(s, μ, ν), rfl⟩
    | algebraMap t =>
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
        ← IsScalarTower.algebraMap_smul ℂ t
          ((1 : ℂ) ⊗ₜ[ℝ] (1 : JetAlgebra) : ℂ ⊗[ℝ] JetAlgebra)]
      exact Subalgebra.smul_mem _ (one_mem _) _
    | add y z hy hz ihy ihz =>
      rw [TensorProduct.tmul_add]
      exact add_mem ihy ihz
    | mul y z hy hz ihy ihz =>
      rw [show ((1 : ℂ) ⊗ₜ[ℝ] (y * z) : ℂ ⊗[ℝ] JetAlgebra) =
          ((1 : ℂ) ⊗ₜ[ℝ] y) * ((1 : ℂ) ⊗ₜ[ℝ] z) from by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]]
      exact mul_mem ihy ihz
  rw [h1 x]
  refine add_mem (hinc _ (hmem 0)) ?_
  rw [show (Complex.I ⊗ₜ[ℝ] complexCoordAux 1 x : ℂ ⊗[ℝ] JetAlgebra) =
      Complex.I • ((1 : ℂ) ⊗ₜ[ℝ] complexCoordAux 1 x) from by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
  exact Subalgebra.smul_mem _ (hinc _ (hmem 1)) _

/-- An EFT lagrangian with field content consisting only of
  a `B` bosons is invariant under the full gauge group if and only if
  it can be written in terms of the field strength and derivatives thereof. -/
lemma repJetGaugeGroupI_apply_eq_self_iff_mem (V : JetAlgebra) :
  (∀ U, repJetGaugeGroupI U V = V) ↔ V ∈ Algebra.adjoin ℝ
    (fieldStrengthDeriv.uncurry.uncurry '' Set.univ) := by
  constructor
  · intro hV
    exact mem_adjoin_of_forall_expUnitary V fun a w hw => hV _
  · intro hVmem U
    induction hVmem using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨⟨⟨s', μ⟩, ν⟩, -, rfl⟩ := hx
      exact repJetGaugeGroupI_fieldStrengthDeriv U s' μ ν
    | algebraMap r => exact repJetGaugeGroupI_algebraMap U r
    | add x y hx hy ihx ihy => rw [map_add, ihx, ihy]
    | mul x y hx hy ihx ihy => rw [repJetGaugeGroupI_mul, ihx, ihy]

/-!

## Mass weight scaling

-/


/-- The mass-dimension scaling on the jet algebra of the B boson: the algebra
  map multiplying each generator by `c ^ w`, where `w` is twice its mass
  dimension. -/
noncomputable def massWeightScaleReal (c : ℝ) : JetAlgebra →ₐ[ℝ] JetAlgebra :=
  SymmetricAlgebra.lift
    ((SymmetricAlgebra.ι ℝ JetComponentSpace) ∘ₗ JetComponentSpace.massWeightScale c)

/-- Each generator scales by `c` to the power of its mass weight. -/
@[simp]
lemma massWeightScaleReal_ofGenerator (c : ℝ) (j : JetGenerators) :
    massWeightScaleReal c (ofGenerator j) = c ^ j.massWeight • ofGenerator j := by
  rw [ofGenerator, massWeightScaleReal, SymmetricAlgebra.lift_ι_apply]
  simp only [LinearMap.coe_comp, Function.comp_apply,
    JetComponentSpace.massWeightScale_basis, map_smul]

/-- The mass-dimension scaling on the complexified jet algebra of the B boson:
  the `ℂ`-algebra map multiplying each generator by `c ^ w`, where `w` is twice
  its mass dimension. -/
noncomputable def massWeightScale (c : ℂ) :
    ℂ ⊗[ℝ] JetAlgebra →ₐ[ℂ] ℂ ⊗[ℝ] JetAlgebra :=
  Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft
    (SymmetricAlgebra.lift (JetComponentSpace.basis.constr ℝ fun j =>
      c ^ j.massWeight • ((1 : ℂ) ⊗ₜ[ℝ] ofGenerator j)))
    fun _ _ => Commute.all _ _

/-- Each complexified generator scales by `c` to the power of its mass
  weight. -/
@[simp]
lemma massWeightScale_tmul_ofGenerator (c z : ℂ) (j : JetGenerators) :
    massWeightScale c (z ⊗ₜ[ℝ] ofGenerator j) =
      c ^ j.massWeight • (z ⊗ₜ[ℝ] ofGenerator j) := by
  rw [massWeightScale, Algebra.TensorProduct.lift_tmul, ofGenerator,
    SymmetricAlgebra.lift_ι_apply, Module.Basis.constr_basis, mul_smul_comm]
  congr 1
  rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul]
  rfl

set_option maxHeartbeats 1000000 in
/-- The complexified total derivative raises the mass weight by two: the scaling
  and the derivative commute up to `c ^ 2`. -/
lemma massWeightScale_jetDeriv_baseChange (c : ℂ) (μ : Fin 1 ⊕ Fin 3)
    (x : ℂ ⊗[ℝ] JetAlgebra) :
    massWeightScale c (LinearMap.baseChange ℂ (jetDeriv μ) x) =
      c ^ 2 • LinearMap.baseChange ℂ (jetDeriv μ) (massWeightScale c x) := by
  have hm : ∀ a b : ℂ ⊗[ℝ] JetAlgebra, massWeightScale c (a * b) =
      massWeightScale c a * massWeightScale c b := fun a b => map_mul _ a b
  have hone : ∀ b : JetAlgebra,
      massWeightScale c ((1 : ℂ) ⊗ₜ[ℝ] jetDeriv μ b) =
        c ^ 2 • LinearMap.baseChange ℂ (jetDeriv μ)
          (massWeightScale c ((1 : ℂ) ⊗ₜ[ℝ] b)) := by
    intro b
    induction b using SymmetricAlgebra.induction with
    | algebraMap r =>
      have hd : jetDeriv μ (algebraMap ℝ JetAlgebra r) = 0 := by
        rw [Algebra.algebraMap_eq_smul_one, map_smul, jetDeriv_one, smul_zero]
      have h1 : (1 : ℂ) ⊗ₜ[ℝ] algebraMap ℝ JetAlgebra r =
          algebraMap ℂ (ℂ ⊗[ℝ] JetAlgebra) (algebraMap ℝ ℂ r) := by
        rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
          ← algebraMap_smul (R := ℝ) ℂ r ((1 : ℂ) ⊗ₜ[ℝ] (1 : JetAlgebra)),
          Algebra.algebraMap_eq_smul_one (R := ℂ) (A := ℂ ⊗[ℝ] JetAlgebra)]
        rfl
      have hD1 : LinearMap.baseChange ℂ (jetDeriv μ)
          ((1 : ℂ) ⊗ₜ[ℝ] algebraMap ℝ JetAlgebra r) = 0 := by
        rw [LinearMap.baseChange_tmul, hd, TensorProduct.tmul_zero]
      rw [hd, TensorProduct.tmul_zero, map_zero, h1, AlgHom.commutes,
        show algebraMap ℂ (ℂ ⊗[ℝ] JetAlgebra) (algebraMap ℝ ℂ r) =
          (1 : ℂ) ⊗ₜ[ℝ] algebraMap ℝ JetAlgebra r from h1.symm, hD1, smul_zero]
    | ι v =>
      have h : ((massWeightScale c).toLinearMap.restrictScalars ℝ) ∘ₗ
          (TensorProduct.mk ℝ ℂ JetAlgebra 1) ∘ₗ (jetDeriv μ) ∘ₗ
            (SymmetricAlgebra.ι ℝ JetComponentSpace) =
          c ^ 2 • (((LinearMap.baseChange ℂ (jetDeriv μ)).restrictScalars ℝ) ∘ₗ
            ((massWeightScale c).toLinearMap.restrictScalars ℝ) ∘ₗ
            (TensorProduct.mk ℝ ℂ JetAlgebra 1) ∘ₗ
            (SymmetricAlgebra.ι ℝ JetComponentSpace)) := by
        refine JetComponentSpace.basis.ext fun g => ?_
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
          LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply,
          TensorProduct.mk_apply]
        rw [show SymmetricAlgebra.ι ℝ JetComponentSpace (JetComponentSpace.basis g) =
            ofGenerator g from rfl, jetDeriv_ofGenerator,
          massWeightScale_tmul_ofGenerator, massWeightScale_tmul_ofGenerator,
          map_smul, jetDeriv_baseChange_ofGenerator, JetGenerators.massWeight_shift,
          smul_smul, ← pow_add]
        congr 1
        ring
      exact DFunLike.congr_fun h v
    | mul a b ha hb =>
      have h₁ : (1 : ℂ) ⊗ₜ[ℝ] (jetDeriv μ a * b) =
          ((1 : ℂ) ⊗ₜ[ℝ] jetDeriv μ a) * ((1 : ℂ) ⊗ₜ[ℝ] b) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      have h₂ : (1 : ℂ) ⊗ₜ[ℝ] (a * jetDeriv μ b) =
          ((1 : ℂ) ⊗ₜ[ℝ] a) * ((1 : ℂ) ⊗ₜ[ℝ] jetDeriv μ b) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      have h₃ : (1 : ℂ) ⊗ₜ[ℝ] (a * b) =
          ((1 : ℂ) ⊗ₜ[ℝ] a) * ((1 : ℂ) ⊗ₜ[ℝ] b) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      calc massWeightScale c ((1 : ℂ) ⊗ₜ[ℝ] jetDeriv μ (a * b))
          = massWeightScale c ((1 : ℂ) ⊗ₜ[ℝ] (jetDeriv μ a * b) +
              (1 : ℂ) ⊗ₜ[ℝ] (a * jetDeriv μ b)) := by
            rw [jetDeriv_mul, TensorProduct.tmul_add]
        _ = massWeightScale c ((1 : ℂ) ⊗ₜ[ℝ] jetDeriv μ a) *
              massWeightScale c ((1 : ℂ) ⊗ₜ[ℝ] b) +
            massWeightScale c ((1 : ℂ) ⊗ₜ[ℝ] a) *
              massWeightScale c ((1 : ℂ) ⊗ₜ[ℝ] jetDeriv μ b) := by
            rw [map_add, h₁, h₂, hm, hm]
        _ = (c ^ 2 • LinearMap.baseChange ℂ (jetDeriv μ)
              (massWeightScale c ((1 : ℂ) ⊗ₜ[ℝ] a))) *
              massWeightScale c ((1 : ℂ) ⊗ₜ[ℝ] b) +
            massWeightScale c ((1 : ℂ) ⊗ₜ[ℝ] a) *
              (c ^ 2 • LinearMap.baseChange ℂ (jetDeriv μ)
                (massWeightScale c ((1 : ℂ) ⊗ₜ[ℝ] b))) := by
            rw [ha, hb]
        _ = c ^ 2 • (LinearMap.baseChange ℂ (jetDeriv μ)
              (massWeightScale c ((1 : ℂ) ⊗ₜ[ℝ] a)) *
              massWeightScale c ((1 : ℂ) ⊗ₜ[ℝ] b) +
            massWeightScale c ((1 : ℂ) ⊗ₜ[ℝ] a) *
              LinearMap.baseChange ℂ (jetDeriv μ)
                (massWeightScale c ((1 : ℂ) ⊗ₜ[ℝ] b))) := by
            rw [smul_mul_assoc, mul_smul_comm, smul_add]
        _ = c ^ 2 • LinearMap.baseChange ℂ (jetDeriv μ)
              (massWeightScale c ((1 : ℂ) ⊗ₜ[ℝ] a) *
                massWeightScale c ((1 : ℂ) ⊗ₜ[ℝ] b)) := by
            rw [jetDeriv_baseChange_mul]
        _ = c ^ 2 • LinearMap.baseChange ℂ (jetDeriv μ)
              (massWeightScale c ((1 : ℂ) ⊗ₜ[ℝ] (a * b))) := by
            rw [h₃, hm]
    | add a b ha hb =>
      simp only [map_add, TensorProduct.tmul_add, ha, hb, smul_add]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb, smul_add]
  | tmul z b =>
    have hz₁ : z ⊗ₜ[ℝ] jetDeriv μ b = z • ((1 : ℂ) ⊗ₜ[ℝ] jetDeriv μ b) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have hz₂ : massWeightScale c (z ⊗ₜ[ℝ] b) =
        z • massWeightScale c ((1 : ℂ) ⊗ₜ[ℝ] b) := by
      rw [show z ⊗ₜ[ℝ] b = z • ((1 : ℂ) ⊗ₜ[ℝ] b) from by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
      exact map_smul (massWeightScale c) z _
    calc massWeightScale c (LinearMap.baseChange ℂ (jetDeriv μ) (z ⊗ₜ[ℝ] b))
        = massWeightScale c (z • ((1 : ℂ) ⊗ₜ[ℝ] jetDeriv μ b)) := by
          rw [LinearMap.baseChange_tmul, hz₁]
      _ = z • massWeightScale c ((1 : ℂ) ⊗ₜ[ℝ] jetDeriv μ b) :=
          map_smul (massWeightScale c) z _
      _ = z • (c ^ 2 • LinearMap.baseChange ℂ (jetDeriv μ)
            (massWeightScale c ((1 : ℂ) ⊗ₜ[ℝ] b))) := by rw [hone b]
      _ = c ^ 2 • (z • LinearMap.baseChange ℂ (jetDeriv μ)
            (massWeightScale c ((1 : ℂ) ⊗ₜ[ℝ] b))) := smul_comm z _ _
      _ = c ^ 2 • LinearMap.baseChange ℂ (jetDeriv μ)
            (z • massWeightScale c ((1 : ℂ) ⊗ₜ[ℝ] b)) := by
          rw [(LinearMap.baseChange ℂ (jetDeriv μ)).map_smul]
      _ = c ^ 2 • LinearMap.baseChange ℂ (jetDeriv μ)
            (massWeightScale c (z ⊗ₜ[ℝ] b)) :=
          congrArg (fun y => c ^ 2 •
            LinearMap.baseChange ℂ (jetDeriv μ) y) hz₂.symm

end JetAlgebra

/-!

## Lorentz transformation laws of the B-boson jet coordinates

-/

/-- The multiset basis of the real dual derivative slots at a singleton index. -/
lemma dualRealJetAlgebraBasis_singleton (μ : Fin 1 ⊕ Fin 3) :
    LagrangianTheory.dualRealJetAlgebraBasis ({μ} : Multiset (Fin 1 ⊕ Fin 3)) =
      SymmetricAlgebra.ι ℝ (Module.Dual ℝ Lorentz.CoVector)
        (Lorentz.CoVector.basis.dualBasis μ) := by
  have h : (MvPolynomial.basisMonomials (Fin 1 ⊕ Fin 3) ℝ) (Finsupp.single μ 1) =
      MvPolynomial.X μ := rfl
  rw [LagrangianTheory.dualRealJetAlgebraBasis, Module.Basis.reindex_apply,
    Equiv.symm_symm,
    show Multiset.toFinsupp.toEquiv ({μ} : Multiset (Fin 1 ⊕ Fin 3)) =
      Finsupp.single μ 1 by simp,
    Module.Basis.symmetricAlgebra, Module.Basis.map_apply, h]
  simp

/-- The degree scaling multiplies the multiset basis vector at `s` by
  `t ^ |s|`. -/
lemma gradeScale_dualRealJetAlgebraBasis (t : ℝ) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    DerivAlgebraReal.gradeScale t (LagrangianTheory.dualRealJetAlgebraBasis s) =
      t ^ Multiset.card s • LagrangianTheory.dualRealJetAlgebraBasis s := by
  induction s using Multiset.induction_on with
  | empty =>
    rw [show LagrangianTheory.dualRealJetAlgebraBasis
        (0 : Multiset (Fin 1 ⊕ Fin 3)) = 1 from dualRealJetAlgebraBasis_nil, map_one]
    simp
  | cons a s ih =>
    rw [← Multiset.singleton_add, ← dualRealJetAlgebraBasis_mul, map_mul, ih,
      dualRealJetAlgebraBasis_singleton, DerivAlgebraReal.gradeScale_ι,
      smul_mul_smul_comm, ← _root_.pow_succ', ← dualRealJetAlgebraBasis_singleton,
      dualRealJetAlgebraBasis_mul, Multiset.singleton_add, Multiset.card_cons]

/-- The mass-dimension scaling commutes with the Lorentz action on the B-boson
  component space: the Lorentz action preserves the derivative degree. -/
lemma JetComponentSpace.massWeightScale_repLorentzGroup (c : ℝ) (Λ : SL(2,ℂ)) :
    JetComponentSpace.massWeightScale c ∘ₗ JetComponentSpace.repLorentzGroup Λ =
      JetComponentSpace.repLorentzGroup Λ ∘ₗ JetComponentSpace.massWeightScale c := by
  have hfact : JetComponentSpace.massWeightScale c =
      TensorProduct.map (DerivAlgebraReal.gradeScale (c ^ 2)).toLinearMap
        (c ^ 2 • LinearMap.id) := by
    refine JetComponentSpace.basis.ext fun j => ?_
    cases j with
    | dB s ν =>
      have hscal : (c : ℝ) ^ (JetGenerators.dB s ν).massWeight =
          c ^ 2 * (c ^ 2) ^ Multiset.card s := by
        show c ^ (2 * (1 + Multiset.card s)) = _
        rw [pow_mul]
        ring
      rw [JetComponentSpace.massWeightScale_basis, hscal]
      simp only [jetComponentSpace_basis_dB, TensorProduct.map_tmul,
        AlgHom.toLinearMap_apply, LinearMap.smul_apply, LinearMap.id_apply,
        gradeScale_dualRealJetAlgebraBasis, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', smul_smul]
  have hA : (DerivAlgebraReal.gradeScale (c ^ 2)).toLinearMap ∘ₗ
      DerivAlgebraReal.repLorentzGroup Λ =
      (DerivAlgebraReal.repLorentzGroup Λ :
        DerivAlgebraReal →ₗ[ℝ] DerivAlgebraReal) ∘ₗ
        (DerivAlgebraReal.gradeScale (c ^ 2)).toLinearMap :=
    LinearMap.ext fun a => DerivAlgebraReal.gradeScale_repLorentzGroup (c ^ 2) Λ a
  have hB : (c ^ 2 • (LinearMap.id : Module.End ℝ (Module.Dual ℝ BBoson))) ∘ₗ
      BBoson.repLorentzGroup.dual Λ =
      BBoson.repLorentzGroup.dual Λ ∘ₗ (c ^ 2 • LinearMap.id) := by
    rw [LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp,
      LinearMap.comp_id]
  rw [hfact, show JetComponentSpace.repLorentzGroup Λ =
      TensorProduct.map (DerivAlgebraReal.repLorentzGroup Λ)
        (BBoson.repLorentzGroup.dual Λ) from rfl,
    ← TensorProduct.map_comp, ← TensorProduct.map_comp, hA, hB]

set_option maxHeartbeats 1000000 in
/-- The Lorentz action on the first-order B-boson jet coordinates: both indices
  transform contravariantly, by the columns of the Lorentz matrix. -/
lemma JetComponentSpace.repLorentzGroup_basis_dB_singleton (Λ : SL(2,ℂ))
    (μ ν : Fin 1 ⊕ Fin 3) :
    JetComponentSpace.repLorentzGroup Λ (JetComponentSpace.basis (.dB {μ} ν)) =
      ∑ a, ∑ b, ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ *
        (Lorentz.SL2C.toLorentzGroup Λ).1 b ν) •
        JetComponentSpace.basis (.dB {a} b) := by
  have happ : JetComponentSpace.repLorentzGroup Λ
      (LagrangianTheory.dualRealJetAlgebraBasis {μ} ⊗ₜ[ℝ] BBoson.basis.dualBasis ν) =
      (DerivAlgebraReal.repLorentzGroup Λ
        (LagrangianTheory.dualRealJetAlgebraBasis {μ})) ⊗ₜ[ℝ]
      (BBoson.repLorentzGroup.dual Λ (BBoson.basis.dualBasis ν)) := rfl
  rw [jetComponentSpace_basis_dB, happ, dualRealJetAlgebraBasis_singleton,
    DerivAlgebraReal.repLorentzGroup_apply_ι, Lorentz.CoVector.sl2Rep_dual_dualBasis,
    BBoson.repLorentzGroup_dual_dualBasis]
  simp only [map_sum, map_smul, TensorProduct.sum_tmul, TensorProduct.tmul_sum,
    TensorProduct.smul_tmul', TensorProduct.tmul_smul, Finset.smul_sum, smul_smul,
    jetComponentSpace_basis_dB, dualRealJetAlgebraBasis_singleton]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 2
  ring

set_option maxHeartbeats 2000000 in
/-- The Lorentz action on the two-derivative-index B-boson jet coordinates:
  all three indices transform contravariantly, by the columns of the Lorentz
  matrix. -/
lemma JetComponentSpace.repLorentzGroup_basis_dB_pair
    (Λ : SL(2,ℂ)) (ρ μ ν : Fin 1 ⊕ Fin 3) :
    BBoson.JetComponentSpace.repLorentzGroup Λ
      (BBoson.JetComponentSpace.basis (.dB {ρ, μ} ν)) =
      ∑ r, ∑ a, ∑ b, ((Lorentz.SL2C.toLorentzGroup Λ).1 r ρ *
        ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ *
          (Lorentz.SL2C.toLorentzGroup Λ).1 b ν)) •
        BBoson.JetComponentSpace.basis (.dB {r, a} b) := by
  have hpair : ∀ x y : Fin 1 ⊕ Fin 3,
      LagrangianTheory.dualRealJetAlgebraBasis ({x, y} : Multiset (Fin 1 ⊕ Fin 3)) =
        SymmetricAlgebra.ι ℝ (Module.Dual ℝ Lorentz.CoVector)
            (Lorentz.CoVector.basis.dualBasis x) *
          SymmetricAlgebra.ι ℝ (Module.Dual ℝ Lorentz.CoVector)
            (Lorentz.CoVector.basis.dualBasis y) := fun x y => by
    rw [← BBoson.dualRealJetAlgebraBasis_singleton,
      ← BBoson.dualRealJetAlgebraBasis_singleton,
      BBoson.dualRealJetAlgebraBasis_mul, Multiset.singleton_add,
      ← Multiset.insert_eq_cons]
  have hmul : ∀ x y : DerivAlgebraReal,
      DerivAlgebraReal.repLorentzGroup Λ (x * y) =
        DerivAlgebraReal.repLorentzGroup Λ x *
          DerivAlgebraReal.repLorentzGroup Λ y := fun x y =>
    map_mul (SymmetricAlgebra.lift (SymmetricAlgebra.ι ℝ _ ∘ₗ
      Lorentz.CoVector.sl2Rep.dual Λ)) x y
  have happ : BBoson.JetComponentSpace.repLorentzGroup Λ
      (LagrangianTheory.dualRealJetAlgebraBasis {ρ, μ} ⊗ₜ[ℝ]
        StandardModel.BBoson.basis.dualBasis ν) =
      (DerivAlgebraReal.repLorentzGroup Λ
        (LagrangianTheory.dualRealJetAlgebraBasis {ρ, μ})) ⊗ₜ[ℝ]
      (BBoson.repLorentzGroup.dual Λ
        (StandardModel.BBoson.basis.dualBasis ν)) := rfl
  rw [BBoson.jetComponentSpace_basis_dB, happ, hpair, hmul,
    DerivAlgebraReal.repLorentzGroup_apply_ι,
    DerivAlgebraReal.repLorentzGroup_apply_ι,
    Lorentz.CoVector.sl2Rep_dual_dualBasis, Lorentz.CoVector.sl2Rep_dual_dualBasis,
    BBoson.repLorentzGroup_dual_dualBasis]
  simp only [map_sum, map_smul, Finset.sum_mul, Finset.mul_sum,
    smul_mul_smul_comm, TensorProduct.sum_tmul, TensorProduct.tmul_sum,
    ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, Finset.smul_sum,
    smul_smul, BBoson.jetComponentSpace_basis_dB, hpair]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, j]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => ?_
  module

set_option maxHeartbeats 2000000 in
/-- The Lorentz action on the three-derivative-index B-boson jet coordinates:
  all four indices transform contravariantly, by the columns of the Lorentz
  matrix. -/
lemma JetComponentSpace.repLorentzGroup_basis_dB_triple
    (Λ : SL(2,ℂ)) (ρ τ μ ν : Fin 1 ⊕ Fin 3) :
    BBoson.JetComponentSpace.repLorentzGroup Λ
      (BBoson.JetComponentSpace.basis (.dB {ρ, τ, μ} ν)) =
      ∑ r, ∑ s, ∑ a, ∑ b, ((Lorentz.SL2C.toLorentzGroup Λ).1 r ρ *
        ((Lorentz.SL2C.toLorentzGroup Λ).1 s τ *
          ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ *
          (Lorentz.SL2C.toLorentzGroup Λ).1 b ν))) •
        BBoson.JetComponentSpace.basis (.dB {r, s, a} b) := by
  have htriple : ∀ x y z : Fin 1 ⊕ Fin 3,
      LagrangianTheory.dualRealJetAlgebraBasis ({x, y, z} : Multiset (Fin 1 ⊕ Fin 3)) =
        SymmetricAlgebra.ι ℝ (Module.Dual ℝ Lorentz.CoVector)
            (Lorentz.CoVector.basis.dualBasis x) *
          (SymmetricAlgebra.ι ℝ (Module.Dual ℝ Lorentz.CoVector)
            (Lorentz.CoVector.basis.dualBasis y) *
           SymmetricAlgebra.ι ℝ (Module.Dual ℝ Lorentz.CoVector)
            (Lorentz.CoVector.basis.dualBasis z)) := fun x y z => by
    rw [← BBoson.dualRealJetAlgebraBasis_singleton,
      ← BBoson.dualRealJetAlgebraBasis_singleton,
      ← BBoson.dualRealJetAlgebraBasis_singleton,
      BBoson.dualRealJetAlgebraBasis_mul, BBoson.dualRealJetAlgebraBasis_mul,
      Multiset.singleton_add, Multiset.singleton_add, ← Multiset.insert_eq_cons,
      ← Multiset.insert_eq_cons]
  have hmul : ∀ x y : DerivAlgebraReal,
      DerivAlgebraReal.repLorentzGroup Λ (x * y) =
        DerivAlgebraReal.repLorentzGroup Λ x *
          DerivAlgebraReal.repLorentzGroup Λ y := fun x y =>
    map_mul (SymmetricAlgebra.lift (SymmetricAlgebra.ι ℝ _ ∘ₗ
      Lorentz.CoVector.sl2Rep.dual Λ)) x y
  have happ : BBoson.JetComponentSpace.repLorentzGroup Λ
      (LagrangianTheory.dualRealJetAlgebraBasis {ρ, τ, μ} ⊗ₜ[ℝ]
        StandardModel.BBoson.basis.dualBasis ν) =
      (DerivAlgebraReal.repLorentzGroup Λ
        (LagrangianTheory.dualRealJetAlgebraBasis {ρ, τ, μ})) ⊗ₜ[ℝ]
      (BBoson.repLorentzGroup.dual Λ
        (StandardModel.BBoson.basis.dualBasis ν)) := rfl
  rw [BBoson.jetComponentSpace_basis_dB, happ, htriple, hmul, hmul,
    DerivAlgebraReal.repLorentzGroup_apply_ι,
    DerivAlgebraReal.repLorentzGroup_apply_ι,
    DerivAlgebraReal.repLorentzGroup_apply_ι,
    Lorentz.CoVector.sl2Rep_dual_dualBasis, Lorentz.CoVector.sl2Rep_dual_dualBasis,
    Lorentz.CoVector.sl2Rep_dual_dualBasis,
    BBoson.repLorentzGroup_dual_dualBasis]
  simp only [map_sum, map_smul, Finset.sum_mul, Finset.mul_sum,
    smul_mul_smul_comm, TensorProduct.sum_tmul, TensorProduct.tmul_sum,
    ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, Finset.smul_sum,
    smul_smul, BBoson.jetComponentSpace_basis_dB, htriple]
  conv_lhs => enter [2, i, 2, j]; rw [Finset.sum_comm]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, i, 2, j]; rw [Finset.sum_comm]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  conv_lhs => enter [2, i, 2, j]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  module

namespace JetAlgebra


set_option maxHeartbeats 1000000 in
/-- The zeroth-order field strength transforms as an antisymmetric two-tensor:
  the Lorentz action preserves the span of the field strengths. -/
lemma repLorentzGroup_fieldStrengthDeriv_nil (Λ : SL(2,ℂ)) (μ ν : Fin 1 ⊕ Fin 3) :
    repLorentzGroup Λ (fieldStrengthDeriv {} μ ν) =
      ∑ a, ∑ b, ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ *
        (Lorentz.SL2C.toLorentzGroup Λ).1 b ν) • fieldStrengthDeriv {} a b := by
  have hFS : ∀ a b : Fin 1 ⊕ Fin 3, fieldStrengthDeriv ({} : Multiset _) a b =
      ofGenerator (JetGenerators.dB {a} b) -
        ofGenerator (JetGenerators.dB {b} a) := by
    intro a b
    rw [fieldStrengthDeriv,
      show ({} : Multiset (Fin 1 ⊕ Fin 3)) + {a} = {a} from by simp,
      show ({} : Multiset (Fin 1 ⊕ Fin 3)) + {b} = {b} from by simp]
  simp only [hFS]
  rw [map_sub, ofGenerator, ofGenerator, repLorentzGroup_apply_ι,
    repLorentzGroup_apply_ι, JetComponentSpace.repLorentzGroup_basis_dB_singleton,
    JetComponentSpace.repLorentzGroup_basis_dB_singleton]
  simp only [map_sum, map_smul, smul_sub, Finset.sum_sub_distrib, ofGenerator]
  congr 1
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  ring

/-- The transformation of the complexified zeroth-order field strength. -/
lemma complexRepLorentzGroup_one_tmul_fieldStrengthDeriv_nil (Λ : SL(2,ℂ))
    (μ ν : Fin 1 ⊕ Fin 3) :
    complexRepLorentzGroup Λ ((1 : ℂ) ⊗ₜ[ℝ] fieldStrengthDeriv {} μ ν) =
      ∑ a, ∑ b, ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ *
        (Lorentz.SL2C.toLorentzGroup Λ).1 b ν) •
        ((1 : ℂ) ⊗ₜ[ℝ] fieldStrengthDeriv {} a b) := by
  rw [show complexRepLorentzGroup Λ ((1 : ℂ) ⊗ₜ[ℝ] fieldStrengthDeriv {} μ ν) =
      (1 : ℂ) ⊗ₜ[ℝ] repLorentzGroup Λ (fieldStrengthDeriv {} μ ν) from rfl,
    repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul]

/-- The mass-dimension scaling commutes with the Lorentz action on the B-boson
  jet algebra. -/
lemma massWeightScaleReal_repLorentzGroup (c : ℝ) (Λ : SL(2,ℂ)) (x : JetAlgebra) :
    massWeightScaleReal c (repLorentzGroup Λ x) =
      repLorentzGroup Λ (massWeightScaleReal c x) := by
  have h1 : ∀ w, massWeightScaleReal c (SymmetricAlgebra.ι ℝ JetComponentSpace w) =
      SymmetricAlgebra.ι ℝ JetComponentSpace
        (JetComponentSpace.massWeightScale c w) := fun w => by
    rw [massWeightScaleReal, SymmetricAlgebra.lift_ι_apply]
    rfl
  have h2 : ∀ w, SymmetricAlgebra.lift (SymmetricAlgebra.ι ℝ JetComponentSpace ∘ₗ
      JetComponentSpace.repLorentzGroup Λ)
      (SymmetricAlgebra.ι ℝ JetComponentSpace w) =
      SymmetricAlgebra.ι ℝ JetComponentSpace
        (JetComponentSpace.repLorentzGroup Λ w) := fun w => by
    rw [SymmetricAlgebra.lift_ι_apply]
    rfl
  have h : (massWeightScaleReal c).comp (SymmetricAlgebra.lift
      (SymmetricAlgebra.ι ℝ JetComponentSpace ∘ₗ
        JetComponentSpace.repLorentzGroup Λ)) =
      (SymmetricAlgebra.lift (SymmetricAlgebra.ι ℝ JetComponentSpace ∘ₗ
        JetComponentSpace.repLorentzGroup Λ)).comp (massWeightScaleReal c) := by
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun v => ?_)
    show massWeightScaleReal c ((SymmetricAlgebra.lift
        (SymmetricAlgebra.ι ℝ JetComponentSpace ∘ₗ
          JetComponentSpace.repLorentzGroup Λ))
        ((SymmetricAlgebra.ι ℝ JetComponentSpace) v)) =
      (SymmetricAlgebra.lift (SymmetricAlgebra.ι ℝ JetComponentSpace ∘ₗ
        JetComponentSpace.repLorentzGroup Λ))
        (massWeightScaleReal c ((SymmetricAlgebra.ι ℝ JetComponentSpace) v))
    rw [h2, h1, h1, h2]
    exact congrArg (SymmetricAlgebra.ι ℝ JetComponentSpace)
      (DFunLike.congr_fun
        (JetComponentSpace.massWeightScale_repLorentzGroup c Λ) v)
  exact DFunLike.congr_fun h x

/-- For real scalars the complexified mass-dimension scaling is the base change
  of the real scaling. -/
lemma massWeightScale_ofReal (r : ℝ) :
    massWeightScale (r : ℂ) =
      Algebra.TensorProduct.map (AlgHom.id ℂ ℂ) (massWeightScaleReal r) := by
  refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) ?_
  refine SymmetricAlgebra.algHom_ext ?_
  refine JetComponentSpace.basis.ext fun j => ?_
  show massWeightScale (r : ℂ) ((1 : ℂ) ⊗ₜ[ℝ] ofGenerator j) =
    Algebra.TensorProduct.map (AlgHom.id ℂ ℂ) (massWeightScaleReal r)
      ((1 : ℂ) ⊗ₜ[ℝ] ofGenerator j)
  rw [massWeightScale_tmul_ofGenerator, Algebra.TensorProduct.map_tmul,
    massWeightScaleReal_ofGenerator, TensorProduct.tmul_smul, ← Complex.ofReal_pow]
  exact algebraMap_smul ℂ (r ^ j.massWeight) ((1 : ℂ) ⊗ₜ[ℝ] ofGenerator j)

/-- The complexified scaling at a real scalar commutes with the Lorentz
  action. -/
lemma massWeightScale_ofReal_complexRepLorentzGroup (r : ℝ) (Λ : SL(2,ℂ))
    (x : ℂ ⊗[ℝ] JetAlgebra) :
    massWeightScale (r : ℂ) (complexRepLorentzGroup Λ x) =
      complexRepLorentzGroup Λ (massWeightScale (r : ℂ) x) := by
  rw [massWeightScale_ofReal]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul z b =>
    rw [show complexRepLorentzGroup Λ (z ⊗ₜ[ℝ] b) =
        z ⊗ₜ[ℝ] repLorentzGroup Λ b from rfl,
      Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
      show complexRepLorentzGroup Λ ((AlgHom.id ℂ ℂ) z ⊗ₜ[ℝ]
        massWeightScaleReal r b) = (AlgHom.id ℂ ℂ) z ⊗ₜ[ℝ]
        repLorentzGroup Λ (massWeightScaleReal r b) from rfl,
      massWeightScaleReal_repLorentzGroup]

/-!

## Lorentz transformation laws of the field strength

The field strength `F_{μν} = ∂_μ B_ν - ∂_ν B_μ` and its derivatives are
tensors: every index transforms by the Lorentz matrix.

-/

set_option maxHeartbeats 2000000 in
/-- The transformation law of the first-derivative field strength on the
  B-boson jet algebra: a three-index tensor. -/
lemma repLorentzGroup_fieldStrengthDeriv_singleton
    (Λ : SL(2,ℂ)) (ρ μ ν : Fin 1 ⊕ Fin 3) :
    BBoson.JetAlgebra.repLorentzGroup Λ
      (BBoson.JetAlgebra.fieldStrengthDeriv {ρ} μ ν) =
      ∑ r, ∑ a, ∑ b, ((Lorentz.SL2C.toLorentzGroup Λ).1 r ρ *
        ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ *
          (Lorentz.SL2C.toLorentzGroup Λ).1 b ν)) •
        BBoson.JetAlgebra.fieldStrengthDeriv {r} a b := by
  have hFS : ∀ r a b : Fin 1 ⊕ Fin 3,
      BBoson.JetAlgebra.fieldStrengthDeriv ({r} : Multiset _) a b =
        BBoson.JetAlgebra.ofGenerator (.dB {r, a} b) -
          BBoson.JetAlgebra.ofGenerator (.dB {r, b} a) := fun r a b => by
    rw [BBoson.JetAlgebra.fieldStrengthDeriv,
      show ({r} : Multiset (Fin 1 ⊕ Fin 3)) + {a} = {r, a} from by
        rw [Multiset.singleton_add, ← Multiset.insert_eq_cons],
      show ({r} : Multiset (Fin 1 ⊕ Fin 3)) + {b} = {r, b} from by
        rw [Multiset.singleton_add, ← Multiset.insert_eq_cons]]
  simp only [hFS]
  rw [map_sub, BBoson.JetAlgebra.ofGenerator, BBoson.JetAlgebra.ofGenerator,
    BBoson.JetAlgebra.repLorentzGroup_apply_ι,
    BBoson.JetAlgebra.repLorentzGroup_apply_ι,
    BBoson.JetComponentSpace.repLorentzGroup_basis_dB_pair,
    BBoson.JetComponentSpace.repLorentzGroup_basis_dB_pair]
  simp only [map_sum, map_smul, smul_sub, Finset.sum_sub_distrib,
    BBoson.JetAlgebra.ofGenerator]
  rw [sub_right_inj]
  conv_rhs => enter [2, r]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => ?_
  congr 1
  ring

/-- The transformation of the complexified first-derivative field strength. -/
lemma complexRepLorentzGroup_one_tmul_fieldStrengthDeriv_singleton
    (Λ : SL(2,ℂ)) (ρ μ ν : Fin 1 ⊕ Fin 3) :
    BBoson.JetAlgebra.complexRepLorentzGroup Λ
        ((1 : ℂ) ⊗ₜ[ℝ] BBoson.JetAlgebra.fieldStrengthDeriv {ρ} μ ν) =
      ∑ r, ∑ a, ∑ b, ((Lorentz.SL2C.toLorentzGroup Λ).1 r ρ *
        ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ *
          (Lorentz.SL2C.toLorentzGroup Λ).1 b ν)) •
        ((1 : ℂ) ⊗ₜ[ℝ] BBoson.JetAlgebra.fieldStrengthDeriv {r} a b) := by
  rw [show BBoson.JetAlgebra.complexRepLorentzGroup Λ
      ((1 : ℂ) ⊗ₜ[ℝ] BBoson.JetAlgebra.fieldStrengthDeriv {ρ} μ ν) =
      (1 : ℂ) ⊗ₜ[ℝ] BBoson.JetAlgebra.repLorentzGroup Λ
        (BBoson.JetAlgebra.fieldStrengthDeriv {ρ} μ ν) from rfl,
    BBoson.JetAlgebra.repLorentzGroup_fieldStrengthDeriv_singleton]
  simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul]

set_option maxHeartbeats 2000000 in
/-- The transformation law of the second-derivative field strength on the
  B-boson jet algebra: a four-index tensor. -/
lemma repLorentzGroup_fieldStrengthDeriv_pair
    (Λ : SL(2,ℂ)) (ρ τ μ ν : Fin 1 ⊕ Fin 3) :
    BBoson.JetAlgebra.repLorentzGroup Λ
      (BBoson.JetAlgebra.fieldStrengthDeriv {ρ, τ} μ ν) =
      ∑ r, ∑ s, ∑ a, ∑ b, ((Lorentz.SL2C.toLorentzGroup Λ).1 r ρ *
        ((Lorentz.SL2C.toLorentzGroup Λ).1 s τ *
          ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ *
          (Lorentz.SL2C.toLorentzGroup Λ).1 b ν))) •
        BBoson.JetAlgebra.fieldStrengthDeriv {r, s} a b := by
  have hFS : ∀ r s a b : Fin 1 ⊕ Fin 3,
      BBoson.JetAlgebra.fieldStrengthDeriv ({r, s} : Multiset _) a b =
        BBoson.JetAlgebra.ofGenerator (.dB {r, s, a} b) -
          BBoson.JetAlgebra.ofGenerator (.dB {r, s, b} a) := fun r s a b => by
    rw [BBoson.JetAlgebra.fieldStrengthDeriv,
      show ({r, s} : Multiset (Fin 1 ⊕ Fin 3)) + {a} = {r, s, a} from by
        rw [Multiset.insert_eq_cons, Multiset.cons_add, Multiset.singleton_add,
          ← Multiset.insert_eq_cons, ← Multiset.insert_eq_cons],
      show ({r, s} : Multiset (Fin 1 ⊕ Fin 3)) + {b} = {r, s, b} from by
        rw [Multiset.insert_eq_cons, Multiset.cons_add, Multiset.singleton_add,
          ← Multiset.insert_eq_cons, ← Multiset.insert_eq_cons]]
  simp only [hFS]
  rw [map_sub, BBoson.JetAlgebra.ofGenerator, BBoson.JetAlgebra.ofGenerator,
    BBoson.JetAlgebra.repLorentzGroup_apply_ι,
    BBoson.JetAlgebra.repLorentzGroup_apply_ι,
    BBoson.JetComponentSpace.repLorentzGroup_basis_dB_triple,
    BBoson.JetComponentSpace.repLorentzGroup_basis_dB_triple]
  simp only [map_sum, map_smul, smul_sub, Finset.sum_sub_distrib,
    BBoson.JetAlgebra.ofGenerator]
  rw [sub_right_inj]
  conv_rhs => enter [2, r, 2, s]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  ring

/-- The transformation of the complexified second-derivative field strength. -/
lemma complexRepLorentzGroup_one_tmul_fieldStrengthDeriv_pair
    (Λ : SL(2,ℂ)) (ρ τ μ ν : Fin 1 ⊕ Fin 3) :
    BBoson.JetAlgebra.complexRepLorentzGroup Λ
        ((1 : ℂ) ⊗ₜ[ℝ] BBoson.JetAlgebra.fieldStrengthDeriv {ρ, τ} μ ν) =
      ∑ r, ∑ s, ∑ a, ∑ b, ((Lorentz.SL2C.toLorentzGroup Λ).1 r ρ *
        ((Lorentz.SL2C.toLorentzGroup Λ).1 s τ *
          ((Lorentz.SL2C.toLorentzGroup Λ).1 a μ *
          (Lorentz.SL2C.toLorentzGroup Λ).1 b ν))) •
        ((1 : ℂ) ⊗ₜ[ℝ] BBoson.JetAlgebra.fieldStrengthDeriv {r, s} a b) := by
  rw [show BBoson.JetAlgebra.complexRepLorentzGroup Λ
      ((1 : ℂ) ⊗ₜ[ℝ] BBoson.JetAlgebra.fieldStrengthDeriv {ρ, τ} μ ν) =
      (1 : ℂ) ⊗ₜ[ℝ] BBoson.JetAlgebra.repLorentzGroup Λ
        (BBoson.JetAlgebra.fieldStrengthDeriv {ρ, τ} μ ν) from rfl,
    BBoson.JetAlgebra.repLorentzGroup_fieldStrengthDeriv_pair]
  simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul]

end JetAlgebra

end BBoson

end StandardModel
