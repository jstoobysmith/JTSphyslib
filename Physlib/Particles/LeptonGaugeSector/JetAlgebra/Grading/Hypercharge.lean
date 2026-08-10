/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.FermionicParity
public import Mathlib.Algebra.Polynomial.Laurent
/-!
# Grading due to hypercharge

The JetAlgebra can be mapped into a `LaurentPolynomial` mapping generators
to exponents of the generator `T` corresponding to their hypercharge.
This map is an algebra map. For example `ψ ↦ T^6 • ψ`

In the same way which mass dimension is defined through `Polynomial`,
we define a grading on `JetAlgebra` through `LaurentPolynomial`.

This grading can be used to define a projection from `JetAlgebra` to itself
picking out only the subspace of terms which are charge singlets.

Every term which is invariant is stable under this projection.
This result trivially generalizes to any theory based on the SM gauge group.

*Sign convention*: charges are normalized as `6Y`, and the generators of the jet algebra are
the *component functions* of the fields, which transform contragrediently to them. The
charged-lepton singlet is the `(1, 1)_{-6}` field, so its component function `ψ_α` carries
`+6`, matching `repJetGaugeGroupI_dψ_nil`; the conjugate component function `ψ̄_α` carries
`-6`, and the B-boson component functions carry `0`.

Only the constant gauge transformations are used below, and they already suffice: a gauge jet
mixes derivative orders but not species, so the constant part is where the charge is read off.

## i. Overview

Every generator is an eigenvector of the constant `U(1)` gauge transformations, with the
character `z ↦ z ^ q` for `q` its hypercharge. Recording that exponent in the formal variable
`T` of a Laurent polynomial gives an algebra map `hyperchargePoly`, whose `T ^ q` coefficient
is the part of an element of hypercharge `q`.

The constant gauge action is then literally the evaluation of the hypercharge polynomial at
the gauge parameter, `repJetGaugeGroupI_ofConstant_eq_evalUnit`. Invariance therefore says
that a fixed Laurent expression takes the same value at every point of the unit circle, which
by independence of the circle characters forces every charged component to vanish.

## ii. Key results

- `Hypercharge` : the hypercharge of a generator.
- `JetAlgebra.hyperchargePoly` : the hypercharge Laurent polynomial.
- `JetAlgebra.hyperchargeSubmodule` : the submodule of elements of a given hypercharge.
- `JetAlgebra.neutralProjection` : the projection onto the charge singlets.
- `JetAlgebra.mem_hyperchargeSubmodule_zero_of_isInvariant` : an invariant term is a charge
  singlet.
- `JetAlgebra.neutralProjection_of_isInvariant` : an invariant term is fixed by the
  projection.

## iii. Table of contents

- A. Laurent polynomials over a noncommutative ring
- B. The hypercharge Laurent polynomial
- C. The hypercharge grading
- D. Evaluation, and the constant gauge action
- E. Independence of the circle characters
- F. Invariant terms are charge singlets

-/

@[expose] public section

namespace LeptonGaugeSector
open TensorProduct StandardModel Matrix MatrixGroups LorentzGroup LaurentPolynomial

/-- The hypercharge of a generator of the lepton–gauge-sector jet algebra, normalized as `6Y`.
  The generators are component functions, so they carry the charge contragredient to that of
  the field: `ψ_α` carries `+6` and `ψ̄_α` carries `-6`, while the B-boson component functions
  are neutral. -/
def Hypercharge : JetGenerators → ℤ
  | JetGenerators.dB _ _ => 0
  | JetGenerators.dψ _ _ => 6
  | JetGenerators.dbarψ _ _ => -6

/-- The hypercharge of a generator of the charged-lepton factor. -/
def leptonHypercharge : LeptonSinglet.JetGenerators → ℤ
  | LeptonSinglet.JetGenerators.dψ _ _ => 6
  | LeptonSinglet.JetGenerators.dbarψ _ _ => -6

namespace JetAlgebra

/-!

## A. Laurent polynomials over a noncommutative ring

The coefficient ring here is the jet algebra, which is not commutative, so the parts of the
`LaurentPolynomial` API that assume commutativity — in particular `eval₂` — are unavailable.
The three facts below are all that is needed: how two Laurent monomials multiply and add, and
that `C` of a central element is central.

-/

section Laurent

variable {R : Type*} [Semiring R]

/-- Laurent monomials multiply by adding exponents. -/
lemma C_mul_T_mul_C_mul_T (a b : R) (m n : ℤ) :
    C a * T m * (C b * T n) = C (a * b) * T (m + n) := by
  rw [← single_eq_C_mul_T, ← single_eq_C_mul_T, ← single_eq_C_mul_T,
    AddMonoidAlgebra.single_mul_single]

/-- Laurent monomials of equal exponent add coefficientwise. -/
lemma C_mul_T_add_C_mul_T (a b : R) (n : ℤ) :
    C a * T n + C b * T n = C (a + b) * T n := by
  rw [← add_mul, ← map_add]

/-- `C` of a central element is central: multiplication by `C a` acts on each coefficient. -/
lemma commute_C_of_central {a : R} (ha : ∀ z : R, Commute a z) (p : R[T;T⁻¹]) :
    Commute (C a) p := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => exact Commute.zero_right _
  | add p q hp hq => exact hp.add_right hq
  | single m r =>
    show C a * _ = _ * C a
    rw [← single_eq_C, AddMonoidAlgebra.single_mul_single,
      AddMonoidAlgebra.single_mul_single, zero_add, add_zero, ha r]

end Laurent

/-- `LaurentPolynomial.C` as an algebra map. It is not `algebraMap`, which is unavailable
  because the jet algebra is not commutative. -/
noncomputable def CAlgHom : JetAlgebra →ₐ[ℂ] LaurentPolynomial JetAlgebra where
  toFun := C
  map_one' := map_one C
  map_mul' := map_mul C
  map_zero' := map_zero C
  map_add' := map_add C
  commutes' r := (LaurentPolynomial.algebraMap_apply r).symm

@[simp]
lemma CAlgHom_apply (x : JetAlgebra) : CAlgHom x = C x := rfl

/-- The bosonic factor is central in the jet algebra: it is a tensor factor, and the
  complexified B-boson jet algebra is commutative. -/
lemma commute_inclB (a : ℂ ⊗[ℝ] BBoson.JetAlgebra) (x : JetAlgebra) :
    Commute (inclB a) x := by
  induction x using JetAlgebra.induction_on with
  | zero => exact Commute.zero_right _
  | add u v hu hv => exact hu.add_right hv
  | tmul b l =>
    show inclB a * (b ⊗ⱼ l) = (b ⊗ⱼ l) * inclB a
    rw [show inclB a = a ⊗ⱼ (1 : LeptonSinglet.JetAlgebra) from rfl, tmul_mul_tmul,
      tmul_mul_tmul, mul_one, one_mul, mul_comm a b]

/-!

## B. The hypercharge Laurent polynomial

The bosonic factor is neutral, so on it the hypercharge polynomial is the constant polynomial.
On the fermionic factor the generators are eigenvectors of charge `±6`; sending each to
`C · T ^ (±6)` squares to zero, because the two exponents cancel in the cross terms, so it
extends to the exterior algebra.

-/

/-- The generator map of the hypercharge polynomial on the charged-lepton component space. -/
noncomputable def hyperchargeι :
    LeptonSinglet.JetComponentSpace →ₗ[ℂ] LaurentPolynomial JetAlgebra :=
  LeptonSinglet.JetComponentSpace.basis.constr ℂ fun j =>
    C (inclL (LeptonSinglet.JetAlgebra.ofGenerator j)) * T (leptonHypercharge j)

@[simp]
lemma hyperchargeι_basis (j : LeptonSinglet.JetGenerators) :
    hyperchargeι (LeptonSinglet.JetComponentSpace.basis j) =
      C (inclL (LeptonSinglet.JetAlgebra.ofGenerator j)) * T (leptonHypercharge j) := by
  rw [hyperchargeι, Module.Basis.constr_basis]

/-- The generator map squares to zero: the exponents of a cross term cancel, leaving the
  anticommutator of two exterior generators. -/
lemma hyperchargeι_mul_self (v : LeptonSinglet.JetComponentSpace) :
    hyperchargeι v * hyperchargeι v = 0 := by
  set B := (LinearMap.mul ℂ (LaurentPolynomial JetAlgebra)).compl₁₂ hyperchargeι hyperchargeι
    with hBdef
  have hB : B + B.flip = 0 :=
    LinearMap.ext_basis LeptonSinglet.JetComponentSpace.basis
      LeptonSinglet.JetComponentSpace.basis fun j k => by
      simp only [hBdef, LinearMap.add_apply, LinearMap.compl₁₂_apply, LinearMap.flip_apply,
        LinearMap.mul_apply', LinearMap.zero_apply, hyperchargeι_basis]
      rw [C_mul_T_mul_C_mul_T, C_mul_T_mul_C_mul_T,
        add_comm (leptonHypercharge k) (leptonHypercharge j), C_mul_T_add_C_mul_T,
        ← map_mul inclL, ← map_mul inclL, ← map_add inclL,
        show LeptonSinglet.JetAlgebra.ofGenerator j *
              LeptonSinglet.JetAlgebra.ofGenerator k +
            LeptonSinglet.JetAlgebra.ofGenerator k *
              LeptonSinglet.JetAlgebra.ofGenerator j = 0 from
          ExteriorAlgebra.ι_add_mul_swap _ _,
        map_zero, map_zero, zero_mul]
  have h2 : (2 : ℂ) • (hyperchargeι v * hyperchargeι v) = 0 := by
    rw [two_smul]
    exact LinearMap.congr_fun (LinearMap.congr_fun hB v) v
  simpa [smul_smul] using congrArg (fun y => (2⁻¹ : ℂ) • y) h2

/-- The hypercharge polynomial on the charged-lepton factor. -/
noncomputable def hyperchargePolyL :
    LeptonSinglet.JetAlgebra →ₐ[ℂ] LaurentPolynomial JetAlgebra :=
  ExteriorAlgebra.lift ℂ ⟨hyperchargeι, hyperchargeι_mul_self⟩

@[simp]
lemma hyperchargePolyL_ofGenerator (j : LeptonSinglet.JetGenerators) :
    hyperchargePolyL (LeptonSinglet.JetAlgebra.ofGenerator j) =
      C (inclL (LeptonSinglet.JetAlgebra.ofGenerator j)) * T (leptonHypercharge j) := by
  rw [show LeptonSinglet.JetAlgebra.ofGenerator j =
      ExteriorAlgebra.ι ℂ (LeptonSinglet.JetComponentSpace.basis j) from rfl,
    hyperchargePolyL, ExteriorAlgebra.lift_ι_apply, hyperchargeι_basis]
  rfl

/-- The hypercharge Laurent polynomial: the `ℂ`-algebra map sending each generator `j` to
  `j * T ^ q`, where `q` is the hypercharge of `j`. The coefficient of `T ^ q` in the
  hypercharge polynomial of an element is its part of hypercharge `q`. -/
noncomputable def hyperchargePoly : JetAlgebra →ₐ[ℂ] LaurentPolynomial JetAlgebra :=
  Algebra.TensorProduct.lift (CAlgHom.comp inclB) hyperchargePolyL
    fun a _ => commute_C_of_central (commute_inclB a) _

@[simp]
lemma hyperchargePoly_tmul (a : ℂ ⊗[ℝ] BBoson.JetAlgebra) (l : LeptonSinglet.JetAlgebra) :
    hyperchargePoly (a ⊗ⱼ l) = C (inclB a) * hyperchargePolyL l := rfl

/-- On the bosonic factor the hypercharge polynomial is constant: the B boson is neutral. -/
lemma hyperchargePoly_inclB (a : ℂ ⊗[ℝ] BBoson.JetAlgebra) :
    hyperchargePoly (inclB a) = C (inclB a) := by
  rw [show hyperchargePoly (inclB a) = C (inclB a) * hyperchargePolyL 1 from rfl,
    map_one, mul_one]

/-- On the fermionic factor the hypercharge polynomial is the charged-lepton one. -/
lemma hyperchargePoly_inclL (l : LeptonSinglet.JetAlgebra) :
    hyperchargePoly (inclL l) = hyperchargePolyL l := by
  rw [show hyperchargePoly (inclL l) =
      C (inclB (1 : ℂ ⊗[ℝ] BBoson.JetAlgebra)) * hyperchargePolyL l from rfl,
    map_one, map_one, one_mul]

/-- Each generator is sent to `j * T ^ q`, where `q` is its hypercharge. -/
@[simp]
lemma hyperchargePoly_ofGenerator (j : JetGenerators) :
    hyperchargePoly [j]ₐ = C [j]ₐ * T (Hypercharge j) := by
  cases j with
  | dB s μ =>
    rw [show ([JetGenerators.dB s μ]ₐ : JetAlgebra) = inclB ((1 : ℂ) ⊗ₜ[ℝ]
        BBoson.JetAlgebra.ofGenerator (BBoson.JetGenerators.dB s μ)) from rfl,
      hyperchargePoly_inclB, show Hypercharge (JetGenerators.dB s μ) = 0 from rfl, T_zero,
      mul_one]
  | dψ s α =>
    rw [show ([JetGenerators.dψ s α]ₐ : JetAlgebra) = inclL
        (LeptonSinglet.JetAlgebra.ofGenerator (LeptonSinglet.JetGenerators.dψ s α)) from rfl,
      hyperchargePoly_inclL, hyperchargePolyL_ofGenerator]
    rfl
  | dbarψ s α =>
    rw [show ([JetGenerators.dbarψ s α]ₐ : JetAlgebra) = inclL
        (LeptonSinglet.JetAlgebra.ofGenerator (LeptonSinglet.JetGenerators.dbarψ s α))
        from rfl,
      hyperchargePoly_inclL, hyperchargePolyL_ofGenerator]
    rfl

/-!

## C. The hypercharge grading

-/

/-- The submodule of elements of hypercharge `q`: those `x` whose hypercharge polynomial is
  `x * T ^ q`. -/
def hyperchargeSubmodule (q : ℤ) : Submodule ℂ JetAlgebra where
  carrier := {x | hyperchargePoly x = C x * T q}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
    rw [ha, hb, add_mul]
  zero_mem' := by simp
  smul_mem' c x hx := by
    simp only [Set.mem_setOf_eq, map_smul] at hx ⊢
    rw [hx, Algebra.smul_def, Algebra.smul_def, LaurentPolynomial.algebraMap_apply, ← mul_assoc,
      ← map_mul]

@[simp]
lemma mem_hyperchargeSubmodule {q : ℤ} {x : JetAlgebra} :
    x ∈ hyperchargeSubmodule q ↔ hyperchargePoly x = C x * T q := Iff.rfl

/-- Hypercharges add under multiplication. -/
lemma mul_mem_hyperchargeSubmodule {p q : ℤ} {x y : JetAlgebra}
    (hx : x ∈ hyperchargeSubmodule p) (hy : y ∈ hyperchargeSubmodule q) :
    x * y ∈ hyperchargeSubmodule (p + q) := by
  simp only [mem_hyperchargeSubmodule, map_mul] at hx hy ⊢
  rw [hx, hy, C_mul_T_mul_C_mul_T, map_mul]

/-- Hypercharges add under multiplication, and `1` is neutral. -/
instance : SetLike.GradedMonoid hyperchargeSubmodule where
  one_mem := by
    show hyperchargePoly 1 = C 1 * T 0
    rw [T_zero, mul_one, map_one, map_one]
  mul_mem _ _ _ _ hx hy := mul_mem_hyperchargeSubmodule hx hy

/-- The generator `j` has hypercharge `Hypercharge j`. -/
lemma ofGenerator_mem_hyperchargeSubmodule (j : JetGenerators) :
    [j]ₐ ∈ hyperchargeSubmodule (Hypercharge j) :=
  hyperchargePoly_ofGenerator j

/-- The hypercharge-`q` component of an element: the coefficient of `T ^ q` in its hypercharge
  polynomial. -/
noncomputable def chargeComponent (q : ℤ) : JetAlgebra →ₗ[ℂ] JetAlgebra where
  toFun x := (hyperchargePoly x).coeff q
  map_add' x y := by rw [map_add]; rfl
  map_smul' c x := by rw [map_smul]; rfl

@[simp]
lemma chargeComponent_apply (q : ℤ) (x : JetAlgebra) :
    chargeComponent q x = (hyperchargePoly x).coeff q := rfl

/-- On a homogeneous element the component of its own charge is the element itself. -/
lemma chargeComponent_of_mem {q : ℤ} {x : JetAlgebra} (hx : x ∈ hyperchargeSubmodule q) :
    chargeComponent q x = x := by
  rw [chargeComponent_apply, mem_hyperchargeSubmodule.mp hx, ← single_eq_C_mul_T,
    AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]

/-- On a homogeneous element every other charge component vanishes. -/
lemma chargeComponent_of_mem_ne {p q : ℤ} {x : JetAlgebra} (hpq : p ≠ q)
    (hx : x ∈ hyperchargeSubmodule p) : chargeComponent q x = 0 := by
  rw [chargeComponent_apply, mem_hyperchargeSubmodule.mp hx, ← single_eq_C_mul_T,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg hpq]

/-- The projection onto the charge singlets: the part of hypercharge zero. -/
noncomputable def neutralProjection : JetAlgebra →ₗ[ℂ] JetAlgebra := chargeComponent 0

lemma neutralProjection_apply (x : JetAlgebra) :
    neutralProjection x = (hyperchargePoly x).coeff 0 := rfl

/-!

## D. Evaluation, and the constant gauge action

Setting the formal variable to an invertible scalar gives an algebra map back to the jet
algebra. Evaluating at `1` recovers the element; evaluating at a unitary scalar `z` is exactly
the action of the constant gauge transformation with `U(1)` part `z`.

-/

/-- The character `k ↦ z ^ k` of a unit, valued in the jet algebra. -/
noncomputable def charMonoidHom (z : ℂˣ) : Multiplicative ℤ →* JetAlgebra :=
  ((algebraMap ℂ JetAlgebra).toMonoidHom.comp (Units.coeHom ℂ)).comp (zpowersHom ℂˣ z)

@[simp]
lemma charMonoidHom_apply (z : ℂˣ) (k : ℤ) :
    charMonoidHom z (Multiplicative.ofAdd k) = algebraMap ℂ JetAlgebra ((z : ℂ) ^ k) := by
  simp [charMonoidHom, Units.val_zpow_eq_zpow_val]

/-- Evaluation of a Laurent polynomial at an invertible scalar. The jet algebra is not
  commutative, so this is multiplicative only because the scalars are central. -/
noncomputable def evalUnit (z : ℂˣ) : LaurentPolynomial JetAlgebra →ₐ[ℂ] JetAlgebra :=
  AddMonoidAlgebra.liftNCAlgHom (AlgHom.id ℂ JetAlgebra) (charMonoidHom z)
    fun x k => by
      rw [show charMonoidHom z k =
        algebraMap ℂ JetAlgebra ((z : ℂ) ^ (Multiplicative.toAdd k)) from
          charMonoidHom_apply z _]
      exact (Algebra.commutes _ _).symm

lemma evalUnit_single (z : ℂˣ) (k : ℤ) (a : JetAlgebra) :
    evalUnit z (AddMonoidAlgebra.single k a) = ((z : ℂ) ^ k) • a := by
  show AddMonoidAlgebra.liftNC _ _ _ = _
  rw [AddMonoidAlgebra.liftNC_single, charMonoidHom_apply]
  show a * algebraMap ℂ JetAlgebra ((z : ℂ) ^ k) = _
  rw [← Algebra.commutes, ← Algebra.smul_def]

@[simp]
lemma evalUnit_C_mul_T (z : ℂˣ) (k : ℤ) (a : JetAlgebra) :
    evalUnit z (C a * T k) = ((z : ℂ) ^ k) • a := by
  rw [← single_eq_C_mul_T, evalUnit_single]

/-- Evaluation is the sum of the coefficients, weighted by the powers of the scalar. -/
lemma evalUnit_eq_sum (z : ℂˣ) (p : LaurentPolynomial JetAlgebra) :
    evalUnit z p = ∑ k ∈ p.coeff.support, ((z : ℂ) ^ k) • p.coeff k := by
  have hsum : ∀ q : LaurentPolynomial JetAlgebra,
      evalUnit z q = q.coeff.sum fun k a => ((z : ℂ) ^ k) • a := by
    intro q
    induction q using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add u v hu hv =>
      rw [map_add, hu, hv, AddMonoidAlgebra.coeff_add,
        Finsupp.sum_add_index' (fun k => smul_zero _) fun k a b => smul_add _ a b]
    | single m r =>
      rw [evalUnit_single, AddMonoidAlgebra.coeff_single, Finsupp.sum]
      by_cases hr : r = 0
      · subst hr
        simp
      · rw [Finsupp.support_single m hr, Finset.sum_singleton, Finsupp.single_eq_same]
  exact hsum p

/-- Setting the formal variable to one recovers the original element. -/
lemma evalUnit_one_hyperchargePoly (x : JetAlgebra) : evalUnit 1 (hyperchargePoly x) = x := by
  have h : (evalUnit 1).comp hyperchargePoly = AlgHom.id ℂ JetAlgebra := by
    refine algHom_ext fun j => ?_
    rw [AlgHom.comp_apply, hyperchargePoly_ofGenerator, evalUnit_C_mul_T]
    simp
  exact AlgHom.congr_fun h x

/-- Every element is the sum of its charge components. -/
lemma eq_sum_chargeComponent (x : JetAlgebra) :
    x = ∑ k ∈ (hyperchargePoly x).coeff.support, chargeComponent k x := by
  conv_lhs => rw [← evalUnit_one_hyperchargePoly x]
  rw [evalUnit_eq_sum]
  exact Finset.sum_congr rfl fun k _ => by simp

/-- The `U(1)` part of a gauge-group element, as a unit of `ℂ`. -/
noncomputable def u1Unit (g : GaugeGroupI) : ℂˣ where
  val := (g.2.2 : ℂ)
  inv := star (g.2.2 : ℂ)
  val_inv := (Unitary.mem_iff.mp g.2.2.2).2
  inv_val := (Unitary.mem_iff.mp g.2.2.2).1

@[simp]
lemma u1Unit_val (g : GaugeGroupI) : ((u1Unit g : ℂˣ) : ℂ) = (g.2.2 : ℂ) := rfl

lemma u1Unit_inv (g : GaugeGroupI) :
    (((u1Unit g)⁻¹ : ℂˣ) : ℂ) = star (g.2.2 : ℂ) := rfl

/-- The constant gauge action on the charged-lepton component space is diagonal on the
  generator basis, with the hypercharge character as eigenvalue. -/
lemma leptonSinglet_repJetGaugeGroupI_ofConstant_basis (g : GaugeGroupI)
    (j : LeptonSinglet.JetGenerators) :
    LeptonSinglet.JetComponentSpace.repJetGaugeGroupI (JetGaugeGroupI.ofConstant g)
        (LeptonSinglet.JetComponentSpace.basis j) =
      ((u1Unit g : ℂ) ^ leptonHypercharge j) • LeptonSinglet.JetComponentSpace.basis j := by
  have hu : ((((JetGaugeGroupI.ofConstant g).2.2 : unitary JetRing)) : JetRing) =
      MvPowerSeries.C ((g.2.2 : ℂ)) := rfl
  cases j with
  | dψ s α =>
    rw [show leptonHypercharge (LeptonSinglet.JetGenerators.dψ s α) = (6 : ℕ) from rfl,
      zpow_natCast, u1Unit_val, LeptonSinglet.JetComponentSpace.basis_dψ,
      LeptonSinglet.JetComponentSpace.repJetGaugeGroupI_inl, hu, ← map_pow,
      DerivAlgebraComplex.jetRingAction_C]
    simp [TensorProduct.smul_tmul', Prod.smul_mk]
  | dbarψ s α =>
    rw [show leptonHypercharge (LeptonSinglet.JetGenerators.dbarψ s α) = -(6 : ℕ) from rfl,
      _root_.zpow_neg, zpow_natCast, ← inv_pow, ← Units.val_inv_eq_inv_val, u1Unit_inv,
      LeptonSinglet.JetComponentSpace.basis_dbarψ,
      LeptonSinglet.JetComponentSpace.repJetGaugeGroupI_inr, hu, JetRing.star_C, ← map_pow,
      DerivAlgebraComplex.jetRingAction_C]
    simp [TensorProduct.smul_tmul', Prod.smul_mk]

/-- A jet of a constant gauge transformation acts on each generator by its hypercharge
  character. -/
lemma repJetGaugeGroupI_ofConstant_ofGenerator (g : GaugeGroupI) (j : JetGenerators) :
    repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) [j]ₐ =
      ((u1Unit g : ℂ) ^ Hypercharge j) • [j]ₐ := by
  cases j with
  | dB s μ =>
    rw [show ([JetGenerators.dB s μ]ₐ : JetAlgebra) = inclB ((1 : ℂ) ⊗ₜ[ℝ]
        BBoson.JetAlgebra.ofGenerator (BBoson.JetGenerators.dB s μ)) from rfl,
      show Hypercharge (JetGenerators.dB s μ) = 0 from rfl, zpow_zero, one_smul,
      show inclB ((1 : ℂ) ⊗ₜ[ℝ] BBoson.JetAlgebra.ofGenerator (BBoson.JetGenerators.dB s μ)) =
        ((1 : ℂ) ⊗ₜ[ℝ] BBoson.JetAlgebra.ofGenerator (BBoson.JetGenerators.dB s μ)) ⊗ⱼ
          (1 : LeptonSinglet.JetAlgebra) from rfl,
      repJetGaugeGroupI_tmul', BBoson.JetAlgebra.complexRepJetGaugeGroupI_ofConstant,
      LeptonSinglet.JetAlgebra.repJetGaugeGroupI_apply_one]
  | dψ s α =>
    rw [show ([JetGenerators.dψ s α]ₐ : JetAlgebra) = (1 : ℂ ⊗[ℝ] BBoson.JetAlgebra) ⊗ⱼ
        LeptonSinglet.JetAlgebra.ofGenerator (LeptonSinglet.JetGenerators.dψ s α) from rfl,
      repJetGaugeGroupI_tmul', BBoson.JetAlgebra.complexRepJetGaugeGroupI_ofConstant,
      LeptonSinglet.JetAlgebra.repJetGaugeGroupI_apply,
      show LeptonSinglet.JetAlgebra.ofGenerator (LeptonSinglet.JetGenerators.dψ s α) =
        ExteriorAlgebra.ι ℂ (LeptonSinglet.JetComponentSpace.basis
          (LeptonSinglet.JetGenerators.dψ s α)) from rfl,
      ExteriorAlgebra.map_apply_ι, leptonSinglet_repJetGaugeGroupI_ofConstant_basis, map_smul,
      tmul_smul]
    rfl
  | dbarψ s α =>
    rw [show ([JetGenerators.dbarψ s α]ₐ : JetAlgebra) = (1 : ℂ ⊗[ℝ] BBoson.JetAlgebra) ⊗ⱼ
        LeptonSinglet.JetAlgebra.ofGenerator (LeptonSinglet.JetGenerators.dbarψ s α) from rfl,
      repJetGaugeGroupI_tmul', BBoson.JetAlgebra.complexRepJetGaugeGroupI_ofConstant,
      LeptonSinglet.JetAlgebra.repJetGaugeGroupI_apply,
      show LeptonSinglet.JetAlgebra.ofGenerator (LeptonSinglet.JetGenerators.dbarψ s α) =
        ExteriorAlgebra.ι ℂ (LeptonSinglet.JetComponentSpace.basis
          (LeptonSinglet.JetGenerators.dbarψ s α)) from rfl,
      ExteriorAlgebra.map_apply_ι, leptonSinglet_repJetGaugeGroupI_ofConstant_basis, map_smul,
      tmul_smul]
    rfl

/-- The constant gauge action is the evaluation of the hypercharge polynomial at the gauge
  parameter. This is the content of the hypercharge grading: the `U(1)` gauge group acts
  through the formal variable alone. -/
lemma repJetGaugeGroupI_ofConstant_eq_evalUnit (g : GaugeGroupI) (x : JetAlgebra) :
    repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) x =
      evalUnit (u1Unit g) (hyperchargePoly x) := by
  have h : repAlgHom (JetGaugeGroupI.ofConstant g) =
      (evalUnit (u1Unit g)).comp hyperchargePoly := by
    refine algHom_ext fun j => ?_
    rw [AlgHom.comp_apply, hyperchargePoly_ofGenerator, evalUnit_C_mul_T,
      ← repJetGaugeGroupI_eq_repAlgHom, repJetGaugeGroupI_ofConstant_ofGenerator]
  rw [repJetGaugeGroupI_eq_repAlgHom, h, AlgHom.comp_apply]

/-!

## E. Independence of the circle characters

A finite Laurent combination of the characters `z ↦ z ^ k` that vanishes on the whole unit
circle has vanishing coefficients: after clearing the negative powers it becomes a polynomial
with infinitely many roots.

-/

/-- The unit-circle exponential is unitary. -/
lemma exp_mul_I_mem_unitary (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) ∈ unitary ℂ := by
  have hstar : star (Complex.exp ((θ : ℂ) * Complex.I)) =
      Complex.exp (-((θ : ℂ) * Complex.I)) := by
    rw [show star (Complex.exp ((θ : ℂ) * Complex.I)) =
        (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * Complex.I)) from rfl,
      ← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal]
  rw [Unitary.mem_iff]
  constructor
  · rw [hstar, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  · rw [hstar, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

/-- The unit-circle exponentials are injective on `(0, 1)`. -/
lemma exp_mul_I_injOn :
    Set.InjOn (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I))
      (Set.Ioo (0 : ℝ) 1) := by
  intro a ha b hb hab
  rcases Complex.exp_eq_exp_iff_exists_int.mp hab with ⟨n, hn⟩
  have h2 : (a : ℂ) = (b : ℂ) + (n : ℂ) * (2 * (Real.pi : ℂ)) := by
    have h1 : (a : ℂ) * Complex.I =
        ((b : ℂ) + (n : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by
      rw [hn]
      ring
    exact mul_right_cancel₀ Complex.I_ne_zero h1
  have h3 : a = b + (n : ℝ) * (2 * Real.pi) := by exact_mod_cast h2
  have hn0 : n = 0 := by
    by_contra hne
    have h4 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hne
    have hπ : (2 : ℝ) ≤ Real.pi := Real.two_le_pi
    have h5 : |a - b| < 1 := by
      rw [abs_sub_lt_iff]
      constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]
    rw [h3] at h5
    simp only [add_sub_cancel_left] at h5
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h5
    nlinarith
  rw [hn0] at h3
  push_cast at h3
  linarith

/-- Independence of the circle characters: a finite Laurent combination vanishing on the unit
  circle has vanishing coefficients. -/
lemma eq_zero_of_forall_circle_sum_zpow_smul_eq_zero {V : Type*} [AddCommGroup V]
    [Module ℂ V] (s : Finset ℤ) (v : ℤ → V)
    (h : ∀ θ : ℝ, ∑ j ∈ s, (Complex.exp ((θ : ℂ) * Complex.I)) ^ j • v j = 0)
    {k : ℤ} (hk : k ∈ s) : v k = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  have hne : s.Nonempty := ⟨k, hk⟩
  set n₀ : ℤ := -s.min' hne with hn₀
  have hshift : ∀ j ∈ s, 0 ≤ j + n₀ := fun j hj => by
    have := s.min'_le j hj
    omega
  have heval : ∀ θ : ℝ, Polynomial.eval (Complex.exp ((θ : ℂ) * Complex.I))
      (∑ j ∈ s, Polynomial.monomial (j + n₀).toNat (φ (v j))) = 0 := by
    intro θ
    have hz0 : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    have h2 := congrArg φ (h θ)
    rw [map_sum, map_zero] at h2
    have h3 : ∑ j ∈ s, Complex.exp ((θ : ℂ) * Complex.I) ^ j * φ (v j) = 0 := by
      rw [← h2]
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul]; rfl
    have h4 : Complex.exp ((θ : ℂ) * Complex.I) ^ n₀ *
        ∑ j ∈ s, Complex.exp ((θ : ℂ) * Complex.I) ^ j * φ (v j) = 0 := by
      rw [h3, mul_zero]
    rw [Finset.mul_sum] at h4
    rw [Polynomial.eval_finsetSum, ← h4]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Polynomial.eval_monomial,
      show Complex.exp ((θ : ℂ) * Complex.I) ^ (j + n₀).toNat =
        Complex.exp ((θ : ℂ) * Complex.I) ^ ((j + n₀) : ℤ) from by
        rw [← zpow_natCast, Int.toNat_of_nonneg (hshift j hj)],
      zpow_add₀ hz0]
    ring
  have hzero : (∑ j ∈ s, Polynomial.monomial (j + n₀).toNat (φ (v j))) = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot _ ?_
    refine Set.Infinite.mono ?_
      ((Set.Ioo_infinite (by norm_num : (0 : ℝ) < 1)).image exp_mul_I_injOn)
    rintro z ⟨θ, _, rfl⟩
    exact heval θ
  have hcoeff := congrArg (fun p => Polynomial.coeff p (k + n₀).toNat) hzero
  rw [Polynomial.finsetSum_coeff] at hcoeff
  rw [Finset.sum_eq_single k
    (fun j hj hjk => by
      rw [Polynomial.coeff_monomial, if_neg (fun heq => hjk (by
        have h1 : j + n₀ = k + n₀ := by
          rw [← Int.toNat_of_nonneg (hshift j hj),
            ← Int.toNat_of_nonneg (hshift k hk), heq]
        omega))])
    (fun hks => absurd hk hks)] at hcoeff
  simpa using hcoeff

/-- The constant `U(1)` gauge transformation at a unitary scalar. -/
noncomputable def u1Gauge (z : ℂ) (hz : z ∈ unitary ℂ) : GaugeGroupI := (1, 1, ⟨z, hz⟩)

@[simp]
lemma u1Unit_u1Gauge (z : ℂ) (hz : z ∈ unitary ℂ) :
    ((u1Unit (u1Gauge z hz) : ℂˣ) : ℂ) = z := rfl

/-!

## F. Invariant terms are charge singlets

An invariant element is fixed by every constant gauge transformation, so its hypercharge
polynomial takes the same value at every point of the unit circle. By independence of the
circle characters its charged components all vanish, so it is homogeneous of hypercharge zero
and is fixed by the projection onto the charge singlets.

-/

/-- An element fixed by every constant gauge transformation is a charge singlet. -/
lemma mem_hyperchargeSubmodule_zero_of_forall_repJetGaugeGroupI_ofConstant_eq {x : JetAlgebra}
    (h : ∀ g : GaugeGroupI, repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) x = x) :
    x ∈ hyperchargeSubmodule 0 := by
  set p := hyperchargePoly x with hp
  set s : Finset ℤ := insert 0 p.coeff.support with hs
  set v : ℤ → JetAlgebra := fun k => p.coeff k - (if k = 0 then x else 0) with hv
  have hcirc : ∀ θ : ℝ, ∑ j ∈ s, (Complex.exp ((θ : ℂ) * Complex.I)) ^ j • v j = 0 := by
    intro θ
    set z : ℂ := Complex.exp ((θ : ℂ) * Complex.I) with hz
    set g : GaugeGroupI := u1Gauge z (exp_mul_I_mem_unitary θ) with hg
    have hsum : ∑ j ∈ s, z ^ j • p.coeff j = x := by
      have h1 : evalUnit (u1Unit g) p = x := by
        rw [hp, ← repJetGaugeGroupI_ofConstant_eq_evalUnit, h g]
      rw [← h1, evalUnit_eq_sum, u1Unit_u1Gauge]
      refine (Finset.sum_subset (Finset.subset_insert _ _) fun j _ hj => ?_).symm
      rw [Finsupp.notMem_support_iff.mp hj, smul_zero]
    have hx0 : ∑ j ∈ s, z ^ j • (if j = 0 then x else 0) = x := by
      rw [Finset.sum_eq_single (0 : ℤ) (fun j _ hj => by simp [hj])
        (fun hns => absurd (Finset.mem_insert_self (0 : ℤ) _) hns)]
      simp
    have hsplit : ∑ j ∈ s, z ^ j • v j =
        (∑ j ∈ s, z ^ j • p.coeff j) - ∑ j ∈ s, z ^ j • (if j = 0 then x else 0) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [hv]; exact smul_sub _ _ _
    rw [hsplit, hsum, hx0, sub_self]
  have hzero : ∀ k ∈ s, v k = 0 := fun k hk =>
    eq_zero_of_forall_circle_sum_zpow_smul_eq_zero s v hcirc hk
  have hcoeff0 : p.coeff 0 = x := by
    have h0 := hzero 0 (Finset.mem_insert_self _ _)
    rw [hv] at h0
    simpa using sub_eq_zero.mp (by simpa using h0)
  have hcoeffk : ∀ k : ℤ, k ≠ 0 → p.coeff k = 0 := by
    intro k hk
    by_cases hks : k ∈ p.coeff.support
    · have hkz := hzero k (Finset.mem_insert_of_mem hks)
      rw [hv] at hkz
      simpa [hk] using hkz
    · exact Finsupp.notMem_support_iff.mp hks
  rw [mem_hyperchargeSubmodule, ← hp, ← single_eq_C_mul_T]
  refine LaurentPolynomial.ext fun k => ?_
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases hk : (0 : ℤ) = k
  · rw [if_pos hk, ← hk, hcoeff0]
  · rw [if_neg hk, hcoeffk k (fun h => hk h.symm)]

/-- An invariant term is a charge singlet: it is homogeneous of hypercharge zero. -/
lemma mem_hyperchargeSubmodule_zero_of_isInvariant {x : JetAlgebra} (hx : IsInvariant x) :
    x ∈ hyperchargeSubmodule 0 :=
  mem_hyperchargeSubmodule_zero_of_forall_repJetGaugeGroupI_ofConstant_eq fun _ => hx.1 _

/-- Every invariant term is stable under the projection onto the charge singlets. -/
lemma neutralProjection_of_isInvariant {x : JetAlgebra} (hx : IsInvariant x) :
    neutralProjection x = x :=
  chargeComponent_of_mem (mem_hyperchargeSubmodule_zero_of_isInvariant hx)

/-- Every charged component of an invariant term vanishes. -/
lemma chargeComponent_of_isInvariant {q : ℤ} (hq : q ≠ 0) {x : JetAlgebra}
    (hx : IsInvariant x) : chargeComponent q x = 0 :=
  chargeComponent_of_mem_ne (fun h => hq h.symm)
    (mem_hyperchargeSubmodule_zero_of_isInvariant hx)

end JetAlgebra

end LeptonGaugeSector

end
