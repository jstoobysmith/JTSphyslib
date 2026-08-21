/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Analysis.Real.Pi.Irrational
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
/-!
# The hypercharge grading

## i. Overview

A representation of the global gauge group on a module has, for each integer `n`, a
**hypercharge weight space**: the vectors scaling by `u ^ n` under the pure `U(1)`
transformations. Charges are normalized as `6Y` throughout.

On an algebra, the representation is **hypercharge-graded** — `IsHyperchargeGraded` —
when it acts by algebra automorphisms and its weight spaces span. Multiplicativity makes
the weight spaces a graded monoid (weights add under products, the unit is neutral); the
spanning axiom is genuinely extra, since an abstract action of `U(1)` need not be
diagonalizable. Independence of the weight spaces, by contrast, is automatic: each weight
space lies in an eigenspace of the single transformation by `exp i`, whose powers are
pairwise distinct because `π` is irrational. Together these produce the internal direct
sum decomposition, the graded-algebra structure, and the projections onto each charge.

The charge-zero projection is the projection onto the charge singlets, which every
gauge-invariant element must survive.

## ii. Key results

- `GaugeGroupI.ofU1` : the inclusion of the `U(1)` factor of the gauge group.
- `hyperchargeSubmodule` : the weight space of a given hypercharge.
- `IsHyperchargeGraded` : the representation acts by algebra automorphisms and its
  weight spaces span.
- `hyperchargeSubmodule_iSupIndep` : the weight spaces are always independent.
- `GradedAlgebra (hyperchargeSubmodule rep)` : the hypercharge grading.
- `hyperchargeProj` : the projection onto a given hypercharge.

## iii. Table of contents

- A. The `U(1)` factor of the gauge group
- B. The hypercharge weight spaces
  - B.1. Weight spaces under multiplication
  - B.2. The span of the weight spaces
  - B.3. Tensor products
- C. Hypercharge-graded representations
- D. Independence of the weight spaces
- E. The grading
- F. The hypercharge projections

-/

@[expose] public section

namespace StandardModel

open Matrix

/-!

## A. The `U(1)` factor of the gauge group

-/

/-- The inclusion of the `U(1)` factor of the global gauge group: `u ↦ (1, 1, u)`.

  This is the subgroup against which hypercharge is read off. It is not the subgroup
  `GaugeGroupI.ofU1Subgroup`, which mixes a weak-isospin rotation into the `SU(2)`
  factor to be compatible with the discrete quotients. -/
def GaugeGroupI.ofU1 : unitary ℂ →* GaugeGroupI where
  toFun u := ⟨1, 1, u⟩
  map_one' := rfl
  map_mul' u v := by
    refine GaugeGroupI.ext ?_ ?_ ?_ <;> simp [GaugeGroupI.toSU3, GaugeGroupI.toSU2,
      GaugeGroupI.toU1]

/-- The underlying complex number of a unitary scalar is nonzero. -/
lemma unitary_coe_ne_zero (u : unitary ℂ) : ((u : ℂ)) ≠ 0 := fun h0 => by
  have h := Unitary.mul_star_self_of_mem u.2
  rw [h0, zero_mul] at h
  exact zero_ne_one h

/-!

## B. The hypercharge weight spaces

-/

variable {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

/-- The hypercharge-`n` weight space of a representation of the global gauge group: the
  vectors scaling by `u ^ n` under the pure `U(1)` transformations. Charges are
  normalized as `6Y`. -/
def hyperchargeSubmodule (rep : Representation ℂ GaugeGroupI M) (n : ℤ) :
    Submodule ℂ M where
  carrier := {x | ∀ u : unitary ℂ, rep (GaugeGroupI.ofU1 u) x = ((u : ℂ) ^ n) • x}
  add_mem' {a b} ha hb := fun u => by rw [map_add, ha u, hb u, smul_add]
  zero_mem' := fun u => by rw [map_zero, smul_zero]
  smul_mem' c x hx := fun u => by rw [map_smul, hx u, smul_comm]

lemma mem_hyperchargeSubmodule {rep : Representation ℂ GaugeGroupI M} {n : ℤ} {x : M} :
    x ∈ hyperchargeSubmodule rep n
      ↔ ∀ u : unitary ℂ, rep (GaugeGroupI.ofU1 u) x = ((u : ℂ) ^ n) • x := Iff.rfl

/-!

### B.1. Weight spaces under multiplication

-/

variable {B : Type*} [Ring B] [Algebra ℂ B]

/-- The unit is a charge singlet, for a unital action of the `U(1)` factor. -/
lemma one_mem_hyperchargeSubmodule {rep : Representation ℂ GaugeGroupI B}
    (h : ∀ u : unitary ℂ, rep (GaugeGroupI.ofU1 u) 1 = 1) :
    (1 : B) ∈ hyperchargeSubmodule rep 0 := fun u => by
  rw [h u, zpow_zero, one_smul]

/-- Hypercharges add under multiplication, for a multiplicative action of the `U(1)`
  factor. -/
lemma mul_mem_hyperchargeSubmodule {rep : Representation ℂ GaugeGroupI B}
    (h : ∀ (u : unitary ℂ) (x y : B),
      rep (GaugeGroupI.ofU1 u) (x * y)
        = rep (GaugeGroupI.ofU1 u) x * rep (GaugeGroupI.ofU1 u) y)
    {m n : ℤ} {x y : B} (hx : x ∈ hyperchargeSubmodule rep m)
    (hy : y ∈ hyperchargeSubmodule rep n) :
    x * y ∈ hyperchargeSubmodule rep (m + n) := fun u => by
  rw [h u, hx u, hy u, smul_mul_smul_comm, ← zpow_add₀ (unitary_coe_ne_zero u)]

/-!

### B.2. The span of the weight spaces

-/

/-- The span of all the hypercharge weight spaces. -/
def hyperchargeSpan (rep : Representation ℂ GaugeGroupI M) : Submodule ℂ M :=
  ⨆ n, hyperchargeSubmodule rep n

lemma mem_hyperchargeSpan_of_mem_hyperchargeSubmodule
    {rep : Representation ℂ GaugeGroupI M} {n : ℤ} {x : M}
    (h : x ∈ hyperchargeSubmodule rep n) : x ∈ hyperchargeSpan rep :=
  Submodule.mem_iSup_of_mem n h

/-- A representation with a spanning family of vectors in the hypercharge span is
  graded. -/
lemma hyperchargeSpan_eq_top_of_span {rep : Representation ℂ GaugeGroupI M} {S : Set M}
    (hS : Submodule.span ℂ S = ⊤) (h : ∀ x ∈ S, x ∈ hyperchargeSpan rep) :
    hyperchargeSpan rep = ⊤ :=
  eq_top_iff.mpr (hS ▸ Submodule.span_le.mpr h)

/-- A representation with a basis of vectors lying in the hypercharge span is graded. -/
lemma hyperchargeSpan_eq_top_of_basis {ι : Type*} {rep : Representation ℂ GaugeGroupI M}
    (b : Module.Basis ι ℂ M) (h : ∀ n, b n ∈ hyperchargeSpan rep) :
    hyperchargeSpan rep = ⊤ :=
  hyperchargeSpan_eq_top_of_span b.span_eq (by rintro _ ⟨n, rfl⟩; exact h n)

/-!

### B.3. Tensor products

-/

open TensorProduct in
/-- Hypercharges add under tensor products. -/
lemma tmul_mem_hyperchargeSubmodule {rep : Representation ℂ GaugeGroupI M}
    {rep₂ : Representation ℂ GaugeGroupI N} {a b : ℤ} {x : M} {y : N}
    (hx : x ∈ hyperchargeSubmodule rep a) (hy : y ∈ hyperchargeSubmodule rep₂ b) :
    x ⊗ₜ[ℂ] y ∈ hyperchargeSubmodule (rep.tprod rep₂) (a + b) := by
  intro u
  show (TensorProduct.map _ _) _ = _
  rw [TensorProduct.map_tmul, hx u, hy u, TensorProduct.smul_tmul',
    TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_smul,
    mul_comm (((u : ℂ)) ^ b), ← zpow_add₀ (unitary_coe_ne_zero u)]

/-!

## C. Hypercharge-graded representations

-/

/-- A representation of the global gauge group on an algebra is **hypercharge-graded**
  when it acts by algebra automorphisms and its hypercharge weight spaces span.

  Multiplicativity makes the weight spaces a graded monoid; the spanning axiom is the
  genuinely extra condition, since an abstract linear action of `U(1)` need not be
  diagonalizable. Independence of the weight spaces is automatic
  (`hyperchargeSubmodule_iSupIndep`), so together these grade the algebra. -/
class IsHyperchargeGraded (rep : Representation ℂ GaugeGroupI B) : Prop where
  apply_one : ∀ g, rep g 1 = 1
  apply_mul : ∀ (g : GaugeGroupI) (x y : B), rep g (x * y) = rep g x * rep g y
  hyperchargeSpan_eq_top : hyperchargeSpan rep = ⊤

variable (rep : Representation ℂ GaugeGroupI B)

/-- The unit is a charge singlet. -/
lemma one_mem [IsHyperchargeGraded rep] : (1 : B) ∈ hyperchargeSubmodule rep 0 :=
  one_mem_hyperchargeSubmodule fun u => IsHyperchargeGraded.apply_one (GaugeGroupI.ofU1 u)

/-- Hypercharges add under multiplication. -/
lemma mul_mem [IsHyperchargeGraded rep] {m n : ℤ} {x y : B}
    (hx : x ∈ hyperchargeSubmodule rep m) (hy : y ∈ hyperchargeSubmodule rep n) :
    x * y ∈ hyperchargeSubmodule rep (m + n) :=
  mul_mem_hyperchargeSubmodule
    (fun u => IsHyperchargeGraded.apply_mul (GaugeGroupI.ofU1 u)) hx hy

instance [IsHyperchargeGraded rep] : SetLike.GradedMonoid (hyperchargeSubmodule rep) where
  one_mem := one_mem rep
  mul_mem _ _ _ _ hx hy := mul_mem rep hx hy

/-!

## D. Independence of the weight spaces

The weight spaces are independent with no assumption on the representation: each lies in
an eigenspace of the single transformation by `exp i`, and the powers of `exp i` are
pairwise distinct because `π` is irrational.

-/

/-- The unitary scalar `exp i`: a point of the unit circle of infinite order. -/
noncomputable def expI : unitary ℂ :=
  ⟨Complex.exp Complex.I, by
    have hstar : star (Complex.exp Complex.I) = Complex.exp (-Complex.I) := by
      rw [show star (Complex.exp Complex.I)
          = (starRingEnd ℂ) (Complex.exp Complex.I) from rfl, ← Complex.exp_conj,
        Complex.conj_I]
    constructor
    · rw [hstar, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    · rw [hstar, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]⟩

/-- The powers of `exp i` are pairwise distinct: `exp i` is not a root of unity, by the
  irrationality of `π`. -/
lemma expI_zpow_injective : Function.Injective fun n : ℤ => ((expI : ℂ) ^ n) := by
  intro a b hab
  simp only [show ((expI : ℂ)) = Complex.exp Complex.I from rfl,
    ← Complex.exp_int_mul] at hab
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hab
  have hℂ : ((a : ℂ)) = b + k * (2 * (Real.pi : ℂ)) := by
    refine mul_right_cancel₀ Complex.I_ne_zero ?_
    rw [hk]
    ring
  have hℝ : ((a : ℝ)) = b + k * (2 * Real.pi) := by
    have h := congrArg Complex.re hℂ
    simpa using h
  rcases eq_or_ne k 0 with rfl | hk0
  · exact_mod_cast (by simpa using hℝ : ((a : ℝ)) = b)
  · exfalso
    refine irrational_pi ⟨(a - b) / (2 * k), ?_⟩
    have h2k : ((2 * k : ℝ)) ≠ 0 :=
      mul_ne_zero two_ne_zero (Int.cast_ne_zero.mpr hk0)
    push_cast
    rw [div_eq_iff h2k]
    linarith [hℝ]

/-- The hypercharge-`n` weight space lies in the `(exp i) ^ n` eigenspace of the
  transformation by `exp i`. -/
lemma hyperchargeSubmodule_le_eigenspace (rep : Representation ℂ GaugeGroupI M)
    (n : ℤ) :
    hyperchargeSubmodule rep n
      ≤ Module.End.eigenspace (rep (GaugeGroupI.ofU1 expI)) ((expI : ℂ) ^ n) :=
  fun _ hx => Module.End.mem_eigenspace_iff.mpr (hx expI)

/-- **The hypercharge weight spaces are independent**: a decomposition into homogeneous
  parts is unique when it exists. This holds with no assumption on the
  representation. -/
lemma hyperchargeSubmodule_iSupIndep (rep : Representation ℂ GaugeGroupI M) :
    iSupIndep (hyperchargeSubmodule rep) :=
  ((Module.End.eigenspaces_iSupIndep
      (rep (GaugeGroupI.ofU1 expI) : Module.End ℂ M)).comp
    expI_zpow_injective).mono fun n => hyperchargeSubmodule_le_eigenspace rep n

/-!

## E. The grading

-/

/-- **The hypercharge grades the algebra**: the weight spaces of a hypercharge-graded
  representation decompose the algebra as an internal direct sum. -/
theorem hyperchargeSubmodule_isInternal [IsHyperchargeGraded rep] :
    DirectSum.IsInternal (hyperchargeSubmodule rep) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
    ⟨hyperchargeSubmodule_iSupIndep rep,
      IsHyperchargeGraded.hyperchargeSpan_eq_top⟩

/-- The decomposition into hypercharge components. -/
noncomputable instance [IsHyperchargeGraded rep] :
    DirectSum.Decomposition (hyperchargeSubmodule rep) :=
  (hyperchargeSubmodule_isInternal rep).chooseDecomposition

/-- **A hypercharge-graded representation is a graded algebra.** -/
noncomputable instance [IsHyperchargeGraded rep] :
    GradedAlgebra (hyperchargeSubmodule rep) where
  one_mem := one_mem rep
  mul_mem _ _ _ _ hx hy := mul_mem rep hx hy

/-!

## F. The hypercharge projections

-/

/-- The projection onto the part of hypercharge `n`, read off from the hypercharge
  decomposition. The charge-zero projection `hyperchargeProj rep 0` is the projection
  onto the charge singlets. -/
noncomputable def hyperchargeProj [IsHyperchargeGraded rep] (n : ℤ) : B →ₗ[ℂ] B :=
  (hyperchargeSubmodule rep n).subtype ∘ₗ
    DirectSum.component ℂ ℤ (fun n => (hyperchargeSubmodule rep n : Submodule ℂ B)) n ∘ₗ
      (DirectSum.decomposeLinearEquiv (hyperchargeSubmodule rep)).toLinearMap

variable [IsHyperchargeGraded rep]

lemma hyperchargeProj_apply (n : ℤ) (x : B) :
    hyperchargeProj rep n x
      = (DirectSum.decompose (hyperchargeSubmodule rep) x n : B) := rfl

/-- The projection lands in the hypercharge it projects onto. -/
lemma hyperchargeProj_mem (n : ℤ) (x : B) :
    hyperchargeProj rep n x ∈ hyperchargeSubmodule rep n :=
  (DirectSum.decompose (hyperchargeSubmodule rep) x n).2

/-- On an element of hypercharge `n` the hypercharge-`n` projection is the identity. -/
@[simp]
lemma hyperchargeProj_of_mem {n : ℤ} {x : B} (hx : x ∈ hyperchargeSubmodule rep n) :
    hyperchargeProj rep n x = x :=
  DirectSum.decompose_of_mem_same _ hx

/-- On an element of another hypercharge the projection vanishes. -/
lemma hyperchargeProj_of_mem_ne {n m : ℤ} {x : B}
    (hx : x ∈ hyperchargeSubmodule rep m) (hmn : m ≠ n) :
    hyperchargeProj rep n x = 0 :=
  DirectSum.decompose_of_mem_ne _ hx hmn

/-- An element is of hypercharge `n` exactly when the hypercharge-`n` projection fixes
  it. -/
lemma hyperchargeProj_eq_self_iff {n : ℤ} {x : B} :
    hyperchargeProj rep n x = x ↔ x ∈ hyperchargeSubmodule rep n :=
  ⟨fun h => h ▸ hyperchargeProj_mem rep n x, hyperchargeProj_of_mem rep⟩

/-- The projections are idempotent. -/
@[simp]
lemma hyperchargeProj_hyperchargeProj (n : ℤ) (x : B) :
    hyperchargeProj rep n (hyperchargeProj rep n x) = hyperchargeProj rep n x :=
  hyperchargeProj_of_mem rep (hyperchargeProj_mem rep n x)

/-- Distinct projections are orthogonal. -/
lemma hyperchargeProj_hyperchargeProj_of_ne {n m : ℤ} (hmn : m ≠ n) (x : B) :
    hyperchargeProj rep n (hyperchargeProj rep m x) = 0 :=
  hyperchargeProj_of_mem_ne rep (hyperchargeProj_mem rep m x) hmn

end StandardModel
