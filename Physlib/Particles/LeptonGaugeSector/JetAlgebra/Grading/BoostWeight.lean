/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.Invariants.Averages.BoostAverage
/-!
# Grading by boost weight in the Z-direction

The jet algebra is graded by the boost weight, corresponding to how the element scales under a
boost in the Z-direction: `x` has boost weight `k` when `ρ(boostZel t) x = t ^ k • x` for every
`t`.

*Unlike the hypercharge grading, this one is not diagonal on the generators.* The gauge group
acts on each generator by a character, so `hyperchargePoly` could be defined by sending each
generator to `T ^ q` times itself. A boost does not: it mixes the time index with the `z` index,
so `∂_s B_μ` and `∂_s ψ_α` in the coordinate basis are not boost eigenvectors. For instance
`ρ(boostZel t) F_{0x} = ch F_{0x} - sh F_{zx}`. Only the light-cone combinations are homogeneous
— `F_{0x} ∓ F_{zx}` has boost weight `±2` — so a `LaurentPolynomial`-valued grading map in the
style of `Grading/Hypercharge` would first need a light-cone generating set. What is defined
here instead is the grading itself, as the family of weight submodules, which needs no change of
basis.

With this grading we can define the subspace of boost weight zero. Any invariant under the
Lorentz group lies in it, since a boost fixes an invariant.

*How far the grading is established.* Of the two halves of `DirectSum.IsInternal`, independence
is proved — `boostWeightSubmodule_iSupIndep`, from the weight spaces sitting inside the
eigenspaces of a single boost at the distinct eigenvalues `2 ^ k`. Exhaustiveness is reduced to
a single statement: `boostWeightSubalgebra_eq_top_of_forall_ofGenerator` says the homogeneous
elements span everything as soon as each *generator* `[j]ₐ` is a finite sum of boost
eigenvectors, and `boostWeightSubmodule_isInternal_iff` turns spanning into `IsInternal`. So the
whole grading rests on

  `∀ j : JetGenerators, [j]ₐ ∈ boostWeightSubalgebra`,

which is not proved here. The route is to descend to the component spaces, where the boost acts
linearly: `BBoson.JetComponentSpace` is `DerivAlgebraReal ⊗ Module.Dual ℝ BBoson`, and
`DerivAlgebraReal` is a symmetric algebra on `Module.Dual ℝ Lorentz.CoVector`, so — since the
span of eigenvectors is a subalgebra and `repLorentzGroup_apply_ι` and `repLorentzGroup_apply_mul`
are available there — it suffices to give a light-cone eigenbasis of the four-dimensional spaces
`Module.Dual ℝ Lorentz.CoVector` and `Module.Dual ℝ BBoson`, and of the two-dimensional spinor
duals on the fermionic side. No covariance of `jetDeriv` is needed.

The boost weight is bounded by the mass weight: a generator of mass weight `w` carries at most
`w` units of boost weight. A bosonic generator `∂_s B_μ` of mass weight `2(1 + |s|)` has
`1 + |s|` vector indices, each contributing at most `±2`; a fermionic generator `∂_s ψ_α` of
mass weight `3 + 2|s|` has `|s|` vector indices and one spinor index, contributing at most
`2|s| + 1`. So `|boost weight| ≤ mass weight` throughout.

The map `boostAvgZ` is this projection wherever the boost weights that occur are among
`0, ±2, ±4, ±6`: `boostAvgZ` acts on a weight-`k` element by the value at `k` of the
interpolating polynomial `boostAvgZWeight`, which is one at `k = 0` and vanishes at
`k = ±2, ±4, ±6`. On the covariant subalgebra in mass weight eight or less those are the only
weights that occur, so there it is exactly the projection onto boost weight zero. Note that this
is a statement about the *covariant* subalgebra, not about mass weight eight alone: the
mass-weight-eight element `∂_ρ ∂_σ ∂_τ B_μ` reaches boost weight `8`, and `boostAvgZWeight 8` is
not zero.

## i. Overview

The weight submodules are defined by the eigenvector condition, so the multiplicative structure
is immediate: weights add under multiplication and the unit has weight zero. Relating them to
`boostAvgZ` is then a single computation, since `boostAvgZ` is a linear combination of boosts
and each acts on a weight-`k` element by a power of `t`.

## ii. Key results

- `JetAlgebra.boostWeightSubmodule` : the elements of a given boost weight.
- `JetAlgebra.mul_mem_boostWeightSubmodule` : boost weights add under multiplication.
- `JetAlgebra.mem_boostWeightSubmodule_zero_of_isInvariant` : an invariant has boost weight zero.
- `JetAlgebra.boostAvgZ_apply_of_mem` : `boostAvgZ` acts on a weight-`k` element by
  `boostAvgZWeight k`.
- `JetAlgebra.boostAvgZ_apply_of_mem_zero` and `JetAlgebra.boostAvgZ_apply_eq_zero_of_mem` :
  it is the identity on boost weight zero and annihilates weights `±2, ±4, ±6`.
- `JetAlgebra.boostWeightSubmodule_iSupIndep` : the weight spaces are independent.
- `JetAlgebra.boostWeightSubalgebra` : the subalgebra they span.
- `JetAlgebra.boostWeightSubalgebra_eq_top_of_forall_ofGenerator` and
  `JetAlgebra.boostWeightSubmodule_isInternal_iff` : the reduction of the grading to the
  generators.

## iii. Table of contents

- A. The boost-weight submodules
- B. Homogeneous elements
- B'. Independence of the weight submodules
- B''. The span of the homogeneous elements is a subalgebra
- C. The interpolating polynomial of `boostAvgZ`
- D. `boostAvgZ` is the projection onto boost weight zero

-/

@[expose] public section

namespace LeptonGaugeSector
open TensorProduct StandardModel
open scoped minkowskiMatrix PauliMatrix
open Matrix MatrixGroups

namespace JetAlgebra

/-!

## A. The boost-weight submodules

-/

/-- The submodule of elements of boost weight `k`: those scaling by `t ^ k` under the `z`-boost
  with parameter `t`. -/
def boostWeightSubmodule (k : ℤ) : Submodule ℂ JetAlgebra where
  carrier := {x | ∀ (t : ℝ) (ht : t ≠ 0),
    repLorentzGroup (boostZel t ht) x = (((t : ℝ) : ℂ) ^ k) • x}
  add_mem' {a b} ha hb := fun t ht => by rw [map_add, ha t ht, hb t ht, smul_add]
  zero_mem' := fun t ht => by rw [map_zero, smul_zero]
  smul_mem' c x hx := fun t ht => by rw [map_smul, hx t ht, smul_comm]

@[simp]
lemma mem_boostWeightSubmodule {k : ℤ} {x : JetAlgebra} :
    x ∈ boostWeightSubmodule k ↔ ∀ (t : ℝ) (ht : t ≠ 0),
      repLorentzGroup (boostZel t ht) x = (((t : ℝ) : ℂ) ^ k) • x := Iff.rfl

/-- The unit has boost weight zero. -/
lemma one_mem_boostWeightSubmodule : (1 : JetAlgebra) ∈ boostWeightSubmodule 0 :=
  fun t _ => by rw [repLorentzGroup_apply_one, zpow_zero, one_smul]

/-- Boost weights add under multiplication. -/
lemma mul_mem_boostWeightSubmodule {k l : ℤ} {x y : JetAlgebra}
    (hx : x ∈ boostWeightSubmodule k) (hy : y ∈ boostWeightSubmodule l) :
    x * y ∈ boostWeightSubmodule (k + l) := by
  intro t ht
  have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [repLorentzGroup_apply_mul, hx t ht, hy t ht, smul_mul_smul_comm, zpow_add₀ ht']

instance : SetLike.GradedMonoid boostWeightSubmodule where
  one_mem := one_mem_boostWeightSubmodule
  mul_mem _ _ _ _ hx hy := mul_mem_boostWeightSubmodule hx hy

/-- A Lorentz-invariant element has boost weight zero. -/
lemma mem_boostWeightSubmodule_zero_of_isInvariant {x : JetAlgebra} (hx : IsInvariant x) :
    x ∈ boostWeightSubmodule 0 :=
  fun t ht => by rw [hx.2 (boostZel t ht), zpow_zero, one_smul]

/-!

## B. Homogeneous elements

The coordinate components of a field strength are not boost eigenvectors; the light-cone
combinations are. The two components with both indices transverse to the boost — `F_{xy}` — and
the one along it — `F_{0z}` — are invariant.

-/

/-- The light-cone combination `F_{0x} - F_{zx}` has boost weight `2`. -/
lemma fieldStrengthDeriv_lightCone_mem_two :
    fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) -
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) ∈ boostWeightSubmodule 2 := by
  intro t ht
  have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [map_sub, repLorentzGroup_fieldStrengthDeriv_nil, repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ, fieldStrengthDeriv_self,
    mul_zero, zero_mul, mul_one, one_mul, Complex.ofReal_zero, Complex.ofReal_one,
    zero_smul, smul_zero, add_zero, zero_add]
  push_cast
  match_scalars <;> (field_simp; ring)

/-- The light-cone combination `F_{0x} + F_{zx}` has boost weight `-2`. -/
lemma fieldStrengthDeriv_lightCone_mem_neg_two :
    fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) +
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) ∈ boostWeightSubmodule (-2) := by
  intro t ht
  have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [map_add, repLorentzGroup_fieldStrengthDeriv_nil, repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ, fieldStrengthDeriv_self,
    mul_zero, zero_mul, mul_one, one_mul, Complex.ofReal_zero, Complex.ofReal_one,
    zero_smul, smul_zero, add_zero, zero_add]
  push_cast
  match_scalars <;> (field_simp; ring)

/-- The transverse component `F_{xy}` has boost weight zero. -/
lemma fieldStrengthDeriv_transverse_mem_zero :
    fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) ∈ boostWeightSubmodule 0 := by
  intro t ht
  rw [repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ, fieldStrengthDeriv_self,
    mul_zero, zero_mul, mul_one, one_mul, Complex.ofReal_zero, Complex.ofReal_one,
    zero_smul, smul_zero, add_zero, zero_add]
  push_cast
  match_scalars <;> norm_num

/-- The zeroth-order lepton coordinate `ψ_0` has boost weight `-1`. -/
lemma Dψ_nil_zero_mem_neg_one : Dψ [] 0 ∈ boostWeightSubmodule (-1) := by
  intro t ht
  rw [repLorentzGroup_Dψ_nil, boostZel_inv_coe]
  simp only [Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
    Fin.isValue, Complex.star_def, map_zero, star_zero, zero_smul, add_zero,
    Complex.conj_ofReal]
  rw [_root_.zpow_neg, zpow_one, Complex.ofReal_inv]

/-- The zeroth-order lepton coordinate `ψ_1` has boost weight `1`. -/
lemma Dψ_nil_one_mem_one : Dψ [] 1 ∈ boostWeightSubmodule 1 := by
  intro t ht
  rw [repLorentzGroup_Dψ_nil, boostZel_inv_coe]
  simp only [Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
    Fin.isValue, Complex.star_def, map_zero, star_zero, zero_smul, zero_add,
    Complex.conj_ofReal]
  rw [zpow_one]

/-- The zeroth-order conjugate lepton coordinate `ψ̄_0` has boost weight `-1`. -/
lemma Dbarψ_nil_zero_mem_neg_one : Dbarψ [] 0 ∈ boostWeightSubmodule (-1) := by
  intro t ht
  rw [repLorentzGroup_Dbarψ_nil, boostZel_inv_coe]
  simp only [Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
    Fin.isValue, zero_smul, add_zero]
  rw [_root_.zpow_neg, zpow_one, Complex.ofReal_inv]

/-- The zeroth-order conjugate lepton coordinate `ψ̄_1` has boost weight `1`. -/
lemma Dbarψ_nil_one_mem_one : Dbarψ [] 1 ∈ boostWeightSubmodule 1 := by
  intro t ht
  rw [repLorentzGroup_Dbarψ_nil, boostZel_inv_coe]
  simp only [Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
    Fin.isValue, zero_smul, zero_add]
  rw [zpow_one]

/-- The gauge potential in the light-cone direction, `B_0 - B_z`, has boost weight `2`. -/
lemma B_lightCone_mem_two :
    [JetGenerators.dB {} (Sum.inl 0)]ₐ - [JetGenerators.dB {} (Sum.inr 2)]ₐ ∈
      boostWeightSubmodule 2 := by
  intro t ht
  have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [map_sub, repLorentzGroup_B, repLorentzGroup_B]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ, Complex.ofReal_zero, Complex.ofReal_one,
    zero_smul, add_zero, zero_add, one_smul]
  push_cast
  match_scalars <;> (field_simp; ring)

/-- The gauge potential in the other light-cone direction has boost weight `-2`. -/
lemma B_lightCone_mem_neg_two :
    [JetGenerators.dB {} (Sum.inl 0)]ₐ + [JetGenerators.dB {} (Sum.inr 2)]ₐ ∈
      boostWeightSubmodule (-2) := by
  intro t ht
  have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [map_add, repLorentzGroup_B, repLorentzGroup_B]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ, Complex.ofReal_zero, Complex.ofReal_one,
    zero_smul, add_zero, zero_add, one_smul]
  push_cast
  match_scalars <;> (field_simp; ring)

/-!

## B'. Independence of the weight submodules

The weight submodules sit inside the eigenspaces of a single boost, `ρ(boostZel 2)`, at the
pairwise distinct eigenvalues `2 ^ k`. Eigenspaces at distinct eigenvalues are independent, so
the family is independent: an element has at most one decomposition into homogeneous parts.
This is one of the two halves of `DirectSum.IsInternal`; the other, that the weight submodules
span, is not proved here — see the module docstring.

-/

/-- The weight submodule of weight `k` sits inside the `2 ^ k` eigenspace of the boost at
  parameter two. -/
lemma boostWeightSubmodule_le_eigenspace (k : ℤ) :
    boostWeightSubmodule k ≤
      Module.End.eigenspace (repLorentzGroup (boostZel 2 two_ne_zero)) ((2 : ℂ) ^ k) := by
  intro x hx
  rw [Module.End.mem_eigenspace_iff]
  have h := hx 2 two_ne_zero
  norm_num at h ⊢
  exact h

private lemma zpow_two_injective : Function.Injective (fun k : ℤ => ((2 : ℂ) ^ k)) := by
  have hcast : ∀ k : ℤ, ((2 : ℂ) ^ k) = (((2 : ℝ) ^ k : ℝ) : ℂ) := by
    intro k
    rw [Complex.ofReal_zpow]
    norm_num
  intro a b hab
  simp only [hcast] at hab
  exact zpow_right_injective₀ (by norm_num) (by norm_num) (Complex.ofReal_injective hab)

/-- The boost-weight submodules are independent: a decomposition into homogeneous parts is
  unique when it exists. -/
lemma boostWeightSubmodule_iSupIndep : iSupIndep boostWeightSubmodule :=
  ((Module.End.eigenspaces_iSupIndep
      (repLorentzGroup (boostZel 2 two_ne_zero) : Module.End ℂ JetAlgebra)).comp
    zpow_two_injective).mono boostWeightSubmodule_le_eigenspace

/-!

## B''. The span of the homogeneous elements is a subalgebra

-/

/-- The span of the homogeneous elements contains one. -/
lemma one_mem_iSup_boostWeightSubmodule :
    (1 : JetAlgebra) ∈ ⨆ k, boostWeightSubmodule k :=
  Submodule.mem_iSup_of_mem 0 one_mem_boostWeightSubmodule

/-- The span of the homogeneous elements is closed under multiplication. -/
lemma mul_mem_iSup_boostWeightSubmodule {x y : JetAlgebra}
    (hx : x ∈ ⨆ k, boostWeightSubmodule k) (hy : y ∈ ⨆ k, boostWeightSubmodule k) :
    x * y ∈ ⨆ k, boostWeightSubmodule k := by
  induction hx using Submodule.iSup_induction' with
  | mem k a ha =>
    induction hy using Submodule.iSup_induction' with
    | mem l b hb =>
      exact Submodule.mem_iSup_of_mem (k + l) (mul_mem_boostWeightSubmodule ha hb)
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add b c _ _ ihb ihc => rw [mul_add]; exact Submodule.add_mem _ ihb ihc
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add a b _ _ iha ihb => rw [add_mul]; exact Submodule.add_mem _ iha ihb

/-- The homogeneous elements span a subalgebra of the jet algebra. -/
noncomputable def boostWeightSubalgebra : Subalgebra ℂ JetAlgebra :=
  Submodule.toSubalgebra (⨆ k, boostWeightSubmodule k) one_mem_iSup_boostWeightSubmodule
    fun _ _ hx hy => mul_mem_iSup_boostWeightSubmodule hx hy

@[simp]
lemma mem_boostWeightSubalgebra {x : JetAlgebra} :
    x ∈ boostWeightSubalgebra ↔ x ∈ ⨆ k, boostWeightSubmodule k := Iff.rfl

/-- The homogeneous span contains the whole bosonic factor once it contains the generators. -/
private lemma inclB_mem_boostWeightSubalgebra
    (h : ∀ j : JetGenerators, [j]ₐ ∈ boostWeightSubalgebra)
    (a : ℂ ⊗[ℝ] BBoson.JetAlgebra) : inclB a ∈ boostWeightSubalgebra := by
  have hone : ∀ c : BBoson.JetAlgebra,
      inclB ((1 : ℂ) ⊗ₜ[ℝ] c) ∈ boostWeightSubalgebra := by
    intro c
    induction c using SymmetricAlgebra.induction with
    | algebraMap r =>
      rw [show ((1 : ℂ) ⊗ₜ[ℝ] (algebraMap ℝ BBoson.JetAlgebra r) :
            ℂ ⊗[ℝ] BBoson.JetAlgebra) =
          algebraMap ℂ (ℂ ⊗[ℝ] BBoson.JetAlgebra) (algebraMap ℝ ℂ r) from by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
          TensorProduct.tmul_smul, TensorProduct.smul_tmul']
        rfl, AlgHom.commutes]
      exact Subalgebra.algebraMap_mem _ _
    | ι v =>
      have hv : v ∈ Submodule.span ℝ (Set.range BBoson.JetComponentSpace.basis) := by
        rw [BBoson.JetComponentSpace.basis.span_eq]
        trivial
      induction hv using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        obtain ⟨s, μ⟩ := j
        exact h (JetGenerators.dB s μ)
      | zero => simpa using Subalgebra.zero_mem _
      | add u w _ _ ihu ihw =>
        simp only [map_add, TensorProduct.tmul_add]
        exact Subalgebra.add_mem _ ihu ihw
      | smul r u _ ihu =>
        rw [show ((1 : ℂ) ⊗ₜ[ℝ]
            (SymmetricAlgebra.ι ℝ BBoson.JetComponentSpace (r • u)) :
            ℂ ⊗[ℝ] BBoson.JetAlgebra) =
            (algebraMap ℝ ℂ r) • ((1 : ℂ) ⊗ₜ[ℝ]
              SymmetricAlgebra.ι ℝ BBoson.JetComponentSpace u) from by
          rw [map_smul, TensorProduct.tmul_smul, ← algebraMap_smul ℂ r], map_smul]
        exact Subalgebra.smul_mem _ ihu _
    | mul u v ihu ihv =>
      rw [show ((1 : ℂ) ⊗ₜ[ℝ] (u * v) : ℂ ⊗[ℝ] BBoson.JetAlgebra) =
          ((1 : ℂ) ⊗ₜ[ℝ] u) * ((1 : ℂ) ⊗ₜ[ℝ] v) from by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul], map_mul]
      exact Subalgebra.mul_mem _ ihu ihv
    | add u v ihu ihv =>
      simp only [TensorProduct.tmul_add, map_add]
      exact Subalgebra.add_mem _ ihu ihv
  induction a using TensorProduct.induction_on with
  | zero => simpa using Subalgebra.zero_mem _
  | add u v hu hv => rw [map_add]; exact Subalgebra.add_mem _ hu hv
  | tmul z c =>
    rw [show (z ⊗ₜ[ℝ] c : ℂ ⊗[ℝ] BBoson.JetAlgebra) = z • ((1 : ℂ) ⊗ₜ[ℝ] c) from by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul]
    exact Subalgebra.smul_mem _ (hone c) _

/-- The homogeneous span contains the whole fermionic factor once it contains the generators. -/
private lemma inclL_mem_boostWeightSubalgebra
    (h : ∀ j : JetGenerators, [j]ₐ ∈ boostWeightSubalgebra)
    (b : LeptonSinglet.JetAlgebra) : inclL b ∈ boostWeightSubalgebra := by
  have hι : ∀ m : LeptonSinglet.JetComponentSpace,
      inclL (ExteriorAlgebra.ι ℂ m) ∈ boostWeightSubalgebra := by
    intro m
    have hm : m ∈ Submodule.span ℂ (Set.range LeptonSinglet.JetComponentSpace.basis) := by
      rw [LeptonSinglet.JetComponentSpace.basis.span_eq]
      trivial
    induction hm using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      cases j with
      | dψ s α => exact h (JetGenerators.dψ s α)
      | dbarψ s α => exact h (JetGenerators.dbarψ s α)
    | zero => simpa using Subalgebra.zero_mem _
    | add u v _ _ ihu ihv =>
      simp only [map_add]
      exact Subalgebra.add_mem _ ihu ihv
    | smul c u _ ihu =>
      simp only [map_smul]
      exact Subalgebra.smul_mem _ ihu _
  induction b using ExteriorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact Subalgebra.algebraMap_mem _ _
  | ι m => exact hι m
  | mul u v ihu ihv => rw [map_mul]; exact Subalgebra.mul_mem _ ihu ihv
  | add u v ihu ihv => rw [map_add]; exact Subalgebra.add_mem _ ihu ihv

/-- Once every generator is a finite sum of boost eigenvectors, so is every element: the
  homogeneous elements then span the whole jet algebra. -/
theorem boostWeightSubalgebra_eq_top_of_forall_ofGenerator
    (h : ∀ j : JetGenerators, [j]ₐ ∈ boostWeightSubalgebra) : boostWeightSubalgebra = ⊤ := by
  refine Algebra.eq_top_iff.mpr fun x => ?_
  induction x using JetAlgebra.induction_on with
  | zero => exact Subalgebra.zero_mem _
  | add u v hu hv => exact Subalgebra.add_mem _ hu hv
  | tmul a b =>
    rw [tmul_eq_inclB_mul_inclL]
    exact Subalgebra.mul_mem _ (inclB_mem_boostWeightSubalgebra h a)
      (inclL_mem_boostWeightSubalgebra h b)

/-- The decomposition of the jet algebra into boost-weight spaces is internal exactly when the
  homogeneous elements span. Independence always holds, so this isolates the one remaining
  obligation: that every element is a finite sum of boost eigenvectors. -/
theorem boostWeightSubmodule_isInternal_iff :
    DirectSum.IsInternal boostWeightSubmodule ↔ (⨆ k, boostWeightSubmodule k) = ⊤ := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  exact ⟨And.right, fun h => ⟨boostWeightSubmodule_iSupIndep, h⟩⟩

/-- The homogeneous elements span a subalgebra which the boost weights grade internally: the
  decomposition into weights is defined on it and is unique. -/
theorem boostWeightSubmodule_isInternal_of_top
    (h : (⨆ k, boostWeightSubmodule k) = ⊤) : DirectSum.IsInternal boostWeightSubmodule :=
  boostWeightSubmodule_isInternal_iff.mpr h

/-!

## C. The interpolating polynomial of `boostAvgZ`

`boostAvgZ` is a fixed rational combination of the identity and the boosts at `t = 2, 3, 4`
paired with their inverses, so on an element of boost weight `k` it acts by the scalar obtained
by substituting `t ^ k + t ^ (-k)` for each pair. The weights were chosen to make that scalar
one at `k = 0` and zero at `k = 2, 4, 6`; being a function of `t ^ k + t ^ (-k)` it is
automatically even in `k`, so it vanishes at `k = -2, -4, -6` as well.

-/

/-- The scalar by which `boostAvgZ` acts on an element of boost weight `k`. -/
noncomputable def boostAvgZWeight (k : ℤ) : ℂ :=
  (65359/21600 : ℂ)
  + (-133264/99225 : ℂ) * ((2 : ℂ) ^ k + (2 : ℂ) ^ (-k))
  + (384183/1019200 : ℂ) * ((3 : ℂ) ^ k + (3 : ℂ) ^ (-k))
  + (-60416/1289925 : ℂ) * ((4 : ℂ) ^ k + (4 : ℂ) ^ (-k))

/-- The interpolating scalar is even in the weight. -/
lemma boostAvgZWeight_neg (k : ℤ) : boostAvgZWeight (-k) = boostAvgZWeight k := by
  simp only [boostAvgZWeight, neg_neg]
  ring

@[simp] lemma boostAvgZWeight_zero : boostAvgZWeight 0 = 1 := by norm_num [boostAvgZWeight]
@[simp] lemma boostAvgZWeight_two : boostAvgZWeight 2 = 0 := by norm_num [boostAvgZWeight]
@[simp] lemma boostAvgZWeight_four : boostAvgZWeight 4 = 0 := by norm_num [boostAvgZWeight]
@[simp] lemma boostAvgZWeight_six : boostAvgZWeight 6 = 0 := by norm_num [boostAvgZWeight]

/-- The interpolating scalar does *not* vanish at weight eight. This is why `boostAvgZ` is the
  projection only where the boost weights are among `0, ±2, ±4, ±6` — on the covariant
  subalgebra in mass weight eight — and not on all of mass weight eight, which contains the
  weight-eight element `∂_ρ ∂_σ ∂_τ B_μ`. -/
lemma boostAvgZWeight_eight_ne_zero : boostAvgZWeight 8 ≠ 0 := by
  norm_num [boostAvgZWeight]

@[simp] lemma boostAvgZWeight_neg_two : boostAvgZWeight (-2) = 0 := by
  rw [boostAvgZWeight_neg, boostAvgZWeight_two]

@[simp] lemma boostAvgZWeight_neg_four : boostAvgZWeight (-4) = 0 := by
  rw [boostAvgZWeight_neg, boostAvgZWeight_four]

@[simp] lemma boostAvgZWeight_neg_six : boostAvgZWeight (-6) = 0 := by
  rw [boostAvgZWeight_neg, boostAvgZWeight_six]

/-!

## D. `boostAvgZ` is the projection onto boost weight zero

-/

/-- `boostAvgZ` acts on an element of boost weight `k` by the scalar `boostAvgZWeight k`. -/
lemma boostAvgZ_apply_of_mem {k : ℤ} {x : JetAlgebra} (hx : x ∈ boostWeightSubmodule k) :
    boostAvgZ x = boostAvgZWeight k • x := by
  have hinv : ∀ (t : ℝ) (ht : t ≠ 0),
      repLorentzGroup ((boostZel t ht)⁻¹) x = ((((t : ℝ) : ℂ))⁻¹ ^ k) • x := by
    intro t ht
    rw [boostZel_inv, hx t⁻¹ (inv_ne_zero ht), Complex.ofReal_inv]
  simp only [boostAvgZ, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    hx 2 (by norm_num), hx 3 (by norm_num), hx 4 (by norm_num),
    hinv 2 (by norm_num), hinv 3 (by norm_num), hinv 4 (by norm_num),
    boostAvgZWeight]
  push_cast
  match_scalars
  simp only [one_div, _root_.inv_zpow, ← _root_.zpow_neg]
  ring

/-- On boost weight zero `boostAvgZ` is the identity. -/
lemma boostAvgZ_apply_of_mem_zero {x : JetAlgebra} (hx : x ∈ boostWeightSubmodule 0) :
    boostAvgZ x = x := by
  rw [boostAvgZ_apply_of_mem hx, boostAvgZWeight_zero, one_smul]

/-- `boostAvgZ` annihilates the boost weights `±2, ±4, ±6`. -/
lemma boostAvgZ_apply_eq_zero_of_mem {k : ℤ} {x : JetAlgebra} (hx : x ∈ boostWeightSubmodule k)
    (hk : k = 2 ∨ k = 4 ∨ k = 6 ∨ k = -2 ∨ k = -4 ∨ k = -6) : boostAvgZ x = 0 := by
  rw [boostAvgZ_apply_of_mem hx]
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- `boostAvgZ` fixes every Lorentz-invariant element, as the projection onto boost weight zero
  must. -/
lemma boostAvgZ_apply_of_isInvariant {x : JetAlgebra} (hx : IsInvariant x) : boostAvgZ x = x :=
  boostAvgZ_apply_of_mem_zero (mem_boostWeightSubmodule_zero_of_isInvariant hx)

end JetAlgebra

end LeptonGaugeSector

end
