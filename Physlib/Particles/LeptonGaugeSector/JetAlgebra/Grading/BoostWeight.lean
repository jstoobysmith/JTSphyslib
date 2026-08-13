/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.IsInvariant
public import Physlib.Relativity.LorentzGroup.Boosts.WeightGrading
public import Physlib.Relativity.IsLorentzDeriv
public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.MassDim
public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.JetDerivLorentz
/-!
# Grading by boost weight

The jet algebra is graded by the boost weight along each spatial axis: `x` has boost weight `k`
along the `i`-th axis when `ρ(boostAxis i t) x = t ^ k • x` for every `t`. This is proved:
`boostWeightSubmodule_isInternal` decomposes the jet algebra as an internal direct sum of the
weight submodules, and `GradedAlgebra (BoostWeight.boostWeightSubmodule repLorentzGroup i)` is an instance for each of the
three axes.

*It is not the hypercharge construction.* The gauge group acts on every generator by a
character, so `hyperchargePoly` can send each generator to `T ^ q` times itself. A boost does
not: it mixes the time index with the boost direction, so `∂_s B_μ` and `∂_s ψ_α` in the
coordinate basis are *not* boost eigenvectors — for the `z`-boost,
`ρ(boostZel t) F_{0x} = ch F_{0x} - sh F_{zx}`. Only the light-cone combinations are
homogeneous, so a `LaurentPolynomial`-valued grading map in the style of `Grading/Hypercharge`
would need a light-cone generating set. The grading is instead established as the family of
weight submodules, which needs no change of generators.

*How exhaustiveness is proved.* Independence is immediate: the weight spaces sit inside the
eigenspaces of a single boost at the distinct eigenvalues `2 ^ k`. Exhaustiveness descends to
the component spaces, where the boost acts *linearly* and the statement propagates mechanically
— the span of eigenvectors is closed under tensor products, products, symmetric and exterior
algebras, and base change (section B). The recursion bottoms out at four- and two-dimensional
spaces: for `Module.Dual ℝ Lorentz.CoVector`, `Module.Dual ℂ Lorentz.CoℂModule` and
`Module.Dual ℝ BBoson` the eigenvectors are the light-cone combinations `b₀ ∓ b₃`, of weight
`±2`, together with the transverse directions, of weight `0`; on the spinor duals the boost is
already diagonal, with weights `∓1`. No covariance of `jetDeriv` is needed anywhere.

*The three axes.* Everything is proved for the `z`-axis and transported. The axis boosts are
conjugate — a rotation by `π/2` carries the `z`-boost to the `x`- and `y`-boosts
(`boostXel_eq_conj`, `boostYel_eq_conj`) — so `weightSpan_eq_top_of_two` moves the grading
between them without repeating the descent.

With this grading we can single out the subspace of boost weight zero. Any invariant under the
Lorentz group lies in it, for every axis, since a boost fixes an invariant.

The boost weight is bounded by the mass weight: a generator of mass weight `w` carries at most
`w` units of boost weight. A bosonic generator `∂_s B_μ` of mass weight `2(1 + |s|)` has
`1 + |s|` vector indices, each contributing at most `±2`; a fermionic generator `∂_s ψ_α` of
mass weight `3 + 2|s|` has `|s|` vector indices and one spinor index, contributing at most
`2|s| + 1`. So `|boost weight| ≤ mass weight` throughout. Odd weights do occur: a single fermion
sits at `±1`.

The maps `boostAvgX`, `boostAvgY`, `boostAvgZ` are these projections wherever the boost weights
that occur are among `0, ±2, ±4, ±6`: each acts on a weight-`k` element by the value at `k` of
the interpolating polynomial `boostAvgZWeight`, which is one at `k = 0` and vanishes at
`k = ±2, ±4, ±6`. On the covariant subalgebra in mass weight eight or less those are the only
weights that occur, so there each is exactly the projection onto boost weight zero. Note that
this is a statement about the *covariant* subalgebra, not about mass weight eight alone: the
mass-weight-eight element `∂_ρ ∂_σ ∂_τ B_μ` reaches boost weight `8`, and
`boostAvgZWeight_eight_ne_zero`.

## i. Overview

The weight submodules are defined by the eigenvector condition, so the multiplicative structure
is immediate: weights add under multiplication and the unit has weight zero. The work is
exhaustiveness, and it is done once for a general representation and then applied layer by
layer to the spaces the jet algebra is built from.

## ii. Key results

- `JetAlgebra.boostAxis` : the boost along a given spatial axis, and `boostXel_eq_conj`,
  `boostYel_eq_conj` exhibiting the three as conjugate.
- `weightSpan rep i = ⊤` and the transport lemmas of section B : the grading
  propagates along tensor products, products, symmetric and exterior algebras, base change and
  conjugation.
- `JetAlgebra.boostWeightSubmodule` : the elements of a given boost weight along a given axis.
- `JetAlgebra.mul_mem_boostWeightSubmodule` : boost weights add under multiplication.
- `JetAlgebra.mem_boostWeightSubmodule_zero_of_isInvariant` : an invariant has boost weight zero.
- `JetAlgebra.boostWeightSubmodule_isInternal` : the weight submodules decompose the jet algebra
  as an internal direct sum, so `GradedAlgebra (BoostWeight.boostWeightSubmodule repLorentzGroup i)` holds.
- `JetAlgebra.boostAvgAxis_apply_of_mem` : the boost average along an axis acts on a weight-`k`
  element by `boostAvgZWeight k`, hence is the identity on boost weight zero and annihilates
  weights `±2, ±4, ±6`.

## iii. Table of contents

- A. The boosts along the three axes
- B. Boost weights of a general representation
- C. The component spaces are boost-graded
- D. The boost-weight submodules
- E. Homogeneous elements
- F. Independence of the weight submodules
- G. The span of the homogeneous elements is a subalgebra
- H. The interpolating polynomial of the boost averages
- I. The boost averages are the projections onto boost weight zero
- J. The grading

-/

@[expose] public section

namespace LeptonGaugeSector
open TensorProduct StandardModel Lorentz
open scoped minkowskiMatrix PauliMatrix
open Matrix MatrixGroups

namespace JetAlgebra

/-!

## C. The component spaces are boost-graded

Each layer of the jet algebra is graded once the layer below it is: the two four-dimensional
derivative and target spaces by `weightSpan_eq_top_of_lorentzColumns`, the spinor duals directly (the
boost is already diagonal on them), and everything above by the tensor, product, symmetric- and
exterior-algebra transports.

-/

open BoostWeight in
/-- The real dual covectors — the derivative slots — are boost-graded. -/
lemma weightSpan_coVectorDual_eq_top : weightSpan (Lorentz.CoVector.sl2Rep.dual) 2 = ⊤ :=
  weightSpan_eq_top_of_lorentzColumns Lorentz.CoVector.basis.dualBasis fun Λ μ => by
    simpa using Lorentz.CoVector.sl2Rep_dual_dualBasis Λ μ

open BoostWeight in
/-- The complex dual covectors are boost-graded. -/
lemma weightSpan_coℂModuleDual_eq_top : weightSpan (Lorentz.CoℂModule.SL2CRep.dual) 2 = ⊤ :=
  weightSpan_eq_top_of_lorentzColumns Lorentz.complexCoBasis.dualBasis fun Λ μ => by
    simpa using Lorentz.CoℂModule.SL2CRep_dual_dualBasis Λ μ

open BoostWeight in
/-- The dual B-boson target space is boost-graded. -/
lemma weightSpan_bBosonDual_eq_top : weightSpan (BBoson.repLorentzGroup.dual) 2 = ⊤ :=
  weightSpan_eq_top_of_lorentzColumns BBoson.basis.dualBasis fun Λ μ => by
    simpa using BBoson.repLorentzGroup_dual_dualBasis Λ μ

open BoostWeight in
/-- The real algebra of derivative symbols is boost-graded. -/
lemma weightSpan_derivAlgebraReal_eq_top : weightSpan (DerivAlgebraReal.repLorentzGroup) 2 = ⊤ :=
  weightSpan_symmetricAlgebra_eq_top (repV := Lorentz.CoVector.sl2Rep.dual)
    (fun Λ => by
      show (SymmetricAlgebra.lift
        (SymmetricAlgebra.ι ℝ _ ∘ₗ Lorentz.CoVector.sl2Rep.dual Λ)) 1 = 1
      exact map_one _)
    (fun Λ x y => by
      show (SymmetricAlgebra.lift
        (SymmetricAlgebra.ι ℝ _ ∘ₗ Lorentz.CoVector.sl2Rep.dual Λ)) (x * y) = _
      exact map_mul _ _ _)
    (fun Λ x => DerivAlgebraReal.repLorentzGroup_apply_ι Λ x)
    weightSpan_coVectorDual_eq_top

open BoostWeight in
/-- The complex algebra of derivative symbols is boost-graded. -/
lemma weightSpan_derivAlgebraComplex_eq_top :
    weightSpan (DerivAlgebraComplex.repLorentzGroup) 2 = ⊤ :=
  weightSpan_symmetricAlgebra_eq_top (repV := Lorentz.CoℂModule.SL2CRep.dual)
    (fun Λ => DerivAlgebraComplex.repLorentzGroup_apply_one Λ)
    (fun Λ x y => DerivAlgebraComplex.repLorentzGroup_apply_mul Λ x y)
    (fun Λ x => DerivAlgebraComplex.repLorentzGroup_apply_ι Λ x)
    weightSpan_coℂModuleDual_eq_top

open BoostWeight in
/-- The B-boson jet component space is boost-graded. -/
lemma weightSpan_bBosonJetComponentSpace_eq_top :
    weightSpan (BBoson.JetComponentSpace.repLorentzGroup) 2 = ⊤ :=
  weightSpan_tprod_eq_top weightSpan_derivAlgebraReal_eq_top weightSpan_bBosonDual_eq_top

open BoostWeight in
/-- The B-boson jet algebra is boost-graded. -/
lemma weightSpan_bBosonJetAlgebra_eq_top : weightSpan (BBoson.JetAlgebra.repLorentzGroup) 2 = ⊤ :=
  weightSpan_symmetricAlgebra_eq_top (repV := BBoson.JetComponentSpace.repLorentzGroup)
    (fun Λ => by
      show (SymmetricAlgebra.lift
        (SymmetricAlgebra.ι ℝ _ ∘ₗ BBoson.JetComponentSpace.repLorentzGroup Λ)) 1 = 1
      exact map_one _)
    (fun Λ x y => by
      show (SymmetricAlgebra.lift
        (SymmetricAlgebra.ι ℝ _ ∘ₗ BBoson.JetComponentSpace.repLorentzGroup Λ)) (x * y) = _
      exact map_mul _ _ _)
    (fun Λ x => BBoson.JetAlgebra.repLorentzGroup_apply_ι Λ x)
    weightSpan_bBosonJetComponentSpace_eq_top

open BoostWeight in
/-- The complexified B-boson jet algebra is boost-graded. -/
lemma weightSpan_complexBBosonJetAlgebra_eq_top :
    weightSpan (BBoson.JetAlgebra.complexRepLorentzGroup) 2 = ⊤ :=
  weightSpan_baseChange_eq_top (fun _ _ _ => rfl) weightSpan_bBosonJetAlgebra_eq_top


open BoostWeight in
/-- The dual charged-lepton spinors are boost-graded: the boost is already diagonal on them,
  with weights `∓1`. -/
lemma weightSpan_leptonSingletDual_eq_top :
    weightSpan (LeptonSinglet.repLorentzGroup.dual) 2 = ⊤ := by
  refine weightSpan_eq_top_of_basis LeptonSinglet.basis.dualBasis fun α => ?_
  match α with
  | 0 =>
    refine mem_weightSpan_of_mem_boostWeightSubmodule (w := -1) fun t ht => ?_
    rw [show boostAxis 2 t ht = boostZel t ht from rfl,
      LeptonSinglet.repLorentzGroup_dual_dualBasis, boostZel_inv_coe]
    simp only [Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
      Fin.isValue, Complex.star_def, map_zero, zero_smul, add_zero,
      Complex.conj_ofReal]
    rw [_root_.zpow_neg, zpow_one, Complex.ofReal_inv]
    rfl
  | 1 =>
    refine mem_weightSpan_of_mem_boostWeightSubmodule (w := 1) fun t ht => ?_
    rw [show boostAxis 2 t ht = boostZel t ht from rfl,
      LeptonSinglet.repLorentzGroup_dual_dualBasis, boostZel_inv_coe]
    simp only [Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
      Fin.isValue, Complex.star_def, map_zero, zero_smul, zero_add,
      Complex.conj_ofReal]
    rw [zpow_one]
    rfl

open BoostWeight in
/-- The dual conjugate charged-lepton spinors are boost-graded. -/
lemma weightSpan_leptonSingletConjDual_eq_top :
    weightSpan (LeptonSinglet.repLorentzGroup.conj.dual) 2 = ⊤ := by
  refine weightSpan_eq_top_of_basis LeptonSinglet.basis.conj.dualBasis fun α => ?_
  match α with
  | 0 =>
    refine mem_weightSpan_of_mem_boostWeightSubmodule (w := -1) fun t ht => ?_
    rw [show boostAxis 2 t ht = boostZel t ht from rfl,
      LeptonSinglet.repLorentzGroup_conj_dual_dualBasis, boostZel_inv_coe]
    simp only [Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
      Fin.isValue, zero_smul, add_zero]
    rw [_root_.zpow_neg, zpow_one, Complex.ofReal_inv]
    rfl
  | 1 =>
    refine mem_weightSpan_of_mem_boostWeightSubmodule (w := 1) fun t ht => ?_
    rw [show boostAxis 2 t ht = boostZel t ht from rfl,
      LeptonSinglet.repLorentzGroup_conj_dual_dualBasis, boostZel_inv_coe]
    simp only [Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
      Fin.isValue, zero_smul, zero_add]
    rw [zpow_one]
    rfl

open BoostWeight in
/-- The charged-lepton jet component space is boost-graded. -/
lemma weightSpan_leptonJetComponentSpace_eq_top :
    weightSpan (LeptonSinglet.JetComponentSpace.repLorentzGroup) 2 = ⊤ :=
  weightSpan_prod_eq_top (weightSpan_tprod_eq_top weightSpan_derivAlgebraComplex_eq_top weightSpan_leptonSingletDual_eq_top)
    (weightSpan_tprod_eq_top weightSpan_derivAlgebraComplex_eq_top weightSpan_leptonSingletConjDual_eq_top)

open BoostWeight in
/-- The charged-lepton jet algebra is boost-graded. -/
lemma weightSpan_leptonJetAlgebra_eq_top :
    weightSpan (LeptonSinglet.JetAlgebra.repLorentzGroup) 2 = ⊤ :=
  weightSpan_exteriorAlgebra_eq_top (repV := LeptonSinglet.JetComponentSpace.repLorentzGroup)
    (fun Λ => by
      show (ExteriorAlgebra.map (LeptonSinglet.JetComponentSpace.repLorentzGroup Λ)) 1 = 1
      exact map_one _)
    (fun Λ x y => by
      show (ExteriorAlgebra.map (LeptonSinglet.JetComponentSpace.repLorentzGroup Λ)) (x * y) = _
      exact map_mul _ _ _)
    (fun Λ x => by
      show (ExteriorAlgebra.map (LeptonSinglet.JetComponentSpace.repLorentzGroup Λ))
        (ExteriorAlgebra.ι ℂ x) = _
      exact ExteriorAlgebra.map_apply_ι _ _)
    weightSpan_leptonJetComponentSpace_eq_top

open BoostWeight in
/-- The lepton–gauge-sector jet algebra is boost-graded. -/
lemma weightSpan_jetAlgebra_eq_top : weightSpan (repLorentzGroup) 2 = ⊤ :=
  weightSpan_tprod_eq_top weightSpan_complexBBosonJetAlgebra_eq_top weightSpan_leptonJetAlgebra_eq_top

/-- **The lepton–gauge-sector jet algebra is boost-graded**: the Lorentz action is by algebra
  automorphisms, and along every axis the weight spaces span, by the descent of section C
  transported between the axes. -/
instance : BoostWeight.IsBoostGraded (repLorentzGroup) :=
  ⟨repLorentzGroup_apply_one, repLorentzGroup_apply_mul,
    fun i => BoostWeight.weightSpan_eq_top_of_two weightSpan_jetAlgebra_eq_top i⟩

/-!

## D. The boost-weight submodules

-/

variable {i : Fin 3}

/-- The scalar action of a real parameter on the jet algebra, in the form the weight condition
  presents it. -/
private lemma algebraMap_real_complex (t : ℝ) : (algebraMap ℝ ℂ) t = ((t : ℝ) : ℂ) := rfl

/-- A Lorentz-invariant element has boost weight zero, along every axis. -/
lemma mem_boostWeightSubmodule_zero_of_isInvariant {x : JetAlgebra} (hx : IsInvariant x) :
    x ∈ BoostWeight.boostWeightSubmodule repLorentzGroup i 0 :=
  fun t ht => by rw [hx.2 (boostAxis i t ht), zpow_zero, one_smul]

/-!

## E. Homogeneous elements

The coordinate components of the gauge potential are not boost eigenvectors; the light-cone
combinations `B_0 ∓ B_z` are, of weight `±2`. The zeroth-order lepton coordinates are
eigenvectors of weight `∓1`.

-/

/-- The zeroth-order lepton coordinate `ψ_0` has boost weight `-1`. -/
lemma Dψ_nil_zero_mem_neg_one : Dψ [] 0 ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 2 (-1) := by
  intro t ht
  simp only [algebraMap_real_complex]
  rw [boostAxis_two, repLorentzGroup_Dψ_nil, boostZel_inv_coe]
  simp only [Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
    Fin.isValue, Complex.star_def, map_zero, zero_smul, add_zero,
    Complex.conj_ofReal]
  rw [_root_.zpow_neg, zpow_one, Complex.ofReal_inv]

/-- The zeroth-order lepton coordinate `ψ_1` has boost weight `1`. -/
lemma Dψ_nil_one_mem_one : Dψ [] 1 ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 2 1 := by
  intro t ht
  simp only [algebraMap_real_complex]
  rw [boostAxis_two, repLorentzGroup_Dψ_nil, boostZel_inv_coe]
  simp only [Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
    Fin.isValue, Complex.star_def, map_zero, zero_smul, zero_add,
    Complex.conj_ofReal]
  rw [zpow_one]

/-- The zeroth-order conjugate lepton coordinate `ψ̄_0` has boost weight `-1`. -/
lemma Dbarψ_nil_zero_mem_neg_one : Dbarψ [] 0 ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 2 (-1) := by
  intro t ht
  simp only [algebraMap_real_complex]
  rw [boostAxis_two, repLorentzGroup_Dbarψ_nil, boostZel_inv_coe]
  simp only [Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
    Fin.isValue, zero_smul, add_zero]
  rw [_root_.zpow_neg, zpow_one, Complex.ofReal_inv]

/-- The zeroth-order conjugate lepton coordinate `ψ̄_1` has boost weight `1`. -/
lemma Dbarψ_nil_one_mem_one : Dbarψ [] 1 ∈ BoostWeight.boostWeightSubmodule repLorentzGroup 2 1 := by
  intro t ht
  simp only [algebraMap_real_complex]
  rw [boostAxis_two, repLorentzGroup_Dbarψ_nil, boostZel_inv_coe]
  simp only [Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
    Fin.isValue, zero_smul, zero_add]
  rw [zpow_one]

/-- The gauge potential in the light-cone direction, `B_0 - B_z`, has boost weight `2`. -/
lemma B_lightCone_mem_two :
    [JetGenerators.dB {} (Sum.inl 0)]ₐ - [JetGenerators.dB {} (Sum.inr 2)]ₐ ∈
      BoostWeight.boostWeightSubmodule repLorentzGroup 2 2 := by
  intro t ht
  simp only [algebraMap_real_complex]
  have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [map_sub, repLorentzGroup_B, repLorentzGroup_B]
  simp only [boostAxis_two, toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ, Complex.ofReal_zero,
    zero_smul, add_zero, zero_add]
  push_cast
  match_scalars <;> (field_simp; ring)

/-- The gauge potential in the other light-cone direction has boost weight `-2`. -/
lemma B_lightCone_mem_neg_two :
    [JetGenerators.dB {} (Sum.inl 0)]ₐ + [JetGenerators.dB {} (Sum.inr 2)]ₐ ∈
      BoostWeight.boostWeightSubmodule repLorentzGroup 2 (-2) := by
  intro t ht
  simp only [algebraMap_real_complex]
  have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [map_add, repLorentzGroup_B, repLorentzGroup_B]
  simp only [boostAxis_two, toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ, Complex.ofReal_zero,
    zero_smul, add_zero, zero_add]
  push_cast
  match_scalars <;> (field_simp; ring)

/-!

## F. Independence of the weight submodules

The weight submodules sit inside the eigenspaces of a single boost, `ρ(boostZel 2)`, at the
pairwise distinct eigenvalues `2 ^ k`. Eigenspaces at distinct eigenvalues are independent, so
the family is independent: an element has at most one decomposition into homogeneous parts.
This is one of the two halves of `DirectSum.IsInternal`; the other, that the weight submodules
span, is section C.

-/

/-!

## G. The span of the homogeneous elements is a subalgebra

-/

/-- The homogeneous span contains the whole bosonic factor once it contains the generators. -/
private lemma inclB_mem_boostWeightSubalgebra
    (h : ∀ j : JetGenerators, [j]ₐ ∈ BoostWeight.subalgebra repLorentzGroup i)
    (a : ℂ ⊗[ℝ] BBoson.JetAlgebra) : inclB a ∈ BoostWeight.subalgebra repLorentzGroup i := by
  have hone : ∀ c : BBoson.JetAlgebra,
      inclB ((1 : ℂ) ⊗ₜ[ℝ] c) ∈ BoostWeight.subalgebra repLorentzGroup i := by
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
      | zero => simp
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
  | zero => simp
  | add u v hu hv => rw [map_add]; exact Subalgebra.add_mem _ hu hv
  | tmul z c =>
    rw [show (z ⊗ₜ[ℝ] c : ℂ ⊗[ℝ] BBoson.JetAlgebra) = z • ((1 : ℂ) ⊗ₜ[ℝ] c) from by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul]
    exact Subalgebra.smul_mem _ (hone c) _

/-- The homogeneous span contains the whole fermionic factor once it contains the generators. -/
private lemma inclL_mem_boostWeightSubalgebra
    (h : ∀ j : JetGenerators, [j]ₐ ∈ BoostWeight.subalgebra repLorentzGroup i)
    (b : LeptonSinglet.JetAlgebra) : inclL b ∈ BoostWeight.subalgebra repLorentzGroup i := by
  have hι : ∀ m : LeptonSinglet.JetComponentSpace,
      inclL (ExteriorAlgebra.ι ℂ m) ∈ BoostWeight.subalgebra repLorentzGroup i := by
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
    | zero => simp
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
    (h : ∀ j : JetGenerators, [j]ₐ ∈ BoostWeight.subalgebra repLorentzGroup i) :
    BoostWeight.subalgebra repLorentzGroup i = ⊤ := by
  refine Algebra.eq_top_iff.mpr fun x => ?_
  induction x using JetAlgebra.induction_on with
  | zero => exact Subalgebra.zero_mem _
  | add u v hu hv => exact Subalgebra.add_mem _ hu hv
  | tmul a b =>
    rw [tmul_eq_inclB_mul_inclL]
    exact Subalgebra.mul_mem _ (inclB_mem_boostWeightSubalgebra h a)
      (inclL_mem_boostWeightSubalgebra h b)

/-!

## J. The grading

The weight submodules are independent (`BoostWeight.boostWeightSubmodule_iSupIndep repLorentzGroup`) and, by the descent
through the component spaces of section C transported along section A, they span. So they
decompose the jet algebra internally along every axis, and together with the graded-monoid
structure of section D they make it a graded algebra three times over.

-/

/-- Every generator is a finite sum of boost eigenvectors, for every axis. -/
theorem ofGenerator_mem_boostWeightSubalgebra (i : Fin 3) (j : JetGenerators) :
    [j]ₐ ∈ BoostWeight.subalgebra repLorentzGroup i := by
  rw [BoostWeight.mem_subalgebra, BoostWeight.iSup_boostWeightSubmodule_eq_top repLorentzGroup]
  trivial

/-!

## K. The projection onto a boost weight

The grading of section J writes every element as a *unique* finite sum of homogeneous ones, so it
supplies a projection onto each weight, `BoostWeight.boostProj repLorentzGroup i k` — in particular onto boost weight zero,
where the invariants live.

The projection is exact, for every weight and every element. What it is not is a formula in the
group action: it is defined through the decomposition, so nothing here says it preserves a
subspace merely because that subspace is carried to itself by the Lorentz action. A combination
of finitely many boosts would give that for free, but only interpolates the weight-zero
projection correctly across a bounded range of weights.

-/

/-- An invariant is fixed by the weight-zero projection, along every axis. -/
lemma boostProj_zero_of_isInvariant (i : Fin 3) {x : JetAlgebra} (hx : IsInvariant x) :
    BoostWeight.boostProj repLorentzGroup i 0 x = x :=
  BoostWeight.boostProj_of_mem repLorentzGroup (mem_boostWeightSubmodule_zero_of_isInvariant hx)

/-- An invariant has no component of nonzero weight. -/
lemma boostProj_of_isInvariant_ne {i : Fin 3} {k : ℤ} (hk : (0 : ℤ) ≠ k) {x : JetAlgebra}
    (hx : IsInvariant x) : BoostWeight.boostProj repLorentzGroup i k x = 0 :=
  BoostWeight.boostProj_of_mem_ne repLorentzGroup (mem_boostWeightSubmodule_zero_of_isInvariant hx) hk

/-!

## L. The jet derivatives are a Lorentz derivative

The covariance `repLorentzGroup_jetDeriv` makes the jet derivatives an instance of
`Lorentz.IsLorentzDeriv`. The weight shifts of the light-cone combinations, the weight
preservation of the transverse derivatives, and the boost projections of the span of all
jet derivatives of a submodule (`IsLorentzDeriv.boostProj_map_submodule_x/y/z`) are
inherited from the general theory.

-/

/-- The jet derivatives transform as a Lorentz covector. -/
instance : IsLorentzDeriv repLorentzGroup jetDeriv where
  rep_deriv {Λ μ x} := repLorentzGroup_jetDeriv Λ μ x

/-!

## The multiplication of submodules

-/

/-- A submodule product with a bosonic left factor commutes. -/
lemma mul_comm_of_le_bosonic {A B : Submodule ℂ JetAlgebra} (hA : A ≤ bosonic) :
    A * B = B * A := by
  refine le_antisymm (Submodule.mul_le.2 fun a ha b hb => ?_)
    (Submodule.mul_le.2 fun b hb a ha => ?_)
  · rw [mul_comm_of_mem_bosonic (hA ha)]
    exact Submodule.mul_mem_mul hb ha
  · rw [← mul_comm_of_mem_bosonic (hA ha)]
    exact Submodule.mul_mem_mul ha hb

end JetAlgebra

end LeptonGaugeSector

end
