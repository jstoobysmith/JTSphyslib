/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.Particles.StandardModel.GaugeBosons.Gluons
public import Physlib.Particles.StandardModel.GaugeBosons.Gluons.JetCompleteness.DiagonalJet
/-!
# All eight colour directions

## i. Overview

This file proves that the single colour direction `H = diag(1, -1, 0)` realized by the `DiagonalJet`
diagonal jet
generates the whole physical colour carrier, and that based gauge jets therefore realize an
arbitrary traceless hermitian translation.

Three things are produced.

* `colourBasis` — an explicit `Basis (Fin 8) ℝ` of the traceless hermitian `3 × 3` matrices. This
  is stronger than the "spanning family" alternative allowed by the proof strategy, and it is the
  form later modules need: `SymmetricAlgebra.equivMvPolynomial` requires a `Basis`, so the colour
  index type of the jet coordinate carrier has to come from here.
* `colourBasis_eq_adjointAction` — every basis vector is a *single* constant `SU(3)` conjugate of
  `H`. No simplicity or irreducibility theory for `su(3)` is used; the six constant matrices are
  written down.
* `exists_based_mcCoeff` — for every traceless hermitian `X` and every spacetime direction `μ`
  there is a *based* gauge jet whose Maurer–Cartan coefficient is `X` in the direction `μ` and `0`
  in every other direction. This is the translation input the layerwise elimination of
  `FiniteCompleteness`, `HighestLayer` and
  `FiniteHeight` consumes.

## ii. The conjugation chain

Only one of the six constant matrices has irrational entries, the `π/4` rotation in the `(0,1)`
block; everything else is a permutation or a diagonal phase. The chain is

```text
H --Ad(cyc2)--> E₂
H --Ad(u01)--> X₀₁ --Ad(d01)--> Y₀₁
X₀₁ --Ad(cyc)--> X₀₂ --Ad(d02)--> Y₀₂
X₀₂ --Ad(cyc)--> X₁₂ --Ad(d12)--> Y₁₂
```

The eigenvalues of `H` are `1, -1, 0`, so every single conjugate of `H` has those eigenvalues; the
basis is chosen to consist of such matrices, which is why each basis vector is one conjugate rather
than a combination.

-/

@[expose] public section

namespace StandardModel

open Matrix MvPowerSeries JetRing Module

namespace SU3Jet

/-!

## A. The colour carrier

The physical colour carrier in the traceless-Hermitian convention is the real vector space of
traceless hermitian `3 × 3` matrices.

-/

/-- The traceless hermitian `3 × 3` matrices: the Lie algebra `su(3)`. -/
def ColourSpace : Submodule ℝ (selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ)) where
  carrier := {A | trace (A : Matrix (Fin 3) (Fin 3) ℂ) = 0}
  add_mem' {A B} hA hB := by
    simp only [Set.mem_setOf_eq, AddSubgroup.coe_add, Matrix.trace_add] at *
    rw [hA, hB, add_zero]
  zero_mem' := by
    simp only [Set.mem_setOf_eq, ZeroMemClass.coe_zero, Matrix.trace_zero]
  smul_mem' r A hA := by
    simp only [Set.mem_setOf_eq, selfAdjoint.val_smul, Matrix.trace_smul] at *
    rw [hA, smul_zero]

@[simp]
lemma mem_ColourSpace {A : selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ)} :
    A ∈ ColourSpace ↔ trace (A : Matrix (Fin 3) (Fin 3) ℂ) = 0 := Iff.rfl

/-!

## B. The eight colour matrices

-/

/-- `E₁ = diag(1, -1, 0)`, the direction realized directly by the `DiagonalJet` jet. -/
def cm0 : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; 0, -1, 0; 0, 0, 0]
/-- `E₂ = diag(0, 1, -1)`. -/
def cm1 : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 0; 0, 1, 0; 0, 0, -1]
/-- `X₀₁`. -/
def cm2 : Matrix (Fin 3) (Fin 3) ℂ := !![0, 1, 0; 1, 0, 0; 0, 0, 0]
/-- `Y₀₁`. -/
noncomputable def cm3 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, -Complex.I, 0; Complex.I, 0, 0; 0, 0, 0]
/-- `X₀₂`. -/
def cm4 : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 1; 0, 0, 0; 1, 0, 0]
/-- `Y₀₂`. -/
noncomputable def cm5 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, -Complex.I; 0, 0, 0; Complex.I, 0, 0]
/-- `X₁₂`. -/
def cm6 : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 0; 0, 0, 1; 0, 1, 0]
/-- `Y₁₂`. -/
noncomputable def cm7 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 0; 0, 0, -Complex.I; 0, Complex.I, 0]

/-- The `DiagonalJet` colour direction is the first colour matrix. -/
lemma colourMat_eq_cm0 : colourMat = cm0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [colourMat, cm0]

private lemma mem_sa (M : Matrix (Fin 3) (Fin 3) ℂ)
    (h : ∀ i j, (starRingEnd ℂ) (M j i) = M i j) :
    M ∈ selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ) := by
  rw [selfAdjoint.mem_iff]
  ext i j
  rw [Matrix.star_apply]
  exact h i j

lemma cm0_mem : cm0 ∈ selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ) :=
  mem_sa _ fun i j => by fin_cases i <;> fin_cases j <;> simp [cm0]
lemma cm1_mem : cm1 ∈ selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ) :=
  mem_sa _ fun i j => by fin_cases i <;> fin_cases j <;> simp [cm1]
lemma cm2_mem : cm2 ∈ selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ) :=
  mem_sa _ fun i j => by fin_cases i <;> fin_cases j <;> simp [cm2]
lemma cm3_mem : cm3 ∈ selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ) :=
  mem_sa _ fun i j => by fin_cases i <;> fin_cases j <;> simp [cm3]
lemma cm4_mem : cm4 ∈ selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ) :=
  mem_sa _ fun i j => by fin_cases i <;> fin_cases j <;> simp [cm4]
lemma cm5_mem : cm5 ∈ selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ) :=
  mem_sa _ fun i j => by fin_cases i <;> fin_cases j <;> simp [cm5]
lemma cm6_mem : cm6 ∈ selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ) :=
  mem_sa _ fun i j => by fin_cases i <;> fin_cases j <;> simp [cm6]
lemma cm7_mem : cm7 ∈ selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ) :=
  mem_sa _ fun i j => by fin_cases i <;> fin_cases j <;> simp [cm7]

/-- The eight colour directions, as hermitian matrices. -/
noncomputable def colourVec : Fin 8 → selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ) :=
  ![⟨cm0, cm0_mem⟩, ⟨cm1, cm1_mem⟩, ⟨cm2, cm2_mem⟩, ⟨cm3, cm3_mem⟩,
    ⟨cm4, cm4_mem⟩, ⟨cm5, cm5_mem⟩, ⟨cm6, cm6_mem⟩, ⟨cm7, cm7_mem⟩]

lemma colourVec_mem (k : Fin 8) : colourVec k ∈ ColourSpace := by
  fin_cases k <;>
    simp [colourVec, ColourSpace, cm0, cm1, cm2, cm3, cm4, cm5, cm6, cm7,
      Matrix.trace_fin_three]

/-!

## C. Coordinates and the basis

-/

/-- The eight real coordinates of a hermitian matrix relative to the colour directions. -/
noncomputable def colourCoord :
    selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ) →ₗ[ℝ] (Fin 8 → ℝ) where
  toFun A := ![((A : Matrix (Fin 3) (Fin 3) ℂ) 0 0).re, -((A : Matrix (Fin 3) (Fin 3) ℂ) 2 2).re,
    ((A : Matrix (Fin 3) (Fin 3) ℂ) 0 1).re, -((A : Matrix (Fin 3) (Fin 3) ℂ) 0 1).im,
    ((A : Matrix (Fin 3) (Fin 3) ℂ) 0 2).re, -((A : Matrix (Fin 3) (Fin 3) ℂ) 0 2).im,
    ((A : Matrix (Fin 3) (Fin 3) ℂ) 1 2).re, -((A : Matrix (Fin 3) (Fin 3) ℂ) 1 2).im]
  map_add' A B := by
    funext k
    fin_cases k <;> simp [Matrix.add_apply] <;> ring
  map_smul' r A := by
    funext k
    fin_cases k <;>
      simp [selfAdjoint.val_smul, Matrix.smul_apply, Complex.real_smul, Complex.mul_re,
        Complex.mul_im]

/-- The hermitian matrix with prescribed colour coordinates. -/
noncomputable def colourMk : (Fin 8 → ℝ) →ₗ[ℝ] selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ) :=
  Fintype.linearCombination ℝ colourVec

lemma colourMk_apply (c : Fin 8 → ℝ) : colourMk c = ∑ k, c k • colourVec k :=
  Fintype.linearCombination_apply _ _ c

lemma colourMk_mem (c : Fin 8 → ℝ) : colourMk c ∈ ColourSpace := by
  rw [colourMk_apply]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (colourVec_mem k)

lemma colourMk_val (c : Fin 8 → ℝ) (i j : Fin 3) :
    ((colourMk c : selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ)) : Matrix (Fin 3) (Fin 3) ℂ) i j =
      ∑ k, (c k : ℂ) * (colourVec k : Matrix (Fin 3) (Fin 3) ℂ) i j := by
  rw [colourMk_apply]
  rw [show ((∑ k, c k • colourVec k : selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ)) :
      Matrix (Fin 3) (Fin 3) ℂ) = ∑ k, c k • (colourVec k : Matrix (Fin 3) (Fin 3) ℂ) from by
    simp [selfAdjoint.val_smul]]
  rw [Matrix.sum_apply]
  exact Finset.sum_congr rfl fun k _ => by
    rw [Matrix.smul_apply, Complex.real_smul]

/-- The entries of the hermitian matrix built from eight real coordinates. -/
lemma colourMk_entries (c : Fin 8 → ℝ) :
    ((colourMk c : selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ)) : Matrix (Fin 3) (Fin 3) ℂ) =
      !![(c 0 : ℂ), (c 2 : ℂ) - (c 3 : ℂ) * Complex.I, (c 4 : ℂ) - (c 5 : ℂ) * Complex.I;
         (c 2 : ℂ) + (c 3 : ℂ) * Complex.I, -(c 0 : ℂ) + (c 1 : ℂ),
           (c 6 : ℂ) - (c 7 : ℂ) * Complex.I;
         (c 4 : ℂ) + (c 5 : ℂ) * Complex.I, (c 6 : ℂ) + (c 7 : ℂ) * Complex.I, -(c 1 : ℂ)] := by
  ext i j
  rw [colourMk_val]
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_eight, colourVec, cm0, cm1, cm2, cm3, cm4, cm5, cm6, cm7] <;> ring

lemma colourCoord_colourMk (c : Fin 8 → ℝ) : colourCoord (colourMk c) = c := by
  funext k
  fin_cases k <;>
    simp [colourCoord, colourMk_entries]

lemma colourMk_colourCoord {A : selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ)} (hA : A ∈ ColourSpace) :
    colourMk (colourCoord A) = A := by
  have hAs : star (A : Matrix (Fin 3) (Fin 3) ℂ) = (A : Matrix (Fin 3) (Fin 3) ℂ) :=
    selfAdjoint.mem_iff.mp A.2
  have hentry : ∀ i j, star ((A : Matrix (Fin 3) (Fin 3) ℂ) j i) =
      (A : Matrix (Fin 3) (Fin 3) ℂ) i j := by
    intro i j
    have h := congrArg (fun N : Matrix (Fin 3) (Fin 3) ℂ => N i j) hAs
    simpa [Matrix.star_apply] using h
  have hre : ∀ i j, ((A : Matrix (Fin 3) (Fin 3) ℂ) j i).re =
      ((A : Matrix (Fin 3) (Fin 3) ℂ) i j).re := by
    intro i j
    have := congrArg Complex.re (hentry i j)
    simpa using this
  have him : ∀ i j, ((A : Matrix (Fin 3) (Fin 3) ℂ) j i).im =
      -((A : Matrix (Fin 3) (Fin 3) ℂ) i j).im := by
    intro i j
    have := congrArg Complex.im (hentry i j)
    simp at this
    linarith
  have hdiagim : ∀ i, ((A : Matrix (Fin 3) (Fin 3) ℂ) i i).im = 0 := by
    intro i
    have := him i i
    linarith
  have htrre : ((A : Matrix (Fin 3) (Fin 3) ℂ) 0 0).re +
      ((A : Matrix (Fin 3) (Fin 3) ℂ) 1 1).re + ((A : Matrix (Fin 3) (Fin 3) ℂ) 2 2).re = 0 := by
    have h := mem_ColourSpace.mp hA
    rw [Matrix.trace_fin_three] at h
    have := congrArg Complex.re h
    simpa using this
  apply Subtype.ext
  rw [colourMk_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (apply Complex.ext <;>
      simp [colourCoord] <;>
      linarith [hre 0 1, hre 0 2, hre 1 2, him 0 1, him 0 2, him 1 2,
        hdiagim 0, hdiagim 1, hdiagim 2, htrre])

/-- The colour carrier is eight-dimensional, with explicit coordinates. -/
noncomputable def colourEquiv : ColourSpace ≃ₗ[ℝ] (Fin 8 → ℝ) where
  toFun A := colourCoord (A : selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ))
  invFun c := ⟨colourMk c, colourMk_mem c⟩
  map_add' A B := by simp
  map_smul' r A := by simp
  left_inv A := Subtype.ext (colourMk_colourCoord A.2)
  right_inv c := colourCoord_colourMk c

/-- **An explicit basis of the colour carrier.** Eight traceless hermitian matrices, with
  coordinates given by the real and imaginary parts of the entries. -/
noncomputable def colourBasis : Basis (Fin 8) ℝ ColourSpace :=
  Basis.ofEquivFun colourEquiv

lemma colourBasis_apply (k : Fin 8) :
    ((colourBasis k : ColourSpace) : selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ)) = colourVec k := by
  rw [colourBasis, Basis.coe_ofEquivFun]
  show (colourEquiv.symm (Pi.single k 1) : selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ)) = _
  show colourMk (Pi.single k 1) = _
  rw [colourMk, Fintype.linearCombination_apply_single, one_smul]

/-!

## D. The six constant gauge matrices

-/

/-- `1/√2`, as a complex scalar. -/
noncomputable def rt : ℂ := ((Real.sqrt 2 / 2 : ℝ) : ℂ)

@[simp]
lemma rt_mul_rt : rt * rt = 1 / 2 := by
  have h : (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = 1 / 2 := by
    rw [show Real.sqrt 2 / 2 * (Real.sqrt 2 / 2) = Real.sqrt 2 * Real.sqrt 2 / 4 by ring,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [rt, ← Complex.ofReal_mul, h]
  norm_num

@[simp]
lemma star_rt : star rt = rt := by
  rw [rt, Complex.star_def, Complex.conj_ofReal]

@[simp]
lemma conj_rt : (starRingEnd ℂ) rt = rt := star_rt

@[simp]
lemma rt_sq : rt ^ 2 = 1 / 2 := by rw [pow_two]; exact rt_mul_rt

/-- The cyclic permutation matrix. -/
def gcyc : Matrix (Fin 3) (Fin 3) ℂ := !![0, 1, 0; 0, 0, 1; 1, 0, 0]
/-- The square of the cyclic permutation matrix. -/
def gcyc2 : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 1; 1, 0, 0; 0, 1, 0]
/-- The `π/4` rotation in the `(0,1)` block: the only irrational constant needed. -/
noncomputable def g01 : Matrix (Fin 3) (Fin 3) ℂ := !![rt, -rt, 0; rt, rt, 0; 0, 0, 1]
/-- The diagonal phase `diag(1, i, -i)`. -/
noncomputable def d01 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0; 0, Complex.I, 0; 0, 0, -Complex.I]
/-- The diagonal phase `diag(1, -i, i)`. -/
noncomputable def d02 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0; 0, -Complex.I, 0; 0, 0, Complex.I]
/-- The diagonal phase `diag(-i, 1, i)`. -/
noncomputable def d12 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-Complex.I, 0, 0; 0, 1, 0; 0, 0, Complex.I]

private lemma mem_su3 (M : Matrix (Fin 3) (Fin 3) ℂ) (hu : M * star M = 1) (hd : M.det = 1) :
    M ∈ specialUnitaryGroup (Fin 3) ℂ :=
  mem_specialUnitaryGroup_iff.mpr ⟨mem_unitaryGroup_iff.mpr hu, hd⟩

lemma gcyc_mem : gcyc ∈ specialUnitaryGroup (Fin 3) ℂ := by
  refine mem_su3 _ ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gcyc, Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply]
  · simp [gcyc, Matrix.det_fin_three]

lemma gcyc2_mem : gcyc2 ∈ specialUnitaryGroup (Fin 3) ℂ := by
  refine mem_su3 _ ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gcyc2, Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply]
  · simp [gcyc2, Matrix.det_fin_three]

lemma g01_mem : g01 ∈ specialUnitaryGroup (Fin 3) ℂ := by
  refine mem_su3 _ ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [g01, Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply] <;>
      all_goals ring_nf
  · rw [g01, Matrix.det_fin_three]
    simp; ring_nf

lemma d01_mem : d01 ∈ specialUnitaryGroup (Fin 3) ℂ := by
  refine mem_su3 _ ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [d01, Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply, Complex.conj_I]
  · simp [d01, Matrix.det_fin_three, Complex.I_mul_I]

lemma d02_mem : d02 ∈ specialUnitaryGroup (Fin 3) ℂ := by
  refine mem_su3 _ ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [d02, Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply, Complex.conj_I]
  · simp [d02, Matrix.det_fin_three, Complex.I_mul_I]

lemma d12_mem : d12 ∈ specialUnitaryGroup (Fin 3) ℂ := by
  refine mem_su3 _ ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [d12, Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply, Complex.conj_I]
  · simp [d12, Matrix.det_fin_three, Complex.I_mul_I]

/-- The six constant gauge matrices as elements of `SU(3)`. -/
noncomputable def ucyc : specialUnitaryGroup (Fin 3) ℂ := ⟨gcyc, gcyc_mem⟩
/-- `cyc²` as an element of `SU(3)`. -/
noncomputable def ucyc2 : specialUnitaryGroup (Fin 3) ℂ := ⟨gcyc2, gcyc2_mem⟩
/-- The `π/4` rotation as an element of `SU(3)`. -/
noncomputable def u01 : specialUnitaryGroup (Fin 3) ℂ := ⟨g01, g01_mem⟩
/-- `diag(1, i, -i)` as an element of `SU(3)`. -/
noncomputable def p01 : specialUnitaryGroup (Fin 3) ℂ := ⟨d01, d01_mem⟩
/-- `diag(1, -i, i)` as an element of `SU(3)`. -/
noncomputable def p02 : specialUnitaryGroup (Fin 3) ℂ := ⟨d02, d02_mem⟩
/-- `diag(-i, 1, i)` as an element of `SU(3)`. -/
noncomputable def p12 : specialUnitaryGroup (Fin 3) ℂ := ⟨d12, d12_mem⟩

/-!

## E. The conjugation chain

-/

private lemma conj_eq (u : specialUnitaryGroup (Fin 3) ℂ)
    (A : selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ)) (B : selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ))
    (h : (u : Matrix (Fin 3) (Fin 3) ℂ) * (A : Matrix (Fin 3) (Fin 3) ℂ) *
      ((u : Matrix (Fin 3) (Fin 3) ℂ))ᴴ = (B : Matrix (Fin 3) (Fin 3) ℂ)) :
    Gluon.adjointAction u A = B :=
  Subtype.ext (by rw [Gluon.adjointAction_apply_coe]; exact h)

lemma adjointAction_ucyc2_cm0 :
    Gluon.adjointAction ucyc2 ⟨cm0, cm0_mem⟩ = ⟨cm1, cm1_mem⟩ := by
  refine conj_eq _ _ _ ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ucyc2, gcyc2, cm0, cm1, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.conjTranspose_apply]

lemma adjointAction_u01_cm0 :
    Gluon.adjointAction u01 ⟨cm0, cm0_mem⟩ = ⟨cm2, cm2_mem⟩ := by
  refine conj_eq _ _ _ ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u01, g01, cm0, cm2, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.conjTranspose_apply] <;>
    all_goals ring_nf

lemma adjointAction_p01_cm2 :
    Gluon.adjointAction p01 ⟨cm2, cm2_mem⟩ = ⟨cm3, cm3_mem⟩ := by
  refine conj_eq _ _ _ ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [p01, d01, cm2, cm3, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.conjTranspose_apply, Complex.conj_I]

lemma adjointAction_ucyc_cm2 :
    Gluon.adjointAction ucyc ⟨cm2, cm2_mem⟩ = ⟨cm4, cm4_mem⟩ := by
  refine conj_eq _ _ _ ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ucyc, gcyc, cm2, cm4, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.conjTranspose_apply]

lemma adjointAction_p02_cm4 :
    Gluon.adjointAction p02 ⟨cm4, cm4_mem⟩ = ⟨cm5, cm5_mem⟩ := by
  refine conj_eq _ _ _ ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [p02, d02, cm4, cm5, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.conjTranspose_apply, Complex.conj_I]

lemma adjointAction_ucyc_cm4 :
    Gluon.adjointAction ucyc ⟨cm4, cm4_mem⟩ = ⟨cm6, cm6_mem⟩ := by
  refine conj_eq _ _ _ ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ucyc, gcyc, cm4, cm6, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.conjTranspose_apply]

lemma adjointAction_p12_cm6 :
    Gluon.adjointAction p12 ⟨cm6, cm6_mem⟩ = ⟨cm7, cm7_mem⟩ := by
  refine conj_eq _ _ _ ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [p12, d12, cm6, cm7, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.conjTranspose_apply, Complex.conj_I]

/-- The constant `SU(3)` element carrying `H = diag(1, -1, 0)` to the `k`-th colour direction. -/
noncomputable def colourConj : Fin 8 → specialUnitaryGroup (Fin 3) ℂ :=
  ![1, ucyc2, u01, p01 * u01, ucyc * u01, p02 * (ucyc * u01),
    ucyc * (ucyc * u01), p12 * (ucyc * (ucyc * u01))]

/-- **Every colour direction is a single constant conjugate of the `DiagonalJet` direction.** No
  simplicity
  or irreducibility theory for `su(3)` is used: the six constant matrices are explicit. -/
lemma colourBasis_eq_adjointAction (k : Fin 8) :
    Gluon.adjointAction (colourConj k) colourH =
      ((colourBasis k : ColourSpace) : selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ)) := by
  have hH : (colourH : selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ)) = ⟨cm0, cm0_mem⟩ :=
    Subtype.ext colourMat_eq_cm0
  have hmul : ∀ (u v : specialUnitaryGroup (Fin 3) ℂ)
      (A : selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ)),
      Gluon.adjointAction (u * v) A = Gluon.adjointAction u (Gluon.adjointAction v A) := by
    intro u v A
    rw [Gluon.adjointAction_mul]
    rfl
  simp only [colourBasis_apply]
  fin_cases k
  · show Gluon.adjointAction 1 colourH = colourVec 0
    rw [hH, Gluon.adjointAction_one]
    rfl
  · show Gluon.adjointAction ucyc2 colourH = colourVec 1
    rw [hH]
    exact adjointAction_ucyc2_cm0
  · show Gluon.adjointAction u01 colourH = colourVec 2
    rw [hH]
    exact adjointAction_u01_cm0
  · show Gluon.adjointAction (p01 * u01) colourH = colourVec 3
    rw [hH, hmul, adjointAction_u01_cm0]
    exact adjointAction_p01_cm2
  · show Gluon.adjointAction (ucyc * u01) colourH = colourVec 4
    rw [hH, hmul, adjointAction_u01_cm0]
    exact adjointAction_ucyc_cm2
  · show Gluon.adjointAction (p02 * (ucyc * u01)) colourH = colourVec 5
    rw [hH, hmul, hmul, adjointAction_u01_cm0, adjointAction_ucyc_cm2]
    exact adjointAction_p02_cm4
  · show Gluon.adjointAction (ucyc * (ucyc * u01)) colourH = colourVec 6
    rw [hH, hmul, hmul, adjointAction_u01_cm0, adjointAction_ucyc_cm2]
    exact adjointAction_ucyc_cm4
  · show Gluon.adjointAction (p12 * (ucyc * (ucyc * u01))) colourH = colourVec 7
    rw [hH, hmul, hmul, hmul, adjointAction_u01_cm0, adjointAction_ucyc_cm2,
      adjointAction_ucyc_cm4]
    exact adjointAction_p12_cm6

/-- The conjugate of the `DiagonalJet` colour direction by a constant gauge transformation is
  traceless
  hermitian. -/
lemma adjointAction_colourH_mem (u : specialUnitaryGroup (Fin 3) ℂ) :
    Gluon.adjointAction u colourH ∈ ColourSpace := by
  have hu : ((u : Matrix (Fin 3) (Fin 3) ℂ))ᴴ * (u : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
    have h := mem_unitaryGroup_iff'.mp (mem_specialUnitaryGroup_iff.mp u.2).1
    rwa [star_eq_conjTranspose] at h
  rw [mem_ColourSpace, Gluon.adjointAction_apply_coe, trace_mul_cycle, hu, Matrix.one_mul,
    colourH_coe]
  exact trace_colourMat

/-- The orbit of the `DiagonalJet` colour direction under constant gauge transformations, inside the
  colour carrier. -/
noncomputable def colourOrbit : Set ColourSpace :=
  Set.range fun u : specialUnitaryGroup (Fin 3) ℂ =>
    (⟨Gluon.adjointAction u colourH, adjointAction_colourH_mem u⟩ : ColourSpace)

/-- **The conjugate orbit spans the colour carrier.** Every traceless hermitian matrix is a real
  linear combination of constant `SU(3)` conjugates of `H = diag(1, -1, 0)`. -/
lemma span_colourOrbit : Submodule.span ℝ colourOrbit = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← colourBasis.span_eq]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  exact Submodule.subset_span ⟨colourConj k, Subtype.ext (colourBasis_eq_adjointAction k)⟩

/-!

## F. Based jets in every colour direction

-/

lemma evalSU_ofConstantSU (u : specialUnitaryGroup (Fin 3) ℂ) :
    JetGaugeGroupI.evalSU (Fin 3) (JetGaugeGroupI.ofConstantSU (Fin 3) u) = u := by
  apply Subtype.ext
  ext i j
  simp [JetGaugeGroupI.evalSU, JetGaugeGroupI.ofConstantSU, RingHom.mapMatrix_apply,
    Matrix.map_apply]

lemma mcCoeff_ofConstantSU (u : specialUnitaryGroup (Fin 3) ℂ) (μ : Fin 1 ⊕ Fin 3) :
    Gluon.mcCoeff (JetGaugeGroupI.ofConstantSU (Fin 3) u) μ = 0 := by
  apply Subtype.ext
  show Gluon.mcMatrix μ ((JetGaugeGroupI.ofConstantSU (Fin 3) u) :
    Matrix (Fin 3) (Fin 3) JetRing) = _
  rw [show ((JetGaugeGroupI.ofConstantSU (Fin 3) u) : Matrix (Fin 3) (Fin 3) JetRing) =
      (u : Matrix (Fin 3) (Fin 3) ℂ).map (C : ℂ →+* JetRing) from rfl]
  simp [Gluon.mcMatrix]

/-- For based jets the Maurer–Cartan cocycle degenerates to additivity. -/
lemma mcCoeff_mul_of_based {U V : specialUnitaryGroup (Fin 3) JetRing}
    (hU : JetGaugeGroupI.evalSU (Fin 3) U = 1) (μ : Fin 1 ⊕ Fin 3) :
    Gluon.mcCoeff (U * V) μ = Gluon.mcCoeff U μ + Gluon.mcCoeff V μ := by
  rw [Gluon.mcCoeff_mul, hU, Gluon.adjointAction_one]
  rfl

/-- The ordered product of eight gauge jets. The colour jet group is not commutative, so the
  product is written out rather than taken over a `Finset`. -/
noncomputable def prodJet (f : Fin 8 → specialUnitaryGroup (Fin 3) JetRing) :
    specialUnitaryGroup (Fin 3) JetRing :=
  f 0 * (f 1 * (f 2 * (f 3 * (f 4 * (f 5 * (f 6 * f 7))))))

lemma evalSU_prodJet {f : Fin 8 → specialUnitaryGroup (Fin 3) JetRing}
    (hf : ∀ k, JetGaugeGroupI.evalSU (Fin 3) (f k) = 1) :
    JetGaugeGroupI.evalSU (Fin 3) (prodJet f) = 1 := by
  simp [prodJet, map_mul, hf]

/-- On based jets the Maurer–Cartan coefficient of a product is the sum of the coefficients. -/
lemma mcCoeff_prodJet {f : Fin 8 → specialUnitaryGroup (Fin 3) JetRing}
    (hf : ∀ k, JetGaugeGroupI.evalSU (Fin 3) (f k) = 1) (ν : Fin 1 ⊕ Fin 3) :
    Gluon.mcCoeff (prodJet f) ν = ∑ k, Gluon.mcCoeff (f k) ν := by
  rw [Fin.sum_univ_eight, prodJet, mcCoeff_mul_of_based (hf 0), mcCoeff_mul_of_based (hf 1),
    mcCoeff_mul_of_based (hf 2), mcCoeff_mul_of_based (hf 3), mcCoeff_mul_of_based (hf 4),
    mcCoeff_mul_of_based (hf 5), mcCoeff_mul_of_based (hf 6)]
  abel

/-- The based jet realizing the shift `r • Ad(u) H` in the direction `μ`: the `DiagonalJet` diagonal
  jet
  conjugated by a constant colour rotation. -/
noncomputable def conjJet (u : specialUnitaryGroup (Fin 3) ℂ) (r : ℝ) (μ : Fin 1 ⊕ Fin 3) :
    specialUnitaryGroup (Fin 3) JetRing :=
  JetGaugeGroupI.ofConstantSU (Fin 3) u * diagSU r (Finsupp.single μ 1) (single_ne_zero' μ) *
    (JetGaugeGroupI.ofConstantSU (Fin 3) u)⁻¹

lemma evalSU_conjJet (u : specialUnitaryGroup (Fin 3) ℂ) (r : ℝ) (μ : Fin 1 ⊕ Fin 3) :
    JetGaugeGroupI.evalSU (Fin 3) (conjJet u r μ) = 1 := by
  rw [conjJet, map_mul, map_mul, map_inv, evalSU_ofConstantSU, evalSU_diagSU, mul_one,
    mul_inv_cancel]

lemma mcCoeff_conjJet (u : specialUnitaryGroup (Fin 3) ℂ) (r : ℝ) (μ ν : Fin 1 ⊕ Fin 3) :
    Gluon.mcCoeff (conjJet u r μ) ν =
      Gluon.adjointAction u
        (Gluon.mcCoeff (diagSU r (Finsupp.single μ 1) (single_ne_zero' μ)) ν) := by
  have hinv : (JetGaugeGroupI.ofConstantSU (Fin 3) u)⁻¹ =
      JetGaugeGroupI.ofConstantSU (Fin 3) u⁻¹ := (map_inv _ u).symm
  simp only [conjJet, hinv, Gluon.mcCoeff_mul, mcCoeff_ofConstantSU, zero_add,
    evalSU_ofConstantSU, map_zero, add_zero]

/-- **Realizability in one colour direction.** For every constant `u`, every real `r` and every
  spacetime direction `μ` there is a based gauge jet whose Maurer–Cartan coefficient is
  `r • Ad(u) H` in the direction `μ` and zero elsewhere. -/
lemma mcCoeff_conjJet_eq (u : specialUnitaryGroup (Fin 3) ℂ) (r : ℝ) (μ ν : Fin 1 ⊕ Fin 3) :
    Gluon.mcCoeff (conjJet u r μ) ν =
      if ν = μ then r • Gluon.adjointAction u colourH else 0 := by
  rw [mcCoeff_conjJet]
  by_cases h : ν = μ
  · subst h
    rw [if_pos rfl, mcCoeff_diagSU_single, map_smul]
  · rw [if_neg h, mcCoeff_diagSU_single_of_ne r μ ν h, map_zero]

/-- **Arbitrary based translations of the colour carrier.** For every traceless hermitian `X` and
  every spacetime direction `μ` there is a based gauge jet whose Maurer–Cartan coefficient is `X`
  in the direction `μ` and zero in every other direction.

  This is the exact input that layerwise polynomial-translation elimination consumes: the shift is
  an arbitrary constant element of the colour carrier, concentrated in one Lorentz direction. -/
lemma exists_based_mcCoeff (μ : Fin 1 ⊕ Fin 3) (X : ColourSpace) :
    ∃ U : specialUnitaryGroup (Fin 3) JetRing,
      JetGaugeGroupI.evalSU (Fin 3) U = 1 ∧
      ∀ ν, Gluon.mcCoeff U ν =
        if ν = μ then (X : selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ)) else 0 := by
  classical
  refine ⟨prodJet fun k => conjJet (colourConj k) (colourBasis.repr X k) μ, ?_, ?_⟩
  · exact evalSU_prodJet fun k => evalSU_conjJet _ _ _
  · intro ν
    rw [mcCoeff_prodJet (fun k => evalSU_conjJet _ _ _) ν]
    rcases eq_or_ne ν μ with rfl | hne
    · have hcoe : ∀ k : Fin 8,
          Gluon.mcCoeff (conjJet (colourConj k) (colourBasis.repr X k) ν) ν =
            Submodule.subtype ColourSpace (colourBasis.repr X k • colourBasis k) := fun k => by
        rw [mcCoeff_conjJet_eq, if_pos rfl, colourBasis_eq_adjointAction k]
        rfl
      rw [if_pos rfl, Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => hcoe k, ← map_sum,
        colourBasis.sum_repr X]
      rfl
    · rw [if_neg hne]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [mcCoeff_conjJet_eq, if_neg hne]

end SU3Jet

end StandardModel
