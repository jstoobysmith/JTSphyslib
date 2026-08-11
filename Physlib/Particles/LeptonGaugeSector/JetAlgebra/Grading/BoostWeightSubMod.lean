/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.Grading.BoostWeight
/-!
# The boost weight zero part of the photon pairs

The products `F_{μν} F_{μ'ν'}` of two field strengths span a submodule of the jet algebra. This
file computes its intersection with the boost weight zero submodule: it is spanned by seven
explicit products, listed in `fieldStrengthPairsWeightZero`.

*The proof is a certificate.* Rather than deducing the intersection abstractly, the span of the
products is written out in boost eigenvectors. The coordinate components `F_{μν}` are not boost
eigenvectors, but six combinations of them are: the light-cone combinations `F_{0x} - F_{zx}` and
`F_{0y} - F_{zy}` of weight `2`, their partners `F_{0x} + F_{zx}` and `F_{0y} + F_{zy}` of weight
`-2`, and the two components with no free light-cone index, `F_{xy}` and `F_{0z}`, of weight `0`.
Every `F_{μν}` is a combination of these six — the sixteen cases of `fieldStrengthSpan_le` — so
the span of the products is contained in the sum of the nine products of the three weight spaces,
whose weights are `0, ±2, ±4`. The three of weight zero — a weight-`2` field strength against a
weight-`-2` one, and two weight-zero ones — are exactly the seven products listed.

The intersection then follows formally, with no linear independence of the products needed. The
weight submodules are independent (`boostWeightSubmodule_iSupIndep`), so boost weight zero is
disjoint from the span of the weights `±2, ±4`; since the weight-zero part sits inside boost
weight zero, the modular law cuts the intersection down to it.

## i. Overview

Section A exhibits the six boost eigenvectors, section B decomposes every coordinate component
into them, section C multiplies the weight spaces together and reads off the weight of each of
the nine products, and section D assembles the intersection.

## ii. Key results

- `JetAlgebra.fieldStrengthPlusX` and its five partners : the boost eigenvectors among the
  field strengths, of weights `2`, `-2` and `0`.
- `JetAlgebra.fieldStrengthSpan_le` : every field strength is a combination of the six.
- `JetAlgebra.fieldStrengthPairs` : the products `F_{μν} F_{μ'ν'}`.
- `JetAlgebra.fieldStrengthPairsWeightZero` : the seven products of boost weight zero.
- `JetAlgebra.span_fieldStrengthPairs_le` : the span of the products, split into its weights.
- `JetAlgebra.boostWeight_inter_fieldStrength` : the intersection of boost weight zero with the
  span of the products is the span of the seven.

## iii. Table of contents

- A. The boost eigenvectors among the field strengths
- B. Every field strength is a combination of the eigenvectors
- C. Products of two field strengths
- D. The weight zero part of the photon pairs

-/

@[expose] public section

namespace LeptonGaugeSector
open TensorProduct StandardModel
open scoped minkowskiMatrix PauliMatrix
open Matrix MatrixGroups

namespace JetAlgebra

open scoped Pointwise

/-!

## A. The boost eigenvectors among the field strengths

A boost in the `z`-direction mixes the time index with the `z` index, so the coordinate
components of the field strength are not boost eigenvectors. Six combinations of them are: the
four light-cone combinations, of weight `±2`, and the two components whose index pair is either
transverse to the boost or contained in the `0z` plane, of weight `0`.

-/

/-- `F_{0x} - F_{zx}`, of boost weight `2`. -/
noncomputable def fieldStrengthPlusX : JetAlgebra :=
  fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) -
    fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0)

/-- `F_{0y} - F_{zy}`, of boost weight `2`. -/
noncomputable def fieldStrengthPlusY : JetAlgebra :=
  fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) -
    fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1)

/-- `F_{0x} + F_{zx}`, of boost weight `-2`. -/
noncomputable def fieldStrengthMinusX : JetAlgebra :=
  fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) +
    fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0)

/-- `F_{0y} + F_{zy}`, of boost weight `-2`. -/
noncomputable def fieldStrengthMinusY : JetAlgebra :=
  fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) +
    fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1)

/-- `F_{xy}`, of boost weight `0`. -/
noncomputable def fieldStrengthTransverse : JetAlgebra :=
  fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)

/-- `F_{0z}`, of boost weight `0`. -/
noncomputable def fieldStrengthLongitudinal : JetAlgebra :=
  fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)

/-- `F_{0x} - F_{zx}` has boost weight `2`. -/
lemma fieldStrengthPlusX_mem : fieldStrengthPlusX ∈ boostWeightSubmodule 2 :=
  fieldStrengthDeriv_lightCone_mem_two

/-- `F_{0x} + F_{zx}` has boost weight `-2`. -/
lemma fieldStrengthMinusX_mem : fieldStrengthMinusX ∈ boostWeightSubmodule (-2) :=
  fieldStrengthDeriv_lightCone_mem_neg_two

/-- `F_{xy}` has boost weight `0`: both indices are transverse to the boost. -/
lemma fieldStrengthTransverse_mem : fieldStrengthTransverse ∈ boostWeightSubmodule 0 :=
  fieldStrengthDeriv_transverse_mem_zero

/-- `F_{0y} - F_{zy}` has boost weight `2`. -/
lemma fieldStrengthPlusY_mem : fieldStrengthPlusY ∈ boostWeightSubmodule 2 := by
  intro t ht
  have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [fieldStrengthPlusY, map_sub, repLorentzGroup_fieldStrengthDeriv_nil,
    repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ, fieldStrengthDeriv_self,
    mul_zero, mul_one, Complex.ofReal_zero,
    zero_smul, smul_zero, add_zero, zero_add]
  push_cast
  match_scalars <;> (field_simp; ring)

/-- `F_{0y} + F_{zy}` has boost weight `-2`. -/
lemma fieldStrengthMinusY_mem : fieldStrengthMinusY ∈ boostWeightSubmodule (-2) := by
  intro t ht
  have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [fieldStrengthMinusY, map_add, repLorentzGroup_fieldStrengthDeriv_nil,
    repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ, fieldStrengthDeriv_self,
    mul_zero, mul_one, Complex.ofReal_zero,
    zero_smul, smul_zero, add_zero, zero_add]
  push_cast
  match_scalars <;> (field_simp; ring)

/-- `F_{0z}` has boost weight `0`: the boost acts on its two indices by inverse factors. -/
lemma fieldStrengthLongitudinal_mem : fieldStrengthLongitudinal ∈ boostWeightSubmodule 0 := by
  intro t ht
  have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [fieldStrengthLongitudinal, repLorentzGroup_fieldStrengthDeriv_nil]
  simp only [toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one,
    Fin.sum_univ_three, boostMatZ, fieldStrengthDeriv_self,
    mul_zero, zero_mul, Complex.ofReal_zero,
    zero_smul, smul_zero, add_zero, zero_add]
  rw [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) =
    - fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) from
    fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 2)]
  push_cast
  match_scalars
  field_simp
  ring

/-!

## B. Every field strength is a combination of the eigenvectors

The six eigenvectors span the same submodule as the sixteen coordinate components: on the
light-cone pairs this is the change of basis `F_{0x} = ((F_{0x} - F_{zx}) + (F_{0x} + F_{zx}))/2`
and its partners, and the remaining components are either zero, one of the two weight-zero
eigenvectors, or minus one of these by antisymmetry.

-/

/-- The span of the two weight-`2` field strengths. -/
noncomputable def fieldStrengthSpanTwo : Submodule ℂ JetAlgebra :=
  Submodule.span ℂ {fieldStrengthPlusX, fieldStrengthPlusY}

/-- The span of the two weight-`0` field strengths. -/
noncomputable def fieldStrengthSpanZero : Submodule ℂ JetAlgebra :=
  Submodule.span ℂ {fieldStrengthTransverse, fieldStrengthLongitudinal}

/-- The span of the two weight-`-2` field strengths. -/
noncomputable def fieldStrengthSpanNegTwo : Submodule ℂ JetAlgebra :=
  Submodule.span ℂ {fieldStrengthMinusX, fieldStrengthMinusY}

/-- The span of the field strengths `F_{μν}`. -/
noncomputable def fieldStrengthSpan : Submodule ℂ JetAlgebra :=
  Submodule.span ℂ {x | ∃ μ ν, x = fieldStrengthDeriv {} μ ν}

/-- The weight-`2` field strengths span a submodule of boost weight `2`. -/
lemma fieldStrengthSpanTwo_le : fieldStrengthSpanTwo ≤ boostWeightSubmodule 2 := by
  refine Submodule.span_le.2 ?_
  rintro x (rfl | rfl)
  · exact fieldStrengthPlusX_mem
  · exact fieldStrengthPlusY_mem

/-- The weight-`0` field strengths span a submodule of boost weight `0`. -/
lemma fieldStrengthSpanZero_le : fieldStrengthSpanZero ≤ boostWeightSubmodule 0 := by
  refine Submodule.span_le.2 ?_
  rintro x (rfl | rfl)
  · exact fieldStrengthTransverse_mem
  · exact fieldStrengthLongitudinal_mem

/-- The weight-`-2` field strengths span a submodule of boost weight `-2`. -/
lemma fieldStrengthSpanNegTwo_le : fieldStrengthSpanNegTwo ≤ boostWeightSubmodule (-2) := by
  refine Submodule.span_le.2 ?_
  rintro x (rfl | rfl)
  · exact fieldStrengthMinusX_mem
  · exact fieldStrengthMinusY_mem

/-- Every field strength is a combination of the six boost eigenvectors. -/
lemma fieldStrengthSpan_le :
    fieldStrengthSpan ≤ fieldStrengthSpanTwo ⊔ fieldStrengthSpanZero ⊔ fieldStrengthSpanNegTwo := by
  have hPX : fieldStrengthPlusX ∈ fieldStrengthSpanTwo ⊔ fieldStrengthSpanZero ⊔
      fieldStrengthSpanNegTwo :=
    Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span (by simp)))
  have hPY : fieldStrengthPlusY ∈ fieldStrengthSpanTwo ⊔ fieldStrengthSpanZero ⊔
      fieldStrengthSpanNegTwo :=
    Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span (by simp)))
  have hT : fieldStrengthTransverse ∈ fieldStrengthSpanTwo ⊔ fieldStrengthSpanZero ⊔
      fieldStrengthSpanNegTwo :=
    Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
  have hL : fieldStrengthLongitudinal ∈ fieldStrengthSpanTwo ⊔ fieldStrengthSpanZero ⊔
      fieldStrengthSpanNegTwo :=
    Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
  have hMX : fieldStrengthMinusX ∈ fieldStrengthSpanTwo ⊔ fieldStrengthSpanZero ⊔
      fieldStrengthSpanNegTwo :=
    Submodule.mem_sup_right (Submodule.subset_span (by simp))
  have hMY : fieldStrengthMinusY ∈ fieldStrengthSpanTwo ⊔ fieldStrengthSpanZero ⊔
      fieldStrengthSpanNegTwo :=
    Submodule.mem_sup_right (Submodule.subset_span (by simp))
  refine Submodule.span_le.2 ?_
  rintro x ⟨μ, ν, rfl⟩
  match μ, ν with
  | Sum.inl 0, Sum.inl 0 => rw [fieldStrengthDeriv_self]; exact Submodule.zero_mem _
  | Sum.inr 0, Sum.inr 0 => rw [fieldStrengthDeriv_self]; exact Submodule.zero_mem _
  | Sum.inr 1, Sum.inr 1 => rw [fieldStrengthDeriv_self]; exact Submodule.zero_mem _
  | Sum.inr 2, Sum.inr 2 => rw [fieldStrengthDeriv_self]; exact Submodule.zero_mem _
  | Sum.inl 0, Sum.inr 0 =>
    rw [show fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) =
        (2⁻¹ : ℂ) • (fieldStrengthPlusX + fieldStrengthMinusX) from by
      rw [fieldStrengthPlusX, fieldStrengthMinusX]; module]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ hPX hMX)
  | Sum.inr 0, Sum.inl 0 =>
    rw [show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) =
        (-2⁻¹ : ℂ) • (fieldStrengthPlusX + fieldStrengthMinusX) from by
      rw [fieldStrengthPlusX, fieldStrengthMinusX,
        fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 0)]; module]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ hPX hMX)
  | Sum.inl 0, Sum.inr 1 =>
    rw [show fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) =
        (2⁻¹ : ℂ) • (fieldStrengthPlusY + fieldStrengthMinusY) from by
      rw [fieldStrengthPlusY, fieldStrengthMinusY]; module]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ hPY hMY)
  | Sum.inr 1, Sum.inl 0 =>
    rw [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) =
        (-2⁻¹ : ℂ) • (fieldStrengthPlusY + fieldStrengthMinusY) from by
      rw [fieldStrengthPlusY, fieldStrengthMinusY,
        fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 1)]; module]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ hPY hMY)
  | Sum.inr 2, Sum.inr 0 =>
    rw [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) =
        (2⁻¹ : ℂ) • (fieldStrengthMinusX - fieldStrengthPlusX) from by
      rw [fieldStrengthPlusX, fieldStrengthMinusX]; module]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hMX hPX)
  | Sum.inr 0, Sum.inr 2 =>
    rw [show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) =
        (2⁻¹ : ℂ) • (fieldStrengthPlusX - fieldStrengthMinusX) from by
      rw [fieldStrengthPlusX, fieldStrengthMinusX,
        fieldStrengthDeriv_antisymm {} (Sum.inr 2) (Sum.inr 0)]; module]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hPX hMX)
  | Sum.inr 2, Sum.inr 1 =>
    rw [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) =
        (2⁻¹ : ℂ) • (fieldStrengthMinusY - fieldStrengthPlusY) from by
      rw [fieldStrengthPlusY, fieldStrengthMinusY]; module]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hMY hPY)
  | Sum.inr 1, Sum.inr 2 =>
    rw [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) =
        (2⁻¹ : ℂ) • (fieldStrengthPlusY - fieldStrengthMinusY) from by
      rw [fieldStrengthPlusY, fieldStrengthMinusY,
        fieldStrengthDeriv_antisymm {} (Sum.inr 2) (Sum.inr 1)]; module]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hPY hMY)
  | Sum.inr 0, Sum.inr 1 => exact hT
  | Sum.inr 1, Sum.inr 0 =>
    rw [fieldStrengthDeriv_antisymm {} (Sum.inr 0) (Sum.inr 1)]
    exact neg_mem hT
  | Sum.inl 0, Sum.inr 2 => exact hL
  | Sum.inr 2, Sum.inl 0 =>
    rw [fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 2)]
    exact neg_mem hL

/-!

## C. Products of two field strengths

The span of the products is the product of the span of the field strengths with itself, so it is
contained in the product of the sum of the three weight spaces with itself. That expands into
nine products of weight spaces, and boost weights add under multiplication, so each of the nine
carries a single weight: `0` for the three products of a weight `w` space with a weight `-w` one,
and `±2` or `±4` for the other six.

-/

/-- Each field strength lies in the field-strength span. -/
lemma fieldStrengthDeriv_mem_span (μ ν : Fin 1 ⊕ Fin 3) :
    fieldStrengthDeriv {} μ ν ∈ fieldStrengthSpan :=
  Submodule.subset_span ⟨μ, ν, rfl⟩

/-- The weight-`2` eigenvector `F_{0x} - F_{zx}` lies in the field-strength span. -/
lemma fieldStrengthPlusX_mem_span : fieldStrengthPlusX ∈ fieldStrengthSpan :=
  Submodule.sub_mem _ (fieldStrengthDeriv_mem_span _ _) (fieldStrengthDeriv_mem_span _ _)

/-- The weight-`2` eigenvector `F_{0y} - F_{zy}` lies in the field-strength span. -/
lemma fieldStrengthPlusY_mem_span : fieldStrengthPlusY ∈ fieldStrengthSpan :=
  Submodule.sub_mem _ (fieldStrengthDeriv_mem_span _ _) (fieldStrengthDeriv_mem_span _ _)

/-- The weight-`-2` eigenvector `F_{0x} + F_{zx}` lies in the field-strength span. -/
lemma fieldStrengthMinusX_mem_span : fieldStrengthMinusX ∈ fieldStrengthSpan :=
  Submodule.add_mem _ (fieldStrengthDeriv_mem_span _ _) (fieldStrengthDeriv_mem_span _ _)

/-- The weight-`-2` eigenvector `F_{0y} + F_{zy}` lies in the field-strength span. -/
lemma fieldStrengthMinusY_mem_span : fieldStrengthMinusY ∈ fieldStrengthSpan :=
  Submodule.add_mem _ (fieldStrengthDeriv_mem_span _ _) (fieldStrengthDeriv_mem_span _ _)

/-- `F_{xy}` lies in the field-strength span. -/
lemma fieldStrengthTransverse_mem_span : fieldStrengthTransverse ∈ fieldStrengthSpan :=
  fieldStrengthDeriv_mem_span _ _

/-- `F_{0z}` lies in the field-strength span. -/
lemma fieldStrengthLongitudinal_mem_span : fieldStrengthLongitudinal ∈ fieldStrengthSpan :=
  fieldStrengthDeriv_mem_span _ _

/-- Elements of the field-strength span commute. -/
lemma mul_comm_of_mem_fieldStrengthSpan {x y : JetAlgebra} (hx : x ∈ fieldStrengthSpan)
    (hy : y ∈ fieldStrengthSpan) : x * y = y * x := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨μ, ν, rfl⟩ := ha
    induction hy using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨μ', ν', rfl⟩ := hb
      exact fieldStrengthDeriv_mul_comm {} {} μ ν μ' ν'
    | zero => rw [mul_zero, zero_mul]
    | add u v _ _ ihu ihv => rw [mul_add, add_mul, ihu, ihv]
    | smul c u _ ihu => rw [mul_smul_comm, smul_mul_assoc, ihu]
  | zero => rw [mul_zero, zero_mul]
  | add u v _ _ ihu ihv => rw [mul_add, add_mul, ihu, ihv]
  | smul c u _ ihu => rw [mul_smul_comm, smul_mul_assoc, ihu]

/-- Boost weights add under multiplication. -/
lemma mul_mem_boostWeightSubmodule' {k l m : ℤ} (hm : k + l = m) {x y : JetAlgebra}
    (hx : x ∈ boostWeightSubmodule k) (hy : y ∈ boostWeightSubmodule l) :
    x * y ∈ boostWeightSubmodule m := by
  rw [← hm]
  exact mul_mem_boostWeightSubmodule hx hy

/-- Boost weights add under the product of submodules. -/
lemma mul_le_boostWeightSubmodule {X Y : Submodule ℂ JetAlgebra} {k l m : ℤ} (hm : k + l = m)
    (hX : X ≤ boostWeightSubmodule k) (hY : Y ≤ boostWeightSubmodule l) :
    X * Y ≤ boostWeightSubmodule m := by
  rw [← hm]
  exact Submodule.mul_le.2 fun _ hx _ hy => mul_mem_boostWeightSubmodule (hX hx) (hY hy)

/-- The products `F_{μν} F_{μ'ν'}` of two field strengths. -/
def fieldStrengthPairs : Set JetAlgebra :=
  {x | ∃ μ ν μ' ν', x = fieldStrengthDeriv {} μ ν * fieldStrengthDeriv {} μ' ν'}

/-- The products of two field strengths which are of boost weight zero: a weight-`2` light-cone
  field strength against a weight-`-2` one, or a pair drawn from `F_{xy}` and `F_{0z}`. -/
def fieldStrengthPairsWeightZero : Set JetAlgebra :=
  {fieldStrengthPlusX * fieldStrengthMinusX, fieldStrengthPlusX * fieldStrengthMinusY,
    fieldStrengthPlusY * fieldStrengthMinusX, fieldStrengthPlusY * fieldStrengthMinusY,
    fieldStrengthTransverse * fieldStrengthTransverse,
    fieldStrengthTransverse * fieldStrengthLongitudinal,
    fieldStrengthLongitudinal * fieldStrengthLongitudinal}

/-- The span of the products of two field strengths is the product of the field-strength span
  with itself. -/
lemma span_fieldStrengthPairs :
    Submodule.span ℂ fieldStrengthPairs = fieldStrengthSpan * fieldStrengthSpan := by
  rw [fieldStrengthSpan, Submodule.span_mul_span]
  congr 1
  ext x
  constructor
  · rintro ⟨μ, ν, μ', ν', rfl⟩
    exact ⟨_, ⟨μ, ν, rfl⟩, _, ⟨μ', ν', rfl⟩, rfl⟩
  · rintro ⟨a, ⟨μ, ν, rfl⟩, b, ⟨μ', ν', rfl⟩, rfl⟩
    exact ⟨μ, ν, μ', ν', rfl⟩

/-- A weight-`2` field strength times a weight-`-2` one is one of the weight-zero pairs. -/
lemma fieldStrengthSpanTwo_mul_NegTwo_le :
    fieldStrengthSpanTwo * fieldStrengthSpanNegTwo ≤
      Submodule.span ℂ fieldStrengthPairsWeightZero := by
  rw [fieldStrengthSpanTwo, fieldStrengthSpanNegTwo, Submodule.span_mul_span]
  refine Submodule.span_le.2 ?_
  rintro x ⟨a, ha, b, hb, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    exact Submodule.subset_span (by simp [fieldStrengthPairsWeightZero])

/-- The same product in the other order, using that the field strengths commute. -/
lemma fieldStrengthSpanNegTwo_mul_Two_le :
    fieldStrengthSpanNegTwo * fieldStrengthSpanTwo ≤
      Submodule.span ℂ fieldStrengthPairsWeightZero := by
  rw [fieldStrengthSpanTwo, fieldStrengthSpanNegTwo, Submodule.span_mul_span]
  refine Submodule.span_le.2 ?_
  rintro x ⟨a, ha, b, hb, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> beta_reduce
  · rw [mul_comm_of_mem_fieldStrengthSpan fieldStrengthMinusX_mem_span
      fieldStrengthPlusX_mem_span]
    exact Submodule.subset_span (by simp [fieldStrengthPairsWeightZero])
  · rw [mul_comm_of_mem_fieldStrengthSpan fieldStrengthMinusX_mem_span
      fieldStrengthPlusY_mem_span]
    exact Submodule.subset_span (by simp [fieldStrengthPairsWeightZero])
  · rw [mul_comm_of_mem_fieldStrengthSpan fieldStrengthMinusY_mem_span
      fieldStrengthPlusX_mem_span]
    exact Submodule.subset_span (by simp [fieldStrengthPairsWeightZero])
  · rw [mul_comm_of_mem_fieldStrengthSpan fieldStrengthMinusY_mem_span
      fieldStrengthPlusY_mem_span]
    exact Submodule.subset_span (by simp [fieldStrengthPairsWeightZero])

/-- Two transverse field strengths multiply into the weight-zero pairs. -/
lemma fieldStrengthSpanZero_mul_Zero_le :
    fieldStrengthSpanZero * fieldStrengthSpanZero ≤
      Submodule.span ℂ fieldStrengthPairsWeightZero := by
  rw [fieldStrengthSpanZero, Submodule.span_mul_span]
  refine Submodule.span_le.2 ?_
  rintro x ⟨a, ha, b, hb, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> beta_reduce
  · exact Submodule.subset_span (by simp [fieldStrengthPairsWeightZero])
  · exact Submodule.subset_span (by simp [fieldStrengthPairsWeightZero])
  · rw [mul_comm_of_mem_fieldStrengthSpan fieldStrengthLongitudinal_mem_span
      fieldStrengthTransverse_mem_span]
    exact Submodule.subset_span (by simp [fieldStrengthPairsWeightZero])
  · exact Submodule.subset_span (by simp [fieldStrengthPairsWeightZero])

/-- The span of the products of two field strengths, split into its boost weights: the
  weight-zero pairs together with the weights `±2` and `±4`. -/
lemma span_fieldStrengthPairs_le :
    Submodule.span ℂ fieldStrengthPairs ≤
      Submodule.span ℂ fieldStrengthPairsWeightZero ⊔
        ⨆ (j : ℤ) (_ : j ≠ 0), boostWeightSubmodule j := by
  have hrest : ∀ k : ℤ, k ≠ 0 → boostWeightSubmodule k ≤
      ⨆ (j : ℤ) (_ : j ≠ 0), boostWeightSubmodule j :=
    fun k hk => le_iSup_of_le k (le_iSup_of_le hk le_rfl)
  rw [span_fieldStrengthPairs]
  refine (Submodule.mul_le.2 fun _ hx _ hy =>
    Submodule.mul_mem_mul (fieldStrengthSpan_le hx) (fieldStrengthSpan_le hy)).trans ?_
  simp only [Submodule.sup_mul, Submodule.mul_sup]
  repeat' apply sup_le
  · -- `(+2) + (+2) = 4`
    exact le_sup_of_le_right ((mul_le_boostWeightSubmodule rfl fieldStrengthSpanTwo_le
      fieldStrengthSpanTwo_le).trans (hrest _ (by norm_num)))
  · -- `0 + (+2) = 2`
    exact le_sup_of_le_right ((mul_le_boostWeightSubmodule rfl fieldStrengthSpanZero_le
      fieldStrengthSpanTwo_le).trans (hrest _ (by norm_num)))
  · -- `(-2) + (+2) = 0`
    exact le_sup_of_le_left fieldStrengthSpanNegTwo_mul_Two_le
  · -- `(+2) + 0 = 2`
    exact le_sup_of_le_right ((mul_le_boostWeightSubmodule rfl fieldStrengthSpanTwo_le
      fieldStrengthSpanZero_le).trans (hrest _ (by norm_num)))
  · -- `0 + 0 = 0`
    exact le_sup_of_le_left fieldStrengthSpanZero_mul_Zero_le
  · -- `(-2) + 0 = -2`
    exact le_sup_of_le_right ((mul_le_boostWeightSubmodule rfl fieldStrengthSpanNegTwo_le
      fieldStrengthSpanZero_le).trans (hrest _ (by norm_num)))
  · -- `(+2) + (-2) = 0`
    exact le_sup_of_le_left fieldStrengthSpanTwo_mul_NegTwo_le
  · -- `0 + (-2) = -2`
    exact le_sup_of_le_right ((mul_le_boostWeightSubmodule rfl fieldStrengthSpanZero_le
      fieldStrengthSpanNegTwo_le).trans (hrest _ (by norm_num)))
  · -- `(-2) + (-2) = -4`
    exact le_sup_of_le_right ((mul_le_boostWeightSubmodule rfl fieldStrengthSpanNegTwo_le
      fieldStrengthSpanNegTwo_le).trans (hrest _ (by norm_num)))

/-- The weight-zero pairs have boost weight zero. -/
lemma span_fieldStrengthPairsWeightZero_le_boostWeightSubmodule :
    Submodule.span ℂ fieldStrengthPairsWeightZero ≤ boostWeightSubmodule 0 := by
  refine Submodule.span_le.2 ?_
  rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact mul_mem_boostWeightSubmodule' (by norm_num) fieldStrengthPlusX_mem
      fieldStrengthMinusX_mem
  · exact mul_mem_boostWeightSubmodule' (by norm_num) fieldStrengthPlusX_mem
      fieldStrengthMinusY_mem
  · exact mul_mem_boostWeightSubmodule' (by norm_num) fieldStrengthPlusY_mem
      fieldStrengthMinusX_mem
  · exact mul_mem_boostWeightSubmodule' (by norm_num) fieldStrengthPlusY_mem
      fieldStrengthMinusY_mem
  · exact mul_mem_boostWeightSubmodule' (by norm_num) fieldStrengthTransverse_mem
      fieldStrengthTransverse_mem
  · exact mul_mem_boostWeightSubmodule' (by norm_num) fieldStrengthTransverse_mem
      fieldStrengthLongitudinal_mem
  · exact mul_mem_boostWeightSubmodule' (by norm_num) fieldStrengthLongitudinal_mem
      fieldStrengthLongitudinal_mem

/-- The weight-zero pairs are products of two field strengths. -/
lemma span_fieldStrengthPairsWeightZero_le :
    Submodule.span ℂ fieldStrengthPairsWeightZero ≤ Submodule.span ℂ fieldStrengthPairs := by
  rw [span_fieldStrengthPairs]
  refine Submodule.span_le.2 ?_
  rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact Submodule.mul_mem_mul fieldStrengthPlusX_mem_span fieldStrengthMinusX_mem_span
  · exact Submodule.mul_mem_mul fieldStrengthPlusX_mem_span fieldStrengthMinusY_mem_span
  · exact Submodule.mul_mem_mul fieldStrengthPlusY_mem_span fieldStrengthMinusX_mem_span
  · exact Submodule.mul_mem_mul fieldStrengthPlusY_mem_span fieldStrengthMinusY_mem_span
  · exact Submodule.mul_mem_mul fieldStrengthTransverse_mem_span fieldStrengthTransverse_mem_span
  · exact Submodule.mul_mem_mul fieldStrengthTransverse_mem_span
      fieldStrengthLongitudinal_mem_span
  · exact Submodule.mul_mem_mul fieldStrengthLongitudinal_mem_span
      fieldStrengthLongitudinal_mem_span

/-!

## D. The weight zero part of the photon pairs

-/

/-- **The boost weight zero part of the photon pairs.** An element of the span of the products
  `F_{μν} F_{μ'ν'}` has boost weight zero exactly when it is a combination of the seven products
  of `fieldStrengthPairsWeightZero`.

  The inclusion of the right-hand side is the two membership lemmas above. For the other, the
  span of the products decomposes into the weights `0, ±2, ±4` by `span_fieldStrengthPairs_le`;
  boost weight zero is disjoint from the sum of the nonzero weights by
  `boostWeightSubmodule_iSupIndep`, and the modular law removes it. -/
theorem boostWeight_inter_fieldStrength :
    boostWeightSubmodule 0 ⊓ Submodule.span ℂ fieldStrengthPairs =
      Submodule.span ℂ fieldStrengthPairsWeightZero := by
  refine le_antisymm ?_ (le_inf span_fieldStrengthPairsWeightZero_le_boostWeightSubmodule
    span_fieldStrengthPairsWeightZero_le)
  calc boostWeightSubmodule 0 ⊓ Submodule.span ℂ fieldStrengthPairs
      ≤ boostWeightSubmodule 0 ⊓ (Submodule.span ℂ fieldStrengthPairsWeightZero ⊔
          ⨆ (j : ℤ) (_ : j ≠ 0), boostWeightSubmodule j) :=
        inf_le_inf_left _ span_fieldStrengthPairs_le
    _ = (Submodule.span ℂ fieldStrengthPairsWeightZero ⊔
          ⨆ (j : ℤ) (_ : j ≠ 0), boostWeightSubmodule j) ⊓ boostWeightSubmodule 0 := inf_comm _ _
    _ = Submodule.span ℂ fieldStrengthPairsWeightZero ⊔
          ((⨆ (j : ℤ) (_ : j ≠ 0), boostWeightSubmodule j) ⊓ boostWeightSubmodule 0) :=
        sup_inf_assoc_of_le _ span_fieldStrengthPairsWeightZero_le_boostWeightSubmodule
    _ = Submodule.span ℂ fieldStrengthPairsWeightZero := by
        rw [disjoint_iff.mp (boostWeightSubmodule_iSupIndep 0).symm, sup_bot_eq]

end JetAlgebra

end LeptonGaugeSector

end
