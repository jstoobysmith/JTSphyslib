/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.Grading.BoostWeight
public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.Terms.ThetaTerm
public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.GaugeKineticTerm.LinearIndependence
/-!
# The boost weight zero part of the photon pairs

The products `F_{μν} F_{μ'ν'}` of two field strengths span a submodule of the jet algebra. This
file computes the intersection of that span with the boost weight zero submodule of each of the
three axes: for one axis it is spanned by seven explicit products, written out in the statement
of the theorem; imposing all three at once leaves the Maxwell and theta terms.

*The one-axis proof is a certificate.* Rather than deducing the intersection abstractly, the span
of the products is expanded into boost eigenvectors. For the `z`-boost the coordinate components
`F_{μν}` are not boost eigenvectors, but six combinations of them are: the light-cone
combinations `F_{0x} - F_{zx}` and `F_{0y} - F_{zy}` of weight `2`, their partners
`F_{0x} + F_{zx}` and `F_{0y} + F_{zy}` of weight `-2`, and the two components with no free
light-cone index, `F_{xy}` and `F_{0z}`, of weight `0`. Every `F_{μν}` is a combination of these
six — the sixteen cases of step B — so the span of the products lies in the sum of the nine
products of the three weight spaces, of weights `0, ±2, ±4`. The three of weight zero — a
weight-`2` field strength against a weight-`-2` one, and two weight-zero ones — are exactly the
seven products listed.

The intersection then follows formally, with no linear independence of the products needed. The
weight submodules are independent (`boostWeightSubmodule_iSupIndep`), so boost weight zero is
disjoint from the span of the weights `±2, ±4`; since the weight-zero part sits inside boost
weight zero, the modular law cuts the intersection down to it. The `x`- and `y`-axis theorems are
the same certificate with the light-cone pairs built on those axes instead.

*The three-axis theorem is not a certificate.* The three seven-dimensional spans have to be
intersected, and that is done on coefficients, with the dual family of
`GaugeKineticTerm.LinearIndependence` reading them off.

## i. Overview

Each one-axis proof runs in four steps, marked in its source. Step A exhibits the boost
eigenvectors, step B decomposes the coordinate components, step C splits every product into
eigen products of a single weight, and step D assembles the intersection.

## ii. Key results

- `JetAlgebra.boostWeight_inter_fieldStrength` : the intersection of boost weight zero with the
  span of the products `F_{μν} F_{μ'ν'}` is the span of the seven weight-zero products, and
  `_x`, `_y` for the other two axes.
- `JetAlgebra.boostWeight_inter_fieldStrength_full` : imposing boost weight zero along all three
  axes at once leaves the span of the Maxwell and theta terms.

-/

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace LeptonGaugeSector
open TensorProduct StandardModel
open scoped minkowskiMatrix PauliMatrix Pointwise
open Matrix MatrixGroups

namespace JetAlgebra

private lemma algebraMap_real_complex (t : ℝ) : (algebraMap ℝ ℂ) t = ((t : ℝ) : ℂ) := rfl

/-- **The boost weight zero part of the photon pairs.** An element of the span of the products
  `F_{μν} F_{μ'ν'}` of two field strengths has boost weight zero exactly when it is a combination
  of the seven products of a weight-`2` light-cone field strength `F_{0x} - F_{zx}`,
  `F_{0y} - F_{zy}` with a weight-`-2` one `F_{0x} + F_{zx}`, `F_{0y} + F_{zy}`, and of the
  weight-zero components `F_{xy}` and `F_{0z}` with each other. -/
theorem boostWeight_inter_fieldStrength :
    boostWeightSubmodule 2 0 ⊓ Submodule.span ℂ
        {x | ∃ μ ν μ' ν', x = fieldStrengthDeriv {} μ ν * fieldStrengthDeriv {} μ' ν'} =
      Submodule.span ℂ {(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) -
            fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0)) *
          (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) +
            fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0)),
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) -
            fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0)) *
          (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) +
            fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1)),
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) -
            fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1)) *
          (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) +
            fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0)),
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) -
            fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1)) *
          (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) +
            fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1)),
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1),
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2),
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2)} := by
  -- ### A. The boost eigenvectors among the field strengths
  -- The light-cone combinations `F_{0i} ∓ F_{zi}` have weight `±2`; `F_{xy}` and `F_{0z}`, with
  -- no free light-cone index, have weight `0`.
  set PX := fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) -
    fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) with hPX
  set PY := fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) -
    fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) with hPY
  set MX := fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) +
    fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) with hMX
  set MY := fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) +
    fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) with hMY
  set T := fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) with hT
  set L := fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) with hL
  set FF : Set JetAlgebra :=
    {x | ∃ μ ν μ' ν', x = fieldStrengthDeriv {} μ ν * fieldStrengthDeriv {} μ' ν'} with hFF
  set S : Set JetAlgebra := {PX * MX, PX * MY, PY * MX, PY * MY, T * T, T * L, L * L} with hS
  have hPXw : PX ∈ boostWeightSubmodule 2 2 := fieldStrengthDeriv_lightCone_mem_two
  have hMXw : MX ∈ boostWeightSubmodule 2 (-2) := fieldStrengthDeriv_lightCone_mem_neg_two
  have hTw : T ∈ boostWeightSubmodule 2 0 := fieldStrengthDeriv_transverse_mem_zero
  obtain ⟨hPYw, hMYw, hLw⟩ : PY ∈ boostWeightSubmodule 2 2 ∧ MY ∈ boostWeightSubmodule 2 (-2) ∧
      L ∈ boostWeightSubmodule 2 0 := by
    refine ⟨?_, ?_, ?_⟩ <;> intro t ht
    all_goals
      have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
      simp only [hPY, hMY, hL, map_sub, map_add, boostAxis_two,
        repLorentzGroup_fieldStrengthDeriv_nil, algebraMap_real_complex,
        toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three,
        boostMatZ, fieldStrengthDeriv_self, mul_zero, zero_mul, mul_one, Complex.ofReal_zero,
        zero_smul, smul_zero, add_zero, zero_add]
      try rw [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) =
        -fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) from
        fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 2)]
      push_cast
      match_scalars <;> (field_simp; try ring)
  -- ### B. Every field strength is a combination of the eigenvectors
  -- On the light-cone pairs this is `F_{0x} = ((F_{0x} - F_{zx}) + (F_{0x} + F_{zx}))/2` and its
  -- partners; the remaining components are zero, `±F_{xy}`, or `±F_{0z}` by antisymmetry.
  set A := Submodule.span ℂ {PX, PY} with hA
  set B := Submodule.span ℂ {T, L} with hB
  set C := Submodule.span ℂ {MX, MY} with hC
  set V := Submodule.span ℂ {x | ∃ μ ν, x = fieldStrengthDeriv {} μ ν} with hV
  have hAle : A ≤ boostWeightSubmodule 2 2 := by
    rw [hA]; exact Submodule.span_le.2 (by rintro x (rfl | rfl); exacts [hPXw, hPYw])
  have hBle : B ≤ boostWeightSubmodule 2 0 := by
    rw [hB]; exact Submodule.span_le.2 (by rintro x (rfl | rfl); exacts [hTw, hLw])
  have hCle : C ≤ boostWeightSubmodule 2 (-2) := by
    rw [hC]; exact Submodule.span_le.2 (by rintro x (rfl | rfl); exacts [hMXw, hMYw])
  have hAV : A ≤ A ⊔ B ⊔ C := le_sup_left.trans le_sup_left
  have hBV : B ≤ A ⊔ B ⊔ C := le_sup_right.trans le_sup_left
  have hCV : C ≤ A ⊔ B ⊔ C := le_sup_right
  have hPXV : PX ∈ A ⊔ B ⊔ C := hAV (Submodule.subset_span (by simp))
  have hPYV : PY ∈ A ⊔ B ⊔ C := hAV (Submodule.subset_span (by simp))
  have hTV : T ∈ A ⊔ B ⊔ C := hBV (Submodule.subset_span (by simp))
  have hLV : L ∈ A ⊔ B ⊔ C := hBV (Submodule.subset_span (by simp))
  have hMXV : MX ∈ A ⊔ B ⊔ C := hCV (Submodule.subset_span (by simp))
  have hMYV : MY ∈ A ⊔ B ⊔ C := hCV (Submodule.subset_span (by simp))
  have key : ∀ {u v x : JetAlgebra} (c d : ℂ), u ∈ A ⊔ B ⊔ C → v ∈ A ⊔ B ⊔ C →
      x = c • u + d • v → x ∈ A ⊔ B ⊔ C := by
    rintro u v x c d hu hv rfl
    exact add_mem (Submodule.smul_mem _ c hu) (Submodule.smul_mem _ d hv)
  have keyn : ∀ {u v : JetAlgebra} (c d : ℂ) {μ ν : Fin 1 ⊕ Fin 3}, u ∈ A ⊔ B ⊔ C →
      v ∈ A ⊔ B ⊔ C → fieldStrengthDeriv {} μ ν = c • u + d • v →
      fieldStrengthDeriv {} ν μ ∈ A ⊔ B ⊔ C := by
    intro u v c d μ ν hu hv h
    rw [fieldStrengthDeriv_antisymm, h]
    exact neg_mem (add_mem (Submodule.smul_mem _ c hu) (Submodule.smul_mem _ d hv))
  have hVle : V ≤ A ⊔ B ⊔ C := by
    rw [hV]
    refine Submodule.span_le.2 ?_
    rintro x ⟨μ, ν, rfl⟩
    match μ, ν with
    | Sum.inl 0, Sum.inl 0 | Sum.inr 0, Sum.inr 0 | Sum.inr 1, Sum.inr 1
    | Sum.inr 2, Sum.inr 2 => rw [fieldStrengthDeriv_self]; exact zero_mem _
    | Sum.inl 0, Sum.inr 0 => exact key 2⁻¹ 2⁻¹ hPXV hMXV (by rw [hPX, hMX]; module)
    | Sum.inr 0, Sum.inl 0 => exact keyn 2⁻¹ 2⁻¹ hPXV hMXV (by rw [hPX, hMX]; module)
    | Sum.inl 0, Sum.inr 1 => exact key 2⁻¹ 2⁻¹ hPYV hMYV (by rw [hPY, hMY]; module)
    | Sum.inr 1, Sum.inl 0 => exact keyn 2⁻¹ 2⁻¹ hPYV hMYV (by rw [hPY, hMY]; module)
    | Sum.inr 2, Sum.inr 0 => exact key (-2⁻¹) 2⁻¹ hPXV hMXV (by rw [hPX, hMX]; module)
    | Sum.inr 0, Sum.inr 2 => exact keyn (-2⁻¹) 2⁻¹ hPXV hMXV (by rw [hPX, hMX]; module)
    | Sum.inr 2, Sum.inr 1 => exact key (-2⁻¹) 2⁻¹ hPYV hMYV (by rw [hPY, hMY]; module)
    | Sum.inr 1, Sum.inr 2 => exact keyn (-2⁻¹) 2⁻¹ hPYV hMYV (by rw [hPY, hMY]; module)
    | Sum.inr 0, Sum.inr 1 => exact hTV
    | Sum.inr 1, Sum.inr 0 => rw [fieldStrengthDeriv_antisymm]; exact neg_mem hTV
    | Sum.inl 0, Sum.inr 2 => exact hLV
    | Sum.inr 2, Sum.inl 0 => rw [fieldStrengthDeriv_antisymm]; exact neg_mem hLV
  -- ### C. Products of two field strengths
  -- The span of the products is `V * V ≤ (A ⊔ B ⊔ C) * (A ⊔ B ⊔ C)`, nine products of weight
  -- spaces each of a single weight: `A * C`, `C * A` and `B * B` land in the seven products
  -- (using that the field strengths commute), the other six in the nonzero weights.
  have hFV : ∀ μ ν, fieldStrengthDeriv {} μ ν ∈ V := fun μ ν => by
    rw [hV]; exact Submodule.subset_span ⟨μ, ν, rfl⟩
  have hPXV' : PX ∈ V := by rw [hPX]; exact sub_mem (hFV _ _) (hFV _ _)
  have hPYV' : PY ∈ V := by rw [hPY]; exact sub_mem (hFV _ _) (hFV _ _)
  have hMXV' : MX ∈ V := by rw [hMX]; exact add_mem (hFV _ _) (hFV _ _)
  have hMYV' : MY ∈ V := by rw [hMY]; exact add_mem (hFV _ _) (hFV _ _)
  have hTV' : T ∈ V := hFV _ _
  have hLV' : L ∈ V := hFV _ _
  have hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
    intro x hx y hy
    rw [hV] at hx hy
    induction hx, hy using Submodule.span_induction₂ with
    | mem_mem a b ha hb =>
      obtain ⟨μ, ν, rfl⟩ := ha; obtain ⟨μ', ν', rfl⟩ := hb
      exact fieldStrengthDeriv_mul_comm _ _ _ _ _ _
    | zero_left => rw [zero_mul, mul_zero]
    | zero_right => rw [zero_mul, mul_zero]
    | add_left _ _ _ _ _ _ h₁ h₂ => rw [add_mul, mul_add, h₁, h₂]
    | add_right _ _ _ _ _ _ h₁ h₂ => rw [mul_add, add_mul, h₁, h₂]
    | smul_left _ _ _ _ _ h => rw [smul_mul_assoc, mul_smul_comm, h]
    | smul_right _ _ _ _ _ h => rw [mul_smul_comm, smul_mul_assoc, h]
  have hspan : Submodule.span ℂ FF = V * V := by
    rw [hV, hFF, Submodule.span_mul_span]
    congr 1
    ext x
    constructor
    · rintro ⟨μ, ν, μ', ν', rfl⟩; exact ⟨_, ⟨μ, ν, rfl⟩, _, ⟨μ', ν', rfl⟩, rfl⟩
    · rintro ⟨a, ⟨μ, ν, rfl⟩, b, ⟨μ', ν', rfl⟩, rfl⟩; exact ⟨μ, ν, μ', ν', rfl⟩
  have hne : ∀ {X Y : Submodule ℂ JetAlgebra} {k l : ℤ}, X ≤ boostWeightSubmodule 2 k →
      Y ≤ boostWeightSubmodule 2 l → k + l ≠ 0 →
      X * Y ≤ Submodule.span ℂ S ⊔ ⨆ (j : ℤ) (_ : j ≠ 0), boostWeightSubmodule 2 j :=
    fun hX hY h => le_sup_of_le_right
      ((Submodule.mul_le.2 fun _ hx _ hy => mul_mem_boostWeightSubmodule (hX hx) (hY hy)).trans
        (le_iSup_of_le _ (le_iSup_of_le h le_rfl)))
  have hsub : ∀ {a b : JetAlgebra}, a ∈ V → b ∈ V → b * a ∈ S →
      a * b ∈ Submodule.span ℂ S := fun ha hb h => by
    rw [hcomm _ ha _ hb]; exact Submodule.subset_span h
  obtain ⟨hAC, hCA, hBB⟩ : A * C ≤ Submodule.span ℂ S ∧ C * A ≤ Submodule.span ℂ S ∧
      B * B ≤ Submodule.span ℂ S := by
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [hA, hB, hC, Submodule.span_mul_span] <;>
      refine Submodule.span_le.2 ?_ <;>
      rintro x ⟨a, rfl | rfl, b, rfl | rfl, rfl⟩
    -- `A * C` and `B * B` are products in `S`; `C * A` needs one commutation each
    exacts [Submodule.subset_span (by simp [hS]), Submodule.subset_span (by simp [hS]),
      Submodule.subset_span (by simp [hS]), Submodule.subset_span (by simp [hS]),
      hsub hMXV' hPXV' (by simp [hS]), hsub hMXV' hPYV' (by simp [hS]),
      hsub hMYV' hPXV' (by simp [hS]), hsub hMYV' hPYV' (by simp [hS]),
      Submodule.subset_span (by simp [hS]), Submodule.subset_span (by simp [hS]),
      hsub hLV' hTV' (by simp [hS]), Submodule.subset_span (by simp [hS])]
  have hkey : Submodule.span ℂ FF ≤
      Submodule.span ℂ S ⊔ ⨆ (j : ℤ) (_ : j ≠ 0), boostWeightSubmodule 2 j := by
    rw [hspan]
    refine (Submodule.mul_le.2 fun _ hx _ hy =>
      Submodule.mul_mem_mul (hVle hx) (hVle hy)).trans ?_
    simp only [Submodule.sup_mul, Submodule.mul_sup]
    repeat' apply sup_le
    -- the weights `AA, BA, CA, AB, BB, CB, AC, BC, CC = 4, 2, 0, 2, 0, -2, 0, -2, -4`
    exacts [hne hAle hAle (by norm_num), hne hBle hAle (by norm_num), le_sup_of_le_left hCA,
      hne hAle hBle (by norm_num), le_sup_of_le_left hBB, hne hCle hBle (by norm_num),
      le_sup_of_le_left hAC, hne hBle hCle (by norm_num), hne hCle hCle (by norm_num)]
  -- ### D. The weight zero part of the photon pairs
  -- The seven products have weight zero and are photon pairs, which is one inclusion. For the
  -- other, weight zero is disjoint from the sum of the nonzero weights by
  -- `boostWeightSubmodule_iSupIndep`, and the modular law removes it from the splitting above.
  have hz : ∀ {k l : ℤ} {x y : JetAlgebra}, x ∈ boostWeightSubmodule 2 k →
      y ∈ boostWeightSubmodule 2 l → k + l = 0 → x * y ∈ boostWeightSubmodule 2 0 := by
    intro k l x y hx hy h
    rw [← h]; exact mul_mem_boostWeightSubmodule hx hy
  have hSw : Submodule.span ℂ S ≤ boostWeightSubmodule 2 0 := by
    rw [hS]
    refine Submodule.span_le.2 ?_
    rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      exact hz (by assumption) (by assumption) (by norm_num)
  have hSF : Submodule.span ℂ S ≤ Submodule.span ℂ FF := by
    rw [hspan, hS]
    refine Submodule.span_le.2 ?_
    rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      exact Submodule.mul_mem_mul (by assumption) (by assumption)
  refine le_antisymm (le_trans (inf_le_inf_left _ hkey) ?_) (le_inf hSw hSF)
  rw [inf_comm, sup_inf_assoc_of_le _ hSw,
    disjoint_iff.mp (boostWeightSubmodule_iSupIndep (i := 2) 0).symm, sup_bot_eq]

/-- **The boost weight zero part of the photon pairs, `x`-direction.** As for the `z`-boost,
  with the light-cone pairs now built on the `x`-axis: `F_{0y} ∓ F_{xy}` and `F_{0z} ∓ F_{xz}`
  have weight `±2`, and `F_{yz}`, `F_{0x}` have weight zero. -/
theorem boostWeight_inter_fieldStrength_x :
    boostWeightSubmodule 0 0 ⊓ Submodule.span ℂ
        {x | ∃ μ ν μ' ν', x = fieldStrengthDeriv {} μ ν * fieldStrengthDeriv {} μ' ν'} =
      Submodule.span ℂ {(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) -
            fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) *
          (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) +
            fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)),
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) -
            fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) *
          (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) +
            fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)),
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) -
            fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) *
          (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) +
            fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)),
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) -
            fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)) *
          (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) +
            fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2)),
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2),
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0),
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0)} := by
  -- ### A. The boost eigenvectors among the field strengths
  set P1 := fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) -
    fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) with hP1
  set P2 := fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) -
    fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) with hP2
  set M1 := fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) +
    fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) with hM1
  set M2 := fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) +
    fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) with hM2
  set T := fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) with hT
  set L := fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) with hL
  set FF : Set JetAlgebra :=
    {x | ∃ μ ν μ' ν', x = fieldStrengthDeriv {} μ ν * fieldStrengthDeriv {} μ' ν'} with hFF
  set S : Set JetAlgebra := {P1 * M1, P1 * M2, P2 * M1, P2 * M2, T * T, T * L, L * L} with hS
  obtain ⟨hP1w, hP2w, hM1w, hM2w, hTw, hLw⟩ :
      P1 ∈ boostWeightSubmodule 0 2 ∧ P2 ∈ boostWeightSubmodule 0 2 ∧
      M1 ∈ boostWeightSubmodule 0 (-2) ∧ M2 ∈ boostWeightSubmodule 0 (-2) ∧
      T ∈ boostWeightSubmodule 0 0 ∧ L ∈ boostWeightSubmodule 0 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro t ht
    all_goals
      have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
      simp only [hP1, hP2, hM1, hM2, hT, hL, map_sub, map_add, boostAxis_zero,
        repLorentzGroup_fieldStrengthDeriv_nil, algebraMap_real_complex,
        toLorentzGroup_boostXel, Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three,
        boostMatX, fieldStrengthDeriv_self, mul_zero, zero_mul, mul_one, Complex.ofReal_zero,
        zero_smul, smul_zero, add_zero, zero_add]
      try rw [show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) =
        -fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) from
        fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 0)]
      push_cast
      match_scalars <;> (field_simp; try ring)
  -- ### B. Every field strength is a combination of the eigenvectors
  set A := Submodule.span ℂ {P1, P2} with hA
  set B := Submodule.span ℂ {T, L} with hB
  set C := Submodule.span ℂ {M1, M2} with hC
  set V := Submodule.span ℂ {x | ∃ μ ν, x = fieldStrengthDeriv {} μ ν} with hV
  have hAle : A ≤ boostWeightSubmodule 0 2 := by
    rw [hA]; exact Submodule.span_le.2 (by rintro x (rfl | rfl); exacts [hP1w, hP2w])
  have hBle : B ≤ boostWeightSubmodule 0 0 := by
    rw [hB]; exact Submodule.span_le.2 (by rintro x (rfl | rfl); exacts [hTw, hLw])
  have hCle : C ≤ boostWeightSubmodule 0 (-2) := by
    rw [hC]; exact Submodule.span_le.2 (by rintro x (rfl | rfl); exacts [hM1w, hM2w])
  have hAV : A ≤ A ⊔ B ⊔ C := le_sup_left.trans le_sup_left
  have hBV : B ≤ A ⊔ B ⊔ C := le_sup_right.trans le_sup_left
  have hCV : C ≤ A ⊔ B ⊔ C := le_sup_right
  have hP1V : P1 ∈ A ⊔ B ⊔ C := hAV (Submodule.subset_span (by simp))
  have hP2V : P2 ∈ A ⊔ B ⊔ C := hAV (Submodule.subset_span (by simp))
  have hTV : T ∈ A ⊔ B ⊔ C := hBV (Submodule.subset_span (by simp))
  have hLV : L ∈ A ⊔ B ⊔ C := hBV (Submodule.subset_span (by simp))
  have hM1V : M1 ∈ A ⊔ B ⊔ C := hCV (Submodule.subset_span (by simp))
  have hM2V : M2 ∈ A ⊔ B ⊔ C := hCV (Submodule.subset_span (by simp))
  have key : ∀ {u v x : JetAlgebra} (c d : ℂ), u ∈ A ⊔ B ⊔ C → v ∈ A ⊔ B ⊔ C →
      x = c • u + d • v → x ∈ A ⊔ B ⊔ C := by
    rintro u v x c d hu hv rfl
    exact add_mem (Submodule.smul_mem _ c hu) (Submodule.smul_mem _ d hv)
  have keyn : ∀ {u v : JetAlgebra} (c d : ℂ) {μ ν : Fin 1 ⊕ Fin 3}, u ∈ A ⊔ B ⊔ C →
      v ∈ A ⊔ B ⊔ C → fieldStrengthDeriv {} μ ν = c • u + d • v →
      fieldStrengthDeriv {} ν μ ∈ A ⊔ B ⊔ C := by
    intro u v c d μ ν hu hv h
    rw [fieldStrengthDeriv_antisymm, h]
    exact neg_mem (add_mem (Submodule.smul_mem _ c hu) (Submodule.smul_mem _ d hv))
  have hVle : V ≤ A ⊔ B ⊔ C := by
    rw [hV]
    refine Submodule.span_le.2 ?_
    rintro x ⟨μ, ν, rfl⟩
    match μ, ν with
    | Sum.inl 0, Sum.inl 0 | Sum.inr 0, Sum.inr 0 | Sum.inr 1, Sum.inr 1
    | Sum.inr 2, Sum.inr 2 => rw [fieldStrengthDeriv_self]; exact zero_mem _
    | Sum.inl 0, Sum.inr 1 => exact key 2⁻¹ 2⁻¹ hP1V hM1V (by rw [hP1, hM1]; module)
    | Sum.inr 1, Sum.inl 0 => exact keyn 2⁻¹ 2⁻¹ hP1V hM1V (by rw [hP1, hM1]; module)
    | Sum.inl 0, Sum.inr 2 => exact key 2⁻¹ 2⁻¹ hP2V hM2V (by rw [hP2, hM2]; module)
    | Sum.inr 2, Sum.inl 0 => exact keyn 2⁻¹ 2⁻¹ hP2V hM2V (by rw [hP2, hM2]; module)
    | Sum.inr 0, Sum.inr 1 => exact key (-2⁻¹) 2⁻¹ hP1V hM1V (by rw [hP1, hM1]; module)
    | Sum.inr 1, Sum.inr 0 => exact keyn (-2⁻¹) 2⁻¹ hP1V hM1V (by rw [hP1, hM1]; module)
    | Sum.inr 0, Sum.inr 2 => exact key (-2⁻¹) 2⁻¹ hP2V hM2V (by rw [hP2, hM2]; module)
    | Sum.inr 2, Sum.inr 0 => exact keyn (-2⁻¹) 2⁻¹ hP2V hM2V (by rw [hP2, hM2]; module)
    | Sum.inr 1, Sum.inr 2 => exact hTV
    | Sum.inr 2, Sum.inr 1 => rw [fieldStrengthDeriv_antisymm]; exact neg_mem hTV
    | Sum.inl 0, Sum.inr 0 => exact hLV
    | Sum.inr 0, Sum.inl 0 => rw [fieldStrengthDeriv_antisymm]; exact neg_mem hLV
  -- ### C. Products of two field strengths
  have hFV : ∀ μ ν, fieldStrengthDeriv {} μ ν ∈ V := fun μ ν => by
    rw [hV]; exact Submodule.subset_span ⟨μ, ν, rfl⟩
  have hP1V' : P1 ∈ V := by rw [hP1]; exact sub_mem (hFV _ _) (hFV _ _)
  have hP2V' : P2 ∈ V := by rw [hP2]; exact sub_mem (hFV _ _) (hFV _ _)
  have hM1V' : M1 ∈ V := by rw [hM1]; exact add_mem (hFV _ _) (hFV _ _)
  have hM2V' : M2 ∈ V := by rw [hM2]; exact add_mem (hFV _ _) (hFV _ _)
  have hTV' : T ∈ V := hFV _ _
  have hLV' : L ∈ V := hFV _ _
  have hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
    intro x hx y hy
    rw [hV] at hx hy
    induction hx, hy using Submodule.span_induction₂ with
    | mem_mem a b ha hb =>
      obtain ⟨μ, ν, rfl⟩ := ha; obtain ⟨μ', ν', rfl⟩ := hb
      exact fieldStrengthDeriv_mul_comm _ _ _ _ _ _
    | zero_left => rw [zero_mul, mul_zero]
    | zero_right => rw [zero_mul, mul_zero]
    | add_left _ _ _ _ _ _ h₁ h₂ => rw [add_mul, mul_add, h₁, h₂]
    | add_right _ _ _ _ _ _ h₁ h₂ => rw [mul_add, add_mul, h₁, h₂]
    | smul_left _ _ _ _ _ h => rw [smul_mul_assoc, mul_smul_comm, h]
    | smul_right _ _ _ _ _ h => rw [mul_smul_comm, smul_mul_assoc, h]
  have hspan : Submodule.span ℂ FF = V * V := by
    rw [hV, hFF, Submodule.span_mul_span]
    congr 1
    ext x
    constructor
    · rintro ⟨μ, ν, μ', ν', rfl⟩; exact ⟨_, ⟨μ, ν, rfl⟩, _, ⟨μ', ν', rfl⟩, rfl⟩
    · rintro ⟨a, ⟨μ, ν, rfl⟩, b, ⟨μ', ν', rfl⟩, rfl⟩; exact ⟨μ, ν, μ', ν', rfl⟩
  have hne : ∀ {X Y : Submodule ℂ JetAlgebra} {k l : ℤ}, X ≤ boostWeightSubmodule 0 k →
      Y ≤ boostWeightSubmodule 0 l → k + l ≠ 0 →
      X * Y ≤ Submodule.span ℂ S ⊔ ⨆ (j : ℤ) (_ : j ≠ 0), boostWeightSubmodule 0 j :=
    fun hX hY h => le_sup_of_le_right
      ((Submodule.mul_le.2 fun _ hx _ hy => mul_mem_boostWeightSubmodule (hX hx) (hY hy)).trans
        (le_iSup_of_le _ (le_iSup_of_le h le_rfl)))
  have hsub : ∀ {a b : JetAlgebra}, a ∈ V → b ∈ V → b * a ∈ S →
      a * b ∈ Submodule.span ℂ S := fun ha hb h => by
    rw [hcomm _ ha _ hb]; exact Submodule.subset_span h
  obtain ⟨hAC, hCA, hBB⟩ : A * C ≤ Submodule.span ℂ S ∧ C * A ≤ Submodule.span ℂ S ∧
      B * B ≤ Submodule.span ℂ S := by
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [hA, hB, hC, Submodule.span_mul_span] <;>
      refine Submodule.span_le.2 ?_ <;>
      rintro x ⟨a, rfl | rfl, b, rfl | rfl, rfl⟩
    exacts [Submodule.subset_span (by simp [hS]), Submodule.subset_span (by simp [hS]),
      Submodule.subset_span (by simp [hS]), Submodule.subset_span (by simp [hS]),
      hsub hM1V' hP1V' (by simp [hS]), hsub hM1V' hP2V' (by simp [hS]),
      hsub hM2V' hP1V' (by simp [hS]), hsub hM2V' hP2V' (by simp [hS]),
      Submodule.subset_span (by simp [hS]), Submodule.subset_span (by simp [hS]),
      hsub hLV' hTV' (by simp [hS]), Submodule.subset_span (by simp [hS])]
  have hkey : Submodule.span ℂ FF ≤
      Submodule.span ℂ S ⊔ ⨆ (j : ℤ) (_ : j ≠ 0), boostWeightSubmodule 0 j := by
    rw [hspan]
    refine (Submodule.mul_le.2 fun _ hx _ hy =>
      Submodule.mul_mem_mul (hVle hx) (hVle hy)).trans ?_
    simp only [Submodule.sup_mul, Submodule.mul_sup]
    repeat' apply sup_le
    exacts [hne hAle hAle (by norm_num), hne hBle hAle (by norm_num), le_sup_of_le_left hCA,
      hne hAle hBle (by norm_num), le_sup_of_le_left hBB, hne hCle hBle (by norm_num),
      le_sup_of_le_left hAC, hne hBle hCle (by norm_num), hne hCle hCle (by norm_num)]
  -- ### D. The weight zero part of the photon pairs
  have hz : ∀ {k l : ℤ} {x y : JetAlgebra}, x ∈ boostWeightSubmodule 0 k →
      y ∈ boostWeightSubmodule 0 l → k + l = 0 → x * y ∈ boostWeightSubmodule 0 0 := by
    intro k l x y hx hy h
    rw [← h]; exact mul_mem_boostWeightSubmodule hx hy
  have hSw : Submodule.span ℂ S ≤ boostWeightSubmodule 0 0 := by
    rw [hS]
    refine Submodule.span_le.2 ?_
    rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      exact hz (by assumption) (by assumption) (by norm_num)
  have hSF : Submodule.span ℂ S ≤ Submodule.span ℂ FF := by
    rw [hspan, hS]
    refine Submodule.span_le.2 ?_
    rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      exact Submodule.mul_mem_mul (by assumption) (by assumption)
  refine le_antisymm (le_trans (inf_le_inf_left _ hkey) ?_) (le_inf hSw hSF)
  rw [inf_comm, sup_inf_assoc_of_le _ hSw,
    disjoint_iff.mp (boostWeightSubmodule_iSupIndep (i := 0) 0).symm, sup_bot_eq]

/-- **The boost weight zero part of the photon pairs, `y`-direction.** As for the `z`-boost,
  with the light-cone pairs now built on the `y`-axis: `F_{0z} ∓ F_{yz}` and `F_{0x} ∓ F_{yx}`
  have weight `±2`, and `F_{zx}`, `F_{0y}` have weight zero. -/
theorem boostWeight_inter_fieldStrength_y :
    boostWeightSubmodule 1 0 ⊓ Submodule.span ℂ
        {x | ∃ μ ν μ' ν', x = fieldStrengthDeriv {} μ ν * fieldStrengthDeriv {} μ' ν'} =
      Submodule.span ℂ {(fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) -
            fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) *
          (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) +
            fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)),
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) -
            fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) *
          (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) +
            fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0)),
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) -
            fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0)) *
          (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) +
            fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)),
        (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) -
            fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0)) *
          (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) +
            fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0)),
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0),
        fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1),
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
          fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1)} := by
  -- ### A. The boost eigenvectors among the field strengths
  set P1 := fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) -
    fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) with hP1
  set P2 := fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) -
    fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) with hP2
  set M1 := fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) +
    fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) with hM1
  set M2 := fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) +
    fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) with hM2
  set T := fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) with hT
  set L := fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) with hL
  set FF : Set JetAlgebra :=
    {x | ∃ μ ν μ' ν', x = fieldStrengthDeriv {} μ ν * fieldStrengthDeriv {} μ' ν'} with hFF
  set S : Set JetAlgebra := {P1 * M1, P1 * M2, P2 * M1, P2 * M2, T * T, T * L, L * L} with hS
  obtain ⟨hP1w, hP2w, hM1w, hM2w, hTw, hLw⟩ :
      P1 ∈ boostWeightSubmodule 1 2 ∧ P2 ∈ boostWeightSubmodule 1 2 ∧
      M1 ∈ boostWeightSubmodule 1 (-2) ∧ M2 ∈ boostWeightSubmodule 1 (-2) ∧
      T ∈ boostWeightSubmodule 1 0 ∧ L ∈ boostWeightSubmodule 1 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro t ht
    all_goals
      have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
      simp only [hP1, hP2, hM1, hM2, hT, hL, map_sub, map_add, boostAxis_one,
        repLorentzGroup_fieldStrengthDeriv_nil, algebraMap_real_complex,
        toLorentzGroup_boostYel, Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three,
        boostMatY, fieldStrengthDeriv_self, mul_zero, zero_mul, mul_one, Complex.ofReal_zero,
        zero_smul, smul_zero, add_zero, zero_add]
      try rw [show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) =
        -fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) from
        fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 1)]
      push_cast
      match_scalars <;> (field_simp; try ring)
  -- ### B. Every field strength is a combination of the eigenvectors
  set A := Submodule.span ℂ {P1, P2} with hA
  set B := Submodule.span ℂ {T, L} with hB
  set C := Submodule.span ℂ {M1, M2} with hC
  set V := Submodule.span ℂ {x | ∃ μ ν, x = fieldStrengthDeriv {} μ ν} with hV
  have hAle : A ≤ boostWeightSubmodule 1 2 := by
    rw [hA]; exact Submodule.span_le.2 (by rintro x (rfl | rfl); exacts [hP1w, hP2w])
  have hBle : B ≤ boostWeightSubmodule 1 0 := by
    rw [hB]; exact Submodule.span_le.2 (by rintro x (rfl | rfl); exacts [hTw, hLw])
  have hCle : C ≤ boostWeightSubmodule 1 (-2) := by
    rw [hC]; exact Submodule.span_le.2 (by rintro x (rfl | rfl); exacts [hM1w, hM2w])
  have hAV : A ≤ A ⊔ B ⊔ C := le_sup_left.trans le_sup_left
  have hBV : B ≤ A ⊔ B ⊔ C := le_sup_right.trans le_sup_left
  have hCV : C ≤ A ⊔ B ⊔ C := le_sup_right
  have hP1V : P1 ∈ A ⊔ B ⊔ C := hAV (Submodule.subset_span (by simp))
  have hP2V : P2 ∈ A ⊔ B ⊔ C := hAV (Submodule.subset_span (by simp))
  have hTV : T ∈ A ⊔ B ⊔ C := hBV (Submodule.subset_span (by simp))
  have hLV : L ∈ A ⊔ B ⊔ C := hBV (Submodule.subset_span (by simp))
  have hM1V : M1 ∈ A ⊔ B ⊔ C := hCV (Submodule.subset_span (by simp))
  have hM2V : M2 ∈ A ⊔ B ⊔ C := hCV (Submodule.subset_span (by simp))
  have key : ∀ {u v x : JetAlgebra} (c d : ℂ), u ∈ A ⊔ B ⊔ C → v ∈ A ⊔ B ⊔ C →
      x = c • u + d • v → x ∈ A ⊔ B ⊔ C := by
    rintro u v x c d hu hv rfl
    exact add_mem (Submodule.smul_mem _ c hu) (Submodule.smul_mem _ d hv)
  have keyn : ∀ {u v : JetAlgebra} (c d : ℂ) {μ ν : Fin 1 ⊕ Fin 3}, u ∈ A ⊔ B ⊔ C →
      v ∈ A ⊔ B ⊔ C → fieldStrengthDeriv {} μ ν = c • u + d • v →
      fieldStrengthDeriv {} ν μ ∈ A ⊔ B ⊔ C := by
    intro u v c d μ ν hu hv h
    rw [fieldStrengthDeriv_antisymm, h]
    exact neg_mem (add_mem (Submodule.smul_mem _ c hu) (Submodule.smul_mem _ d hv))
  have hVle : V ≤ A ⊔ B ⊔ C := by
    rw [hV]
    refine Submodule.span_le.2 ?_
    rintro x ⟨μ, ν, rfl⟩
    match μ, ν with
    | Sum.inl 0, Sum.inl 0 | Sum.inr 0, Sum.inr 0 | Sum.inr 1, Sum.inr 1
    | Sum.inr 2, Sum.inr 2 => rw [fieldStrengthDeriv_self]; exact zero_mem _
    | Sum.inl 0, Sum.inr 2 => exact key 2⁻¹ 2⁻¹ hP1V hM1V (by rw [hP1, hM1]; module)
    | Sum.inr 2, Sum.inl 0 => exact keyn 2⁻¹ 2⁻¹ hP1V hM1V (by rw [hP1, hM1]; module)
    | Sum.inl 0, Sum.inr 0 => exact key 2⁻¹ 2⁻¹ hP2V hM2V (by rw [hP2, hM2]; module)
    | Sum.inr 0, Sum.inl 0 => exact keyn 2⁻¹ 2⁻¹ hP2V hM2V (by rw [hP2, hM2]; module)
    | Sum.inr 1, Sum.inr 2 => exact key (-2⁻¹) 2⁻¹ hP1V hM1V (by rw [hP1, hM1]; module)
    | Sum.inr 2, Sum.inr 1 => exact keyn (-2⁻¹) 2⁻¹ hP1V hM1V (by rw [hP1, hM1]; module)
    | Sum.inr 1, Sum.inr 0 => exact key (-2⁻¹) 2⁻¹ hP2V hM2V (by rw [hP2, hM2]; module)
    | Sum.inr 0, Sum.inr 1 => exact keyn (-2⁻¹) 2⁻¹ hP2V hM2V (by rw [hP2, hM2]; module)
    | Sum.inr 2, Sum.inr 0 => exact hTV
    | Sum.inr 0, Sum.inr 2 => rw [fieldStrengthDeriv_antisymm]; exact neg_mem hTV
    | Sum.inl 0, Sum.inr 1 => exact hLV
    | Sum.inr 1, Sum.inl 0 => rw [fieldStrengthDeriv_antisymm]; exact neg_mem hLV
  -- ### C. Products of two field strengths
  have hFV : ∀ μ ν, fieldStrengthDeriv {} μ ν ∈ V := fun μ ν => by
    rw [hV]; exact Submodule.subset_span ⟨μ, ν, rfl⟩
  have hP1V' : P1 ∈ V := by rw [hP1]; exact sub_mem (hFV _ _) (hFV _ _)
  have hP2V' : P2 ∈ V := by rw [hP2]; exact sub_mem (hFV _ _) (hFV _ _)
  have hM1V' : M1 ∈ V := by rw [hM1]; exact add_mem (hFV _ _) (hFV _ _)
  have hM2V' : M2 ∈ V := by rw [hM2]; exact add_mem (hFV _ _) (hFV _ _)
  have hTV' : T ∈ V := hFV _ _
  have hLV' : L ∈ V := hFV _ _
  have hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
    intro x hx y hy
    rw [hV] at hx hy
    induction hx, hy using Submodule.span_induction₂ with
    | mem_mem a b ha hb =>
      obtain ⟨μ, ν, rfl⟩ := ha; obtain ⟨μ', ν', rfl⟩ := hb
      exact fieldStrengthDeriv_mul_comm _ _ _ _ _ _
    | zero_left => rw [zero_mul, mul_zero]
    | zero_right => rw [zero_mul, mul_zero]
    | add_left _ _ _ _ _ _ h₁ h₂ => rw [add_mul, mul_add, h₁, h₂]
    | add_right _ _ _ _ _ _ h₁ h₂ => rw [mul_add, add_mul, h₁, h₂]
    | smul_left _ _ _ _ _ h => rw [smul_mul_assoc, mul_smul_comm, h]
    | smul_right _ _ _ _ _ h => rw [mul_smul_comm, smul_mul_assoc, h]
  have hspan : Submodule.span ℂ FF = V * V := by
    rw [hV, hFF, Submodule.span_mul_span]
    congr 1
    ext x
    constructor
    · rintro ⟨μ, ν, μ', ν', rfl⟩; exact ⟨_, ⟨μ, ν, rfl⟩, _, ⟨μ', ν', rfl⟩, rfl⟩
    · rintro ⟨a, ⟨μ, ν, rfl⟩, b, ⟨μ', ν', rfl⟩, rfl⟩; exact ⟨μ, ν, μ', ν', rfl⟩
  have hne : ∀ {X Y : Submodule ℂ JetAlgebra} {k l : ℤ}, X ≤ boostWeightSubmodule 1 k →
      Y ≤ boostWeightSubmodule 1 l → k + l ≠ 0 →
      X * Y ≤ Submodule.span ℂ S ⊔ ⨆ (j : ℤ) (_ : j ≠ 0), boostWeightSubmodule 1 j :=
    fun hX hY h => le_sup_of_le_right
      ((Submodule.mul_le.2 fun _ hx _ hy => mul_mem_boostWeightSubmodule (hX hx) (hY hy)).trans
        (le_iSup_of_le _ (le_iSup_of_le h le_rfl)))
  have hsub : ∀ {a b : JetAlgebra}, a ∈ V → b ∈ V → b * a ∈ S →
      a * b ∈ Submodule.span ℂ S := fun ha hb h => by
    rw [hcomm _ ha _ hb]; exact Submodule.subset_span h
  obtain ⟨hAC, hCA, hBB⟩ : A * C ≤ Submodule.span ℂ S ∧ C * A ≤ Submodule.span ℂ S ∧
      B * B ≤ Submodule.span ℂ S := by
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [hA, hB, hC, Submodule.span_mul_span] <;>
      refine Submodule.span_le.2 ?_ <;>
      rintro x ⟨a, rfl | rfl, b, rfl | rfl, rfl⟩
    exacts [Submodule.subset_span (by simp [hS]), Submodule.subset_span (by simp [hS]),
      Submodule.subset_span (by simp [hS]), Submodule.subset_span (by simp [hS]),
      hsub hM1V' hP1V' (by simp [hS]), hsub hM1V' hP2V' (by simp [hS]),
      hsub hM2V' hP1V' (by simp [hS]), hsub hM2V' hP2V' (by simp [hS]),
      Submodule.subset_span (by simp [hS]), Submodule.subset_span (by simp [hS]),
      hsub hLV' hTV' (by simp [hS]), Submodule.subset_span (by simp [hS])]
  have hkey : Submodule.span ℂ FF ≤
      Submodule.span ℂ S ⊔ ⨆ (j : ℤ) (_ : j ≠ 0), boostWeightSubmodule 1 j := by
    rw [hspan]
    refine (Submodule.mul_le.2 fun _ hx _ hy =>
      Submodule.mul_mem_mul (hVle hx) (hVle hy)).trans ?_
    simp only [Submodule.sup_mul, Submodule.mul_sup]
    repeat' apply sup_le
    exacts [hne hAle hAle (by norm_num), hne hBle hAle (by norm_num), le_sup_of_le_left hCA,
      hne hAle hBle (by norm_num), le_sup_of_le_left hBB, hne hCle hBle (by norm_num),
      le_sup_of_le_left hAC, hne hBle hCle (by norm_num), hne hCle hCle (by norm_num)]
  -- ### D. The weight zero part of the photon pairs
  have hz : ∀ {k l : ℤ} {x y : JetAlgebra}, x ∈ boostWeightSubmodule 1 k →
      y ∈ boostWeightSubmodule 1 l → k + l = 0 → x * y ∈ boostWeightSubmodule 1 0 := by
    intro k l x y hx hy h
    rw [← h]; exact mul_mem_boostWeightSubmodule hx hy
  have hSw : Submodule.span ℂ S ≤ boostWeightSubmodule 1 0 := by
    rw [hS]
    refine Submodule.span_le.2 ?_
    rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      exact hz (by assumption) (by assumption) (by norm_num)
  have hSF : Submodule.span ℂ S ≤ Submodule.span ℂ FF := by
    rw [hspan, hS]
    refine Submodule.span_le.2 ?_
    rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      exact Submodule.mul_mem_mul (by assumption) (by assumption)
  refine le_antisymm (le_trans (inf_le_inf_left _ hkey) ?_) (le_inf hSw hSF)
  rw [inf_comm, sup_inf_assoc_of_le _ hSw,
    disjoint_iff.mp (boostWeightSubmodule_iSupIndep (i := 1) 0).symm, sup_bot_eq]

/-- **The Maxwell and theta terms are the only photon pairs of boost weight zero in every
  direction.** An element of the span of the products `F_{μν} F_{μ'ν'}` has boost weight zero
  along all three axes exactly when it is a combination of `F_{μν} F^{μν}` and
  `ε^{μνρσ} F_{μν} F_{ρσ}`.

  *Here the proof is not a certificate.* The three one-axis theorems cut the span of the photon
  pairs down to a seven-dimensional space each, and the three sevens have to be intersected; the
  intersection is read off from the coefficients, which is where the dual family
  `gaugeDual` enters. The `z`-axis theorem provides the seven coefficients `a₁, …, a₇`, and five
  functionals, each a sum of at most two of the duals chosen to annihilate the `x`- or the
  `y`-axis span, cut them down to two. -/
theorem boostWeight_inter_fieldStrength_full :
    boostWeightSubmodule 0 0 ⊓ boostWeightSubmodule 1 0 ⊓
    boostWeightSubmodule 2 0 ⊓ Submodule.span ℂ
        {x | ∃ μ ν μ' ν', x = fieldStrengthDeriv {} μ ν * fieldStrengthDeriv {} μ' ν'} =
      Submodule.span ℂ {maxwellTerm, thetaTerm} := by
  have hFm : ∀ μ ν μ' ν', fieldStrengthDeriv {} μ ν * fieldStrengthDeriv {} μ' ν' ∈
      Submodule.span ℂ {x : JetAlgebra | ∃ μ ν μ' ν',
        x = fieldStrengthDeriv {} μ ν * fieldStrengthDeriv {} μ' ν'} :=
    fun μ ν μ' ν' => Submodule.subset_span ⟨μ, ν, μ', ν', rfl⟩
  have hinvM : IsInvariant maxwellTerm :=
    ⟨repJetGaugeGroupI_maxwellTerm, repLorentzGroup_maxwellTerm⟩
  have hinvT : IsInvariant thetaTerm :=
    ⟨repJetGaugeGroupI_thetaTerm, repLorentzGroup_thetaTerm⟩
  refine le_antisymm ?_ ?_
  -- ### A. The three one-axis intersections
  · intro x hx
    rw [Submodule.mem_inf, Submodule.mem_inf, Submodule.mem_inf] at hx
    obtain ⟨⟨⟨hx0, hx1⟩, hx2⟩, hxF⟩ := hx
    have hz := boostWeight_inter_fieldStrength.le (Submodule.mem_inf.2 ⟨hx2, hxF⟩)
    have hbx := boostWeight_inter_fieldStrength_x.le (Submodule.mem_inf.2 ⟨hx0, hxF⟩)
    have hby := boostWeight_inter_fieldStrength_y.le (Submodule.mem_inf.2 ⟨hx1, hxF⟩)
    -- ### B. Dual functionals annihilating the `x`- and `y`-axis spans
    have hann : ∀ (φ : JetAlgebra →ₗ[ℂ] ℂ) {T : Set JetAlgebra}, (∀ s ∈ T, φ s = 0) →
        ∀ y ∈ Submodule.span ℂ T, φ y = 0 := by
      intro φ T hT y hy
      induction hy using Submodule.span_induction with
      | mem s hs => exact hT s hs
      | zero => simp
      | add u v _ _ hu hv => rw [map_add, hu, hv, add_zero]
      | smul c u _ hu => rw [map_smul, hu, smul_zero]
    obtain ⟨e1, e2, e3, e4⟩ :
        gaugeDual (Sum.inl 0, Sum.inr 0) (Sum.inl 0, Sum.inr 1) x = 0 ∧
        (gaugeDual (Sum.inl 0, Sum.inr 1) (Sum.inr 0, Sum.inr 2) +
          gaugeDual (Sum.inl 0, Sum.inr 2) (Sum.inr 0, Sum.inr 1)) x = 0 ∧
        (gaugeDual (Sum.inl 0, Sum.inr 1) (Sum.inl 0, Sum.inr 1) +
          gaugeDual (Sum.inr 0, Sum.inr 1) (Sum.inr 0, Sum.inr 1)) x = 0 ∧
        (gaugeDual (Sum.inl 0, Sum.inr 2) (Sum.inl 0, Sum.inr 2) +
          gaugeDual (Sum.inr 0, Sum.inr 2) (Sum.inr 0, Sum.inr 2)) x = 0 := by
      refine ⟨hann _ ?_ x hbx, hann _ ?_ x hbx, hann _ ?_ x hbx, hann _ ?_ x hbx⟩ <;>
        intro s hs <;>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs <;>
        rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [LinearMap.add_apply, mul_add, add_mul, mul_sub, sub_mul, map_add, map_sub,
          gaugeDual_fieldStrength_mul, fsCoeff, Prod.mk.injEq, reduceCtorEq, Fin.isValue,
          Fin.reduceEq, Sum.inr.injEq, Sum.inl.injEq, and_false, false_and, if_false, and_true,
          true_and, if_true] <;> norm_num
    have e5 : (gaugeDual (Sum.inl 0, Sum.inr 0) (Sum.inl 0, Sum.inr 0) +
        gaugeDual (Sum.inr 0, Sum.inr 1) (Sum.inr 0, Sum.inr 1)) x = 0 := by
      refine hann _ ?_ x hby
      intro s hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [LinearMap.add_apply, mul_add, add_mul, mul_sub, sub_mul, map_add, map_sub,
          gaugeDual_fieldStrength_mul, fsCoeff, Prod.mk.injEq, reduceCtorEq, Fin.isValue,
          Fin.reduceEq, Sum.inr.injEq, Sum.inl.injEq, and_false, false_and, if_false, and_true,
          true_and, if_true] <;> norm_num
    -- ### C. The seven coefficients of the `z`-axis span, and the five relations on them
    rw [Submodule.mem_span_insert] at hz
    obtain ⟨a1, y1, hy1, rfl⟩ := hz
    rw [Submodule.mem_span_insert] at hy1
    obtain ⟨a2, y2, hy2, rfl⟩ := hy1
    rw [Submodule.mem_span_insert] at hy2
    obtain ⟨a3, y3, hy3, rfl⟩ := hy2
    rw [Submodule.mem_span_insert] at hy3
    obtain ⟨a4, y4, hy4, rfl⟩ := hy3
    rw [Submodule.mem_span_insert] at hy4
    obtain ⟨a5, y5, hy5, rfl⟩ := hy4
    rw [Submodule.mem_span_insert] at hy5
    obtain ⟨a6, y6, hy6, rfl⟩ := hy5
    obtain ⟨a7, rfl⟩ := Submodule.mem_span_singleton.1 hy6
    simp only [LinearMap.add_apply, map_add, map_smul, smul_eq_mul, mul_add, add_mul, mul_sub,
      sub_mul, map_sub, gaugeDual_fieldStrength_mul, fsCoeff, Prod.mk.injEq, reduceCtorEq,
      Fin.isValue, Fin.reduceEq, Sum.inr.injEq, Sum.inl.injEq, and_false, false_and, if_false,
      and_true, true_and, if_true, mul_zero, mul_one, add_zero, zero_add, sub_zero,
      zero_sub] at e1 e2 e3 e4 e5
    -- ### D. Two coefficients are left: the Maxwell and theta terms
    have ha3 : a3 = -a2 := by linear_combination e1
    have ha6 : a6 = -2 * a2 := by linear_combination e1 + e2
    have ha5 : a5 = -a1 := by linear_combination e5 / 2
    have ha4 : a4 = a1 := by linear_combination e3 / 2 - e5 / 2
    have ha7 : a7 = a1 := by linear_combination e4 / 2
    rw [ha3, ha4, ha5, ha6, ha7, Submodule.mem_span_pair]
    refine ⟨-a1 / 2, -a2 / 4, ?_⟩
    rw [maxwellTerm_eq, thetaTerm_eq]
    simp only [mul_add, add_mul, mul_sub, sub_mul,
      show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) =
        -fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) from
        fieldStrengthDeriv_antisymm {} (Sum.inr 0) (Sum.inr 2),
      show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) =
        -fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) from
        fieldStrengthDeriv_antisymm {} (Sum.inr 1) (Sum.inr 2),
      neg_mul, mul_neg, neg_neg, sub_neg_eq_add,
      fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 2) (Sum.inl 0) (Sum.inr 0),
      fieldStrengthDeriv_mul_comm {} {} (Sum.inl 0) (Sum.inr 1) (Sum.inl 0) (Sum.inr 0),
      fieldStrengthDeriv_mul_comm {} {} (Sum.inr 1) (Sum.inr 2) (Sum.inl 0) (Sum.inr 0),
      fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 2) (Sum.inl 0) (Sum.inr 1),
      fieldStrengthDeriv_mul_comm {} {} (Sum.inr 1) (Sum.inr 2) (Sum.inl 0) (Sum.inr 1),
      fieldStrengthDeriv_mul_comm {} {} (Sum.inr 1) (Sum.inr 2) (Sum.inr 0) (Sum.inr 2),
      fieldStrengthDeriv_mul_comm {} {} (Sum.inr 0) (Sum.inr 1) (Sum.inl 0) (Sum.inr 2)]
    match_scalars <;> ring
  -- ### E. Both terms are invariant, hence of weight zero along every axis
  · rw [Submodule.span_le]
    rintro y (rfl | rfl)
    · refine ⟨⟨⟨mem_boostWeightSubmodule_zero_of_isInvariant hinvM,
        mem_boostWeightSubmodule_zero_of_isInvariant hinvM⟩,
        mem_boostWeightSubmodule_zero_of_isInvariant hinvM⟩, ?_⟩
      rw [maxwellTerm_eq]
      exact add_mem (add_mem (add_mem (add_mem (add_mem
        (Submodule.smul_mem _ _ (hFm _ _ _ _)) (Submodule.smul_mem _ _ (hFm _ _ _ _)))
        (Submodule.smul_mem _ _ (hFm _ _ _ _))) (Submodule.smul_mem _ _ (hFm _ _ _ _)))
        (Submodule.smul_mem _ _ (hFm _ _ _ _))) (Submodule.smul_mem _ _ (hFm _ _ _ _))
    · refine ⟨⟨⟨mem_boostWeightSubmodule_zero_of_isInvariant hinvT,
        mem_boostWeightSubmodule_zero_of_isInvariant hinvT⟩,
        mem_boostWeightSubmodule_zero_of_isInvariant hinvT⟩, ?_⟩
      rw [thetaTerm_eq]
      exact add_mem (add_mem (Submodule.smul_mem _ _ (hFm _ _ _ _))
        (Submodule.smul_mem _ _ (hFm _ _ _ _))) (Submodule.smul_mem _ _ (hFm _ _ _ _))

end JetAlgebra

end LeptonGaugeSector

end
