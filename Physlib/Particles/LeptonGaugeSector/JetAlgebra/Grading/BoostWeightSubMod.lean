/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.Grading.BoostWeight
/-!
# The boost weight zero parts of the photon pairs and the fermion kinetic bilinears

The products `F_{μν} F_{μ'ν'}` of two field strengths span a submodule of the jet algebra, as do
the fermion kinetic bilinears `ψ̄_α ∂_μ ψ_β`. This file computes the intersections of these spans
with the boost weight zero submodule: they are spanned by seven, respectively six, explicit
products, and both spans are written out in the statements of the two theorems below.

*The proof is a certificate.* Rather than deducing the intersection abstractly, the span of the
products is expanded into boost eigenvectors. The coordinate components `F_{μν}` are not boost
eigenvectors, but six combinations of them are: the light-cone combinations `F_{0x} - F_{zx}` and
`F_{0y} - F_{zy}` of weight `2`, their partners `F_{0x} + F_{zx}` and `F_{0y} + F_{zy}` of weight
`-2`, and the two components with no free light-cone index, `F_{xy}` and `F_{0z}`, of weight `0`.
Every `F_{μν}` is a combination of these six — the sixteen cases of step B — so the span of the
products lies in the sum of the nine products of the three weight spaces, of weights `0, ±2, ±4`.
The three of weight zero — a weight-`2` field strength against a weight-`-2` one, and two
weight-zero ones — are exactly the seven products listed.

The intersection then follows formally, with no linear independence of the products needed. The
weight submodules are independent (`boostWeightSubmodule_iSupIndep`), so boost weight zero is
disjoint from the span of the weights `±2, ±4`; since the weight-zero part sits inside boost
weight zero, the modular law cuts the intersection down to it.

The fermion bilinears follow the same pattern with less bookkeeping: the left factors `ψ̄_α` are
already eigenvectors of weight `∓1`, and on `∂_μ ψ_β` the spinor index contributes `∓1` while the
light-cone derivative combinations `(∂_0 ∓ ∂_z) ψ_β` add `±2`. The six weight-zero bilinears are
listed as `±`-pairs grouped into a `∂_0/∂_z` block and `∂_x`, `∂_y` blocks, adapted to a later
restriction by the boost weights in the `x`- and `y`-directions.

## i. Overview

Each proof runs in four steps, marked in its source. Step A exhibits the boost eigenvectors,
step B decomposes the coordinate components (or, for the bilinears, spans the weight-zero
products), step C splits every product into eigen products of a single weight, and step D
assembles the intersection.

## ii. Key results

- `JetAlgebra.boostWeight_inter_fieldStrength` : the intersection of boost weight zero with the
  span of the products `F_{μν} F_{μ'ν'}` is the span of the seven weight-zero products.
- `JetAlgebra.boostWeight_inter_fermionic_kinetic_term` : the intersection of boost weight zero
  with the span of the bilinears `ψ̄_α ∂_μ ψ_β` is the span of six explicit bilinears, paired
  into blocks adapted to the boosts in the `x`- and `y`-directions.

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

/-- **The boost weight zero part of the photon pairs.** An element of the span of the products
  `F_{μν} F_{μ'ν'}` of two field strengths has boost weight zero exactly when it is a combination
  of the seven products of a weight-`2` light-cone field strength `F_{0x} - F_{zx}`,
  `F_{0y} - F_{zy}` with a weight-`-2` one `F_{0x} + F_{zx}`, `F_{0y} + F_{zy}`, and of the
  weight-zero components `F_{xy}` and `F_{0z}` with each other. -/
theorem boostWeight_inter_fieldStrength :
    boostWeightSubmodule 0 ⊓ Submodule.span ℂ
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
  have hPXw : PX ∈ boostWeightSubmodule 2 := fieldStrengthDeriv_lightCone_mem_two
  have hMXw : MX ∈ boostWeightSubmodule (-2) := fieldStrengthDeriv_lightCone_mem_neg_two
  have hTw : T ∈ boostWeightSubmodule 0 := fieldStrengthDeriv_transverse_mem_zero
  obtain ⟨hPYw, hMYw, hLw⟩ : PY ∈ boostWeightSubmodule 2 ∧ MY ∈ boostWeightSubmodule (-2) ∧
      L ∈ boostWeightSubmodule 0 := by
    refine ⟨?_, ?_, ?_⟩ <;> intro t ht
    all_goals
      have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
      simp only [hPY, hMY, hL, map_sub, map_add, repLorentzGroup_fieldStrengthDeriv_nil,
        toLorentzGroup_boostZel, Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three,
        boostMatZ, fieldStrengthDeriv_self, mul_zero, zero_mul, mul_one, Complex.ofReal_zero,
        zero_smul, smul_zero, add_zero, zero_add]
      try rw [show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) =
        -fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) from
        fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 2)]
      push_cast
      match_scalars <;> (field_simp; ring)
  -- ### B. Every field strength is a combination of the eigenvectors
  -- On the light-cone pairs this is `F_{0x} = ((F_{0x} - F_{zx}) + (F_{0x} + F_{zx}))/2` and its
  -- partners; the remaining components are zero, `±F_{xy}`, or `±F_{0z}` by antisymmetry.
  set A := Submodule.span ℂ {PX, PY} with hA
  set B := Submodule.span ℂ {T, L} with hB
  set C := Submodule.span ℂ {MX, MY} with hC
  set V := Submodule.span ℂ {x | ∃ μ ν, x = fieldStrengthDeriv {} μ ν} with hV
  have hAle : A ≤ boostWeightSubmodule 2 := by
    rw [hA]; exact Submodule.span_le.2 (by rintro x (rfl | rfl); exacts [hPXw, hPYw])
  have hBle : B ≤ boostWeightSubmodule 0 := by
    rw [hB]; exact Submodule.span_le.2 (by rintro x (rfl | rfl); exacts [hTw, hLw])
  have hCle : C ≤ boostWeightSubmodule (-2) := by
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
  have hne : ∀ {X Y : Submodule ℂ JetAlgebra} {k l : ℤ}, X ≤ boostWeightSubmodule k →
      Y ≤ boostWeightSubmodule l → k + l ≠ 0 →
      X * Y ≤ Submodule.span ℂ S ⊔ ⨆ (j : ℤ) (_ : j ≠ 0), boostWeightSubmodule j :=
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
      Submodule.span ℂ S ⊔ ⨆ (j : ℤ) (_ : j ≠ 0), boostWeightSubmodule j := by
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
  have hz : ∀ {k l : ℤ} {x y : JetAlgebra}, x ∈ boostWeightSubmodule k →
      y ∈ boostWeightSubmodule l → k + l = 0 → x * y ∈ boostWeightSubmodule 0 := by
    intro k l x y hx hy h
    rw [← h]; exact mul_mem_boostWeightSubmodule hx hy
  have hSw : Submodule.span ℂ S ≤ boostWeightSubmodule 0 := by
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
    disjoint_iff.mp (boostWeightSubmodule_iSupIndep 0).symm, sup_bot_eq]

/-- **The boost weight zero part of the fermion kinetic bilinears.** An element of the span of
  the products `ψ̄_α ∂_μ ψ_β` has boost weight zero exactly when it is a combination of the six
  bilinears listed. Both spinor indices carry `z`-boost weight `∓1` for the index `0, 1` and the
  derivative index carries `±2` on the light-cone combinations `∂_0 ∓ ∂_z` and `0` on `∂_x, ∂_y`,
  so the weight-zero bilinears pair the spinor indices `(0,0)` and `(1,1)` with the matching
  light-cone derivative and the mixed spinor indices with a transverse derivative.

  The six spanning elements are chosen with the later restriction by the boost weights in the
  `x`- and `y`-directions in mind: they pair into a `∂_0/∂_z` block and `∂_x` and `∂_y` blocks,
  and in each transverse block the two sign combinations `ψ̄_0 ∂_i ψ_1 ± ψ̄_1 ∂_i ψ_0` split the
  spinor content into the part that is diagonal for the boost in the `i`-direction and the part
  that is not, so their weight decompositions in those directions are immediate. -/
theorem boostWeight_inter_fermionic_kinetic_term :
    boostWeightSubmodule 0 ⊓ Submodule.span ℂ
        {x | ∃ α μ β, x = Dbarψ [] α * Dψ [μ] β} =
      Submodule.span ℂ
        {Dbarψ [] 0 * (Dψ [Sum.inl 0] 0 - Dψ [Sum.inr 2] 0) +
            Dbarψ [] 1 * (Dψ [Sum.inl 0] 1 + Dψ [Sum.inr 2] 1),
          Dbarψ [] 0 * (Dψ [Sum.inl 0] 0 - Dψ [Sum.inr 2] 0) -
            Dbarψ [] 1 * (Dψ [Sum.inl 0] 1 + Dψ [Sum.inr 2] 1),
          Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0,
          Dbarψ [] 0 * Dψ [Sum.inr 0] 1 - Dbarψ [] 1 * Dψ [Sum.inr 0] 0,
          Dbarψ [] 0 * Dψ [Sum.inr 1] 1 + Dbarψ [] 1 * Dψ [Sum.inr 1] 0,
          Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0} := by
  -- ### A. The boost eigenvectors among the first-order fermion coordinates
  -- `ψ̄_α` is an eigenvector of weight `∓1` for `α = 0, 1`; on `∂_μ ψ_β` the spinor index
  -- contributes `∓1` and the light-cone derivative combinations `(∂_0 ∓ ∂_z) ψ_β` add `±2`.
  set B0 := Dbarψ [] 0 with hB0
  set B1 := Dbarψ [] 1 with hB1
  set P0 := Dψ [Sum.inl 0] 0 - Dψ [Sum.inr 2] 0 with hP0
  set P1 := Dψ [Sum.inl 0] 1 - Dψ [Sum.inr 2] 1 with hP1
  set M0 := Dψ [Sum.inl 0] 0 + Dψ [Sum.inr 2] 0 with hM0
  set M1 := Dψ [Sum.inl 0] 1 + Dψ [Sum.inr 2] 1 with hM1
  set X0 := Dψ [Sum.inr 0] 0 with hX0
  set X1 := Dψ [Sum.inr 0] 1 with hX1
  set Y0 := Dψ [Sum.inr 1] 0 with hY0
  set Y1 := Dψ [Sum.inr 1] 1 with hY1
  set FF : Set JetAlgebra := {x | ∃ α μ β, x = Dbarψ [] α * Dψ [μ] β} with hFF
  set S : Set JetAlgebra := {B0 * P0 + B1 * M1, B0 * P0 - B1 * M1, B0 * X1 + B1 * X0,
    B0 * X1 - B1 * X0, B0 * Y1 + B1 * Y0, B0 * Y1 - B1 * Y0} with hS
  set W := Submodule.span ℂ S ⊔ ⨆ (j : ℤ) (_ : j ≠ 0), boostWeightSubmodule j with hW
  have hB0w : B0 ∈ boostWeightSubmodule (-1) := Dbarψ_nil_zero_mem_neg_one
  have hB1w : B1 ∈ boostWeightSubmodule 1 := Dbarψ_nil_one_mem_one
  obtain ⟨hP0w, hP1w, hM0w, hM1w, hX0w, hX1w, hY0w, hY1w⟩ :
      P0 ∈ boostWeightSubmodule 1 ∧ P1 ∈ boostWeightSubmodule 3 ∧
      M0 ∈ boostWeightSubmodule (-3) ∧ M1 ∈ boostWeightSubmodule (-1) ∧
      X0 ∈ boostWeightSubmodule (-1) ∧ X1 ∈ boostWeightSubmodule 1 ∧
      Y0 ∈ boostWeightSubmodule (-1) ∧ Y1 ∈ boostWeightSubmodule 1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro t ht
    all_goals
      have ht' : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
      simp only [hP0, hP1, hM0, hM1, hX0, hX1, hY0, hY1, map_sub, map_add,
        repLorentzGroup_Dψ_singleton, toLorentzGroup_boostZel, boostZel_inv_coe, boostMatZ,
        Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three, Fin.sum_univ_two,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue,
        Complex.star_def, map_zero, star_zero, Complex.conj_ofReal, Complex.ofReal_zero,
        Complex.ofReal_one, mul_zero, zero_mul, mul_one, one_mul, zero_smul, smul_zero,
        add_zero, zero_add]
      push_cast
      match_scalars <;> (field_simp; try ring)
  -- ### B. The six weight-zero bilinears lie in the span of the pairs
  have hSW : Submodule.span ℂ S ≤ W := le_sup_left
  have hpm : ∀ {u v : JetAlgebra}, u + v ∈ S → u - v ∈ S → u ∈ W ∧ v ∈ W := by
    intro u v h₁ h₂
    have e₁ : u + v ∈ W := hSW (Submodule.subset_span h₁)
    have e₂ : u - v ∈ W := hSW (Submodule.subset_span h₂)
    constructor
    · rw [show u = (2⁻¹ : ℂ) • (u + v) + (2⁻¹ : ℂ) • (u - v) from by module]
      exact add_mem (Submodule.smul_mem _ _ e₁) (Submodule.smul_mem _ _ e₂)
    · rw [show v = (2⁻¹ : ℂ) • (u + v) - (2⁻¹ : ℂ) • (u - v) from by module]
      exact sub_mem (Submodule.smul_mem _ _ e₁) (Submodule.smul_mem _ _ e₂)
  obtain ⟨k1, k8⟩ : B0 * P0 ∈ W ∧ B1 * M1 ∈ W := hpm (by simp [hS]) (by simp [hS])
  obtain ⟨kx0, kx1⟩ : B0 * X1 ∈ W ∧ B1 * X0 ∈ W := hpm (by simp [hS]) (by simp [hS])
  obtain ⟨ky0, ky1⟩ : B0 * Y1 ∈ W ∧ B1 * Y0 ∈ W := hpm (by simp [hS]) (by simp [hS])
  -- ### C. Every bilinear splits into eigen bilinears of a single weight
  -- The ten bilinears of nonzero weight, and the decomposition of `∂_0 ψ_β` and `∂_z ψ_β` into
  -- the light-cone combinations.
  have hm : ∀ {k l : ℤ} {x y : JetAlgebra}, x ∈ boostWeightSubmodule k →
      y ∈ boostWeightSubmodule l → k + l ≠ 0 → x * y ∈ W := fun hx hy h =>
    Submodule.mem_sup_right (Submodule.mem_iSup_of_mem _
      (Submodule.mem_iSup_of_mem h (mul_mem_boostWeightSubmodule hx hy)))
  have k2 : B0 * M0 ∈ W := hm hB0w hM0w (by norm_num)
  have k3 : B0 * P1 ∈ W := hm hB0w hP1w (by norm_num)
  have k4 : B0 * M1 ∈ W := hm hB0w hM1w (by norm_num)
  have k5 : B1 * P0 ∈ W := hm hB1w hP0w (by norm_num)
  have k6 : B1 * M0 ∈ W := hm hB1w hM0w (by norm_num)
  have k7 : B1 * P1 ∈ W := hm hB1w hP1w (by norm_num)
  have key : ∀ {a u v : JetAlgebra} (c d : ℂ) {y : JetAlgebra}, a * u ∈ W → a * v ∈ W →
      y = c • u + d • v → a * y ∈ W := by
    rintro a u v c d y hu hv rfl
    rw [mul_add, mul_smul_comm, mul_smul_comm]
    exact add_mem (Submodule.smul_mem _ _ hu) (Submodule.smul_mem _ _ hv)
  have hkey : Submodule.span ℂ FF ≤ W := by
    rw [hFF]
    refine Submodule.span_le.2 ?_
    rintro x ⟨α, μ, β, rfl⟩
    match α, μ, β with
    | 0, Sum.inl 0, 0 => exact key 2⁻¹ 2⁻¹ k1 k2 (by rw [hP0, hM0]; module)
    | 0, Sum.inr 2, 0 => exact key (-2⁻¹) 2⁻¹ k1 k2 (by rw [hP0, hM0]; module)
    | 0, Sum.inl 0, 1 => exact key 2⁻¹ 2⁻¹ k3 k4 (by rw [hP1, hM1]; module)
    | 0, Sum.inr 2, 1 => exact key (-2⁻¹) 2⁻¹ k3 k4 (by rw [hP1, hM1]; module)
    | 1, Sum.inl 0, 0 => exact key 2⁻¹ 2⁻¹ k5 k6 (by rw [hP0, hM0]; module)
    | 1, Sum.inr 2, 0 => exact key (-2⁻¹) 2⁻¹ k5 k6 (by rw [hP0, hM0]; module)
    | 1, Sum.inl 0, 1 => exact key 2⁻¹ 2⁻¹ k7 k8 (by rw [hP1, hM1]; module)
    | 1, Sum.inr 2, 1 => exact key (-2⁻¹) 2⁻¹ k7 k8 (by rw [hP1, hM1]; module)
    | 0, Sum.inr 0, 0 => exact hm hB0w hX0w (by norm_num)
    | 0, Sum.inr 0, 1 => exact kx0
    | 0, Sum.inr 1, 0 => exact hm hB0w hY0w (by norm_num)
    | 0, Sum.inr 1, 1 => exact ky0
    | 1, Sum.inr 0, 0 => exact kx1
    | 1, Sum.inr 0, 1 => exact hm hB1w hX1w (by norm_num)
    | 1, Sum.inr 1, 0 => exact ky1
    | 1, Sum.inr 1, 1 => exact hm hB1w hY1w (by norm_num)
  -- ### D. The intersection
  have hz : ∀ {k l : ℤ} {x y : JetAlgebra}, x ∈ boostWeightSubmodule k →
      y ∈ boostWeightSubmodule l → k + l = 0 → x * y ∈ boostWeightSubmodule 0 := by
    intro k l x y hx hy h
    rw [← h]; exact mul_mem_boostWeightSubmodule hx hy
  have hSw : Submodule.span ℂ S ≤ boostWeightSubmodule 0 := by
    rw [hS]
    refine Submodule.span_le.2 ?_
    rintro x (rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [add_mem (hz hB0w hP0w (by norm_num)) (hz hB1w hM1w (by norm_num)),
      sub_mem (hz hB0w hP0w (by norm_num)) (hz hB1w hM1w (by norm_num)),
      add_mem (hz hB0w hX1w (by norm_num)) (hz hB1w hX0w (by norm_num)),
      sub_mem (hz hB0w hX1w (by norm_num)) (hz hB1w hX0w (by norm_num)),
      add_mem (hz hB0w hY1w (by norm_num)) (hz hB1w hY0w (by norm_num)),
      sub_mem (hz hB0w hY1w (by norm_num)) (hz hB1w hY0w (by norm_num))]
  have hFm : ∀ α μ β, Dbarψ [] α * Dψ [μ] β ∈ Submodule.span ℂ FF := fun α μ β => by
    rw [hFF]; exact Submodule.subset_span ⟨α, μ, β, rfl⟩
  have hSF : Submodule.span ℂ S ≤ Submodule.span ℂ FF := by
    rw [hS]
    refine Submodule.span_le.2 ?_
    rintro x (rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp only [hB0, hB1, hP0, hM1, hX0, hX1, hY0, hY1, mul_sub, mul_add] <;>
      repeat' first | exact hFm _ _ _ | apply add_mem | apply sub_mem | apply neg_mem
  refine le_antisymm (le_trans (inf_le_inf_left _ hkey) ?_) (le_inf hSw hSF)
  rw [hW, inf_comm, sup_inf_assoc_of_le _ hSw,
    disjoint_iff.mp (boostWeightSubmodule_iSupIndep 0).symm, sup_bot_eq]

end JetAlgebra

end LeptonGaugeSector

end
