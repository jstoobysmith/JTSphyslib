/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsFermionSector.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.GaugeWeightDecomposition
/-!
# The gauge weight decomposition of the fermion sector

The gauge torus acts diagonally on the basis of each fermion value space, with
weights given by the colour and isospin weights of the fundamental representations
and the species' hypercharge. Through the dual (and, for the barred species, the
conjugate-dual) this makes every symbol component a simultaneous eigenvector, and the
derivative submodules of the fermion sector decompose by gauge weight
(`derivSubmoduleGaugeWeight`), for every number of covariant derivatives.

-/

@[expose] public section

namespace StandardModel

open Matrix MatrixGroups

/-!

## A. `expI` helpers

-/

lemma starRingEnd_expI_pow (n : ℕ) :
    ((starRingEnd ℂ) (expI : ℂ)) ^ n = ((expI : ℂ) ^ n)⁻¹ := by
  rw [← inv_pow, expI_inv_eq_star]
  rfl

lemma starRingEnd_expI_zpow (z : ℤ) :
    (starRingEnd ℂ) ((expI : ℂ) ^ z) = (expI : ℂ) ^ (-z) := by
  rw [map_zpow₀, _root_.zpow_neg, ← _root_.inv_zpow]
  congr 1
  rw [expI_inv_eq_star]
  rfl

lemma expI_zpow_ne_zero (z : ℤ) : ((expI : ℂ) ^ z) ≠ 0 :=
  zpow_ne_zero _ (by simpa [expI] using Complex.exp_ne_zero Complex.I)

/-!

## B. The torus weights of the fermion value spaces

-/

/-- The colour weights of the fundamental of `SU(3)` against the two colour torus
  generators. -/
def colourWeight (c : Fin 3) : ℤ × ℤ := ![(1, 0), (-1, 1), (0, -1)] c

/-- The isospin weight of the fundamental of `SU(2)` against the isospin torus
  generator. -/
def isoWeight (s : Fin 2) : ℤ := ![1, -1] s

/-- The gauge weight of the down-singlet basis: the colour weights and hypercharge
  `-2`. -/
def DownSinglet.valueGaugeWeight (j : Fin 2 × Fin 3) : GaugeWeight :=
  ((colourWeight j.2).1, (colourWeight j.2).2, 0, -2)

/-- The gauge weight of the up-singlet basis: the colour weights and hypercharge
  `4`. -/
def UpSinglet.valueGaugeWeight (j : Fin 2 × Fin 3) : GaugeWeight :=
  ((colourWeight j.2).1, (colourWeight j.2).2, 0, 4)

/-- The gauge weight of the quark-doublet basis: the colour and isospin weights and
  hypercharge `1`. -/
def QuarkDoublet.valueGaugeWeight (j : Fin 2 × Fin 3 × Fin 2) : GaugeWeight :=
  ((colourWeight j.2.1).1, (colourWeight j.2.1).2, isoWeight j.2.2, 1)

/-- The gauge weight of the lepton-doublet basis: the isospin weight and hypercharge
  `-3`. -/
def LeptonDoublet.valueGaugeWeight (j : Fin 2 × Fin 2) : GaugeWeight :=
  (0, 0, isoWeight j.2, -3)

/-- The gauge weight of the lepton-singlet basis: hypercharge `-6`. -/
def LeptonSinglet.valueGaugeWeight (_ : Fin 2) : GaugeWeight :=
  (0, 0, 0, -6)

/-!

## C. The torus action on the value-space bases

-/

/-- The gauge torus acts diagonally on the basis of `DownSinglet`, with the weights
  `DownSinglet.valueGaugeWeight`. -/
lemma DownSinglet.repGaugeGroupI_gaugeTorusGen_basis (i : Fin 4) (j : Fin 2 × Fin 3) :
    DownSinglet.repGaugeGroupI (gaugeTorusGen i) (DownSinglet.basis j)
      = ((expI : ℂ) ^ GaugeWeight.coord (DownSinglet.valueGaugeWeight j) i) •
        DownSinglet.basis j := by
  obtain ⟨k, c⟩ := j
  have hb : DownSinglet.basis (k, c) = ⟨Fermion.RightHandedWeyl.basis k ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 3) ℂ c⟩ := by
    simp only [DownSinglet.basis, Module.Basis.map_apply, Module.Basis.tensorProduct_apply, OrthonormalBasis.coe_toBasis]
    rfl
  rw [hb, DownSinglet.repGaugeGroupI_tmul_basis_eq_sum]
  fin_cases i <;> fin_cases c <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, GaugeGroupI.toSU3, su3ExpIOne, su3ExpITwo, Fin.sum_univ_three,
      Matrix.diagonal,
      DownSinglet.valueGaugeWeight, colourWeight, isoWeight, GaugeWeight.coord,
      expI_inv_eq_star, Complex.star_def, starRingEnd_expI_pow, hb] <;>
  (try (congr 1 <;> norm_num))

/-- The gauge torus acts diagonally on the basis of `UpSinglet`, with the weights
  `UpSinglet.valueGaugeWeight`. -/
lemma UpSinglet.repGaugeGroupI_gaugeTorusGen_basis (i : Fin 4) (j : Fin 2 × Fin 3) :
    UpSinglet.repGaugeGroupI (gaugeTorusGen i) (UpSinglet.basis j)
      = ((expI : ℂ) ^ GaugeWeight.coord (UpSinglet.valueGaugeWeight j) i) •
        UpSinglet.basis j := by
  obtain ⟨k, c⟩ := j
  have hb : UpSinglet.basis (k, c) = ⟨Fermion.RightHandedWeyl.basis k ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 3) ℂ c⟩ := by
    simp only [UpSinglet.basis, Module.Basis.map_apply, Module.Basis.tensorProduct_apply, OrthonormalBasis.coe_toBasis]
    rfl
  rw [hb, UpSinglet.repGaugeGroupI_tmul_basis_eq_sum]
  fin_cases i <;> fin_cases c <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, GaugeGroupI.toSU3, su3ExpIOne, su3ExpITwo, Fin.sum_univ_three,
      Matrix.diagonal,
      UpSinglet.valueGaugeWeight, colourWeight, isoWeight, GaugeWeight.coord,
      expI_inv_eq_star, Complex.star_def, starRingEnd_expI_pow, hb] <;>
  (try (congr 1 <;> norm_num))

/-- The gauge torus acts diagonally on the basis of `QuarkDoublet`, with the weights
  `QuarkDoublet.valueGaugeWeight`. -/
lemma QuarkDoublet.repGaugeGroupI_gaugeTorusGen_basis (i : Fin 4) (j : Fin 2 × Fin 3 × Fin 2) :
    QuarkDoublet.repGaugeGroupI (gaugeTorusGen i) (QuarkDoublet.basis j)
      = ((expI : ℂ) ^ GaugeWeight.coord (QuarkDoublet.valueGaugeWeight j) i) •
        QuarkDoublet.basis j := by
  obtain ⟨k, c, s⟩ := j
  have hb : QuarkDoublet.basis (k, c, s) = ⟨Fermion.LeftHandedWeyl.basis k ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 3) ℂ c ⊗ₜ[ℂ]
      EuclideanSpace.basisFun (Fin 2) ℂ s⟩ := by
    simp only [QuarkDoublet.basis, Module.Basis.map_apply, Module.Basis.tensorProduct_apply, OrthonormalBasis.coe_toBasis,
      Module.Basis.reindex_apply, Equiv.prodAssoc_symm_apply]
    rfl
  rw [hb, QuarkDoublet.repGaugeGroupI_tmul_basis_eq_sum]
  fin_cases i <;> fin_cases c <;> fin_cases s <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, GaugeGroupI.toSU3, su3ExpIOne, su3ExpITwo, Fin.sum_univ_three, GaugeGroupI.toSU2, su2ExpI, Fin.sum_univ_two,
      Matrix.diagonal,
      QuarkDoublet.valueGaugeWeight, colourWeight, isoWeight, GaugeWeight.coord,
      expI_inv_eq_star, Complex.star_def, starRingEnd_expI_pow, hb] <;>
  (try (congr 1 <;> norm_num))

/-- The gauge torus acts diagonally on the basis of `LeptonDoublet`, with the weights
  `LeptonDoublet.valueGaugeWeight`. -/
lemma LeptonDoublet.repGaugeGroupI_gaugeTorusGen_basis (i : Fin 4) (j : Fin 2 × Fin 2) :
    LeptonDoublet.repGaugeGroupI (gaugeTorusGen i) (LeptonDoublet.basis j)
      = ((expI : ℂ) ^ GaugeWeight.coord (LeptonDoublet.valueGaugeWeight j) i) •
        LeptonDoublet.basis j := by
  obtain ⟨k, s⟩ := j
  have hb : LeptonDoublet.basis (k, s) = ⟨Fermion.LeftHandedWeyl.basis k ⊗ₜ[ℂ] EuclideanSpace.basisFun (Fin 2) ℂ s⟩ := by
    simp only [LeptonDoublet.basis, Module.Basis.map_apply, Module.Basis.tensorProduct_apply, OrthonormalBasis.coe_toBasis]
    rfl
  rw [hb, LeptonDoublet.repGaugeGroupI_tmul_basis_eq_sum]
  fin_cases i <;> fin_cases s <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, GaugeGroupI.toSU2, su2ExpI, Fin.sum_univ_two,
      Matrix.diagonal,
      LeptonDoublet.valueGaugeWeight, colourWeight, isoWeight, GaugeWeight.coord,
      expI_inv_eq_star, Complex.star_def, starRingEnd_expI_pow, hb] <;>
  (try (congr 1 <;> norm_num))

/-- The gauge torus acts diagonally on the basis of `LeptonSinglet`, with the weights
  `LeptonSinglet.valueGaugeWeight`. -/
lemma LeptonSinglet.repGaugeGroupI_gaugeTorusGen_basis (i : Fin 4) (j : Fin 2) :
    LeptonSinglet.repGaugeGroupI (gaugeTorusGen i) (LeptonSinglet.basis j)
      = ((expI : ℂ) ^ GaugeWeight.coord (LeptonSinglet.valueGaugeWeight j) i) •
        LeptonSinglet.basis j := by
  have hb : LeptonSinglet.basis j = ⟨Fermion.RightHandedWeyl.basis j⟩ := by
    simp only [LeptonSinglet.basis, Module.Basis.map_apply]
    rfl
  rw [hb, LeptonSinglet.repGaugeGroupI_basis]
  fin_cases i <;>
    simp [gaugeTorusGen, GaugeGroupI.toU1, Matrix.diagonal,
      LeptonSinglet.valueGaugeWeight, colourWeight, isoWeight, GaugeWeight.coord,
      expI_inv_eq_star, Complex.star_def, starRingEnd_expI_pow, hb] <;>
  (try (congr 1 <;> norm_num))

/-!

## D. The dual and conjugate-dual actions on the coordinate functionals

-/

section Bridges

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι] [DecidableEq ι]

lemma dual_gaugeTorusGen_coord (ρ : Representation ℂ GaugeGroupI V)
    (b : Module.Basis ι ℂ V) (g : GaugeGroupI) (w : ι → ℤ)
    (hb : ∀ j, ρ g (b j) = ((expI : ℂ) ^ w j) • b j) (j : ι) :
    ρ.dual g (b.coord j) = ((expI : ℂ) ^ (-(w j))) • b.coord j := by
  have hinv : ∀ j', ρ g⁻¹ (b j') = ((expI : ℂ) ^ (-(w j'))) • b j' := by
    intro j'
    have h1 : ρ g⁻¹ (ρ g (b j')) = b j' := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
    rw [hb j', map_smul] at h1
    rw [_root_.zpow_neg]
    exact ((inv_smul_eq_iff₀ (expI_zpow_ne_zero (w j'))).mpr h1.symm).symm
  refine b.ext fun j' => ?_
  rw [Representation.dual_apply]
  simp only [Module.Dual.transpose_apply, LinearMap.comp_apply, hinv j', map_smul,
    LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self, smul_eq_mul]
  by_cases hne : j' = j
  · subst hne
    simp
  · simp [Finsupp.single_apply, hne]

lemma conj_gaugeTorusGen_basis (ρ : Representation ℂ GaugeGroupI V)
    (b : Module.Basis ι ℂ V) (g : GaugeGroupI) (w : ι → ℤ)
    (hb : ∀ j, ρ g (b j) = ((expI : ℂ) ^ w j) • b j) (j : ι) :
    ρ.conj g (Module.Basis.conj b j)
      = ((expI : ℂ) ^ (-(w j))) • Module.Basis.conj b j := by
  simp only [Module.Basis.conj_apply, Representation.conj_apply,
    LinearEquiv.symm_apply_apply, hb j, map_smulₛₗ, starRingEnd_expI_zpow]

lemma range_eq_iSup_span {M : Type} [AddCommGroup M] [Module ℂ M]
    (b : Module.Basis ι ℂ V) (f : Module.Dual ℂ V →ₗ[ℂ] M) :
    LinearMap.range f = ⨆ j, Submodule.span ℂ {f (b.coord j)} := by
  rw [LinearMap.range_eq_map, ← b.dualBasis.span_eq, Submodule.map_span, ← Set.range_comp]
  rw [show (⇑f ∘ ⇑b.dualBasis) = fun j => f (b.coord j) from funext fun j => by
    simp [Module.Basis.coe_dualBasis]]
  rw [Submodule.span_range_eq_iSup]

end Bridges

/-- The dual action of the gauge torus on the coordinate functionals of
  `DownSinglet`: the weights are negated. -/
lemma DownSinglet.repGaugeGroupI_dual_gaugeTorusGen_coord (i : Fin 4) (j : Fin 2 × Fin 3) :
    DownSinglet.repGaugeGroupI.dual (gaugeTorusGen i) (DownSinglet.basis.coord j)
      = ((expI : ℂ) ^ (-(GaugeWeight.coord (DownSinglet.valueGaugeWeight j) i))) •
        DownSinglet.basis.coord j :=
  dual_gaugeTorusGen_coord _ _ _ _
    (fun j' => DownSinglet.repGaugeGroupI_gaugeTorusGen_basis i j') j

/-- The dual of the conjugate action of the gauge torus on the coordinate functionals
  of the conjugate of `DownSinglet`: the two negations cancel and the weights are those of
  the value space. -/
lemma DownSinglet.repGaugeGroupI_conj_dual_gaugeTorusGen_coord (i : Fin 4) (j : Fin 2 × Fin 3) :
    DownSinglet.repGaugeGroupI.conj.dual (gaugeTorusGen i) ((DownSinglet.basis.conj).coord j)
      = ((expI : ℂ) ^ GaugeWeight.coord (DownSinglet.valueGaugeWeight j) i) •
        (DownSinglet.basis.conj).coord j := by
  have hd := dual_gaugeTorusGen_coord DownSinglet.repGaugeGroupI.conj (DownSinglet.basis.conj)
    (gaugeTorusGen i) (fun j' => -(GaugeWeight.coord (DownSinglet.valueGaugeWeight j') i))
    (fun j' => conj_gaugeTorusGen_basis _ _ _ _
      (fun j'' => DownSinglet.repGaugeGroupI_gaugeTorusGen_basis i j'') j') j
  simpa using hd

/-- The dual action of the gauge torus on the coordinate functionals of
  `UpSinglet`: the weights are negated. -/
lemma UpSinglet.repGaugeGroupI_dual_gaugeTorusGen_coord (i : Fin 4) (j : Fin 2 × Fin 3) :
    UpSinglet.repGaugeGroupI.dual (gaugeTorusGen i) (UpSinglet.basis.coord j)
      = ((expI : ℂ) ^ (-(GaugeWeight.coord (UpSinglet.valueGaugeWeight j) i))) •
        UpSinglet.basis.coord j :=
  dual_gaugeTorusGen_coord _ _ _ _
    (fun j' => UpSinglet.repGaugeGroupI_gaugeTorusGen_basis i j') j

/-- The dual of the conjugate action of the gauge torus on the coordinate functionals
  of the conjugate of `UpSinglet`: the two negations cancel and the weights are those of
  the value space. -/
lemma UpSinglet.repGaugeGroupI_conj_dual_gaugeTorusGen_coord (i : Fin 4) (j : Fin 2 × Fin 3) :
    UpSinglet.repGaugeGroupI.conj.dual (gaugeTorusGen i) ((UpSinglet.basis.conj).coord j)
      = ((expI : ℂ) ^ GaugeWeight.coord (UpSinglet.valueGaugeWeight j) i) •
        (UpSinglet.basis.conj).coord j := by
  have hd := dual_gaugeTorusGen_coord UpSinglet.repGaugeGroupI.conj (UpSinglet.basis.conj)
    (gaugeTorusGen i) (fun j' => -(GaugeWeight.coord (UpSinglet.valueGaugeWeight j') i))
    (fun j' => conj_gaugeTorusGen_basis _ _ _ _
      (fun j'' => UpSinglet.repGaugeGroupI_gaugeTorusGen_basis i j'') j') j
  simpa using hd

/-- The dual action of the gauge torus on the coordinate functionals of
  `QuarkDoublet`: the weights are negated. -/
lemma QuarkDoublet.repGaugeGroupI_dual_gaugeTorusGen_coord (i : Fin 4) (j : Fin 2 × Fin 3 × Fin 2) :
    QuarkDoublet.repGaugeGroupI.dual (gaugeTorusGen i) (QuarkDoublet.basis.coord j)
      = ((expI : ℂ) ^ (-(GaugeWeight.coord (QuarkDoublet.valueGaugeWeight j) i))) •
        QuarkDoublet.basis.coord j :=
  dual_gaugeTorusGen_coord _ _ _ _
    (fun j' => QuarkDoublet.repGaugeGroupI_gaugeTorusGen_basis i j') j

/-- The dual of the conjugate action of the gauge torus on the coordinate functionals
  of the conjugate of `QuarkDoublet`: the two negations cancel and the weights are those of
  the value space. -/
lemma QuarkDoublet.repGaugeGroupI_conj_dual_gaugeTorusGen_coord (i : Fin 4) (j : Fin 2 × Fin 3 × Fin 2) :
    QuarkDoublet.repGaugeGroupI.conj.dual (gaugeTorusGen i) ((QuarkDoublet.basis.conj).coord j)
      = ((expI : ℂ) ^ GaugeWeight.coord (QuarkDoublet.valueGaugeWeight j) i) •
        (QuarkDoublet.basis.conj).coord j := by
  have hd := dual_gaugeTorusGen_coord QuarkDoublet.repGaugeGroupI.conj (QuarkDoublet.basis.conj)
    (gaugeTorusGen i) (fun j' => -(GaugeWeight.coord (QuarkDoublet.valueGaugeWeight j') i))
    (fun j' => conj_gaugeTorusGen_basis _ _ _ _
      (fun j'' => QuarkDoublet.repGaugeGroupI_gaugeTorusGen_basis i j'') j') j
  simpa using hd

/-- The dual action of the gauge torus on the coordinate functionals of
  `LeptonDoublet`: the weights are negated. -/
lemma LeptonDoublet.repGaugeGroupI_dual_gaugeTorusGen_coord (i : Fin 4) (j : Fin 2 × Fin 2) :
    LeptonDoublet.repGaugeGroupI.dual (gaugeTorusGen i) (LeptonDoublet.basis.coord j)
      = ((expI : ℂ) ^ (-(GaugeWeight.coord (LeptonDoublet.valueGaugeWeight j) i))) •
        LeptonDoublet.basis.coord j :=
  dual_gaugeTorusGen_coord _ _ _ _
    (fun j' => LeptonDoublet.repGaugeGroupI_gaugeTorusGen_basis i j') j

/-- The dual of the conjugate action of the gauge torus on the coordinate functionals
  of the conjugate of `LeptonDoublet`: the two negations cancel and the weights are those of
  the value space. -/
lemma LeptonDoublet.repGaugeGroupI_conj_dual_gaugeTorusGen_coord (i : Fin 4) (j : Fin 2 × Fin 2) :
    LeptonDoublet.repGaugeGroupI.conj.dual (gaugeTorusGen i) ((LeptonDoublet.basis.conj).coord j)
      = ((expI : ℂ) ^ GaugeWeight.coord (LeptonDoublet.valueGaugeWeight j) i) •
        (LeptonDoublet.basis.conj).coord j := by
  have hd := dual_gaugeTorusGen_coord LeptonDoublet.repGaugeGroupI.conj (LeptonDoublet.basis.conj)
    (gaugeTorusGen i) (fun j' => -(GaugeWeight.coord (LeptonDoublet.valueGaugeWeight j') i))
    (fun j' => conj_gaugeTorusGen_basis _ _ _ _
      (fun j'' => LeptonDoublet.repGaugeGroupI_gaugeTorusGen_basis i j'') j') j
  simpa using hd

/-- The dual action of the gauge torus on the coordinate functionals of
  `LeptonSinglet`: the weights are negated. -/
lemma LeptonSinglet.repGaugeGroupI_dual_gaugeTorusGen_coord (i : Fin 4) (j : Fin 2) :
    LeptonSinglet.repGaugeGroupI.dual (gaugeTorusGen i) (LeptonSinglet.basis.coord j)
      = ((expI : ℂ) ^ (-(GaugeWeight.coord (LeptonSinglet.valueGaugeWeight j) i))) •
        LeptonSinglet.basis.coord j :=
  dual_gaugeTorusGen_coord _ _ _ _
    (fun j' => LeptonSinglet.repGaugeGroupI_gaugeTorusGen_basis i j') j

/-- The dual of the conjugate action of the gauge torus on the coordinate functionals
  of the conjugate of `LeptonSinglet`: the two negations cancel and the weights are those of
  the value space. -/
lemma LeptonSinglet.repGaugeGroupI_conj_dual_gaugeTorusGen_coord (i : Fin 4) (j : Fin 2) :
    LeptonSinglet.repGaugeGroupI.conj.dual (gaugeTorusGen i) ((LeptonSinglet.basis.conj).coord j)
      = ((expI : ℂ) ^ GaugeWeight.coord (LeptonSinglet.valueGaugeWeight j) i) •
        (LeptonSinglet.basis.conj).coord j := by
  have hd := dual_gaugeTorusGen_coord LeptonSinglet.repGaugeGroupI.conj (LeptonSinglet.basis.conj)
    (gaugeTorusGen i) (fun j' => -(GaugeWeight.coord (LeptonSinglet.valueGaugeWeight j') i))
    (fun j' => conj_gaugeTorusGen_basis _ _ _ _
      (fun j'' => LeptonSinglet.repGaugeGroupI_gaugeTorusGen_basis i j'') j') j
  simpa using hd

/-!

## E. The gauge weight decomposition of the derivative submodules

-/

namespace IsFermionSector

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {hrepGauge_mul : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
    repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {hrepLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂}
  {d : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ DownSinglet →ₗ[ℂ] B}
  {bard : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule DownSinglet) →ₗ[ℂ] B}
  {u : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ UpSinglet →ₗ[ℂ] B}
  {baru : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule UpSinglet) →ₗ[ℂ] B}
  {Q : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ QuarkDoublet →ₗ[ℂ] B}
  {barQ : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule QuarkDoublet) →ₗ[ℂ] B}
  {L : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonDoublet →ₗ[ℂ] B}
  {barL : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule LeptonDoublet) →ₗ[ℂ] B}
  {e : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonSinglet →ₗ[ℂ] B}
  {bare : {n : ℕ} → Fin 3 → (Fin n → Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule LeptonSinglet) →ₗ[ℂ] B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : IsFermionSector B repGauge hrepGauge_mul repLorentz hrepLorentz_mul
      d bard u baru Q barQ L barL e bare massWeightPoly)

include h in
/-- The gauge torus acts diagonally on the `d` symbol components. -/
lemma repGauge_gaugeTorusGen_d (i : Fin 4) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge (gaugeTorusGen i) (d f l ((DownSinglet.basis).coord j))
      = ((expI : ℂ) ^ GaugeWeight.coord (-(DownSinglet.valueGaugeWeight j)) i) • d f l ((DownSinglet.basis).coord j) := by
  rw [h.repGauge_d, DownSinglet.repGaugeGroupI_dual_gaugeTorusGen_coord, map_smul, GaugeWeight.coord_neg]

include h in
/-- The gauge torus acts diagonally on the `bard` symbol components. -/
lemma repGauge_gaugeTorusGen_bard (i : Fin 4) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge (gaugeTorusGen i) (bard f l ((DownSinglet.basis.conj).coord j))
      = ((expI : ℂ) ^ GaugeWeight.coord (DownSinglet.valueGaugeWeight j) i) • bard f l ((DownSinglet.basis.conj).coord j) := by
  rw [h.repGauge_bard, DownSinglet.repGaugeGroupI_conj_dual_gaugeTorusGen_coord, map_smul]

include h in
/-- The gauge torus acts diagonally on the `u` symbol components. -/
lemma repGauge_gaugeTorusGen_u (i : Fin 4) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge (gaugeTorusGen i) (u f l ((UpSinglet.basis).coord j))
      = ((expI : ℂ) ^ GaugeWeight.coord (-(UpSinglet.valueGaugeWeight j)) i) • u f l ((UpSinglet.basis).coord j) := by
  rw [h.repGauge_u, UpSinglet.repGaugeGroupI_dual_gaugeTorusGen_coord, map_smul, GaugeWeight.coord_neg]

include h in
/-- The gauge torus acts diagonally on the `baru` symbol components. -/
lemma repGauge_gaugeTorusGen_baru (i : Fin 4) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3) :
    repGauge (gaugeTorusGen i) (baru f l ((UpSinglet.basis.conj).coord j))
      = ((expI : ℂ) ^ GaugeWeight.coord (UpSinglet.valueGaugeWeight j) i) • baru f l ((UpSinglet.basis.conj).coord j) := by
  rw [h.repGauge_baru, UpSinglet.repGaugeGroupI_conj_dual_gaugeTorusGen_coord, map_smul]

include h in
/-- The gauge torus acts diagonally on the `Q` symbol components. -/
lemma repGauge_gaugeTorusGen_Q (i : Fin 4) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3 × Fin 2) :
    repGauge (gaugeTorusGen i) (Q f l ((QuarkDoublet.basis).coord j))
      = ((expI : ℂ) ^ GaugeWeight.coord (-(QuarkDoublet.valueGaugeWeight j)) i) • Q f l ((QuarkDoublet.basis).coord j) := by
  rw [h.repGauge_Q, QuarkDoublet.repGaugeGroupI_dual_gaugeTorusGen_coord, map_smul, GaugeWeight.coord_neg]

include h in
/-- The gauge torus acts diagonally on the `barQ` symbol components. -/
lemma repGauge_gaugeTorusGen_barQ (i : Fin 4) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 3 × Fin 2) :
    repGauge (gaugeTorusGen i) (barQ f l ((QuarkDoublet.basis.conj).coord j))
      = ((expI : ℂ) ^ GaugeWeight.coord (QuarkDoublet.valueGaugeWeight j) i) • barQ f l ((QuarkDoublet.basis.conj).coord j) := by
  rw [h.repGauge_barQ, QuarkDoublet.repGaugeGroupI_conj_dual_gaugeTorusGen_coord, map_smul]

include h in
/-- The gauge torus acts diagonally on the `L` symbol components. -/
lemma repGauge_gaugeTorusGen_L (i : Fin 4) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 2) :
    repGauge (gaugeTorusGen i) (L f l ((LeptonDoublet.basis).coord j))
      = ((expI : ℂ) ^ GaugeWeight.coord (-(LeptonDoublet.valueGaugeWeight j)) i) • L f l ((LeptonDoublet.basis).coord j) := by
  rw [h.repGauge_L, LeptonDoublet.repGaugeGroupI_dual_gaugeTorusGen_coord, map_smul, GaugeWeight.coord_neg]

include h in
/-- The gauge torus acts diagonally on the `barL` symbol components. -/
lemma repGauge_gaugeTorusGen_barL (i : Fin 4) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2 × Fin 2) :
    repGauge (gaugeTorusGen i) (barL f l ((LeptonDoublet.basis.conj).coord j))
      = ((expI : ℂ) ^ GaugeWeight.coord (LeptonDoublet.valueGaugeWeight j) i) • barL f l ((LeptonDoublet.basis.conj).coord j) := by
  rw [h.repGauge_barL, LeptonDoublet.repGaugeGroupI_conj_dual_gaugeTorusGen_coord, map_smul]

include h in
/-- The gauge torus acts diagonally on the `e` symbol components. -/
lemma repGauge_gaugeTorusGen_e (i : Fin 4) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2) :
    repGauge (gaugeTorusGen i) (e f l ((LeptonSinglet.basis).coord j))
      = ((expI : ℂ) ^ GaugeWeight.coord (-(LeptonSinglet.valueGaugeWeight j)) i) • e f l ((LeptonSinglet.basis).coord j) := by
  rw [h.repGauge_e, LeptonSinglet.repGaugeGroupI_dual_gaugeTorusGen_coord, map_smul, GaugeWeight.coord_neg]

include h in
/-- The gauge torus acts diagonally on the `bare` symbol components. -/
lemma repGauge_gaugeTorusGen_bare (i : Fin 4) (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (j : Fin 2) :
    repGauge (gaugeTorusGen i) (bare f l ((LeptonSinglet.basis.conj).coord j))
      = ((expI : ℂ) ^ GaugeWeight.coord (LeptonSinglet.valueGaugeWeight j) i) • bare f l ((LeptonSinglet.basis.conj).coord j) := by
  rw [h.repGauge_bare, LeptonSinglet.repGaugeGroupI_conj_dual_gaugeTorusGen_coord, map_smul]

/-- The gauge weight decomposition of the range of the `d` symbols. -/
@[implicit_reducible]
noncomputable def rangeGaugeWeight_d (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) :
    GaugeWeightDecomposition repGauge (LinearMap.range (d f l)) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup hrepGauge_mul fun j : Fin 2 × Fin 3 =>
      GaugeWeightDecomposition.spanSingleton hrepGauge_mul _ (-(DownSinglet.valueGaugeWeight j))
        (fun i => h.repGauge_gaugeTorusGen_d i f l j))
    _ (range_eq_iSup_span (DownSinglet.basis) (d f l))

/-- The gauge weight decomposition of the range of the `bard` symbols. -/
@[implicit_reducible]
noncomputable def rangeGaugeWeight_bard (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) :
    GaugeWeightDecomposition repGauge (LinearMap.range (bard f l)) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup hrepGauge_mul fun j : Fin 2 × Fin 3 =>
      GaugeWeightDecomposition.spanSingleton hrepGauge_mul _ (DownSinglet.valueGaugeWeight j)
        (fun i => h.repGauge_gaugeTorusGen_bard i f l j))
    _ (range_eq_iSup_span (DownSinglet.basis.conj) (bard f l))

/-- The gauge weight decomposition of the range of the `u` symbols. -/
@[implicit_reducible]
noncomputable def rangeGaugeWeight_u (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) :
    GaugeWeightDecomposition repGauge (LinearMap.range (u f l)) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup hrepGauge_mul fun j : Fin 2 × Fin 3 =>
      GaugeWeightDecomposition.spanSingleton hrepGauge_mul _ (-(UpSinglet.valueGaugeWeight j))
        (fun i => h.repGauge_gaugeTorusGen_u i f l j))
    _ (range_eq_iSup_span (UpSinglet.basis) (u f l))

/-- The gauge weight decomposition of the range of the `baru` symbols. -/
@[implicit_reducible]
noncomputable def rangeGaugeWeight_baru (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) :
    GaugeWeightDecomposition repGauge (LinearMap.range (baru f l)) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup hrepGauge_mul fun j : Fin 2 × Fin 3 =>
      GaugeWeightDecomposition.spanSingleton hrepGauge_mul _ (UpSinglet.valueGaugeWeight j)
        (fun i => h.repGauge_gaugeTorusGen_baru i f l j))
    _ (range_eq_iSup_span (UpSinglet.basis.conj) (baru f l))

/-- The gauge weight decomposition of the range of the `Q` symbols. -/
@[implicit_reducible]
noncomputable def rangeGaugeWeight_Q (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) :
    GaugeWeightDecomposition repGauge (LinearMap.range (Q f l)) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup hrepGauge_mul fun j : Fin 2 × Fin 3 × Fin 2 =>
      GaugeWeightDecomposition.spanSingleton hrepGauge_mul _ (-(QuarkDoublet.valueGaugeWeight j))
        (fun i => h.repGauge_gaugeTorusGen_Q i f l j))
    _ (range_eq_iSup_span (QuarkDoublet.basis) (Q f l))

/-- The gauge weight decomposition of the range of the `barQ` symbols. -/
@[implicit_reducible]
noncomputable def rangeGaugeWeight_barQ (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) :
    GaugeWeightDecomposition repGauge (LinearMap.range (barQ f l)) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup hrepGauge_mul fun j : Fin 2 × Fin 3 × Fin 2 =>
      GaugeWeightDecomposition.spanSingleton hrepGauge_mul _ (QuarkDoublet.valueGaugeWeight j)
        (fun i => h.repGauge_gaugeTorusGen_barQ i f l j))
    _ (range_eq_iSup_span (QuarkDoublet.basis.conj) (barQ f l))

/-- The gauge weight decomposition of the range of the `L` symbols. -/
@[implicit_reducible]
noncomputable def rangeGaugeWeight_L (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) :
    GaugeWeightDecomposition repGauge (LinearMap.range (L f l)) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup hrepGauge_mul fun j : Fin 2 × Fin 2 =>
      GaugeWeightDecomposition.spanSingleton hrepGauge_mul _ (-(LeptonDoublet.valueGaugeWeight j))
        (fun i => h.repGauge_gaugeTorusGen_L i f l j))
    _ (range_eq_iSup_span (LeptonDoublet.basis) (L f l))

/-- The gauge weight decomposition of the range of the `barL` symbols. -/
@[implicit_reducible]
noncomputable def rangeGaugeWeight_barL (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) :
    GaugeWeightDecomposition repGauge (LinearMap.range (barL f l)) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup hrepGauge_mul fun j : Fin 2 × Fin 2 =>
      GaugeWeightDecomposition.spanSingleton hrepGauge_mul _ (LeptonDoublet.valueGaugeWeight j)
        (fun i => h.repGauge_gaugeTorusGen_barL i f l j))
    _ (range_eq_iSup_span (LeptonDoublet.basis.conj) (barL f l))

/-- The gauge weight decomposition of the range of the `e` symbols. -/
@[implicit_reducible]
noncomputable def rangeGaugeWeight_e (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) :
    GaugeWeightDecomposition repGauge (LinearMap.range (e f l)) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup hrepGauge_mul fun j : Fin 2 =>
      GaugeWeightDecomposition.spanSingleton hrepGauge_mul _ (-(LeptonSinglet.valueGaugeWeight j))
        (fun i => h.repGauge_gaugeTorusGen_e i f l j))
    _ (range_eq_iSup_span (LeptonSinglet.basis) (e f l))

/-- The gauge weight decomposition of the range of the `bare` symbols. -/
@[implicit_reducible]
noncomputable def rangeGaugeWeight_bare (f : Fin 3) {n : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) :
    GaugeWeightDecomposition repGauge (LinearMap.range (bare f l)) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup hrepGauge_mul fun j : Fin 2 =>
      GaugeWeightDecomposition.spanSingleton hrepGauge_mul _ (LeptonSinglet.valueGaugeWeight j)
        (fun i => h.repGauge_gaugeTorusGen_bare i f l j))
    _ (range_eq_iSup_span (LeptonSinglet.basis.conj) (bare f l))

/-- **The gauge weight decomposition of the fermion derivative submodules**, for any
  number of covariant derivatives: the join, over families, derivative slots and the
  ten species, of the spans of the symbol components, each of pure gauge weight. -/
@[implicit_reducible]
noncomputable def derivSubmoduleGaugeWeight (n : ℕ) :
    GaugeWeightDecomposition repGauge (h.derivSubmodule n) :=
  GaugeWeightDecomposition.copy
    (GaugeWeightDecomposition.iSup hrepGauge_mul fun f : Fin 3 =>
      GaugeWeightDecomposition.iSup hrepGauge_mul fun l : Fin n → Fin 1 ⊕ Fin 3 =>
      GaugeWeightDecomposition.sup
        (d := GaugeWeightDecomposition.sup
        (d := GaugeWeightDecomposition.sup
        (d := GaugeWeightDecomposition.sup
        (d := GaugeWeightDecomposition.sup
        (d := GaugeWeightDecomposition.sup
        (d := GaugeWeightDecomposition.sup
        (d := GaugeWeightDecomposition.sup
        (d := GaugeWeightDecomposition.sup
        (d := h.rangeGaugeWeight_d f l)
        (d' := h.rangeGaugeWeight_bard f l))
        (d' := h.rangeGaugeWeight_u f l))
        (d' := h.rangeGaugeWeight_baru f l))
        (d' := h.rangeGaugeWeight_Q f l))
        (d' := h.rangeGaugeWeight_barQ f l))
        (d' := h.rangeGaugeWeight_L f l))
        (d' := h.rangeGaugeWeight_barL f l))
        (d' := h.rangeGaugeWeight_e f l))
        (d' := h.rangeGaugeWeight_bare f l))
    _ (by rw [derivSubmodule])

end IsFermionSector

end StandardModel
