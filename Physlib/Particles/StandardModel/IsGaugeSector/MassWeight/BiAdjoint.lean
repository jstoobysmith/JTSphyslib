/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.IsGaugeSector.MassWeight.GaugeWeightDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.IsSU3BiAdjoint
public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.IsSU2BiAdjoint
public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.IsU1BiAdjoint
public import Mathlib.RepresentationTheory.Invariants
/-!
# Products of two field strengths as bi-adjoint gauge tensors

A single field-strength symbol of the gauge sector carries one adjoint index of the gauge
algebra, so a product of two of them carries two. Restricting the value index to one
factor of the gauge group turns such a product into a family indexed by two adjoint
indices of that factor, and the gauge transformation law of the sector says exactly that
these families are bi-adjoint in the sense of `IsSU3BiAdjoint`, `IsSU2BiAdjoint` and
`IsU1BiAdjoint`.

The gauge invariant those propositions supply is the trace contraction, the Kronecker
contraction of the two adjoint indices; for the underived field strength it is the
familiar kinetic pairing of two field strengths. Its mass weight is the sum of the mass
weights of the two factors, so it lies in the corresponding mass-weight submodule, and it
is gauge invariant, so it lies in the zero-weight piece of the gauge weight decomposition
of that submodule.

- A. The gauge transformation of the gauge-factor field strengths
- B. Products of two field strengths as bi-adjoint families
- C. The trace contractions and their mass weights
- D. The underived trace contractions at mass weight eight

-/

@[expose] public section

namespace StandardModel

open Matrix MatrixGroups Lorentz

namespace IsGaugeSector

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}
  {hrepGauge_mul : ∀ (g : GaugeGroupI) (b₁ b₂ : B),
    repGauge g (b₁ * b₂) = repGauge g b₁ * repGauge g b₂}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {hrepLorentz_mul : ∀ (Λ : SL(2,ℂ)) (b₁ b₂ : B),
    repLorentz Λ (b₁ * b₂) = repLorentz Λ b₁ * repLorentz Λ b₂}
  {F : {n : ℕ} → (Fin n → Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) →
    Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  (h : IsGaugeSector B repGauge hrepGauge_mul repLorentz hrepLorentz_mul
      F massWeightPoly)

/-!

## A. The gauge transformation of the gauge-factor field strengths

-/

include h in
/-- The field-strength symbol evaluated on a standard-basis coordinate transforms under
  the gauge group through the column of `adjointMatrix` indexed by that coordinate. -/
lemma repGauge_F_coord (g : GaugeGroupI) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (c : Fin 8 ⊕ Fin 3 ⊕ Fin 1) :
    repGauge g (F l μ ν (GaugeAlgebra.stdBasis.coord c))
      = ∑ b, ((GaugeAlgebra.adjointMatrix g b c : ℝ) : ℂ) •
          F l μ ν (GaugeAlgebra.stdBasis.coord b) := by
  rw [h.repGauge_F g l μ ν,
    show GaugeAlgebra.adjointMap g⁻¹
      = (GaugeAlgebra.adjoint g⁻¹ : GaugeAlgebra →ₗ[ℝ] GaugeAlgebra) from rfl,
    GaugeAlgebra.adjoint_dualMap_coord, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, GaugeAlgebra.adjointMatrix_inv_apply, Complex.coe_smul]

/-- The gluon field strength transforms in the adjoint representation of the `su(3)`
  factor of the gauge group. -/
lemma repGauge_gluonField (g : GaugeGroupI) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (c : Fin 8) :
    repGauge g (h.gluonField l μ ν c)
      = ∑ a : Fin 8, ((GaugeAlgebra.adjointMatrix g (Sum.inl a) (Sum.inl c) : ℝ) : ℂ) •
          h.gluonField l μ ν a := by
  rw [gluonField, h.repGauge_F_coord g l μ ν (Sum.inl c), Fintype.sum_sum_type,
    Fintype.sum_sum_type]
  simp [gluonField]

/-- The `W`-boson field strength transforms in the adjoint representation of the `su(2)`
  factor of the gauge group. -/
lemma repGauge_wField (g : GaugeGroupI) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (c : Fin 3) :
    repGauge g (h.wField l μ ν c)
      = ∑ i : Fin 3, ((GaugeAlgebra.adjointMatrix g (Sum.inr (Sum.inl i))
          (Sum.inr (Sum.inl c)) : ℝ) : ℂ) • h.wField l μ ν i := by
  rw [wField, h.repGauge_F_coord g l μ ν (Sum.inr (Sum.inl c)), Fintype.sum_sum_type,
    Fintype.sum_sum_type]
  simp [wField]

/-- The hypercharge field strength is gauge invariant: the adjoint action of the gauge
  group on the `u(1)` factor of the gauge algebra is trivial. -/
lemma repGauge_hyperchargeField (g : GaugeGroupI) {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) :
    repGauge g (h.hyperchargeField l μ ν) = h.hyperchargeField l μ ν := by
  rw [hyperchargeField, h.repGauge_F_coord g l μ ν (Sum.inr (Sum.inr 0)),
    Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp

/-!

## B. Products of two field strengths as bi-adjoint families

-/

/-- A product of two gluon field strengths, viewed as a family indexed by the two `su(3)`
  adjoint indices it carries, is a bi-adjoint `su(3)` tensor. -/
lemma isSU3BiAdjoint_gluonField_mul {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3) :
    IsSU3BiAdjoint B repGauge
      (fun a : Fin 2 → Fin 8 => h.gluonField l μ ν (a 0) * h.gluonField l' μ' ν' (a 1)) := by
  refine ⟨fun g d => ?_⟩
  rw [hrepGauge_mul, h.repGauge_gluonField, h.repGauge_gluonField,
    Fintype.sum_mul_sum, IsSU3BiAdjoint.sum_pi_two]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [smul_mul_smul_comm]
  simp [Fin.prod_univ_two]

/-- A product of two `W`-boson field strengths, viewed as a family indexed by the two
  `su(2)` adjoint indices it carries, is a bi-adjoint `su(2)` tensor. -/
lemma isSU2BiAdjoint_wField_mul {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3) :
    IsSU2BiAdjoint B repGauge
      (fun a : Fin 2 → Fin 3 => h.wField l μ ν (a 0) * h.wField l' μ' ν' (a 1)) := by
  refine ⟨fun g d => ?_⟩
  rw [hrepGauge_mul, h.repGauge_wField, h.repGauge_wField,
    Fintype.sum_mul_sum, IsSU2BiAdjoint.sum_pi_two]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [smul_mul_smul_comm]
  simp [Fin.prod_univ_two]

/-- A product of two hypercharge field strengths, viewed as a family indexed by the two
  `u(1)` adjoint indices it carries, is a bi-adjoint `u(1)` tensor. -/
lemma isU1BiAdjoint_hyperchargeField_mul {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3) :
    IsU1BiAdjoint B repGauge
      (fun _ : Fin 2 → Fin 1 => h.hyperchargeField l μ ν * h.hyperchargeField l' μ' ν') := by
  refine ⟨fun g d => ?_⟩
  rw [hrepGauge_mul, h.repGauge_hyperchargeField, h.repGauge_hyperchargeField]
  simp

/-!

## C. The trace contractions and their mass weights

-/

/-- The trace contraction of a product of two gluon field strengths is the Kronecker
  contraction of the two `su(3)` adjoint indices. -/
lemma traceContraction_gluonField_mul {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isSU3BiAdjoint_gluonField_mul l μ ν l' μ' ν').traceContraction
      = ∑ a : Fin 8, h.gluonField l μ ν a * h.gluonField l' μ' ν' a := by
  simp [IsSU3BiAdjoint.traceContraction]

/-- The trace contraction of a product of two `W`-boson field strengths is the Kronecker
  contraction of the two `su(2)` adjoint indices. -/
lemma traceContraction_wField_mul {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isSU2BiAdjoint_wField_mul l μ ν l' μ' ν').traceContraction
      = ∑ i : Fin 3, h.wField l μ ν i * h.wField l' μ' ν' i := by
  simp [IsSU2BiAdjoint.traceContraction]

/-- The trace contraction of a product of two hypercharge field strengths is that
  product itself, the `u(1)` factor being one dimensional. -/
lemma traceContraction_hyperchargeField_mul {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isU1BiAdjoint_hyperchargeField_mul l μ ν l' μ' ν').traceContraction
      = h.hyperchargeField l μ ν * h.hyperchargeField l' μ' ν' := by
  simp [IsU1BiAdjoint.traceContraction]

/-- Every field-strength symbol lies in the derivative submodule of its own number of
  covariant derivatives. -/
lemma F_mem_derivSubmodule {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ GaugeAlgebra) : F l μ ν φ ∈ h.derivSubmodule n := by
  rw [derivSubmodule]
  exact Submodule.mem_iSup_of_mem l (Submodule.mem_iSup_of_mem μ
    (Submodule.mem_iSup_of_mem ν (Submodule.subset_span ⟨φ, rfl⟩)))

/-- A product of two field-strength symbols with `n` and `m` covariant derivatives has
  mass weight the sum of the two individual mass weights. -/
lemma F_mul_F_mem_massWeightSubmodule {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (μ' ν' : Fin 1 ⊕ Fin 3) (φ' : Module.Dual ℝ GaugeAlgebra) :
    F l μ ν φ * F l' μ' ν' φ'
      ∈ h.massWeightSubmodule (2 * (2 + n) + 2 * (2 + m)) :=
  h.massWeightSubmodule_mul_le _ _ (Submodule.mul_mem_mul
    (h.derivSubmodule_le_massWeightSubmodule n (h.F_mem_derivSubmodule l μ ν φ))
    (h.derivSubmodule_le_massWeightSubmodule m (h.F_mem_derivSubmodule l' μ' ν' φ')))

/-- The gluon trace contraction is a gauge invariant of the expected mass weight: it lies
  in the mass-weight submodule of weight the sum of the two individual mass weights, and
  it is fixed by the whole gauge group. -/
lemma traceContraction_gluonField_mul_mem {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isSU3BiAdjoint_gluonField_mul l μ ν l' μ' ν').traceContraction
      ∈ h.massWeightSubmodule (2 * (2 + n) + 2 * (2 + m)) ⊓ repGauge.invariants := by
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [h.traceContraction_gluonField_mul]
    exact Submodule.sum_mem _ fun a _ => h.F_mul_F_mem_massWeightSubmodule l μ ν _ l' μ' ν' _
  · exact (Representation.mem_invariants _ _).mpr fun g =>
      IsSU3BiAdjoint.repGauge_traceContraction _ g

/-- The `W`-boson trace contraction is a gauge invariant of the expected mass weight. -/
lemma traceContraction_wField_mul_mem {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isSU2BiAdjoint_wField_mul l μ ν l' μ' ν').traceContraction
      ∈ h.massWeightSubmodule (2 * (2 + n) + 2 * (2 + m)) ⊓ repGauge.invariants := by
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [h.traceContraction_wField_mul]
    exact Submodule.sum_mem _ fun i _ => h.F_mul_F_mem_massWeightSubmodule l μ ν _ l' μ' ν' _
  · exact (Representation.mem_invariants _ _).mpr fun g =>
      IsSU2BiAdjoint.repGauge_traceContraction _ g

/-- The hypercharge trace contraction is a gauge invariant of the expected mass weight. -/
lemma traceContraction_hyperchargeField_mul_mem {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isU1BiAdjoint_hyperchargeField_mul l μ ν l' μ' ν').traceContraction
      ∈ h.massWeightSubmodule (2 * (2 + n) + 2 * (2 + m)) ⊓ repGauge.invariants := by
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [h.traceContraction_hyperchargeField_mul]
    exact h.F_mul_F_mem_massWeightSubmodule l μ ν _ l' μ' ν' _
  · exact (Representation.mem_invariants _ _).mpr fun g =>
      IsU1BiAdjoint.repGauge_traceContraction _ g

/-!

## D. The underived trace contractions at mass weight eight

The product of two underived field strengths has mass weight eight, the `F · F` half of
`massWeightSubmodule_eight_eq`.  Each of the three trace contractions there is a gauge
invariant, so by `GaugeWeightDecomposition.mem_zero_of_invariant` each lies in the
zero-weight piece of the gauge weight decomposition of mass weight eight, computed by
`massWeightSubmoduleGaugeWeightEight_piece_zero`.

-/

/-- The trace contraction of two underived gluon field strengths lies in the mass-weight
  eight submodule and is gauge invariant. -/
lemma traceContraction_gluonField_mul_mem_eight (μ ν μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isSU3BiAdjoint_gluonField_mul ![] μ ν ![] μ' ν').traceContraction
      ∈ h.massWeightSubmodule 8 ⊓ repGauge.invariants := by
  have hmem := h.traceContraction_gluonField_mul_mem (![] : Fin 0 → Fin 1 ⊕ Fin 3) μ ν
    (![] : Fin 0 → Fin 1 ⊕ Fin 3) μ' ν'
  rwa [show 2 * (2 + 0) + 2 * (2 + 0) = 8 from by norm_num] at hmem

/-- The trace contraction of two underived `W`-boson field strengths lies in the
  mass-weight eight submodule and is gauge invariant. -/
lemma traceContraction_wField_mul_mem_eight (μ ν μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isSU2BiAdjoint_wField_mul ![] μ ν ![] μ' ν').traceContraction
      ∈ h.massWeightSubmodule 8 ⊓ repGauge.invariants := by
  have hmem := h.traceContraction_wField_mul_mem (![] : Fin 0 → Fin 1 ⊕ Fin 3) μ ν
    (![] : Fin 0 → Fin 1 ⊕ Fin 3) μ' ν'
  rwa [show 2 * (2 + 0) + 2 * (2 + 0) = 8 from by norm_num] at hmem

/-- The trace contraction of two underived hypercharge field strengths lies in the
  mass-weight eight submodule and is gauge invariant. -/
lemma traceContraction_hyperchargeField_mul_mem_eight (μ ν μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isU1BiAdjoint_hyperchargeField_mul ![] μ ν ![] μ' ν').traceContraction
      ∈ h.massWeightSubmodule 8 ⊓ repGauge.invariants := by
  have hmem := h.traceContraction_hyperchargeField_mul_mem (![] : Fin 0 → Fin 1 ⊕ Fin 3) μ ν
    (![] : Fin 0 → Fin 1 ⊕ Fin 3) μ' ν'
  rwa [show 2 * (2 + 0) + 2 * (2 + 0) = 8 from by norm_num] at hmem

/-- The trace contraction of two underived gluon field strengths lies in the zero-weight
  piece of the gauge weight decomposition of mass weight eight. -/
lemma traceContraction_gluonField_mul_mem_piece_zero (μ ν μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isSU3BiAdjoint_gluonField_mul ![] μ ν ![] μ' ν').traceContraction
      ∈ (h.massWeightSubmoduleGaugeWeightEight).piece 0 :=
  GaugeWeightDecomposition.mem_zero_of_invariant _
    (Submodule.mem_inf.mp (h.traceContraction_gluonField_mul_mem_eight μ ν μ' ν')).1
    fun g => IsSU3BiAdjoint.repGauge_traceContraction _ g

/-- The trace contraction of two underived `W`-boson field strengths lies in the
  zero-weight piece of the gauge weight decomposition of mass weight eight. -/
lemma traceContraction_wField_mul_mem_piece_zero (μ ν μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isSU2BiAdjoint_wField_mul ![] μ ν ![] μ' ν').traceContraction
      ∈ (h.massWeightSubmoduleGaugeWeightEight).piece 0 :=
  GaugeWeightDecomposition.mem_zero_of_invariant _
    (Submodule.mem_inf.mp (h.traceContraction_wField_mul_mem_eight μ ν μ' ν')).1
    fun g => IsSU2BiAdjoint.repGauge_traceContraction _ g

/-- The trace contraction of two underived hypercharge field strengths lies in the
  zero-weight piece of the gauge weight decomposition of mass weight eight. -/
lemma traceContraction_hyperchargeField_mul_mem_piece_zero (μ ν μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isU1BiAdjoint_hyperchargeField_mul ![] μ ν ![] μ' ν').traceContraction
      ∈ (h.massWeightSubmoduleGaugeWeightEight).piece 0 :=
  GaugeWeightDecomposition.mem_zero_of_invariant _
    (Submodule.mem_inf.mp (h.traceContraction_hyperchargeField_mul_mem_eight μ ν μ' ν')).1
    fun g => IsU1BiAdjoint.repGauge_traceContraction _ g

end IsGaugeSector

end StandardModel
