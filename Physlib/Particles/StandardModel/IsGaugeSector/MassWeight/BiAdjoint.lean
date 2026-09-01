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

The bi-adjoint subspaces themselves, the spans of the components of these families, are
related to the mass-weight submodules in both directions. Each such span lies inside the
mass-weight submodule of the sum of the two mass weights, and conversely the colour and
isospin generators of the zero-weight piece of mass weight eight lie inside the spans of
the underived gluon and `W`-boson families.

- A. The gauge transformation of the gauge-factor field strengths
- B. Products of two field strengths as bi-adjoint families
- C. The bi-adjoint spans inside the mass-weight submodules
- D. The trace contractions and their mass weights
- E. The underived trace contractions at mass weight eight
- F. The weight vectors of mass weight eight inside the bi-adjoint spans

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

/-- A gauge transformation moves a product of two gluon field strengths as the `SU(3)`
  factor of that gauge group element moves a tensor with two `su(3)` adjoint indices. -/
lemma isSU3BiAdjointMat_gluonField_mul {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3)
    (g : GaugeGroupI) :
    IsSU3BiAdjointMat (GaugeGroupI.toSU3 g) (repGauge g)
      (fun a : Fin 2 → Fin 8 => h.gluonField l μ ν (a 0) * h.gluonField l' μ' ν' (a 1)) := by
  intro d
  rw [hrepGauge_mul, h.repGauge_gluonField, h.repGauge_gluonField,
    Fintype.sum_mul_sum, IsSU3BiAdjoint.sum_pi_two]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [smul_mul_smul_comm]
  simp [Fin.prod_univ_two]

/-- A product of two gluon field strengths, viewed as a family indexed by the two `su(3)`
  adjoint indices it carries, is a bi-adjoint `su(3)` tensor. -/
lemma isSU3BiAdjoint_gluonField_mul {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3) :
    IsSU3BiAdjoint B repGauge
      (fun a : Fin 2 → Fin 8 => h.gluonField l μ ν (a 0) * h.gluonField l' μ' ν' (a 1)) :=
  ⟨fun U => h.isSU3BiAdjointMat_gluonField_mul l μ ν l' μ' ν' (U, 1, 1)⟩

/-- A gauge transformation moves a product of two `W`-boson field strengths as the `SU(2)`
  factor of that gauge group element moves a tensor with two `su(2)` adjoint indices. -/
lemma isSU2BiAdjointMat_wField_mul {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3)
    (g : GaugeGroupI) :
    IsSU2BiAdjointMat (GaugeGroupI.toSU2 g) (repGauge g)
      (fun a : Fin 2 → Fin 3 => h.wField l μ ν (a 0) * h.wField l' μ' ν' (a 1)) := by
  intro d
  rw [hrepGauge_mul, h.repGauge_wField, h.repGauge_wField,
    Fintype.sum_mul_sum, IsSU2BiAdjoint.sum_pi_two]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [smul_mul_smul_comm]
  simp [Fin.prod_univ_two]

/-- A product of two `W`-boson field strengths, viewed as a family indexed by the two
  `su(2)` adjoint indices it carries, is a bi-adjoint `su(2)` tensor. -/
lemma isSU2BiAdjoint_wField_mul {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3) :
    IsSU2BiAdjoint B repGauge
      (fun a : Fin 2 → Fin 3 => h.wField l μ ν (a 0) * h.wField l' μ' ν' (a 1)) :=
  ⟨fun U => h.isSU2BiAdjointMat_wField_mul l μ ν l' μ' ν' (1, U, 1)⟩

/-- A gauge transformation moves a product of two hypercharge field strengths as the
  `U(1)` factor of that gauge group element moves a tensor with two `u(1)` adjoint
  indices. -/
lemma isU1BiAdjointMat_hyperchargeField_mul {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3)
    (g : GaugeGroupI) :
    IsU1BiAdjointMat (GaugeGroupI.toU1 g) (repGauge g)
      (fun _ : Fin 2 → Fin 1 => h.hyperchargeField l μ ν * h.hyperchargeField l' μ' ν') :=
  (isU1BiAdjointMat_iff _ _ _).2 fun _ => by
    rw [hrepGauge_mul, h.repGauge_hyperchargeField, h.repGauge_hyperchargeField]

/-- A product of two hypercharge field strengths, viewed as a family indexed by the two
  `u(1)` adjoint indices it carries, is a bi-adjoint `u(1)` tensor. -/
lemma isU1BiAdjoint_hyperchargeField_mul {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3) :
    IsU1BiAdjoint B repGauge
      (fun _ : Fin 2 → Fin 1 => h.hyperchargeField l μ ν * h.hyperchargeField l' μ' ν') :=
  ⟨fun u => h.isU1BiAdjointMat_hyperchargeField_mul l μ ν l' μ' ν' (1, 1, u)⟩

/-!

## C. The bi-adjoint spans inside the mass-weight submodules

Every component of one of the three families of section B is a product of two
field-strength symbols, one carrying `n` covariant derivatives and one carrying `m`.
Such a product lies in `derivSubmodule n * derivSubmodule m`, and so in the mass-weight
submodule of weight `2 * (2 + n) + 2 * (2 + m)`; a span is the smallest submodule
containing its generators, so the whole bi-adjoint subspace lies there too.

What holds is an inclusion and not an equality. The mass-weight submodule of that weight
also contains the towers carrying more covariant derivatives, and the products mixing
two different gauge factors, and none of those is a component of any of the three
families. For the `u(1)` family the inclusion sharpens, so that its span meets the
mass-weight submodule inside the gauge invariants. That sharpening does not come from
`IsU1BiAdjoint`, which constrains the hypercharge factor alone; it comes from
`repGauge_hyperchargeField`, the transformation law of the hypercharge field strength
itself, which fixes it under every gauge element and so makes every component of the
family gauge invariant.

-/

/-- Every field-strength symbol lies in the derivative submodule of its own number of
  covariant derivatives. -/
lemma F_mem_derivSubmodule {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℝ GaugeAlgebra) : F l μ ν φ ∈ h.derivSubmodule n := by
  rw [derivSubmodule]
  exact Submodule.mem_iSup_of_mem l (Submodule.mem_iSup_of_mem μ
    (Submodule.mem_iSup_of_mem ν (Submodule.subset_span ⟨φ, rfl⟩)))

/-- The gluon field strength lies in the derivative submodule of its own number of
  covariant derivatives. -/
lemma gluonField_mem_derivSubmodule {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (a : Fin 8) : h.gluonField l μ ν a ∈ h.derivSubmodule n :=
  h.F_mem_derivSubmodule l μ ν _

/-- The `W`-boson field strength lies in the derivative submodule of its own number of
  covariant derivatives. -/
lemma wField_mem_derivSubmodule {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (i : Fin 3) : h.wField l μ ν i ∈ h.derivSubmodule n :=
  h.F_mem_derivSubmodule l μ ν _

/-- The hypercharge field strength lies in the derivative submodule of its own number of
  covariant derivatives. -/
lemma hyperchargeField_mem_derivSubmodule {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) : h.hyperchargeField l μ ν ∈ h.derivSubmodule n :=
  h.F_mem_derivSubmodule l μ ν _

/-- A product of two derivative submodules lies in the mass-weight submodule of the sum
  of the two mass weights. -/
lemma derivSubmodule_mul_le_massWeightSubmodule (n m : ℕ) :
    h.derivSubmodule n * h.derivSubmodule m
      ≤ h.massWeightSubmodule (2 * (2 + n) + 2 * (2 + m)) :=
  Submodule.mul_le.mpr fun _ hx _ hy =>
    h.massWeightSubmodule_mul_le _ _ (Submodule.mul_mem_mul
      (h.derivSubmodule_le_massWeightSubmodule n hx)
      (h.derivSubmodule_le_massWeightSubmodule m hy))

/-- A product of two field-strength symbols with `n` and `m` covariant derivatives has
  mass weight the sum of the two individual mass weights. -/
lemma F_mul_F_mem_massWeightSubmodule {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ GaugeAlgebra) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (μ' ν' : Fin 1 ⊕ Fin 3) (φ' : Module.Dual ℝ GaugeAlgebra) :
    F l μ ν φ * F l' μ' ν' φ'
      ∈ h.massWeightSubmodule (2 * (2 + n) + 2 * (2 + m)) :=
  h.derivSubmodule_mul_le_massWeightSubmodule n m (Submodule.mul_mem_mul
    (h.F_mem_derivSubmodule l μ ν φ) (h.F_mem_derivSubmodule l' μ' ν' φ'))

/-- The bi-adjoint subspace of a product of two gluon field strengths lies in the
  product of the two derivative submodules the factors come from. -/
lemma isSU3BiAdjoint_gluonField_mul_span_le_derivSubmodule_mul {n m : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isSU3BiAdjoint_gluonField_mul l μ ν l' μ' ν').span
      ≤ h.derivSubmodule n * h.derivSubmodule m := by
  intro x hx
  obtain ⟨c, rfl⟩ :=
    ((h.isSU3BiAdjoint_gluonField_mul l μ ν l' μ' ν').mem_span_iff x).1 hx
  exact Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _
    (Submodule.mul_mem_mul (h.gluonField_mem_derivSubmodule l μ ν (d 0))
      (h.gluonField_mem_derivSubmodule l' μ' ν' (d 1)))

/-- The bi-adjoint subspace of a product of two `W`-boson field strengths lies in the
  product of the two derivative submodules the factors come from. -/
lemma isSU2BiAdjoint_wField_mul_span_le_derivSubmodule_mul {n m : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isSU2BiAdjoint_wField_mul l μ ν l' μ' ν').span
      ≤ h.derivSubmodule n * h.derivSubmodule m := by
  intro x hx
  obtain ⟨c, rfl⟩ := ((h.isSU2BiAdjoint_wField_mul l μ ν l' μ' ν').mem_span_iff x).1 hx
  exact Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _
    (Submodule.mul_mem_mul (h.wField_mem_derivSubmodule l μ ν (d 0))
      (h.wField_mem_derivSubmodule l' μ' ν' (d 1)))

/-- The bi-adjoint subspace of a product of two hypercharge field strengths lies in the
  product of the two derivative submodules the factors come from. -/
lemma isU1BiAdjoint_hyperchargeField_mul_span_le_derivSubmodule_mul {n m : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isU1BiAdjoint_hyperchargeField_mul l μ ν l' μ' ν').span
      ≤ h.derivSubmodule n * h.derivSubmodule m := by
  intro x hx
  obtain ⟨c, rfl⟩ :=
    ((h.isU1BiAdjoint_hyperchargeField_mul l μ ν l' μ' ν').mem_span_iff x).1 hx
  exact Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _
    (Submodule.mul_mem_mul (h.hyperchargeField_mem_derivSubmodule l μ ν)
      (h.hyperchargeField_mem_derivSubmodule l' μ' ν'))

/-- The bi-adjoint subspace of a product of two gluon field strengths lies in the
  mass-weight submodule of the sum of the two mass weights. -/
lemma isSU3BiAdjoint_gluonField_mul_span_le_massWeightSubmodule {n m : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isSU3BiAdjoint_gluonField_mul l μ ν l' μ' ν').span
      ≤ h.massWeightSubmodule (2 * (2 + n) + 2 * (2 + m)) :=
  (h.isSU3BiAdjoint_gluonField_mul_span_le_derivSubmodule_mul l μ ν l' μ' ν').trans
    (h.derivSubmodule_mul_le_massWeightSubmodule n m)

/-- The bi-adjoint subspace of a product of two `W`-boson field strengths lies in the
  mass-weight submodule of the sum of the two mass weights. -/
lemma isSU2BiAdjoint_wField_mul_span_le_massWeightSubmodule {n m : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isSU2BiAdjoint_wField_mul l μ ν l' μ' ν').span
      ≤ h.massWeightSubmodule (2 * (2 + n) + 2 * (2 + m)) :=
  (h.isSU2BiAdjoint_wField_mul_span_le_derivSubmodule_mul l μ ν l' μ' ν').trans
    (h.derivSubmodule_mul_le_massWeightSubmodule n m)

/-- The bi-adjoint subspace of a product of two hypercharge field strengths lies in the
  mass-weight submodule of the sum of the two mass weights. -/
lemma isU1BiAdjoint_hyperchargeField_mul_span_le_massWeightSubmodule {n m : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isU1BiAdjoint_hyperchargeField_mul l μ ν l' μ' ν').span
      ≤ h.massWeightSubmodule (2 * (2 + n) + 2 * (2 + m)) :=
  (h.isU1BiAdjoint_hyperchargeField_mul_span_le_derivSubmodule_mul l μ ν l' μ' ν').trans
    (h.derivSubmodule_mul_le_massWeightSubmodule n m)

/-- The bi-adjoint subspace of a product of two hypercharge field strengths is a space of
  gauge invariants of the expected mass weight, each hypercharge field strength being
  fixed by the whole gauge group on its own. -/
lemma isU1BiAdjoint_hyperchargeField_mul_span_le_inf {n m : ℕ}
    (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3)
    (μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isU1BiAdjoint_hyperchargeField_mul l μ ν l' μ' ν').span
      ≤ h.massWeightSubmodule (2 * (2 + n) + 2 * (2 + m)) ⊓ repGauge.invariants :=
  le_inf (h.isU1BiAdjoint_hyperchargeField_mul_span_le_massWeightSubmodule l μ ν l' μ' ν')
    (IsU1BiAdjoint.span_le_invariants _
      fun g => h.isU1BiAdjointMat_hyperchargeField_mul l μ ν l' μ' ν' g)

/-!

## D. The trace contractions and their mass weights

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
      IsSU3BiAdjoint.map_traceContraction _
        (h.isSU3BiAdjointMat_gluonField_mul l μ ν l' μ' ν' g)

/-- The `W`-boson trace contraction is a gauge invariant of the expected mass weight. -/
lemma traceContraction_wField_mul_mem {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isSU2BiAdjoint_wField_mul l μ ν l' μ' ν').traceContraction
      ∈ h.massWeightSubmodule (2 * (2 + n) + 2 * (2 + m)) ⊓ repGauge.invariants := by
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [h.traceContraction_wField_mul]
    exact Submodule.sum_mem _ fun i _ => h.F_mul_F_mem_massWeightSubmodule l μ ν _ l' μ' ν' _
  · exact (Representation.mem_invariants _ _).mpr fun g =>
      IsSU2BiAdjoint.map_traceContraction _
        (h.isSU2BiAdjointMat_wField_mul l μ ν l' μ' ν' g)

/-- The hypercharge trace contraction is a gauge invariant of the expected mass weight. -/
lemma traceContraction_hyperchargeField_mul_mem {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isU1BiAdjoint_hyperchargeField_mul l μ ν l' μ' ν').traceContraction
      ∈ h.massWeightSubmodule (2 * (2 + n) + 2 * (2 + m)) ⊓ repGauge.invariants := by
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [h.traceContraction_hyperchargeField_mul]
    exact h.F_mul_F_mem_massWeightSubmodule l μ ν _ l' μ' ν' _
  · exact (Representation.mem_invariants _ _).mpr fun g =>
      IsU1BiAdjoint.map_traceContraction _
        (h.isU1BiAdjointMat_hyperchargeField_mul l μ ν l' μ' ν' g)

/-!

## E. The underived trace contractions at mass weight eight

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
    fun g => IsSU3BiAdjoint.map_traceContraction _
      (h.isSU3BiAdjointMat_gluonField_mul ![] μ ν ![] μ' ν' g)

/-- The trace contraction of two underived `W`-boson field strengths lies in the
  zero-weight piece of the gauge weight decomposition of mass weight eight. -/
lemma traceContraction_wField_mul_mem_piece_zero (μ ν μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isSU2BiAdjoint_wField_mul ![] μ ν ![] μ' ν').traceContraction
      ∈ (h.massWeightSubmoduleGaugeWeightEight).piece 0 :=
  GaugeWeightDecomposition.mem_zero_of_invariant _
    (Submodule.mem_inf.mp (h.traceContraction_wField_mul_mem_eight μ ν μ' ν')).1
    fun g => IsSU2BiAdjoint.map_traceContraction _
      (h.isSU2BiAdjointMat_wField_mul ![] μ ν ![] μ' ν' g)

/-- The trace contraction of two underived hypercharge field strengths lies in the
  zero-weight piece of the gauge weight decomposition of mass weight eight. -/
lemma traceContraction_hyperchargeField_mul_mem_piece_zero (μ ν μ' ν' : Fin 1 ⊕ Fin 3) :
    (h.isU1BiAdjoint_hyperchargeField_mul ![] μ ν ![] μ' ν').traceContraction
      ∈ (h.massWeightSubmoduleGaugeWeightEight).piece 0 :=
  GaugeWeightDecomposition.mem_zero_of_invariant _
    (Submodule.mem_inf.mp (h.traceContraction_hyperchargeField_mul_mem_eight μ ν μ' ν')).1
    fun g => IsU1BiAdjoint.map_traceContraction _
      (h.isU1BiAdjointMat_hyperchargeField_mul ![] μ ν ![] μ' ν' g)

/-!

## F. The weight vectors of mass weight eight inside the bi-adjoint spans

Section C runs from the bi-adjoint side to the mass-weight side. The opposite direction
is available for the parts of the mass-weight submodules that see a single gauge factor.
The gauge weight decomposition of the derivative submodules is built from the weight
vectors `adjVec` of one adjoint index, and on a colour direction such a vector is a
combination of gluon field strengths, on the isospin directions a combination of
`W`-boson field strengths, and on the hypercharge direction the hypercharge field
strength itself. A product of two of them is then a bi-adjoint weight vector of the
matching family, so it lies in the span of that family.

At mass weight eight this covers the gluon root part and the isospin root part of the
zero-weight piece computed by `massWeightSubmoduleGaugeWeightEight_piece_zero`. It does
not cover the neutral Cartan part, whose generators may pair a Cartan direction of one
gauge factor with a Cartan direction of another, and such a mixed product is a component
of none of the three bi-adjoint families.

-/

/-- The `su(3)` adjoint weight indices read as weight indices of the whole gauge
  algebra: the three colour roots and the two colour Cartan directions. -/
def su3AdjIdx : IsSU3BiAdjoint.WeightIdx → Fin 4 ⊕ Fin 4 ⊕ Fin 4
  | Sum.inl r => Sum.inl r.castSucc
  | Sum.inr (Sum.inl r) => Sum.inr (Sum.inl r.castSucc)
  | Sum.inr (Sum.inr c) => Sum.inr (Sum.inr c.castSucc.castSucc)

/-- The `su(2)` adjoint weight indices read as weight indices of the whole gauge
  algebra: the isospin root and the isospin Cartan direction. -/
def su2AdjIdx : IsSU2BiAdjoint.WeightIdx → Fin 4 ⊕ Fin 4 ⊕ Fin 4
  | Sum.inl _ => Sum.inl 3
  | Sum.inr (Sum.inl _) => Sum.inr (Sum.inl 3)
  | Sum.inr (Sum.inr _) => Sum.inr (Sum.inr 2)

/-- A weight vector of the colour part of the adjoint is the matching combination of
  gluon field strengths. -/
lemma sum_wtCoeff_smul_gluonField {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (k : IsSU3BiAdjoint.WeightIdx) :
    ∑ a : Fin 8, IsSU3BiAdjoint.wtCoeff k a • h.gluonField l μ ν a
      = h.adjVec l μ ν (su3AdjIdx k) := by
  match k with
  | Sum.inl r =>
    rw [show h.adjVec l μ ν (su3AdjIdx (Sum.inl r))
        = F l μ ν (GaugeAlgebra.stdBasis.coord (GaugeAlgebra.rootIdx r.castSucc).1)
          + Complex.I •
            F l μ ν (GaugeAlgebra.stdBasis.coord (GaugeAlgebra.rootIdx r.castSucc).2)
        from rfl, IsSU3BiAdjoint.rootIdx_castSucc]
    simp only [IsSU3BiAdjoint.wtCoeff, add_smul, ite_smul, one_smul, zero_smul, mul_ite,
      mul_one, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    rfl
  | Sum.inr (Sum.inl r) =>
    rw [show h.adjVec l μ ν (su3AdjIdx (Sum.inr (Sum.inl r)))
        = F l μ ν (GaugeAlgebra.stdBasis.coord (GaugeAlgebra.rootIdx r.castSucc).1)
          - Complex.I •
            F l μ ν (GaugeAlgebra.stdBasis.coord (GaugeAlgebra.rootIdx r.castSucc).2)
        from rfl, IsSU3BiAdjoint.rootIdx_castSucc]
    simp only [IsSU3BiAdjoint.wtCoeff, sub_smul, ite_smul, one_smul, zero_smul, mul_ite,
      mul_one, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    rfl
  | Sum.inr (Sum.inr c) =>
    rw [show h.adjVec l μ ν (su3AdjIdx (Sum.inr (Sum.inr c)))
        = F l μ ν (GaugeAlgebra.stdBasis.coord
            (GaugeAlgebra.cartanIdx c.castSucc.castSucc)) from rfl,
      IsSU3BiAdjoint.cartanIdx_castSucc]
    simp only [IsSU3BiAdjoint.wtCoeff, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl

/-- A weight vector of the isospin part of the adjoint is the matching combination of
  `W`-boson field strengths. -/
lemma sum_wtCoeff_smul_wField {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (k : IsSU2BiAdjoint.WeightIdx) :
    ∑ i : Fin 3, IsSU2BiAdjoint.wtCoeff k i • h.wField l μ ν i
      = h.adjVec l μ ν (su2AdjIdx k) := by
  match k with
  | Sum.inl r =>
    rw [show h.adjVec l μ ν (su2AdjIdx (Sum.inl r))
        = F l μ ν (GaugeAlgebra.stdBasis.coord (GaugeAlgebra.rootIdx 3).1)
          + Complex.I • F l μ ν (GaugeAlgebra.stdBasis.coord (GaugeAlgebra.rootIdx 3).2)
        from rfl, IsSU2BiAdjoint.rootIdx_three]
    simp only [IsSU2BiAdjoint.wtCoeff, add_smul, ite_smul, one_smul, zero_smul, mul_ite,
      mul_one, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    rfl
  | Sum.inr (Sum.inl r) =>
    rw [show h.adjVec l μ ν (su2AdjIdx (Sum.inr (Sum.inl r)))
        = F l μ ν (GaugeAlgebra.stdBasis.coord (GaugeAlgebra.rootIdx 3).1)
          - Complex.I • F l μ ν (GaugeAlgebra.stdBasis.coord (GaugeAlgebra.rootIdx 3).2)
        from rfl, IsSU2BiAdjoint.rootIdx_three]
    simp only [IsSU2BiAdjoint.wtCoeff, sub_smul, ite_smul, one_smul, zero_smul, mul_ite,
      mul_one, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    rfl
  | Sum.inr (Sum.inr c) =>
    rw [show h.adjVec l μ ν (su2AdjIdx (Sum.inr (Sum.inr c)))
        = F l μ ν (GaugeAlgebra.stdBasis.coord (GaugeAlgebra.cartanIdx 2)) from rfl,
      IsSU2BiAdjoint.cartanIdx_two]
    simp only [IsSU2BiAdjoint.wtCoeff, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl

/-- A bi-adjoint weight vector of a product of two gluon field strengths is the product
  of the two contracted field strengths. -/
lemma biVec_gluonField_mul {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3) (c₀ c₁ : Fin 8 → ℂ) :
    (h.isSU3BiAdjoint_gluonField_mul l μ ν l' μ' ν').biVec c₀ c₁
      = (∑ a : Fin 8, c₀ a • h.gluonField l μ ν a)
        * ∑ b : Fin 8, c₁ b • h.gluonField l' μ' ν' b := by
  rw [IsSU3BiAdjoint.biVec, IsSU3BiAdjoint.sum_pi_two, Fintype.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [smul_mul_smul_comm]
  simp

/-- A bi-adjoint weight vector of a product of two `W`-boson field strengths is the
  product of the two contracted field strengths. -/
lemma biVec_wField_mul {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3)
    (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3) (c₀ c₁ : Fin 3 → ℂ) :
    (h.isSU2BiAdjoint_wField_mul l μ ν l' μ' ν').biVec c₀ c₁
      = (∑ i : Fin 3, c₀ i • h.wField l μ ν i)
        * ∑ j : Fin 3, c₁ j • h.wField l' μ' ν' j := by
  rw [IsSU2BiAdjoint.biVec, IsSU2BiAdjoint.sum_pi_two, Fintype.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [smul_mul_smul_comm]
  simp

/-- A product of two colour weight vectors of the adjoint is a bi-adjoint weight vector
  of the corresponding family of two gluon field strengths. -/
lemma adjVec_mul_adjVec_eq_biVec_gluonField {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3)
    (k₀ k₁ : IsSU3BiAdjoint.WeightIdx) :
    h.adjVec l μ ν (su3AdjIdx k₀) * h.adjVec l' μ' ν' (su3AdjIdx k₁)
      = (h.isSU3BiAdjoint_gluonField_mul l μ ν l' μ' ν').biVec
          (IsSU3BiAdjoint.wtCoeff k₀) (IsSU3BiAdjoint.wtCoeff k₁) := by
  rw [h.biVec_gluonField_mul, h.sum_wtCoeff_smul_gluonField,
    h.sum_wtCoeff_smul_gluonField]

/-- A product of two isospin weight vectors of the adjoint is a bi-adjoint weight vector
  of the corresponding family of two `W`-boson field strengths. -/
lemma adjVec_mul_adjVec_eq_biVec_wField {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3)
    (k₀ k₁ : IsSU2BiAdjoint.WeightIdx) :
    h.adjVec l μ ν (su2AdjIdx k₀) * h.adjVec l' μ' ν' (su2AdjIdx k₁)
      = (h.isSU2BiAdjoint_wField_mul l μ ν l' μ' ν').biVec
          (IsSU2BiAdjoint.wtCoeff k₀) (IsSU2BiAdjoint.wtCoeff k₁) := by
  rw [h.biVec_wField_mul, h.sum_wtCoeff_smul_wField, h.sum_wtCoeff_smul_wField]

/-- A product of two colour weight vectors of the adjoint lies in the bi-adjoint subspace
  of the corresponding family of two gluon field strengths. -/
lemma adjVec_mul_adjVec_mem_isSU3BiAdjoint_span {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3)
    (k₀ k₁ : IsSU3BiAdjoint.WeightIdx) :
    h.adjVec l μ ν (su3AdjIdx k₀) * h.adjVec l' μ' ν' (su3AdjIdx k₁)
      ∈ (h.isSU3BiAdjoint_gluonField_mul l μ ν l' μ' ν').span := by
  rw [h.adjVec_mul_adjVec_eq_biVec_gluonField, IsSU3BiAdjoint.span_eq_wtSpan,
    IsSU3BiAdjoint.wtSpan]
  exact Submodule.mem_iSup_of_mem (k₀, k₁) (Submodule.mem_span_singleton_self _)

/-- A product of two isospin weight vectors of the adjoint lies in the bi-adjoint
  subspace of the corresponding family of two `W`-boson field strengths. -/
lemma adjVec_mul_adjVec_mem_isSU2BiAdjoint_span {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3)
    (k₀ k₁ : IsSU2BiAdjoint.WeightIdx) :
    h.adjVec l μ ν (su2AdjIdx k₀) * h.adjVec l' μ' ν' (su2AdjIdx k₁)
      ∈ (h.isSU2BiAdjoint_wField_mul l μ ν l' μ' ν').span := by
  rw [h.adjVec_mul_adjVec_eq_biVec_wField, IsSU2BiAdjoint.span_eq_wtSpan,
    IsSU2BiAdjoint.wtSpan]
  exact Submodule.mem_iSup_of_mem (k₀, k₁) (Submodule.mem_span_singleton_self _)

/-- The hypercharge weight vector of the adjoint is the hypercharge field strength, the
  adjoint action of the gauge group on the `u(1)` factor being trivial. -/
lemma adjVec_hyperchargeIdx {n : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3) (μ ν : Fin 1 ⊕ Fin 3) :
    h.adjVec l μ ν (Sum.inr (Sum.inr 3)) = h.hyperchargeField l μ ν := rfl

/-- A product of two hypercharge weight vectors of the adjoint lies in the bi-adjoint
  subspace of the corresponding family of two hypercharge field strengths. -/
lemma adjVec_mul_adjVec_mem_isU1BiAdjoint_span {n m : ℕ} (l : Fin n → Fin 1 ⊕ Fin 3)
    (μ ν : Fin 1 ⊕ Fin 3) (l' : Fin m → Fin 1 ⊕ Fin 3) (μ' ν' : Fin 1 ⊕ Fin 3) :
    h.adjVec l μ ν (Sum.inr (Sum.inr 3)) * h.adjVec l' μ' ν' (Sum.inr (Sum.inr 3))
      ∈ (h.isU1BiAdjoint_hyperchargeField_mul l μ ν l' μ' ν').span := by
  rw [h.adjVec_hyperchargeIdx, h.adjVec_hyperchargeIdx, IsU1BiAdjoint.span]
  exact Submodule.mem_iSup_of_mem ![0, 0] (Submodule.mem_span_singleton_self _)

/-- The gluon contribution to the zero-weight piece of mass weight eight lies in the join
  of the bi-adjoint subspaces of the products of two underived gluon field strengths. -/
lemma gluonRootPart_le_iSup_isSU3BiAdjoint_span :
    h.gluonRootPart ≤ ⨆ (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3) (μ' : Fin 1 ⊕ Fin 3)
      (ν' : Fin 1 ⊕ Fin 3), (h.isSU3BiAdjoint_gluonField_mul ![] μ ν ![] μ' ν').span := by
  have key : ∀ r : Fin 3, h.rootRaisingSpan r.castSucc * h.rootLoweringSpan r.castSucc
      ≤ ⨆ (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3) (μ' : Fin 1 ⊕ Fin 3)
        (ν' : Fin 1 ⊕ Fin 3), (h.isSU3BiAdjoint_gluonField_mul ![] μ ν ![] μ' ν').span := by
    intro r
    rw [rootRaisingSpan, rootLoweringSpan]
    simp only [Submodule.iSup_mul, Submodule.mul_iSup]
    refine iSup_le fun l => iSup_le fun μ => iSup_le fun ν => iSup_le fun l' =>
      iSup_le fun μ' => iSup_le fun ν' => ?_
    rw [Submodule.span_mul_span, Set.singleton_mul_singleton,
      Submodule.span_singleton_le_iff_mem, Subsingleton.elim l ![],
      Subsingleton.elim l' ![]]
    exact Submodule.mem_iSup_of_mem μ' (Submodule.mem_iSup_of_mem ν'
      (Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem ν
        (h.adjVec_mul_adjVec_mem_isSU3BiAdjoint_span ![] μ' ν' ![] μ ν
          (Sum.inl r) (Sum.inr (Sum.inl r))))))
  rw [gluonRootPart]
  exact sup_le (key 0) (sup_le (key 1) (key 2))

/-- The isospin contribution to the zero-weight piece of mass weight eight lies in the
  join of the bi-adjoint subspaces of the products of two underived `W`-boson field
  strengths. -/
lemma isospinRootPart_le_iSup_isSU2BiAdjoint_span :
    h.isospinRootPart ≤ ⨆ (μ : Fin 1 ⊕ Fin 3) (ν : Fin 1 ⊕ Fin 3) (μ' : Fin 1 ⊕ Fin 3)
      (ν' : Fin 1 ⊕ Fin 3), (h.isSU2BiAdjoint_wField_mul ![] μ ν ![] μ' ν').span := by
  rw [isospinRootPart, rootRaisingSpan, rootLoweringSpan]
  simp only [Submodule.iSup_mul, Submodule.mul_iSup]
  refine iSup_le fun l => iSup_le fun μ => iSup_le fun ν => iSup_le fun l' =>
    iSup_le fun μ' => iSup_le fun ν' => ?_
  rw [Submodule.span_mul_span, Set.singleton_mul_singleton,
    Submodule.span_singleton_le_iff_mem, Subsingleton.elim l ![],
    Subsingleton.elim l' ![]]
  exact Submodule.mem_iSup_of_mem μ' (Submodule.mem_iSup_of_mem ν'
    (Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem ν
      (h.adjVec_mul_adjVec_mem_isSU2BiAdjoint_span ![] μ' ν' ![] μ ν
        (Sum.inl 0) (Sum.inr (Sum.inl 0))))))

end IsGaugeSector

end StandardModel
