/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.QED.JetAlgebra.Invariants.Sectors
/-!
# The invariants in monomial form

The Lorentz transformation law of the second-derivative field strength, the
(anti)commutation rules for the covariant factors, the parametric boosts along
the three coordinate axes, and the four renormalizable invariants written out
in the monomial basis. These are the inputs to the weight-eight analysis.
-/

@[expose] public section

set_option maxHeartbeats 1000000

namespace QED
open TensorProduct StandardModel

namespace JetAlgebra

open scoped minkowskiMatrix PauliMatrix
open Matrix MatrixGroups
/-!

### Commutation and anticommutation of the covariant factors

-/

/-- The embedded field-strength derivatives commute: they live in the
  commutative bosonic factor of the jet algebra. -/
lemma fieldStrengthDeriv_mul_comm (s s' : Multiset (Fin 1 ⊕ Fin 3))
    (μ ν ρ τ : Fin 1 ⊕ Fin 3) :
    fieldStrengthDeriv s μ ν * fieldStrengthDeriv s' ρ τ =
      fieldStrengthDeriv s' ρ τ * fieldStrengthDeriv s μ ν := by
  rw [fieldStrengthDeriv, fieldStrengthDeriv, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul,
    mul_comm (BBoson.JetAlgebra.fieldStrengthDeriv s μ ν)]

set_option maxHeartbeats 16000000 in
/-- The embedded lepton-linear and conjugate-linear elements anticommute:
  both are odd elements of the exterior factor of the jet algebra. -/
lemma leptonLinearIncl_mul_conjLeptonLinearIncl_anticomm (x : LeptonLinear)
    (y : ConjLeptonLinear) :
    leptonLinearIncl x * conjLeptonLinearIncl y =
      -(conjLeptonLinearIncl y * leptonLinearIncl x) := by
  have hz₁ : ∀ z : JetAlgebra, 0 * z = 0 := fun z => zero_mul z
  have hz₂ : ∀ z : JetAlgebra, z * 0 = 0 := fun z => mul_zero z
  have hd₁ : ∀ u v w : JetAlgebra, (u + v) * w = u * w + v * w := by grind
  have hd₂ : ∀ u v w : JetAlgebra, u * (v + w) = u * v + u * w := by grind
  have hι : ∀ (a : LeptonComponent) (b : ConjLeptonComponent),
      leptonComponentIncl a * conjLeptonComponentIncl b =
        -(conjLeptonComponentIncl b * leptonComponentIncl a) := fun a b => by
    rw [leptonComponentIncl_apply, conjLeptonComponentIncl_apply]
    exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, hz₁, hz₂, neg_zero]
  | add a b ha hb => rw [map_add, hd₁, hd₂, ha, hb, neg_add]
  | tmul p a =>
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero, hz₂, hz₁, neg_zero]
    | add c d hc hd => rw [map_add, hd₂, hd₁, hc, hd, neg_add]
    | tmul q b =>
      rw [leptonLinearIncl_tmul, conjLeptonLinearIncl_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        hι a b, mul_comm q p, TensorProduct.tmul_neg]

/-- The covariant lepton derivatives anticommute with the conjugate covariant
  derivatives. -/
lemma Dψ_mul_Dbarψ_anticomm (l l' : List (Fin 1 ⊕ Fin 3)) (α β : Fin 2) :
    Dψ l α * Dbarψ l' β = -(Dbarψ l' β * Dψ l α) := by
  rw [Dψ_eq_leptonLinearIncl, Dbarψ_eq_conjLeptonLinearIncl,
    leptonLinearIncl_mul_conjLeptonLinearIncl_anticomm]

set_option maxHeartbeats 16000000 in
/-- Two embedded lepton-linear elements anticommute. -/
lemma leptonLinearIncl_mul_leptonLinearIncl_anticomm (x y : LeptonLinear) :
    leptonLinearIncl x * leptonLinearIncl y =
      -(leptonLinearIncl y * leptonLinearIncl x) := by
  have hz₁ : ∀ z : JetAlgebra, 0 * z = 0 := fun z => zero_mul z
  have hz₂ : ∀ z : JetAlgebra, z * 0 = 0 := fun z => mul_zero z
  have hd₁ : ∀ u v w : JetAlgebra, (u + v) * w = u * w + v * w := by grind
  have hd₂ : ∀ u v w : JetAlgebra, u * (v + w) = u * v + u * w := by grind
  have hι : ∀ a b : LeptonComponent,
      leptonComponentIncl a * leptonComponentIncl b =
        -(leptonComponentIncl b * leptonComponentIncl a) := fun a b => by
    rw [leptonComponentIncl_apply, leptonComponentIncl_apply]
    exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, hz₁, hz₂, neg_zero]
  | add a b ha hb => rw [map_add, hd₁, hd₂, ha, hb, neg_add]
  | tmul p a =>
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero, hz₂, hz₁, neg_zero]
    | add c d hc hd => rw [map_add, hd₂, hd₁, hc, hd, neg_add]
    | tmul q b =>
      rw [leptonLinearIncl_tmul, leptonLinearIncl_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        hι a b, mul_comm q p, TensorProduct.tmul_neg]

/-!

### Parametric boosts along the three axes

The one-parameter families of boosts `diag(t, t⁻¹)` (along `z`) and their
conjugates along `x` and `y`, with symbolic Lorentz matrices in `t`.

-/

/-- The lift `diag(t, t⁻¹)` of the boost along the `z`-axis with rapidity
  `2 log t`. -/
noncomputable def boostZel (t : ℝ) (ht : t ≠ 0) : SL(2,ℂ) :=
  ⟨!![(t : ℂ), 0; 0, (t : ℂ)⁻¹], by
    have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
    rw [Matrix.det_fin_two_of]
    simp [mul_inv_cancel₀ htc]⟩

/-- The lift of the boost along the `x`-axis with rapidity `2 log t`. -/
noncomputable def boostXel (t : ℝ) (ht : t ≠ 0) : SL(2,ℂ) :=
  ⟨!![((t : ℂ) + (t : ℂ)⁻¹)/2, ((t : ℂ) - (t : ℂ)⁻¹)/2;
      ((t : ℂ) - (t : ℂ)⁻¹)/2, ((t : ℂ) + (t : ℂ)⁻¹)/2], by
    have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
    rw [Matrix.det_fin_two_of]
    field_simp
    ring⟩

/-- The lift of the boost along the `y`-axis with rapidity `2 log t`. -/
noncomputable def boostYel (t : ℝ) (ht : t ≠ 0) : SL(2,ℂ) :=
  ⟨!![((t : ℂ) + (t : ℂ)⁻¹)/2, -Complex.I * ((t : ℂ) - (t : ℂ)⁻¹)/2;
      Complex.I * ((t : ℂ) - (t : ℂ)⁻¹)/2, ((t : ℂ) + (t : ℂ)⁻¹)/2], by
    have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
    have h2 : -Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2 *
        (Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2) =
        ((t : ℂ) - (t : ℂ)⁻¹) / 2 * (((t : ℂ) - (t : ℂ)⁻¹) / 2) := by
      have hI : -Complex.I * Complex.I = 1 := by
        rw [neg_mul, Complex.I_mul_I, neg_neg]
      calc -Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2 *
            (Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2)
          = (-Complex.I * Complex.I) *
              (((t : ℂ) - (t : ℂ)⁻¹) / 2 * (((t : ℂ) - (t : ℂ)⁻¹) / 2)) := by
            ring
        _ = ((t : ℂ) - (t : ℂ)⁻¹) / 2 * (((t : ℂ) - (t : ℂ)⁻¹) / 2) := by
            rw [hI, one_mul]
    rw [Matrix.det_fin_two_of, h2]
    field_simp
    ring⟩

/-- The Lorentz matrix of `boostZel t`: `ch = (t² + t⁻²)/2` on the time-time
  and `zz` entries, `-sh = -(t² - t⁻²)/2` on the mixed entries. -/
noncomputable def boostMatZ (t : ℝ) : (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → ℝ
  | Sum.inl _, Sum.inl _ => (t^2 + (t⁻¹)^2)/2
  | Sum.inl _, Sum.inr 2 => -((t^2 - (t⁻¹)^2)/2)
  | Sum.inr 2, Sum.inl _ => -((t^2 - (t⁻¹)^2)/2)
  | Sum.inr 0, Sum.inr 0 => 1
  | Sum.inr 1, Sum.inr 1 => 1
  | Sum.inr 2, Sum.inr 2 => (t^2 + (t⁻¹)^2)/2
  | _, _ => 0

/-- The Lorentz matrix of `boostXel t`. -/
noncomputable def boostMatX (t : ℝ) : (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → ℝ
  | Sum.inl _, Sum.inl _ => (t^2 + (t⁻¹)^2)/2
  | Sum.inl _, Sum.inr 0 => -((t^2 - (t⁻¹)^2)/2)
  | Sum.inr 0, Sum.inl _ => -((t^2 - (t⁻¹)^2)/2)
  | Sum.inr 0, Sum.inr 0 => (t^2 + (t⁻¹)^2)/2
  | Sum.inr 1, Sum.inr 1 => 1
  | Sum.inr 2, Sum.inr 2 => 1
  | _, _ => 0

/-- The Lorentz matrix of `boostYel t`. -/
noncomputable def boostMatY (t : ℝ) : (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → ℝ
  | Sum.inl _, Sum.inl _ => (t^2 + (t⁻¹)^2)/2
  | Sum.inl _, Sum.inr 1 => -((t^2 - (t⁻¹)^2)/2)
  | Sum.inr 1, Sum.inl _ => -((t^2 - (t⁻¹)^2)/2)
  | Sum.inr 0, Sum.inr 0 => 1
  | Sum.inr 1, Sum.inr 1 => (t^2 + (t⁻¹)^2)/2
  | Sum.inr 2, Sum.inr 2 => 1
  | _, _ => 0

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- The Lorentz matrix of the parametric `z`-boost. -/
lemma toLorentzGroup_boostZel (t : ℝ) (ht : t ≠ 0) (a b : Fin 1 ⊕ Fin 3) :
    (Lorentz.SL2C.toLorentzGroup (boostZel t ht)).1 a b = boostMatZ t a b := by
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  refine Complex.ofReal_injective ?_
  rw [Lorentz.SL2C.toLorentzGroup_eq_trace]
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    · try simp [boostZel, boostMatZ, PauliMatrix.pauliSelfAdjoint',
        PauliMatrix.pauliMatrix, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose, Matrix.diag, Complex.conj_ofNat,
        Complex.conj_ofReal, Complex.conj_I, Complex.I_sq]
      try simp [Matrix.vecMul, Matrix.vecHead, Matrix.vecTail]
      try push_cast
      try field_simp
      try ring_nf
      try norm_num [Complex.I_sq, Complex.conj_ofNat]
      try ring

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- The Lorentz matrix of the parametric `x`-boost. -/
lemma toLorentzGroup_boostXel (t : ℝ) (ht : t ≠ 0) (a b : Fin 1 ⊕ Fin 3) :
    (Lorentz.SL2C.toLorentzGroup (boostXel t ht)).1 a b = boostMatX t a b := by
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  refine Complex.ofReal_injective ?_
  rw [Lorentz.SL2C.toLorentzGroup_eq_trace]
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    · try simp [boostXel, boostMatX, PauliMatrix.pauliSelfAdjoint',
        PauliMatrix.pauliMatrix, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose, Matrix.diag, Complex.conj_ofNat,
        Complex.conj_ofReal, Complex.conj_I, Complex.I_sq]
      try simp [Matrix.vecMul, Matrix.vecHead, Matrix.vecTail]
      try push_cast
      try field_simp
      try ring_nf
      try norm_num [Complex.I_sq, Complex.conj_ofNat]
      try ring

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- The Lorentz matrix of the parametric `y`-boost. -/
lemma toLorentzGroup_boostYel (t : ℝ) (ht : t ≠ 0) (a b : Fin 1 ⊕ Fin 3) :
    (Lorentz.SL2C.toLorentzGroup (boostYel t ht)).1 a b = boostMatY t a b := by
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  refine Complex.ofReal_injective ?_
  rw [Lorentz.SL2C.toLorentzGroup_eq_trace]
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    · try simp [boostYel, boostMatY, PauliMatrix.pauliSelfAdjoint',
        PauliMatrix.pauliMatrix, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose, Matrix.diag, Complex.conj_ofNat,
        Complex.conj_ofReal, Complex.conj_I, Complex.I_sq]
      try simp [Matrix.vecMul, Matrix.vecHead, Matrix.vecTail]
      try push_cast
      try field_simp
      try ring_nf
      try norm_num [Complex.I_sq, Complex.conj_ofNat]
      try ring

/-- The inverse of the parametric `z`-boost is the boost at the inverse
  parameter. -/
lemma boostZel_inv (t : ℝ) (ht : t ≠ 0) :
    (boostZel t ht)⁻¹ = boostZel t⁻¹ (inv_ne_zero ht) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  fin_cases i <;> fin_cases j <;>
    simp [boostZel, Complex.ofReal_inv, inv_inv]

/-- The inverse of the parametric `x`-boost is the boost at the inverse
  parameter. -/
lemma boostXel_inv (t : ℝ) (ht : t ≠ 0) :
    (boostXel t ht)⁻¹ = boostXel t⁻¹ (inv_ne_zero ht) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  fin_cases i <;> fin_cases j <;>
    · simp [boostXel, Complex.ofReal_inv, inv_inv]
      try ring

/-- The inverse of the parametric `y`-boost is the boost at the inverse
  parameter. -/
lemma boostYel_inv (t : ℝ) (ht : t ≠ 0) :
    (boostYel t ht)⁻¹ = boostYel t⁻¹ (inv_ne_zero ht) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  fin_cases i <;> fin_cases j <;>
    · simp [boostYel, Complex.ofReal_inv, inv_inv]
      try ring

/-- The inverse of the parametric `z`-boost, entrywise, with real entries. -/
lemma boostZel_inv_coe (t : ℝ) (ht : t ≠ 0) :
    ((boostZel t ht)⁻¹ : SL(2,ℂ)).1 =
      !![(((t⁻¹ : ℝ)) : ℂ), 0; 0, ((t : ℝ) : ℂ)] := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boostZel]

/-- The inverse of the parametric `x`-boost, entrywise. -/
lemma boostXel_inv_coe (t : ℝ) (ht : t ≠ 0) :
    ((boostXel t ht)⁻¹ : SL(2,ℂ)).1 =
      !![((t : ℂ) + (t : ℂ)⁻¹)/2, -(((t : ℂ) - (t : ℂ)⁻¹)/2);
         -(((t : ℂ) - (t : ℂ)⁻¹)/2), ((t : ℂ) + (t : ℂ)⁻¹)/2] := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boostXel]

/-- The inverse of the parametric `y`-boost, entrywise. -/
lemma boostYel_inv_coe (t : ℝ) (ht : t ≠ 0) :
    ((boostYel t ht)⁻¹ : SL(2,ℂ)).1 =
      !![((t : ℂ) + (t : ℂ)⁻¹)/2, Complex.I * ((t : ℂ) - (t : ℂ)⁻¹)/2;
         -(Complex.I * ((t : ℂ) - (t : ℂ)⁻¹)/2), ((t : ℂ) + (t : ℂ)⁻¹)/2] := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;> · simp [boostYel]; try ring

/-- The Lorentz matrix of the inverse `z`-boost: the boost matrix at the
  inverse parameter. -/
lemma toLorentzGroup_boostZel_inv (t : ℝ) (ht : t ≠ 0) (a b : Fin 1 ⊕ Fin 3) :
    (Lorentz.SL2C.toLorentzGroup (boostZel t ht)⁻¹).1 a b = boostMatZ t⁻¹ a b := by
  rw [boostZel_inv, toLorentzGroup_boostZel]

/-- The Lorentz matrix of the inverse `x`-boost. -/
lemma toLorentzGroup_boostXel_inv (t : ℝ) (ht : t ≠ 0) (a b : Fin 1 ⊕ Fin 3) :
    (Lorentz.SL2C.toLorentzGroup (boostXel t ht)⁻¹).1 a b = boostMatX t⁻¹ a b := by
  rw [boostXel_inv, toLorentzGroup_boostXel]

/-- The Lorentz matrix of the inverse `y`-boost. -/
lemma toLorentzGroup_boostYel_inv (t : ℝ) (ht : t ≠ 0) (a b : Fin 1 ⊕ Fin 3) :
    (Lorentz.SL2C.toLorentzGroup (boostYel t ht)⁻¹).1 a b = boostMatY t⁻¹ a b := by
  rw [boostYel_inv, toLorentzGroup_boostYel]

/-!

### The four invariants in monomial form

-/

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- The Maxwell term as an explicit combination of the six independent
  field-strength squares. -/
lemma maxwellTerm_eq : maxwellTerm =
    (-2 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0))
    + (-2 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1))
    + (-2 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2))
    + (2 : ℂ) • (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1))
    + (2 : ℂ) • (fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2))
    + (2 : ℂ) • (fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2)) := by
  have hz₁ : ∀ z : JetAlgebra, 0 * z = 0 := fun z => zero_mul z
  have hz₂ : ∀ z : JetAlgebra, z * 0 = 0 := fun z => mul_zero z
  have hnm : ∀ u v : JetAlgebra, (-u) * v = -(u * v) := by grind
  have hmn : ∀ u v : JetAlgebra, u * (-v) = -(u * v) := by grind
  rw [maxwellTerm]
  simp only [Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three,
    minkowskiMatrix.inl_0_inl_0, minkowskiMatrix.inr_i_inr_i,
    fieldStrengthDeriv_self, hz₁, hz₂, smul_zero, add_zero, zero_add]
  simp only [
    show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) =
      -fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) from
      fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 0),
    show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) =
      -fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) from
      fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 1),
    show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) =
      -fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) from
      fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 2),
    show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) =
      -fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) from
      fieldStrengthDeriv_antisymm {} (Sum.inr 0) (Sum.inr 1),
    show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) =
      -fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) from
      fieldStrengthDeriv_antisymm {} (Sum.inr 0) (Sum.inr 2),
    show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) =
      -fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) from
      fieldStrengthDeriv_antisymm {} (Sum.inr 1) (Sum.inr 2),
    hnm, hmn, neg_neg]
  push_cast
  module

set_option maxHeartbeats 8000000 in
set_option linter.unusedSimpArgs false in
/-- The theta term as an explicit combination of the three pair-partition
  products of field strengths. -/
lemma thetaTerm_eq : thetaTerm =
    (8 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2))
    + (-8 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2))
    + (8 : ℂ) • (fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1)) := by
  have hnm : ∀ u v : JetAlgebra, (-u) * v = -(u * v) := by grind
  have hmn : ∀ u v : JetAlgebra, u * (-v) = -(u * v) := by grind
  rw [thetaTerm]
  conv_lhs =>
    enter [2, p]
    rw [show (1 : Fin 4) = (0 : Fin 3).succ from rfl,
      show (2 : Fin 4) = (1 : Fin 3).succ from rfl,
      show (3 : Fin 4) = (2 : Fin 3).succ from rfl]
  rw [Finset.univ_perm_fin_succ, Finset.sum_map, Fintype.sum_prod_type]
  conv_lhs =>
    enter [2, i]
    rw [Finset.univ_perm_fin_succ, Finset.sum_map, Fintype.sum_prod_type]
  conv_lhs =>
    enter [2, i, 2, j]
    rw [Finset.univ_perm_fin_succ, Finset.sum_map, Fintype.sum_prod_type]
  conv_lhs =>
    enter [2, i, 2, j, 2, k]
    rw [Fintype.sum_subsingleton _ (1 : Equiv.Perm (Fin 1))]
  simp only [Equiv.coe_toEmbedding, Fin.sum_univ_four, Fin.sum_univ_three,
    Fin.sum_univ_two,
    show ((1 : Fin 3)) = (0 : Fin 2).succ from rfl,
    show ((2 : Fin 3)) = (1 : Fin 2).succ from rfl,
    Equiv.Perm.decomposeFin_symm_of_one,
    Equiv.Perm.decomposeFin.symm_sign,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one,
    Equiv.Perm.decomposeFin_symm_apply_succ]
  simp only [show ((0 : Fin 2).succ) = (1 : Fin 3) from rfl,
    show ((1 : Fin 2).succ) = (2 : Fin 3) from rfl,
    show ((0 : Fin 3).succ) = (1 : Fin 4) from rfl,
    show ((1 : Fin 3).succ) = (2 : Fin 4) from rfl,
    show ((2 : Fin 3).succ) = (3 : Fin 4) from rfl,
    Equiv.swap_self, Equiv.Perm.sign_refl, Equiv.refl_apply, Equiv.Perm.sign_one,
    Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne,
    Equiv.Perm.sign_swap', Fin.reduceEq, reduceIte, ne_eq, not_false_iff,
    show ((finSumFinEquiv (m := 1) (n := 3)).symm 0) = Sum.inl 0 from rfl,
    show ((finSumFinEquiv (m := 1) (n := 3)).symm 1) = Sum.inr 0 from rfl,
    show ((finSumFinEquiv (m := 1) (n := 3)).symm 2) = Sum.inr 1 from rfl,
    show ((finSumFinEquiv (m := 1) (n := 3)).symm 3) = Sum.inr 2 from rfl,
    Units.val_one, Units.val_neg, one_smul, neg_smul, one_mul, mul_one]
  simp only [
    show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inl 0) =
      -fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) from
      fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 0),
    show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inl 0) =
      -fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) from
      fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 1),
    show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inl 0) =
      -fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) from
      fieldStrengthDeriv_antisymm {} (Sum.inl 0) (Sum.inr 2),
    show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 0) =
      -fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) from
      fieldStrengthDeriv_antisymm {} (Sum.inr 0) (Sum.inr 1),
    show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 0) =
      -fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) from
      fieldStrengthDeriv_antisymm {} (Sum.inr 0) (Sum.inr 2),
    show fieldStrengthDeriv {} (Sum.inr 2) (Sum.inr 1) =
      -fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) from
      fieldStrengthDeriv_antisymm {} (Sum.inr 1) (Sum.inr 2),
    hnm, hmn, neg_neg]
  simp only [
    show fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) =
      fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 0) *
        fieldStrengthDeriv {} (Sum.inr 1) (Sum.inr 2) from
      fieldStrengthDeriv_mul_comm {} {} _ _ _ _,
    show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) =
      fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 2) from
      fieldStrengthDeriv_mul_comm {} {} _ _ _ _,
    show fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) *
        fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) =
      fieldStrengthDeriv {} (Sum.inl 0) (Sum.inr 2) *
        fieldStrengthDeriv {} (Sum.inr 0) (Sum.inr 1) from
      fieldStrengthDeriv_mul_comm {} {} _ _ _ _]
  module

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
/-- The fermion kinetic term as an explicit combination of the eight
  `ψ̄ (D ψ)` monomials. -/
lemma fermionKineticTerm_eq : fermionKineticTerm =
    Complex.I • ((Dbarψ [] 0 * Dψ [Sum.inl 0] 0 + Dbarψ [] 1 * Dψ [Sum.inl 0] 1)
      - (Dbarψ [] 0 * Dψ [Sum.inr 0] 1 + Dbarψ [] 1 * Dψ [Sum.inr 0] 0)
      - Complex.I • (Dbarψ [] 0 * Dψ [Sum.inr 1] 1 - Dbarψ [] 1 * Dψ [Sum.inr 1] 0)
      - (Dbarψ [] 0 * Dψ [Sum.inr 2] 0 - Dbarψ [] 1 * Dψ [Sum.inr 2] 1)) := by
  rw [fermionKineticTerm]
  congr 1
  simp only [Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three,
    Fin.sum_univ_two]
  norm_num [kineticPauli, PauliMatrix.pauliSelfAdjoint', PauliMatrix.pauliMatrix,
    Matrix.transpose_apply, Matrix.one_apply]
  module

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
/-- The conjugate fermion kinetic term as an explicit combination of the eight
  `(D̄ ψ̄) ψ` monomials. -/
lemma fermionKineticTermBar_eq : fermionKineticTermBar =
    (-Complex.I) • ((Dbarψ [Sum.inl 0] 0 * Dψ [] 0 + Dbarψ [Sum.inl 0] 1 * Dψ [] 1)
      - (Dbarψ [Sum.inr 0] 0 * Dψ [] 1 + Dbarψ [Sum.inr 0] 1 * Dψ [] 0)
      - Complex.I • (Dbarψ [Sum.inr 1] 0 * Dψ [] 1 - Dbarψ [Sum.inr 1] 1 * Dψ [] 0)
      - (Dbarψ [Sum.inr 2] 0 * Dψ [] 0 - Dbarψ [Sum.inr 2] 1 * Dψ [] 1)) := by
  rw [fermionKineticTermBar]
  congr 1
  simp only [Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_three,
    Fin.sum_univ_two]
  norm_num [kineticPauli, PauliMatrix.pauliSelfAdjoint', PauliMatrix.pauliMatrix,
    Matrix.transpose_apply, Matrix.one_apply]
  module
end JetAlgebra

end QED
