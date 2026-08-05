/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Physlib.Particles.StandardModel.GaugeGroup.Jet
public import Physlib.Relativity.Tensors.ComplexTensor.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Representation
public import Physlib.Relativity.SL2C.Basic
public import Physlib.Mathematics.ConjModule
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Physlib.Particles.LagrangianTheory.Basic
public import Physlib.Mathematics.MvPowerSeriesDerivative
public import Physlib.Mathematics.MvPolynomialTranslation
public import Mathlib.Algebra.MvPolynomial.Derivation
/-!
# The Maurer–Cartan forms of the jet gauge group

The Maurer–Cartan forms `i (∂_ν U) U†` of a jet of gauge transformations, one for
each factor of the Standard Model gauge group: the scalar-valued `U(1)` form and
the matrix-valued `SU(3)` and `SU(2)` forms. These are the inhomogeneous terms in
the local gauge transformations of the corresponding gauge bosons.

The abelian `U(1)` form is an additive cocycle; the nonabelian forms satisfy the
twisted cocycle law `mc(UV) = mc(U) + U mc(V) U†`. Each form satisfies its
Maurer–Cartan structure equation, relating the antisymmetrized derivative to the
commutator; in the abelian case the derivative is symmetric, i.e. the form is
closed.

-/

@[expose] public section
namespace StandardModel
open MvPowerSeries

/-!

## The Maurer–Cartan forms of the jet gauge group

-/

/-- The `U(1)` Maurer–Cartan form of a jet of gauge transformations in the
  direction `ν`: the series `i (∂_ν u) ū` for `u` the hypercharge factor of the
  jet. -/
noncomputable def maurerCartanU1 (g : JetGaugeGroupI) (ν : Fin 1 ⊕ Fin 3) : JetRing :=
  (MvPowerSeries.C Complex.I : JetRing) * (pderiv ℂ ν (g.2.2 : JetRing) * star (g.2.2 : JetRing))

/-- The `SU(3)` Maurer–Cartan form of a jet of gauge transformations in the
  direction `ν`: the matrix-valued series `i (∂_ν U) U†` for `U` the colour factor
  of the jet, with the formal partial derivative applied entrywise and `star` the
  conjugate transpose. -/
noncomputable def maurerCartanSU3 (g : JetGaugeGroupI) (ν : Fin 1 ⊕ Fin 3) :
    Matrix (Fin 3) (Fin 3) JetRing :=
  (MvPowerSeries.C Complex.I : JetRing) •
    ((g.1 : Matrix (Fin 3) (Fin 3) JetRing).map (pderiv ℂ ν) *
      star (g.1 : Matrix (Fin 3) (Fin 3) JetRing))

/-- The `SU(2)` Maurer–Cartan form of a jet of gauge transformations in the
  direction `ν`: the matrix-valued series `i (∂_ν U) U†` for `U` the weak factor
  of the jet, with the formal partial derivative applied entrywise and `star` the
  conjugate transpose. -/
noncomputable def maurerCartanSU2 (g : JetGaugeGroupI) (ν : Fin 1 ⊕ Fin 3) :
    Matrix (Fin 2) (Fin 2) JetRing :=
  (MvPowerSeries.C Complex.I : JetRing) •
    ((g.2.1 : Matrix (Fin 2) (Fin 2) JetRing).map (pderiv ℂ ν) *
      star (g.2.1 : Matrix (Fin 2) (Fin 2) JetRing))

/-!

### Basic properties of the Maurer–Cartan forms

-/

@[simp]
lemma maurerCartanU1_one (ν : Fin 1 ⊕ Fin 3) : maurerCartanU1 1 ν = 0 := by
  simp [maurerCartanU1, star_one]

@[simp]
lemma maurerCartanSU3_one (ν : Fin 1 ⊕ Fin 3) : maurerCartanSU3 1 ν = 0 := by
  ext i j
  simp [maurerCartanSU3, Matrix.map_apply, Matrix.one_apply, apply_ite (pderiv ℂ ν)]

@[simp]
lemma maurerCartanSU2_one (ν : Fin 1 ⊕ Fin 3) : maurerCartanSU2 1 ν = 0 := by
  ext i j
  simp [maurerCartanSU2, Matrix.map_apply, Matrix.one_apply, apply_ite (pderiv ℂ ν)]

lemma maurerCartanU1_mul (g1 g2 : JetGaugeGroupI) (ν : Fin 1 ⊕ Fin 3) :
    maurerCartanU1 (g1 * g2) ν = maurerCartanU1 g1 ν + maurerCartanU1 g2 ν := by
  have hcoe : ((g1 * g2).2.2 : JetRing) = (g1.2.2 : JetRing) * (g2.2.2 : JetRing) := rfl
  have h1 : (g1.2.2 : JetRing) * star (g1.2.2 : JetRing) = 1 :=
    (Unitary.mem_iff.mp g1.2.2.2).2
  have h2 : (g2.2.2 : JetRing) * star (g2.2.2 : JetRing) = 1 :=
    (Unitary.mem_iff.mp g2.2.2.2).2
  rw [maurerCartanU1, maurerCartanU1, maurerCartanU1, hcoe, Derivation.leibniz, star_mul']
  simp only [smul_eq_mul]
  linear_combination ((MvPowerSeries.C Complex.I : JetRing) *
      pderiv ℂ ν (g2.2.2 : JetRing) * star (g2.2.2 : JetRing)) * h1 +
    ((MvPowerSeries.C Complex.I : JetRing) *
      pderiv ℂ ν (g1.2.2 : JetRing) * star (g1.2.2 : JetRing)) * h2

/-- The cocycle law of the `SU(3)` Maurer–Cartan form: it is additive only up to
  conjugating the second factor's form by the first factor,
  `mc(UV) = mc(U) + U mc(V) U†`. -/
lemma maurerCartanSU3_mul (g1 g2 : JetGaugeGroupI) (ν : Fin 1 ⊕ Fin 3) :
    maurerCartanSU3 (g1 * g2) ν =
      maurerCartanSU3 g1 ν +
        (g1.1 : Matrix (Fin 3) (Fin 3) JetRing) * maurerCartanSU3 g2 ν *
          star (g1.1 : Matrix (Fin 3) (Fin 3) JetRing) := by
  have hcoe : ((g1 * g2).1 : Matrix (Fin 3) (Fin 3) JetRing) =
      (g1.1 : Matrix (Fin 3) (Fin 3) JetRing) * (g2.1 : Matrix (Fin 3) (Fin 3) JetRing) := rfl
  rw [maurerCartanSU3, maurerCartanSU3, maurerCartanSU3, hcoe]
  set U : Matrix (Fin 3) (Fin 3) JetRing := (g1.1 : Matrix (Fin 3) (Fin 3) JetRing)
  set V : Matrix (Fin 3) (Fin 3) JetRing := (g2.1 : Matrix (Fin 3) (Fin 3) JetRing)
  have hV : V * star V = 1 := by
    have h := (Matrix.mem_specialUnitaryGroup_iff.mp g2.1.2).1
    rwa [Matrix.mem_unitaryGroup_iff] at h
  have hleib : (U * V).map (pderiv ℂ ν) =
      U.map (pderiv ℂ ν) * V + U * V.map (pderiv ℂ ν) := by
    ext i j : 1
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum,
      Derivation.leibniz, smul_eq_mul]
    exact (Finset.sum_congr rfl fun k _ => by ring).trans Finset.sum_add_distrib
  rw [hleib, star_mul, Matrix.add_mul, smul_add]
  congr 1
  · rw [mul_assoc, ← mul_assoc V, hV, one_mul]
  · rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    rw [mul_assoc, ← mul_assoc (V.map (pderiv ℂ ν)), ← mul_assoc U]

lemma maurerCartanSU2_mul (g1 g2 : JetGaugeGroupI) (ν : Fin 1 ⊕ Fin 3) :
    maurerCartanSU2 (g1 * g2) ν =
      maurerCartanSU2 g1 ν + (g1.2.1 : Matrix (Fin 2) (Fin 2) JetRing) * maurerCartanSU2 g2 ν *
        star (g1.2.1 : Matrix (Fin 2) (Fin 2) JetRing) := by
  have hcoe : ((g1 * g2).2.1 : Matrix (Fin 2) (Fin 2) JetRing) =
      (g1.2.1 : Matrix (Fin 2) (Fin 2) JetRing) * (g2.2.1 : Matrix (Fin 2) (Fin 2) JetRing) := rfl
  rw [maurerCartanSU2, maurerCartanSU2, maurerCartanSU2, hcoe]
  set U : Matrix (Fin 2) (Fin 2) JetRing := (g1.2.1 : Matrix (Fin 2) (Fin 2) JetRing)
  set V : Matrix (Fin 2) (Fin 2) JetRing := (g2.2.1 : Matrix (Fin 2) (Fin 2) JetRing)
  have hV : V * star V = 1 := by
    have h := (Matrix.mem_specialUnitaryGroup_iff.mp g2.2.1.2).1
    rwa [Matrix.mem_unitaryGroup_iff] at h
  have hleib : (U * V).map (pderiv ℂ ν) =
      U.map (pderiv ℂ ν) * V + U * V.map (pderiv ℂ ν) := by
    ext i j : 1
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum,
      Derivation.leibniz, smul_eq_mul]
    exact (Finset.sum_congr rfl fun k _ => by ring).trans Finset.sum_add_distrib
  rw [hleib, star_mul, Matrix.add_mul, smul_add]
  congr 1
  · rw [mul_assoc, ← mul_assoc V, hV, one_mul]
  · rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    rw [mul_assoc, ← mul_assoc (V.map (pderiv ℂ ν)), ← mul_assoc U]


/-- The Maurer–Cartan series is hermitian: `star (i (∂_ν u) ū) = i (∂_ν u) ū`,
  by differentiating the unitarity relation `u ū = 1`. All its Taylor
  coefficients are therefore real. -/
lemma star_maurerCartanU1 (U : JetGaugeGroupI) (ν : Fin 1 ⊕ Fin 3) :
    star (maurerCartanU1 U ν) = maurerCartanU1 U ν := by
  have hu : (U.2.2 : JetRing) * star (U.2.2 : JetRing) = 1 := (Unitary.mem_iff.mp U.2.2.2).2
  have h0 : pderiv ℂ ν ((U.2.2 : JetRing) * star (U.2.2 : JetRing)) = 0 := by
    rw [hu, pderiv_one]
  rw [Derivation.leibniz] at h0
  simp only [smul_eq_mul] at h0
  have hq : pderiv ℂ ν (star (U.2.2 : JetRing)) * (U.2.2 : JetRing) =
      -(pderiv ℂ ν (U.2.2 : JetRing) * star (U.2.2 : JetRing)) := by
    linear_combination h0
  rw [maurerCartanU1, star_mul', JetRing.star_C, star_mul', star_star, ← JetRing.pderiv_star, hq,
    show (star Complex.I) = -Complex.I by simp, map_neg, neg_mul, mul_neg, neg_neg]

/-- The `SU(3)` Maurer–Cartan form is hermitian: `(i (∂_ν U) U†)† = i (∂_ν U) U†`,
  by differentiating the unitarity relation `U U† = 1` entrywise. -/
lemma star_maurerCartanSU3 (U : JetGaugeGroupI) (ν : Fin 1 ⊕ Fin 3) :
    star (maurerCartanSU3 U ν) = maurerCartanSU3 U ν := by
  rw [maurerCartanSU3]
  set A : Matrix (Fin 3) (Fin 3) JetRing := (U.1 : Matrix (Fin 3) (Fin 3) JetRing) with hA
  have hU : A * star A = 1 := by
    have h := (Matrix.mem_specialUnitaryGroup_iff.mp U.1.2).1
    rwa [Matrix.mem_unitaryGroup_iff] at h
  have hone : (1 : Matrix (Fin 3) (Fin 3) JetRing).map (pderiv ℂ ν) = 0 := by
    ext i j : 1
    simp [Matrix.map_apply, Matrix.one_apply, apply_ite (pderiv ℂ ν)]
  have hleib : (A * star A).map (pderiv ℂ ν) =
      A.map (pderiv ℂ ν) * star A + A * (star A).map (pderiv ℂ ν) := by
    ext i j : 1
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum,
      Derivation.leibniz, smul_eq_mul]
    exact (Finset.sum_congr rfl fun k _ => by ring).trans Finset.sum_add_distrib
  have h0 : A.map (pderiv ℂ ν) * star A + A * (star A).map (pderiv ℂ ν) = 0 := by
    rw [← hleib, hU, hone]
  have hq : A * ((star A).map (pderiv ℂ ν)) = -(A.map (pderiv ℂ ν) * star A) :=
    eq_neg_of_add_eq_zero_right h0
  have hstarmap : star (A.map (pderiv ℂ ν)) = (star A).map (pderiv ℂ ν) := by
    ext i j : 1
    simp only [Matrix.star_apply, Matrix.map_apply]
    exact (JetRing.pderiv_star ν (A j i)).symm
  rw [star_smul, star_mul, star_star, hstarmap, hq, JetRing.star_C,
    show (star Complex.I) = -Complex.I by simp, map_neg, neg_smul, smul_neg, neg_neg]

/-- The `SU(2)` Maurer–Cartan form is hermitian; see `star_maurerCartanSU3`. -/
lemma star_maurerCartanSU2 (U : JetGaugeGroupI) (ν : Fin 1 ⊕ Fin 3) :
    star (maurerCartanSU2 U ν) = maurerCartanSU2 U ν := by
  rw [maurerCartanSU2]
  set A : Matrix (Fin 2) (Fin 2) JetRing := (U.2.1 : Matrix (Fin 2) (Fin 2) JetRing) with hA
  have hU : A * star A = 1 := by
    have h := (Matrix.mem_specialUnitaryGroup_iff.mp U.2.1.2).1
    rwa [Matrix.mem_unitaryGroup_iff] at h
  have hone : (1 : Matrix (Fin 2) (Fin 2) JetRing).map (pderiv ℂ ν) = 0 := by
    ext i j : 1
    simp [Matrix.map_apply, Matrix.one_apply, apply_ite (pderiv ℂ ν)]
  have hleib : (A * star A).map (pderiv ℂ ν) =
      A.map (pderiv ℂ ν) * star A + A * (star A).map (pderiv ℂ ν) := by
    ext i j : 1
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum,
      Derivation.leibniz, smul_eq_mul]
    exact (Finset.sum_congr rfl fun k _ => by ring).trans Finset.sum_add_distrib
  have h0 : A.map (pderiv ℂ ν) * star A + A * (star A).map (pderiv ℂ ν) = 0 := by
    rw [← hleib, hU, hone]
  have hq : A * ((star A).map (pderiv ℂ ν)) = -(A.map (pderiv ℂ ν) * star A) :=
    eq_neg_of_add_eq_zero_right h0
  have hstarmap : star (A.map (pderiv ℂ ν)) = (star A).map (pderiv ℂ ν) := by
    ext i j : 1
    simp only [Matrix.star_apply, Matrix.map_apply]
    exact (JetRing.pderiv_star ν (A j i)).symm
  rw [star_smul, star_mul, star_star, hstarmap, hq, JetRing.star_C,
    show (star Complex.I) = -Complex.I by simp, map_neg, neg_smul, smul_neg, neg_neg]

/-!

### Derivatives of the Maurer–Cartan forms

-/

lemma pderiv_maurerCartanU1_symm (u : JetGaugeGroupI) (μ ν : Fin 1 ⊕ Fin 3) :
    pderiv ℂ μ (maurerCartanU1 u ν) = pderiv ℂ ν (maurerCartanU1 u μ) := by
  have hu : (u.2.2 : JetRing) * star (u.2.2 : JetRing) = 1 := (Unitary.mem_iff.mp u.2.2.2).2
  have hu' : star (u.2.2 : JetRing) * (u.2.2 : JetRing) = 1 := (Unitary.mem_iff.mp u.2.2.2).1
  have hstar : ∀ ρ : Fin 1 ⊕ Fin 3, pderiv ℂ ρ (star (u.2.2 : JetRing)) =
      -(star (u.2.2 : JetRing) * pderiv ℂ ρ (u.2.2 : JetRing) * star (u.2.2 : JetRing)) := by
    intro ρ
    have h0 : pderiv ℂ ρ ((u.2.2 : JetRing) * star (u.2.2 : JetRing)) = 0 := by
      rw [hu, pderiv_one]
    rw [Derivation.leibniz] at h0
    simp only [smul_eq_mul] at h0
    linear_combination star (u.2.2 : JetRing) * h0 -
      (pderiv ℂ ρ (star (u.2.2 : JetRing))) * hu'
  simp only [maurerCartanU1, Derivation.leibniz, pderiv_C, smul_eq_mul, mul_zero, add_zero]
  rw [hstar μ, hstar ν, JetRing.pderiv_comm μ ν]
  ring

/-- The Maurer–Cartan structure equation for the `SU(3)` form: the antisymmetrized
  derivative is the commutator, `∂_μ mc_ν - ∂_ν mc_μ = -i [mc_μ, mc_ν]`, here
  stated additively. In the abelian `U(1)` case the commutator vanishes and this
  reduces to `pderiv_maurerCartanU1_symm`. -/
lemma pderiv_maurerCartanSU3_symm (u : JetGaugeGroupI) (μ ν : Fin 1 ⊕ Fin 3) :
    (maurerCartanSU3 u ν).map (pderiv ℂ μ) +
        (MvPowerSeries.C Complex.I : JetRing) • (maurerCartanSU3 u μ * maurerCartanSU3 u ν) =
      (maurerCartanSU3 u μ).map (pderiv ℂ ν) +
        (MvPowerSeries.C Complex.I : JetRing) • (maurerCartanSU3 u ν * maurerCartanSU3 u μ) := by
  simp only [maurerCartanSU3]
  set U : Matrix (Fin 3) (Fin 3) JetRing := (u.1 : Matrix (Fin 3) (Fin 3) JetRing)
  have hU : U * star U = 1 := by
    have h := (Matrix.mem_specialUnitaryGroup_iff.mp u.1.2).1
    rwa [Matrix.mem_unitaryGroup_iff] at h
  have hU' : star U * U = 1 := by
    have h := (Matrix.mem_specialUnitaryGroup_iff.mp u.1.2).1
    rwa [Matrix.mem_unitaryGroup_iff'] at h
  have hone : ∀ ρ : Fin 1 ⊕ Fin 3,
      (1 : Matrix (Fin 3) (Fin 3) JetRing).map (pderiv ℂ ρ) = 0 := by
    intro ρ
    ext i j : 1
    simp [Matrix.map_apply, Matrix.one_apply, apply_ite (pderiv ℂ ρ)]
  have hleib : ∀ (ρ : Fin 1 ⊕ Fin 3) (A B : Matrix (Fin 3) (Fin 3) JetRing),
      (A * B).map (pderiv ℂ ρ) = A.map (pderiv ℂ ρ) * B + A * B.map (pderiv ℂ ρ) := by
    intro ρ A B
    ext i j : 1
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum,
      Derivation.leibniz, smul_eq_mul]
    exact (Finset.sum_congr rfl fun k _ => by ring).trans Finset.sum_add_distrib
  have hstar : ∀ ρ : Fin 1 ⊕ Fin 3, (star U).map (pderiv ℂ ρ) =
      -(star U * (U.map (pderiv ℂ ρ) * star U)) := by
    intro ρ
    have h0 : U.map (pderiv ℂ ρ) * star U + U * (star U).map (pderiv ℂ ρ) = 0 := by
      rw [← hleib ρ U (star U), hU, hone]
    have h1 : star U * (U.map (pderiv ℂ ρ) * star U) +
        star U * (U * (star U).map (pderiv ℂ ρ)) = 0 := by
      rw [← Matrix.mul_add, h0, mul_zero]
    rw [show star U * (U * (star U).map (pderiv ℂ ρ)) =
        star U * U * (star U).map (pderiv ℂ ρ) from (mul_assoc _ _ _).symm, hU', one_mul] at h1
    exact eq_neg_of_add_eq_zero_right h1
  have hCsmul : ∀ (ρ : Fin 1 ⊕ Fin 3) (A : Matrix (Fin 3) (Fin 3) JetRing),
      ((MvPowerSeries.C Complex.I : JetRing) • A).map (pderiv ℂ ρ) =
        (MvPowerSeries.C Complex.I : JetRing) • A.map (pderiv ℂ ρ) := by
    intro ρ A
    ext i j : 1
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Derivation.leibniz,
      pderiv_C, mul_zero, add_zero]
  have hDcomm : (U.map (pderiv ℂ ν)).map (pderiv ℂ μ) =
      (U.map (pderiv ℂ μ)).map (pderiv ℂ ν) := by
    ext i j : 1
    simp only [Matrix.map_apply]
    exact JetRing.pderiv_comm μ ν (U i j)
  have hI : (MvPowerSeries.C Complex.I : JetRing) * MvPowerSeries.C Complex.I = -1 := by
    rw [← map_mul, Complex.I_mul_I, map_neg, map_one]
  have hprod : ∀ (X Y : Matrix (Fin 3) (Fin 3) JetRing),
      (MvPowerSeries.C Complex.I : JetRing) •
          (((MvPowerSeries.C Complex.I : JetRing) • X) *
            ((MvPowerSeries.C Complex.I : JetRing) • Y)) =
        -((MvPowerSeries.C Complex.I : JetRing) • (X * Y)) := by
    intro X Y
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, smul_smul, hI, neg_one_mul, neg_smul]
  rw [hCsmul μ, hCsmul ν, hleib μ (U.map (pderiv ℂ ν)) (star U),
    hleib ν (U.map (pderiv ℂ μ)) (star U), hstar μ, hstar ν, hDcomm, hprod, hprod]
  simp only [mul_neg, smul_add, smul_neg, mul_assoc]
  abel

/-- The Maurer–Cartan structure equation for the `SU(2)` form; see
  `pderiv_maurerCartanSU3_symm`. -/
lemma pderiv_maurerCartanSU2_symm (u : JetGaugeGroupI) (μ ν : Fin 1 ⊕ Fin 3) :
    (maurerCartanSU2 u ν).map (pderiv ℂ μ) +
        (MvPowerSeries.C Complex.I : JetRing) • (maurerCartanSU2 u μ * maurerCartanSU2 u ν) =
      (maurerCartanSU2 u μ).map (pderiv ℂ ν) +
        (MvPowerSeries.C Complex.I : JetRing) • (maurerCartanSU2 u ν * maurerCartanSU2 u μ) := by
  simp only [maurerCartanSU2]
  set U : Matrix (Fin 2) (Fin 2) JetRing := (u.2.1 : Matrix (Fin 2) (Fin 2) JetRing)
  have hU : U * star U = 1 := by
    have h := (Matrix.mem_specialUnitaryGroup_iff.mp u.2.1.2).1
    rwa [Matrix.mem_unitaryGroup_iff] at h
  have hU' : star U * U = 1 := by
    have h := (Matrix.mem_specialUnitaryGroup_iff.mp u.2.1.2).1
    rwa [Matrix.mem_unitaryGroup_iff'] at h
  have hone : ∀ ρ : Fin 1 ⊕ Fin 3,
      (1 : Matrix (Fin 2) (Fin 2) JetRing).map (pderiv ℂ ρ) = 0 := by
    intro ρ
    ext i j : 1
    simp [Matrix.map_apply, Matrix.one_apply, apply_ite (pderiv ℂ ρ)]
  have hleib : ∀ (ρ : Fin 1 ⊕ Fin 3) (A B : Matrix (Fin 2) (Fin 2) JetRing),
      (A * B).map (pderiv ℂ ρ) = A.map (pderiv ℂ ρ) * B + A * B.map (pderiv ℂ ρ) := by
    intro ρ A B
    ext i j : 1
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum,
      Derivation.leibniz, smul_eq_mul]
    exact (Finset.sum_congr rfl fun k _ => by ring).trans Finset.sum_add_distrib
  have hstar : ∀ ρ : Fin 1 ⊕ Fin 3, (star U).map (pderiv ℂ ρ) =
      -(star U * (U.map (pderiv ℂ ρ) * star U)) := by
    intro ρ
    have h0 : U.map (pderiv ℂ ρ) * star U + U * (star U).map (pderiv ℂ ρ) = 0 := by
      rw [← hleib ρ U (star U), hU, hone]
    have h1 : star U * (U.map (pderiv ℂ ρ) * star U) +
        star U * (U * (star U).map (pderiv ℂ ρ)) = 0 := by
      rw [← Matrix.mul_add, h0, mul_zero]
    rw [show star U * (U * (star U).map (pderiv ℂ ρ)) =
        star U * U * (star U).map (pderiv ℂ ρ) from (mul_assoc _ _ _).symm, hU', one_mul] at h1
    exact eq_neg_of_add_eq_zero_right h1
  have hCsmul : ∀ (ρ : Fin 1 ⊕ Fin 3) (A : Matrix (Fin 2) (Fin 2) JetRing),
      ((MvPowerSeries.C Complex.I : JetRing) • A).map (pderiv ℂ ρ) =
        (MvPowerSeries.C Complex.I : JetRing) • A.map (pderiv ℂ ρ) := by
    intro ρ A
    ext i j : 1
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Derivation.leibniz,
      pderiv_C, mul_zero, add_zero]
  have hDcomm : (U.map (pderiv ℂ ν)).map (pderiv ℂ μ) =
      (U.map (pderiv ℂ μ)).map (pderiv ℂ ν) := by
    ext i j : 1
    simp only [Matrix.map_apply]
    exact JetRing.pderiv_comm μ ν (U i j)
  have hI : (MvPowerSeries.C Complex.I : JetRing) * MvPowerSeries.C Complex.I = -1 := by
    rw [← map_mul, Complex.I_mul_I, map_neg, map_one]
  have hprod : ∀ (X Y : Matrix (Fin 2) (Fin 2) JetRing),
      (MvPowerSeries.C Complex.I : JetRing) •
          (((MvPowerSeries.C Complex.I : JetRing) • X) *
            ((MvPowerSeries.C Complex.I : JetRing) • Y)) =
        -((MvPowerSeries.C Complex.I : JetRing) • (X * Y)) := by
    intro X Y
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, smul_smul, hI, neg_one_mul, neg_smul]
  rw [hCsmul μ, hCsmul ν, hleib μ (U.map (pderiv ℂ ν)) (star U),
    hleib ν (U.map (pderiv ℂ μ)) (star U), hstar μ, hstar ν, hDcomm, hprod, hprod]
  simp only [mul_neg, smul_add, smul_neg, mul_assoc]
  abel

end StandardModel
