/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
/-!

# The jet gauge group

## i. Overview

This file defines the group of formal infinite-order jets, at a spacetime point, of
local gauge transformations of the Standard Model.

A local gauge transformation is a map from spacetime into the gauge group. Its
infinite-order jet at a point is the collection of all its Taylor coefficients
there, which, by Borel's theorem, is exactly a formal power series in the spacetime
coordinates. Since gauge transformations multiply pointwise, jets multiply as
(truncated) power series, with the Leibniz rule handled automatically by the
power-series product.

This leads to a purely algebraic definition: the jet gauge group is the group of
`R`-points of the gauge group, where `R` is the commutative ring of formal power
series in the spacetime coordinates with complex coefficients. Concretely, an
element of the `SU(3)` factor is a `3 × 3` matrix of power series `U` satisfying
`U * Uᴴ = 1` and `det U = 1` as power series, which encodes the unitarity and
determinant constraints at every jet order simultaneously.

The star operation on the power-series ring is coefficientwise complex conjugation,
so that the spacetime coordinates themselves are self-adjoint (they are real
coordinates); this star structure is defined in section A below and is not currently
in Mathlib.

Evaluation of power series at the base point (the constant coefficient) gives a
group homomorphism from the jet gauge group to the gauge group `GaugeGroupI`,
projecting a jet to its zeroth-order part; conversely the constant power series give
an embedding of `GaugeGroupI` into the jet gauge group as the jets of constant
(global) gauge transformations.

-/

@[expose] public section

/-!

## A. The star structure on multivariate power series

The star operation on `MvPowerSeries σ R` is coefficientwise star. In particular
over `ℂ` it is coefficientwise complex conjugation, fixing the formal variables.

-/

namespace MvPowerSeries

variable {σ R : Type*}

instance [Star R] : Star (MvPowerSeries σ R) where
  star f := fun n => star (f n)

@[simp]
lemma coeff_star [Semiring R] [StarRing R] (n : σ →₀ ℕ) (f : MvPowerSeries σ R) :
    coeff n (star f) = star (coeff n f) := rfl

instance [CommSemiring R] [StarRing R] : StarRing (MvPowerSeries σ R) where
  star_involutive f := funext fun n => star_star (f n)
  star_add f g := funext fun n => star_add (f n) (g n)
  star_mul f g := by
    have h : ∀ a b : MvPowerSeries σ R, star (a * b) = star a * star b := by
      intro a b
      ext n
      classical
      rw [coeff_star, coeff_mul, coeff_mul, star_sum]
      exact Finset.sum_congr rfl fun p _ => by rw [star_mul', coeff_star, coeff_star]
    rw [h, mul_comm]

@[simp]
lemma constantCoeff_star [CommSemiring R] [StarRing R] (f : MvPowerSeries σ R) :
    constantCoeff (star f) = star (constantCoeff f) := rfl

@[simp]
lemma star_C [CommSemiring R] [StarRing R] (a : R) :
    star (C (σ := σ) a) = C (star a) := by
  ext n
  classical
  rw [coeff_star, coeff_C, coeff_C]
  split_ifs <;> simp

/-- The first-order Leibniz rule: the degree-one Taylor coefficient, in the
  direction `μ`, of a product of power series. This is the coefficient-level
  statement that the first jet of a product is given by the product rule. -/
lemma coeff_single_one_mul [CommSemiring R] (μ : σ) (f g : MvPowerSeries σ R) :
    coeff (Finsupp.single μ 1) (f * g) =
      coeff (Finsupp.single μ 1) f * constantCoeff g +
        constantCoeff f * coeff (Finsupp.single μ 1) g := by
  classical
  rw [coeff_mul, Finsupp.antidiagonal_single,
    show Finset.antidiagonal (1 : ℕ) = {(0, 1), (1, 0)} by decide, Finset.map_insert,
    Finset.map_singleton, Finset.sum_insert (by simp [Finsupp.single_eq_zero]),
    Finset.sum_singleton]
  simp only [Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk, Prod.map_apply,
    Finsupp.single_zero, coeff_zero_eq_constantCoeff]
  ring

end MvPowerSeries

namespace StandardModel

open Matrix MvPowerSeries

/-!

## B. The jet ring

-/

/-- The ring of formal power series in the four spacetime coordinates, with complex
  coefficients. Jets of fields and of gauge transformations at a spacetime point are
  valued in this ring. The star operation is coefficientwise complex conjugation, so
  the spacetime coordinates themselves are self-adjoint. -/
abbrev JetRing : Type := MvPowerSeries (Fin 1 ⊕ Fin 3) ℂ

/-!

## C. The jet gauge group

-/

/-- The group of formal infinite-order jets, at a spacetime point, of local gauge
  transformations of the Standard Model: the `R`-points of the gauge group for `R`
  the ring `JetRing` of formal power series in the spacetime coordinates.

  Since gauge transformations multiply pointwise, jets multiply as power series and
  the group structure is that of the matrix groups over `JetRing`. The unitarity and
  determinant constraints hold as power-series identities, i.e. at every jet order.

  Evaluation at the base point recovers `GaugeGroupI`; see `JetGaugeGroupI.eval`. -/
abbrev JetGaugeGroupI : Type :=
  specialUnitaryGroup (Fin 3) JetRing × specialUnitaryGroup (Fin 2) JetRing ×
  unitary JetRing

namespace JetGaugeGroupI

/-!

## D. Evaluation at the base point

The constant coefficient of a power series is its value at the base point of the
jet. Applied entrywise it sends jets of gauge transformations to their zeroth-order
parts, giving a group homomorphism `JetGaugeGroupI →* GaugeGroupI`.

-/

/-- Entrywise evaluation at the base point commutes with the conjugate transpose. -/
lemma mapMatrix_constantCoeff_star {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n JetRing) :
    (constantCoeff : JetRing →+* ℂ).mapMatrix (star A) =
      star ((constantCoeff : JetRing →+* ℂ).mapMatrix A) := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.star_apply]

/-- Evaluation of a jet of a special-unitary gauge transformation at the base point:
  the entrywise constant coefficient. -/
noncomputable def evalSU (n : Type) [Fintype n] [DecidableEq n] :
    specialUnitaryGroup n JetRing →* specialUnitaryGroup n ℂ where
  toFun U := ⟨(constantCoeff : JetRing →+* ℂ).mapMatrix U.1, by
    obtain ⟨h1, h2⟩ := mem_specialUnitaryGroup_iff.mp U.2
    rw [mem_specialUnitaryGroup_iff]
    constructor
    · rw [mem_unitaryGroup_iff] at h1 ⊢
      rw [show star ((constantCoeff : JetRing →+* ℂ).mapMatrix U.1) =
          (constantCoeff : JetRing →+* ℂ).mapMatrix (star U.1) from
          (mapMatrix_constantCoeff_star U.1).symm, ← map_mul, h1, map_one]
    · rw [← RingHom.map_det, h2, map_one]⟩
  map_one' := Subtype.ext (map_one ((constantCoeff : JetRing →+* ℂ).mapMatrix))
  map_mul' U V := Subtype.ext (map_mul ((constantCoeff : JetRing →+* ℂ).mapMatrix) U.1 V.1)

/-- Evaluation of a jet of a `U(1)` gauge transformation at the base point: the
  constant coefficient. -/
noncomputable def evalU1 : unitary JetRing →* unitary ℂ where
  toFun u := ⟨constantCoeff u.1, by
    obtain ⟨h1, h2⟩ := Unitary.mem_iff.mp u.2
    exact Unitary.mem_iff.mpr
      ⟨by rw [← constantCoeff_star, ← map_mul, h1, map_one],
        by rw [← constantCoeff_star, ← map_mul, h2, map_one]⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' u v := Subtype.ext (map_mul _ u.1 v.1)

/-- Evaluation of a jet of a gauge transformation at the base point, projecting the
  jet gauge group onto the gauge group `GaugeGroupI` by taking zeroth-order parts on
  each factor. -/
noncomputable def eval : JetGaugeGroupI →* GaugeGroupI :=
  (evalSU (Fin 3)).prodMap ((evalSU (Fin 2)).prodMap evalU1)

/-!

## E. Constant jets

The constant power series embed the gauge group `GaugeGroupI` into the jet gauge
group, as the jets of constant (global) gauge transformations. This is a section of
the evaluation `eval`.

-/

/-- Entrywise inclusion of constants commutes with the conjugate transpose. -/
lemma mapMatrix_C_star {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    (C : ℂ →+* JetRing).mapMatrix (star A) = star ((C : ℂ →+* JetRing).mapMatrix A) := by
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.star_apply]

/-- The jet of a constant special-unitary gauge transformation: the entrywise
  inclusion of constants. -/
noncomputable def ofConstantSU (n : Type) [Fintype n] [DecidableEq n] :
    specialUnitaryGroup n ℂ →* specialUnitaryGroup n JetRing where
  toFun u := ⟨(C : ℂ →+* JetRing).mapMatrix u.1, by
    obtain ⟨h1, h2⟩ := mem_specialUnitaryGroup_iff.mp u.2
    rw [mem_specialUnitaryGroup_iff]
    constructor
    · rw [mem_unitaryGroup_iff] at h1 ⊢
      rw [show star ((C : ℂ →+* JetRing).mapMatrix u.1) =
          (C : ℂ →+* JetRing).mapMatrix (star u.1) from (mapMatrix_C_star u.1).symm,
        ← map_mul, h1, map_one]
    · rw [← RingHom.map_det, h2, map_one]⟩
  map_one' := Subtype.ext (map_one ((C : ℂ →+* JetRing).mapMatrix))
  map_mul' u v := Subtype.ext (map_mul ((C : ℂ →+* JetRing).mapMatrix) u.1 v.1)

/-- The jet of a constant `U(1)` gauge transformation: the inclusion of constants. -/
noncomputable def ofConstantU1 : unitary ℂ →* unitary JetRing where
  toFun u := ⟨C u.1, by
    obtain ⟨h1, h2⟩ := Unitary.mem_iff.mp u.2
    exact Unitary.mem_iff.mpr
      ⟨by rw [star_C, ← map_mul, h1, map_one],
        by rw [star_C, ← map_mul, h2, map_one]⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' u v := Subtype.ext (map_mul _ u.1 v.1)

/-- The embedding of the gauge group into the jet gauge group as the jets of
  constant (global) gauge transformations. -/
noncomputable def ofConstant : GaugeGroupI →* JetGaugeGroupI :=
  (ofConstantSU (Fin 3)).prodMap ((ofConstantSU (Fin 2)).prodMap ofConstantU1)

/-- Evaluating the jet of a constant gauge transformation at the base point recovers
  the gauge transformation: `ofConstant` is a section of `eval`. -/
@[simp]
lemma eval_ofConstant (g : GaugeGroupI) : eval (ofConstant g) = g := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
  · ext i j
    simp [eval, ofConstant, evalSU, ofConstantSU,
      RingHom.mapMatrix_apply, Matrix.map_apply]
  · ext i j
    simp [eval, ofConstant, evalSU, ofConstantSU,
      RingHom.mapMatrix_apply, Matrix.map_apply]
  · simp [eval, ofConstant, evalU1, ofConstantU1]



end JetGaugeGroupI

end StandardModel
