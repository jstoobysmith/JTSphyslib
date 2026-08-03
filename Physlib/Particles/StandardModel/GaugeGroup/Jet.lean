/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Physlib.Relativity.Tensors.ComplexTensor.Vector.Pre.Basic
/-!

# The jet gauge group

## i. Overview

The essential idea is that at a point `x` in spacetime,
a gauge transformation on fields at `x` and their derivatives
is determined by the gauge transformation
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

/-- The first-order power rule: the degree-one Taylor coefficient, in the direction
  `μ`, of a power of a power series. -/
lemma coeff_single_one_pow [CommRing R] (μ : σ) (f : MvPowerSeries σ R) (n : ℕ) :
    coeff (Finsupp.single μ 1) (f ^ n) =
      (n : R) * constantCoeff f ^ (n - 1) * coeff (Finsupp.single μ 1) f := by
  classical
  induction n with
  | zero =>
      simp [coeff_one, Finsupp.single_eq_zero]
  | succ n ih =>
      rw [pow_succ, coeff_single_one_mul, ih, map_pow, Nat.add_sub_cancel]
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp
      · have hpow : constantCoeff f ^ (n - 1) * constantCoeff f = constantCoeff f ^ n := by
          rw [← pow_succ, Nat.sub_add_cancel hn]
        push_cast
        linear_combination ((n : R) * coeff (Finsupp.single μ 1) f) * hpow

end MvPowerSeries

namespace Module.Basis

variable {R M κ : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The basis vector of the symmetric algebra at the zero multi-index is the unit
  of the algebra. -/
lemma symmetricAlgebra_zero (b : Module.Basis κ R M) :
    b.symmetricAlgebra (0 : κ →₀ ℕ) = 1 := by
  have h : (MvPolynomial.basisMonomials κ R) (0 : κ →₀ ℕ) = 1 := by
    rw [MvPolynomial.coe_basisMonomials]
    simp [MvPolynomial.monomial_zero']
  rw [symmetricAlgebra, map_apply, h]
  simp

/-- The basis vector of the symmetric algebra at a single multi-index is the
  corresponding generator. -/
lemma symmetricAlgebra_single (b : Module.Basis κ R M) (i : κ) :
    b.symmetricAlgebra (Finsupp.single i 1) = SymmetricAlgebra.ι R M (b i) := by
  have h : (MvPolynomial.basisMonomials κ R) (Finsupp.single i 1) = MvPolynomial.X i := rfl
  rw [symmetricAlgebra, map_apply, h]
  simp

end Module.Basis

namespace StandardModel

open Matrix MvPowerSeries
open scoped Nat

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

/-!

## F. The derivative action on the symmetric algebra

The polynomial jet spaces of `LagrangianTheory` are built on the symmetric algebra
`SymmetricAlgebra ℂ Lorentz.CoℂModule`, whose multiset monomials are the commuting
derivative symbols `∂_m`. The jet ring pairs with this algebra by the
divided-power duality `⟨∂_m, f⟩ = m! · coeff m f` (the constant-coefficient
operator `∂_m` applied to `f`, evaluated at the base point).

Through this pairing a jet `χ : JetRing` acts on the symmetric algebra as the
transpose of multiplication by `χ`, which is the infinite-order
constant-coefficient differential operator `χ(∂)`. On the derivative symbol `∂_m`
it acts by `∂_m ↦ ∑_{k + l = m} (m.descFactorial k) · (coeff k χ) · ∂_l`: the
Leibniz rule for how the derivatives of a field pick up derivatives of the gauge
parameter, e.g. `∂_μ ↦ χ(0) ∂_μ + (∂_μ χ)(0) ∂_∅`. Because the jet ring is
commutative, transposition preserves multiplicativity, so `χ ↦ χ(∂)` is
multiplicative; this is proved via adjointness and nondegeneracy of the pairing.

-/

/-- The divided-power pairing between the symmetric algebra of covectors (the
  algebra of derivative symbols) and the jet ring: on the monomial `∂_m` it is
  `f ↦ m! · coeff m f`. -/
noncomputable def symPairing :
    SymmetricAlgebra ℂ Lorentz.CoℂModule →ₗ[ℂ] JetRing →ₗ[ℂ] ℂ :=
  Lorentz.complexCoBasis.symmetricAlgebra.constr ℂ fun m =>
    (∏ μ, (m μ)! : ℕ) • MvPowerSeries.coeff m

@[simp]
lemma symPairing_basis (m : (Fin 1 ⊕ Fin 3) →₀ ℕ) (f : JetRing) :
    symPairing (Lorentz.complexCoBasis.symmetricAlgebra m) f =
      (∏ μ, (m μ)! : ℕ) • MvPowerSeries.coeff m f := by
  rw [symPairing, Module.Basis.constr_basis]
  rfl

/-- The pairing of an element of the symmetric algebra with a monomial extracts the
  corresponding basis coordinate, weighted by the factorial. -/
lemma symPairing_monomial (p : SymmetricAlgebra ℂ Lorentz.CoℂModule)
    (m : (Fin 1 ⊕ Fin 3) →₀ ℕ) :
    symPairing p (MvPowerSeries.monomial m 1) =
      ((∏ μ, (m μ)! : ℕ) : ℂ) * Lorentz.complexCoBasis.symmetricAlgebra.repr p m := by
  classical
  rw [symPairing, Module.Basis.constr_apply, Finsupp.sum, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, MvPowerSeries.coeff_monomial]
  rw [Finset.sum_eq_single m]
  · by_cases hm : m ∈ (Lorentz.complexCoBasis.symmetricAlgebra.repr p).support
    · simp [mul_comm]
    · rw [Finsupp.notMem_support_iff.mp hm]
      simp
  · intro i _ hi
    simp [hi]
  · intro hm
    rw [Finsupp.notMem_support_iff.mp hm]
    simp

/-- Two elements of the symmetric algebra pairing equally against every jet are
  equal: the divided-power pairing is nondegenerate on the symmetric-algebra side
  (the factorials are invertible in characteristic zero). -/
lemma symPairing_injective {p q : SymmetricAlgebra ℂ Lorentz.CoℂModule}
    (h : ∀ f, symPairing p f = symPairing q f) : p = q := by
  refine Lorentz.complexCoBasis.symmetricAlgebra.ext_elem fun m => ?_
  have hf := h (MvPowerSeries.monomial m 1)
  rw [symPairing_monomial, symPairing_monomial] at hf
  have hfac : ((∏ μ, (m μ)! : ℕ) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun μ _ => Nat.factorial_ne_zero (m μ)
  exact mul_left_cancel₀ hfac hf

/-- The action of a jet `χ` on the algebra of derivative symbols: the transpose of
  multiplication by `χ` under the divided-power pairing, i.e. the constant
  coefficient differential operator `χ(∂)`. On the derivative symbol `∂_m` it is
  `∑_{k + l = m} (m.descFactorial k) · (coeff k χ) · ∂_l`, the Leibniz rule; for
  example `∂_μ ↦ χ(0) ∂_μ + (∂_μχ)(0) ∂_∅`. -/
noncomputable def derivAction (χ : JetRing) :
    SymmetricAlgebra ℂ Lorentz.CoℂModule →ₗ[ℂ] SymmetricAlgebra ℂ Lorentz.CoℂModule :=
  Lorentz.complexCoBasis.symmetricAlgebra.constr ℂ fun m =>
    ∑ p ∈ Finset.antidiagonal m,
      ((∏ μ, (m μ).descFactorial (p.1 μ) : ℕ) : ℂ) • MvPowerSeries.coeff p.1 χ •
        Lorentz.complexCoBasis.symmetricAlgebra p.2

/-- Adjointness: the derivative action of `χ` is the transpose of multiplication by
  `χ` under the divided-power pairing. This is the coefficient-level statement of
  the Leibniz rule. -/
lemma symPairing_derivAction (χ f : JetRing) (p : SymmetricAlgebra ℂ Lorentz.CoℂModule) :
    symPairing (derivAction χ p) f = symPairing p (χ * f) := by
  classical
  have h : (symPairing.flip f) ∘ₗ derivAction χ = symPairing.flip (χ * f) := by
    refine Lorentz.complexCoBasis.symmetricAlgebra.ext fun m => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply]
    rw [derivAction, Module.Basis.constr_basis]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      symPairing_basis, smul_eq_mul, nsmul_eq_mul]
    rw [MvPowerSeries.coeff_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hm : q.1 + q.2 = m := Finset.mem_antidiagonal.mp hq
    have hfac : ((∏ μ, (m μ).descFactorial (q.1 μ) : ℕ) : ℂ) *
        ((∏ μ, (q.2 μ)! : ℕ) : ℂ) = ((∏ μ, (m μ)! : ℕ) : ℂ) := by
      rw [← Nat.cast_mul, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun μ _ => ?_
      rw [mul_comm]
      have h1 : q.1 μ ≤ m μ := by
        rw [← hm]; simp
      have h2 : m μ - q.1 μ = q.2 μ := by
        rw [← hm]; simp
      rw [← h2]
      exact Nat.factorial_mul_descFactorial h1
    rw [← hfac]
    ring
  exact LinearMap.congr_fun h p

/-- Constant jets act on the derivative symbols by their value: `C c` has no
  derivative coordinates. -/
@[simp]
lemma derivAction_C (c : ℂ) :
    derivAction (MvPowerSeries.C c) = c • LinearMap.id := by
  refine LinearMap.ext fun p => symPairing_injective fun f => ?_
  rw [symPairing_derivAction,
    show (MvPowerSeries.C c : JetRing) * f = c • f from
      (algebraMap_smul JetRing c f).symm ▸ (Algebra.smul_def c f).symm]
  simp

@[simp]
lemma derivAction_one : derivAction (1 : JetRing) = LinearMap.id := by
  rw [show (1 : JetRing) = MvPowerSeries.C 1 from (map_one _).symm, derivAction_C, one_smul]

/-- The derivative action is multiplicative: it is the transpose of multiplication
  in the commutative jet ring. This makes `χ ↦ χ(∂)` a monoid homomorphism and
  hence yields representations of the jet gauge group on polynomial jet spaces. -/
lemma derivAction_mul (χ ψ : JetRing) :
    derivAction (χ * ψ) = derivAction χ ∘ₗ derivAction ψ := by
  refine LinearMap.ext fun p => symPairing_injective fun f => ?_
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [symPairing_derivAction, symPairing_derivAction, symPairing_derivAction]
  ring_nf

@[simp]
lemma derivAction_zero : derivAction (0 : JetRing) = 0 := by
  refine LinearMap.ext fun p => symPairing_injective fun f => ?_
  rw [symPairing_derivAction, zero_mul]
  simp

lemma derivAction_add (χ ψ : JetRing) :
    derivAction (χ + ψ) = derivAction χ + derivAction ψ := by
  refine LinearMap.ext fun p => symPairing_injective fun f => ?_
  simp only [LinearMap.add_apply, map_add, symPairing_derivAction]
  rw [add_mul, map_add]

/-- The derivative action as a ring homomorphism from the jet ring to the
  endomorphisms of the algebra of derivative symbols: the module structure of the
  jet ring on its graded dual. -/
noncomputable def derivActionHom :
    JetRing →+* Module.End ℂ (SymmetricAlgebra ℂ Lorentz.CoℂModule) where
  toFun := derivAction
  map_one' := derivAction_one
  map_mul' χ ψ := derivAction_mul χ ψ
  map_zero' := derivAction_zero
  map_add' := derivAction_add

/-- The derivative action on the zeroth-order (field) symbol: it is scaled by the
  value of the jet at the base point. -/
@[simp]
lemma derivAction_apply_one (χ : JetRing) :
    derivAction χ (1 : SymmetricAlgebra ℂ Lorentz.CoℂModule) =
      MvPowerSeries.constantCoeff χ • 1 := by
  rw [show (1 : SymmetricAlgebra ℂ Lorentz.CoℂModule) =
      Lorentz.complexCoBasis.symmetricAlgebra 0 from
      (Lorentz.complexCoBasis.symmetricAlgebra_zero).symm,
    derivAction, Module.Basis.constr_basis, Finsupp.antidiagonal_zero, Finset.sum_singleton]
  simp

/-- The derivative action on a first-order derivative symbol implements the Leibniz
  rule: `∂_μ ↦ χ(0) ∂_μ + (∂_μχ)(0) 1`. The value of the jet multiplies the
  first-derivative symbol, and its first derivative feeds the zeroth-order
  symbol. -/
lemma derivAction_apply_ι (χ : JetRing) (μ : Fin 1 ⊕ Fin 3) :
    derivAction χ (SymmetricAlgebra.ι ℂ Lorentz.CoℂModule (Lorentz.complexCoBasis μ)) =
      MvPowerSeries.constantCoeff χ •
        SymmetricAlgebra.ι ℂ Lorentz.CoℂModule (Lorentz.complexCoBasis μ) +
        MvPowerSeries.coeff (Finsupp.single μ 1) χ • 1 := by
  classical
  rw [show SymmetricAlgebra.ι ℂ Lorentz.CoℂModule (Lorentz.complexCoBasis μ) =
      Lorentz.complexCoBasis.symmetricAlgebra (Finsupp.single μ 1) from
      (Lorentz.complexCoBasis.symmetricAlgebra_single μ).symm,
    derivAction, Module.Basis.constr_basis, Finsupp.antidiagonal_single,
    show Finset.antidiagonal (1 : ℕ) = {(0, 1), (1, 0)} by decide, Finset.map_insert,
    Finset.map_singleton, Finset.sum_insert (by simp [Finsupp.single_eq_zero]),
    Finset.sum_singleton]
  have h1 : (∏ ν, ((Finsupp.single μ 1) ν).descFactorial ((Finsupp.single μ 1) ν)) = 1 :=
    Finset.prod_eq_one fun ν _ => by
      rcases eq_or_ne μ ν with h | h
      · subst h; simp
      · simp [h]
  simp only [Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk, Prod.map_apply,
    Finsupp.single_zero, Finsupp.coe_zero, Pi.zero_apply, Nat.descFactorial_zero,
    Finset.prod_const_one, Nat.cast_one, one_smul, coeff_zero_eq_constantCoeff, h1,
    Lorentz.complexCoBasis.symmetricAlgebra_single, Lorentz.complexCoBasis.symmetricAlgebra_zero]

end StandardModel
