/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.IsInvariant
public import Physlib.Relativity.MinkowskiMatrix
public import Physlib.Relativity.PauliMatrices.Basic
public import Physlib.Particles.StandardModel.GaugeBosons.BBoson.MassDim
public import Physlib.Mathematics.PolynomialEval
/-!
# Mass dimension on the lepton–gauge-sector jet algebra

*Note*: In this file we use the notion 'mass weight'. The idea been that the
'mass weight' is twice the mass dimension. This is because it is easier to work exclusively with
integers, and the mass dimension of the fermion fields is 3/2.

The grading is carried by the *mass-weight polynomial*: the algebra map sending each generator
`j` to `X ^ w * j`, where `w` is its mass weight. The coefficient of `X ^ n` in the mass-weight
polynomial of an element is its part of mass weight `n`, so an element is homogeneous of weight
`n` exactly when its mass-weight polynomial is `X ^ n` times itself, which is the condition
defining `massWeightSubmodule`.

The jet algebra is the tensor product of the two factors and mass weights add under that
product, so the mass-weight polynomial of the whole is assembled from the two factor
polynomials: push each into `Polynomial JetAlgebra` along the tensor inclusions and multiply.
On monomials this is exactly `X ^ a * b ⊗ X ^ c * l ↦ X ^ (a + c) * (b ⊗ l)`.

-/

@[expose] public section


namespace LeptonGaugeSector
open TensorProduct StandardModel Matrix MatrixGroups

/-- We define the mass weight of a term as two times its mass dimnesion. -/
def MassWeight : JetGenerators → ℕ
  | JetGenerators.dB s _ => 2 * (1 + s.card)
  | JetGenerators.dψ s _ => 3 + 2 * s.card
  | JetGenerators.dbarψ s _ => 3 + 2 * s.card

namespace JetAlgebra

/-!

## A. The mass-weight polynomial

-/

/-- The mass-weight polynomial on the lepton–gauge-sector jet algebra, assembled from the
  mass-weight polynomials of the two factors. -/
noncomputable def massWeightPoly : JetAlgebra →ₐ[ℂ] Polynomial JetAlgebra :=
  (Algebra.TensorProduct.lift (Polynomial.mapAlgHom inclB)
      (Polynomial.mapAlgHom inclL) commute_mapAlgHom_inclB_inclL).comp
    (Algebra.TensorProduct.map BBoson.JetAlgebra.massWeightPoly
      LeptonSinglet.JetAlgebra.massWeightPoly)

@[simp]
lemma massWeightPoly_tmul (b : ℂ ⊗[ℝ] BBoson.JetAlgebra) (l : LeptonSinglet.JetAlgebra) :
    massWeightPoly (b ⊗ⱼ l) =
      Polynomial.mapAlgHom inclB (BBoson.JetAlgebra.massWeightPoly b) *
        Polynomial.mapAlgHom inclL (LeptonSinglet.JetAlgebra.massWeightPoly l) := rfl

/-- On the bosonic factor the mass-weight polynomial is the B-boson mass-weight polynomial
  pushed along the inclusion. -/
lemma massWeightPoly_inclB (b : ℂ ⊗[ℝ] BBoson.JetAlgebra) :
    massWeightPoly (inclB b) =
      Polynomial.mapAlgHom inclB (BBoson.JetAlgebra.massWeightPoly b) := by
  rw [show inclB b = b ⊗ⱼ (1 : LeptonSinglet.JetAlgebra) from rfl, massWeightPoly_tmul,
    map_one, map_one, mul_one]

/-- On the fermionic factor the mass-weight polynomial is the charged-lepton mass-weight
  polynomial pushed along the inclusion. -/
lemma massWeightPoly_inclL (l : LeptonSinglet.JetAlgebra) :
    massWeightPoly (inclL l) =
      Polynomial.mapAlgHom inclL (LeptonSinglet.JetAlgebra.massWeightPoly l) := by
  rw [show inclL l = (1 : ℂ ⊗[ℝ] BBoson.JetAlgebra) ⊗ⱼ l from rfl, massWeightPoly_tmul,
    map_one, map_one, one_mul]

/-- The bosonic inclusion is unital. -/
private lemma inclB_one : inclB (1 : ℂ ⊗[ℝ] BBoson.JetAlgebra) = 1 := rfl

/-- The fermionic inclusion is unital. -/
private lemma inclL_one : inclL (1 : LeptonSinglet.JetAlgebra) = 1 := rfl

/-- A pure tensor is the product of the images of its two factors. -/
lemma tmul_eq_inclB_mul_inclL (b : ℂ ⊗[ℝ] BBoson.JetAlgebra)
    (l : LeptonSinglet.JetAlgebra) : b ⊗ⱼ l = inclB b * inclL l := by
  rw [show inclB b = b ⊗ⱼ (1 : LeptonSinglet.JetAlgebra) from rfl,
    show inclL l = (1 : ℂ ⊗[ℝ] BBoson.JetAlgebra) ⊗ⱼ l from rfl,
    tmul_mul_tmul, mul_one, one_mul]

/-- Each generator is sent to `j * X ^ w`, where `w` is its mass weight. -/
@[simp]
lemma massWeightPoly_ofGenerator (j : JetGenerators) :
    massWeightPoly [j]ₐ = Polynomial.monomial (MassWeight j) [j]ₐ := by
  cases j with
  | dB s μ =>
    rw [show ([JetGenerators.dB s μ]ₐ : JetAlgebra) = inclB ((1 : ℂ) ⊗ₜ[ℝ]
        BBoson.JetAlgebra.ofGenerator (BBoson.JetGenerators.dB s μ)) from rfl,
      massWeightPoly_inclB, BBoson.JetAlgebra.massWeightPoly_ofGenerator,
      Polynomial.mapAlgHom_monomial]
    rfl
  | dψ s α =>
    rw [show ([JetGenerators.dψ s α]ₐ : JetAlgebra) = inclL
        (LeptonSinglet.JetAlgebra.ofGenerator (LeptonSinglet.JetGenerators.dψ s α)) from rfl,
      massWeightPoly_inclL, LeptonSinglet.JetAlgebra.massWeightPoly_ofGenerator,
      Polynomial.mapAlgHom_monomial]
    rfl
  | dbarψ s α =>
    rw [show ([JetGenerators.dbarψ s α]ₐ : JetAlgebra) = inclL
        (LeptonSinglet.JetAlgebra.ofGenerator (LeptonSinglet.JetGenerators.dbarψ s α))
        from rfl,
      massWeightPoly_inclL, LeptonSinglet.JetAlgebra.massWeightPoly_ofGenerator,
      Polynomial.mapAlgHom_monomial]
    rfl

/-- Evaluation at one, as an algebra map. The jet algebra is not commutative, so evaluation
  is multiplicative only because the point `1` is central. -/
private noncomputable def evalOne : Polynomial JetAlgebra →ₐ[ℂ] JetAlgebra :=
  Polynomial.eval₂AlgHom (AlgHom.id ℂ JetAlgebra) 1 fun a => Commute.one_right a

private lemma evalOne_apply (p : Polynomial JetAlgebra) : evalOne p = p.eval 1 := rfl

/-- Setting the formal variable to one recovers the original element. -/
lemma massWeightPoly_eval_one (x : JetAlgebra) : (massWeightPoly x).eval 1 = x := by
  induction x using JetAlgebra.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, Polynomial.eval_add, ha, hb]
  | tmul b l =>
    rw [massWeightPoly_tmul, ← evalOne_apply, map_mul, evalOne_apply, evalOne_apply,
      Polynomial.eval_one_mapAlgHom, Polynomial.eval_one_mapAlgHom,
      BBoson.JetAlgebra.massWeightPoly_eval_one,
      LeptonSinglet.JetAlgebra.massWeightPoly_eval_one, ← tmul_eq_inclB_mul_inclL]

/-- Every element is the sum of the coefficients of its mass-weight polynomial. -/
lemma eq_sum_massWeightPoly_coeff (x : JetAlgebra) :
    x = ∑ n ∈ Polynomial.support (massWeightPoly x), (massWeightPoly x).coeff n := by
  conv_lhs => rw [← massWeightPoly_eval_one x]
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  exact Finset.sum_congr rfl fun n _ => by
    have h1 : (1 : JetAlgebra) ^ n = 1 := one_pow (M := JetAlgebra) n
    grind

/-- `massWeightPoly` is injective, however, it is not surjective. -/
lemma massWeightPoly_injective : Function.Injective massWeightPoly := by
  intro x y h
  have h1 : (massWeightPoly x).eval 1 = (massWeightPoly y).eval 1 := by rw [h]
  rwa [massWeightPoly_eval_one, massWeightPoly_eval_one] at h1

/-!

## B. The mass-weight submodules

-/

/-- The submodule of elements of mass weight `n`: those `x` whose mass-weight polynomial is
  `x * X ^ n`. -/
def massWeightSubmodule (n : ℕ) : Submodule ℂ JetAlgebra where
  carrier := {x | massWeightPoly x = Polynomial.monomial n x}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
    rw [ha, hb]
  zero_mem' := by simp
  smul_mem' c x hx := by
    simp only [Set.mem_setOf_eq, map_smul] at hx ⊢
    rw [hx, Polynomial.smul_monomial]

@[simp]
lemma mem_massWeightSubmodule {n : ℕ} {x : JetAlgebra} :
    x ∈ massWeightSubmodule n ↔ massWeightPoly x = Polynomial.monomial n x := Iff.rfl

/-- Mass weights add under multiplication, and `1` has mass weight zero. -/
instance : SetLike.GradedMonoid massWeightSubmodule where
  one_mem := by
    show massWeightPoly 1 = Polynomial.monomial 0 1
    rw [Polynomial.monomial_zero_left, Polynomial.C_1]
    exact massWeightPoly.map_one
  mul_mem {m n x y} hx hy := by
    simp only [mem_massWeightSubmodule, map_mul] at hx hy ⊢
    rw [hx, hy, Polynomial.monomial_mul_monomial]

/-- Mass weights add under multiplication. -/
lemma mul_mem_massWeightSubmodule {m n : ℕ} {x y : JetAlgebra}
    (hx : x ∈ massWeightSubmodule m) (hy : y ∈ massWeightSubmodule n) :
    x * y ∈ massWeightSubmodule (m + n) := by
  simp only [mem_massWeightSubmodule, map_mul] at hx hy ⊢
  rw [hx, hy, Polynomial.monomial_mul_monomial]

/-- The generator `j` has mass weight `MassWeight j`. -/
lemma ofGenerator_mem_massWeightSubmodule (j : JetGenerators) :
    [j]ₐ ∈ massWeightSubmodule (MassWeight j) :=
  massWeightPoly_ofGenerator j

/-- The inclusion of the bosonic factor preserves mass weights. -/
lemma inclB_mem_massWeightSubmodule {n : ℕ} {b : ℂ ⊗[ℝ] BBoson.JetAlgebra}
    (hb : b ∈ BBoson.JetAlgebra.massWeightSubmodule n) :
    inclB b ∈ massWeightSubmodule n := by
  rw [mem_massWeightSubmodule, massWeightPoly_inclB,
    BBoson.JetAlgebra.mem_massWeightSubmodule.mp hb, Polynomial.mapAlgHom_monomial]

/-- The inclusion of the fermionic factor preserves mass weights. -/
lemma inclL_mem_massWeightSubmodule {n : ℕ} {l : LeptonSinglet.JetAlgebra}
    (hl : l ∈ LeptonSinglet.JetAlgebra.massWeightSubmodule n) :
    inclL l ∈ massWeightSubmodule n := by
  rw [mem_massWeightSubmodule, massWeightPoly_inclL,
    LeptonSinglet.JetAlgebra.mem_massWeightSubmodule.mp hl, Polynomial.mapAlgHom_monomial]

/-- The coefficient of `X ^ n` in the mass-weight polynomial of `x` has mass weight `n`: on a
  pure tensor it is a sum of products of a bosonic and a fermionic coefficient of
  complementary weights. -/
lemma coeff_massWeightPoly_mem_massWeightSubmodule (n : ℕ) (x : JetAlgebra) :
    (massWeightPoly x).coeff n ∈ massWeightSubmodule n := by
  induction x using JetAlgebra.induction_on generalizing n with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add, Polynomial.coeff_add]
    exact Submodule.add_mem _ (ha n) (hb n)
  | tmul b l =>
    rw [massWeightPoly_tmul, Polynomial.coeff_mul]
    refine Submodule.sum_mem _ fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    rw [Polynomial.coeff_mapAlgHom_apply, Polynomial.coeff_mapAlgHom_apply, ← hp]
    exact mul_mem_massWeightSubmodule
      (inclB_mem_massWeightSubmodule
        (BBoson.JetAlgebra.coeff_massWeightPoly_mem_massWeightSubmodule p.1 b))
      (inclL_mem_massWeightSubmodule
        (LeptonSinglet.JetAlgebra.coeff_massWeightPoly_mem_massWeightSubmodule p.2 l))

/-- The coefficients of a mass-weight polynomial are homogeneous: the coefficient of `X ^ n`
  in `massWeightPoly x` is sent by `massWeightPoly` to `X ^ n` times itself. -/
lemma massWeightPoly_coeff_massWeightPoly (n : ℕ) (x : JetAlgebra) :
    massWeightPoly ((massWeightPoly x).coeff n) =
      Polynomial.monomial n ((massWeightPoly x).coeff n) :=
  coeff_massWeightPoly_mem_massWeightSubmodule n x

/-- On an element of mass weight `n`, the `n`-th coefficient of the mass-weight polynomial is
  the element itself. -/
lemma coeff_massWeightPoly_of_mem {n : ℕ} {x : JetAlgebra}
    (hx : x ∈ massWeightSubmodule n) : (massWeightPoly x).coeff n = x := by
  rw [mem_massWeightSubmodule.mp hx, Polynomial.coeff_monomial, if_pos rfl]

/-- On an element of mass weight `m`, every other coefficient of the mass-weight polynomial
  vanishes. -/
lemma coeff_massWeightPoly_of_mem_ne {m n : ℕ} {x : JetAlgebra} (hmn : m ≠ n)
    (hx : x ∈ massWeightSubmodule m) : (massWeightPoly x).coeff n = 0 := by
  rw [mem_massWeightSubmodule.mp hx, Polynomial.coeff_monomial, if_neg hmn]

/-- The submodule of elements of mass weight at most `n`: the renormalizable Lagrangian
  densities are those of mass weight at most eight. -/
noncomputable def MassWeightLESubmodule (n : ℕ) : Submodule ℂ JetAlgebra :=
  ⨆ (m : ℕ) (_ : m ≤ n), massWeightSubmodule m

lemma massWeightSubmodule_le_massWeightLESubmodule {m n : ℕ} (hmn : m ≤ n) :
    massWeightSubmodule m ≤ MassWeightLESubmodule n :=
  le_iSup_of_le m (le_iSup_of_le hmn le_rfl)

/-- An element of mass weight `m ≤ n` has mass weight at most `n`. -/
lemma mem_massWeightLESubmodule_of_mem {m n : ℕ} (hmn : m ≤ n) {x : JetAlgebra}
    (hx : x ∈ massWeightSubmodule m) : x ∈ MassWeightLESubmodule n :=
  massWeightSubmodule_le_massWeightLESubmodule hmn hx

/-- Above the bound the coefficients of the mass-weight polynomial vanish. -/
lemma coeff_massWeightPoly_eq_zero_of_mem_massWeightLESubmodule {n : ℕ} {x : JetAlgebra}
    (hx : x ∈ MassWeightLESubmodule n) {i : ℕ} (hi : n < i) :
    (massWeightPoly x).coeff i = 0 := by
  induction hx using Submodule.iSup_induction' with
  | mem m y hy =>
    by_cases hmn : m ≤ n
    · rw [iSup_pos hmn] at hy
      exact coeff_massWeightPoly_of_mem_ne (by omega) hy
    · rw [iSup_neg hmn, Submodule.mem_bot] at hy
      rw [hy, map_zero, Polynomial.coeff_zero]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, Polynomial.coeff_add, ha, hb, add_zero]

/-- An element of mass weight at most `n` is the sum of its parts of weight `0, …, n`, each
  read off as a coefficient of its mass-weight polynomial. -/
lemma eq_sum_coeff_of_mem_massWeightLESubmodule {n : ℕ} {x : JetAlgebra}
    (hx : x ∈ MassWeightLESubmodule n) :
    x = ∑ m ∈ Finset.range (n + 1), (massWeightPoly x).coeff m := by
  conv_lhs => rw [eq_sum_massWeightPoly_coeff x]
  refine Finset.sum_subset (fun m hm => ?_) (fun m _ hm => ?_)
  · rw [Finset.mem_range]
    by_contra hlt
    exact Polynomial.mem_support_iff.mp hm
      (coeff_massWeightPoly_eq_zero_of_mem_massWeightLESubmodule hx (by omega))
  · exact Polynomial.notMem_support_iff.mp hm

/-- The Lorentz-invariant Lagrangian densities of mass weight at most `n`. -/
noncomputable def InvariantMassWeightSubmodule (n : ℕ) : Submodule ℂ JetAlgebra :=
  MassWeightLESubmodule n ⊓ InvariantSubmodule

/-!

## C. The mass weight of the derivatives and of the field strength

-/

/-- The total derivative acts on the bosonic factor through its own total derivative. -/
lemma jetDeriv_inclB (μ : Fin 1 ⊕ Fin 3) (b : ℂ ⊗[ℝ] BBoson.JetAlgebra) :
    jetDeriv μ (inclB b) =
      inclB (LinearMap.baseChange ℂ (BBoson.JetAlgebra.jetDeriv μ) b) := by
  rw [show inclB b = b ⊗ⱼ (1 : LeptonSinglet.JetAlgebra) from rfl, jetDeriv_tmul,
    LeptonSinglet.JetAlgebra.jetDeriv_one, tmul_zero, add_zero]
  rfl

/-- The total derivative acts on the fermionic factor through its own total derivative. -/
lemma jetDeriv_inclL (μ : Fin 1 ⊕ Fin 3) (l : LeptonSinglet.JetAlgebra) :
    jetDeriv μ (inclL l) = inclL (LeptonSinglet.JetAlgebra.jetDeriv μ l) := by
  rw [show inclL l = (1 : ℂ ⊗[ℝ] BBoson.JetAlgebra) ⊗ⱼ l from rfl, jetDeriv_tmul,
    show LinearMap.baseChange ℂ (BBoson.JetAlgebra.jetDeriv μ)
        (1 : ℂ ⊗[ℝ] BBoson.JetAlgebra) = 0 from by
      rw [show (1 : ℂ ⊗[ℝ] BBoson.JetAlgebra) =
          (1 : ℂ) ⊗ₜ[ℝ] (1 : BBoson.JetAlgebra) from rfl, LinearMap.baseChange_tmul,
        BBoson.JetAlgebra.jetDeriv_one, TensorProduct.tmul_zero],
    zero_tmul, zero_add]
  rfl

/-- Pushing a polynomial forward along the bosonic inclusion commutes with applying the total
  derivative to its coefficients. -/
private lemma mapCoeffs_jetDeriv_mapAlgHom_inclB (μ : Fin 1 ⊕ Fin 3)
    (p : Polynomial (ℂ ⊗[ℝ] BBoson.JetAlgebra)) :
    Polynomial.mapCoeffs (jetDeriv μ) (Polynomial.mapAlgHom inclB p) =
      Polynomial.mapAlgHom inclB
        (Polynomial.mapCoeffs (LinearMap.baseChange ℂ (BBoson.JetAlgebra.jetDeriv μ)) p) := by
  refine Polynomial.ext fun n => ?_
  rw [Polynomial.coeff_mapCoeffs (map_zero (jetDeriv μ)),
    Polynomial.coeff_mapAlgHom_apply, Polynomial.coeff_mapAlgHom_apply,
    Polynomial.coeff_mapCoeffs
      (map_zero (LinearMap.baseChange ℂ (BBoson.JetAlgebra.jetDeriv μ)))]
  exact jetDeriv_inclB μ _

/-- Pushing a polynomial forward along the fermionic inclusion commutes with applying the
  total derivative to its coefficients. -/
private lemma mapCoeffs_jetDeriv_mapAlgHom_inclL (μ : Fin 1 ⊕ Fin 3)
    (p : Polynomial LeptonSinglet.JetAlgebra) :
    Polynomial.mapCoeffs (jetDeriv μ) (Polynomial.mapAlgHom inclL p) =
      Polynomial.mapAlgHom inclL
        (Polynomial.mapCoeffs (LeptonSinglet.JetAlgebra.jetDeriv μ) p) := by
  refine Polynomial.ext fun n => ?_
  rw [Polynomial.coeff_mapCoeffs (map_zero (jetDeriv μ)),
    Polynomial.coeff_mapAlgHom_apply, Polynomial.coeff_mapAlgHom_apply,
    Polynomial.coeff_mapCoeffs (map_zero (LeptonSinglet.JetAlgebra.jetDeriv μ))]
  exact jetDeriv_inclL μ _

/-- The formal variable is fixed by the tensor inclusions. -/
private lemma mapAlgHom_X_sq_inclB :
    Polynomial.mapAlgHom inclB
        ((Polynomial.X : Polynomial (ℂ ⊗[ℝ] BBoson.JetAlgebra)) ^ 2) =
      (Polynomial.X : Polynomial JetAlgebra) ^ 2 := by
  rw [Polynomial.X_pow_eq_monomial, Polynomial.mapAlgHom_monomial, inclB_one,
    ← Polynomial.X_pow_eq_monomial]

private lemma mapAlgHom_X_sq_inclL :
    Polynomial.mapAlgHom inclL ((Polynomial.X : Polynomial LeptonSinglet.JetAlgebra) ^ 2) =
      (Polynomial.X : Polynomial JetAlgebra) ^ 2 := by
  rw [Polynomial.X_pow_eq_monomial, Polynomial.mapAlgHom_monomial, inclL_one,
    ← Polynomial.X_pow_eq_monomial]

/-- The Leibniz rule for the total derivative applied coefficientwise to a product of
  polynomials. -/
private lemma mapCoeffs_jetDeriv_mul (μ : Fin 1 ⊕ Fin 3) (P Q : Polynomial JetAlgebra) :
    Polynomial.mapCoeffs (jetDeriv μ) (P * Q) =
      Polynomial.mapCoeffs (jetDeriv μ) P * Q + P * Polynomial.mapCoeffs (jetDeriv μ) Q :=
  Polynomial.mapCoeffs_mul_of_leibniz (map_zero (jetDeriv μ)) (map_add (jetDeriv μ))
    (jetDeriv_mul μ) P Q

/-- Rearrangement used for the Leibniz step: `X ^ 2` is central, so it can be pulled out of a
  Leibniz combination. -/
private lemma X_sq_mul_leibniz {R : Type} [Semiring R] (p q r s : Polynomial R) :
    Polynomial.X ^ 2 * p * q + r * (Polynomial.X ^ 2 * s) =
      Polynomial.X ^ 2 * (p * q + r * s) := by
  rw [mul_add, mul_assoc, ← mul_assoc r, ← Polynomial.X_pow_mul, mul_assoc]

/-- The total derivative raises the mass weight by two: its mass-weight polynomial is `X ^ 2`
  times the coefficientwise total derivative. -/
lemma massWeightPoly_jetDeriv (μ : Fin 1 ⊕ Fin 3) (x : JetAlgebra) :
    massWeightPoly (jetDeriv μ x) =
      Polynomial.X ^ 2 * Polynomial.mapCoeffs (jetDeriv μ) (massWeightPoly x) := by
  have hmul : ∀ a b : JetAlgebra,
      massWeightPoly (jetDeriv μ a) =
          Polynomial.X ^ 2 * Polynomial.mapCoeffs (jetDeriv μ) (massWeightPoly a) →
      massWeightPoly (jetDeriv μ b) =
          Polynomial.X ^ 2 * Polynomial.mapCoeffs (jetDeriv μ) (massWeightPoly b) →
      massWeightPoly (jetDeriv μ (a * b)) =
        Polynomial.X ^ 2 * Polynomial.mapCoeffs (jetDeriv μ) (massWeightPoly (a * b)) := by
    intro a b ha hb
    rw [jetDeriv_mul]
    simp only [map_add, map_mul]
    rw [ha, hb, mapCoeffs_jetDeriv_mul, X_sq_mul_leibniz]
  have hB : ∀ b : ℂ ⊗[ℝ] BBoson.JetAlgebra,
      massWeightPoly (jetDeriv μ (inclB b)) =
        Polynomial.X ^ 2 * Polynomial.mapCoeffs (jetDeriv μ) (massWeightPoly (inclB b)) := by
    intro b
    rw [jetDeriv_inclB, massWeightPoly_inclB, massWeightPoly_inclB,
      BBoson.JetAlgebra.massWeightPoly_jetDeriv_baseChange, map_mul,
      mapAlgHom_X_sq_inclB, mapCoeffs_jetDeriv_mapAlgHom_inclB]
  have hL : ∀ l : LeptonSinglet.JetAlgebra,
      massWeightPoly (jetDeriv μ (inclL l)) =
        Polynomial.X ^ 2 * Polynomial.mapCoeffs (jetDeriv μ) (massWeightPoly (inclL l)) := by
    intro l
    rw [jetDeriv_inclL, massWeightPoly_inclL, massWeightPoly_inclL,
      LeptonSinglet.JetAlgebra.massWeightPoly_jetDeriv, map_mul,
      mapAlgHom_X_sq_inclL, mapCoeffs_jetDeriv_mapAlgHom_inclL]
  induction x using JetAlgebra.induction_on with
  | zero => simp
  | add a b ha hb =>
    rw [map_add, map_add, ha, hb, map_add,
      Polynomial.mapCoeffs_add (map_zero (jetDeriv μ)) (map_add (jetDeriv μ)), mul_add]
  | tmul b l =>
    rw [tmul_eq_inclB_mul_inclL]
    exact hmul _ _ (hB b) (hL l)

/-- The total derivative raises the mass weight by two. -/
lemma jetDeriv_mem_massWeightSubmodule (μ : Fin 1 ⊕ Fin 3) {n : ℕ} {x : JetAlgebra}
    (hx : x ∈ massWeightSubmodule n) : jetDeriv μ x ∈ massWeightSubmodule (n + 2) := by
  rw [mem_massWeightSubmodule] at hx ⊢
  rw [massWeightPoly_jetDeriv, hx, Polynomial.mapCoeffs_monomial (map_zero (jetDeriv μ)),
    Polynomial.X_pow_eq_monomial, Polynomial.monomial_mul_monomial, one_mul,
    Nat.add_comm 2 n]

/-- The gauge field has mass weight two. -/
lemma dB_nil_mem_massWeightSubmodule (μ : Fin 1 ⊕ Fin 3) :
    [JetGenerators.dB {} μ]ₐ ∈ massWeightSubmodule 2 := by
  have h := ofGenerator_mem_massWeightSubmodule (JetGenerators.dB {} μ)
  rwa [show MassWeight (JetGenerators.dB {} μ) = 2 from by simp [MassWeight]] at h

/-- The covariant step raises the mass weight by two: the gauge-field term `6 i B_μ ·`
  carries the same weight as the derivative. -/
lemma covariantStep_mem_massWeightSubmodule (μ : Fin 1 ⊕ Fin 3) {n : ℕ} {x : JetAlgebra}
    (hx : x ∈ massWeightSubmodule n) :
    covariantStep μ x ∈ massWeightSubmodule (n + 2) := by
  rw [covariantStep_apply]
  refine Submodule.sub_mem _ (jetDeriv_mem_massWeightSubmodule μ hx)
    (Submodule.smul_mem _ _ ?_)
  have h := mul_mem_massWeightSubmodule (dB_nil_mem_massWeightSubmodule μ) hx
  rwa [Nat.add_comm 2 n] at h

/-- The conjugate covariant step raises the mass weight by two. -/
lemma covariantStepBar_mem_massWeightSubmodule (μ : Fin 1 ⊕ Fin 3) {n : ℕ} {x : JetAlgebra}
    (hx : x ∈ massWeightSubmodule n) :
    covariantStepBar μ x ∈ massWeightSubmodule (n + 2) := by
  rw [covariantStepBar_apply]
  refine Submodule.add_mem _ (jetDeriv_mem_massWeightSubmodule μ hx)
    (Submodule.smul_mem _ _ ?_)
  have h := mul_mem_massWeightSubmodule (dB_nil_mem_massWeightSubmodule μ) hx
  rwa [Nat.add_comm 2 n] at h

/-- Homogeneity of the covariant derivative: `D_l ψ_α` has mass weight `3 + 2 |l|`. -/
lemma Dψ_mem_massWeightSubmodule (l : List (Fin 1 ⊕ Fin 3)) (α : Fin 2) :
    Dψ l α ∈ massWeightSubmodule (3 + 2 * l.length) := by
  induction l with
  | nil =>
    rw [Dψ_nil]
    have h := ofGenerator_mem_massWeightSubmodule (JetGenerators.dψ {} α)
    rwa [show MassWeight (JetGenerators.dψ {} α) = 3 + 2 * ([] : List (Fin 1 ⊕ Fin 3)).length
      from by simp [MassWeight]] at h
  | cons μ l ih =>
    rw [Dψ_cons]
    have h := covariantStep_mem_massWeightSubmodule μ ih
    rwa [show 3 + 2 * l.length + 2 = 3 + 2 * (μ :: l).length from by
      simp only [List.length_cons]; omega] at h

/-- Homogeneity of the conjugate covariant derivative: `D̄_l ψ̄_α` has mass weight
  `3 + 2 |l|`. -/
lemma Dbarψ_mem_massWeightSubmodule (l : List (Fin 1 ⊕ Fin 3)) (α : Fin 2) :
    Dbarψ l α ∈ massWeightSubmodule (3 + 2 * l.length) := by
  induction l with
  | nil =>
    rw [Dbarψ_nil]
    have h := ofGenerator_mem_massWeightSubmodule (JetGenerators.dbarψ {} α)
    rwa [show MassWeight (JetGenerators.dbarψ {} α) =
      3 + 2 * ([] : List (Fin 1 ⊕ Fin 3)).length from by simp [MassWeight]] at h
  | cons μ l ih =>
    rw [Dbarψ_cons]
    have h := covariantStepBar_mem_massWeightSubmodule μ ih
    rwa [show 3 + 2 * l.length + 2 = 3 + 2 * (μ :: l).length from by
      simp only [List.length_cons]; omega] at h

/-- Homogeneity of the field-strength derivatives: `∂_s F_{μν}` has mass weight
  `4 + 2 |s|`. -/
lemma fieldStrengthDeriv_mem_massWeightSubmodule (s : Multiset (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) :
    fieldStrengthDeriv s μ ν ∈ massWeightSubmodule (4 + 2 * Multiset.card s) := by
  have h : (fieldStrengthDeriv s μ ν : JetAlgebra) =
      [JetGenerators.dB (s + {μ}) ν]ₐ - [JetGenerators.dB (s + {ν}) μ]ₐ := by
    rw [fieldStrengthDeriv, BBoson.JetAlgebra.fieldStrengthDeriv,
      TensorProduct.tmul_sub, sub_tmul]
    rfl
  rw [h]
  refine Submodule.sub_mem _ ?_ ?_
  · have hg := ofGenerator_mem_massWeightSubmodule (JetGenerators.dB (s + {μ}) ν)
    rwa [show MassWeight (JetGenerators.dB (s + {μ}) ν) = 4 + 2 * Multiset.card s from by
      simp only [MassWeight, Multiset.card_add, Multiset.card_singleton]; omega] at hg
  · have hg := ofGenerator_mem_massWeightSubmodule (JetGenerators.dB (s + {ν}) μ)
    rwa [show MassWeight (JetGenerators.dB (s + {ν}) μ) = 4 + 2 * Multiset.card s from by
      simp only [MassWeight, Multiset.card_add, Multiset.card_singleton]; omega] at hg

/-!

## D. Invariance of the mass weights under the Lorentz and constant gauge actions

-/

set_option maxHeartbeats 400000 in
/-- The Lorentz action preserves mass weights: the mass-weight polynomial of a transformed
  element is the transform of its mass-weight polynomial. -/
lemma massWeightPoly_repLorentzGroup (Λ : SL(2,ℂ)) (x : JetAlgebra) :
    massWeightPoly (repLorentzGroup Λ x) =
      Polynomial.mapAlgHom (repLorentzGroupAlgHom Λ) (massWeightPoly x) := by
  have hB : ∀ z : ℂ ⊗[ℝ] BBoson.JetAlgebra, repLorentzGroupAlgHom Λ (inclB z) =
      inclB (BBoson.JetAlgebra.complexRepLorentzGroup Λ z) := by
    intro z
    show repLorentzGroup Λ (z ⊗ⱼ (1 : LeptonSinglet.JetAlgebra)) = _
    rw [repLorentzGroup_tmul, LeptonSinglet.JetAlgebra.repLorentzGroup_apply_one]
    rfl
  have hL : ∀ z : LeptonSinglet.JetAlgebra, repLorentzGroupAlgHom Λ (inclL z) =
      inclL (LeptonSinglet.JetAlgebra.repLorentzGroup Λ z) := by
    intro z
    show repLorentzGroup Λ ((1 : ℂ ⊗[ℝ] BBoson.JetAlgebra) ⊗ⱼ z) = _
    rw [repLorentzGroup_tmul, BBoson.JetAlgebra.complexRepLorentzGroup_apply_one]
    rfl
  induction x using JetAlgebra.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul b l =>
    rw [repLorentzGroup_tmul, massWeightPoly_tmul, massWeightPoly_tmul,
      BBoson.JetAlgebra.massWeightPoly_complexRepLorentzGroup,
      LeptonSinglet.JetAlgebra.massWeightPoly_repLorentzGroup, map_mul]
    refine congrArg₂ (· * ·) (Polynomial.ext fun n => ?_) (Polynomial.ext fun n => ?_)
    · rw [Polynomial.coeff_mapAlgHom_apply, Polynomial.coeff_mapAlgHom_apply,
        Polynomial.coeff_mapAlgHom_apply, Polynomial.coeff_mapAlgHom_apply, hB]
      rfl
    · rw [Polynomial.coeff_mapAlgHom_apply, Polynomial.coeff_mapAlgHom_apply,
        Polynomial.coeff_mapAlgHom_apply, Polynomial.coeff_mapAlgHom_apply, hL]
      rfl

/-- The Lorentz action preserves each mass-weight submodule. -/
lemma repLorentzGroup_mem_massWeightSubmodule (Λ : SL(2,ℂ)) {n : ℕ} {x : JetAlgebra}
    (hx : x ∈ massWeightSubmodule n) : repLorentzGroup Λ x ∈ massWeightSubmodule n := by
  rw [mem_massWeightSubmodule] at hx ⊢
  rw [massWeightPoly_repLorentzGroup, hx, Polynomial.mapAlgHom_monomial]
  rfl

set_option maxHeartbeats 400000 in
/-- Jets of constant gauge transformations preserve mass weights. This fails for a general
  jet: the higher Taylor coefficients of the hypercharge character lower the derivative
  degree, mixing weights. -/
lemma massWeightPoly_repJetGaugeGroupI_ofConstant (g : GaugeGroupI) (x : JetAlgebra) :
    massWeightPoly (repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) x) =
      Polynomial.mapAlgHom (repAlgHom (JetGaugeGroupI.ofConstant g)) (massWeightPoly x) := by
  set U := JetGaugeGroupI.ofConstant g with hUdef
  have hB : ∀ z : ℂ ⊗[ℝ] BBoson.JetAlgebra, repAlgHom U (inclB z) =
      inclB (BBoson.JetAlgebra.complexRepJetGaugeGroupI U z) := by
    intro z
    rw [show inclB z = z ⊗ⱼ (1 : LeptonSinglet.JetAlgebra) from rfl, repAlgHom_tmul,
      show (ExteriorAlgebra.map (LeptonSinglet.JetComponentSpace.repJetGaugeGroupI U))
          (1 : LeptonSinglet.JetAlgebra) = 1 from map_one _]
    rfl
  have hL : ∀ z : LeptonSinglet.JetAlgebra, repAlgHom U (inclL z) =
      inclL (LeptonSinglet.JetAlgebra.repJetGaugeGroupI U z) := by
    intro z
    rw [show inclL z = (1 : ℂ ⊗[ℝ] BBoson.JetAlgebra) ⊗ⱼ z from rfl, repAlgHom_tmul,
      BBoson.JetAlgebra.complexRepJetGaugeGroupI_one]
    rfl
  induction x using JetAlgebra.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul b l =>
    rw [repJetGaugeGroupI_tmul', massWeightPoly_tmul, massWeightPoly_tmul,
      BBoson.JetAlgebra.massWeightPoly_complexRepJetGaugeGroupI_ofConstant,
      LeptonSinglet.JetAlgebra.massWeightPoly_repJetGaugeGroupI_ofConstant, map_mul]
    refine congrArg₂ (· * ·) (Polynomial.ext fun n => ?_) (Polynomial.ext fun n => ?_)
    · rw [Polynomial.coeff_mapAlgHom_apply, Polynomial.coeff_mapAlgHom_apply,
        Polynomial.coeff_mapAlgHom_apply, hB,
        BBoson.JetAlgebra.complexRepJetGaugeGroupI_ofConstant]
    · rw [Polynomial.coeff_mapAlgHom_apply, Polynomial.coeff_mapAlgHom_apply,
        Polynomial.coeff_mapAlgHom_apply, Polynomial.coeff_mapAlgHom_apply, hL]
      rfl

/-- Jets of constant gauge transformations preserve each mass-weight submodule. -/
lemma repJetGaugeGroupI_ofConstant_mem_massWeightSubmodule (g : GaugeGroupI) {n : ℕ}
    {x : JetAlgebra} (hx : x ∈ massWeightSubmodule n) :
    repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) x ∈ massWeightSubmodule n := by
  rw [mem_massWeightSubmodule] at hx ⊢
  rw [massWeightPoly_repJetGaugeGroupI_ofConstant, hx, Polynomial.mapAlgHom_monomial,
    ← repJetGaugeGroupI_eq_repAlgHom]


/-!

## E. Invariance of the mass-weight components

Taking the part of a given mass weight commutes with the Lorentz action and with the action of
the *constant* gauge transformations, because both preserve mass weights. The covariant
subalgebra is generated by homogeneous elements, so it too is graded by mass weight. Together
these say that an invariant element of the covariant subalgebra has invariant mass-weight
components — which is what lets the classification be run one weight at a time.

-/

/-- Taking the weight-`n` part commutes with the Lorentz action. -/
lemma repLorentzGroup_coeff_massWeightPoly (Λ : SL(2,ℂ)) (x : JetAlgebra) (n : ℕ) :
    repLorentzGroup Λ ((massWeightPoly x).coeff n) =
      (massWeightPoly (repLorentzGroup Λ x)).coeff n := by
  rw [massWeightPoly_repLorentzGroup, Polynomial.coeff_mapAlgHom_apply]
  rfl

/-- Taking the weight-`n` part commutes with the action of a constant gauge transformation.
  This fails for a general gauge jet, whose higher Taylor coefficients mix weights. -/
lemma repJetGaugeGroupI_ofConstant_coeff_massWeightPoly (g : GaugeGroupI) (x : JetAlgebra)
    (n : ℕ) :
    repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) ((massWeightPoly x).coeff n) =
      (massWeightPoly (repJetGaugeGroupI (JetGaugeGroupI.ofConstant g) x)).coeff n := by
  rw [massWeightPoly_repJetGaugeGroupI_ofConstant, Polynomial.coeff_mapAlgHom_apply,
    ← repJetGaugeGroupI_eq_repAlgHom]

/-- The covariant subalgebra is graded by mass weight: its generators are homogeneous — the
  field-strength derivative `∂_s F_{μν}` has weight `4 + 2 |s|` and the covariant derivatives
  `D_l ψ_α`, `D̄_l ψ̄_α` weight `3 + 2 |l|` — so every mass-weight part of an element of the
  subalgebra lies in the subalgebra again. -/
lemma coeff_massWeightPoly_mem_covariantAlgebra {x : JetAlgebra} (hx : x ∈ CovariantAlgebra)
    (n : ℕ) : (massWeightPoly x).coeff n ∈ CovariantAlgebra := by
  induction hx using CovariantAlgebra.induction_on generalizing n with
  | fieldStrength s μ ν =>
    by_cases hn : 4 + 2 * Multiset.card s = n
    · rw [coeff_massWeightPoly_of_mem (hn ▸ fieldStrengthDeriv_mem_massWeightSubmodule s μ ν)]
      exact fieldStrengthDeriv_mem_covariantAlgebra s μ ν
    · rw [coeff_massWeightPoly_of_mem_ne hn (fieldStrengthDeriv_mem_massWeightSubmodule s μ ν)]
      exact Subalgebra.zero_mem _
  | lepton l α =>
    by_cases hn : 3 + 2 * l.length = n
    · rw [coeff_massWeightPoly_of_mem (hn ▸ Dψ_mem_massWeightSubmodule l α)]
      exact Dψ_mem_covariantAlgebra l α
    · rw [coeff_massWeightPoly_of_mem_ne hn (Dψ_mem_massWeightSubmodule l α)]
      exact Subalgebra.zero_mem _
  | conjLepton l α =>
    by_cases hn : 3 + 2 * l.length = n
    · rw [coeff_massWeightPoly_of_mem (hn ▸ Dbarψ_mem_massWeightSubmodule l α)]
      exact Dbarψ_mem_covariantAlgebra l α
    · rw [coeff_massWeightPoly_of_mem_ne hn (Dbarψ_mem_massWeightSubmodule l α)]
      exact Subalgebra.zero_mem _
  | algebraMap r =>
    rw [AlgHom.commutes, Polynomial.algebraMap_apply, Polynomial.coeff_C]
    split_ifs
    · exact Subalgebra.algebraMap_mem _ r
    · exact Subalgebra.zero_mem _
  | add u v _ _ ihu ihv =>
    rw [map_add, Polynomial.coeff_add]
    exact Subalgebra.add_mem _ (ihu n) (ihv n)
  | mul u v _ _ ihu ihv =>
    rw [map_mul, Polynomial.coeff_mul]
    exact Subalgebra.sum_mem _ fun p _ => Subalgebra.mul_mem _ (ihu p.1) (ihv p.2)

/-- The mass-weight components of an invariant element are themselves invariant.

  Invariance under the full jet gauge group does not by itself pass to the components — a
  general gauge jet mixes mass weights. It passes because an invariant element lies in the
  covariant subalgebra (`isInvariant_iff_mem_covariantAlgebra`), on which invariance is
  equivalent to membership together with invariance under the *constant* gauge transformations
  and the Lorentz group, and all three of those conditions are inherited by the components. -/
lemma isInvariant_coeff_massWeightPoly {x : JetAlgebra} (hx : IsInvariant x) (n : ℕ) :
    IsInvariant ((massWeightPoly x).coeff n) := by
  rw [isInvariant_iff_mem_covariantAlgebra] at hx ⊢
  obtain ⟨hmem, hconst, hlor⟩ := hx
  refine ⟨coeff_massWeightPoly_mem_covariantAlgebra hmem n, fun g => ?_, fun Λ => ?_⟩
  · rw [repJetGaugeGroupI_ofConstant_coeff_massWeightPoly, hconst g]
  · rw [repLorentzGroup_coeff_massWeightPoly, hlor Λ]

end JetAlgebra

end LeptonGaugeSector
