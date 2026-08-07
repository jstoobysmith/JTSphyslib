/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.Mathematics.MvPolynomialTranslation
public import Physlib.Particles.StandardModel.GaugeBosons.Gluons.JetCompleteness.ColourBasis
/-!
# The first-order covariant coordinate change

## i. Overview

`A₁` is the polynomial algebra over `ℝ` on the gluon connection coordinates `A_μ^c` and their
first ordinary derivatives `(∂_ν A_μ)^c`, with `μ, ν` spacetime directions and `c` a colour index
running over the basis `SU3Jet.colourBasis` of `ColourBasis`. This file replaces the `∂_ν A_μ` block
by the
*symmetric* derivative coordinates together with the field strength

```text
F_{νμ} = ∂_ν A_μ - ∂_μ A_ν + i [A_ν, A_μ],
```

and proves that the replacement is an isomorphism of algebras whose inverse carries the nonabelian
commutator correction.

## ii. Conventions

Physlib uses hermitian gluon potentials. Converting the Lie-algebra formula of
the underlying matrix-valued jet model (`F = ∂A - ∂A - [A, A]`, anti-hermitian) by
`A^{ah} = -i A^h` gives the hermitian field strength `F = ∂A - ∂A + i [A, A]`, which is the sign
used here. Correspondingly the colour bracket carried by the coordinate change is
`brMat M N = i (M N - N M)`, which preserves the traceless hermitian carrier.

## iii. Index design

* the colour index is the `Fin 8` of `SU3Jet.colourBasis`, as required by the proof strategy;
* symmetric derivative coordinates are indexed by `Sym2 Lor`;
* curvature coordinates are indexed by `CurvPair`, the *strictly ordered* pairs of spacetime
  directions, so that the carrier holds six independent curvature variables per colour direction
  and no antisymmetry relation.

`LinearOrder (Fin 1 ⊕ Fin 3)` does not synthesize in this Mathlib. Rather than introduce a local
order instance the order is transported along the explicit equivalence `lorRank : Lor ≃ Fin 4`;
`Fin 4` already carries the decidability and trichotomy that the curvature variable needs, and
nothing else in the development wants an order on `Lor`.

Coordinate count: `∂A` is `16 × 8 = 128`, splitting as symmetric `10 × 8 = 80` plus curvature
`6 × 8 = 48`.

## iv. Results

* `brP`, `cstruct` — the colour bracket in coordinates, and its structure constants;
* `curvPoly` — the field strength as a polynomial in the ordinary coordinates;
* `oldToNew`, `newToOld` — the two substitution algebra maps;
* `newToOld_oldToNew`, `oldToNew_newToOld` — they are mutually inverse on every generator;
* `covEquiv : A₁ ≃ₐ[ℝ] A₁cov` — the resulting coordinate change.

-/

@[expose] public section

namespace StandardModel

open Matrix Module MvPolynomial

namespace SU3Jet

/-!

## A. Index types

-/

/-- The spacetime index. -/
abbrev Lor : Type := Fin 1 ⊕ Fin 3

/-- The colour index, the index type of `SU3Jet.colourBasis`. -/
abbrev Col : Type := Fin 8

/-- A linear ordering of the four spacetime directions, transported along an explicit
  equivalence: `LinearOrder (Fin 1 ⊕ Fin 3)` does not synthesize. -/
def lorRank : Lor ≃ Fin 4 := finSumFinEquiv

/-- The transported strict order on spacetime directions. -/
def LorLT (ν μ : Lor) : Prop := lorRank ν < lorRank μ

instance (ν μ : Lor) : Decidable (LorLT ν μ) := by
  unfold LorLT; infer_instance

lemma lorLT_irrefl (ν : Lor) : ¬ LorLT ν ν := lt_irrefl _

lemma lorLT_asymm {ν μ : Lor} (h : LorLT ν μ) : ¬ LorLT μ ν := lt_asymm h

lemma lor_trichotomy (ν μ : Lor) : LorLT ν μ ∨ ν = μ ∨ LorLT μ ν := by
  rcases lt_trichotomy (lorRank ν) (lorRank μ) with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (lorRank.injective h))
  · exact Or.inr (Or.inr h)

/-- The six independent curvature slots: strictly ordered pairs of spacetime directions. -/
abbrev CurvPair : Type := {p : Lor × Lor // LorLT p.1 p.2}

/-- The ordinary coordinates of the first-order gluon jet algebra: the connection and its first
  ordinary derivatives. -/
inductive Coord where
  /-- The connection coordinate `A_μ^c`. -/
  | conn : Lor → Col → Coord
  /-- The ordinary derivative coordinate `(∂_ν A_μ)^c`. -/
  | der : Lor → Lor → Col → Coord
deriving DecidableEq

/-- The covariant coordinates: the connection, the symmetric part of its derivative, and the
  field strength. -/
inductive CovCoord where
  /-- The connection coordinate `A_μ^c`. -/
  | conn : Lor → Col → CovCoord
  /-- The symmetric derivative coordinate `(∂_{(ν} A_{μ)})^c`. -/
  | sym : Sym2 Lor → Col → CovCoord
  /-- The field strength coordinate `F_{νμ}^c`, one variable per ordered pair. -/
  | curv : CurvPair → Col → CovCoord
deriving DecidableEq

/-- The first-order gluon jet algebra in ordinary coordinates. -/
abbrev A₁ : Type := MvPolynomial Coord ℝ

/-- The first-order gluon jet algebra in covariant coordinates. -/
abbrev A₁cov : Type := MvPolynomial CovCoord ℝ

/-!

## B. The colour bracket

-/

/-- The underlying complex matrix of a colour vector. -/
def cmat (X : ColourSpace) : Matrix (Fin 3) (Fin 3) ℂ :=
  ((X : selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ)) : Matrix (Fin 3) (Fin 3) ℂ)

lemma cmat_injective : Function.Injective cmat := fun _ _ h =>
  Subtype.ext (Subtype.ext h)

@[simp]
lemma cmat_add (X Y : ColourSpace) : cmat (X + Y) = cmat X + cmat Y := rfl

@[simp]
lemma cmat_smul (r : ℝ) (X : ColourSpace) : cmat (r • X) = r • cmat X := rfl

@[simp]
lemma cmat_zero : cmat 0 = 0 := rfl

@[simp]
lemma cmat_sub (X Y : ColourSpace) : cmat (X - Y) = cmat X - cmat Y := rfl

lemma cmat_star (X : ColourSpace) : star (cmat X) = cmat X :=
  selfAdjoint.mem_iff.mp (X : selfAdjoint (Matrix (Fin 3) (Fin 3) ℂ)).2

lemma cmat_trace (X : ColourSpace) : trace (cmat X) = 0 := X.2

/-- Assemble a colour vector from a traceless hermitian matrix. -/
def mkCM (M : Matrix (Fin 3) (Fin 3) ℂ) (hs : star M = M) (ht : trace M = 0) : ColourSpace :=
  ⟨⟨M, selfAdjoint.mem_iff.mpr hs⟩, ht⟩

@[simp]
lemma cmat_mkCM (M : Matrix (Fin 3) (Fin 3) ℂ) (hs : star M = M) (ht : trace M = 0) :
    cmat (mkCM M hs ht) = M := rfl

/-- The hermitian colour bracket `i (M N - N M)`. The factor of `i` is what keeps the bracket
  inside the hermitian carrier; it is the same `i` that appears in the hermitian field strength. -/
def brMat (M N : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Complex.I • (M * N - N * M)

lemma brMat_star {M N : Matrix (Fin 3) (Fin 3) ℂ} (hM : star M = M) (hN : star N = N) :
    star (brMat M N) = brMat M N := by
  rw [brMat, star_smul, star_sub, star_mul, star_mul, hM, hN, Complex.star_def, Complex.conj_I,
    neg_smul, ← smul_neg, neg_sub]

lemma brMat_trace (M N : Matrix (Fin 3) (Fin 3) ℂ) : trace (brMat M N) = 0 := by
  rw [brMat, trace_smul, trace_sub, trace_mul_comm M N, sub_self, smul_zero]

lemma brMat_swap (M N : Matrix (Fin 3) (Fin 3) ℂ) : brMat M N = -brMat N M := by
  rw [brMat, brMat, ← smul_neg, neg_sub]

lemma brMat_self (M : Matrix (Fin 3) (Fin 3) ℂ) : brMat M M = 0 := by
  rw [brMat, sub_self, smul_zero]

/-- The colour bracket `X, Y ↦ i [X, Y]` on the traceless hermitian carrier. -/
noncomputable def br : ColourSpace →ₗ[ℝ] ColourSpace →ₗ[ℝ] ColourSpace :=
  LinearMap.mk₂ ℝ
    (fun X Y => mkCM (brMat (cmat X) (cmat Y))
      (brMat_star (cmat_star X) (cmat_star Y)) (brMat_trace _ _))
    (fun _ _ _ => cmat_injective (by
      simp only [cmat_mkCM, cmat_add, brMat, add_mul, mul_add]
      module))
    (fun _ _ _ => cmat_injective (by
      simp only [cmat_mkCM, cmat_smul, brMat, Matrix.smul_mul, Matrix.mul_smul]
      module))
    (fun _ _ _ => cmat_injective (by
      simp only [cmat_mkCM, cmat_add, brMat, add_mul, mul_add]
      module))
    (fun _ _ _ => cmat_injective (by
      simp only [cmat_mkCM, cmat_smul, brMat, Matrix.smul_mul, Matrix.mul_smul]
      module))

@[simp]
lemma cmat_br (X Y : ColourSpace) : cmat (br X Y) = brMat (cmat X) (cmat Y) := rfl

lemma br_swap (X Y : ColourSpace) : br X Y = -br Y X :=
  cmat_injective (by
    rw [cmat_br, brMat_swap]
    show _ = cmat (-br Y X)
    rw [show cmat (-br Y X) = -cmat (br Y X) from rfl, cmat_br])

lemma br_self (X : ColourSpace) : br X X = 0 :=
  cmat_injective (by rw [cmat_br, brMat_self, cmat_zero])

/-!

## C. Colour coordinates and structure constants

-/

/-- The `c`-th coordinate of a colour vector relative to `colourBasis`, as a linear
  functional. -/
noncomputable def coordC (c : Col) : ColourSpace →ₗ[ℝ] ℝ where
  toFun X := colourBasis.repr X c
  map_add' X Y := by simp
  map_smul' r X := by simp

@[simp]
lemma coordC_apply (c : Col) (X : ColourSpace) : coordC c X = colourBasis.repr X c := rfl

/-- The colour vector with prescribed coordinates. -/
noncomputable def mkC (f : Col → ℝ) : ColourSpace := colourBasis.equivFun.symm f

@[simp]
lemma coordC_mkC (f : Col → ℝ) (a : Col) : coordC a (mkC f) = f a :=
  congrFun (colourBasis.equivFun.apply_symm_apply f) a

lemma mkC_coordC (X : ColourSpace) : mkC (fun a => coordC a X) = X :=
  colourBasis.equivFun.symm_apply_apply X

lemma mkC_eq_sum (f : Col → ℝ) : mkC f = ∑ a, f a • colourBasis a :=
  Basis.equivFun_symm_apply _ _

/-- The structure constants of the colour bracket in the basis `colourBasis`. -/
noncomputable def cstruct (a b c : Col) : ℝ :=
  coordC c (br (colourBasis a) (colourBasis b))

lemma cstruct_swap (a b c : Col) : cstruct a b c = -cstruct b a c := by
  rw [cstruct, cstruct, br_swap, map_neg]

/-- **The colour bracket in coordinates.** -/
lemma coordC_br (X Y : ColourSpace) (c : Col) :
    coordC c (br X Y) = ∑ a, ∑ b, coordC a X * coordC b Y * cstruct a b c := by
  conv_lhs => rw [← colourBasis.sum_repr X, ← colourBasis.sum_repr Y]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    coordC_apply, cstruct, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-!

## D. Colour vectors of polynomials

A colour vector of polynomials is a function `Col → MvPolynomial ι ℝ`. The bracket lifts to such
vectors through the structure constants, and evaluation at a point of the coordinate space
intertwines the lifted bracket with `br`.

-/

section Poly

variable {ι σ τ : Type*}

/-- Any `ℝ`-algebra map between polynomial algebras fixes the constants. -/
lemma algHom_C (φ : MvPolynomial σ ℝ →ₐ[ℝ] MvPolynomial τ ℝ) (r : ℝ) :
    φ (C r) = C r := by
  rw [← algebraMap_eq, AlgHom.commutes, algebraMap_eq]

/-- The colour bracket of two colour vectors of polynomials. -/
noncomputable def brP (p q : Col → MvPolynomial ι ℝ) : Col → MvPolynomial ι ℝ :=
  fun c => ∑ a, ∑ b, C (cstruct a b c) * (p a * q b)

lemma brP_swap (p q : Col → MvPolynomial ι ℝ) (c : Col) : brP p q c = -brP q p c := by
  have key : (brP q p c : MvPolynomial ι ℝ) =
      ∑ a, ∑ b, -(C (cstruct a b c) * (p a * q b)) := by
    rw [brP, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [cstruct_swap b a c, map_neg]
    ring
  rw [key, brP]
  simp [Finset.sum_neg_distrib]

lemma brP_self (p : Col → MvPolynomial ι ℝ) (c : Col) : brP p p c = 0 := by
  have h : (2 : ℝ) • brP p p c = 0 := by
    rw [two_smul]
    nth_rewrite 1 [brP_swap p p c]
    exact neg_add_cancel _
  have h2 := congrArg (fun x : MvPolynomial ι ℝ => (2⁻¹ : ℝ) • x) h
  simpa [smul_smul] using h2

lemma algHom_brP (φ : MvPolynomial σ ℝ →ₐ[ℝ] MvPolynomial τ ℝ) (p q : Col → MvPolynomial σ ℝ)
    (c : Col) :
    φ (brP p q c) = brP (fun a => φ (p a)) (fun b => φ (q b)) c := by
  rw [brP, brP, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  exact Finset.sum_congr rfl fun b _ => by rw [map_mul, map_mul, algHom_C]

/-- **Evaluation intertwines the polynomial bracket with the colour bracket.** -/
lemma eval_brP (x : ι → ℝ) (p q : Col → MvPolynomial ι ℝ) (c : Col) :
    eval x (brP p q c) =
      coordC c (br (mkC fun a => eval x (p a)) (mkC fun b => eval x (q b))) := by
  rw [coordC_br]
  simp only [coordC_mkC]
  rw [brP, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, map_mul, eval_C]
  ring

end Poly

/-!

## E. The two coordinate systems

-/

/-- The connection colour vector in ordinary coordinates. -/
noncomputable def connOld (μ : Lor) : Col → A₁ := fun c => X (Coord.conn μ c)

/-- The connection colour vector in covariant coordinates. -/
noncomputable def connCov (μ : Lor) : Col → A₁cov := fun c => X (CovCoord.conn μ c)

/-- **The field strength in ordinary coordinates:**
  `F_{νμ}^c = (∂_ν A_μ)^c - (∂_μ A_ν)^c + (i [A_ν, A_μ])^c`. -/
noncomputable def curvPoly (ν μ : Lor) (c : Col) : A₁ :=
  X (Coord.der ν μ c) - X (Coord.der μ ν c) + brP (connOld ν) (connOld μ) c

lemma curvPoly_swap (ν μ : Lor) (c : Col) : curvPoly ν μ c = -curvPoly μ ν c := by
  rw [curvPoly, curvPoly, brP_swap (connOld μ) (connOld ν) c]
  ring

lemma curvPoly_self (ν : Lor) (c : Col) : curvPoly ν ν c = 0 := by
  rw [curvPoly, brP_self, sub_self, add_zero]

/-- The curvature variable of the covariant carrier, for an arbitrary ordered pair of directions:
  the variable itself on an increasing pair, minus the variable on a decreasing pair, and zero on
  the diagonal. This is what keeps the carrier free of antisymmetry relations. -/
noncomputable def curvVar (ν μ : Lor) (c : Col) : A₁cov :=
  if h : LorLT ν μ then X (CovCoord.curv ⟨(ν, μ), h⟩ c)
  else if h' : LorLT μ ν then -X (CovCoord.curv ⟨(μ, ν), h'⟩ c)
  else 0

lemma curvVar_swap (ν μ : Lor) (c : Col) : curvVar ν μ c = -curvVar μ ν c := by
  rw [curvVar, curvVar]
  by_cases h : LorLT ν μ
  · rw [dif_pos h, dif_neg (lorLT_asymm h), dif_pos h, neg_neg]
  · by_cases h' : LorLT μ ν
    · rw [dif_neg h, dif_pos h', dif_pos h']
    · rw [dif_neg h, dif_neg h', dif_neg h', dif_neg h, neg_zero]

lemma curvVar_of_lt {ν μ : Lor} (h : LorLT ν μ) (c : Col) :
    curvVar ν μ c = X (CovCoord.curv ⟨(ν, μ), h⟩ c) := by
  rw [curvVar, dif_pos h]

/-- The symmetric derivative coordinate of the covariant carrier, written in ordinary
  coordinates. -/
noncomputable def symOld (c : Col) : Sym2 Lor → A₁ :=
  Sym2.lift ⟨fun ν μ => (2⁻¹ : ℝ) • (X (Coord.der ν μ c) + X (Coord.der μ ν c)), by
    intro a b
    show (2⁻¹ : ℝ) • (X (Coord.der a b c) + X (Coord.der b a c)) =
      (2⁻¹ : ℝ) • (X (Coord.der b a c) + X (Coord.der a b c))
    rw [add_comm]⟩

@[simp]
lemma symOld_mk (c : Col) (ν μ : Lor) :
    symOld c s(ν, μ) = (2⁻¹ : ℝ) • (X (Coord.der ν μ c) + X (Coord.der μ ν c)) :=
  Sym2.lift_mk _ _ _

/-!

## F. The two substitutions

-/

/-- The ordinary coordinates written in covariant coordinates: the derivative coordinate splits
  as its symmetric part plus half the field strength, corrected by the commutator. -/
noncomputable def oldToNewGen : Coord → A₁cov
  | Coord.conn μ c => X (CovCoord.conn μ c)
  | Coord.der ν μ c =>
      X (CovCoord.sym s(ν, μ) c) +
        (2⁻¹ : ℝ) • (curvVar ν μ c - brP (connCov ν) (connCov μ) c)

/-- The covariant coordinates written in ordinary coordinates. -/
noncomputable def newToOldGen : CovCoord → A₁
  | CovCoord.conn μ c => X (Coord.conn μ c)
  | CovCoord.sym s c => symOld c s
  | CovCoord.curv q c => curvPoly q.1.1 q.1.2 c

/-- The substitution from ordinary to covariant coordinates. -/
noncomputable def oldToNew : A₁ →ₐ[ℝ] A₁cov := aeval oldToNewGen

/-- The substitution from covariant to ordinary coordinates. -/
noncomputable def newToOld : A₁cov →ₐ[ℝ] A₁ := aeval newToOldGen

@[simp]
lemma oldToNew_conn (μ : Lor) (c : Col) :
    oldToNew (X (Coord.conn μ c)) = X (CovCoord.conn μ c) := aeval_X _ _

@[simp]
lemma oldToNew_der (ν μ : Lor) (c : Col) :
    oldToNew (X (Coord.der ν μ c)) =
      X (CovCoord.sym s(ν, μ) c) +
        (2⁻¹ : ℝ) • (curvVar ν μ c - brP (connCov ν) (connCov μ) c) := aeval_X _ _

@[simp]
lemma newToOld_conn (μ : Lor) (c : Col) :
    newToOld (X (CovCoord.conn μ c)) = X (Coord.conn μ c) := aeval_X _ _

@[simp]
lemma newToOld_sym (s : Sym2 Lor) (c : Col) :
    newToOld (X (CovCoord.sym s c)) = symOld c s := aeval_X _ _

@[simp]
lemma newToOld_curv (q : CurvPair) (c : Col) :
    newToOld (X (CovCoord.curv q c)) = curvPoly q.1.1 q.1.2 c := aeval_X _ _

lemma newToOld_connCov (ν : Lor) : (fun a => newToOld (connCov ν a)) = connOld ν := by
  funext a
  exact newToOld_conn ν a

lemma oldToNew_connOld (ν : Lor) : (fun a => oldToNew (connOld ν a)) = connCov ν := by
  funext a
  exact oldToNew_conn ν a

lemma newToOld_brP_conn (ν μ : Lor) (c : Col) :
    newToOld (brP (connCov ν) (connCov μ) c) = brP (connOld ν) (connOld μ) c := by
  rw [algHom_brP, newToOld_connCov, newToOld_connCov]

lemma oldToNew_brP_conn (ν μ : Lor) (c : Col) :
    oldToNew (brP (connOld ν) (connOld μ) c) = brP (connCov ν) (connCov μ) c := by
  rw [algHom_brP, oldToNew_connOld, oldToNew_connOld]

/-- The inverse image of the curvature variable is the field strength, at every ordered pair. -/
lemma newToOld_curvVar (ν μ : Lor) (c : Col) :
    newToOld (curvVar ν μ c) = curvPoly ν μ c := by
  rw [curvVar]
  by_cases h : LorLT ν μ
  · rw [dif_pos h, newToOld_curv]
  · by_cases h' : LorLT μ ν
    · rw [dif_neg h, dif_pos h', map_neg, newToOld_curv, ← curvPoly_swap]
    · rw [dif_neg h, dif_neg h', map_zero]
      rcases lor_trichotomy ν μ with hlt | rfl | hgt
      · exact absurd hlt h
      · rw [curvPoly_self]
      · exact absurd hgt h'

/-!

## G. The coordinate change is invertible

-/

lemma newToOld_oldToNew (i : Coord) : newToOld (oldToNew (X i)) = X i := by
  cases i with
  | conn μ c => rw [oldToNew_conn, newToOld_conn]
  | der ν μ c =>
      rw [oldToNew_der, map_add, map_smul, map_sub, newToOld_sym, newToOld_curvVar,
        newToOld_brP_conn, symOld_mk, curvPoly]
      module

lemma oldToNew_newToOld (i : CovCoord) : oldToNew (newToOld (X i)) = X i := by
  cases i with
  | conn μ c => rw [newToOld_conn, oldToNew_conn]
  | sym s c =>
      induction s using Sym2.ind with
      | _ ν μ =>
        rw [newToOld_sym, symOld_mk, map_smul, map_add, oldToNew_der, oldToNew_der,
          Sym2.eq_swap (a := μ) (b := ν), curvVar_swap μ ν c,
          brP_swap (connCov μ) (connCov ν) c]
        module
  | curv q c =>
      obtain ⟨⟨ν, μ⟩, hq⟩ := q
      rw [newToOld_curv, curvPoly, map_add, map_sub, oldToNew_der, oldToNew_der,
        oldToNew_brP_conn, Sym2.eq_swap (a := μ) (b := ν), curvVar_swap μ ν c,
        brP_swap (connCov μ) (connCov ν) c, curvVar_of_lt hq]
      module

/-- **The first-order covariant coordinate change.** The ordinary first-order gluon jet algebra
  and the covariant one are the same algebra: the derivative block splits as its symmetric part
  together with the field strength, and the inverse substitution carries the nonabelian commutator
  correction. -/
noncomputable def covEquiv : A₁ ≃ₐ[ℝ] A₁cov :=
  AlgEquiv.ofAlgHom oldToNew newToOld
    (by refine algHom_ext fun i => ?_; rw [AlgHom.comp_apply, oldToNew_newToOld, AlgHom.id_apply])
    (by refine algHom_ext fun i => ?_; rw [AlgHom.comp_apply, newToOld_oldToNew, AlgHom.id_apply])

@[simp]
lemma covEquiv_apply (P : A₁) : covEquiv P = oldToNew P := rfl

@[simp]
lemma covEquiv_symm_apply (Q : A₁cov) : covEquiv.symm Q = newToOld Q := rfl

@[simp]
lemma newToOld_oldToNew_apply (P : A₁) : newToOld (oldToNew P) = P :=
  covEquiv.symm_apply_apply P

@[simp]
lemma oldToNew_newToOld_apply (Q : A₁cov) : oldToNew (newToOld Q) = Q :=
  covEquiv.apply_symm_apply Q

end SU3Jet

end StandardModel
