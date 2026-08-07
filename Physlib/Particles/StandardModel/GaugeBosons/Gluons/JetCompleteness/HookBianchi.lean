/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.Particles.StandardModel.GaugeBosons.Gluons.JetCompleteness.GaugeAction
/-!
# Second-order hook coordinates and the Bianchi identity

## i. Overview

This file extends the finite gluon-jet carrier through second ordinary derivatives.
The old second-order block is indexed by `Sym2 Lor × Lor`; the covariant block splits it into a
fully symmetric twenty-component block and twenty independent components of `D F`.

The displayed family `D_ρ F_νμ`, with `ν < μ`, has twenty-four members.  `HookIdx` omits
exactly the four members with `ρ < ν < μ`.  Those components are reconstructed by

```text
D_ρ F_νμ = D_ν F_ρμ - D_μ F_ρν.
```

## ii. Convention

The hermitian field strength of `CoordinateChange` is
`F_νμ = ∂_ν A_μ - ∂_μ A_ν + br(A_ν,A_μ)`, where
`br(M,N) = i (M N - N M)`.  The affine action `actPot` of `GaugeAction` forces the adjoint covariant
derivative used here:

```text
D_ρ F_νμ = ∂_ρ F_νμ + br(A_ρ,F_νμ)
           = ∂_ρ F_νμ + i [A_ρ,F_νμ].
```

No production declaration is changed by this file.
-/

@[expose] public section

namespace StandardModel

open Matrix Module MvPolynomial

namespace SU3Jet

/-!

## A. Independent finite index types

-/

/-- Three ranks in nondecreasing order, representing a completely symmetric Lorentz triple. -/
abbrev Sym3Idx : Type :=
  {t : Fin 4 × Fin 4 × Fin 4 // t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2}

/-- A three-input sorting network on `Fin 4`. -/
def sort3 (a b c : Fin 4) : Fin 4 × Fin 4 × Fin 4 :=
  let p := min a b
  let q := max a b
  let r := min q c
  let z := max q c
  (min p r, max p r, z)

lemma sort3_ordered (a b c : Fin 4) :
    (sort3 a b c).1 ≤ (sort3 a b c).2.1 ∧
      (sort3 a b c).2.1 ≤ (sort3 a b c).2.2 := by
  dsimp [sort3]
  constructor
  · exact min_le_max
  · apply max_le
    · exact (min_le_max.trans (le_max_left _ _))
    · exact (min_le_left _ _).trans (le_max_left _ _)

/-- The completely symmetric triple containing `ρ`, `ν`, and `μ`. -/
def sym3Key (ρ ν μ : Lor) : Sym3Idx :=
  ⟨sort3 (lorRank ρ) (lorRank ν) (lorRank μ), sort3_ordered _ _ _⟩

lemma sort3_of_ordered {a b c : Fin 4} (hab : a ≤ b) (hbc : b ≤ c) :
    sort3 a b c = (a, b, c) := by
  simp [sort3, min_eq_left hab, max_eq_right hab, min_eq_left hbc, max_eq_right hbc]

lemma sym3Key_components (t : Sym3Idx) :
    sym3Key (lorRank.symm t.1.1) (lorRank.symm t.1.2.1) (lorRank.symm t.1.2.2) = t := by
  apply Subtype.ext
  simp only [sym3Key, Equiv.apply_symm_apply]
  exact sort3_of_ordered t.2.1 t.2.2

lemma sym3Key_swap12 (ρ ν μ : Lor) : sym3Key ρ ν μ = sym3Key ν ρ μ := by
  apply Subtype.ext
  fin_cases ρ <;> fin_cases ν <;> fin_cases μ <;> rfl

lemma sym3Key_swap23 (ρ ν μ : Lor) : sym3Key ρ ν μ = sym3Key ρ μ ν := by
  apply Subtype.ext
  fin_cases ρ <;> fin_cases ν <;> fin_cases μ <;> rfl

lemma sym3Key_cycle (ρ ν μ : Lor) : sym3Key ρ ν μ = sym3Key ν μ ρ := by
  rw [sym3Key_swap12, sym3Key_swap23]

/-- The independent hook coordinates.  For an increasing curvature pair `ν < μ`, the
component with derivative index `ρ` is retained precisely when it is not the omitted member
`ρ < ν < μ`. -/
abbrev HookIdx : Type :=
  {p : Lor × CurvPair // ¬ LorLT p.1 p.2.1.1}

set_option maxRecDepth 20000 in
lemma card_sym3Idx : Fintype.card Sym3Idx = 20 := by decide

set_option maxRecDepth 20000 in
lemma card_hookIdx : Fintype.card HookIdx = 20 := by decide

set_option maxRecDepth 20000 in
lemma card_old_second_layer : Fintype.card (Sym2 Lor × Lor) = 40 := by decide

set_option maxRecDepth 20000 in
lemma card_cov_second_layer : Fintype.card (Sym3Idx ⊕ HookIdx) = 40 := by decide

/-!

## B. The two second-order polynomial carriers

-/

/-- Ordinary coordinates through second order.  The two derivative indices of `sec` are stored
as a symmetric pair. -/
inductive Coord2 where
  /-- The connection coordinate. -/
  | conn : Lor → Col → Coord2
  /-- The first ordinary derivative. -/
  | der : Lor → Lor → Col → Coord2
  /-- The second ordinary derivative, symmetric in its first two Lorentz indices. -/
  | sec : Sym2 Lor → Lor → Col → Coord2
deriving DecidableEq, Fintype

/-- Covariant coordinates through second order. -/
inductive CovCoord2 where
  /-- The connection coordinate. -/
  | conn : Lor → Col → CovCoord2
  /-- The symmetric first derivative. -/
  | sym1 : Sym2 Lor → Col → CovCoord2
  /-- The independent curvature coordinate. -/
  | curv : CurvPair → Col → CovCoord2
  /-- The completely symmetric second derivative. -/
  | sym2 : Sym3Idx → Col → CovCoord2
  /-- An independent covariant derivative of curvature. -/
  | hook : HookIdx → Col → CovCoord2
deriving DecidableEq, Fintype

/-- The ordinary polynomial algebra through second order. -/
abbrev A₂ : Type := MvPolynomial Coord2 ℝ

/-- The covariant polynomial algebra through second order. -/
abbrev A₂cov : Type := MvPolynomial CovCoord2 ℝ

set_option maxRecDepth 20000 in
lemma card_coord2 : Fintype.card Coord2 = 480 := by decide

set_option maxRecDepth 20000 in
lemma card_covCoord2 : Fintype.card CovCoord2 = 480 := by decide

/-!

## C. Bracket identities used by Bianchi

-/

/-- Jacobi for the hermitian colour bracket. -/
lemma br_jacobi (X Y Z : ColourSpace) :
    br X (br Y Z) - br Y (br X Z) + br Z (br X Y) = 0 := by
  apply cmat_injective
  ext i j
  simp only [cmat_add, cmat_sub, cmat_zero, cmat_br, brMat, Matrix.add_apply,
    Matrix.sub_apply, Matrix.zero_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_three]
  ring_nf

section PolyIdentities

variable { ι : Type* }

lemma brP_add_left (p q r : Col → MvPolynomial ι ℝ) (c : Col) :
    brP (fun a ↦ p a + q a) r c = brP p r c + brP q r c := by
  simp only [brP, add_mul, mul_add, Finset.sum_add_distrib]

lemma brP_add_right (p q r : Col → MvPolynomial ι ℝ) (c : Col) :
    brP p (fun a ↦ q a + r a) c = brP p q c + brP p r c := by
  simp only [brP, mul_add, Finset.sum_add_distrib]

lemma brP_sub_left (p q r : Col → MvPolynomial ι ℝ) (c : Col) :
    brP (fun a ↦ p a - q a) r c = brP p r c - brP q r c := by
  simp only [brP, sub_mul, mul_sub, Finset.sum_sub_distrib]

lemma brP_sub_right (p q r : Col → MvPolynomial ι ℝ) (c : Col) :
    brP p (fun a ↦ q a - r a) c = brP p q c - brP p r c := by
  simp only [brP, mul_sub, Finset.sum_sub_distrib]

lemma brP_neg_right (p q : Col → MvPolynomial ι ℝ) (c : Col) :
    brP p (fun a ↦ -q a) c = -brP p q c := by
  simp only [brP, mul_neg, Finset.sum_neg_distrib]

lemma mkC_eval_brP (x : ι → ℝ) (p q : Col → MvPolynomial ι ℝ) :
    mkC (fun c ↦ eval x (brP p q c)) =
      br (mkC fun a ↦ eval x (p a)) (mkC fun b ↦ eval x (q b)) := by
  rw [show (fun c ↦ eval x (brP p q c)) = fun c ↦
      coordC c (br (mkC fun a ↦ eval x (p a)) (mkC fun b ↦ eval x (q b))) from
    funext fun c ↦ eval_brP x p q c]
  exact mkC_coordC _

/-- Jacobi after lifting three colour vectors to polynomial coordinates. -/
lemma brP_jacobi (p q r : Col → MvPolynomial ι ℝ) (c : Col) :
    brP p (brP q r) c - brP q (brP p r) c + brP r (brP p q) c = 0 := by
  refine MvPolynomial.funext fun x ↦ ?_
  simp only [map_add, map_sub, map_zero]
  rw [eval_brP, eval_brP, eval_brP, mkC_eval_brP, mkC_eval_brP, mkC_eval_brP]
  simpa only [map_add, map_sub, map_zero] using congrArg (coordC c)
    (br_jacobi (mkC fun a ↦ eval x (p a)) (mkC fun a ↦ eval x (q a))
      (mkC fun a ↦ eval x (r a)))

end PolyIdentities

/-!

## D. Curvature and its covariant derivative in ordinary coordinates

-/

/-- The connection colour vector in the second-order ordinary carrier. -/
noncomputable def conn2Old (μ : Lor) : Col → A₂ := fun c ↦ X (Coord2.conn μ c)

/-- The first derivative colour vector in the second-order ordinary carrier. -/
noncomputable def der2Old (ρ μ : Lor) : Col → A₂ := fun c ↦ X (Coord2.der ρ μ c)

/-- A displayed second derivative in the ordinary carrier. -/
noncomputable def secAt (ρ ν μ : Lor) (c : Col) : A₂ := X (Coord2.sec s(ρ, ν) μ c)

lemma secAt_swap (ρ ν μ : Lor) (c : Col) : secAt ρ ν μ c = secAt ν ρ μ c := by
  rw [secAt, secAt, Sym2.eq_swap]

/-- The curvature polynomial in the second-order ordinary carrier. -/
noncomputable def curv2Poly (ν μ : Lor) (c : Col) : A₂ :=
  X (Coord2.der ν μ c) - X (Coord2.der μ ν c) + brP (conn2Old ν) (conn2Old μ) c

lemma curv2Poly_swap (ν μ : Lor) (c : Col) : curv2Poly ν μ c = -curv2Poly μ ν c := by
  rw [curv2Poly, curv2Poly, brP_swap (conn2Old μ) (conn2Old ν) c]
  ring_nf

lemma curv2Poly_self (ν : Lor) (c : Col) : curv2Poly ν ν c = 0 := by
  rw [curv2Poly, brP_self, sub_self, add_zero]

/-- The terms in `D_ρ F_νμ` below the leading second-derivative hook. -/
noncomputable def dFNonlin (ρ ν μ : Lor) : Col → A₂ := fun c ↦
  brP (der2Old ρ ν) (conn2Old μ) c +
    brP (conn2Old ν) (der2Old ρ μ) c +
    brP (conn2Old ρ) (curv2Poly ν μ) c

/-- The leading linear hook in the second ordinary derivative. -/
noncomputable def leadHook (ρ ν μ : Lor) : Col → A₂ :=
  fun c ↦ secAt ρ ν μ c - secAt ρ μ ν c

/-- The covariant derivative
`D_ρ F_νμ = ∂_ρ F_νμ + br(A_ρ,F_νμ)` in ordinary coordinates. -/
noncomputable def dFPoly (ρ ν μ : Lor) : Col → A₂ :=
  fun c ↦ leadHook ρ ν μ c + dFNonlin ρ ν μ c

lemma leadHook_swap (ρ ν μ : Lor) (c : Col) :
    leadHook ρ ν μ c = -leadHook ρ μ ν c := by
  rw [leadHook, leadHook]
  ring_nf

lemma leadHook_bianchi (ρ ν μ : Lor) (c : Col) :
    leadHook ρ ν μ c - leadHook ν ρ μ c + leadHook μ ρ ν c = 0 := by
  rw [leadHook, leadHook, leadHook, secAt_swap ν ρ, secAt_swap μ ρ,
    secAt_swap μ ν]
  ring_nf

lemma dFNonlin_swap (ρ ν μ : Lor) (c : Col) :
    dFNonlin ρ ν μ c = -dFNonlin ρ μ ν c := by
  rw [dFNonlin, dFNonlin]
  rw [brP_swap (der2Old ρ ν) (conn2Old μ) c,
    brP_swap (der2Old ρ μ) (conn2Old ν) c]
  have hcurv : curv2Poly ν μ = fun a ↦ -curv2Poly μ ν a := by
    funext a
    exact curv2Poly_swap ν μ a
  rw [hcurv, brP_neg_right]
  ring_nf

/-- The nonlinear terms obey the cyclic identity by Jacobi. -/
lemma dFNonlin_bianchi (ρ ν μ : Lor) (c : Col) :
    dFNonlin ρ ν μ c - dFNonlin ν ρ μ c + dFNonlin μ ρ ν c = 0 := by
  simp only [dFNonlin]
  change
    (brP (der2Old ρ ν) (conn2Old μ) c + brP (conn2Old ν) (der2Old ρ μ) c +
      brP (conn2Old ρ) (fun a ↦ der2Old ν μ a - der2Old μ ν a +
        brP (conn2Old ν) (conn2Old μ) a) c) -
    (brP (der2Old ν ρ) (conn2Old μ) c + brP (conn2Old ρ) (der2Old ν μ) c +
      brP (conn2Old ν) (fun a ↦ der2Old ρ μ a - der2Old μ ρ a +
        brP (conn2Old ρ) (conn2Old μ) a) c) +
    (brP (der2Old μ ρ) (conn2Old ν) c + brP (conn2Old ρ) (der2Old μ ν) c +
      brP (conn2Old μ) (fun a ↦ der2Old ρ ν a - der2Old ν ρ a +
        brP (conn2Old ρ) (conn2Old ν) a) c) = 0
  rw [brP_add_right, brP_sub_right, brP_add_right, brP_sub_right, brP_add_right,
    brP_sub_right]
  rw [brP_swap (conn2Old μ) (der2Old ρ ν) c,
    brP_swap (conn2Old μ) (der2Old ν ρ) c,
    brP_swap (der2Old μ ρ) (conn2Old ν) c]
  have hj := brP_jacobi (conn2Old ρ) (conn2Old ν) (conn2Old μ) c
  linear_combination (norm := ring_nf) hj

/-- Antisymmetry of the covariant derivative in its curvature indices. -/
lemma dFPoly_swap (ρ ν μ : Lor) (c : Col) : dFPoly ρ ν μ c = -dFPoly ρ μ ν c := by
  rw [dFPoly, dFPoly, leadHook_swap, dFNonlin_swap]
  ring_nf

/-- The algebraic Bianchi identity in ordinary polynomial coordinates. -/
lemma dFPoly_bianchi (ρ ν μ : Lor) (c : Col) :
    dFPoly ρ ν μ c - dFPoly ν ρ μ c + dFPoly μ ρ ν c = 0 := by
  rw [dFPoly, dFPoly, dFPoly]
  linear_combination (norm := ring_nf)
    leadHook_bianchi ρ ν μ c + dFNonlin_bianchi ρ ν μ c

/-!

## E. Reconstructing all displayed hook components

-/

/-- A retained hook variable, or the Bianchi reconstruction when the displayed component was
omitted.  Its curvature pair is already increasing. -/
noncomputable def hookInc (ρ : Lor) (q : CurvPair) (c : Col) : A₂cov :=
  if h : LorLT ρ q.1.1 then
    X (CovCoord2.hook
        ⟨(q.1.1, ⟨(ρ, q.1.2), lt_trans h q.2⟩), lorLT_asymm h⟩ c) -
      X (CovCoord2.hook
        ⟨(q.1.2, ⟨(ρ, q.1.1), h⟩), lorLT_asymm (lt_trans h q.2)⟩ c)
  else X (CovCoord2.hook ⟨(ρ, q), h⟩ c)

/-- The covariant-coordinate polynomial representing `D_ρ F_νμ` for an arbitrary ordered
curvature pair. -/
noncomputable def hookVar (ρ ν μ : Lor) (c : Col) : A₂cov :=
  if h : LorLT ν μ then hookInc ρ ⟨(ν, μ), h⟩ c
  else if h' : LorLT μ ν then -hookInc ρ ⟨(μ, ν), h'⟩ c
  else 0

lemma hookVar_swap (ρ ν μ : Lor) (c : Col) : hookVar ρ ν μ c = -hookVar ρ μ ν c := by
  rw [hookVar, hookVar]
  by_cases h : LorLT ν μ
  · rw [dif_pos h, dif_neg (lorLT_asymm h), dif_pos h, neg_neg]
  · by_cases h' : LorLT μ ν
    · rw [dif_neg h, dif_pos h', dif_pos h']
    · rw [dif_neg h, dif_neg h', dif_neg h', dif_neg h, neg_zero]

lemma hookVar_self (ρ ν : Lor) (c : Col) : hookVar ρ ν ν c = 0 := by
  simp [hookVar, lorLT_irrefl]

/-- The omitted component for `ρ < ν < μ` is reconstructed from the two retained components. -/
lemma hookVar_reconstruct { ρ ν μ : Lor } (hρν : LorLT ρ ν) (hνμ : LorLT ν μ) (c : Col) :
    hookVar ρ ν μ c = hookVar ν ρ μ c - hookVar μ ρ ν c := by
  have hρμ : LorLT ρ μ := lt_trans hρν hνμ
  simp only [hookVar, dif_pos hνμ, hookInc, dif_pos hρν, dif_pos hρμ,
    dif_neg (lorLT_asymm hρν), dif_neg (lorLT_asymm hρμ)]

private lemma hookVar_bianchi_of_lt {ρ ν : Lor} (hρν : LorLT ρ ν) (μ : Lor) (c : Col) :
    hookVar ρ ν μ c - hookVar ν ρ μ c + hookVar μ ρ ν c = 0 := by
  rcases lor_trichotomy ν μ with hνμ | rfl | hμν
  · rw [hookVar_reconstruct hρν hνμ]
    ring_nf
  · rw [hookVar_self]
    ring_nf
  · rcases lor_trichotomy ρ μ with hρμ | rfl | hμρ
    · have hr := hookVar_reconstruct hρμ hμν c
      rw [hookVar_swap ρ ν μ]
      rw [hr]
      ring_nf
    · rw [hookVar_self, hookVar_swap ρ ν ρ]
      ring_nf
    · have hr := hookVar_reconstruct hμρ hρν c
      rw [hookVar_swap ρ ν μ, hookVar_swap ν ρ μ]
      linear_combination (norm := ring_nf) hr

/-- Bianchi for the reconstructed covariant-coordinate hook family. -/
lemma hookVar_bianchi (ρ ν μ : Lor) (c : Col) :
    hookVar ρ ν μ c - hookVar ν ρ μ c + hookVar μ ρ ν c = 0 := by
  rcases lor_trichotomy ρ ν with hρν | rfl | hνρ
  · exact hookVar_bianchi_of_lt hρν μ c
  · rw [hookVar_self]
    ring_nf
  · have h := hookVar_bianchi_of_lt hνρ μ c
    rw [hookVar_swap μ ν ρ] at h
    linear_combination (norm := ring_nf) -h

/-!

## F. The nonlinear triangular substitutions

-/

/-- The connection colour vector in covariant coordinates. -/
noncomputable def conn2Cov (μ : Lor) : Col → A₂cov := fun c ↦ X (CovCoord2.conn μ c)

/-- The curvature variable in the covariant carrier, extended antisymmetrically to every pair. -/
noncomputable def curv2Var (ν μ : Lor) (c : Col) : A₂cov :=
  if h : LorLT ν μ then X (CovCoord2.curv ⟨(ν, μ), h⟩ c)
  else if h' : LorLT μ ν then -X (CovCoord2.curv ⟨(μ, ν), h'⟩ c)
  else 0

lemma curv2Var_swap (ν μ : Lor) (c : Col) : curv2Var ν μ c = -curv2Var μ ν c := by
  rw [curv2Var, curv2Var]
  by_cases h : LorLT ν μ
  · rw [dif_pos h, dif_neg (lorLT_asymm h), dif_pos h, neg_neg]
  · by_cases h' : LorLT μ ν
    · rw [dif_neg h, dif_pos h', dif_pos h']
    · rw [dif_neg h, dif_neg h', dif_neg h', dif_neg h, neg_zero]

/-- A first derivative written in the lower covariant coordinates. -/
noncomputable def der2Cov (ν μ : Lor) : Col → A₂cov := fun c ↦
  X (CovCoord2.sym1 s(ν, μ) c) +
    (2⁻¹ : ℝ) • (curv2Var ν μ c - brP (conn2Cov ν) (conn2Cov μ) c)

/-- The lower-order nonlinear part of `D_ρ F_νμ` in covariant coordinates. -/
noncomputable def dFNonlinCov (ρ ν μ : Lor) : Col → A₂cov := fun c ↦
  brP (der2Cov ρ ν) (conn2Cov μ) c +
    brP (conn2Cov ν) (der2Cov ρ μ) c +
    brP (conn2Cov ρ) (curv2Var ν μ) c

lemma dFNonlinCov_swap (ρ ν μ : Lor) (c : Col) :
    dFNonlinCov ρ ν μ c = -dFNonlinCov ρ μ ν c := by
  rw [dFNonlinCov, dFNonlinCov]
  rw [brP_swap (der2Cov ρ ν) (conn2Cov μ) c,
    brP_swap (der2Cov ρ μ) (conn2Cov ν) c]
  have hcurv : curv2Var ν μ = fun a ↦ -curv2Var μ ν a := by
    funext a
    exact curv2Var_swap ν μ a
  rw [hcurv, brP_neg_right]
  ring_nf

/-- The completely symmetric average of an ordinary second derivative. -/
noncomputable def sym3Average (ρ ν μ : Lor) (c : Col) : A₂ :=
  (3⁻¹ : ℝ) • (secAt ρ ν μ c + secAt ρ μ ν c + secAt ν μ ρ c)

/-- A completely symmetric covariant generator written in ordinary coordinates. -/
noncomputable def sym3Old (t : Sym3Idx) (c : Col) : A₂ :=
  sym3Average (lorRank.symm t.1.1) (lorRank.symm t.1.2.1) (lorRank.symm t.1.2.2) c

lemma sym3Average_swap12 (ρ ν μ : Lor) (c : Col) :
    sym3Average ρ ν μ c = sym3Average ν ρ μ c := by
  rw [sym3Average, sym3Average, secAt_swap ν ρ]
  ring_nf

lemma sym3Average_swap23 (ρ ν μ : Lor) (c : Col) :
    sym3Average ρ ν μ c = sym3Average ρ μ ν c := by
  rw [sym3Average, sym3Average, secAt_swap μ ν]
  ring_nf

private lemma sym3Average_sort3Ranks (a b d : Fin 4) (c : Col) :
    sym3Average (lorRank.symm (sort3 a b d).1)
        (lorRank.symm (sort3 a b d).2.1) (lorRank.symm (sort3 a b d).2.2) c =
      sym3Average (lorRank.symm a) (lorRank.symm b) (lorRank.symm d) c := by
  let p := min a b
  let q := max a b
  let r := min q d
  let z := max q d
  calc
    sym3Average (lorRank.symm (sort3 a b d).1)
        (lorRank.symm (sort3 a b d).2.1) (lorRank.symm (sort3 a b d).2.2) c =
        sym3Average (lorRank.symm (min p r)) (lorRank.symm (max p r))
          (lorRank.symm z) c := by rfl
    _ = sym3Average (lorRank.symm p) (lorRank.symm r) (lorRank.symm z) c := by
      by_cases h : p ≤ r
      · rw [min_eq_left h, max_eq_right h]
      · rw [min_eq_right (le_of_not_ge h), max_eq_left (le_of_not_ge h)]
        exact sym3Average_swap12 _ _ _ _
    _ = sym3Average (lorRank.symm p) (lorRank.symm q) (lorRank.symm d) c := by
      by_cases h : q ≤ d
      · rw [show r = q from min_eq_left h, show z = d from max_eq_right h]
      · rw [show r = d from min_eq_right (le_of_not_ge h),
          show z = q from max_eq_left (le_of_not_ge h)]
        exact sym3Average_swap23 _ _ _ _
    _ = sym3Average (lorRank.symm a) (lorRank.symm b) (lorRank.symm d) c := by
      by_cases h : a ≤ b
      · rw [show p = a from min_eq_left h, show q = b from max_eq_right h]
      · rw [show p = b from min_eq_right (le_of_not_ge h),
          show q = a from max_eq_left (le_of_not_ge h)]
        exact sym3Average_swap12 _ _ _ _

lemma sym3Old_key (ρ ν μ : Lor) (c : Col) :
    sym3Old (sym3Key ρ ν μ) c = sym3Average ρ ν μ c := by
  change sym3Average (lorRank.symm (sort3 (lorRank ρ) (lorRank ν) (lorRank μ)).1)
      (lorRank.symm (sort3 (lorRank ρ) (lorRank ν) (lorRank μ)).2.1)
      (lorRank.symm (sort3 (lorRank ρ) (lorRank ν) (lorRank μ)).2.2) c = _
  simpa using sym3Average_sort3Ranks (lorRank ρ) (lorRank ν) (lorRank μ) c

/-- The leading linear decomposition of a second ordinary derivative. -/
lemma leading_hook_decomposition (ρ ν μ : Lor) (c : Col) :
    secAt ρ ν μ c = sym3Old (sym3Key ρ ν μ) c +
      (3⁻¹ : ℝ) • (leadHook ρ ν μ c + leadHook ν ρ μ c) := by
  rw [sym3Old_key, sym3Average, leadHook, leadHook, secAt_swap ν ρ]
  module

/-- Ordinary generators written in covariant coordinates. -/
noncomputable def oldToNew2Gen : Coord2 → A₂cov
  | Coord2.conn μ c => X (CovCoord2.conn μ c)
  | Coord2.der ν μ c => der2Cov ν μ c
  | Coord2.sec s μ c =>
      Sym2.lift ⟨fun ρ ν ↦
        X (CovCoord2.sym2 (sym3Key ρ ν μ) c) +
          (3⁻¹ : ℝ) •
            ((hookVar ρ ν μ c - dFNonlinCov ρ ν μ c) +
              (hookVar ν ρ μ c - dFNonlinCov ν ρ μ c)), by
        intro ρ ν
        dsimp
        rw [sym3Key_swap12]
        ring_nf⟩ s

/-- Covariant generators written in ordinary coordinates. -/
noncomputable def newToOld2Gen : CovCoord2 → A₂
  | CovCoord2.conn μ c => X (Coord2.conn μ c)
  | CovCoord2.sym1 s c =>
      Sym2.lift ⟨fun ν μ ↦ (2⁻¹ : ℝ) •
        (X (Coord2.der ν μ c) + X (Coord2.der μ ν c)), by
        intro ν μ
        dsimp
        rw [add_comm]⟩ s
  | CovCoord2.curv q c => curv2Poly q.1.1 q.1.2 c
  | CovCoord2.sym2 t c => sym3Old t c
  | CovCoord2.hook i c => dFPoly i.1.1 i.1.2.1.1 i.1.2.1.2 c

/-- The triangular substitution from ordinary to covariant coordinates. -/
noncomputable def oldToNew2 : A₂ →ₐ[ℝ] A₂cov := aeval oldToNew2Gen

/-- The triangular substitution from covariant to ordinary coordinates. -/
noncomputable def newToOld2 : A₂cov →ₐ[ℝ] A₂ := aeval newToOld2Gen

@[simp] lemma oldToNew2_conn (μ : Lor) (c : Col) :
    oldToNew2 (X (Coord2.conn μ c)) = X (CovCoord2.conn μ c) := aeval_X _ _

@[simp] lemma oldToNew2_der (ν μ : Lor) (c : Col) :
    oldToNew2 (X (Coord2.der ν μ c)) = der2Cov ν μ c := aeval_X _ _

@[simp] lemma oldToNew2_sec (ρ ν μ : Lor) (c : Col) :
    oldToNew2 (secAt ρ ν μ c) =
      X (CovCoord2.sym2 (sym3Key ρ ν μ) c) +
        (3⁻¹ : ℝ) •
          ((hookVar ρ ν μ c - dFNonlinCov ρ ν μ c) +
            (hookVar ν ρ μ c - dFNonlinCov ν ρ μ c)) := by
  rw [secAt, oldToNew2, aeval_X, oldToNew2Gen, Sym2.lift_mk]

@[simp] lemma newToOld2_conn (μ : Lor) (c : Col) :
    newToOld2 (X (CovCoord2.conn μ c)) = X (Coord2.conn μ c) := aeval_X _ _

@[simp] lemma newToOld2_sym1 (ν μ : Lor) (c : Col) :
    newToOld2 (X (CovCoord2.sym1 s(ν, μ) c)) =
      (2⁻¹ : ℝ) • (X (Coord2.der ν μ c) + X (Coord2.der μ ν c)) := by
  rw [newToOld2, aeval_X, newToOld2Gen, Sym2.lift_mk]

@[simp] lemma newToOld2_curv (q : CurvPair) (c : Col) :
    newToOld2 (X (CovCoord2.curv q c)) = curv2Poly q.1.1 q.1.2 c := aeval_X _ _

@[simp] lemma newToOld2_sym2 (t : Sym3Idx) (c : Col) :
    newToOld2 (X (CovCoord2.sym2 t c)) = sym3Old t c := aeval_X _ _

@[simp] lemma newToOld2_hook (i : HookIdx) (c : Col) :
    newToOld2 (X (CovCoord2.hook i c)) = dFPoly i.1.1 i.1.2.1.1 i.1.2.1.2 c := aeval_X _ _

lemma oldToNew2_conn2Old (μ : Lor) : (fun c ↦ oldToNew2 (conn2Old μ c)) = conn2Cov μ := by
  funext c
  exact oldToNew2_conn μ c

lemma newToOld2_conn2Cov (μ : Lor) : (fun c ↦ newToOld2 (conn2Cov μ c)) = conn2Old μ := by
  funext c
  exact newToOld2_conn μ c

lemma newToOld2_curv2Var (ν μ : Lor) (c : Col) :
    newToOld2 (curv2Var ν μ c) = curv2Poly ν μ c := by
  rw [curv2Var]
  by_cases h : LorLT ν μ
  · rw [dif_pos h, newToOld2_curv]
  · by_cases h' : LorLT μ ν
    · rw [dif_neg h, dif_pos h', map_neg, newToOld2_curv, ← curv2Poly_swap]
    · rw [dif_neg h, dif_neg h', map_zero]
      rcases lor_trichotomy ν μ with hlt | rfl | hgt
      · exact absurd hlt h
      · rw [curv2Poly_self]
      · exact absurd hgt h'

lemma newToOld2_der2Cov (ν μ : Lor) :
    (fun c ↦ newToOld2 (der2Cov ν μ c)) = der2Old ν μ := by
  funext c
  rw [der2Cov, map_add, map_smul, map_sub, newToOld2_sym1, newToOld2_curv2Var,
    algHom_brP, newToOld2_conn2Cov, newToOld2_conn2Cov, curv2Poly]
  simp only [der2Old]
  norm_num
  module

lemma oldToNew2_curv2Poly (ν μ : Lor) (c : Col) :
    oldToNew2 (curv2Poly ν μ c) = curv2Var ν μ c := by
  rw [curv2Poly, map_add, map_sub, oldToNew2_der, oldToNew2_der, algHom_brP,
    oldToNew2_conn2Old, oldToNew2_conn2Old, der2Cov, der2Cov,
    Sym2.eq_swap (a := μ) (b := ν), curv2Var_swap μ ν c,
    brP_swap (conn2Cov μ) (conn2Cov ν) c]
  module

lemma newToOld2_dFNonlinCov (ρ ν μ : Lor) :
    (fun c ↦ newToOld2 (dFNonlinCov ρ ν μ c)) = dFNonlin ρ ν μ := by
  funext c
  rw [dFNonlinCov, dFNonlin, map_add, map_add, algHom_brP, algHom_brP, algHom_brP,
    newToOld2_der2Cov, newToOld2_der2Cov, newToOld2_conn2Cov,
    newToOld2_conn2Cov, newToOld2_conn2Cov]
  have hcurv : (fun b ↦ newToOld2 (curv2Var ν μ b)) = curv2Poly ν μ := by
    funext b
    exact newToOld2_curv2Var ν μ b
  rw [hcurv]

lemma oldToNew2_dFNonlin (ρ ν μ : Lor) :
    (fun c ↦ oldToNew2 (dFNonlin ρ ν μ c)) = dFNonlinCov ρ ν μ := by
  funext c
  rw [dFNonlin, dFNonlinCov, map_add, map_add, algHom_brP, algHom_brP, algHom_brP,
    oldToNew2_conn2Old, oldToNew2_conn2Old, oldToNew2_conn2Old]
  have hder₁ : (fun a ↦ oldToNew2 (der2Old ρ ν a)) = der2Cov ρ ν := by
    funext a
    exact oldToNew2_der ρ ν a
  have hder₂ : (fun a ↦ oldToNew2 (der2Old ρ μ a)) = der2Cov ρ μ := by
    funext a
    exact oldToNew2_der ρ μ a
  have hcurv : (fun b ↦ oldToNew2 (curv2Poly ν μ b)) = curv2Var ν μ := by
    funext b
    exact oldToNew2_curv2Poly ν μ b
  rw [hder₁, hder₂, hcurv]

lemma newToOld2_hookInc (ρ : Lor) (q : CurvPair) (c : Col) :
    newToOld2 (hookInc ρ q c) = dFPoly ρ q.1.1 q.1.2 c := by
  obtain ⟨⟨ν, μ⟩, hνμ⟩ := q
  rw [hookInc]
  by_cases h : LorLT ρ ν
  · rw [dif_pos h, map_sub, newToOld2_hook, newToOld2_hook]
    have hb := dFPoly_bianchi ρ ν μ c
    linear_combination (norm := ring_nf) -hb
  · rw [dif_neg h, newToOld2_hook]

lemma newToOld2_hookVar (ρ ν μ : Lor) (c : Col) :
    newToOld2 (hookVar ρ ν μ c) = dFPoly ρ ν μ c := by
  rw [hookVar]
  by_cases h : LorLT ν μ
  · rw [dif_pos h, newToOld2_hookInc]
  · by_cases h' : LorLT μ ν
    · rw [dif_neg h, dif_pos h', map_neg, newToOld2_hookInc, ← dFPoly_swap]
    · rw [dif_neg h, dif_neg h', map_zero]
      rcases lor_trichotomy ν μ with hlt | rfl | hgt
      · exact absurd hlt h
      · have hs := dFPoly_swap ρ ν ν c
        have htwo : (2 : ℝ) • dFPoly ρ ν ν c = 0 := by
          rw [two_smul]
          nth_rewrite 1 [hs]
          exact neg_add_cancel _
        have hhalf := congrArg (fun x : A₂ ↦ (2⁻¹ : ℝ) • x) htwo
        symm
        simpa [smul_smul] using hhalf
      · exact absurd hgt h'

lemma newToOld2_oldToNew2 (i : Coord2) : newToOld2 (oldToNew2 (X i)) = X i := by
  cases i with
  | conn μ c => rw [oldToNew2_conn, newToOld2_conn]
  | der ν μ c =>
      rw [oldToNew2_der]
      exact congrFun (newToOld2_der2Cov ν μ) c
  | sec s μ c =>
      induction s using Sym2.ind with
      | _ ρ ν =>
        rw [← secAt, oldToNew2_sec, map_add, map_smul, map_add, map_sub, map_sub,
          newToOld2_sym2, newToOld2_hookVar, newToOld2_hookVar,
          congrFun (newToOld2_dFNonlinCov ρ ν μ) c,
          congrFun (newToOld2_dFNonlinCov ν ρ μ) c,
          dFPoly, dFPoly]
        calc
          sym3Old (sym3Key ρ ν μ) c +
                (3⁻¹ : ℝ) •
                  (leadHook ρ ν μ c + dFNonlin ρ ν μ c - dFNonlin ρ ν μ c +
                    (leadHook ν ρ μ c + dFNonlin ν ρ μ c - dFNonlin ν ρ μ c)) =
              sym3Old (sym3Key ρ ν μ) c +
                (3⁻¹ : ℝ) • (leadHook ρ ν μ c + leadHook ν ρ μ c) := by
                  module
          _ = secAt ρ ν μ c := (leading_hook_decomposition ρ ν μ c).symm

/- The remaining direction is proved after two triangular identities below. -/

lemma dFNonlinCov_bianchi (ρ ν μ : Lor) (c : Col) :
    dFNonlinCov ρ ν μ c - dFNonlinCov ν ρ μ c +
      dFNonlinCov μ ρ ν c = 0 := by
  have h := congrArg oldToNew2 (dFNonlin_bianchi ρ ν μ c)
  simpa only [map_add, map_sub, map_zero, congrFun (oldToNew2_dFNonlin ρ ν μ) c,
    congrFun (oldToNew2_dFNonlin ν ρ μ) c,
    congrFun (oldToNew2_dFNonlin μ ρ ν) c] using h

private lemma triangular_hook_sub (S a b d na nb nd : A₂cov)
    (ha : a - b + d = 0) (hn : na - nb + nd = 0) :
    (S + (3⁻¹ : ℝ) • ((a - na) + (b - nb))) -
        (S + (3⁻¹ : ℝ) • ((-a - -na) + (d - nd))) = a - na := by
  have hb : b = a + d := by
    linear_combination (norm := ring_nf) -ha
  have hnb : nb = na + nd := by
    linear_combination (norm := ring_nf) -hn
  rw [hb, hnb]
  norm_num
  module

lemma oldToNew2_leadHook (ρ ν μ : Lor) (c : Col) :
    oldToNew2 (leadHook ρ ν μ c) =
      hookVar ρ ν μ c - dFNonlinCov ρ ν μ c := by
  have hs : (X (CovCoord2.sym2 (sym3Key ρ μ ν) c) : A₂cov) =
      X (CovCoord2.sym2 (sym3Key ρ ν μ) c) := by
    rw [sym3Key_swap23]
  rw [leadHook, map_sub, oldToNew2_sec, oldToNew2_sec, hs,
    hookVar_swap ρ μ ν, dFNonlinCov_swap ρ μ ν]
  have hh := hookVar_bianchi ρ ν μ c
  have hn := dFNonlinCov_bianchi ρ ν μ c
  exact triangular_hook_sub _ _ _ _ _ _ _ hh hn

lemma oldToNew2_dFPoly (ρ ν μ : Lor) (c : Col) :
    oldToNew2 (dFPoly ρ ν μ c) = hookVar ρ ν μ c := by
  rw [dFPoly, map_add, oldToNew2_leadHook,
    congrFun (oldToNew2_dFNonlin ρ ν μ) c]
  abel

lemma oldToNew2_sym3Average (ρ ν μ : Lor) (c : Col) :
    oldToNew2 (sym3Average ρ ν μ c) = X (CovCoord2.sym2 (sym3Key ρ ν μ) c) := by
  have hs₁ : (X (CovCoord2.sym2 (sym3Key ρ μ ν) c) : A₂cov) =
      X (CovCoord2.sym2 (sym3Key ρ ν μ) c) := by
    exact congrArg (fun t ↦ (X (CovCoord2.sym2 t c) : A₂cov)) (sym3Key_swap23 ρ ν μ).symm
  have hs₂ : (X (CovCoord2.sym2 (sym3Key ν μ ρ) c) : A₂cov) =
      X (CovCoord2.sym2 (sym3Key ρ ν μ) c) := by
    exact congrArg (fun t ↦ (X (CovCoord2.sym2 t c) : A₂cov)) (sym3Key_cycle ρ ν μ).symm
  rw [sym3Average, map_smul, map_add, map_add, oldToNew2_sec, oldToNew2_sec,
    oldToNew2_sec, hs₁, hs₂,
    hookVar_swap ρ μ ν, dFNonlinCov_swap ρ μ ν,
    hookVar_swap ν μ ρ, dFNonlinCov_swap ν μ ρ,
    hookVar_swap μ ν ρ, dFNonlinCov_swap μ ν ρ]
  norm_num
  module

lemma oldToNew2_sym3Old (t : Sym3Idx) (c : Col) :
    oldToNew2 (sym3Old t c) = X (CovCoord2.sym2 t c) := by
  rw [sym3Old, oldToNew2_sym3Average, sym3Key_components]

lemma oldToNew2_hookInc (ρ : Lor) (q : CurvPair) (c : Col) :
    oldToNew2 (dFPoly ρ q.1.1 q.1.2 c) = hookInc ρ q c := by
  rw [oldToNew2_dFPoly, hookVar]
  exact dif_pos q.2

lemma oldToNew2_newToOld2 (i : CovCoord2) : oldToNew2 (newToOld2 (X i)) = X i := by
  cases i with
  | conn μ c => rw [newToOld2_conn, oldToNew2_conn]
  | sym1 s c =>
      induction s using Sym2.ind with
      | _ ν μ =>
        rw [newToOld2_sym1, map_smul, map_add, oldToNew2_der, oldToNew2_der,
          der2Cov, der2Cov, Sym2.eq_swap (a := μ) (b := ν), curv2Var_swap μ ν c,
          brP_swap (conn2Cov μ) (conn2Cov ν) c]
        module
  | curv q c =>
      rw [newToOld2_curv, oldToNew2_curv2Poly, curv2Var]
      exact dif_pos q.2
  | sym2 t c => rw [newToOld2_sym2, oldToNew2_sym3Old]
  | hook i c =>
      obtain ⟨⟨ρ, q⟩, hi⟩ := i
      rw [newToOld2_hook, oldToNew2_hookInc, hookInc, dif_neg hi]

/-!

## G. The second-order coordinate equivalence

-/

/-- The second-order ordinary and covariant polynomial presentations are isomorphic. -/
noncomputable def covEquiv2 : A₂ ≃ₐ[ℝ] A₂cov :=
  AlgEquiv.ofAlgHom oldToNew2 newToOld2
    (by refine algHom_ext fun i ↦ ?_; rw [AlgHom.comp_apply, oldToNew2_newToOld2, AlgHom.id_apply])
    (by refine algHom_ext fun i ↦ ?_; rw [AlgHom.comp_apply, newToOld2_oldToNew2, AlgHom.id_apply])

@[simp] lemma covEquiv2_apply (P : A₂) : covEquiv2 P = oldToNew2 P := rfl

@[simp] lemma covEquiv2_symm_apply (Q : A₂cov) : covEquiv2.symm Q = newToOld2 Q := rfl

end SU3Jet

end StandardModel
