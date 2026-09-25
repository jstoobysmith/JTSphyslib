/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.IsSU2BiFundamental
/-!
# Gauge tensors carrying four `su(2)` fundamental indices

The quartic Higgs coupling `(H†H)²` is a product of four isospin doublets, so it carries four
fundamental `su(2)` indices. A doublet index can only be contracted against another through
the antisymmetric symbol, so an invariant of four indices is a way of pairing them off, and
there are three pairings: `(12)(34)`, `(13)(24)` and `(14)(23)`. They are not independent:
antisymmetrizing three indices of a two-dimensional space gives zero, and written out that is
the Schouten identity, one linear relation between the three. Modulo an isospin-stable
submodule, every isospin invariant of the span of the components is a combination of the
first two epsilon contractions. That the two are independent, which makes `2 ⊗ 2 ⊗ 2 ⊗ 2`
contain exactly two singlets, is not formalized here; for particular families they may even
vanish.

`IsSU2QuadFundamental B repGauge T` records the transformation law: an isospin rotation
`U ∈ SU(2)` moves the components by one factor of `U` per index, so the law acts on
coefficient vectors `c l`, with `l : Fin 4 → Fin 2`, by the fourth Kronecker power of `U`.
Nothing is asked of the colour and hypercharge factors.

Three rotations pin the fixed coefficient vectors down. The diagonal matrix `diag(ζ, ζ²)`,
with `ζ` a primitive cube root of unity, lies in `SU(2)` and scales `c l` by `ζ ^ (4 + k)`
where `k` is the number of indices equal to `1`, so only the six balanced entries, with two
indices of each kind, survive. The Weyl element `su2Perm` exchanges `0` and `1` in all four
slots and equates each balanced entry with its complement, leaving three unknowns. The third
of a turn `su2Cyc` has a first row with two equal entries, so it carries `c ![0, 0, 0, 0]` to a
multiple of the sum of all sixteen entries: that sum vanishes, and with it the sum of the
three unknowns. Two remain, and they are the coefficients of the two pairings.

- A. The transformation law
- B. The two epsilon pairings
- C. An invariant coefficient is a combination of the two pairings
- D. The reduction modulo a stable submodule
-/

@[expose] public section

namespace StandardModel

open Matrix
open IsSU2BiFundamental (epsilon sum_epsilon_mul)

/-!

## A. The transformation law

-/

/-- The linear map `f` moves the components of `T` as `U ∈ SU(2)` moves a tensor with four
  fundamental indices: one factor of `U` per index, with the summed index in the row
  slot. -/
def IsSU2QuadFundamentalMat {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (U : specialUnitaryGroup (Fin 2) ℂ) (f : B →ₗ[ℂ] B)
    (T : (Fin 4 → Fin 2) → B) : Prop :=
  ∀ l : Fin 4 → Fin 2,
    f (T l) = ∑ a : Fin 4 → Fin 2, (∏ i : Fin 4, U.1 (a i) (l i)) • T a

/-- A family `T` of elements of `B`, indexed by four `su(2)` fundamental indices, transforms
  as a tensor `T^{a b c d}` under the isospin factor of the gauge group. Nothing is asked of
  the colour and hypercharge factors. -/
structure IsSU2QuadFundamental (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B)
    (T : (Fin 4 → Fin 2) → B) : Prop where
  repGauge_T : ∀ g : specialUnitaryGroup (Fin 2) ℂ,
    IsSU2QuadFundamentalMat g (repGauge (1, g, 1)) T

namespace IsSU2QuadFundamental

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B}

/-- The span of the components. -/
def span (T : (Fin 4 → Fin 2) → B) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

/-- Every component lies in the span. -/
lemma mem_span {T : (Fin 4 → Fin 2) → B} (d : Fin 4 → Fin 2) : T d ∈ span T :=
  Family.mem_iSup_span_singleton T d

/-- A sum over families of four fundamental indices is a fourfold sum. -/
lemma sum_pi_four {M : Type*} [AddCommMonoid M] (F : (Fin 4 → Fin 2) → M) :
    ∑ d : Fin 4 → Fin 2, F d
      = ∑ x : Fin 2, ∑ y : Fin 2, ∑ z : Fin 2, ∑ w : Fin 2, F ![x, y, z, w] := by
  rw [show (∑ d : Fin 4 → Fin 2, F d)
      = ∑ p : Fin 2 × Fin 2 × Fin 2 × Fin 2, F ![p.1, p.2.1, p.2.2.1, p.2.2.2] from
        Fintype.sum_equiv
          { toFun := fun d => (d 0, d 1, d 2, d 3)
            invFun := fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2]
            left_inv := fun d => by funext i; fin_cases i <;> simp
            right_inv := fun p => by simp } _ _ fun d => by
          congr 1
          funext i
          fin_cases i <;> simp]
  simp only [Fintype.sum_prod_type]

/-- The matrix by which the law acts on coefficient vectors: the fourth Kronecker power of
  `U`. The law says `f (T l) = ∑ a, coeffMatrix U a l • T a` by definition. -/
noncomputable def coeffMatrix (U : specialUnitaryGroup (Fin 2) ℂ) :
    Matrix (Fin 4 → Fin 2) (Fin 4 → Fin 2) ℂ :=
  Family.powMatrix U.1 4

/-- The coefficient matrix acting on a coefficient vector, written out. -/
lemma coeffMatrix_mulVec_apply (U : specialUnitaryGroup (Fin 2) ℂ) (c : (Fin 4 → Fin 2) → ℂ)
    (a : Fin 4 → Fin 2) :
    (coeffMatrix U *ᵥ c) a = ∑ l, (∏ i : Fin 4, U.1 (a i) (l i)) * c l :=
  rfl

/-- The coefficient matrix of `U⁻¹` is the conjugate transpose of that of `U`. -/
lemma coeffMatrix_inv (U : specialUnitaryGroup (Fin 2) ℂ) :
    coeffMatrix U⁻¹ = (coeffMatrix U)ᴴ := by
  rw [coeffMatrix, coeffMatrix, Family.powMatrix_conjTranspose, ← star_eq_inv,
    specialUnitaryGroup.coe_star, star_eq_conjTranspose]

/-!

## B. The two epsilon pairings

The pairing `(12)(34)` has coefficient vector `ε (l 0) (l 1) * ε (l 2) (l 3)`, and the pairing
`(13)(24)` has `ε (l 0) (l 2) * ε (l 1) (l 3)`. The third pairing is the difference of these
two by the Schouten identity, so two contractions suffice: `epsilonContraction₁₂` and
`epsilonContraction₁₃`, the contractions of `T` against the two coefficient vectors. Each
pairing is fixed by every coefficient matrix, being a product of two invariant antisymmetric
symbols.

-/

/-- The coefficient vector of the pairing `(12)(34)`. -/
def epsilonPair₁₂ (l : Fin 4 → Fin 2) : ℂ := epsilon (l 0) (l 1) * epsilon (l 2) (l 3)

/-- The coefficient vector of the pairing `(13)(24)`. -/
def epsilonPair₁₃ (l : Fin 4 → Fin 2) : ℂ := epsilon (l 0) (l 2) * epsilon (l 1) (l 3)

/-- The contraction pairing the first index with the second and the third with the
  fourth. -/
def epsilonContraction₁₂ (T : (Fin 4 → Fin 2) → B) : B :=
  T ![0, 1, 0, 1] - T ![0, 1, 1, 0] - T ![1, 0, 0, 1] + T ![1, 0, 1, 0]

/-- The contraction pairing the first index with the third and the second with the
  fourth. -/
def epsilonContraction₁₃ (T : (Fin 4 → Fin 2) → B) : B :=
  T ![0, 0, 1, 1] - T ![0, 1, 1, 0] - T ![1, 0, 0, 1] + T ![1, 1, 0, 0]

/-- The first contraction is the contraction against the first pairing. -/
lemma sum_epsilonPair₁₂_smul (T : (Fin 4 → Fin 2) → B) :
    ∑ l, epsilonPair₁₂ l • T l = epsilonContraction₁₂ T := by
  rw [sum_pi_four]
  simp [epsilonPair₁₂, epsilonContraction₁₂, Fin.sum_univ_two]
  abel

/-- The second contraction is the contraction against the second pairing. -/
lemma sum_epsilonPair₁₃_smul (T : (Fin 4 → Fin 2) → B) :
    ∑ l, epsilonPair₁₃ l • T l = epsilonContraction₁₃ T := by
  rw [sum_pi_four]
  simp [epsilonPair₁₃, epsilonContraction₁₃, Fin.sum_univ_two]
  abel

/-- The first pairing is fixed: the sum over the four indices factors into two invariant
  antisymmetric symbols. -/
lemma coeffMatrix_mulVec_epsilonPair₁₂ (U : specialUnitaryGroup (Fin 2) ℂ) :
    coeffMatrix U *ᵥ epsilonPair₁₂ = epsilonPair₁₂ := by
  funext a
  have key : (coeffMatrix U *ᵥ epsilonPair₁₂) a
      = (∑ x : Fin 2, ∑ y : Fin 2, epsilon x y * (U.1 (a 0) x * U.1 (a 1) y))
        * (∑ z : Fin 2, ∑ w : Fin 2, epsilon z w * (U.1 (a 2) z * U.1 (a 3) w)) := by
    rw [coeffMatrix_mulVec_apply, sum_pi_four]
    simp only [epsilonPair₁₂, Fin.prod_univ_four, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    ring
  rw [key, sum_epsilon_mul, sum_epsilon_mul, epsilonPair₁₂]

/-- The second pairing is fixed, by the same factorization with the indices interleaved. -/
lemma coeffMatrix_mulVec_epsilonPair₁₃ (U : specialUnitaryGroup (Fin 2) ℂ) :
    coeffMatrix U *ᵥ epsilonPair₁₃ = epsilonPair₁₃ := by
  funext a
  have key : (coeffMatrix U *ᵥ epsilonPair₁₃) a
      = (∑ x : Fin 2, ∑ z : Fin 2, epsilon x z * (U.1 (a 0) x * U.1 (a 2) z))
        * (∑ y : Fin 2, ∑ w : Fin 2, epsilon y w * (U.1 (a 1) y * U.1 (a 3) w)) := by
    rw [coeffMatrix_mulVec_apply, sum_pi_four]
    simp only [epsilonPair₁₃, Fin.prod_univ_four, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    ring
  rw [key, sum_epsilon_mul, sum_epsilon_mul, epsilonPair₁₃]

/-- Any map moving the components by an element of `SU(2)` fixes the first
  contraction. -/
lemma map_epsilonContraction₁₂ {T : (Fin 4 → Fin 2) → B} {U : specialUnitaryGroup (Fin 2) ℂ}
    {f : B →ₗ[ℂ] B} (hf : IsSU2QuadFundamentalMat U f T) :
    f (epsilonContraction₁₂ T) = epsilonContraction₁₂ T := by
  have h := f.map_sum_smul_eq_self_of_mulVec_eq T (coeffMatrix U) hf
    (coeffMatrix_mulVec_epsilonPair₁₂ U)
  rwa [sum_epsilonPair₁₂_smul] at h

/-- Any map moving the components by an element of `SU(2)` fixes the second
  contraction. -/
lemma map_epsilonContraction₁₃ {T : (Fin 4 → Fin 2) → B} {U : specialUnitaryGroup (Fin 2) ℂ}
    {f : B →ₗ[ℂ] B} (hf : IsSU2QuadFundamentalMat U f T) :
    f (epsilonContraction₁₃ T) = epsilonContraction₁₃ T := by
  have h := f.map_sum_smul_eq_self_of_mulVec_eq T (coeffMatrix U) hf
    (coeffMatrix_mulVec_epsilonPair₁₃ U)
  rwa [sum_epsilonPair₁₃_smul] at h

/-!

## C. An invariant coefficient is a combination of the two pairings

## C.1. A diagonal element of order three keeps only the balanced entries

The matrix `diag(ζ, ζ²)`, with `ζ` a primitive cube root of unity, is unitary of determinant
`ζ³ = 1`. It scales the entry `c l` by `ζ` for each index equal to `0` and by `ζ²` for each
index equal to `1`, so by `ζ ^ (4 + k)` with `k` the number of indices equal to `1`, and that
is `1` only when `3 ∣ 4 + k`, which for `k ≤ 4` means `k = 2`.

-/

/-- The diagonal matrix `diag(ζ, ζ²)` as an element of `SU(2)`. -/
noncomputable def su2Cube : specialUnitaryGroup (Fin 2) ℂ :=
  ⟨Matrix.diagonal ![cubeRootOfUnity, cubeRootOfUnity ^ 2], by
    have hd : ∀ i : Fin 2, ![cubeRootOfUnity, cubeRootOfUnity ^ 2] i
        * star (![cubeRootOfUnity, cubeRootOfUnity ^ 2] i) = 1 := by
      intro i
      fin_cases i
      · simpa using cubeRootOfUnity_mul_star
      · show cubeRootOfUnity ^ 2 * star (cubeRootOfUnity ^ 2) = 1
        rw [star_pow, ← mul_pow, cubeRootOfUnity_mul_star, one_pow]
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
      simp only [Pi.star_apply, hd, Matrix.diagonal_one]
    · rw [Matrix.det_diagonal, Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination cubeRootOfUnity_isPrimitiveRoot.pow_eq_one⟩

/-- The entries of the diagonal element. -/
lemma su2Cube_apply (a b : Fin 2) :
    su2Cube.1 a b = if a = b then cubeRootOfUnity ^ (1 + (a : ℕ)) else 0 := by
  show Matrix.diagonal ![cubeRootOfUnity, cubeRootOfUnity ^ 2] a b = _
  rw [Matrix.diagonal_apply]
  fin_cases a <;> fin_cases b <;> simp

/-- The diagonal element scales an entry by `ζ ^ (4 + k)`, where `k` is the number of its
  indices equal to `1`. -/
lemma coeffMatrix_su2Cube_mulVec (c : (Fin 4 → Fin 2) → ℂ) (l : Fin 4 → Fin 2) :
    (coeffMatrix su2Cube *ᵥ c) l = cubeRootOfUnity ^ (4 + ∑ i, (l i : ℕ)) * c l := by
  rw [coeffMatrix_mulVec_apply, Finset.sum_eq_single l]
  · congr 1
    rw [show (∏ i, su2Cube.1 (l i) (l i)) = ∏ i : Fin 4, cubeRootOfUnity ^ (1 + (l i : ℕ)) from
      Finset.prod_congr rfl fun i _ => by rw [su2Cube_apply, ite_eq_left rfl],
      Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib]
    simp
  · intro m _ hm
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hm
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [su2Cube_apply, ite_eq_right (Ne.symm hi)]),
      zero_mul]
  · simp

/-- An entry of a coefficient vector fixed by the diagonal element vanishes unless exactly two
  of its indices are `1`. -/
lemma eq_zero_of_coeffMatrix_su2Cube_mulVec_eq {c : (Fin 4 → Fin 2) → ℂ}
    (hc : coeffMatrix su2Cube *ᵥ c = c) {l : Fin 4 → Fin 2} (hl : (∑ i, (l i : ℕ)) ≠ 2) :
    c l = 0 := by
  have h := congrFun hc l
  rw [coeffMatrix_su2Cube_mulVec] at h
  have hdvd : ∀ l : Fin 4 → Fin 2, (∑ i, (l i : ℕ)) ≠ 2 → ¬ 3 ∣ 4 + ∑ i, (l i : ℕ) := by
    decide
  refine (mul_left_eq_self₀.1 h).resolve_left fun h1 => hdvd l hl ?_
  exact (cubeRootOfUnity_isPrimitiveRoot.pow_eq_one_iff_dvd _).1 h1

/-!

## C.2. The Weyl element and the third of a turn

The Weyl element `su2Perm = !![0, -1; 1, 0]` exchanges the two values of every index, and
on a balanced entry the four signs multiply to `1`. The third of a turn `su2Cyc` has both
entries of its first row equal to `(1 + i)/2`, so the entry `c ![0, 0, 0, 0]` of its action
on `c` is `((1 + i)/2)⁴` times the sum of all sixteen entries of `c`.

-/

/-- The Weyl element carries `c ![0, 0, 1, 1]` to `c ![1, 1, 0, 0]`. -/
lemma coeffMatrix_su2Perm_mulVec_zero_zero_one_one (c : (Fin 4 → Fin 2) → ℂ) :
    (coeffMatrix su2Perm *ᵥ c) ![0, 0, 1, 1] = c ![1, 1, 0, 0] := by
  rw [coeffMatrix_mulVec_apply, sum_pi_four]
  simp [su2Perm_coe, Fin.sum_univ_two, Fin.prod_univ_four]

/-- The Weyl element carries `c ![0, 1, 0, 1]` to `c ![1, 0, 1, 0]`. -/
lemma coeffMatrix_su2Perm_mulVec_zero_one_zero_one (c : (Fin 4 → Fin 2) → ℂ) :
    (coeffMatrix su2Perm *ᵥ c) ![0, 1, 0, 1] = c ![1, 0, 1, 0] := by
  rw [coeffMatrix_mulVec_apply, sum_pi_four]
  simp [su2Perm_coe, Fin.sum_univ_two, Fin.prod_univ_four]

/-- The Weyl element carries `c ![0, 1, 1, 0]` to `c ![1, 0, 0, 1]`. -/
lemma coeffMatrix_su2Perm_mulVec_zero_one_one_zero (c : (Fin 4 → Fin 2) → ℂ) :
    (coeffMatrix su2Perm *ᵥ c) ![0, 1, 1, 0] = c ![1, 0, 0, 1] := by
  rw [coeffMatrix_mulVec_apply, sum_pi_four]
  simp [su2Perm_coe, Fin.sum_univ_two, Fin.prod_univ_four]

/-- The third of a turn carries the entry with all indices `0` to a nonzero multiple of the
  sum of all the entries. -/
lemma coeffMatrix_su2Cyc_mulVec_zero (c : (Fin 4 → Fin 2) → ℂ) :
    (coeffMatrix su2Cyc *ᵥ c) (fun _ => 0) = ((1 + Complex.I) / 2) ^ 4 * ∑ m, c m := by
  have hrow : ∀ j : Fin 2, su2Cyc.1 0 j = (1 + Complex.I) / 2 := by
    intro j
    fin_cases j <;> simp [su2Cyc_coe]
  rw [coeffMatrix_mulVec_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [hrow, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-!

## C.3. The classification

-/

/-- A coefficient vector fixed by every coefficient matrix is a combination of the two
  pairings. -/
lemma exists_eq_smul_add_smul_of_forall_mulVec_eq {c : (Fin 4 → Fin 2) → ℂ}
    (hc : ∀ U : specialUnitaryGroup (Fin 2) ℂ, coeffMatrix U *ᵥ c = c) :
    ∃ c₁ c₂ : ℂ, c = c₁ • epsilonPair₁₂ + c₂ • epsilonPair₁₃ := by
  -- the diagonal element: only the balanced entries survive
  have hz : ∀ l : Fin 4 → Fin 2, (∑ i, (l i : ℕ)) ≠ 2 → c l = 0 :=
    fun l hl => eq_zero_of_coeffMatrix_su2Cube_mulVec_eq (hc su2Cube) hl
  have hz0000 : c ![0, 0, 0, 0] = 0 := hz _ (by decide)
  have hz0001 : c ![0, 0, 0, 1] = 0 := hz _ (by decide)
  have hz0010 : c ![0, 0, 1, 0] = 0 := hz _ (by decide)
  have hz0100 : c ![0, 1, 0, 0] = 0 := hz _ (by decide)
  have hz1000 : c ![1, 0, 0, 0] = 0 := hz _ (by decide)
  have hz0111 : c ![0, 1, 1, 1] = 0 := hz _ (by decide)
  have hz1011 : c ![1, 0, 1, 1] = 0 := hz _ (by decide)
  have hz1101 : c ![1, 1, 0, 1] = 0 := hz _ (by decide)
  have hz1110 : c ![1, 1, 1, 0] = 0 := hz _ (by decide)
  have hz1111 : c ![1, 1, 1, 1] = 0 := hz _ (by decide)
  -- the Weyl element: each balanced entry equals its complement
  have hw1 : c ![1, 1, 0, 0] = c ![0, 0, 1, 1] := by
    have h := congrFun (hc su2Perm) ![0, 0, 1, 1]
    rwa [coeffMatrix_su2Perm_mulVec_zero_zero_one_one] at h
  have hw2 : c ![1, 0, 1, 0] = c ![0, 1, 0, 1] := by
    have h := congrFun (hc su2Perm) ![0, 1, 0, 1]
    rwa [coeffMatrix_su2Perm_mulVec_zero_one_zero_one] at h
  have hw3 : c ![1, 0, 0, 1] = c ![0, 1, 1, 0] := by
    have h := congrFun (hc su2Perm) ![0, 1, 1, 0]
    rwa [coeffMatrix_su2Perm_mulVec_zero_one_one_zero] at h
  -- the third of a turn: the three remaining unknowns sum to zero
  have hcyc : c ![0, 0, 1, 1] + c ![0, 1, 0, 1] + c ![0, 1, 1, 0] = 0 := by
    have h := congrFun (hc su2Cyc) (fun _ => 0)
    rw [coeffMatrix_su2Cyc_mulVec_zero, hz (fun _ => 0) (by decide)] at h
    have hu : ((1 + Complex.I) / 2) ^ 4 ≠ 0 := by
      refine pow_ne_zero _ fun h0 => ?_
      have := congrArg Complex.re h0
      norm_num at this
    have hsum := (mul_eq_zero.1 h).resolve_left hu
    rw [sum_pi_four] at hsum
    simp only [Fin.sum_univ_two, hz0000, hz0001, hz0010, hz0100, hz1000, hz0111, hz1011,
      hz1101, hz1110, hz1111, hw1, hw2, hw3] at hsum
    linear_combination hsum / 2
  refine ⟨c ![0, 1, 0, 1], c ![0, 0, 1, 1], funext fun l => ?_⟩
  obtain ⟨a, b, d, e, rfl⟩ : ∃ a b d e, l = ![a, b, d, e] :=
    ⟨l 0, l 1, l 2, l 3, by ext i; fin_cases i <;> rfl⟩
  fin_cases a <;> fin_cases b <;> fin_cases d <;> fin_cases e <;>
    simp [epsilonPair₁₂, epsilonPair₁₃, hz0000, hz0001, hz0010, hz0100, hz1000, hz0111,
      hz1011, hz1101, hz1110, hz1111, hw1, hw2, hw3] <;>
    linear_combination hcyc

/-!

## D. The reduction modulo a stable submodule

`reducesInvariantsTo_of_mulVec_eq`, with the span of the two pairings as the target submodule
of coefficient vectors, applies section C in every quotient by a stable submodule. The gauge
form, used by the Higgs sector, lets the other two factors act as well: once the two
contractions are known to be gauge invariant, so is the remainder.

-/

/-- For any family of maps `σ U` obeying the law, a `σ`-invariant of the span joined with a
  `σ`-stable submodule `S` is a combination of the two epsilon contractions plus an element
  of `S`. -/
lemma reducesInvariantsTo_span_epsilonContractions
    (σ : specialUnitaryGroup (Fin 2) ℂ → B →ₗ[ℂ] B) {T : (Fin 4 → Fin 2) → B}
    (hT : ∀ U, IsSU2QuadFundamentalMat U (σ U) T) :
    ReducesInvariantsTo σ (span T)
      (Submodule.span ℂ {epsilonContraction₁₂ T, epsilonContraction₁₃ T}) := by
  have h := reducesInvariantsTo_of_mulVec_eq (σ := σ) T coeffMatrix hT
    (fun U => ⟨U⁻¹, coeffMatrix_inv U⟩) (Submodule.span ℂ {epsilonPair₁₂, epsilonPair₁₃})
    fun c hc => by
      obtain ⟨c₁, c₂, rfl⟩ := exists_eq_smul_add_smul_of_forall_mulVec_eq hc
      exact Submodule.mem_span_pair.2 ⟨c₁, c₂, rfl⟩
  rwa [Submodule.map_span, Set.image_pair, Fintype.linearCombination_apply,
    Fintype.linearCombination_apply, sum_epsilonPair₁₂_smul, sum_epsilonPair₁₃_smul] at h

/-- A gauge invariant of the span joined with a gauge-stable submodule is a combination of
  the two epsilon contractions plus a gauge-invariant remainder, once the two contractions
  are known to be gauge invariant. The hypotheses on the contractions cannot be dropped: the
  law says nothing about the hypercharge factor, which may scale them. -/
lemma exists_smul_add_smul_add_of_gauge_invariant {T : (Fin 4 → Fin 2) → B}
    (hT : IsSU2QuadFundamental B repGauge T) (x : B) (S : Submodule ℂ B)
    (hS : ∀ g : GaugeGroupI, ∀ y ∈ S, repGauge g y ∈ S)
    (hec₁₂ : ∀ g : GaugeGroupI,
      repGauge g (epsilonContraction₁₂ T) = epsilonContraction₁₂ T)
    (hec₁₃ : ∀ g : GaugeGroupI,
      repGauge g (epsilonContraction₁₃ T) = epsilonContraction₁₃ T)
    (hx : x ∈ span T ⊔ S) (hinv : ∀ g : GaugeGroupI, repGauge g x = x) :
    ∃ c₁ c₂ : ℂ, ∃ y ∈ S,
      x = c₁ • epsilonContraction₁₂ T + c₂ • epsilonContraction₁₃ T + y
        ∧ ∀ g : GaugeGroupI, repGauge g y = y := by
  have h := reducesInvariantsTo_span_epsilonContractions _ hT.repGauge_T S
    (fun V => hS (1, V, 1)) x hx fun V => hinv (1, V, 1)
  have hfix : IsFixedBy (fun g : GaugeGroupI => repGauge g)
      (Submodule.span ℂ {epsilonContraction₁₂ T, epsilonContraction₁₃ T}) := by
    intro g w hw
    obtain ⟨c₁, c₂, rfl⟩ := Submodule.mem_span_pair.1 hw
    rw [map_add, map_smul, map_smul, hec₁₂ g, hec₁₃ g]
  obtain ⟨w, hw, y, hy, rfl, hyinv⟩ := hfix.exists_add_of_mem_sup h hinv
  obtain ⟨c₁, c₂, rfl⟩ := Submodule.mem_span_pair.1 hw
  exact ⟨c₁, c₂, y, hy, rfl, hyinv⟩

end IsSU2QuadFundamental

end StandardModel
