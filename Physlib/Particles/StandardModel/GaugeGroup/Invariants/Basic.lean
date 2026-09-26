/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Mathematics.InvariantReduction
public import Physlib.Mathematics.LinearCombination
/-!
# Families of components and their invariants

Every file of this folder studies a family `T : ι → B` of vectors in a module `B`: the
components of a tensor with a fixed set of gauge indices, such as a product of two gluon
field strengths `F^a F^b` indexed by `ι = Fin 2 → Fin 8`. A gauge transformation moves the
components into one another by a matrix, `f (T l) = ∑ a, M a l • T a`, and the question is
always which combinations of the components every transformation leaves alone.

Each file follows the same four steps.

1. The transformation law and its coefficient matrix `M`. Two index conventions meet here.
   On the family the law sums over the row index, `f (T l) = ∑ a, M a l • T a`. On
   coefficient vectors `c : ι → ℂ` the matrix acts by `M *ᵥ c`, summing over the column index,
   `(M *ᵥ c) a = ∑ l, M a l * c l`. The two agree: `f (∑ l, c l • T l) = ∑ a, (M *ᵥ c) a • T a`
   (`LinearMap.map_sum_smul_eq_sum_mulVec_smul`). The conjugate transpose of the matrix of `U`
   is the matrix of `U⁻¹`.
2. The invariant contractions: coefficient vectors fixed by every matrix, such as the
   Kronecker delta, whose combinations are therefore fixed.
3. The classification: every fixed coefficient vector is a combination of those, a finite
   computation with a few group elements.
4. The reduction modulo a stable remainder, `reducesInvariantsTo_of_mulVec_eq` and its forms
   in `Physlib.Mathematics.InvariantReduction`, which apply step 3 in every quotient `B ⧸ S`.

The span of the components is Mathlib's `Submodule.span ℂ (Set.range T)`.
The conclusions are spanning statements: an invariant is a combination of the named
contractions. Nothing here shows that the contractions are nonzero or independent.

This file holds what the families share: sums over pairs of indices, the matrices of laws with
one factor per index (`powMatrix`, `pairMatrix`), and the Kronecker delta on two indices, which
is fixed by a pair of matrices whose rows are orthonormal against each other.

- A. Sums over pairs of indices
- B. Matrices of tensor laws
- C. The Kronecker delta on two indices
-/

@[expose] public section

namespace StandardModel

namespace Family

variable {B : Type*} [AddCommGroup B] [Module ℂ B]

/-!

## A. Sums over pairs of indices

-/

/-- A sum over pairs of indices is a double sum. -/
lemma sum_pi_two {n : ℕ} {M : Type*} [AddCommMonoid M] (F : (Fin 2 → Fin n) → M) :
    ∑ d : Fin 2 → Fin n, F d = ∑ x : Fin n, ∑ y : Fin n, F ![x, y] := by
  rw [show (∑ d : Fin 2 → Fin n, F d) = ∑ p : Fin n × Fin n, F ![p.1, p.2] from
      Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin n) _ _ fun d => by
        congr 1
        funext i
        fin_cases i <;> simp,
    Fintype.sum_prod_type]

/-!

## B. Matrices of tensor laws

A law with one factor of a matrix per index acts on coefficient vectors by a Kronecker
product. `powMatrix M k` has one factor of `M` for each of `k` indices, and `pairMatrix A C`
has a factor of `A` on the first of two indices and a factor of `C` on the second, which is
how a fundamental and an anti-fundamental index combine. In both the entry at `(a, l)` is the
coefficient of `T a` in the image of `T l`: the family law sums over the row `a`, and
`M *ᵥ c` over the column `l`.

-/

open Matrix

/-- The matrix of a law with one factor of `M` on each of `k` indices. -/
def powMatrix {n : Type*} (M : Matrix n n ℂ) (k : ℕ) : Matrix (Fin k → n) (Fin k → n) ℂ :=
  Matrix.of fun a l => ∏ i, M (a i) (l i)

/-- The conjugate transpose of a Kronecker power is the power of the conjugate transpose. -/
lemma powMatrix_conjTranspose {n : Type*} (M : Matrix n n ℂ) (k : ℕ) :
    (powMatrix M k)ᴴ = powMatrix Mᴴ k := by
  ext a l
  simp [powMatrix, conjTranspose_apply]

/-- The matrix of a law with a factor of `A` on the first of two indices and a factor of `C`
  on the second. -/
def pairMatrix {n : Type*} (A C : Matrix n n ℂ) : Matrix (Fin 2 → n) (Fin 2 → n) ℂ :=
  Matrix.of fun a l => A (a 0) (l 0) * C (a 1) (l 1)

/-- The conjugate transpose of a pair matrix is the pair of the conjugate transposes. -/
lemma pairMatrix_conjTranspose {n : Type*} (A C : Matrix n n ℂ) :
    (pairMatrix A C)ᴴ = pairMatrix Aᴴ Cᴴ := by
  ext a l
  simp [pairMatrix, conjTranspose_apply]

/-- The second Kronecker power is the pair matrix of `M` with itself. -/
lemma powMatrix_two {n : Type*} (M : Matrix n n ℂ) : powMatrix M 2 = pairMatrix M M := by
  ext a l
  simp [powMatrix, pairMatrix, Fin.prod_univ_two]

/-!

## C. The Kronecker delta on two indices

The Kronecker delta contracts two indices into the trace `∑ a, T ![a, a]`. It is fixed by
`pairMatrix A C` exactly when the rows of `A` and `C` are orthonormal against each other,
`A * Cᵀ = 1`: for two adjoint indices this is the orthogonality of the real adjoint matrix,
and for a fundamental and an anti-fundamental index, with `C = conj U`, it is the unitarity
`U * Uᴴ = 1`.

-/

/-- The Kronecker delta on a pair of indices. -/
def deltaCoeff {n : ℕ} : (Fin 2 → Fin n) → ℂ := fun l => if l 0 = l 1 then 1 else 0

/-- The combination with coefficients the Kronecker delta is the trace. -/
lemma sum_deltaCoeff_smul {n : ℕ} (T : (Fin 2 → Fin n) → B) :
    ∑ l, deltaCoeff l • T l = ∑ a : Fin n, T ![a, a] := by
  rw [sum_pi_two]
  simp [deltaCoeff, ite_smul]

/-- The Kronecker delta is fixed by `pairMatrix A C` when `A * Cᵀ = 1`. -/
lemma pairMatrix_mulVec_deltaCoeff {n : ℕ} {A C : Matrix (Fin n) (Fin n) ℂ} (h : A * Cᵀ = 1) :
    pairMatrix A C *ᵥ deltaCoeff = deltaCoeff := by
  funext a
  have key : ∀ x y : Fin n, pairMatrix A C a ![x, y] * deltaCoeff ![x, y]
      = if x = y then A (a 0) x * C (a 1) x else 0 := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      simp [pairMatrix, deltaCoeff]
    · simp [deltaCoeff, hxy]
  simp only [mulVec, dotProduct]
  rw [sum_pi_two]
  simp only [key, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have h' := congrFun (congrFun h (a 0)) (a 1)
  simp only [mul_apply, transpose_apply, one_apply] at h'
  rw [h']
  rfl

end Family

end StandardModel
