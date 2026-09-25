/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.GaugeGroup.SU3PermDecomposition
public import Physlib.Particles.StandardModel.GaugeGroup.Invariants.Basic
/-!
# Gauge tensors carrying two `su(3)` fundamental indices

A quark carries one fundamental colour index, and a product of two quark fields carries two.
There is no colour singlet in `3 ⊗ 3 = 6 ⊕ 3̄`: a colour singlet needs three quarks, or a
quark and an antiquark, never two quarks. Modulo a colour-stable submodule `S`, every colour
invariant of the span of the components lies in `S`.

`IsSU3BiFundamental B repGauge T` records the transformation law: a colour rotation
`U ∈ SU(3)` moves the components by one factor of `U` per index, so the law acts on
coefficient vectors by the Kronecker square of `U`. Nothing is asked of the isospin and
hypercharge factors.

The proof is triality. The scalar matrix `ω • 1`, with `ω` a primitive cube root of unity,
lies in `SU(3)` because `ω ^ 3 = 1` is exactly the determinant condition, and it scales a
tensor with `k` fundamental indices by `ω ^ k`. An invariant tensor therefore needs `3 ∣ k`,
and `k = 2` fails: the centre alone scales every coefficient vector by `ω ^ 2 ≠ 1`, so no
nonzero coefficient vector is fixed.

- A. The transformation law
- B. The centre of `SU(3)` fixes no coefficient vector
- C. The reduction modulo a stable submodule
-/

@[expose] public section

namespace StandardModel

open Matrix

/-!

## A. The transformation law

-/

/-- The linear map `f` moves the components of `T` as `U ∈ SU(3)` moves a tensor with two
  fundamental indices: one factor of `U` per index. -/
def IsSU3BiFundamentalMat {B : Type*} [AddCommMonoid B] [Module ℂ B]
    (U : specialUnitaryGroup (Fin 3) ℂ) (f : B →ₗ[ℂ] B)
    (T : (Fin 2 → Fin 3) → B) : Prop :=
  ∀ l : Fin 2 → Fin 3,
    f (T l) = ∑ a : Fin 2 → Fin 3, (∏ i : Fin 2, U.1 (a i) (l i)) • T a

/-- A family `T` of elements of `B`, indexed by two `su(3)` fundamental indices, transforms
  as a tensor `T^{a b}` under the colour factor of the gauge group. Nothing is asked of the
  isospin and hypercharge factors. -/
structure IsSU3BiFundamental (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repGauge : Representation ℂ GaugeGroupI B)
    (T : (Fin 2 → Fin 3) → B) : Prop where
  repGauge_T : ∀ g : specialUnitaryGroup (Fin 3) ℂ,
    IsSU3BiFundamentalMat g (repGauge (g, 1, 1)) T

namespace IsSU3BiFundamental

/- `span` takes the hypothesis `hT` only to hang off it by dot notation. -/
set_option linter.unusedVariables false

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repGauge : Representation ℂ GaugeGroupI B} {T : (Fin 2 → Fin 3) → B}

/-- The span of the components. -/
@[nolint unusedArguments]
def span (hT : IsSU3BiFundamental B repGauge T) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

/-- The matrix by which the law acts on coefficient vectors: the Kronecker square of `U`.
  The law says `f (T l) = ∑ a, coeffMatrix U a l • T a` by definition. -/
noncomputable def coeffMatrix (U : specialUnitaryGroup (Fin 3) ℂ) :
    Matrix (Fin 2 → Fin 3) (Fin 2 → Fin 3) ℂ :=
  Family.powMatrix U.1 2

/-- The coefficient matrix of `U⁻¹` is the conjugate transpose of that of `U`. -/
lemma coeffMatrix_inv (U : specialUnitaryGroup (Fin 3) ℂ) :
    coeffMatrix U⁻¹ = (coeffMatrix U)ᴴ := by
  rw [coeffMatrix, coeffMatrix, Family.powMatrix_conjTranspose, ← star_eq_inv,
    specialUnitaryGroup.coe_star, star_eq_conjTranspose]

/-!

## B. The centre of `SU(3)` fixes no coefficient vector

-/

/-- The generator `ω • 1` of the centre `ℤ₃` of `SU(3)`: the determinant condition on a
  scalar matrix in three dimensions is exactly `ω ^ 3 = 1`. -/
noncomputable def su3Centre : specialUnitaryGroup (Fin 3) ℂ :=
  ⟨Matrix.diagonal fun _ => cubeRootOfUnity, by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
      simp only [Pi.star_apply, cubeRootOfUnity_mul_star, Matrix.diagonal_one]
    · rw [Matrix.det_diagonal]
      simp⟩

/-- The central element is `ω` times the identity. -/
lemma su3Centre_apply (a b : Fin 3) :
    (su3Centre : specialUnitaryGroup (Fin 3) ℂ).1 a b = if a = b then cubeRootOfUnity else 0 := by
  simp [su3Centre, Matrix.diagonal_apply]

/-- The coefficient matrix of the central element is `ω ^ 2` times the identity, one factor
  of `ω` for each index. -/
lemma coeffMatrix_su3Centre : coeffMatrix su3Centre = cubeRootOfUnity ^ 2 • (1 : Matrix _ _ ℂ) := by
  ext a l
  simp only [coeffMatrix, Family.powMatrix, of_apply, Fin.prod_univ_two, su3Centre_apply,
    Matrix.smul_apply, one_apply, smul_eq_mul]
  by_cases hal : a = l
  · subst hal
    simp [sq]
  · have h : a 0 ≠ l 0 ∨ a 1 ≠ l 1 := by
      by_contra hc
      simp only [not_or, ne_eq, not_not] at hc
      exact hal (funext fun j => by fin_cases j <;> simp [hc.1, hc.2])
    rcases h with h | h <;> simp [h, hal]

/-- A coefficient vector fixed by every coefficient matrix is zero: the centre scales it by
  `ω ^ 2 ≠ 1`. -/
lemma eq_zero_of_forall_mulVec_eq {c : (Fin 2 → Fin 3) → ℂ}
    (hc : ∀ U : specialUnitaryGroup (Fin 3) ℂ, coeffMatrix U *ᵥ c = c) : c = 0 := by
  have h := hc su3Centre
  rw [coeffMatrix_su3Centre, smul_mulVec, one_mulVec] at h
  have hne : cubeRootOfUnity ^ 2 - 1 ≠ 0 :=
    sub_ne_zero.2 (cubeRootOfUnity_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by norm_num)
      (by norm_num))
  have h0 : (cubeRootOfUnity ^ 2 - 1) • c = 0 := by rw [sub_smul, one_smul, h, sub_self]
  exact (smul_eq_zero.1 h0).resolve_left hne

/-!

## C. The reduction modulo a stable submodule

`reducesInvariantsTo_bot_of_mulVec_eq` applies section B in every quotient by a stable
submodule: two fundamental colour indices contribute nothing to the invariants.

-/

/-- For any family of maps `σ U` obeying the law, a `σ`-invariant of the span joined with a
  `σ`-stable submodule `S` lies in `S`. -/
lemma reducesInvariantsTo_bot (σ : specialUnitaryGroup (Fin 3) ℂ → B →ₗ[ℂ] B)
    (hT : ∀ U, IsSU3BiFundamentalMat U (σ U) T) :
    ReducesInvariantsTo σ (⨆ i, ℂ ∙ T i) ⊥ :=
  reducesInvariantsTo_bot_of_mulVec_eq T coeffMatrix hT (fun U => ⟨U⁻¹, coeffMatrix_inv U⟩)
    fun _ hc => eq_zero_of_forall_mulVec_eq hc

end IsSU3BiFundamental

end StandardModel
