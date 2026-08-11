/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.FieldStrength
/-!
# A dual family for the photon pairs

The products `F_{μν} F_{μ'ν'}` of two field strengths are not linearly independent — the field
strengths are antisymmetric and commute — but the coefficients of a combination of them can
still be read off one by one. This file constructs the functionals that read them: `gaugeDual p q`
picks out the coefficient of the product of the field strengths indexed by the generator pairs
`p` and `q`. Statements about an explicit span of photon pairs — the boost-weight-zero part of
the gauge sector, say — then reduce to linear algebra on coefficients.

*The construction is a polarization.* The B-boson factor of the jet algebra is a symmetric
algebra, so a linear functional `φ` on the jet component space extends to an algebra map
`symEval φ` to `ℂ`, quadratic on the degree-two part. The second difference

`symEval (φ + ψ) - symEval φ - symEval ψ + symEval 0`

is linear, vanishes in degrees zero and one, and sends a degree-two monomial `u v` to
`φ u * ψ v + ψ u * φ v`: the dual of the symmetric product. Tensoring with the augmentation of
the lepton factor gives `gaugePairDual` on the whole jet algebra, and taking for `φ`, `ψ` the
coordinates of two gauge-field generators gives `gaugeDual`.

## Key results

- `gaugePairDual` : the polarization of `symEval`, dual to a symmetric product of generators.
- `gaugeDual_fieldStrength_mul` : the value of `gaugeDual p q` on a product of two field
  strengths, in terms of the antisymmetric coefficient `fsCoeff`.

-/

@[expose] public section

namespace LeptonGaugeSector
open TensorProduct StandardModel

namespace JetAlgebra

/-!

## A. Evaluating the B-boson factor

-/

/-- The algebra map on the B-boson factor sending each gauge-field generator to its value
  under `φ`. -/
noncomputable def symEval (φ : BBoson.JetComponentSpace →ₗ[ℝ] ℂ) :
    (ℂ ⊗[ℝ] BBoson.JetAlgebra) →ₐ[ℂ] ℂ :=
  Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) (SymmetricAlgebra.lift φ)
    (fun _ _ => Commute.all _ _)

@[simp]
lemma symEval_tmul_ofGenerator (φ : BBoson.JetComponentSpace →ₗ[ℝ] ℂ)
    (g : BBoson.JetGenerators) :
    symEval φ (1 ⊗ₜ[ℝ] BBoson.JetAlgebra.ofGenerator g) =
      φ (BBoson.JetComponentSpace.basis g) := by
  simp [symEval, BBoson.JetAlgebra.ofGenerator]

/-- The augmentation of the lepton factor: the algebra map to `ℂ` sending every lepton
  generator to zero. -/
noncomputable def augL : LeptonSinglet.JetAlgebra →ₐ[ℂ] ℂ :=
  ExteriorAlgebra.lift ℂ ⟨0, fun m => by simp⟩

/-!

## B. The polarization

-/

/-- The second difference of `symEval`: the functional on the B-boson factor dual to the
  degree-two monomial paired with `φ` and `ψ`. It is linear where `symEval` is quadratic, and
  vanishes on the degrees zero and one where the second difference of a quadratic is blind. -/
noncomputable def symPairDual (φ ψ : BBoson.JetComponentSpace →ₗ[ℝ] ℂ) :
    (ℂ ⊗[ℝ] BBoson.JetAlgebra) →ₗ[ℂ] ℂ :=
  (symEval (φ + ψ)).toLinearMap - (symEval φ).toLinearMap - (symEval ψ).toLinearMap +
    (symEval 0).toLinearMap

lemma symPairDual_tmul_ofGenerator_mul (φ ψ : BBoson.JetComponentSpace →ₗ[ℝ] ℂ)
    (g h : BBoson.JetGenerators) :
    symPairDual φ ψ ((1 ⊗ₜ[ℝ] BBoson.JetAlgebra.ofGenerator g) *
        (1 ⊗ₜ[ℝ] BBoson.JetAlgebra.ofGenerator h)) =
      φ (BBoson.JetComponentSpace.basis g) * ψ (BBoson.JetComponentSpace.basis h) +
        ψ (BBoson.JetComponentSpace.basis g) * φ (BBoson.JetComponentSpace.basis h) := by
  simp only [symPairDual, LinearMap.add_apply, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
    map_mul, symEval_tmul_ofGenerator, LinearMap.add_apply, LinearMap.zero_apply]
  ring

/-- The functional on the jet algebra dual to a symmetric product of two gauge-field
  generators: the polarization on the B-boson factor tensored with the augmentation on the
  lepton factor. -/
noncomputable def gaugePairDual (φ ψ : BBoson.JetComponentSpace →ₗ[ℝ] ℂ) :
    JetAlgebra →ₗ[ℂ] ℂ :=
  TensorProduct.lift (((LinearMap.mul ℂ ℂ).comp (symPairDual φ ψ)).compl₂ augL.toLinearMap)

@[simp]
lemma gaugePairDual_tmul (φ ψ : BBoson.JetComponentSpace →ₗ[ℝ] ℂ)
    (a : ℂ ⊗[ℝ] BBoson.JetAlgebra) (b : LeptonSinglet.JetAlgebra) :
    gaugePairDual φ ψ (a ⊗ⱼ b) = symPairDual φ ψ a * augL b := rfl

lemma gaugePairDual_ofGenerator_mul (φ ψ : BBoson.JetComponentSpace →ₗ[ℝ] ℂ)
    (s t : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) :
    gaugePairDual φ ψ (ofGenerator (JetGenerators.dB s μ) *
        ofGenerator (JetGenerators.dB t ν)) =
      φ (BBoson.JetComponentSpace.basis (BBoson.JetGenerators.dB s μ)) *
          ψ (BBoson.JetComponentSpace.basis (BBoson.JetGenerators.dB t ν)) +
        ψ (BBoson.JetComponentSpace.basis (BBoson.JetGenerators.dB s μ)) *
          φ (BBoson.JetComponentSpace.basis (BBoson.JetGenerators.dB t ν)) := by
  rw [ofGenerator_B_eq, ofGenerator_B_eq, JetAlgebra.tmul_mul_tmul, mul_one,
    gaugePairDual_tmul, symPairDual_tmul_ofGenerator_mul, map_one, mul_one]

/-!

## C. The dual family for the photon pairs

-/

/-- The coefficient with which the field strength `F_{a b}` contains the gauge-field generator
  `∂_{p.1} B_{p.2}`: `+1`, `-1` or `0`, by the antisymmetry of `F`. -/
noncomputable def fsCoeff (p : (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)) (a b : Fin 1 ⊕ Fin 3) : ℂ :=
  (if a = p.1 ∧ b = p.2 then 1 else 0) - (if b = p.1 ∧ a = p.2 then 1 else 0)

/-- The functional dual to the product of the two field strengths indexed by the generator
  pairs `p` and `q`. -/
noncomputable def gaugeDual (p q : (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)) : JetAlgebra →ₗ[ℂ] ℂ :=
  gaugePairDual ((BBoson.JetComponentSpace.basis.coord
      (BBoson.JetGenerators.dB {p.1} p.2)).smulRight (1 : ℂ))
    ((BBoson.JetComponentSpace.basis.coord
      (BBoson.JetGenerators.dB {q.1} q.2)).smulRight (1 : ℂ))

/-- A first-order field strength written out on the generators. -/
lemma fieldStrengthDeriv_nil_eq (a b : Fin 1 ⊕ Fin 3) :
    fieldStrengthDeriv {} a b =
      ofGenerator (JetGenerators.dB {a} b) - ofGenerator (JetGenerators.dB {b} a) := by
  rw [fieldStrengthDeriv, BBoson.JetAlgebra.fieldStrengthDeriv, TensorProduct.tmul_sub, sub_tmul]
  rfl

/-- **`gaugeDual` is dual to the photon pairs.** The value on a product of two field strengths
  is the symmetric pairing of the two antisymmetric coefficients. -/
@[simp]
lemma gaugeDual_fieldStrength_mul (p q : (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3))
    (a b c d : Fin 1 ⊕ Fin 3) :
    gaugeDual p q (fieldStrengthDeriv {} a b * fieldStrengthDeriv {} c d) =
      fsCoeff p a b * fsCoeff q c d + fsCoeff q a b * fsCoeff p c d := by
  simp only [fieldStrengthDeriv_nil_eq, sub_mul, mul_sub, map_sub, gaugeDual,
    gaugePairDual_ofGenerator_mul, Module.Basis.coord_apply, Module.Basis.repr_self,
    LinearMap.smulRight_apply, Finsupp.single_apply, BBoson.JetGenerators.dB.injEq,
    Multiset.singleton_inj, fsCoeff, ite_smul, one_smul, zero_smul]
  ring

end JetAlgebra

end LeptonGaugeSector

end
