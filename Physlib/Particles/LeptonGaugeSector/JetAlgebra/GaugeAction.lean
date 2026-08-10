/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.CovariantAlgebra
/-!
# The gauge action on the lepton–gauge-sector jet algebra

The representation of the jet gauge group, the covariance of the covariant
derivatives under it, and the linear-matter model in which that covariance is
proved uniformly in the matter species before being instantiated at the lepton
and at its conjugate.
-/

@[expose] public section


namespace LeptonGaugeSector
open TensorProduct StandardModel

namespace JetAlgebra

/-!

## B. Representation of the jet gauge group

Gauge transformations act on the lepton–gauge-sector jet algebra
locally via the group `JetGaugeGroupI`.

-/

/-- The representation of the jet gauge group on the lepton–gauge-sector jet algebra: the
  Maurer–Cartan substitution action on the (complexified) B-boson factor tensored
  with the hypercharge action on the charged-lepton factor. -/
noncomputable def repJetGaugeGroupI : Representation ℂ JetGaugeGroupI JetAlgebra :=
  BBoson.JetAlgebra.complexRepJetGaugeGroupI.tprod LeptonSinglet.JetAlgebra.repJetGaugeGroupI

lemma repJetGaugeGroupI_eq_algHom (g : JetGaugeGroupI) (x : JetAlgebra) :
    repJetGaugeGroupI g x = Algebra.TensorProduct.map
        (BBoson.JetAlgebra.complexRepJetGaugeGroupIAlgHom g)
        (LeptonSinglet.JetAlgebra.repJetGaugeGroupIAlgHom g) x := rfl

lemma repJetGaugeGroupI_tmul (U : JetGaugeGroupI) (c : ℂ) (b : BBoson.JetAlgebra)
    (l : LeptonSinglet.JetAlgebra) :
    repJetGaugeGroupI U ((c ⊗ₜ[ℝ] b) ⊗ⱼ l) =
      (c ⊗ₜ[ℝ] BBoson.JetAlgebra.repJetGaugeGroupI U b) ⊗ⱼ
        LeptonSinglet.JetAlgebra.repJetGaugeGroupI U l := rfl

/-- The gauge action on a pure tensor of the two jet-algebra factors. -/
lemma repJetGaugeGroupI_tmul' (U : JetGaugeGroupI) (p : ℂ ⊗[ℝ] BBoson.JetAlgebra)
    (l : LeptonSinglet.JetAlgebra) :
    repJetGaugeGroupI U (p ⊗ⱼ l) =
      (BBoson.JetAlgebra.complexRepJetGaugeGroupI U p) ⊗ⱼ
        (LeptonSinglet.JetAlgebra.repJetGaugeGroupI U l) := rfl

lemma repJetGaugeGroupI_apply_mul (g : JetGaugeGroupI) (x y : JetAlgebra) :
    repJetGaugeGroupI g (x * y) =
      repJetGaugeGroupI g x * repJetGaugeGroupI g y := by
  induction x using JetAlgebra.induction_on with
  | zero => simp
  | add a b ha hb => simp only [add_mul, map_add, ha, hb]
  | tmul p l =>
    induction y using JetAlgebra.induction_on with
    | zero => simp
    | add a b ha hb => simp only [mul_add, map_add, ha, hb]
    | tmul q k =>
      simp only [tmul_mul_tmul, repJetGaugeGroupI_tmul',
        BBoson.JetAlgebra.complexRepJetGaugeGroupI_mul,
        LeptonSinglet.JetAlgebra.repJetGaugeGroupI_apply_mul]

lemma repJetGaugeGroupI_apply_one (g : JetGaugeGroupI) :
    repJetGaugeGroupI g (1 : JetAlgebra) = 1 := by
  rw [one_eq_tmul, repJetGaugeGroupI_tmul',
    BBoson.JetAlgebra.complexRepJetGaugeGroupI_one,
    LeptonSinglet.JetAlgebra.repJetGaugeGroupI_apply_one, ← one_eq_tmul]

/-- The gauge action on a spanning element of the linear-matter submodule: it
  acts on the two factors separately, leaving the matter degree at one. This is
  the only input the closure result needs, and it holds for any matter factor
  whose gauge action is functorial in the component space. -/
lemma repJetGaugeGroupI_tmul_ι (U : JetGaugeGroupI) (p : ℂ ⊗[ℝ] BBoson.JetAlgebra)
    (m : LeptonSinglet.JetComponentSpace) :
    repJetGaugeGroupI U (p ⊗ⱼ ExteriorAlgebra.ι ℂ m) =
      (BBoson.JetAlgebra.complexRepJetGaugeGroupI U p) ⊗ⱼ
        ExteriorAlgebra.ι ℂ (LeptonSinglet.JetComponentSpace.repJetGaugeGroupI U m) := by
  rw [repJetGaugeGroupI_tmul', LeptonSinglet.JetAlgebra.repJetGaugeGroupI_apply,
    ExteriorAlgebra.map_apply_ι]

/-- The zeroth-order lepton coordinate carries hypercharge `6`: a jet of gauge
  transformations acts on it through the character of its value at the base
  point alone, with no derivative contributions. This is the base case of
  `repJetGaugeGroupI_Dψ`. -/
lemma repJetGaugeGroupI_dψ_nil (U : JetGaugeGroupI) (α : Fin 2) :
    repJetGaugeGroupI U [JetGenerators.dψ {} α]ₐ = U.eval.2.2 ^ 6 • [JetGenerators.dψ {} α]ₐ := by
  rw [ofGenerator_dψ_eq, repJetGaugeGroupI_tmul',
    BBoson.JetAlgebra.complexRepJetGaugeGroupI_one_tmul_one,
    LeptonSinglet.JetAlgebra.repJetGaugeGroupI_ofGenerator_ψ_nil,
    Submonoid.smul_def, Submonoid.smul_def, tmul_smul]

lemma repJetGaugeGroupI_dψ (U : JetGaugeGroupI) (s : Multiset (Fin 1 ⊕ Fin 3)) (α : Fin 2) :
    repJetGaugeGroupI U [.dψ s α]ₐ =
     ∑ p ∈ Finset.antidiagonal (Multiset.toFinsupp s),
        ((∏ μ, (Multiset.toFinsupp s μ).descFactorial (p.1 μ) : ℕ) : ℂ) •
          MvPowerSeries.coeff p.1 (((U.2.2 : unitary JetRing) : JetRing) ^ 6) •
            [.dψ (Finsupp.toMultiset p.2) α]ₐ := by
  rw [ofGenerator_dψ_eq, repJetGaugeGroupI_tmul', BBoson.JetAlgebra.complexRepJetGaugeGroupI_one_tmul_one,
    StandardModel.LeptonSinglet.JetAlgebra.repJetGaugeGroupI_ofGenerator_ψ]
  simp [tmul_sum, ← ofGenerator_dψ_eq]

lemma repJetGaugeGroupI_apply_dB (U : JetGaugeGroupI) (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) :
    repJetGaugeGroupI U [JetGenerators.dB s μ]ₐ =
    [JetGenerators.dB s μ]ₐ + (BBoson.mcShift U (.basis (.dB s μ))) • 1 := by
  rw [ofGenerator_B_eq, repJetGaugeGroupI_tmul',
    BBoson.JetAlgebra.complexRepJetGaugeGroupI_ofGenerator,
    LeptonSinglet.JetAlgebra.repJetGaugeGroupI_apply_one, add_tmul, smul_tmul']
  rfl



/-- The statement that if `x` and all its derivatives transform in the
  same way that `ψ` transforms under the full
  gauge group, then `covariantStep μ x` transforms this.-/
lemma repJetGaugeGroupI_jetDerivM_covariantSteplemma
   (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3) (x : JetAlgebra)
    (hx : ∀ s, (repJetGaugeGroupI U) (jetDerivM s x)
      = ∑ p ∈ Finset.antidiagonal (Multiset.toFinsupp s),
        ((∏ μ, (Multiset.toFinsupp s μ).descFactorial (p.1 μ) : ℕ) : ℂ) •
          MvPowerSeries.coeff p.1 (((U.2.2 : unitary JetRing) : JetRing) ^ 6) •
          jetDerivM (Finsupp.toMultiset p.2) x)
    (s : Multiset (Fin 1 ⊕ Fin 3)) :
    repJetGaugeGroupI U (jetDerivM s (covariantStep μ x)) =
    ∑ p ∈ Finset.antidiagonal (Multiset.toFinsupp s),
        ((∏ μ, (Multiset.toFinsupp s μ).descFactorial (p.1 μ) : ℕ) : ℂ) •
          MvPowerSeries.coeff p.1 (((U.2.2 : unitary JetRing) : JetRing) ^ 6) •
          jetDerivM (Finsupp.toMultiset p.2) (covariantStep μ x) := by
  calc _
    _ = repJetGaugeGroupI U (jetDerivM s (jetDeriv μ x -
        (6 * Complex.I) • ([JetGenerators.dB {} μ]ₐ * x))) := by
      rfl
    -- 1. Split the covariant step: `jetDerivM s` and `repJetGaugeGroupI U` are
    --    linear, and `jetDerivM s (jetDeriv μ x) = jetDerivM (μ ::ₘ s) x` by
    --    `jetDerivM_cons` together with `jetDerivM_add` / `jetDeriv_comm`.
    _ = repJetGaugeGroupI U (jetDerivM (μ ::ₘ s) x) -
        (6 * Complex.I) • repJetGaugeGroupI U (jetDerivM s ([JetGenerators.dB {} μ]ₐ * x)) := by
      sorry
    -- 2. `rw [hx (μ ::ₘ s)]` turns the first term into the expected sum at the
    --    enlarged index `μ ::ₘ s`.
    --
    -- 3. Leibniz on the gauge-field term via `jetDerivM_apply_mul`, then
    --    `repJetGaugeGroupI_apply_mul` to split the action across each product:
    --      ρ (∂_s (B_μ * x)) = ∑_q w_q • (ρ (∂_{q.1} B_μ) * ρ (∂_{q.2} x))
    --    NOTE: `jetDerivM_apply_mul` needs weight `Nat.choose`, not
    --    `Nat.descFactorial`.  At `s = {μ, μ}` the splitting `a = s` wants
    --    `C(2,2) = 1`, but `Nat.descFactorial 2 2 = 2`.  (`descFactorial` is
    --    correct in `hx`: that comes from `jetRingAction` on a
    --    factorial-weighted basis, a different normalisation.)
    --
    -- 4. The gauge field is a coordinate, so it only shifts by a constant:
    --      ρ_U (∂_a B_μ) = ∂_a B_μ + mcShift U [∂_{a+μ} B] • 1
    --    the sector-level counterpart of `BBoson.repJetGaugeGroupI_apply_dB`
    --    transported through `repJetGaugeGroupI_tmul'`, together with
    --    `jetDerivM a [dB {} μ]ₐ = [dB a μ]ₐ`.  Neither exists yet.
    --
    -- 5. The `x`-factor of each term is the hypothesis again, at index `q.2`.
    --
    -- 6. Match against the target, expanded the same way:
    --      ∂_p (D_μ x) = ∂_{μ ::ₘ p} x - 6i • ∂_p (B_μ * x)
    --    Needs a Vandermonde/Pascal identity relating the weights at `μ ::ₘ s`
    --    to those at `s` (reconciling `descFactorial` with `choose`), and
    --    `coeff_p (u ^ 6)` at a shifted index expressed through the
    --    Maurer–Cartan coefficients — the all-orders form of
    --    `pderiv_pow_unitary`, currently only an inline `have` in
    --    `LeptonSinglet`.  That identity is what makes the shift from step 4
    --    cancel the derivative of the hypercharge character.
    _ = ∑ p ∈ Finset.antidiagonal (Multiset.toFinsupp s),
        ((∏ ν, (Multiset.toFinsupp s ν).descFactorial (p.1 ν) : ℕ) : ℂ) •
          MvPowerSeries.coeff p.1 (((U.2.2 : unitary JetRing) : JetRing) ^ 6) •
          jetDerivM (Finsupp.toMultiset p.2) (covariantStep μ x) := by
      sorry

/-- The linear-matter submodule is closed under the gauge group: the gauge action
  preserves the matter degree, because it acts on the matter factor functorially
  in the component space and so intertwines with the canonical inclusion. -/
lemma repJetGaugeGroupI_mem_LinearMatterSubmodule (U : JetGaugeGroupI)
    {x : JetAlgebra} (hx : x ∈ LinearMatterSubmodule) :
    repJetGaugeGroupI U x ∈ LinearMatterSubmodule := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨p, m, rfl⟩ := hz
    rw [repJetGaugeGroupI_tmul_ι]
    exact tmul_ι_mem_LinearMatterSubmodule _ _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u v _ _ hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv
  | smul c u _ hu => rw [map_smul]; exact Submodule.smul_mem _ _ hu

/-- The submodule form of `repJetGaugeGroupI_mem_LinearMatterSubmodule`. -/
lemma map_repJetGaugeGroupI_LinearMatterSubmodule_le (U : JetGaugeGroupI) :
    LinearMatterSubmodule.map (repJetGaugeGroupI U) ≤ LinearMatterSubmodule := by
  rintro x ⟨y, hy, rfl⟩
  exact repJetGaugeGroupI_mem_LinearMatterSubmodule U hy

/-- The gauge action restricts to an automorphism of the linear-matter
  submodule: the reverse inclusion holds by applying the bound to `U⁻¹`. -/
lemma map_repJetGaugeGroupI_LinearMatterSubmodule (U : JetGaugeGroupI) :
    LinearMatterSubmodule.map (repJetGaugeGroupI U) = LinearMatterSubmodule := by
  refine le_antisymm (map_repJetGaugeGroupI_LinearMatterSubmodule_le U) fun x hx => ?_
  exact ⟨repJetGaugeGroupI U⁻¹ x,
    repJetGaugeGroupI_mem_LinearMatterSubmodule U⁻¹ hx,
    repJetGaugeGroupI.self_inv_apply U x⟩

/-- The embedded field-strength derivatives are gauge invariant. -/
lemma repJetGaugeGroupI_fieldStrengthDeriv (U : JetGaugeGroupI)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ ν : Fin 1 ⊕ Fin 3) :
    repJetGaugeGroupI U (fieldStrengthDeriv s μ ν) = fieldStrengthDeriv s μ ν := by
  rw [fieldStrengthDeriv, repJetGaugeGroupI_tmul,
    BBoson.JetAlgebra.repJetGaugeGroupI_fieldStrengthDeriv,
    show LeptonSinglet.JetAlgebra.repJetGaugeGroupI U (1 : LeptonSinglet.JetAlgebra) = 1 from
      map_one (ExteriorAlgebra.map (LeptonSinglet.JetComponentSpace.repJetGaugeGroupI U))]


/-!

## Covariance of the covariant derivatives

The covariant derivatives of the charged lepton transform through the
hypercharge character of the value of the gauge jet at the base point alone:
`ρ_U (D_l ψ_α) = u(0)⁶ • D_l ψ_α`, with no derivative contributions.

The proof works on the lepton-linear model of the `ψ`-sector: B-boson
polynomials tensored with a single unconjugated lepton component function. On
this model the gauge action `ρ`, the covariant step `D_μ`, and a family of
Maurer–Cartan anomaly operators `N_{s,μ}` satisfy a closed commutation algebra:

* `ρ ∘ D_μ = D_μ ∘ ρ + ρ ∘ N_{[],μ}`,
* `N_{s,μ} ∘ D_ν = D_ν ∘ N_{s,μ} + N_{ν::s,μ}`,
* `N_{s,μ} ψ = 0` and `ρ ψ = u(0)⁶ • ψ`,

so by induction every anomaly operator annihilates every covariant derivative,
and covariance propagates along the covariant-derivative recursion.

-/

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- The linear-matter model over a matter target `W`: B-boson polynomials
  tensored with a single matter component function. -/
abbrev MatterLinear (W : Type*) [AddCommGroup W] [Module ℂ W] :=
  (ℂ ⊗[ℝ] BBoson.JetAlgebra) ⊗[ℂ] (DerivAlgebraComplex ⊗[ℂ] W)


/-- The derivative action of a jet on component functions valued in any target
  `W`, acting on the derivative symbols. -/
noncomputable def actionC (χ : JetRing) :
    (DerivAlgebraComplex ⊗[ℂ] W) →ₗ[ℂ] (DerivAlgebraComplex ⊗[ℂ] W) :=
  TensorProduct.map (DerivAlgebraComplex.jetRingAction χ) LinearMap.id

/-- The derivative-symbol shift on component functions valued in any target
  `W`. -/
noncomputable def shiftC (ν : Fin 1 ⊕ Fin 3) :
    (DerivAlgebraComplex ⊗[ℂ] W) →ₗ[ℂ] (DerivAlgebraComplex ⊗[ℂ] W) :=
  TensorProduct.map (DerivAlgebraComplex.deriv ν) LinearMap.id

lemma actionC_shiftC (χ : JetRing) (ν : Fin 1 ⊕ Fin 3) (a : DerivAlgebraComplex ⊗[ℂ] W) :
    actionC χ (shiftC ν a) =
      shiftC ν (actionC χ a) + actionC (MvPowerSeries.pderiv ℂ ν χ) a := by
  have h : (actionC (W := W) χ) ∘ₗ (shiftC ν) =
      (shiftC ν) ∘ₗ (actionC χ) + actionC (MvPowerSeries.pderiv ℂ ν χ) := by
    simp only [actionC, shiftC]
    rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.id_comp,
      show (DerivAlgebraComplex.jetRingAction χ) ∘ₗ (DerivAlgebraComplex.deriv ν) =
        (DerivAlgebraComplex.deriv ν) ∘ₗ (DerivAlgebraComplex.jetRingAction χ) +
          DerivAlgebraComplex.jetRingAction (MvPowerSeries.pderiv ℂ ν χ) from
        LinearMap.ext fun b => DerivAlgebraComplex.jetRingAction_deriv χ ν b,
      TensorProduct.map_add_left]
  exact LinearMap.congr_fun h a

lemma actionC_comm (χ ψ : JetRing) (a : DerivAlgebraComplex ⊗[ℂ] W) :
    actionC χ (actionC ψ a) = actionC ψ (actionC χ a) := by
  have h : (actionC (W := W) χ) ∘ₗ (actionC ψ) = (actionC ψ) ∘ₗ (actionC χ) := by
    simp only [actionC]
    rw [← TensorProduct.map_comp, ← TensorProduct.map_comp,
      show (DerivAlgebraComplex.jetRingAction χ) ∘ₗ (DerivAlgebraComplex.jetRingAction ψ) =
        (DerivAlgebraComplex.jetRingAction ψ) ∘ₗ (DerivAlgebraComplex.jetRingAction χ) from
        LinearMap.ext fun b => DerivAlgebraComplex.jetRingAction_comm χ ψ b]
  exact LinearMap.congr_fun h a

lemma actionC_mul (χ ψ : JetRing) (a : DerivAlgebraComplex ⊗[ℂ] W) :
    actionC (χ * ψ) a = actionC χ (actionC ψ a) := by
  have h : actionC (W := W) (χ * ψ) = (actionC χ) ∘ₗ (actionC ψ) := by
    simp only [actionC]
    rw [← TensorProduct.map_comp, LinearMap.id_comp,
      DerivAlgebraComplex.jetRingAction_mul]
  exact LinearMap.congr_fun h a

lemma actionC_C (c : ℂ) (a : DerivAlgebraComplex ⊗[ℂ] W) :
    actionC (MvPowerSeries.C c : JetRing) a = c • a := by
  have h : actionC (W := W) (MvPowerSeries.C c : JetRing) = c • LinearMap.id := by
    rw [actionC, DerivAlgebraComplex.jetRingAction_C, TensorProduct.map_smul_left,
      TensorProduct.map_id]
  rw [h]
  rfl

/-- The embedding of a lepton component function into the lepton jet algebra. -/
noncomputable def leptonComponentIncl :
    (DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ LeptonSinglet) →ₗ[ℂ] LeptonSinglet.JetAlgebra :=
  (ExteriorAlgebra.ι ℂ) ∘ₗ (LinearMap.inl ℂ (DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ LeptonSinglet)
    (SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
      Module.Dual ℂ (ConjModule LeptonSinglet)))

lemma leptonComponentIncl_apply (a : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ LeptonSinglet) :
    leptonComponentIncl a =
      ExteriorAlgebra.ι ℂ ((a, 0) : LeptonSinglet.JetComponentSpace) := rfl

/-- The inclusion of the lepton-linear elements into the lepton–gauge-sector jet algebra. -/
noncomputable def leptonLinearIncl :
    MatterLinear (Module.Dual ℂ LeptonSinglet) →ₗ[ℂ] JetAlgebra :=
  TensorProduct.map LinearMap.id leptonComponentIncl

lemma leptonLinearIncl_tmul (p : ℂ ⊗[ℝ] BBoson.JetAlgebra) (a : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ LeptonSinglet) :
    leptonLinearIncl (p ⊗ₜ[ℂ] a) = p ⊗ⱼ leptonComponentIncl a := rfl

/-- The derivative action of a jet on the zeroth-order lepton component: the
  scalar action of its value at the base point. -/
lemma actionC_one_tmul (χ : JetRing) (φ : W) :
    actionC χ ((1 : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule)) ⊗ₜ[ℂ] φ) =
      MvPowerSeries.constantCoeff χ •
        ((1 : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule)) ⊗ₜ[ℂ] φ) := by
  rw [actionC, TensorProduct.map_tmul, DerivAlgebraComplex.jetRingAction_apply_one,
    LinearMap.id_coe, id_eq, TensorProduct.smul_tmul']

/-!

### The linear-matter model, uniformly in the matter species

The covariance argument depends on the matter species only through two
parameters: the jet `χ` through which the gauge group acts on the matter
component functions, and the coupling `c` in the covariant step
`D_μ = ∂_μ + c B_μ`. They are tied together by the single hypothesis

`∂_ν χ = -c · (mcShiftSeries U ν []) · χ`

which is exactly what makes the anomaly cancel. Everything below is stated once,
for a general matter target `W`, and instantiated at each species: for the
charged lepton `χ = u^6`, `c = -6i`, and for its conjugate `χ = star u ^ 6`,
`c = +6i`, the hypothesis in both cases being `pderiv_pow_unitary_mcShiftSeries`
and its conjugate.

-/

/-- The covariant step `D_μ = ∂_μ + c B_μ` on the linear-matter model. -/
noncomputable def covStepM (c : ℂ) (μ : Fin 1 ⊕ Fin 3) :
    MatterLinear W →ₗ[ℂ] MatterLinear W :=
  TensorProduct.map (LinearMap.baseChange ℂ (BBoson.JetAlgebra.jetDeriv μ))
      LinearMap.id +
    TensorProduct.map LinearMap.id (shiftC μ) +
    c • TensorProduct.map (LinearMap.mulLeft ℂ ((1 : ℂ) ⊗ₜ[ℝ]
      BBoson.JetAlgebra.ofGenerator (BBoson.JetGenerators.dB {} μ))) LinearMap.id

lemma covStepM_tmul (c : ℂ) (μ : Fin 1 ⊕ Fin 3) (p : ℂ ⊗[ℝ] BBoson.JetAlgebra)
    (a : DerivAlgebraComplex ⊗[ℂ] W) :
    covStepM c μ (p ⊗ₜ[ℂ] a) =
      (LinearMap.baseChange ℂ (BBoson.JetAlgebra.jetDeriv μ) p) ⊗ₜ[ℂ] a +
        p ⊗ₜ[ℂ] shiftC μ a +
        c • ((((1 : ℂ) ⊗ₜ[ℝ] BBoson.JetAlgebra.ofGenerator
          (BBoson.JetGenerators.dB {} μ)) * p) ⊗ₜ[ℂ] a) := by
  simp [covStepM]

/-- The gauge action on the linear-matter model, acting on the matter factor
  through the jet `χ`. -/
noncomputable def repM (U : JetGaugeGroupI) (χ : JetRing) :
    MatterLinear W →ₗ[ℂ] MatterLinear W :=
  TensorProduct.map (BBoson.JetAlgebra.complexRepJetGaugeGroupI U) (actionC χ)

lemma repM_tmul (U : JetGaugeGroupI) (χ : JetRing) (p : ℂ ⊗[ℝ] BBoson.JetAlgebra)
    (a : DerivAlgebraComplex ⊗[ℂ] W) :
    repM U χ (p ⊗ₜ[ℂ] a) =
      (BBoson.JetAlgebra.complexRepJetGaugeGroupI U p) ⊗ₜ[ℂ] actionC χ a := by
  simp [repM]

/-- The Maurer–Cartan anomaly operators on the linear-matter model. -/
noncomputable def anomalyM (U : JetGaugeGroupI) (c : ℂ) (s : List (Fin 1 ⊕ Fin 3))
    (μ : Fin 1 ⊕ Fin 3) : MatterLinear W →ₗ[ℂ] MatterLinear W :=
  TensorProduct.map (LinearMap.baseChange ℂ
      (BBoson.JetAlgebra.mcDeriv U (↑s + {μ}))) LinearMap.id +
    (c * ((BBoson.mcShift U (BBoson.JetComponentSpace.basis
      (BBoson.JetGenerators.dB ↑s μ)) : ℝ) : ℂ)) • LinearMap.id -
    c • TensorProduct.map LinearMap.id (actionC (BBoson.mcShiftSeries U μ s))

lemma anomalyM_tmul (U : JetGaugeGroupI) (c : ℂ) (s : List (Fin 1 ⊕ Fin 3))
    (μ : Fin 1 ⊕ Fin 3) (p : ℂ ⊗[ℝ] BBoson.JetAlgebra)
    (a : DerivAlgebraComplex ⊗[ℂ] W) :
    anomalyM U c s μ (p ⊗ₜ[ℂ] a) =
      (LinearMap.baseChange ℂ (BBoson.JetAlgebra.mcDeriv U (↑s + {μ})) p) ⊗ₜ[ℂ] a +
        (c * ((BBoson.mcShift U (BBoson.JetComponentSpace.basis
          (BBoson.JetGenerators.dB ↑s μ)) : ℝ) : ℂ)) • (p ⊗ₜ[ℂ] a) -
        c • (p ⊗ₜ[ℂ] actionC (BBoson.mcShiftSeries U μ s) a) := by
  simp [anomalyM]

/-- The shift series commutes with any other jet action. -/
lemma actionC_mcShiftSeries_comm (U : JetGaugeGroupI) (μ : Fin 1 ⊕ Fin 3)
    (s : List (Fin 1 ⊕ Fin 3)) (χ : JetRing) (a : DerivAlgebraComplex ⊗[ℂ] W) :
    actionC (BBoson.mcShiftSeries U μ s) (actionC χ a) =
      actionC χ (actionC (BBoson.mcShiftSeries U μ s) a) :=
  actionC_comm _ _ a

/-- The base vector of the model: a matter component function with trivial
  derivative history and unit B-boson coefficient. -/
noncomputable def baseM (φ : W) : MatterLinear W :=
  ((1 : ℂ) ⊗ₜ[ℝ] (1 : BBoson.JetAlgebra)) ⊗ₜ[ℂ]
    ((1 : SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule)) ⊗ₜ[ℂ] φ)

/-- The covariant derivative in the model. -/
noncomputable def DM (c : ℂ) (l : List (Fin 1 ⊕ Fin 3)) (φ : W) : MatterLinear W :=
  l.foldr (fun μ x => covStepM c μ x) (baseM φ)

lemma DM_cons (c : ℂ) (μ : Fin 1 ⊕ Fin 3) (l : List (Fin 1 ⊕ Fin 3)) (φ : W) :
    DM c (μ :: l) φ = covStepM c μ (DM c l φ) := rfl

/-- Multiplication by the unit of the complexified B-boson jet algebra. -/
lemma one_mul_complex (z : ℂ ⊗[ℝ] BBoson.JetAlgebra) :
    ((1 : ℂ) ⊗ₜ[ℝ] (1 : BBoson.JetAlgebra)) * z = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [mul_add, ha, hb]
  | tmul c b => simp [tmul_mul_tmul]

/-- The gauge action commutes with the covariant step up to the gauge action of
  the zeroth anomaly operator. This is where the hypothesis relating `χ` and `c`
  is used, and the only place it is needed. -/
lemma repM_covStepM (U : JetGaugeGroupI) (χ : JetRing) (c : ℂ)
    (hχ : ∀ ν : Fin 1 ⊕ Fin 3, MvPowerSeries.pderiv ℂ ν χ =
      MvPowerSeries.C (-c) * (BBoson.mcShiftSeries U ν [] * χ))
    (μ : Fin 1 ⊕ Fin 3) (x : MatterLinear W) :
    repM U χ (covStepM c μ x) =
      covStepM c μ (repM U χ x) + repM U χ (anomalyM U c [] μ x) := by
  have key : (repM U χ) ∘ₗ (covStepM (W := W) c μ) =
      (covStepM c μ) ∘ₗ (repM U χ) + (repM U χ) ∘ₗ (anomalyM U c [] μ) := by
    refine TensorProduct.ext' fun p a => ?_
    simp only [LinearMap.comp_apply, LinearMap.add_apply, covStepM_tmul,
      anomalyM_tmul, map_add, map_smul, map_sub,
      repM_tmul, Multiset.coe_nil, Multiset.empty_eq_zero, zero_add]
    simp only [BBoson.JetAlgebra.complexRepJetGaugeGroupI_baseChange_jetDeriv,
      actionC_shiftC, hχ, actionC_mul, actionC_C,
      BBoson.JetAlgebra.complexRepJetGaugeGroupI_mul,
      BBoson.JetAlgebra.complexRepJetGaugeGroupI_ofGenerator,
      actionC_mcShiftSeries_comm]
    have hdist : ((1 : ℂ) ⊗ₜ[ℝ] BBoson.JetAlgebra.ofGenerator
          (BBoson.JetGenerators.dB 0 μ) +
        ((BBoson.mcShift U (BBoson.JetComponentSpace.basis
          (BBoson.JetGenerators.dB 0 μ)) : ℝ) : ℂ) •
          ((1 : ℂ) ⊗ₜ[ℝ] (1 : BBoson.JetAlgebra))) *
        BBoson.JetAlgebra.complexRepJetGaugeGroupI U p =
        ((1 : ℂ) ⊗ₜ[ℝ] BBoson.JetAlgebra.ofGenerator (BBoson.JetGenerators.dB 0 μ)) *
          BBoson.JetAlgebra.complexRepJetGaugeGroupI U p +
        ((BBoson.mcShift U (BBoson.JetComponentSpace.basis
          (BBoson.JetGenerators.dB 0 μ)) : ℝ) : ℂ) •
          BBoson.JetAlgebra.complexRepJetGaugeGroupI U p := by
      rw [add_mul, smul_mul_assoc, one_mul_complex]
    simp only [hdist]
    simp only [TensorProduct.tmul_add, TensorProduct.add_tmul, ← TensorProduct.smul_tmul',
      TensorProduct.tmul_smul, smul_add, smul_smul]
    push_cast
    module
  exact LinearMap.congr_fun key x

/-- The anomaly operators commute with the covariant step up to the anomaly
  operator with the derivative direction appended to its history. -/
lemma anomalyM_covStepM (U : JetGaugeGroupI) (c : ℂ) (s : List (Fin 1 ⊕ Fin 3))
    (μ ν : Fin 1 ⊕ Fin 3) (x : MatterLinear W) :
    anomalyM U c s μ (covStepM c ν x) =
      covStepM c ν (anomalyM U c s μ x) + anomalyM U c (ν :: s) μ x := by
  have hT : ((↑s : Multiset (Fin 1 ⊕ Fin 3)) + {μ}) + {ν} =
      (↑(ν :: s) : Multiset (Fin 1 ⊕ Fin 3)) + {μ} := by
    rw [show (↑(ν :: s) : Multiset (Fin 1 ⊕ Fin 3)) = {ν} + ↑s from by
      rw [Multiset.singleton_add, Multiset.cons_coe]]
    ac_rfl
  have hshift : BBoson.JetGenerators.shiftMulti ((↑s : Multiset (Fin 1 ⊕ Fin 3)) + {μ})
      (BBoson.JetGenerators.dB {} ν) =
      BBoson.JetGenerators.dB ((↑s : Multiset (Fin 1 ⊕ Fin 3)) + {μ}) ν := by
    rw [BBoson.JetGenerators.shiftMulti_dB]
    congr 1
  have hm : BBoson.mcShift U (BBoson.JetComponentSpace.basis
      (BBoson.JetGenerators.dB ((↑s : Multiset (Fin 1 ⊕ Fin 3)) + {μ}) ν)) =
      BBoson.mcShift U (BBoson.JetComponentSpace.basis
        (BBoson.JetGenerators.dB (↑(ν :: s) : Multiset (Fin 1 ⊕ Fin 3)) μ)) := by
    rw [BBoson.mcShift_basis_dB_symm, show (↑(ν :: s) : Multiset (Fin 1 ⊕ Fin 3)) =
      ↑s + {ν} from by rw [show (↑(ν :: s) : Multiset (Fin 1 ⊕ Fin 3)) = {ν} + ↑s from by
        rw [Multiset.singleton_add, Multiset.cons_coe]]; ac_rfl]
  have key : (anomalyM U c s μ) ∘ₗ (covStepM (W := W) c ν) =
      (covStepM c ν) ∘ₗ (anomalyM U c s μ) + anomalyM U c (ν :: s) μ := by
    refine TensorProduct.ext' fun p a => ?_
    simp only [LinearMap.comp_apply, LinearMap.add_apply, covStepM_tmul,
      anomalyM_tmul, map_add, map_smul, map_sub, BBoson.mcShiftSeries_cons]
    simp only [BBoson.JetAlgebra.mcDeriv_baseChange_jetDeriv, hT, actionC_shiftC,
      BBoson.JetAlgebra.mcDeriv_baseChange_mul,
      BBoson.JetAlgebra.mcDeriv_baseChange_ofGenerator, hshift, hm]
    have hdist : (((BBoson.mcShift U (BBoson.JetComponentSpace.basis
          (BBoson.JetGenerators.dB (↑(ν :: s) : Multiset (Fin 1 ⊕ Fin 3)) μ)) : ℝ) : ℂ) •
          ((1 : ℂ) ⊗ₜ[ℝ] (1 : BBoson.JetAlgebra))) * p =
        ((BBoson.mcShift U (BBoson.JetComponentSpace.basis
          (BBoson.JetGenerators.dB (↑(ν :: s) : Multiset (Fin 1 ⊕ Fin 3)) μ)) : ℝ) : ℂ) •
          p := by
      rw [smul_mul_assoc, one_mul_complex]
    simp only [hdist]
    simp only [TensorProduct.tmul_add, TensorProduct.add_tmul, ← TensorProduct.smul_tmul',
      smul_add, smul_smul]
    module
  exact LinearMap.congr_fun key x

/-- The anomaly operators annihilate the base vector. -/
lemma anomalyM_baseM (U : JetGaugeGroupI) (c : ℂ) (s : List (Fin 1 ⊕ Fin 3))
    (μ : Fin 1 ⊕ Fin 3) (φ : W) : anomalyM U c s μ (baseM φ) = 0 := by
  rw [baseM, anomalyM_tmul, LinearMap.baseChange_tmul]
  simp only [BBoson.JetAlgebra.mcDeriv_one, TensorProduct.tmul_zero, tmul_zero,
    TensorProduct.zero_tmul, zero_tmul, actionC_one_tmul,
    BBoson.constantCoeff_mcShiftSeries,
    TensorProduct.tmul_smul, smul_smul, zero_add]
  module

/-- The gauge action on the base vector is the value of `χ` at the base point. -/
lemma repM_baseM (U : JetGaugeGroupI) (χ : JetRing) (φ : W) :
    repM U χ (baseM φ) = MvPowerSeries.constantCoeff χ • baseM φ := by
  rw [baseM, repM_tmul, BBoson.JetAlgebra.complexRepJetGaugeGroupI_tmul]
  simp only [BBoson.JetAlgebra.repJetGaugeGroupI_apply_one, actionC_one_tmul,
    TensorProduct.tmul_smul]

/-- Every anomaly operator annihilates every covariant derivative. -/
lemma anomalyM_DM (U : JetGaugeGroupI) (c : ℂ) (l : List (Fin 1 ⊕ Fin 3)) (φ : W) :
    ∀ (s : List (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3), anomalyM U c s μ (DM c l φ) = 0 := by
  induction l with
  | nil => exact fun s μ => anomalyM_baseM U c s μ φ
  | cons ν l ih =>
    intro s μ
    rw [DM_cons, anomalyM_covStepM, ih s μ, map_zero, zero_add, ih (ν :: s) μ]

/-- Covariance of the covariant derivatives on the linear-matter model. -/
lemma repM_DM (U : JetGaugeGroupI) (χ : JetRing) (c : ℂ)
    (hχ : ∀ ν : Fin 1 ⊕ Fin 3, MvPowerSeries.pderiv ℂ ν χ =
      MvPowerSeries.C (-c) * (BBoson.mcShiftSeries U ν [] * χ))
    (l : List (Fin 1 ⊕ Fin 3)) (φ : W) :
    repM U χ (DM c l φ) = MvPowerSeries.constantCoeff χ • DM c l φ := by
  induction l with
  | nil => exact repM_baseM U χ φ
  | cons ν l ih =>
    rw [DM_cons, repM_covStepM U χ c hχ, ih, map_smul, anomalyM_DM U c l φ [] ν,
      map_zero, add_zero]

/-!

### Instantiation at the unconjugated lepton

-/

/-- The unconjugated lepton acts through `χ = u ^ 6` with coupling `c = -6i`. -/
lemma pderiv_pow_six (U : JetGaugeGroupI) (ν : Fin 1 ⊕ Fin 3) :
    MvPowerSeries.pderiv ℂ ν (((U.2.2 : unitary JetRing) : JetRing) ^ 6) =
      MvPowerSeries.C (-(-(6 : ℂ) * Complex.I)) *
        (BBoson.mcShiftSeries U ν [] * ((U.2.2 : unitary JetRing) : JetRing) ^ 6) := by
  rw [BBoson.pderiv_pow_unitary_mcShiftSeries]
  norm_num

/-- The inclusion intertwines the covariant steps. -/
lemma covariantStep_leptonLinearIncl (μ : Fin 1 ⊕ Fin 3)
    (x : MatterLinear (Module.Dual ℂ LeptonSinglet)) :
    covariantStep μ (leptonLinearIncl x) =
      leptonLinearIncl (covStepM (-(6 : ℂ) * Complex.I) μ x) := by
  have key : (covariantStep μ) ∘ₗ leptonLinearIncl =
      leptonLinearIncl ∘ₗ (covStepM (-(6 : ℂ) * Complex.I) μ) := by
    refine TensorProduct.ext' fun p a => ?_
    simp only [LinearMap.comp_apply, leptonLinearIncl_tmul, covStepM_tmul,
      leptonComponentIncl_apply, covariantStep_apply, map_add, map_smul,
      jetDeriv_tmul, LeptonSinglet.JetAlgebra.jetDeriv_ι,
      LeptonSinglet.JetComponentSpace.jetDeriv_inl', ofGenerator, shiftC,
      tmul_mul_tmul, one_mul]
    module
  exact LinearMap.congr_fun key x

/-- The inclusion intertwines the gauge actions. -/
lemma repJetGaugeGroupI_leptonLinearIncl (U : JetGaugeGroupI)
    (x : MatterLinear (Module.Dual ℂ LeptonSinglet)) :
    repJetGaugeGroupI U (leptonLinearIncl x) =
      leptonLinearIncl (repM U (((U.2.2 : unitary JetRing) : JetRing) ^ 6) x) := by
  have key : (repJetGaugeGroupI U) ∘ₗ leptonLinearIncl =
      leptonLinearIncl ∘ₗ (repM U (((U.2.2 : unitary JetRing) : JetRing) ^ 6)) := by
    refine TensorProduct.ext' fun p a => ?_
    simp only [LinearMap.comp_apply, leptonLinearIncl_tmul, repM_tmul,
      leptonComponentIncl_apply, repJetGaugeGroupI_tmul', LeptonSinglet.JetAlgebra.repJetGaugeGroupI_apply,
      ExteriorAlgebra.map_apply_ι, LeptonSinglet.JetComponentSpace.repJetGaugeGroupI_inl',
      actionC]
  exact LinearMap.congr_fun key x

/-- The covariant derivatives are the images of their linear-matter models. -/
lemma Dψ_eq_leptonLinearIncl (l : List (Fin 1 ⊕ Fin 3)) (α : Fin 2) :
    Dψ l α = leptonLinearIncl (DM (-(6 : ℂ) * Complex.I) l
      (LeptonSinglet.basis.dualBasis α)) := by
  induction l with
  | nil =>
    rw [Dψ_nil, show DM (-(6 : ℂ) * Complex.I) [] (LeptonSinglet.basis.dualBasis α) =
        baseM (LeptonSinglet.basis.dualBasis α) from rfl, baseM, leptonLinearIncl_tmul,
      leptonComponentIncl_apply]
    simp only [ofGenerator, LeptonSinglet.JetAlgebra.ofGenerator,
      LeptonSinglet.JetComponentSpace.basis_dψ_nil]
  | cons ν l ih =>
    rw [Dψ_cons, ih, covariantStep_leptonLinearIncl]
    rfl

/-- Covariance of the covariant derivatives of the charged lepton: a jet of
  gauge transformations acts on `D_l ψ_α` through the hypercharge character of
  its value at the base point alone, with no derivative contributions. This is
  the statement that the covariant derivative of a charged field is again a
  charged field of the same charge. -/
lemma repJetGaugeGroupI_Dψ (U : JetGaugeGroupI) (l : List (Fin 1 ⊕ Fin 3)) (α : Fin 2) :
    repJetGaugeGroupI U (Dψ l α) = U.eval.2.2 ^ 6 • Dψ l α := by
  have hval : ((U.eval.2.2 : unitary ℂ) : ℂ) =
      MvPowerSeries.constantCoeff ((U.2.2 : unitary JetRing) : JetRing) := rfl
  rw [Dψ_eq_leptonLinearIncl, repJetGaugeGroupI_leptonLinearIncl,
    repM_DM U _ _ (pderiv_pow_six U), map_smul, ← Dψ_eq_leptonLinearIncl,
    Submonoid.smul_def, SubmonoidClass.coe_pow, hval, map_pow]

/-!

## Covariant derivatives of the conjugate lepton

The conjugate lepton `ψ̄` carries the opposite hypercharge: its component
functions transform through the conjugate-contragredient power series
`(star u) ^ 6`, so under a jet gauge transformation `∂_μ ψ̄_α` shifts by
`+ 6 i mc_μ ψ̄_α` and the covariant step is `D̄_μ = ∂_μ - 6 i B_μ`.

The covariance proof mirrors the unconjugated case on the conjugate-linear
model, with the coupling `6 i` replaced by `- 6 i` throughout.

-/

/-- The embedding of a conjugate lepton component function into the lepton jet
  algebra. -/
noncomputable def conjLeptonComponentIncl :
    (DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule LeptonSinglet)) →ₗ[ℂ]
      LeptonSinglet.JetAlgebra :=
  (ExteriorAlgebra.ι ℂ) ∘ₗ (LinearMap.inr ℂ
    (SymmetricAlgebra ℂ (Module.Dual ℂ Lorentz.CoℂModule) ⊗[ℂ]
      Module.Dual ℂ LeptonSinglet) (DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule LeptonSinglet)))

lemma conjLeptonComponentIncl_apply (a : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule LeptonSinglet)) :
    conjLeptonComponentIncl a =
      ExteriorAlgebra.ι ℂ ((0, a) : LeptonSinglet.JetComponentSpace) := rfl

/-- The inclusion of the conjugate-linear elements into the lepton–gauge-sector jet algebra. -/
noncomputable def conjLeptonLinearIncl :
    MatterLinear (Module.Dual ℂ (ConjModule LeptonSinglet)) →ₗ[ℂ] JetAlgebra :=
  TensorProduct.map LinearMap.id conjLeptonComponentIncl

lemma conjLeptonLinearIncl_tmul (p : ℂ ⊗[ℝ] BBoson.JetAlgebra)
    (a : DerivAlgebraComplex ⊗[ℂ] Module.Dual ℂ (ConjModule LeptonSinglet)) :
    conjLeptonLinearIncl (p ⊗ₜ[ℂ] a) = p ⊗ⱼ conjLeptonComponentIncl a := rfl

/-- The conjugate lepton acts through `χ = star u ^ 6` with coupling `c = +6i`. -/
lemma pderiv_star_pow_six (U : JetGaugeGroupI) (ν : Fin 1 ⊕ Fin 3) :
    MvPowerSeries.pderiv ℂ ν (star ((U.2.2 : unitary JetRing) : JetRing) ^ 6) =
      MvPowerSeries.C (-((6 : ℂ) * Complex.I)) *
        (BBoson.mcShiftSeries U ν [] * star ((U.2.2 : unitary JetRing) : JetRing) ^ 6) := by
  rw [BBoson.pderiv_pow_unitary_star_mcShiftSeries]
  norm_num

/-- The inclusion intertwines the conjugate covariant steps. -/
lemma covariantStepBar_conjLeptonLinearIncl (μ : Fin 1 ⊕ Fin 3)
    (x : MatterLinear (Module.Dual ℂ (ConjModule LeptonSinglet))) :
    covariantStepBar μ (conjLeptonLinearIncl x) =
      conjLeptonLinearIncl (covStepM ((6 : ℂ) * Complex.I) μ x) := by
  have key : (covariantStepBar μ) ∘ₗ conjLeptonLinearIncl =
      conjLeptonLinearIncl ∘ₗ (covStepM ((6 : ℂ) * Complex.I) μ) := by
    refine TensorProduct.ext' fun p a => ?_
    simp only [LinearMap.comp_apply, conjLeptonLinearIncl_tmul, covStepM_tmul,
      conjLeptonComponentIncl_apply, covariantStepBar_apply, map_add, map_smul,
      jetDeriv_tmul, LeptonSinglet.JetAlgebra.jetDeriv_ι,
      LeptonSinglet.JetComponentSpace.jetDeriv_inr', ofGenerator, shiftC,
      tmul_mul_tmul, one_mul]
  exact LinearMap.congr_fun key x

/-- The inclusion intertwines the gauge actions. -/
lemma repJetGaugeGroupI_conjLeptonLinearIncl (U : JetGaugeGroupI)
    (x : MatterLinear (Module.Dual ℂ (ConjModule LeptonSinglet))) :
    repJetGaugeGroupI U (conjLeptonLinearIncl x) =
      conjLeptonLinearIncl (repM U (star ((U.2.2 : unitary JetRing) : JetRing) ^ 6) x) := by
  have key : (repJetGaugeGroupI U) ∘ₗ conjLeptonLinearIncl =
      conjLeptonLinearIncl ∘ₗ (repM U (star ((U.2.2 : unitary JetRing) : JetRing) ^ 6)) := by
    refine TensorProduct.ext' fun p a => ?_
    simp only [LinearMap.comp_apply, conjLeptonLinearIncl_tmul, repM_tmul,
      conjLeptonComponentIncl_apply, repJetGaugeGroupI_tmul', LeptonSinglet.JetAlgebra.repJetGaugeGroupI_apply,
      ExteriorAlgebra.map_apply_ι, LeptonSinglet.JetComponentSpace.repJetGaugeGroupI_inr',
      actionC]
  exact LinearMap.congr_fun key x

/-- The conjugate covariant derivatives are the images of their linear-matter
  models. -/
lemma Dbarψ_eq_conjLeptonLinearIncl (l : List (Fin 1 ⊕ Fin 3)) (α : Fin 2) :
    Dbarψ l α = conjLeptonLinearIncl (DM ((6 : ℂ) * Complex.I) l
      (LeptonSinglet.basis.conj.dualBasis α)) := by
  induction l with
  | nil =>
    rw [Dbarψ_nil, show DM ((6 : ℂ) * Complex.I) [] (LeptonSinglet.basis.conj.dualBasis α) =
        baseM (LeptonSinglet.basis.conj.dualBasis α) from rfl, baseM,
      conjLeptonLinearIncl_tmul, conjLeptonComponentIncl_apply]
    simp only [ofGenerator, LeptonSinglet.JetAlgebra.ofGenerator,
      LeptonSinglet.JetComponentSpace.basis_dbarψ, DerivAlgebraComplex.basis_nil]
  | cons ν l ih =>
    rw [Dbarψ_cons, ih, covariantStepBar_conjLeptonLinearIncl]
    rfl

/-- Covariance of the covariant derivatives of the conjugate lepton: a jet of
  gauge transformations acts on `D̄_l ψ̄_α` through the conjugate hypercharge
  character of its value at the base point alone. -/
lemma repJetGaugeGroupI_Dbarψ (U : JetGaugeGroupI) (l : List (Fin 1 ⊕ Fin 3)) (α : Fin 2) :
    repJetGaugeGroupI U (Dbarψ l α) = (star U.eval.2.2) ^ 6 • Dbarψ l α := by
  have hval : ((star U.eval.2.2 : unitary ℂ) : ℂ) =
      MvPowerSeries.constantCoeff (star ((U.2.2 : unitary JetRing) : JetRing)) := by
    rw [Unitary.coe_star, JetRing.constantCoeff_star]
    rfl
  rw [Dbarψ_eq_conjLeptonLinearIncl, repJetGaugeGroupI_conjLeptonLinearIncl,
    repM_DM U _ _ (pderiv_star_pow_six U), map_smul, ← Dbarψ_eq_conjLeptonLinearIncl,
    Submonoid.smul_def, SubmonoidClass.coe_pow, hval, map_pow]

/-!

## C. The invariant generators and the gauge action as an algebra homomorphism

The field strengths of the B boson, embedded in the lepton–gauge-sector jet algebra, are exactly
invariant; the covariant derivatives of the lepton and of its conjugate transform
by the hypercharge characters `u(0)^6` and `u(0)^{-6}` of the value of the gauge
jet at the base point. The gauge invariants of the lepton–gauge-sector jet algebra are contained
in the algebra generated by these three families.

-/

/-!

### The gauge action as an algebra homomorphism, and the intertwining

-/

/-- The complexified B-boson gauge action as an algebra homomorphism. -/
noncomputable def complexRepAlgHom (U : JetGaugeGroupI) :
    (ℂ ⊗[ℝ] BBoson.JetAlgebra) →ₐ[ℂ] (ℂ ⊗[ℝ] BBoson.JetAlgebra) :=
  AlgHom.ofLinearMap (BBoson.JetAlgebra.complexRepJetGaugeGroupI U)
    (by
      rw [Algebra.TensorProduct.one_def, BBoson.JetAlgebra.complexRepJetGaugeGroupI_tmul,
        BBoson.JetAlgebra.repJetGaugeGroupI_apply_one])
    (BBoson.JetAlgebra.complexRepJetGaugeGroupI_mul U)

@[simp]
lemma complexRepAlgHom_apply (U : JetGaugeGroupI) (p : ℂ ⊗[ℝ] BBoson.JetAlgebra) :
    complexRepAlgHom U p = BBoson.JetAlgebra.complexRepJetGaugeGroupI U p := rfl

/-- The gauge action as an algebra homomorphism. -/
noncomputable def repAlgHom (U : JetGaugeGroupI) : JetAlgebra →ₐ[ℂ] JetAlgebra :=
  Algebra.TensorProduct.map (complexRepAlgHom U)
    (ExteriorAlgebra.map (LeptonSinglet.JetComponentSpace.repJetGaugeGroupI U))

lemma repAlgHom_tmul (U : JetGaugeGroupI) (p : ℂ ⊗[ℝ] BBoson.JetAlgebra)
    (l : LeptonSinglet.JetAlgebra) :
    repAlgHom U (p ⊗ⱼ l) = (BBoson.JetAlgebra.complexRepJetGaugeGroupI U p) ⊗ⱼ
      (ExteriorAlgebra.map (LeptonSinglet.JetComponentSpace.repJetGaugeGroupI U) l) := rfl

lemma repJetGaugeGroupI_eq_repAlgHom (U : JetGaugeGroupI) (x : JetAlgebra) :
    repJetGaugeGroupI U x = repAlgHom U x := by
  induction x using JetAlgebra.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul p l =>
    rw [repJetGaugeGroupI_tmul']
    rfl

/-- The gauge action is multiplicative (term-level form avoiding elaboration
  blowups on the tensor stack). -/
lemma repJetGaugeGroupI_mul' (U : JetGaugeGroupI) (a b : JetAlgebra) :
    repJetGaugeGroupI U (a * b) =
      repJetGaugeGroupI U a * repJetGaugeGroupI U b :=
  (repJetGaugeGroupI_eq_repAlgHom U (a * b)).trans
    ((map_mul (repAlgHom U) a b).trans
      (congrArg₂ (· * ·) (repJetGaugeGroupI_eq_repAlgHom U a).symm
        (repJetGaugeGroupI_eq_repAlgHom U b).symm))

set_option maxHeartbeats 400000 in
/-- On gauge jets with trivial value at the base point, the covariant elements
  are exactly invariant, so the gauge action intertwines the covariant
  substitution with the B-boson action alone. -/
lemma repJetGaugeGroupI_covSubst (U : JetGaugeGroupI) (hU : U.eval.2.2 = 1)
    (x : JetAlgebra) :
    repJetGaugeGroupI U (covSubst x) =
      covSubst (mapB (BBoson.JetAlgebra.complexRepJetGaugeGroupI U) x) := by
  have hcovfix : (repAlgHom U).comp covExtHom = covExtHom := by
    refine ExteriorAlgebra.hom_ext (LinearMap.ext fun m => ?_)
    simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, Function.comp_apply,
      AlgHom.toLinearMap_apply, covExtHom_ι]
    have hlin : (repAlgHom U).toLinearMap ∘ₗ covMap = covMap := by
      refine LeptonSinglet.JetComponentSpace.basis.ext fun g => ?_
      rw [LinearMap.comp_apply, covMap_basis, AlgHom.toLinearMap_apply,
        ← repJetGaugeGroupI_eq_repAlgHom]
      cases g with
      | dψ s α =>
        rw [show covGenerator (.dψ s α) = Dψ (sortList s) α from rfl,
          repJetGaugeGroupI_Dψ, hU, one_pow, one_smul]
      | dbarψ s α =>
        rw [show covGenerator (.dbarψ s α) = Dbarψ (sortList s) α from rfl,
          repJetGaugeGroupI_Dbarψ, hU, star_one, one_pow, one_smul]
    exact LinearMap.congr_fun hlin m
  induction x using JetAlgebra.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]
  | tmul p l =>
    rw [mapB_tmul, covSubst_tmul, covSubst_tmul]
    rw [repJetGaugeGroupI_eq_repAlgHom]
    have hm : repAlgHom U ((p ⊗ⱼ (1 : LeptonSinglet.JetAlgebra)) * covExtHom l) =
        repAlgHom U (p ⊗ⱼ (1 : LeptonSinglet.JetAlgebra)) *
          repAlgHom U (covExtHom l) := map_mul _ _ _
    have h1 : repAlgHom U (p ⊗ⱼ (1 : LeptonSinglet.JetAlgebra)) =
        (BBoson.JetAlgebra.complexRepJetGaugeGroupI U p) ⊗ⱼ 1 := by
      rw [repAlgHom_tmul]
      congr 1
      exact (ExteriorAlgebra.map _).map_one
    have h2 : repAlgHom U (covExtHom l) = covExtHom l := AlgHom.congr_fun hcovfix l
    rw [hm, h1, h2]

end JetAlgebra

end LeptonGaugeSector
