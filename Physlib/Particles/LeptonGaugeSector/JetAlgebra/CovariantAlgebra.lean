/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.CovariantDeriv
/-!
# The linear-matter submodule of the lepton–gauge-sector jet algebra

The submodule spanned by a single matter component function times a B-boson
polynomial, its closure under the total derivative and the covariant steps, and
the oddness of its elements in the fermionic case.
-/

@[expose] public section

set_option maxHeartbeats 1000000

namespace LeptonGaugeSector
open TensorProduct StandardModel

namespace JetAlgebra

/-!

### The linear-matter submodule

-/

/-- The linear-matter submodule: the elements of the jet algebra in which the
  matter coordinates appear exactly linearly, spanned by the products of a
  gauge-sector element with a single matter component function.

  The construction does not depend on the matter content. A jet algebra of this
  shape is `G ⊗[ℂ] ExteriorAlgebra ℂ M`, with `G` the gauge-sector algebra and
  `M` the space of matter component functions; the fermionic degree is the
  exterior grading of the second factor, and degree one is the image of
  `ExteriorAlgebra.ι`. For several matter species `M` is their direct sum and the
  same definition applies verbatim.

  This is the submodule the covariance argument for the covariant derivatives
  lives on. It is closed under the gauge group
  (`repJetGaugeGroupI_mem_LinearMatterSubmodule`), under the total derivative
  and under the covariant steps, and it is where the Maurer–Cartan anomaly
  operators close: in higher fermionic degree they do not, because the gauge
  action on the exterior algebra is an algebra map and so multiplies the
  hypercharge characters. -/
noncomputable def LinearMatterSubmodule : Submodule ℂ JetAlgebra :=
  Submodule.span ℂ {x : JetAlgebra | ∃ (p : ℂ ⊗[ℝ] BBoson.JetAlgebra)
    (m : LeptonSinglet.JetComponentSpace), x = p ⊗ₜ[ℂ] ExteriorAlgebra.ι ℂ m}

/-- The spanning elements: a gauge-sector coefficient times a single matter
  component function. -/
lemma tmul_ι_mem_LinearMatterSubmodule (p : ℂ ⊗[ℝ] BBoson.JetAlgebra)
    (m : LeptonSinglet.JetComponentSpace) :
    p ⊗ₜ[ℂ] ExteriorAlgebra.ι ℂ m ∈ LinearMatterSubmodule :=
  Submodule.subset_span ⟨p, m, rfl⟩

/-!

The remaining results in this section are specific to *fermionic* matter: they
express that the linear-matter elements are odd. Nothing above depends on them,
and nothing that follows — the closure of the submodule under the derivative,
the covariant steps, or the gauge group — does either. For bosonic matter the
matter factor is a symmetric rather than an exterior algebra, the same
definition of `LinearMatterSubmodule` applies with the corresponding canonical
inclusion, and only this anticommutation block is dropped.

-/

/-- Right distributivity on the jet algebra, with the multiplication forced to
  the `JetAlgebra` instance. Stating it explicitly keeps `rw` from having to
  match through the tensor-product instance path. -/
lemma distrib_add_mul (a b c : JetAlgebra) : (a + b) * c = a * c + b * c := by grind

/-- Left distributivity on the jet algebra; see `distrib_add_mul`. -/
lemma distrib_mul_add (a b c : JetAlgebra) : a * (b + c) = a * b + a * c := by grind

set_option maxHeartbeats 1000000 in
/-- Linear-matter elements anticommute against the spanning elements. -/
lemma tmul_ι_mul_add_swap_of_mem (p : ℂ ⊗[ℝ] BBoson.JetAlgebra)
    (m : LeptonSinglet.JetComponentSpace) {y : JetAlgebra}
    (hy : y ∈ LinearMatterSubmodule) :
    (p ⊗ₜ[ℂ] ExteriorAlgebra.ι ℂ m) * y + y * (p ⊗ₜ[ℂ] ExteriorAlgebra.ι ℂ m) = 0 := by
  have hd₁ := distrib_add_mul
  have hd₂ := distrib_mul_add
  have hz₁ : ∀ a : JetAlgebra, 0 * a = 0 := fun a => zero_mul a
  have hz₂ : ∀ a : JetAlgebra, a * 0 = 0 := fun a => mul_zero a
  have hs₁ : ∀ (c : ℂ) (a b : JetAlgebra), (c • a) * b = c • (a * b) :=
    fun c a b => smul_mul_assoc c a b
  have hs₂ : ∀ (c : ℂ) (a b : JetAlgebra), a * (c • b) = c • (a * b) :=
    fun c a b => mul_smul_comm c a b
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨q, n, rfl⟩ := hz
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      mul_comm q p, ← TensorProduct.tmul_add, ExteriorAlgebra.ι_add_mul_swap,
      TensorProduct.tmul_zero]
  | zero => rw [hz₂, hz₁, add_zero]
  | add u v _ _ hu hv =>
    rw [hd₂, hd₁]
    calc (p ⊗ₜ[ℂ] ExteriorAlgebra.ι ℂ m) * u + (p ⊗ₜ[ℂ] ExteriorAlgebra.ι ℂ m) * v +
          (u * (p ⊗ₜ[ℂ] ExteriorAlgebra.ι ℂ m) + v * (p ⊗ₜ[ℂ] ExteriorAlgebra.ι ℂ m)) =
        ((p ⊗ₜ[ℂ] ExteriorAlgebra.ι ℂ m) * u + u * (p ⊗ₜ[ℂ] ExteriorAlgebra.ι ℂ m)) +
          ((p ⊗ₜ[ℂ] ExteriorAlgebra.ι ℂ m) * v + v * (p ⊗ₜ[ℂ] ExteriorAlgebra.ι ℂ m)) := by
          abel
      _ = 0 := by rw [hu, hv, add_zero]
  | smul c u _ hu =>
    rw [hs₂, hs₁, ← smul_add, hu, smul_zero]

/-- Linear-matter elements anticommute: they are odd. -/
lemma mul_add_swap_of_mem {x y : JetAlgebra} (hx : x ∈ LinearMatterSubmodule)
    (hy : y ∈ LinearMatterSubmodule) : x * y + y * x = 0 := by
  have hd₁ := distrib_add_mul
  have hd₂ := distrib_mul_add
  have hz₁ : ∀ a : JetAlgebra, 0 * a = 0 := fun a => zero_mul a
  have hz₂ : ∀ a : JetAlgebra, a * 0 = 0 := fun a => mul_zero a
  have hs₁ : ∀ (c : ℂ) (a b : JetAlgebra), (c • a) * b = c • (a * b) :=
    fun c a b => smul_mul_assoc c a b
  have hs₂ : ∀ (c : ℂ) (a b : JetAlgebra), a * (c • b) = c • (a * b) :=
    fun c a b => mul_smul_comm c a b
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨p, m, rfl⟩ := hz
    exact tmul_ι_mul_add_swap_of_mem p m hy
  | zero => rw [hz₁, hz₂, add_zero]
  | add u v _ _ hu hv =>
    rw [hd₁, hd₂]
    calc u * y + v * y + (y * u + y * v) =
        (u * y + y * u) + (v * y + y * v) := by abel
      _ = 0 := by rw [hu, hv, add_zero]
  | smul c u _ hu =>
    rw [hs₁, hs₂, ← smul_add, hu, smul_zero]

/-- Linear-matter elements square to zero. -/
lemma mul_self_of_mem {x : JetAlgebra} (hx : x ∈ LinearMatterSubmodule) :
    x * x = 0 := by
  have h2 : (2 : ℂ) • (x * x) = 0 := by
    rw [two_smul]
    exact mul_add_swap_of_mem hx hx
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

/-- The linear-matter submodule is preserved by the total derivative. -/
lemma jetDeriv_mem_LinearMatterSubmodule (μ : Fin 1 ⊕ Fin 3) {x : JetAlgebra}
    (hx : x ∈ LinearMatterSubmodule) : jetDeriv μ x ∈ LinearMatterSubmodule := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨p, m, rfl⟩ := hz
    rw [jetDeriv_tmul, LeptonSinglet.JetAlgebra.jetDeriv_ι]
    exact Submodule.add_mem _ (tmul_ι_mem_LinearMatterSubmodule _ _)
      (tmul_ι_mem_LinearMatterSubmodule _ _)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u v _ _ hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv
  | smul c u _ hu => rw [map_smul]; exact Submodule.smul_mem _ _ hu

/-- The linear-matter submodule is preserved by multiplication by a gauge-field
  generator, which lives in the bosonic factor. -/
lemma dB_mul_mem_LinearMatterSubmodule (μ : Fin 1 ⊕ Fin 3) {x : JetAlgebra}
    (hx : x ∈ LinearMatterSubmodule) :
    [JetGenerators.dB {} μ]ₐ * x ∈ LinearMatterSubmodule := by
  have hd₂ := distrib_mul_add
  have hz₂ : ∀ a : JetAlgebra, a * 0 = 0 := fun a => mul_zero a
  have hs₂ : ∀ (c : ℂ) (a b : JetAlgebra), a * (c • b) = c • (a * b) :=
    fun c a b => mul_smul_comm c a b
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨p, m, rfl⟩ := hz
    rw [show ([JetGenerators.dB {} μ]ₐ : JetAlgebra) =
        ((1 : ℂ) ⊗ₜ[ℝ] BBoson.JetAlgebra.ofGenerator
          (BBoson.JetGenerators.dB {} μ)) ⊗ₜ[ℂ]
          (1 : LeptonSinglet.JetAlgebra) from rfl,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact tmul_ι_mem_LinearMatterSubmodule _ _
  | zero => rw [hz₂]; exact Submodule.zero_mem _
  | add u v _ _ hu hv => rw [hd₂]; exact Submodule.add_mem _ hu hv
  | smul c u _ hu => rw [hs₂]; exact Submodule.smul_mem _ _ hu

/-- The covariant derivatives of the lepton are linear in the matter fields. -/
lemma Dψ_mem_LinearMatterSubmodule (l : List (Fin 1 ⊕ Fin 3)) (α : Fin 2) :
    Dψ l α ∈ LinearMatterSubmodule := by
  induction l with
  | nil =>
    rw [show Dψ [] α = ((1 : ℂ) ⊗ₜ[ℝ] (1 : BBoson.JetAlgebra)) ⊗ₜ[ℂ]
      ExteriorAlgebra.ι ℂ (LeptonSinglet.JetComponentSpace.basis (.dψ {} α)) from rfl]
    exact tmul_ι_mem_LinearMatterSubmodule _ _
  | cons ν l ih =>
    simp only [Dψ_cons, covariantStep_apply]
    exact Submodule.sub_mem _ (jetDeriv_mem_LinearMatterSubmodule ν ih)
      (Submodule.smul_mem _ _ (dB_mul_mem_LinearMatterSubmodule ν ih))

/-- The covariant derivatives of the conjugate lepton are linear in the matter
  fields. -/
lemma Dbarψ_mem_LinearMatterSubmodule (l : List (Fin 1 ⊕ Fin 3)) (α : Fin 2) :
    Dbarψ l α ∈ LinearMatterSubmodule := by
  induction l with
  | nil =>
    rw [show Dbarψ [] α = ((1 : ℂ) ⊗ₜ[ℝ] (1 : BBoson.JetAlgebra)) ⊗ₜ[ℂ]
      ExteriorAlgebra.ι ℂ (LeptonSinglet.JetComponentSpace.basis (.dbarψ {} α)) from rfl]
    exact tmul_ι_mem_LinearMatterSubmodule _ _
  | cons ν l ih =>
    simp only [Dbarψ_cons, covariantStepBar_apply]
    exact Submodule.add_mem _ (jetDeriv_mem_LinearMatterSubmodule ν ih)
      (Submodule.smul_mem _ _ (dB_mul_mem_LinearMatterSubmodule ν ih))

/-- The covariant lepton derivatives anticommute with the conjugate covariant
  derivatives: both are odd elements of the linear-matter submodule. -/
lemma Dψ_mul_Dbarψ_anticomm (l l' : List (Fin 1 ⊕ Fin 3)) (α β : Fin 2) :
    Dψ l α * Dbarψ l' β = -(Dbarψ l' β * Dψ l α) :=
  eq_neg_of_add_eq_zero_left
    (mul_add_swap_of_mem (Dψ_mem_LinearMatterSubmodule l α)
      (Dbarψ_mem_LinearMatterSubmodule l' β))

lemma covGenerator_mem_LinearMatterSubmodule (g : LeptonSinglet.JetGenerators) :
    covGenerator g ∈ LinearMatterSubmodule := by
  cases g with
  | dψ s α => exact Dψ_mem_LinearMatterSubmodule (sortList s) α
  | dbarψ s α => exact Dbarψ_mem_LinearMatterSubmodule (sortList s) α

lemma covMap_mem_LinearMatterSubmodule (m : LeptonSinglet.JetComponentSpace) :
    covMap m ∈ LinearMatterSubmodule := by
  rw [covMap, Module.Basis.constr_apply]
  exact Submodule.sum_mem _ fun g _ =>
    Submodule.smul_mem _ _ (covGenerator_mem_LinearMatterSubmodule g)

lemma covMap_mul_self (m : LeptonSinglet.JetComponentSpace) :
    covMap m * covMap m = 0 :=
  mul_self_of_mem (covMap_mem_LinearMatterSubmodule m)

/-- The covariant substitution on the fermionic factor. -/
noncomputable def covExtHom : LeptonSinglet.JetAlgebra →ₐ[ℂ] JetAlgebra :=
  ExteriorAlgebra.lift ℂ ⟨covMap, covMap_mul_self⟩

@[simp]
lemma covExtHom_ι (m : LeptonSinglet.JetComponentSpace) :
    covExtHom (ExteriorAlgebra.ι ℂ m) = covMap m := by
  rw [covExtHom, ExteriorAlgebra.lift_ι_apply]

/-- Elements of the B-boson factor are central in the lepton–gauge-sector jet algebra. -/
lemma tmul_one_mul_comm (p : ℂ ⊗[ℝ] BBoson.JetAlgebra) (y : JetAlgebra) :
    (p ⊗ₜ[ℂ] (1 : LeptonSinglet.JetAlgebra)) * y =
      y * (p ⊗ₜ[ℂ] (1 : LeptonSinglet.JetAlgebra)) := by
  have hd₁ : ∀ a b c : JetAlgebra, (a + b) * c = a * c + b * c := by grind
  have hd₂ := distrib_mul_add
  have hz₁ : ∀ a : JetAlgebra, 0 * a = 0 := fun a => zero_mul a
  have hz₂ : ∀ a : JetAlgebra, a * 0 = 0 := fun a => mul_zero a
  induction y using TensorProduct.induction_on with
  | zero => rw [hz₂, hz₁]
  | add a b ha hb => simp only [hd₁, hd₂, ha, hb]
  | tmul q l =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      mul_comm, one_mul, mul_one]

/-- The covariant substitution: the algebra endomorphism of the lepton–gauge-sector jet algebra
  fixing the B-boson factor and sending each plain fermionic generator to its
  covariant version. -/
noncomputable def covSubst : JetAlgebra →ₐ[ℂ] JetAlgebra :=
  Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft covExtHom
    (fun p y => (tmul_one_mul_comm p (covExtHom y)))

lemma covSubst_tmul (p : ℂ ⊗[ℝ] BBoson.JetAlgebra) (l : LeptonSinglet.JetAlgebra) :
    covSubst (p ⊗ₜ[ℂ] l) = (p ⊗ₜ[ℂ] (1 : LeptonSinglet.JetAlgebra)) * covExtHom l := by
  rw [covSubst, Algebra.TensorProduct.lift_tmul]
  rfl

@[simp]
lemma covSubst_tmul_one (p : ℂ ⊗[ℝ] BBoson.JetAlgebra) :
    covSubst (p ⊗ₜ[ℂ] (1 : LeptonSinglet.JetAlgebra)) = p ⊗ₜ[ℂ] 1 := by
  have h1 : covExtHom (1 : LeptonSinglet.JetAlgebra) = 1 := covExtHom.map_one
  have hmul : ∀ a : JetAlgebra, a * 1 = a := fun a => mul_one a
  rw [covSubst_tmul, h1, hmul]

@[simp]
lemma covSubst_one_tmul_ι (m : LeptonSinglet.JetComponentSpace) :
    covSubst ((1 : ℂ ⊗[ℝ] BBoson.JetAlgebra) ⊗ₜ[ℂ] ExteriorAlgebra.ι ℂ m) =
      covMap m := by
  have hone : ∀ a : JetAlgebra, 1 * a = a := fun a => one_mul a
  rw [covSubst_tmul, covExtHom_ι, ← Algebra.TensorProduct.one_def, hone]
end JetAlgebra

end LeptonGaugeSector
