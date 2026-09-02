/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.StandardModel.JetAlgebra.MassWeightPoly
public import Physlib.Particles.StandardModel.JetAlgebra.FieldAlgebra
public import Physlib.Particles.StandardModel.Matter.BosonicAlgebra.TransformsIn
public import Physlib.Particles.StandardModel.Matter.FermionicAlgebra.TransformsIn
public import Physlib.Particles.StandardModel.IsStandardModel.MassWeight.Filtration
/-!
# The jet algebra of the Standard Model is a Standard Model

## i. Overview

Everything the abstract theory of `IsStandardModel` asks of an algebra — thirteen families
of derivative symbols, their gauge and Lorentz transformation laws, their mass weights and
their statistics — has been established for the concrete jet algebra
`StandardModel.JetAlgebra` one sector at a time. This file collects those facts into the
single statement `JetAlgebra.isStandardModel`, and then draws the two consequences that
make the statement worth having.

The assembly is mechanical but for one point, which is the content of section A. The three
sector inclusions `includeFermion`, `includeHiggs`, `includeGauge` are equivariant for the
jet gauge action and for the Lorentz action, because both actions are tensor products of
the sector actions and each sector action fixes the unit. `includeGauge` was treated when
the gauge sector was shown to be a gauge field; the other two are proved here, and with
them every transformation law of a matter symbol is its sector's own law, pushed through an
algebra map.

Once the instance exists, two things follow. The field algebra it generates is the whole
algebra — the fields of the Standard Model generate the algebra in which its Lagrangian
lives, since nothing else is available to write down — so the mass-weight submodules stop
being intersections with the field algebra and become the honest eigenspaces of
`massWeightPoly` on the whole of `JetAlgebra`, and are worth defining on `JetAlgebra`
directly.

And then the classification of invariants of mass dimension at most four applies to *every*
element of the algebra of that dimension, with no side condition left to check. That is
the result this whole chain of files exists for, and section F states it: for an arbitrary
`x : JetAlgebra` of mass weight at most eight,

`x` is fixed by the jet gauge group and by the Lorentz group
  ↔ `x` is a combination of the constant term, the Higgs mass term `H† H`, and the
    dimension-four Standard Model Lagrangian.

Nothing is assumed of `x` beyond its mass weight: not membership of a subalgebra, not
covariance, not a bound of the form `0 < w`. Every hypothesis of the abstract statement has
discharged against the concrete algebra. The `⊔ S` form, which sets aside a submodule of
higher-dimension operators, follows as a generalization for a reader who wants one.

## ii. Key results

- `JetAlgebra.mem_massWeightSubmoduleLE_eight_and_invariant_iff_lagrangian` : the theorem
  the chain exists for. For every element of the jet algebra of mass weight at most eight
  — with no other hypothesis of any kind — invariance under the jet gauge group and the
  Lorentz group holds exactly when the element is a combination of the constant term, the
  Higgs mass term `H† H`, and the dimension-four Standard Model Lagrangian.
- `JetAlgebra.mem_massWeightSubmoduleLE_eight_sup_and_invariant_iff_lagrangian` : the same
  classification modulo a submodule of higher-dimension operators set aside.
- `JetAlgebra.isStandardModel` : the jet algebra of the Standard Model is a Standard Model.
- `JetAlgebra.isStandardModel_fieldAlgebra_eq_top` : its field algebra is everything.
- `JetAlgebra.massWeightSubmodule`, `JetAlgebra.massWeightSubmoduleLE` : the mass-weight
  grading and its filtration, on the jet algebra itself.

## iii. Table of contents

- A. The sector inclusions are equivariant
  - A.1. The sector inclusions on pure tensors
  - A.2. The unit of the gauge sector
  - A.3. Equivariance for the jet gauge action
  - A.4. Equivariance for the Lorentz action
- B. The jet gauge transformation of the field symbols
  - B.1. The Higgs families
  - B.2. The fermion families
- C. The Lorentz transformation of the field symbols
  - C.1. The Higgs families
  - C.2. The fermion families
- D. The Standard Model instance
- E. The field algebra is everything
  - E.1. The field algebra
  - E.2. The collapse of the graded pieces
  - E.3. The mass-weight filtration of the jet algebra
- F. The Standard Model Lagrangian

-/

@[expose] public section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
set_option synthInstance.maxSize 2048
set_option maxRecDepth 8000

namespace StandardModel

namespace JetAlgebra

open TensorProduct Matrix MatrixGroups Lorentz

/-!

## A. The sector inclusions are equivariant

Both the jet gauge action and the Lorentz action on the jet algebra are tensor products of
the three sector actions. A sector inclusion puts the unit in the other two factors, so
equivariance is exactly the statement that the other two actions fix their units, which
they do — they are actions by algebra maps.

-/

/-!

### A.1. The sector inclusions on pure tensors

-/

/-- The fermionic inclusion puts the unit in the Higgs and gauge factors. -/
lemma includeFermion_apply (f : FermionJetAlgebra) :
    includeFermion f = ((f ⊗ₜ[ℂ] (1 : HiggsJetAlgebra)) ⊗ₜ[ℂ]
      (1 : ℂ ⊗[ℝ] GaugeJetAlgebra)) := rfl

/-- The Higgs inclusion puts the unit in the fermionic and gauge factors. -/
lemma includeHiggs_apply (h : HiggsJetAlgebra) :
    includeHiggs h = (((1 : FermionJetAlgebra) ⊗ₜ[ℂ] h) ⊗ₜ[ℂ]
      (1 : ℂ ⊗[ℝ] GaugeJetAlgebra)) := rfl

/-!

### A.2. The unit of the gauge sector

-/

/-- The jet gauge action on the complexified gauge sector fixes the unit. -/
lemma complexRepJetGaugeGroupI_apply_one (U : JetGaugeGroupI) :
    GaugeJetAlgebra.complexRepJetGaugeGroupI U (1 : ℂ ⊗[ℝ] GaugeJetAlgebra) = 1 := by
  rw [Algebra.TensorProduct.one_def, GaugeJetAlgebra.complexRepJetGaugeGroupI_tmul,
    GaugeJetAlgebra.repJetGaugeGroupI_apply_one]

/-- The Lorentz action on the complexified gauge sector fixes the unit. -/
lemma complexRepLorentzGroup_apply_one (Λ : SL(2,ℂ)) :
    GaugeJetAlgebra.complexRepLorentzGroup Λ (1 : ℂ ⊗[ℝ] GaugeJetAlgebra) = 1 := by
  rw [Algebra.TensorProduct.one_def, GaugeJetAlgebra.complexRepLorentzGroup_tmul,
    GaugeJetAlgebra.repLorentzGroup_apply_one]

/-!

### A.3. Equivariance for the jet gauge action

-/

/-- The jet gauge action restricts to the fermionic sector's own action. -/
lemma repJetGaugeGroupI_includeFermion (U : JetGaugeGroupI) (f : FermionJetAlgebra) :
    repJetGaugeGroupI U (includeFermion f)
      = includeFermion (FermionJetAlgebra.repJetGaugeGroupI U f) := by
  rw [includeFermion_apply, repJetGaugeGroupI_tmul,
    show (FermionJetAlgebra.repJetGaugeGroupI.tprod HiggsJetAlgebra.repJetGaugeGroupI) U
        (f ⊗ₜ[ℂ] (1 : HiggsJetAlgebra))
      = (FermionJetAlgebra.repJetGaugeGroupI U f) ⊗ₜ[ℂ]
        (HiggsJetAlgebra.repJetGaugeGroupI U (1 : HiggsJetAlgebra)) from rfl,
    show HiggsJetAlgebra.repJetGaugeGroupI U (1 : HiggsJetAlgebra) = 1 from
      BosonicAlgebra.repJetGaugeGroupI_apply_one _ _ U,
    complexRepJetGaugeGroupI_apply_one, includeFermion_apply]

/-- The jet gauge action restricts to the Higgs sector's own action. -/
lemma repJetGaugeGroupI_includeHiggs (U : JetGaugeGroupI) (h : HiggsJetAlgebra) :
    repJetGaugeGroupI U (includeHiggs h)
      = includeHiggs (HiggsJetAlgebra.repJetGaugeGroupI U h) := by
  rw [includeHiggs_apply, repJetGaugeGroupI_tmul,
    show (FermionJetAlgebra.repJetGaugeGroupI.tprod HiggsJetAlgebra.repJetGaugeGroupI) U
        ((1 : FermionJetAlgebra) ⊗ₜ[ℂ] h)
      = (FermionJetAlgebra.repJetGaugeGroupI U (1 : FermionJetAlgebra)) ⊗ₜ[ℂ]
        (HiggsJetAlgebra.repJetGaugeGroupI U h) from rfl,
    show FermionJetAlgebra.repJetGaugeGroupI U (1 : FermionJetAlgebra) = 1 from
      FermionicAlgebra.repJetGaugeGroupI_apply_one _ _ U,
    complexRepJetGaugeGroupI_apply_one, includeHiggs_apply]

/-!

### A.4. Equivariance for the Lorentz action

-/

/-- The Lorentz action restricts to the fermionic sector's own action. -/
lemma repLorentzGroup_includeFermion (Λ : SL(2,ℂ)) (f : FermionJetAlgebra) :
    repLorentzGroup Λ (includeFermion f)
      = includeFermion (FermionJetAlgebra.repLorentzGroup Λ f) := by
  rw [includeFermion_apply, repLorentzGroup_tmul,
    show (FermionJetAlgebra.repLorentzGroup.tprod HiggsJetAlgebra.repLorentzGroup) Λ
        (f ⊗ₜ[ℂ] (1 : HiggsJetAlgebra))
      = (FermionJetAlgebra.repLorentzGroup Λ f) ⊗ₜ[ℂ]
        (HiggsJetAlgebra.repLorentzGroup Λ (1 : HiggsJetAlgebra)) from rfl,
    show HiggsJetAlgebra.repLorentzGroup Λ (1 : HiggsJetAlgebra) = 1 from
      BosonicAlgebra.repLorentzGroup_apply_one _ Λ,
    complexRepLorentzGroup_apply_one, includeFermion_apply]

/-- The Lorentz action restricts to the Higgs sector's own action. -/
lemma repLorentzGroup_includeHiggs (Λ : SL(2,ℂ)) (h : HiggsJetAlgebra) :
    repLorentzGroup Λ (includeHiggs h)
      = includeHiggs (HiggsJetAlgebra.repLorentzGroup Λ h) := by
  rw [includeHiggs_apply, repLorentzGroup_tmul,
    show (FermionJetAlgebra.repLorentzGroup.tprod HiggsJetAlgebra.repLorentzGroup) Λ
        ((1 : FermionJetAlgebra) ⊗ₜ[ℂ] h)
      = (FermionJetAlgebra.repLorentzGroup Λ (1 : FermionJetAlgebra)) ⊗ₜ[ℂ]
        (HiggsJetAlgebra.repLorentzGroup Λ h) from rfl,
    show FermionJetAlgebra.repLorentzGroup Λ (1 : FermionJetAlgebra) = 1 from
      FermionicAlgebra.repLorentzGroup_apply_one _ Λ,
    complexRepLorentzGroup_apply_one, includeHiggs_apply]

/-!

## B. The jet gauge transformation of the field symbols

`TransformsIn` asks that a jet of gauge transformations mix a derivative symbol with the
lower symbols by the all-orders Leibniz convolution of the base-point Taylor coefficients
of the gauge jet. Each sector proves that law for its own symbols; the inclusions of
section A carry it to the full algebra, and the species bridge of
`Physlib.Particles.StandardModel.Fermions.JetAlgebra.Species` moves the fermionic law from
the total target space `FermionSpace` down to the individual species.

-/

/-!

### B.1. The Higgs families

-/

/-- The Higgs symbols transform in the jet gauge representation carried by the jets of the
  Higgs field. -/
theorem transformsIn_higgsField :
    TransformsIn (B := JetAlgebra) repJetGaugeGroupI HiggsVec.repJetGaugeGroupI
      higgsField := by
  intro U φ s
  rw [higgsField_eq_includeHiggs, repJetGaugeGroupI_includeHiggs,
    show HiggsJetAlgebra.repJetGaugeGroupI U
        (BosonicAlgebra.iteratedJetDeriv s (BosonicAlgebra.ofField φ))
      = _ from BosonicAlgebra.repJetGaugeGroupI_iteratedJetDeriv_ofField
        HiggsVec.repJetGaugeGroupI HiggsVec.repJetGaugeGroupI_smul U φ s,
    map_multiset_sum, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
  rw [Function.comp_apply, ← higgsField_eq_includeHiggs]

/-- The conjugate Higgs symbols transform in the conjugate of the jet gauge representation
  carried by the jets of the Higgs field. -/
theorem transformsIn_conjHiggsField :
    TransformsIn (B := JetAlgebra) repJetGaugeGroupI (repConj HiggsVec.repJetGaugeGroupI)
      conjHiggsField := by
  intro U φ s
  rw [conjHiggsField_eq_includeHiggs, repJetGaugeGroupI_includeHiggs,
    show HiggsJetAlgebra.repJetGaugeGroupI U
        (BosonicAlgebra.iteratedJetDeriv s (BosonicAlgebra.ofConjField φ))
      = _ from BosonicAlgebra.repJetGaugeGroupI_iteratedJetDeriv_ofConjField
        HiggsVec.repJetGaugeGroupI HiggsVec.repJetGaugeGroupI_smul U φ s,
    map_multiset_sum, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
  rw [Function.comp_apply, ← conjHiggsField_eq_includeHiggs]

/-!

### B.2. The fermion families

-/

/-- The jet gauge transformation law of a fermion species: a family of symbols obtained
  from the total fermionic symbols by pulling covectors back along a projection
  intertwining the two jet gauge actions transforms in the species' own representation. -/
private lemma transformsIn_species {W : Type} [AddCommGroup W] [Module ℂ W]
    (repW : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] W)) (p : FermionSpace →ₗ[ℂ] W)
    (hp : ∀ U : JetGaugeGroupI, (LinearMap.lTensor JetRing p).comp
        (FermionSpace.repJetGaugeGroupI U)
      = (repW U).comp (LinearMap.lTensor JetRing p))
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ W →ₗ[ℂ] JetAlgebra}
    (hF : ∀ s φ, F s φ = fermionSymbol s (Module.Dual.transpose p φ)) :
    TransformsIn (B := JetAlgebra) repJetGaugeGroupI repW F := by
  intro U φ s
  rw [hF, fermionSymbol_eq_includeFermion, repJetGaugeGroupI_includeFermion,
    show FermionJetAlgebra.repJetGaugeGroupI U
        (FermionicAlgebra.iteratedJetDeriv s
          (FermionicAlgebra.ofField (Module.Dual.transpose p φ)))
      = _ from FermionicAlgebra.repJetGaugeGroupI_iteratedJetDeriv_ofField
        FermionSpace.repJetGaugeGroupI FermionSpace.repJetGaugeGroupI_smul U _ s,
    map_multiset_sum, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun q _ => ?_)
  rw [Function.comp_apply, ← fermionSymbol_eq_includeFermion, hF]
  exact congrArg (fermionSymbol q.2)
    (LinearMap.congr_fun (repDualCoeff_comp p hp U⁻¹ q.1) φ)

/-- The base-point Taylor coefficients of two conjugate jet gauge actions are intertwined,
  on the component-function index, by the conjugate of any map of value spaces intertwining
  the unconjugated coefficients: conjugation changes neither the underlying maps nor the
  real directions in which the coefficients are taken. -/
private lemma repDualCoeff_repConj_transpose {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {repV : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] V)}
    {repW : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] W)} (p : V →ₗ[ℂ] W)
    (hp : ∀ (U : JetGaugeGroupI) (s : Multiset (Fin 1 ⊕ Fin 3)),
      p.comp (IsGaugeField.repCoeff repV U s) = (IsGaugeField.repCoeff repW U s).comp p)
    (U : JetGaugeGroupI) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ (ConjModule W)) :
    IsGaugeField.repDualCoeff (repConj repV) U s
        (Module.Dual.transpose (ConjModule.map p) φ)
      = Module.Dual.transpose (ConjModule.map p)
          (IsGaugeField.repDualCoeff (repConj repW) U s φ) := by
  refine LinearMap.ext fun v => ?_
  show φ (ConjModule.map p (IsGaugeField.repCoeff (repConj repV) U s v))
    = φ (IsGaugeField.repCoeff (repConj repW) U s (ConjModule.map p v))
  rw [GaugeAlgebra.repCoeff_repConj, GaugeAlgebra.repCoeff_repConj]
  exact congrArg φ (LinearMap.congr_fun (hp U s) v)

/-- The jet gauge transformation law of the conjugate symbols of a fermion species: the law
  of the species itself, read on the conjugate representations. -/
private lemma transformsIn_conjSpecies {W : Type} [AddCommGroup W] [Module ℂ W]
    (repW : Representation ℂ JetGaugeGroupI (JetRing ⊗[ℂ] W)) (p : FermionSpace →ₗ[ℂ] W)
    (hp : ∀ U : JetGaugeGroupI, (LinearMap.lTensor JetRing p).comp
        (FermionSpace.repJetGaugeGroupI U)
      = (repW U).comp (LinearMap.lTensor JetRing p))
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule W) →ₗ[ℂ] JetAlgebra}
    (hF : ∀ s φ, F s φ = conjFermionSymbol s
      (Module.Dual.transpose (ConjModule.map p) φ)) :
    TransformsIn (B := JetAlgebra) repJetGaugeGroupI (repConj repW) F := by
  intro U φ s
  rw [hF, conjFermionSymbol_eq_includeFermion, repJetGaugeGroupI_includeFermion,
    show FermionJetAlgebra.repJetGaugeGroupI U
        (FermionicAlgebra.iteratedJetDeriv s
          (FermionicAlgebra.ofConjField (Module.Dual.transpose (ConjModule.map p) φ)))
      = _ from FermionicAlgebra.repJetGaugeGroupI_iteratedJetDeriv_ofConjField
        FermionSpace.repJetGaugeGroupI FermionSpace.repJetGaugeGroupI_smul U _ s,
    map_multiset_sum, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun q _ => ?_)
  rw [Function.comp_apply, ← conjFermionSymbol_eq_includeFermion, hF]
  exact congrArg (conjFermionSymbol q.2)
    (repDualCoeff_repConj_transpose p (fun U' s' => repCoeff_comp p hp U' s') U⁻¹ q.1 φ)


/-- The symbols of the `i`-th generation down-type quark singlet transform in the jet gauge
  representation carried by the jets of that species. -/
theorem transformsIn_downSingletField (i : Fin 3) :
    TransformsIn (B := JetAlgebra) repJetGaugeGroupI DownSinglet.repJetGaugeGroupI
      (downSingletField i) :=
  transformsIn_species _ _ (FermionSpace.lTensor_downSingletProj_repJetGaugeGroupI i)
    (downSingletField_eq_fermionSymbol i)

/-- The conjugate symbols of the `i`-th generation down-type quark singlet transform in the
  conjugate of the jet gauge representation carried by the jets of that species. -/
theorem transformsIn_conjDownSingletField (i : Fin 3) :
    TransformsIn (B := JetAlgebra) repJetGaugeGroupI
      (repConj DownSinglet.repJetGaugeGroupI) (conjDownSingletField i) :=
  transformsIn_conjSpecies _ _ (FermionSpace.lTensor_downSingletProj_repJetGaugeGroupI i)
    (conjDownSingletField_eq_conjFermionSymbol i)


/-- The symbols of the `i`-th generation up-type quark singlet transform in the jet gauge
  representation carried by the jets of that species. -/
theorem transformsIn_upSingletField (i : Fin 3) :
    TransformsIn (B := JetAlgebra) repJetGaugeGroupI UpSinglet.repJetGaugeGroupI
      (upSingletField i) :=
  transformsIn_species _ _ (FermionSpace.lTensor_upSingletProj_repJetGaugeGroupI i)
    (upSingletField_eq_fermionSymbol i)

/-- The conjugate symbols of the `i`-th generation up-type quark singlet transform in the
  conjugate of the jet gauge representation carried by the jets of that species. -/
theorem transformsIn_conjUpSingletField (i : Fin 3) :
    TransformsIn (B := JetAlgebra) repJetGaugeGroupI
      (repConj UpSinglet.repJetGaugeGroupI) (conjUpSingletField i) :=
  transformsIn_conjSpecies _ _ (FermionSpace.lTensor_upSingletProj_repJetGaugeGroupI i)
    (conjUpSingletField_eq_conjFermionSymbol i)


/-- The symbols of the `i`-th generation quark doublet transform in the jet gauge
  representation carried by the jets of that species. -/
theorem transformsIn_quarkDoubletField (i : Fin 3) :
    TransformsIn (B := JetAlgebra) repJetGaugeGroupI QuarkDoublet.repJetGaugeGroupI
      (quarkDoubletField i) :=
  transformsIn_species _ _ (FermionSpace.lTensor_quarkDoubletProj_repJetGaugeGroupI i)
    (quarkDoubletField_eq_fermionSymbol i)

/-- The conjugate symbols of the `i`-th generation quark doublet transform in the
  conjugate of the jet gauge representation carried by the jets of that species. -/
theorem transformsIn_conjQuarkDoubletField (i : Fin 3) :
    TransformsIn (B := JetAlgebra) repJetGaugeGroupI
      (repConj QuarkDoublet.repJetGaugeGroupI) (conjQuarkDoubletField i) :=
  transformsIn_conjSpecies _ _ (FermionSpace.lTensor_quarkDoubletProj_repJetGaugeGroupI i)
    (conjQuarkDoubletField_eq_conjFermionSymbol i)


/-- The symbols of the `i`-th generation lepton doublet transform in the jet gauge
  representation carried by the jets of that species. -/
theorem transformsIn_leptonDoubletField (i : Fin 3) :
    TransformsIn (B := JetAlgebra) repJetGaugeGroupI LeptonDoublet.repJetGaugeGroupI
      (leptonDoubletField i) :=
  transformsIn_species _ _ (FermionSpace.lTensor_leptonDoubletProj_repJetGaugeGroupI i)
    (leptonDoubletField_eq_fermionSymbol i)

/-- The conjugate symbols of the `i`-th generation lepton doublet transform in the
  conjugate of the jet gauge representation carried by the jets of that species. -/
theorem transformsIn_conjLeptonDoubletField (i : Fin 3) :
    TransformsIn (B := JetAlgebra) repJetGaugeGroupI
      (repConj LeptonDoublet.repJetGaugeGroupI) (conjLeptonDoubletField i) :=
  transformsIn_conjSpecies _ _ (FermionSpace.lTensor_leptonDoubletProj_repJetGaugeGroupI i)
    (conjLeptonDoubletField_eq_conjFermionSymbol i)


/-- The symbols of the `i`-th generation charged-lepton singlet transform in the jet gauge
  representation carried by the jets of that species. -/
theorem transformsIn_leptonSingletField (i : Fin 3) :
    TransformsIn (B := JetAlgebra) repJetGaugeGroupI LeptonSinglet.repJetGaugeGroupI
      (leptonSingletField i) :=
  transformsIn_species _ _ (FermionSpace.lTensor_leptonSingletProj_repJetGaugeGroupI i)
    (leptonSingletField_eq_fermionSymbol i)

/-- The conjugate symbols of the `i`-th generation charged-lepton singlet transform in the
  conjugate of the jet gauge representation carried by the jets of that species. -/
theorem transformsIn_conjLeptonSingletField (i : Fin 3) :
    TransformsIn (B := JetAlgebra) repJetGaugeGroupI
      (repConj LeptonSinglet.repJetGaugeGroupI) (conjLeptonSingletField i) :=
  transformsIn_conjSpecies _ _ (FermionSpace.lTensor_leptonSingletProj_repJetGaugeGroupI i)
    (conjLeptonSingletField_eq_conjFermionSymbol i)
/-!

## C. The Lorentz transformation of the field symbols

`IsLorentzDerivTransforms` asks that each derivative slot of a symbol mix into all tuples
of directions by the columns of the Lorentz matrix, while the value index transforms by the
contragredient of the species' Lorentz representation. The mixing of the slots is
`IsLorentzDeriv.rep_iteratedD_ofFn`, available because the total derivative on the jet
algebra is a Lorentz vector; what is left is the undifferentiated law at `n = 0`, which is
the equivariance of the component functions of each sector.

-/

/-!

### C.1. The Higgs families

The Higgs is a Lorentz scalar, so its value index carries the trivial representation and
the conjugate index its conjugate.

-/

/-- The Higgs symbols transform as the derivative symbols of a Lorentz scalar. -/
theorem isLorentzDerivTransforms_higgsField :
    IsLorentzDerivTransforms (A := JetAlgebra) repLorentzGroup
      (Representation.trivial ℂ SL(2,ℂ) HiggsVec) higgsField := by
  intro Λ n l φ
  refine (Lorentz.IsLorentzDeriv.rep_iteratedD_ofFn jetDeriv_comm Λ l
    (includeHiggs (BosonicAlgebra.ofField φ))).trans ?_
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [repLorentzGroup_includeHiggs,
    show HiggsJetAlgebra.repLorentzGroup Λ (BosonicAlgebra.ofField φ)
      = BosonicAlgebra.ofField ((Representation.trivial ℂ SL(2,ℂ) HiggsVec).dual Λ φ) from
      BosonicAlgebra.repLorentzGroup_ofField _ Λ φ]
  rfl

/-- The conjugate Higgs symbols transform as the derivative symbols of the conjugate of a
  Lorentz scalar. -/
theorem isLorentzDerivTransforms_conjHiggsField :
    IsLorentzDerivTransforms (A := JetAlgebra) repLorentzGroup
      (Representation.trivial ℂ SL(2,ℂ) HiggsVec).conj conjHiggsField := by
  intro Λ n l φ
  refine (Lorentz.IsLorentzDeriv.rep_iteratedD_ofFn jetDeriv_comm Λ l
    (includeHiggs (BosonicAlgebra.ofConjField φ))).trans ?_
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [repLorentzGroup_includeHiggs,
    show HiggsJetAlgebra.repLorentzGroup Λ (BosonicAlgebra.ofConjField φ)
      = BosonicAlgebra.ofConjField
        ((Representation.trivial ℂ SL(2,ℂ) HiggsVec).conj.dual Λ φ) from
      BosonicAlgebra.repLorentzGroup_ofConjField _ Λ φ]
  rfl

/-!

### C.2. The fermion families

The Lorentz action on `FermionSpace` is species-diagonal, so the contragredient action on a
covector pulled back from a species is the pullback of the species' own contragredient
action; that identity is definitional, and it is the only input the species need beyond the
law for the total fermionic symbols.

-/

/-- The Lorentz transformation law of a fermion species: a family of symbols obtained from
  the total fermionic symbols by pulling covectors back along a projection whose
  contragredient is species-diagonal transforms in the species' own Weyl representation. -/
private lemma isLorentzDerivTransforms_species {W : Type} [AddCommGroup W] [Module ℂ W]
    (repW : Representation ℂ SL(2,ℂ) W) (p : FermionSpace →ₗ[ℂ] W)
    (hdual : ∀ (Λ : SL(2,ℂ)) (φ : Module.Dual ℂ W),
      FermionSpace.repLorentzGroup.dual Λ (Module.Dual.transpose p φ)
        = Module.Dual.transpose p (repW.dual Λ φ))
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ W →ₗ[ℂ] JetAlgebra}
    (hF : ∀ s φ, F s φ = fermionSymbol s (Module.Dual.transpose p φ)) :
    IsLorentzDerivTransforms (A := JetAlgebra) repLorentzGroup repW F := by
  intro Λ n l φ
  rw [hF]
  refine (Lorentz.IsLorentzDeriv.rep_iteratedD_ofFn jetDeriv_comm Λ l
    (includeFermion (FermionicAlgebra.ofField (Module.Dual.transpose p φ)))).trans ?_
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [repLorentzGroup_includeFermion,
    show FermionJetAlgebra.repLorentzGroup Λ
        (FermionicAlgebra.ofField (Module.Dual.transpose p φ))
      = FermionicAlgebra.ofField
        (FermionSpace.repLorentzGroup.dual Λ (Module.Dual.transpose p φ)) from
      FermionicAlgebra.repLorentzGroup_ofField _ Λ _,
    hdual, hF]
  rfl

/-- The Lorentz transformation law of the conjugate symbols of a fermion species: the law
  of the species itself, read on the conjugate representations. -/
private lemma isLorentzDerivTransforms_conjSpecies {W : Type} [AddCommGroup W]
    [Module ℂ W] (repW : Representation ℂ SL(2,ℂ) W) (p : FermionSpace →ₗ[ℂ] W)
    (hdual : ∀ (Λ : SL(2,ℂ)) (φ : Module.Dual ℂ (ConjModule W)),
      FermionSpace.repLorentzGroup.conj.dual Λ
          (Module.Dual.transpose (ConjModule.map p) φ)
        = Module.Dual.transpose (ConjModule.map p) (repW.conj.dual Λ φ))
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule W) →ₗ[ℂ] JetAlgebra}
    (hF : ∀ s φ, F s φ = conjFermionSymbol s
      (Module.Dual.transpose (ConjModule.map p) φ)) :
    IsLorentzDerivTransforms (A := JetAlgebra) repLorentzGroup repW.conj F := by
  intro Λ n l φ
  rw [hF]
  refine (Lorentz.IsLorentzDeriv.rep_iteratedD_ofFn jetDeriv_comm Λ l
    (includeFermion (FermionicAlgebra.ofConjField
      (Module.Dual.transpose (ConjModule.map p) φ)))).trans ?_
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [repLorentzGroup_includeFermion,
    show FermionJetAlgebra.repLorentzGroup Λ
        (FermionicAlgebra.ofConjField (Module.Dual.transpose (ConjModule.map p) φ))
      = FermionicAlgebra.ofConjField (FermionSpace.repLorentzGroup.conj.dual Λ
          (Module.Dual.transpose (ConjModule.map p) φ)) from
      FermionicAlgebra.repLorentzGroup_ofConjField _ Λ _,
    hdual, hF]
  rfl


/-- The symbols of the `i`-th generation down-type quark singlet transform as the derivative
  symbols of a Weyl spinor in that species' Lorentz representation. -/
theorem isLorentzDerivTransforms_downSingletField (i : Fin 3) :
    IsLorentzDerivTransforms (A := JetAlgebra) repLorentzGroup
      DownSinglet.repLorentzGroup (downSingletField i) :=
  isLorentzDerivTransforms_species _ _ (fun _ _ => rfl)
    (downSingletField_eq_fermionSymbol i)

/-- The conjugate symbols of the `i`-th generation down-type quark singlet transform as the
  derivative symbols of the conjugate Weyl spinor. -/
theorem isLorentzDerivTransforms_conjDownSingletField (i : Fin 3) :
    IsLorentzDerivTransforms (A := JetAlgebra) repLorentzGroup
      DownSinglet.repLorentzGroup.conj (conjDownSingletField i) :=
  isLorentzDerivTransforms_conjSpecies _ _ (fun _ _ => rfl)
    (conjDownSingletField_eq_conjFermionSymbol i)


/-- The symbols of the `i`-th generation up-type quark singlet transform as the derivative
  symbols of a Weyl spinor in that species' Lorentz representation. -/
theorem isLorentzDerivTransforms_upSingletField (i : Fin 3) :
    IsLorentzDerivTransforms (A := JetAlgebra) repLorentzGroup
      UpSinglet.repLorentzGroup (upSingletField i) :=
  isLorentzDerivTransforms_species _ _ (fun _ _ => rfl)
    (upSingletField_eq_fermionSymbol i)

/-- The conjugate symbols of the `i`-th generation up-type quark singlet transform as the
  derivative symbols of the conjugate Weyl spinor. -/
theorem isLorentzDerivTransforms_conjUpSingletField (i : Fin 3) :
    IsLorentzDerivTransforms (A := JetAlgebra) repLorentzGroup
      UpSinglet.repLorentzGroup.conj (conjUpSingletField i) :=
  isLorentzDerivTransforms_conjSpecies _ _ (fun _ _ => rfl)
    (conjUpSingletField_eq_conjFermionSymbol i)


/-- The symbols of the `i`-th generation quark doublet transform as the derivative
  symbols of a Weyl spinor in that species' Lorentz representation. -/
theorem isLorentzDerivTransforms_quarkDoubletField (i : Fin 3) :
    IsLorentzDerivTransforms (A := JetAlgebra) repLorentzGroup
      QuarkDoublet.repLorentzGroup (quarkDoubletField i) :=
  isLorentzDerivTransforms_species _ _ (fun _ _ => rfl)
    (quarkDoubletField_eq_fermionSymbol i)

/-- The conjugate symbols of the `i`-th generation quark doublet transform as the
  derivative symbols of the conjugate Weyl spinor. -/
theorem isLorentzDerivTransforms_conjQuarkDoubletField (i : Fin 3) :
    IsLorentzDerivTransforms (A := JetAlgebra) repLorentzGroup
      QuarkDoublet.repLorentzGroup.conj (conjQuarkDoubletField i) :=
  isLorentzDerivTransforms_conjSpecies _ _ (fun _ _ => rfl)
    (conjQuarkDoubletField_eq_conjFermionSymbol i)


/-- The symbols of the `i`-th generation lepton doublet transform as the derivative
  symbols of a Weyl spinor in that species' Lorentz representation. -/
theorem isLorentzDerivTransforms_leptonDoubletField (i : Fin 3) :
    IsLorentzDerivTransforms (A := JetAlgebra) repLorentzGroup
      LeptonDoublet.repLorentzGroup (leptonDoubletField i) :=
  isLorentzDerivTransforms_species _ _ (fun _ _ => rfl)
    (leptonDoubletField_eq_fermionSymbol i)

/-- The conjugate symbols of the `i`-th generation lepton doublet transform as the
  derivative symbols of the conjugate Weyl spinor. -/
theorem isLorentzDerivTransforms_conjLeptonDoubletField (i : Fin 3) :
    IsLorentzDerivTransforms (A := JetAlgebra) repLorentzGroup
      LeptonDoublet.repLorentzGroup.conj (conjLeptonDoubletField i) :=
  isLorentzDerivTransforms_conjSpecies _ _ (fun _ _ => rfl)
    (conjLeptonDoubletField_eq_conjFermionSymbol i)


/-- The symbols of the `i`-th generation charged-lepton singlet transform as the derivative
  symbols of a Weyl spinor in that species' Lorentz representation. -/
theorem isLorentzDerivTransforms_leptonSingletField (i : Fin 3) :
    IsLorentzDerivTransforms (A := JetAlgebra) repLorentzGroup
      LeptonSinglet.repLorentzGroup (leptonSingletField i) :=
  isLorentzDerivTransforms_species _ _ (fun _ _ => rfl)
    (leptonSingletField_eq_fermionSymbol i)

/-- The conjugate symbols of the `i`-th generation charged-lepton singlet transform as the
  derivative symbols of the conjugate Weyl spinor. -/
theorem isLorentzDerivTransforms_conjLeptonSingletField (i : Fin 3) :
    IsLorentzDerivTransforms (A := JetAlgebra) repLorentzGroup
      LeptonSinglet.repLorentzGroup.conj (conjLeptonSingletField i) :=
  isLorentzDerivTransforms_conjSpecies _ _ (fun _ _ => rfl)
    (conjLeptonSingletField_eq_conjFermionSymbol i)

/-!

## D. The Standard Model instance

Every obligation of `IsStandardModel` is now in hand: the gauge field is a gauge field, the
twelve matter families transform in their jet gauge representations and their Lorentz
representations, the fifteen generating families are monomial eigenvectors of
`massWeightPoly` at the mass weights the structure predicts, and the statistics of the
symbols are the three facts of `JetAlgebra.Generators` — the gauge symbols are central, the
Higgs symbols commute with everything, and the fermion symbols anticommute.

-/

/-- The jet algebra of the Standard Model is a Standard Model: with the jet gauge action,
  the Lorentz action, the mass-weight grading and the thirteen families of derivative
  symbols built in the preceding files, it satisfies every axiom of `IsStandardModel`.

  This is the point at which the abstract theory of `IsStandardModel` — its covariant
  reduction, its mass-weight filtration and its classification of invariants — becomes a
  theory of the concrete algebra in which a Standard Model Lagrangian is written. -/
theorem isStandardModel : IsStandardModel JetAlgebra repJetGaugeGroupI repLorentzGroup
    massWeightPoly higgsField conjHiggsField gaugeField
    downSingletField conjDownSingletField upSingletField conjUpSingletField
    quarkDoubletField conjQuarkDoubletField leptonDoubletField conjLeptonDoubletField
    leptonSingletField conjLeptonSingletField where
  repJet_A := isGaugeField
  repJet_H := transformsIn_higgsField
  repJet_barH := transformsIn_conjHiggsField
  repJet_d := transformsIn_downSingletField
  repJet_bard := transformsIn_conjDownSingletField
  repJet_u := transformsIn_upSingletField
  repJet_baru := transformsIn_conjUpSingletField
  repJet_Q := transformsIn_quarkDoubletField
  repJet_barQ := transformsIn_conjQuarkDoubletField
  repJet_L := transformsIn_leptonDoubletField
  repJet_barL := transformsIn_conjLeptonDoubletField
  repJet_e := transformsIn_leptonSingletField
  repJet_bare := transformsIn_conjLeptonSingletField
  repLorentz_H := isLorentzDerivTransforms_higgsField
  repLorentz_barH := isLorentzDerivTransforms_conjHiggsField
  repLorentz_d := isLorentzDerivTransforms_downSingletField
  repLorentz_bard := isLorentzDerivTransforms_conjDownSingletField
  repLorentz_u := isLorentzDerivTransforms_upSingletField
  repLorentz_baru := isLorentzDerivTransforms_conjUpSingletField
  repLorentz_Q := isLorentzDerivTransforms_quarkDoubletField
  repLorentz_barQ := isLorentzDerivTransforms_conjQuarkDoubletField
  repLorentz_L := isLorentzDerivTransforms_leptonDoubletField
  repLorentz_barL := isLorentzDerivTransforms_conjLeptonDoubletField
  repLorentz_e := isLorentzDerivTransforms_leptonSingletField
  repLorentz_bare := isLorentzDerivTransforms_conjLeptonSingletField
  massWeight_H := massWeightPoly_higgsField
  massWeight_barH := massWeightPoly_conjHiggsField
  massWeight_A := massWeightPoly_gaugeField
  massWeight_d := massWeightPoly_downSingletField
  massWeight_bard := massWeightPoly_conjDownSingletField
  massWeight_u := massWeightPoly_upSingletField
  massWeight_baru := massWeightPoly_conjUpSingletField
  massWeight_Q := massWeightPoly_quarkDoubletField
  massWeight_barQ := massWeightPoly_conjQuarkDoubletField
  massWeight_L := massWeightPoly_leptonDoubletField
  massWeight_barL := massWeightPoly_conjLeptonDoubletField
  massWeight_e := massWeightPoly_leptonSingletField
  massWeight_bare := massWeightPoly_conjLeptonSingletField
  A_comm_A := fun s _ μ _ ψ _ => gaugeField_commute s μ ψ _
  A_comm_H := fun s μ ψ _ _ => gaugeField_commute s μ ψ _
  A_comm_barH := fun s μ ψ _ _ => gaugeField_commute s μ ψ _
  A_comm_d := fun s μ ψ _ _ _ => gaugeField_commute s μ ψ _
  A_comm_bard := fun s μ ψ _ _ _ => gaugeField_commute s μ ψ _
  A_comm_u := fun s μ ψ _ _ _ => gaugeField_commute s μ ψ _
  A_comm_baru := fun s μ ψ _ _ _ => gaugeField_commute s μ ψ _
  A_comm_Q := fun s μ ψ _ _ _ => gaugeField_commute s μ ψ _
  A_comm_barQ := fun s μ ψ _ _ _ => gaugeField_commute s μ ψ _
  A_comm_L := fun s μ ψ _ _ _ => gaugeField_commute s μ ψ _
  A_comm_barL := fun s μ ψ _ _ _ => gaugeField_commute s μ ψ _
  A_comm_e := fun s μ ψ _ _ _ => gaugeField_commute s μ ψ _
  A_comm_bare := fun s μ ψ _ _ _ => gaugeField_commute s μ ψ _
  repLorentz_mul := repLorentzGroup_apply_mul
  H_comm_H := fun s s' φ φ' =>
    (memHiggsSector_higgsField s φ).commute (memHiggsSector_higgsField s' φ')
  H_comm_barH := fun s s' φ φ' =>
    (memHiggsSector_higgsField s φ).commute (memHiggsSector_conjHiggsField s' φ')
  barH_comm_barH := fun s s' φ φ' =>
    (memHiggsSector_conjHiggsField s φ).commute (memHiggsSector_conjHiggsField s' φ')
  H_comm_d := fun s φ i s' φ' =>
    (memHiggsSector_higgsField s φ).commute_of_memFermionSector
      (isFermionGenerator_downSingletField i s' φ').memFermionSector
  H_comm_bard := fun s φ i s' φ' =>
    (memHiggsSector_higgsField s φ).commute_of_memFermionSector
      (isFermionGenerator_conjDownSingletField i s' φ').memFermionSector
  H_comm_u := fun s φ i s' φ' =>
    (memHiggsSector_higgsField s φ).commute_of_memFermionSector
      (isFermionGenerator_upSingletField i s' φ').memFermionSector
  H_comm_baru := fun s φ i s' φ' =>
    (memHiggsSector_higgsField s φ).commute_of_memFermionSector
      (isFermionGenerator_conjUpSingletField i s' φ').memFermionSector
  H_comm_Q := fun s φ i s' φ' =>
    (memHiggsSector_higgsField s φ).commute_of_memFermionSector
      (isFermionGenerator_quarkDoubletField i s' φ').memFermionSector
  H_comm_barQ := fun s φ i s' φ' =>
    (memHiggsSector_higgsField s φ).commute_of_memFermionSector
      (isFermionGenerator_conjQuarkDoubletField i s' φ').memFermionSector
  H_comm_L := fun s φ i s' φ' =>
    (memHiggsSector_higgsField s φ).commute_of_memFermionSector
      (isFermionGenerator_leptonDoubletField i s' φ').memFermionSector
  H_comm_barL := fun s φ i s' φ' =>
    (memHiggsSector_higgsField s φ).commute_of_memFermionSector
      (isFermionGenerator_conjLeptonDoubletField i s' φ').memFermionSector
  H_comm_e := fun s φ i s' φ' =>
    (memHiggsSector_higgsField s φ).commute_of_memFermionSector
      (isFermionGenerator_leptonSingletField i s' φ').memFermionSector
  H_comm_bare := fun s φ i s' φ' =>
    (memHiggsSector_higgsField s φ).commute_of_memFermionSector
      (isFermionGenerator_conjLeptonSingletField i s' φ').memFermionSector
  barH_comm_d := fun s φ i s' φ' =>
    (memHiggsSector_conjHiggsField s φ).commute_of_memFermionSector
      (isFermionGenerator_downSingletField i s' φ').memFermionSector
  barH_comm_bard := fun s φ i s' φ' =>
    (memHiggsSector_conjHiggsField s φ).commute_of_memFermionSector
      (isFermionGenerator_conjDownSingletField i s' φ').memFermionSector
  barH_comm_u := fun s φ i s' φ' =>
    (memHiggsSector_conjHiggsField s φ).commute_of_memFermionSector
      (isFermionGenerator_upSingletField i s' φ').memFermionSector
  barH_comm_baru := fun s φ i s' φ' =>
    (memHiggsSector_conjHiggsField s φ).commute_of_memFermionSector
      (isFermionGenerator_conjUpSingletField i s' φ').memFermionSector
  barH_comm_Q := fun s φ i s' φ' =>
    (memHiggsSector_conjHiggsField s φ).commute_of_memFermionSector
      (isFermionGenerator_quarkDoubletField i s' φ').memFermionSector
  barH_comm_barQ := fun s φ i s' φ' =>
    (memHiggsSector_conjHiggsField s φ).commute_of_memFermionSector
      (isFermionGenerator_conjQuarkDoubletField i s' φ').memFermionSector
  barH_comm_L := fun s φ i s' φ' =>
    (memHiggsSector_conjHiggsField s φ).commute_of_memFermionSector
      (isFermionGenerator_leptonDoubletField i s' φ').memFermionSector
  barH_comm_barL := fun s φ i s' φ' =>
    (memHiggsSector_conjHiggsField s φ).commute_of_memFermionSector
      (isFermionGenerator_conjLeptonDoubletField i s' φ').memFermionSector
  barH_comm_e := fun s φ i s' φ' =>
    (memHiggsSector_conjHiggsField s φ).commute_of_memFermionSector
      (isFermionGenerator_leptonSingletField i s' φ').memFermionSector
  barH_comm_bare := fun s φ i s' φ' =>
    (memHiggsSector_conjHiggsField s φ).commute_of_memFermionSector
      (isFermionGenerator_conjLeptonSingletField i s' φ').memFermionSector
  d_anticomm_d := fun i j s s' φ φ' =>
    (isFermionGenerator_downSingletField i s φ).anticomm
      (isFermionGenerator_downSingletField j s' φ')
  d_anticomm_bard := fun i j s s' φ φ' =>
    (isFermionGenerator_downSingletField i s φ).anticomm
      (isFermionGenerator_conjDownSingletField j s' φ')
  d_anticomm_u := fun i j s s' φ φ' =>
    (isFermionGenerator_downSingletField i s φ).anticomm (isFermionGenerator_upSingletField j s' φ')
  d_anticomm_baru := fun i j s s' φ φ' =>
    (isFermionGenerator_downSingletField i s φ).anticomm
      (isFermionGenerator_conjUpSingletField j s' φ')
  d_anticomm_Q := fun i j s s' φ φ' =>
    (isFermionGenerator_downSingletField i s φ).anticomm
      (isFermionGenerator_quarkDoubletField j s' φ')
  d_anticomm_barQ := fun i j s s' φ φ' =>
    (isFermionGenerator_downSingletField i s φ).anticomm
      (isFermionGenerator_conjQuarkDoubletField j s' φ')
  d_anticomm_L := fun i j s s' φ φ' =>
    (isFermionGenerator_downSingletField i s φ).anticomm
      (isFermionGenerator_leptonDoubletField j s' φ')
  d_anticomm_barL := fun i j s s' φ φ' =>
    (isFermionGenerator_downSingletField i s φ).anticomm
      (isFermionGenerator_conjLeptonDoubletField j s' φ')
  d_anticomm_e := fun i j s s' φ φ' =>
    (isFermionGenerator_downSingletField i s φ).anticomm
      (isFermionGenerator_leptonSingletField j s' φ')
  d_anticomm_bare := fun i j s s' φ φ' =>
    (isFermionGenerator_downSingletField i s φ).anticomm
      (isFermionGenerator_conjLeptonSingletField j s' φ')
  bard_anticomm_bard := fun i j s s' φ φ' =>
    (isFermionGenerator_conjDownSingletField i s φ).anticomm
      (isFermionGenerator_conjDownSingletField j s' φ')
  bard_anticomm_u := fun i j s s' φ φ' =>
    (isFermionGenerator_conjDownSingletField i s φ).anticomm
      (isFermionGenerator_upSingletField j s' φ')
  bard_anticomm_baru := fun i j s s' φ φ' =>
    (isFermionGenerator_conjDownSingletField i s φ).anticomm
      (isFermionGenerator_conjUpSingletField j s' φ')
  bard_anticomm_Q := fun i j s s' φ φ' =>
    (isFermionGenerator_conjDownSingletField i s φ).anticomm
      (isFermionGenerator_quarkDoubletField j s' φ')
  bard_anticomm_barQ := fun i j s s' φ φ' =>
    (isFermionGenerator_conjDownSingletField i s φ).anticomm
      (isFermionGenerator_conjQuarkDoubletField j s' φ')
  bard_anticomm_L := fun i j s s' φ φ' =>
    (isFermionGenerator_conjDownSingletField i s φ).anticomm
      (isFermionGenerator_leptonDoubletField j s' φ')
  bard_anticomm_barL := fun i j s s' φ φ' =>
    (isFermionGenerator_conjDownSingletField i s φ).anticomm
      (isFermionGenerator_conjLeptonDoubletField j s' φ')
  bard_anticomm_e := fun i j s s' φ φ' =>
    (isFermionGenerator_conjDownSingletField i s φ).anticomm
      (isFermionGenerator_leptonSingletField j s' φ')
  bard_anticomm_bare := fun i j s s' φ φ' =>
    (isFermionGenerator_conjDownSingletField i s φ).anticomm
      (isFermionGenerator_conjLeptonSingletField j s' φ')
  u_anticomm_u := fun i j s s' φ φ' =>
    (isFermionGenerator_upSingletField i s φ).anticomm (isFermionGenerator_upSingletField j s' φ')
  u_anticomm_baru := fun i j s s' φ φ' =>
    (isFermionGenerator_upSingletField i s φ).anticomm
      (isFermionGenerator_conjUpSingletField j s' φ')
  u_anticomm_Q := fun i j s s' φ φ' =>
    (isFermionGenerator_upSingletField i s φ).anticomm
      (isFermionGenerator_quarkDoubletField j s' φ')
  u_anticomm_barQ := fun i j s s' φ φ' =>
    (isFermionGenerator_upSingletField i s φ).anticomm
      (isFermionGenerator_conjQuarkDoubletField j s' φ')
  u_anticomm_L := fun i j s s' φ φ' =>
    (isFermionGenerator_upSingletField i s φ).anticomm
      (isFermionGenerator_leptonDoubletField j s' φ')
  u_anticomm_barL := fun i j s s' φ φ' =>
    (isFermionGenerator_upSingletField i s φ).anticomm
      (isFermionGenerator_conjLeptonDoubletField j s' φ')
  u_anticomm_e := fun i j s s' φ φ' =>
    (isFermionGenerator_upSingletField i s φ).anticomm
      (isFermionGenerator_leptonSingletField j s' φ')
  u_anticomm_bare := fun i j s s' φ φ' =>
    (isFermionGenerator_upSingletField i s φ).anticomm
      (isFermionGenerator_conjLeptonSingletField j s' φ')
  baru_anticomm_baru := fun i j s s' φ φ' =>
    (isFermionGenerator_conjUpSingletField i s φ).anticomm
      (isFermionGenerator_conjUpSingletField j s' φ')
  baru_anticomm_Q := fun i j s s' φ φ' =>
    (isFermionGenerator_conjUpSingletField i s φ).anticomm
      (isFermionGenerator_quarkDoubletField j s' φ')
  baru_anticomm_barQ := fun i j s s' φ φ' =>
    (isFermionGenerator_conjUpSingletField i s φ).anticomm
      (isFermionGenerator_conjQuarkDoubletField j s' φ')
  baru_anticomm_L := fun i j s s' φ φ' =>
    (isFermionGenerator_conjUpSingletField i s φ).anticomm
      (isFermionGenerator_leptonDoubletField j s' φ')
  baru_anticomm_barL := fun i j s s' φ φ' =>
    (isFermionGenerator_conjUpSingletField i s φ).anticomm
      (isFermionGenerator_conjLeptonDoubletField j s' φ')
  baru_anticomm_e := fun i j s s' φ φ' =>
    (isFermionGenerator_conjUpSingletField i s φ).anticomm
      (isFermionGenerator_leptonSingletField j s' φ')
  baru_anticomm_bare := fun i j s s' φ φ' =>
    (isFermionGenerator_conjUpSingletField i s φ).anticomm
      (isFermionGenerator_conjLeptonSingletField j s' φ')
  Q_anticomm_Q := fun i j s s' φ φ' =>
    (isFermionGenerator_quarkDoubletField i s φ).anticomm
      (isFermionGenerator_quarkDoubletField j s' φ')
  Q_anticomm_barQ := fun i j s s' φ φ' =>
    (isFermionGenerator_quarkDoubletField i s φ).anticomm
      (isFermionGenerator_conjQuarkDoubletField j s' φ')
  Q_anticomm_L := fun i j s s' φ φ' =>
    (isFermionGenerator_quarkDoubletField i s φ).anticomm
      (isFermionGenerator_leptonDoubletField j s' φ')
  Q_anticomm_barL := fun i j s s' φ φ' =>
    (isFermionGenerator_quarkDoubletField i s φ).anticomm
      (isFermionGenerator_conjLeptonDoubletField j s' φ')
  Q_anticomm_e := fun i j s s' φ φ' =>
    (isFermionGenerator_quarkDoubletField i s φ).anticomm
      (isFermionGenerator_leptonSingletField j s' φ')
  Q_anticomm_bare := fun i j s s' φ φ' =>
    (isFermionGenerator_quarkDoubletField i s φ).anticomm
      (isFermionGenerator_conjLeptonSingletField j s' φ')
  barQ_anticomm_barQ := fun i j s s' φ φ' =>
    (isFermionGenerator_conjQuarkDoubletField i s φ).anticomm
      (isFermionGenerator_conjQuarkDoubletField j s' φ')
  barQ_anticomm_L := fun i j s s' φ φ' =>
    (isFermionGenerator_conjQuarkDoubletField i s φ).anticomm
      (isFermionGenerator_leptonDoubletField j s' φ')
  barQ_anticomm_barL := fun i j s s' φ φ' =>
    (isFermionGenerator_conjQuarkDoubletField i s φ).anticomm
      (isFermionGenerator_conjLeptonDoubletField j s' φ')
  barQ_anticomm_e := fun i j s s' φ φ' =>
    (isFermionGenerator_conjQuarkDoubletField i s φ).anticomm
      (isFermionGenerator_leptonSingletField j s' φ')
  barQ_anticomm_bare := fun i j s s' φ φ' =>
    (isFermionGenerator_conjQuarkDoubletField i s φ).anticomm
      (isFermionGenerator_conjLeptonSingletField j s' φ')
  L_anticomm_L := fun i j s s' φ φ' =>
    (isFermionGenerator_leptonDoubletField i s φ).anticomm
      (isFermionGenerator_leptonDoubletField j s' φ')
  L_anticomm_barL := fun i j s s' φ φ' =>
    (isFermionGenerator_leptonDoubletField i s φ).anticomm
      (isFermionGenerator_conjLeptonDoubletField j s' φ')
  L_anticomm_e := fun i j s s' φ φ' =>
    (isFermionGenerator_leptonDoubletField i s φ).anticomm
      (isFermionGenerator_leptonSingletField j s' φ')
  L_anticomm_bare := fun i j s s' φ φ' =>
    (isFermionGenerator_leptonDoubletField i s φ).anticomm
      (isFermionGenerator_conjLeptonSingletField j s' φ')
  barL_anticomm_barL := fun i j s s' φ φ' =>
    (isFermionGenerator_conjLeptonDoubletField i s φ).anticomm
      (isFermionGenerator_conjLeptonDoubletField j s' φ')
  barL_anticomm_e := fun i j s s' φ φ' =>
    (isFermionGenerator_conjLeptonDoubletField i s φ).anticomm
      (isFermionGenerator_leptonSingletField j s' φ')
  barL_anticomm_bare := fun i j s s' φ φ' =>
    (isFermionGenerator_conjLeptonDoubletField i s φ).anticomm
      (isFermionGenerator_conjLeptonSingletField j s' φ')
  e_anticomm_e := fun i j s s' φ φ' =>
    (isFermionGenerator_leptonSingletField i s φ).anticomm
      (isFermionGenerator_leptonSingletField j s' φ')
  e_anticomm_bare := fun i j s s' φ φ' =>
    (isFermionGenerator_leptonSingletField i s φ).anticomm
      (isFermionGenerator_conjLeptonSingletField j s' φ')
  bare_anticomm_bare := fun i j s s' φ φ' =>
    (isFermionGenerator_conjLeptonSingletField i s φ).anticomm
      (isFermionGenerator_conjLeptonSingletField j s' φ')

/-!

## E. The field algebra is everything

The field algebra of an `IsStandardModel` is the algebra generated by the thirteen families
of derivative symbols. On the jet algebra it is everything: a Standard Model Lagrangian
lives in an algebra in which there is nothing to write down but the fields and their
derivatives.

The consequence is that the mass-weight filtration simplifies. The graded piece
`IsStandardModel.massWeightSubmodule n` is by definition the intersection of the field
algebra with the kernel of `massWeightPoly - X ^ n`; with the field algebra the whole
algebra the intersection is idle, and what is left is the honest weight-`n` eigenspace of
`massWeightPoly` on the whole algebra. That collapse is section E.2, stated for an
arbitrary `IsStandardModel` whose field algebra is everything.

The weight pieces and the filtration are therefore worth having on `JetAlgebra` directly,
with no mention of an `IsStandardModel` instance, and section E.3 gives them: a reader of
the classification of section F should not have to know that an instance exists. They are
defined by the eigenvalue equation rather than as a kernel because `Polynomial JetAlgebra`
carries no synthesizable `Ring` instance — the search does not close at this concrete
type — so the subtraction `massWeightPoly - X ^ n` can only be written at an abstract type.
The bridges of section E.3 identify the two.

-/

/-!

### E.1. The field algebra

-/

/-- The fields of the Standard Model generate its jet algebra: the field algebra of the
  instance is the whole of `JetAlgebra`. -/
theorem isStandardModel_fieldAlgebra_eq_top : isStandardModel.fieldAlgebra = ⊤ :=
  adjoin_generators_eq_top

end JetAlgebra

/-!

### E.2. The collapse of the graded pieces

-/

namespace IsStandardModel

open TensorProduct Matrix MatrixGroups Lorentz

variable {B : Type} [Ring B] [Algebra ℂ B]
  {repJet : Representation ℂ JetGaugeGroupI B}
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {massWeightPoly : B →ₐ[ℂ] Polynomial B}
  {H : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ HiggsVec →ₗ[ℂ] B}
  {barH : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule HiggsVec) →ₗ[ℂ] B}
  {A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ GaugeAlgebra →ₗ[ℝ] B}
  {d : Fin 3 → Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ DownSinglet →ₗ[ℂ] B}
  {bard : Fin 3 → Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule DownSinglet) →ₗ[ℂ] B}
  {u : Fin 3 → Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ UpSinglet →ₗ[ℂ] B}
  {baru : Fin 3 → Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule UpSinglet) →ₗ[ℂ] B}
  {Q : Fin 3 → Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ QuarkDoublet →ₗ[ℂ] B}
  {barQ : Fin 3 → Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule QuarkDoublet) →ₗ[ℂ] B}
  {L : Fin 3 → Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonDoublet →ₗ[ℂ] B}
  {barL : Fin 3 → Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule LeptonDoublet) →ₗ[ℂ] B}
  {e : Fin 3 → Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ LeptonSinglet →ₗ[ℂ] B}
  {bare : Fin 3 → Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ (ConjModule LeptonSinglet) →ₗ[ℂ] B}
  (h : IsStandardModel B repJet repLorentz massWeightPoly H barH A
    d bard u baru Q barQ L barL e bare)

/-- When the field algebra is everything the graded piece of mass weight `n` is the
  weight-`n` eigenspace of `massWeightPoly` on the whole algebra: the intersection with the
  field algebra in the definition of `massWeightSubmodule` cuts nothing away. -/
theorem massWeightSubmodule_eq_ker (htop : h.fieldAlgebra = ⊤) (n : ℕ) :
    h.massWeightSubmodule n
      = LinearMap.ker (massWeightPoly.toLinearMap
        - (Polynomial.monomial n : B →ₗ[B] Polynomial B).restrictScalars ℂ) := by
  show h.fieldAlgebra.toSubmodule ⊓ _ = _
  rw [htop, Algebra.top_toSubmodule, top_inf_eq]

/-- When the field algebra is everything the filtration by mass weight at most `w` is the
  join of the eigenspaces of `massWeightPoly` of weight `0` through `w`, taken over the
  whole algebra. -/
theorem massWeightSubmoduleLE_eq_iSup_ker (htop : h.fieldAlgebra = ⊤) (w : ℕ) :
    h.massWeightSubmoduleLE w
      = ⨆ k ∈ Finset.range (w + 1), LinearMap.ker (massWeightPoly.toLinearMap
          - (Polynomial.monomial k : B →ₗ[B] Polynomial B).restrictScalars ℂ) :=
  iSup_congr fun k => iSup_congr fun _ => h.massWeightSubmodule_eq_ker htop k

end IsStandardModel

namespace JetAlgebra

open TensorProduct Matrix MatrixGroups Lorentz

/-!

### E.3. The mass-weight filtration of the jet algebra

-/

/-- The weight-`n` piece of the jet algebra, defined on the algebra itself: the eigenspace
  on which `massWeightPoly` is the monomial `X ^ n`. Nothing about `IsStandardModel` enters
  the definition; that it agrees with the instance's graded piece is
  `isStandardModel_massWeightSubmodule`. -/
noncomputable def massWeightSubmodule (n : ℕ) : Submodule ℂ JetAlgebra where
  carrier := {x | massWeightPoly x = Polynomial.monomial n x}
  zero_mem' := by simp
  add_mem' hx hy := by
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [map_add, hx, hy, map_add]
  smul_mem' c x hx := by
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [map_smul, hx, ← Polynomial.smul_monomial]

/-- Membership of the weight-`n` piece is the eigenvalue equation. -/
@[simp]
lemma mem_massWeightSubmodule {n : ℕ} {x : JetAlgebra} :
    x ∈ massWeightSubmodule n ↔ massWeightPoly x = Polynomial.monomial n x := Iff.rfl

/-- The mass-weight filtration of the jet algebra, defined on the algebra itself: the join
  of the weight pieces of weight at most `w`. An element lies in it exactly when it is a
  sum of eigenvectors of `massWeightPoly` of weight at most `w`. -/
noncomputable def massWeightSubmoduleLE (w : ℕ) : Submodule ℂ JetAlgebra :=
  ⨆ k ∈ Finset.range (w + 1), massWeightSubmodule k

/-- The graded piece defined on the jet algebra is the graded piece of the instance: the
  two differ only by the intersection with the field algebra, which is everything. -/
lemma isStandardModel_massWeightSubmodule (n : ℕ) :
    isStandardModel.massWeightSubmodule n = massWeightSubmodule n := by
  rw [isStandardModel.massWeightSubmodule_eq_ker isStandardModel_fieldAlgebra_eq_top]
  ext x
  rw [LinearMap.mem_ker, mem_massWeightSubmodule]
  simp [sub_eq_zero]

/-- The filtration defined on the jet algebra is the filtration of the instance. -/
lemma isStandardModel_massWeightSubmoduleLE (w : ℕ) :
    isStandardModel.massWeightSubmoduleLE w = massWeightSubmoduleLE w := by
  show ⨆ k ∈ Finset.range (w + 1), isStandardModel.massWeightSubmodule k = _
  exact iSup_congr fun k => iSup_congr fun _ => isStandardModel_massWeightSubmodule k

/-!

## F. The Standard Model Lagrangian

This is what the chain was built for, and the first theorem below is the headline. Take
any element `x` of the jet algebra of mass weight at most eight — that is, of mass
dimension at most four; by section E that is a condition on `x` alone, and it is the only
hypothesis there is. Then `x` is invariant under the jet gauge group and under the Lorentz
group if and only if it is a combination of

* the constant term, of mass dimension zero;
* the Higgs mass term `H† H`, of mass dimension two;
* and the dimension-four Standard Model Lagrangian — the gauge kinetic and theta terms of
  the three gauge groups, the Higgs kinetic term, its quartic potential and its two box
  terms, the kinetic terms of the ten fermion species over the nine family pairs, and the
  six Yukawa couplings over the nine family pairs —

and nothing else. No further term of dimension four is invariant, and none of these is
forced to vanish.

The second theorem is the same classification with a submodule `S` set aside — the
operators of mass dimension above four, for a reader who wants to work modulo them. It is
strictly more general and strictly less readable, which is why it comes second. It keeps its
hypothesis `hScov : S ≤ covAlgebra.toSubmodule`, and that is not an oversight of the
simplification of section E. The field algebra is everything, but the covariant subalgebra
is not: a covariant element is fixed by the pure gauge jets, while the gauge potential
picks up the Maurer–Cartan shift and so is not. `covAlgebra` therefore stays a proper
subalgebra of `JetAlgebra`, and a set-aside `S` still has to be written in the covariant
towers for the classification to say anything about it.

-/

/-- The invariant content of the Standard Model up to mass dimension four, on the jet
  algebra of the Standard Model itself, with nothing set aside. An element of mass weight
  at most eight is fixed by the jet gauge group and by the Lorentz group exactly when it is
  a combination of the constant term, the Higgs mass term `H† H`, and the Standard Model
  Lagrangian of mass dimension four: the gauge kinetic and theta terms
  (`IsGaugeSector.lorentzContractionEightSpan`), the Higgs kinetic term, quartic potential
  and box terms (`IsHiggsSector.lorentzContractionEightSpan`), the fermion kinetic terms
  (`IsFermionSector.kineticSpan`) and the Yukawa couplings (`yukawaSpan`) — and nothing
  else.

  There are no other hypotheses. The mass-weight condition is a condition on `x` alone: by
  `mem_massWeightSubmodule` it says that `x` is a sum of eigenvectors of `massWeightPoly`
  of weight at most eight, with no demand that `x` lie in any subalgebra. -/
theorem mem_massWeightSubmoduleLE_eight_and_invariant_iff_lagrangian (x : JetAlgebra) :
    (x ∈ massWeightSubmoduleLE 8
        ∧ (∀ U : JetGaugeGroupI, repJetGaugeGroupI U x = x)
        ∧ ∀ Λ : SL(2,ℂ), repLorentzGroup Λ x = x)
      ↔ x ∈ 1
          ⊔ (isStandardModel.isCovStandardModel.isHiggsSector.dotSpan 0 0
            ⊔ (isStandardModel.isCovStandardModel.isGaugeSector.lorentzContractionEightSpan
                ⊔ isStandardModel.isCovStandardModel.isHiggsSector.lorentzContractionEightSpan
              ⊔ (isStandardModel.isCovStandardModel.isFermionSector.kineticSpan
                ⊔ isStandardModel.isCovStandardModel.yukawaSpan))) := by
  rw [← isStandardModel_massWeightSubmoduleLE]
  exact isStandardModel.mem_massWeightSubmoduleLE_eight_and_invariant_iff_lagrangian x

set_option maxHeartbeats 40000000 in
/-- The same classification as
  `mem_massWeightSubmoduleLE_eight_and_invariant_iff_lagrangian`, with a submodule `S` set
  aside — the operators of mass dimension above four, say. An element of
  `massWeightSubmoduleLE 8 ⊔ S` is fixed by the jet gauge group and the Lorentz group
  exactly when it is the Standard Model Lagrangian, the Higgs mass term and a constant, up
  to a remainder in `S` fixed by both groups.

  The hypothesis `hScov` does not disappear when the field algebra becomes everything: the
  covariant subalgebra `covAlgebra` remains a proper subalgebra, because a covariant
  element is fixed by the pure gauge jets whereas the gauge potential picks up the
  Maurer–Cartan shift. A set-aside `S` therefore still has to be written in the covariant
  towers, which is the case of interest — higher-dimension operators are built from
  covariant derivatives and the field strength. -/
theorem mem_massWeightSubmoduleLE_eight_sup_and_invariant_iff_lagrangian
    (S : Submodule ℂ JetAlgebra)
    (hS : ∀ U : JetGaugeGroupI, ∀ y ∈ S, repJetGaugeGroupI U y ∈ S)
    (hSL : ∀ Λ : SL(2,ℂ), ∀ y ∈ S, repLorentzGroup Λ y ∈ S)
    (hScov : S ≤ isStandardModel.covAlgebra.toSubmodule) (x : JetAlgebra) :
    (x ∈ massWeightSubmoduleLE 8 ⊔ S
        ∧ (∀ U : JetGaugeGroupI, repJetGaugeGroupI U x = x)
        ∧ ∀ Λ : SL(2,ℂ), repLorentzGroup Λ x = x)
      ↔ ∃ y ∈ S, (∀ U : JetGaugeGroupI, repJetGaugeGroupI U y = y)
          ∧ (∀ Λ : SL(2,ℂ), repLorentzGroup Λ y = y)
          ∧ x - y ∈ 1
            ⊔ (isStandardModel.isCovStandardModel.isHiggsSector.dotSpan 0 0
              ⊔ (isStandardModel.isCovStandardModel.isGaugeSector.lorentzContractionEightSpan
                  ⊔ isStandardModel.isCovStandardModel.isHiggsSector.lorentzContractionEightSpan
                ⊔ (isStandardModel.isCovStandardModel.isFermionSector.kineticSpan
                  ⊔ isStandardModel.isCovStandardModel.yukawaSpan))) := by
  rw [← isStandardModel_massWeightSubmoduleLE]
  exact isStandardModel.mem_massWeightSubmoduleLE_eight_sup_and_invariant_iff_lagrangian
    S hS hSL hScov x

end JetAlgebra

end StandardModel
