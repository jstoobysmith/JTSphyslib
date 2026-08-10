/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.Terms.KineticTerms
public import Physlib.Particles.LeptonGaugeSector.JetAlgebra.Invariants.GroupAverage
/-!
# The renormalizable terms of the lepton–gauge-sector jet algebra

The four gauge- and Lorentz-invariant elements of mass dimension at most four —
the Maxwell term, the theta term and the two fermion kinetic terms, defined in
`Terms/` — collected into one set, together with the easy half of the
classification: their span is contained in `InvariantMassWeightSubmodule 8`.
-/

@[expose] public section

set_option maxHeartbeats 1000000

namespace LeptonGaugeSector
open TensorProduct StandardModel

namespace JetAlgebra

open scoped minkowskiMatrix PauliMatrix
open Matrix MatrixGroups

/-- The invariants of the lepton–gauge-sector jet algebra of mass dimension at most four: the
  constants and the four kinetic terms. These span
  `InvariantMassWeightSubmodule 8`, the renormalizable Lagrangian densities of the lepton–gauge sector. -/
def massDimFourInvariants : Set JetAlgebra :=
  {1, maxwellTerm, thetaTerm, fermionKineticTerm, fermionKineticTermBar}

/-- Every element of `massDimFourInvariants` is gauge and Lorentz invariant. -/
lemma isInvariant_of_mem_massDimFourInvariants {x : JetAlgebra}
    (hx : x ∈ massDimFourInvariants) : IsInvariant x := by
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact ⟨fun U => (repJetGaugeGroupI_eq_repAlgHom U 1).trans (repAlgHom U).map_one,
      repLorentzGroup_apply_one⟩
  · exact ⟨repJetGaugeGroupI_maxwellTerm, repLorentzGroup_maxwellTerm⟩
  · exact ⟨repJetGaugeGroupI_thetaTerm, repLorentzGroup_thetaTerm⟩
  · exact ⟨repJetGaugeGroupI_fermionKineticTerm, repLorentzGroup_fermionKineticTerm⟩
  · exact ⟨repJetGaugeGroupI_fermionKineticTermBar,
      repLorentzGroup_fermionKineticTermBar⟩

lemma span_massDimFourInvariants_le :
    Submodule.span ℂ massDimFourInvariants ≤ InvariantMassWeightSubmodule 8 := by
  rw [Submodule.span_le]
  intro x hx
  refine Submodule.mem_inf.mpr ⟨?_, Submodule.subset_span
    (isInvariant_of_mem_massDimFourInvariants hx)⟩
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact mem_massWeightLESubmodule_of_mem (m := 0) (Nat.zero_le 8)
      (SetLike.one_mem_graded massWeightSubmodule)
  · exact maxwellTerm_mem_massWeightLESubmodule
  · exact thetaTerm_mem_massWeightLESubmodule
  · exact fermionKineticTerm_mem_massWeightLESubmodule
  · exact fermionKineticTermBar_mem_massWeightLESubmodule

end JetAlgebra

end LeptonGaugeSector
