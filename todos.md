# TODOs introduced by this branch

19 open &middot; as of `bd9a23d1` (2026-08-16)

> Regenerate with `python scripts/todos.py --md todos.md` after adding or
> resolving a TODO, and commit it in the same commit.

**Format.** Use the `TODO "…"` command

### `Particles/LeptonGaugeSector/JetAlgebra/Boosts`

- Generalize the below result for any axis &nbsp;[`FieldStrength.lean:348`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/LeptonGaugeSector/JetAlgebra/Boosts/FieldStrength.lean#L348)

### `Particles/PureFermionic`

- Move the diagonal `SL(2, ℂ)` material `diagSL`, `diagSL_inv`, `diagSL_neg_one` and `twoI` to `Physlib.Relativity.SL2C.Basic`, their canonical home, when the effective-potential development is split up. &nbsp;[`EFTLagrangianExclDeriv.lean:162`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/PureFermionic/EFTLagrangianExclDeriv.lean#L162)

### `Particles/QED`

- Prove the composition law of the Lorentz action. Being a pullback on coordinates it is a right action, `lorentzAction M ∘ lorentzAction N = lorentzAction (N * M)`; the proof needs permutation-invariance and functoriality of `derivSum` over sorted lists. &nbsp;[`Basic.lean:1431`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/QED/Basic.lean#L1431)
- Define an antilinear star on the QED jet algebra with `star ψ = ψ̄`, `star A = A`, and prove hermiticity of the Lagrangian up to the total derivative of the kinetic term. &nbsp;[`Basic.lean:1434`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/QED/Basic.lean#L1434)
- Connect the QED matter content to `Physlib.QFT.QED.AnomalyCancellation`: the electron spectrum is vector-like (charges `±1`), so it satisfies the gravitational and cubic anomaly cancellation conditions. &nbsp;[`CurrentCoupling.lean:56`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/QED/CurrentCoupling.lean#L56)
- Classify the gauge- and Lorentz-invariant elements of mass dimension at most four of the full QED jet algebra: the analogue for the Dirac electron of the classification `LeptonGaugeSector.JetAlgebra.MassDimFour.Classification`, showing the QED Lagrangian is the most general renormalizable choice. &nbsp;[`JetCompleteness.lean:57`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/QED/JetCompleteness.lean#L57)
- Derive `diracEquation`, `diracAdjEquation` and `qedMaxwellEquation` variationally: define the Euler–Lagrange operator on the jet algebra (the variational derivative with respect to each jet coordinate) and prove they are the EL equations of `lagrangian`, following `Physlib.Electromagnetism.Dynamics.IsExtrema` concretely. &nbsp;[`Lagrangian.lean:119`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/QED/Lagrangian.lean#L119)
- Define the theta term `θ ε^{μνρσ} F_{μν} F_{ρσ}` and prove it is gauge invariant and a total derivative for `jetDeriv`, as in the lepton–gauge sector's theta term. &nbsp;[`Lagrangian.lean:123`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/QED/Lagrangian.lean#L123)
- Quantize: instantiate the field species of `Physlib.QFT.PerturbationTheory` with the photon and electron of this file, towards the Feynman rules of QED. &nbsp;[`Lagrangian.lean:125`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/QED/Lagrangian.lean#L125)
- Upgrade the mass-weight scaling to a genuine filtration by submodules, following `LeptonGaugeSector.JetAlgebra.MassDim` (`MassWeightLESubmodule`), together with the derivative-order and fermion-parity gradings needed for classification arguments. &nbsp;[`MassDimension.lean:61`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/QED/MassDimension.lean#L61)

### `Particles/StandardModel/GaugeBosons/BBoson`

- Show invariance of the mass weights with repsect to the Lorentz group. &nbsp;[`MassDim.lean:310`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/StandardModel/GaugeBosons/BBoson/MassDim.lean#L310)

### `Particles/StandardModel/GaugeGroup`

- Make the API here match what is in the doc-string. &nbsp;[`JetGaugeAlgebra.lean:51`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/StandardModel/GaugeGroup/JetGaugeAlgebra.lean#L51)
- Define the Lie algebra instance on `JetGaugeAlgebra`. &nbsp;[`JetGaugeAlgebra.lean:87`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/StandardModel/GaugeGroup/JetGaugeAlgebra.lean#L87)
- Define the basis of the jet gauge algebra. &nbsp;[`JetGaugeAlgebra.lean:95`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/StandardModel/GaugeGroup/JetGaugeAlgebra.lean#L95)
- Define the adjoint representation of the jet gauge group on the jet gauge algebra. &nbsp;[`JetGaugeAlgebra.lean:104`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/StandardModel/GaugeGroup/JetGaugeAlgebra.lean#L104)
- The maurerCartan form should be defined for the whole gauge group, and it should live in the jet Lie algebra. &nbsp;[`MaurerCartan.lean:50`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/StandardModel/GaugeGroup/MaurerCartan.lean#L50)
- Define the symmetrized maurerCartan forms. &nbsp;[`MaurerCartan.lean:53`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/StandardModel/GaugeGroup/MaurerCartan.lean#L53)

### `Particles/WessZumino/EFTLagrangianExclDeriv`

- Define ComplexScalarEFTExclDeriv.rep &nbsp;[`Basic.lean:280`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Particles/WessZumino/EFTLagrangianExclDeriv/Basic.lean#L280)

### `Relativity/Fermions/Weyl`

- Relate `DualLeftHandedWeyl` to `LeftHandedWeyl` via `Module.dual`. &nbsp;[`DualLeftHanded.lean:35`](https://github.com/jstoobysmith/JTSphyslib/blob/AddPotentialAlgebra/Physlib/Relativity/Fermions/Weyl/DualLeftHanded.lean#L35)
