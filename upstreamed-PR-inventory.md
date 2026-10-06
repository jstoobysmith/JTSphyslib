# Standard Model Lagrangian project: Physlib PR inventory

Status checked 2026-10-06. This is a discovery inventory, not a claim that every related PR originated in #1415.

Labels distinguish provenance: **extracted** means evidence links the work to #1415; **related API** and **shared infrastructure** are relevant, without claiming extraction; **historical** records closed work that was not upstreamed.

## Merged contributions

Newest first.

| PR | Status | Contribution and project link |
|---|---|---|
| [#1731 — feat(SpaceTime): the Leibniz rule in the spacetime algebra](https://github.com/leanprover-community/physlib/pull/1731) | Merged 2026-10-05 | **Extracted.** Adds the Leibniz rule for iterated spacetime-algebra derivatives; follows the spacetime-calculus extraction associated with #1415. |
| [#1702 — feat(SpaceTime): the spacetime algebra and its Taylor series](https://github.com/leanprover-community/physlib/pull/1702) | Merged 2026-10-02 | **Extracted.** Adds the spacetime formal-power-series and Taylor-series layer; its description compares the work with #1415 and notes carried-over results. |
| [#1547 — Add coordinate-axis boosts in SL(2, ℂ)](https://github.com/leanprover-community/physlib/pull/1547) | Merged 2026-08-20 | **Extracted.** Adds coordinate-axis boosts and related Lorentz results; project notes trace it to work serving #1415. |
| [#1489 — refactor: Higgs GaugeGroupI action to a Representation](https://github.com/leanprover-community/physlib/pull/1489) | Merged 2026-08-05 | **Extracted.** Refactors the Higgs gauge action; the PR says it was carved out of #1415. |
| [#1430 — feat: Add lepton doublets (Stacked on #1416)](https://github.com/leanprover-community/physlib/pull/1430) | Merged 2026-07-27 | **Related API.** Adds lepton-doublet representations; stacked on #1416. |
| [#1463 — feat: Add down singlets](https://github.com/leanprover-community/physlib/pull/1463) | Merged 2026-07-26 | **Related API.** Adds down-type singlet representations. |
| [#1416 — feat: Add up type singlet quarks (Stacked on #1379)](https://github.com/leanprover-community/physlib/pull/1416) | Merged 2026-07-25 | **Related API.** Adds up-type singlet quark representations; stacked on #1379. |
| [#1379 — feat: Add action of gauge group on Quark Doublets](https://github.com/leanprover-community/physlib/pull/1379) | Merged 2026-07-14 | **Related API.** Adds gauge-group actions for quark doublets. |
| [#1358 — feat: Add equivariance to ConjTensorSpecies](https://github.com/leanprover-community/physlib/pull/1358) | Merged 2026-07-14 | **Shared infrastructure.** Adds equivariance for conjugate tensor species, useful for conjugate Weyl-fermion representations. |

## Open or draft contributions

Newest first.

| PR | Status | Contribution and project link |
|---|---|---|
| [#1743 — feat(SpaceTime): complex conjugation in the spacetime algebra](https://github.com/leanprover-community/physlib/pull/1743) | Open | **Project prerequisite.** Adds coefficient conjugation while fixing spacetime coordinates; supplies the star structure identified as missing for #1415's `JetSUAlgebra` use of the SU(n) algebra. |
| [#1741 — refactor(Tensors): WithMetric instance](https://github.com/leanprover-community/physlib/pull/1741) | Open, not marked draft | **Related infrastructure.** Makes the metric requirement optional for `TensorSpecies`, needed because SU(n) tensors do not have metrics; relevant to the SU(n) work in #1719. |
| [#1719 — feat: Add foundational SU(n) files](https://github.com/leanprover-community/physlib/pull/1719) | Open, draft | **Related upstreaming.** Adds SU(n) algebra foundations connected by branch investigation to structures used in #1415; builds on #1702. |
| [#1415 — feat: Effective potential for Weyl fermions (Stacked on #1404)](https://github.com/leanprover-community/physlib/pull/1415) | Open, draft | **Project hub.** Holds the collaboration branch’s broader Standard Model Lagrangian work; stacked on #1404. |

## Closed or superseded historical work

Newest first.

| PR | Status | Contribution and project link |
|---|---|---|
| [#1468 — feat(mathematics): add the degree-wise linear universal property of the symmetric algebra](https://github.com/leanprover-community/physlib/pull/1468) | Closed 2026-08-05; not merged | **Historical.** Develops symmetric-algebra machinery for the earlier Higgs-monomial and coefficient-projection approach. |
| [#1459 — Define `EFTLagrangianExclDeriv` for the Higgs field](https://github.com/leanprover-community/physlib/pull/1459) | Closed 2026-08-05; not merged | **Historical.** Earlier Higgs-sector EFT approach; its description relates its target to #1415. |

## Separate prerequisite

- [#1404 — feat: Move Fermions and reorganise results](https://github.com/leanprover-community/physlib/pull/1404) — merged 2026-07-14. The explicit base PR for #1415; reorganizes fermion material and is not counted as an extraction.

## Evidence notes and gaps

- The clearest extractions are #1489, #1547, #1702, and #1731. The spacetime, SU(n), and boost-weight investigations are recorded in [their reports](spacetime-algebra-upstream-investigation-report.md), [the SU(n) investigation](special-unitary-algebra-upstream-investigation-report.md), and [the boost-weight extraction report](AITasks/Done/boost-weight-extraction-report.md). The SU(n) report identifies the missing spacetime star structure as a blocker for #1415's `JetSUAlgebra` use.
- Matter-representation and tensor-infrastructure PRs are included as relevant work, not as proven #1415 extractions.
- Further branch history and linked Zulip discussion may identify additional extractions. Generic tensor or SU(N) PRs without a specific project connection remain out of scope.
