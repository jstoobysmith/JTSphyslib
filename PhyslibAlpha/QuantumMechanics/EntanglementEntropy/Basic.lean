/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

/-!

# Entanglement entropy

## i. Overview

Entanglement entropy quantifies the quantum correlations between a
subsystem and its complement. It is a central quantity in quantum
information theory, in the study of quantum phases of matter, and — via
the Ryu–Takayanagi proposal — in holographic descriptions of quantum
gravity.

This page is documentation-only: it has no formalized content yet, and is
intended as a target for future formalization.

## ii. Definition

Let a system in a pure state $|\psi\rangle$ be divided into a subsystem
$A$ and its complement $\bar{A}$. The reduced density matrix of $A$ is
$$
\rho_A = \mathrm{Tr}_{\bar{A}}\, |\psi\rangle\langle\psi|,
$$
and the entanglement entropy of $A$ is its von Neumann entropy
$$
S_A = -\mathrm{Tr}\left( \rho_A \log \rho_A \right).
$$
For a pure global state, $S_A = S_{\bar{A}}$; for mixed global states this
symmetry fails, and $S_A$ mixes classical and quantum correlations.

## iii. Key properties

- **Subadditivity and strong subadditivity.** For disjoint subsystems,
  $S_{AB} \leq S_A + S_B$, and more strongly
  $S_{ABC} + S_B \leq S_{AB} + S_{BC}$ — an inequality with far-reaching
  consequences in quantum information theory.
- **Area laws.** Ground states of local gapped Hamiltonians typically obey
  an area law: $S_A$ scales with the boundary of $A$ rather than its
  volume. In two-dimensional critical systems the entropy of an interval
  of length $\ell$ grows as $\frac{c}{3} \log \ell$ with central charge
  $c$.
- **Holography.** In holographic theories the Ryu–Takayanagi formula
  computes $S_A$ from the area of a minimal surface in the dual geometry,
  $S_A = \mathrm{Area}(\gamma_A) / 4 G_N$.

## iv. References

- C. Holzhey, F. Larsen, F. Wilczek, *Geometric and renormalized entropy
  in conformal field theory*, Nucl. Phys. B 424 (1994) 443.
- P. Calabrese, J. Cardy, *Entanglement entropy and quantum field theory*,
  J. Stat. Mech. 0406 (2004) P06002.
- S. Ryu, T. Takayanagi, *Holographic derivation of entanglement entropy
  from AdS/CFT*, Phys. Rev. Lett. 96 (2006) 181602.

-/
