/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

/-!

# Witten index

## i. Overview

The Witten index is a signed count of the ground states of a supersymmetric
quantum system: bosonic ground states contribute $+1$ and fermionic ground
states contribute $-1$. Because states of nonzero energy come in
boson–fermion pairs related by supersymmetry, their contributions cancel,
and the index is insensitive to smooth deformations of the theory. A
nonzero value therefore guarantees that supersymmetry is not spontaneously
broken.

This page is documentation-only: it has no formalized content yet, and is
intended as a target for future formalization.

## ii. Definition

For a supersymmetric quantum system with Hamiltonian $H$, Hilbert space
$\mathcal{H}$, and fermion-number operator $F$, the Witten index is the
graded thermal trace
$$
I_W(\beta) = \mathrm{Tr}_{\mathcal{H}}\left[ (-1)^F e^{-\beta H} \right].
$$
Supersymmetry pairs every state of energy $E > 0$ with a superpartner of
the opposite statistics, so only zero-energy states contribute and
$$
I_W = n_B^{E=0} - n_F^{E=0},
$$
independently of $\beta$.

## iii. Key properties

- **Deformation invariance.** Under smooth changes of couplings that
  preserve supersymmetry and do not change the asymptotics of the
  potential, paired states enter and leave $E = 0$ together, so $I_W$ is
  unchanged.
- **Obstruction to supersymmetry breaking.** Spontaneous breaking of
  supersymmetry requires that no zero-energy state exists; hence
  $I_W \neq 0$ implies unbroken supersymmetry.
- **Relation to geometry.** For supersymmetric sigma models on a compact
  manifold, the index computes topological invariants of the target: for
  example, the $\mathcal{N} = 2$ sigma model reproduces the Euler
  characteristic, connecting the index to the Atiyah–Singer index theorem.

## iv. References

- E. Witten, *Constraints on supersymmetry breaking*,
  Nucl. Phys. B 202 (1982) 253.
- E. Witten, *Supersymmetry and Morse theory*,
  J. Diff. Geom. 17 (1982) 661.

-/
