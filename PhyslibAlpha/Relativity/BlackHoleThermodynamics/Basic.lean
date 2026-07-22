/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

/-!

# Black hole thermodynamics

## i. Overview

Black hole thermodynamics identifies the laws governing black hole
mechanics with the laws of thermodynamics: horizon area behaves as an
entropy and surface gravity as a temperature. Together with Hawking's
prediction that black holes radiate thermally, these results connect
gravity, quantum theory, and statistical mechanics, and motivate much of
modern research in quantum gravity.

This page is documentation-only: it has no formalized content yet, and is
intended as a target for future formalization.

## ii. The four laws

- **Zeroth law.** The surface gravity $\kappa$ is constant over the event
  horizon of a stationary black hole.
- **First law.** Neighbouring stationary black hole solutions satisfy
  $$
  dM = \frac{\kappa}{8 \pi G}\, dA + \Omega_H \, dJ + \Phi_H \, dQ,
  $$
  relating changes in mass $M$, horizon area $A$, angular momentum $J$,
  and charge $Q$.
- **Second law.** In classical general relativity with matter satisfying
  the null energy condition, the horizon area never decreases,
  $\delta A \geq 0$ (Hawking's area theorem).
- **Third law.** The surface gravity cannot be reduced to zero by a finite
  sequence of physical processes.

## iii. Temperature and entropy

Semiclassical quantum field theory in a black hole background shows that a
black hole radiates thermally at the Hawking temperature
$$
T_H = \frac{\hbar \kappa}{2 \pi},
$$
which fixes the Bekenstein–Hawking entropy
$$
S_{BH} = \frac{A}{4 G \hbar}.
$$
For a Schwarzschild black hole of mass $M$, $T_H \propto 1 / M$: the
specific heat is negative, and evaporation accelerates as the hole
shrinks. Accounting microscopically for $S_{BH}$, and understanding
whether evaporation preserves unitarity (the information paradox), remain
benchmark problems for any theory of quantum gravity.

## iv. References

- J. M. Bardeen, B. Carter, S. W. Hawking, *The four laws of black hole
  mechanics*, Commun. Math. Phys. 31 (1973) 161.
- J. D. Bekenstein, *Black holes and entropy*,
  Phys. Rev. D 7 (1973) 2333.
- S. W. Hawking, *Particle creation by black holes*,
  Commun. Math. Phys. 43 (1975) 199.

-/
