/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

/-!

# Renormalization group

## i. Overview

The renormalization group (RG) describes how the couplings of a physical
theory change with the scale at which the theory is probed. It explains
universality in critical phenomena, the running of couplings in particle
physics, and provides the modern viewpoint on quantum field theory as a
family of effective descriptions indexed by scale.

This page is documentation-only: it has no formalized content yet, and is
intended as a target for future formalization.

## ii. The RG flow

Integrating out degrees of freedom above a scale $\mu$ produces an
effective theory whose couplings $g_i(\mu)$ obey flow equations
$$
\mu \frac{d g_i}{d \mu} = \beta_i(g),
$$
with beta functions $\beta_i$. Fixed points $g^*$, where $\beta_i(g^*) =
0$, describe scale-invariant theories; linearizing the flow around a fixed
point sorts perturbations into relevant, irrelevant, and marginal
according to the sign of their scaling eigenvalues.

## iii. Key consequences

- **Universality.** Long-distance physics near a critical point depends
  only on the fixed point and its relevant directions, not on microscopic
  details — different microscopic systems share critical exponents.
- **Asymptotic freedom.** In four-dimensional Yang–Mills theory the gauge
  coupling decreases at high energy, $\beta(g) < 0$, making the
  short-distance theory weakly coupled.
- **C- and a-theorems.** In two and four dimensions, quantities exist that
  decrease monotonically along RG flows, formalizing the intuition that
  flowing to the infrared loses degrees of freedom.

## iv. References

- K. G. Wilson, J. Kogut, *The renormalization group and the epsilon
  expansion*, Phys. Rept. 12 (1974) 75.
- J. Polchinski, *Renormalization and effective Lagrangians*,
  Nucl. Phys. B 231 (1984) 269.

-/
