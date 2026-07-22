/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

/-!

# Boundary conformal field theory

## i. Overview

Boundary conformal field theory (BCFT) studies conformal field theories on
spaces with a boundary, where the boundary preserves part of the conformal
symmetry. It governs critical phenomena near surfaces, D-branes in string
theory, and boundary critical behaviour in condensed-matter systems.

This page is documentation-only: it has no formalized content yet, and is
intended as a target for future formalization.

## ii. Setup

A conformal field theory on the half-space $x_\perp \geq 0$ in $d$
dimensions retains the subgroup of conformal transformations preserving
the boundary plane $x_\perp = 0$, which is isomorphic to the conformal
group in $d - 1$ dimensions. Conformal boundary conditions require the
absence of energy flux through the boundary:
$$
T^{\perp \mu}\big|_{x_\perp = 0} \cdot t_\mu = 0
$$
for tangential directions $t_\mu$. In two dimensions this is the familiar
gluing condition $T(z) = \bar{T}(\bar z)$ on the real line.

## iii. Key structures

- **Boundary operators.** In addition to bulk operators, a BCFT contains
  operators living on the boundary, organized into representations of the
  preserved conformal group.
- **Bulk-to-boundary expansion.** A bulk operator close to the boundary
  can be expanded in boundary operators, with coefficients that play a
  role analogous to OPE coefficients.
- **One-point functions.** Unlike in a homogeneous CFT, bulk primaries may
  acquire nonzero one-point functions, $\langle \mathcal{O}(x) \rangle
  \propto a_{\mathcal{O}} / (2 x_\perp)^{\Delta}$, and the coefficients
  $a_{\mathcal{O}}$ are part of the BCFT data.
- **Cardy conditions.** In two dimensions, consistency between the open-
  and closed-string channels of the annulus constrains the allowed
  boundary states.

## iv. References

- J. L. Cardy, *Conformal invariance and surface critical behavior*,
  Nucl. Phys. B 240 (1984) 514.
- D. M. McAvity, H. Osborn, *Conformal field theories near a boundary in
  general dimensions*, Nucl. Phys. B 455 (1995) 522.

-/
