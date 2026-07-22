/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

/-!

# Operator product expansion

## i. Overview

The operator product expansion (OPE) expresses the product of two local
operators at nearby points as a sum of single local operators multiplied by
coefficient functions of the separation. It is a cornerstone of quantum
field theory, and in conformal field theory it becomes a convergent
expansion that, together with crossing symmetry, underlies the conformal
bootstrap.

This page is documentation-only: it has no formalized content yet, and is
intended as a target for future formalization.

## ii. Definition

For local operators $\mathcal{O}_i$ inserted at nearby points $x$ and $y$,
the OPE takes the form
$$
\mathcal{O}_i(x)\,\mathcal{O}_j(y) \sim
  \sum_k C_{ijk}(x - y)\, \mathcal{O}_k(y),
$$
where the coefficient functions $C_{ijk}$ encode the short-distance
behaviour and the sum runs over a complete set of local operators. In a
conformal field theory the spacetime dependence of $C_{ijk}$ for primary
operators is fixed entirely by the scaling dimensions $\Delta_i$ and spins
of the operators, leaving only numerical OPE coefficients.

## iii. Key properties

- **Asymptotic vs. convergent.** In a generic quantum field theory the OPE
  is an asymptotic short-distance expansion; in a conformal field theory
  it converges inside correlation functions on a finite domain.
- **Associativity.** Applying the OPE in different orders inside a
  four-point function must give the same answer. This *crossing equation*
  is the central constraint exploited by the conformal bootstrap.
- **Scaling control.** The separation dependence of each term is governed
  by the twist and dimension of the exchanged operator, so the OPE
  organizes short-distance physics by the dimensions of local operators.

## iv. References

- K. G. Wilson, *Non-Lagrangian models of current algebra*,
  Phys. Rev. 179 (1969) 1499.
- S. Ferrara, A. F. Grillo, R. Gatto, *Tensor representations of conformal
  algebra and conformally covariant operator product expansion*,
  Annals Phys. 76 (1973) 161.

-/
