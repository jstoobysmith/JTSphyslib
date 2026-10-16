# Configuration Space

## Abstract (Alpha)

The configuration space of a mechanical system is the manifold of the configurations it can
instantaneously be in, coordinatised by generalized coordinates. It is the base on which the
Lagrangian formulation of mechanics is built: a Lagrangian is a function on the tangent bundle of
positions and velocities, and the Euler–Lagrange equations pick out the physical motions as curves
in the configuration space. Particular systems, such as the harmonic oscillator and the pendulum,
have configuration spaces of their own, while this map concerns the general, system-agnostic
picture, whose positions ultimately live in physical space.

## Content (Alpha)

A configuration manifold {1} abstracts over the choice of mechanical system, and is shared across
the Lagrangian formulation. [planned] Generalized coordinates and the velocity phase space live over
that shared configuration space, and a Lagrangian is a function on them, which is the input to the
Euler–Lagrange equations {2}. [planned] Particular systems, such as the geometric harmonic
oscillator {3} and the pendulum {4}, have configuration spaces of their own, whose positions
ultimately live in physical space {5}.

## Lean References

*None yet.*

## References

1. Ivo Terek, *Introductory Variational Calculus on Manifolds*, Section 1 (the manifold setting).
2. Landau and Lifshitz, *Mechanics*, 3rd ed., Chapter 1 (generalized coordinates, the principle of
   least action and the Lagrangian).
3. Configuration space of the harmonic oscillator API map —
   Physlib/ClassicalMechanics/HarmonicOscillator/Geometric/API-map.md
4. Configuration space for pendulum API map — Physlib/ClassicalMechanics/Pendulum/API-map.md
5. Space API map — Physlib/SpaceAndTime/Space/API-map.md
