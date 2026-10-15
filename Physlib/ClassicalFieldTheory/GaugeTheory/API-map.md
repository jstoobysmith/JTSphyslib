# Gauge theory

A general gauge-theory API would be built around a structure group, a gauge field valued in its
Lie algebra, the curvature of that field, the gauge-covariant derivative acting on matter
fields, and the gauge transformations under which the curvature transforms covariantly and the
action is invariant.

This is a tracking map for issue #859. The library has no general, non-abelian gauge-theory
framework. What it has are two disjoint concrete pieces. The first is the abelian case,
realized as gauge transformations of the electromagnetic potential together with the gauge
invariance of the field strength. The second is the Standard Model gauge group as a group
object with its central discrete subgroup, carrying no connection, curvature or
covariant-derivative theory. Everything the general theory needs is therefore still planned.

## Built on

- Electromagnetic potential — `Physlib/Electromagnetism/Kinematics/EMPotential.lean`
- Field strength — `Physlib/Electromagnetism/Kinematics/FieldStrength.lean`
- Standard Model gauge group — `Physlib/Particles/StandardModel/Basic.lean`

## Requirements

A gauge group is available: the concrete Standard Model group SU(3) × SU(2) × U(1), with its
projections and its central discrete subgroup. [1]

The gauge field in the abelian case is the electromagnetic potential, a spacetime-valued
Lorentz vector. [2]

The curvature of the abelian gauge field, its field strength, is built from the potential. [3]

A gauge transformation of the abelian potential shifts it by the gradient of a scalar, and the
pure-gauge potential is the shift of zero. [4]

The field strength is invariant under abelian gauge transformations. [5]

Pure-gauge configurations have vanishing curvature, while the bare gradient does not — which is
why the metric contraction is needed. [6]

Gauge transformations compose: the trivial shift acts as the identity, and successive shifts
add. [7]

Gauge transformations are compatible with the action of the Lorentz group. [8]

An arbitrary Lie group will serve as the structure group, in place of the Standard Model
group. [planned]

A gauge field for a general, non-abelian structure group will be defined, valued in the Lie
algebra of that group. [planned]

The gauge-covariant derivative acting on matter fields will be defined, with its
transformation law. [planned]

The non-abelian field strength, the Yang–Mills curvature, will be defined, with its covariant
transformation. [planned]

The Yang–Mills action and the field equations it gives rise to will be defined. [planned]

Parallel transport, Wilson lines and loops, and the holonomy of a connection will be
defined. [planned]

Gauge fields will be formulated as connections on a principal bundle. [planned]

## Further reading

- https://en.wikipedia.org/wiki/Mathematical_descriptions_of_the_electromagnetic_field#Gauge_freedom
- https://en.wikipedia.org/wiki/Gauge_theory

## Lean declarations

1. Physlib/Particles/StandardModel/Basic.lean — `GaugeGroupI`, `GaugeGroupI.toSU3`,
   `GaugeGroupI.toSU2`, `GaugeGroupI.toU1`, `gaugeGroupℤ₆SubGroup`
2. Physlib/Electromagnetism/Kinematics/EMPotential.lean — `ElectromagneticPotential`
3. Physlib/Electromagnetism/Kinematics/FieldStrength.lean — `toFieldStrength`
4. Physlib/Electromagnetism/Kinematics/GaugeTransformation.lean — `ofGradient`,
   `gaugeTransform`, `gaugeTransform_apply`
5. Physlib/Electromagnetism/Kinematics/GaugeTransformation.lean — `toFieldStrength_gaugeTransform`,
   `toFieldStrength_eval_gaugeTransform`
6. Physlib/Electromagnetism/Kinematics/GaugeTransformation.lean — `toFieldStrength_ofGradient`,
   `toFieldStrength_eval_bareGradient_inl_inr`, `toFieldStrength_bareGradient_ne_zero`
7. Physlib/Electromagnetism/Kinematics/GaugeTransformation.lean — `gaugeTransform_zero`,
   `gaugeTransform_gaugeTransform`, `ofGradient_add`, `ofGradient_zero`
8. Physlib/Electromagnetism/Kinematics/GaugeTransformation.lean — `ofGradient_equivariant`,
   `gaugeTransform_equivariant`
