# Layering fixtures

Known-answer tests for `scripts/check_layering.py`. Each `*.imports` file is a
hypothetical module: its path below `allowed/` or `forbidden/` is the module's
path below `DerivedAlgGeo/`, and its lines are the module's imports, in Lean
syntax, modifiers included. The gate runs rules 1 to 4 on every fixture and
requires each `allowed` fixture to pass and each `forbidden` fixture to fail
at least one rule, so an edit that silently stops rejecting something is
caught here rather than by the next regression.

| Fixture | Rule exercised |
| --- | --- |
| `allowed/AlgebraicGeometry/Moduli/Semistability` | geometry imports category theory, geometry, and the stability tree |
| `allowed/AlgebraicGeometry/DerivedCategory` | neutral derived geometry imports derived-category theory and coherent sheaves |
| `allowed/AlgebraicGeometry/Stability/Gieseker` | sheaf stability imports intersection theory and the weak slope tree |
| `allowed/AlgebraicGeometry/Numerical/Stability` | the numerical charge/wall subcomponent reaches the stability tree |
| `forbidden/CategoryTheory/Triangulated` | category theory importing geometry, through an import modifier |
| `forbidden/AlgebraicGeometry/DerivedCategory` | neutral derived geometry reaching the stability tree transitively |
| `forbidden/AlgebraicGeometry/Numerical/Core` | the numerical core reaching a charge construction |
| `forbidden/AlgebraicGeometry/Moduli/PerfectComplex` | relative perfection reaching the stability tree transitively |
| `forbidden/CategoryTheory/Triangulated/StabilityCondition/Weak/Families` | weak stability importing the Bridgeland theory |
| `forbidden/CategoryTheory/Triangulated/StabilityCondition/CentralCharge` | central-charge construction importing downstream wall loci |
| `forbidden/LinearAlgebra/QuadraticForm/ComplexPairing` | neutral paired-functional code importing stability conditions or wall arrangements |

The three fixtures below a *subcomponent* -- `Moduli/Semistability`,
`Stability/Gieseker`, `Numerical/Stability` -- sit where they do because rule
3's exemption is named by subcomponent, not by top-level subtree (MO1.01,
#1312). The two matching forbidden fixtures are their siblings, which the
blanket `Moduli/`, `Numerical/` and `Stability/` entries used to exempt and no
longer do. Moving one of these `allowed` fixtures back up a directory is enough
to make the gate reject it, which is the boundary being pinned.

Add a fixture whenever a rule is added or a boundary moves; a rule with no
forbidden fixture is a rule nobody has seen fire.
