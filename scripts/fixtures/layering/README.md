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
| `allowed/AlgebraicGeometry/Moduli` | geometry imports category theory, geometry, and the stability tree |
| `allowed/AlgebraicGeometry/DerivedCategory` | neutral derived geometry imports derived-category theory and coherent sheaves |
| `forbidden/CategoryTheory/Triangulated` | category theory importing geometry, through an import modifier |
| `forbidden/AlgebraicGeometry/DerivedCategory` | neutral derived geometry reaching the stability tree transitively |
| `forbidden/CategoryTheory/Triangulated/StabilityCondition/Weak/Families` | weak stability importing the Bridgeland theory |

Add a fixture whenever a rule is added or a boundary moves; a rule with no
forbidden fixture is a rule nobody has seen fire.
