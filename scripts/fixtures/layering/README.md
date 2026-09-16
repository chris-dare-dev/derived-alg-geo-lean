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
| `allowed/AlgebraicGeometry/Stability/Slope` | sheaf slope stability imports intersection theory and the abelian slope owner |
| `allowed/AlgebraicGeometry/Numerical/Stability` | the numerical charge/wall subcomponent reaches the stability tree |
| `forbidden/CategoryTheory/Triangulated` | category theory importing geometry, through an import modifier |
| `forbidden/AlgebraicGeometry/DerivedCategory` | neutral derived geometry reaching the stability tree transitively |
| `forbidden/AlgebraicGeometry/Numerical/Core` | the numerical core reaching a charge construction |
| `forbidden/AlgebraicGeometry/Moduli/PerfectComplex` | relative perfection reaching the stability tree transitively |
| `forbidden/CategoryTheory/Triangulated/StabilityCondition/Weak/Families` | weak stability importing the Bridgeland theory |
| `forbidden/CategoryTheory/Triangulated/StabilityCondition/CentralCharge` | central-charge construction importing downstream wall loci |
| `forbidden/LinearAlgebra/QuadraticForm/ComplexPairing` | neutral paired-functional code importing stability conditions or wall arrangements |
| `forbidden/AlgebraicGeometry/Stability/Gieseker` | sheaf stability reaching the triangulated stability tree, an exemption MO1.08 removed |
| `forbidden/AlgebraicGeometry/Stability/Slope` | a slope module reaching its Gieseker sibling instead of the comparison owner |
| `forbidden/CategoryTheory/Abelian/Stability` | abelian stability reaching the triangulated heart adapter it is upstream of |
| `allowed/LinearAlgebra/Matrix/GeneralLinearGroup/UniversalCover` | the GL+(2,R) cover importing its four neutral inputs |
| `forbidden/LinearAlgebra/Matrix/GeneralLinearGroup/UniversalCover` | the cover importing the stability action it was extracted from |
| `forbidden/Algebra/Order/NormalizedShift` | the neutral order-automorphism core reaching the stability tree |
| `forbidden/LinearAlgebra/Complex` | the complex-coordinate adapter importing the cover its public type is independent of |
| `forbidden/Topology/Covering` | a general covering lemma acquiring a DerivedAlgGeo dependency |

The two fixtures below a *subcomponent* -- `Moduli/Semistability` and
`Numerical/Stability` -- sit where they do because rule 3's exemption is named
by subcomponent, not by top-level subtree (MO1.01, #1312). The matching
forbidden fixtures are their siblings, which the blanket `Moduli/` and
`Numerical/` entries used to exempt and no longer do. Moving one of these
`allowed` fixtures back up a directory is enough to make the gate reject it,
which is the boundary being pinned.

`Stability/Gieseker` used to be a third such `allowed` fixture. MO1.08 (#1319)
moved the abstract slope theory it instantiates to
`CategoryTheory/Abelian/Stability/`, after which the whole sheaf-stability
subtree reaches no stability condition and the exemption was removed; the same
path is now a *forbidden* fixture, and the `allowed` one beside it imports the
abelian owner instead.

The five MO1.12 (#1323) fixtures pin ledger row 08 in both directions: the
cover and its neutral inputs are importable without stability conditions, and
the action adapter they were separated from stays where the ledger put it.

Add a fixture whenever a rule is added or a boundary moves; a rule with no
forbidden fixture is a rule nobody has seen fire.
