# DerivedAlgGeo

[![CI](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/workflows/ci.yml)
[![Documentation](https://github.com/chris-dare-dev/derived-alg-geo-lean/actions/workflows/docs.yml/badge.svg)](https://chris-dare-dev.github.io/derived-alg-geo-lean/)
[![Lean](https://img.shields.io/badge/Lean-v4.32.1-blue.svg)](https://github.com/leanprover/lean4/releases/tag/v4.32.1)
[![License](https://img.shields.io/badge/license-MIT%20%2F%20Apache--2.0-blue.svg)](LICENSE.md)

`DerivedAlgGeo` is a Lean 4 library for derived algebraic geometry. Its current
scope includes coherent sheaves and cohomology, dg and derived categories,
Bridgeland stability conditions, duality, intersection theory, and
Fourier--Mukai prerequisites.

The project is under active development. APIs may change as the formalization
grows and relevant results are upstreamed to Mathlib.

## Use

The complete stable library is available through one import:

```lean
import DerivedAlgGeo
```

Library code should prefer the narrowest useful subject import, such as:

```lean
import DerivedAlgGeo.AlgebraicGeometry.CoherentSheaf
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory
import DerivedAlgGeo.AlgebraicGeometry.Moduli
import DerivedAlgGeo.CategoryTheory.Monoidal
import DerivedAlgGeo.CategoryTheory.Enriched.DGCategory
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition
```

The repository is pinned to Lean and Mathlib v4.32.1. From a checkout, fetch the
Mathlib cache and build the module you are working on:

```bash
lake exe cache get
LEAN_NUM_THREADS=2 lake build DerivedAlgGeo.The.Module.You.Changed
```

**Full verification runs on the self-hosted Windows runners, not on your
machine.** Pushing an `agent/**` branch runs the whole gate there; a bare
`lake build` and `scripts/gates.sh` are refused locally by a `PreToolUse` hook.
See `CONTRIBUTING.md` §"Where verification runs".

## Layout

The source tree mirrors Mathlib's subject hierarchy, so a file extending a
Mathlib API sits where that API sits in Mathlib. `CLAUDE.md` states the
placement rule and `docs/architecture/layers.md` the dependency contract.

- `DerivedAlgGeo/AlgebraicGeometry` — schemes and everything stated about
  them: coherent sheaves, cohomology, scheme-derived categories and `Dqc`,
  geometric Fourier--Mukai kernels, stability on scheme-derived categories,
  semistable moduli, duality, intersection theory, Proj, and Riemann--Roch.
  Organized by geometric object; geometric realizations of categorical
  interfaces live here with the object they are about.
- `DerivedAlgGeo/CategoryTheory` — abelian, bicategorical, monoidal, and site
  theory; triangulated categories with t-structures, stability conditions,
  dg enhancements, Grothendieck groups, and Fourier--Mukai kernels.
- `DerivedAlgGeo/Algebra` — ring, module, and polynomial algebra; sheaves of
  modules on ringed sites under `Algebra/Category/ModuleCat/Sheaf`; derived
  categories, homotopy categories, dg categories, and spectral sequences
  under `Algebra/Homology`.
- `DerivedAlgGeo/LinearAlgebra`, `RingTheory`, `Topology`,
  `AlgebraicTopology` — reusable supporting mathematics at Mathlib's paths.
- `DerivedAlgGeo/Development` — exploratory code outside the stable umbrella.

Generated API documentation is published at
[chris-dare-dev.github.io/derived-alg-geo-lean](https://chris-dare-dev.github.io/derived-alg-geo-lean/).
See [CONTRIBUTING.md](CONTRIBUTING.md) for placement, proof, audit, and review
requirements.

The enforced dependency contract is documented in
[docs/architecture/layers.md](docs/architecture/layers.md).

## License

Repository-authored work is MIT-licensed. A small number of files derived from
Mathlib or earlier Apache-2.0 work retain that license and attribution. See
[LICENSE.md](LICENSE.md) for the complete scope and notices.
