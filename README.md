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
import DerivedAlgGeo.CategoryTheory.Monoidal
import DerivedAlgGeo.CategoryTheory.Enriched.DGCategory
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition
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

- `DerivedAlgGeo/AlgebraicGeometry` — coherent sheaves, cohomology, duality,
  intersection theory, Proj, and Riemann--Roch.
- `DerivedAlgGeo/CategoryTheory` — monoidal and enriched category theory, raw
  and pretriangulated dg categories, dg enhancements, t-structures, and
  stability conditions.
- `DerivedAlgGeo/Compatibility` — temporary leaf imports for staged module
  migrations; stable subjects never depend on it.
- `DerivedAlgGeo/LinearAlgebra` — integral and Mukai lattices and matrix tools.
- `DerivedAlgGeo/Algebra` and `DerivedAlgGeo/Topology` — reusable supporting
  mathematics.
- `DerivedAlgGeo/Development` — exploratory code outside the stable umbrella.

Generated API documentation is published at
[chris-dare-dev.github.io/derived-alg-geo-lean](https://chris-dare-dev.github.io/derived-alg-geo-lean/).
See [CONTRIBUTING.md](CONTRIBUTING.md) for placement, proof, audit, and review
requirements.

The enforced subject dependency DAG is documented in
[docs/architecture/layers.md](docs/architecture/layers.md).

## License

Repository-authored work is MIT-licensed. A small number of files derived from
Mathlib or earlier Apache-2.0 work retain that license and attribution. See
[LICENSE.md](LICENSE.md) for the complete scope and notices.
