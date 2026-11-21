/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Glue.ExtendByZero
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Glue.MayerVietoris
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Glue.MayerVietorisHom
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Glue.TwoOpens

/-!
# Gluing in the derived category of one scheme

Derived extension by zero and restriction along open immersions, the Mayer–Vietoris triangle for
a cover by two opens, and gluing of derived objects over two opens, all in the derived category
of all module sheaves of a single scheme.

## Main definitions

This umbrella introduces no definitions. It exports the derived restriction and extension by zero,
the Mayer–Vietoris triangle and its sequence of morphisms, and two-open gluing.

## Main results

This umbrella introduces no results; see the modules it exports.

## Implementation notes

The triangle lives in the derived category of all module sheaves, not in `Dqc`, because the
extension by zero of a quasi-coherent sheaf need not be quasi-coherent.

## References

* Stacks Project, Tags 08BT, 08BU, 08BW and 08DG.

## Tags

derived category, gluing, Mayer–Vietoris, extension by zero
-/
