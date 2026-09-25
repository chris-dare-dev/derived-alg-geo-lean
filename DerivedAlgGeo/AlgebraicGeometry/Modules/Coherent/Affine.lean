import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.BasicOpen
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.BasicOpenArrow
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.BasicOpenLocalizedSubobject
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.BasicOpenRestriction
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.BasicOpenSubobject
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.BasicOpenSubobjectClassification
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.Comparison
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.Free
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.Localization
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.LocalizedSubobject

/-! # Coherent sheaves on affine schemes

`Affine.Localization` exports the underived fixed-target arrow and zero-composite
three-term descent theorems for affine noetherian localizations.
`Affine.LocalizedSubobject` compares coherent tilde subobjects with localized
finite submodules on the localized spectrum, using explicit global-sections
transport. `Affine.BasicOpenLocalizedSubobject` transports that comparison to
the actual affine basic open `D(r)`; `Affine.BasicOpenSubobjectClassification`
classifies arbitrary coherent monos on that chart by finite submodules.
`Affine.BasicOpenRestriction` compares the restriction of a chosen finite
tilde subobject to `D(r*s)` with the span of its raw localized-module image.
No union-of-opens gluing is asserted.
-/
