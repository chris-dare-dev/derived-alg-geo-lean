# SF11 #1063 affine-open actual-unit sidecar

## Compiled boundary

`fixedBasePullbackOpenAfterExtension_compat_of_isPullback` derives the base-ring
action equation from `IsPullback.w`, `Scheme.Hom.comp_appTop`, and
`Scheme.ΓSpecIso_inv_naturality`. The resulting
`fixedBasePullbackOpenOfIsPullback` has a generator equation and commutes with
restriction on arbitrary opens. For a localization map of affine spectra,
`affineLocalizationTopNatIso_hom_localizedMk_square` identifies its value on a
top-section tensor generator with the existing localization comparison.

## Resolved elementwise restriction probe

`affineLocalizationTopNatIso_hom_localizedMk_square_restrict` now proves the
elementwise restriction of that identity to any chosen
`W : (Spec R).Opens`. Its proof applies
`fixedBasePullbackOpenOfIsPullback_restrict` with `(U := W)` to the identity
localization square, evaluates the morphism equality on `1 ⊗ x`, and uses the
top-section generator comparison. It only concerns sections restricted from
`⊤` for `tilde M`; it asserts no isomorphism at `W`.

The previous attempt was removed after three compile/revise cycles. Its exact
Lean diagnostics and their resolutions were:

1. `Unknown constant AlgebraicGeometry.Scheme.Opens.map` and
   `TopologicalSpace.Opens.leTop W` has type `W ⟶ ⊤` where `homOfLE` expects
   `W ≤ ⊤`. Opening `TopologicalSpace` and using `le_top` resolved these.
2. `don't know how to synthesize implicit argument Y` in
   `presheaf.map (homOfLE le_top).op`. The explicit annotation
   `(homOfLE le_top : W ⟶ ⊤).op` resolved this.
3. `don't know how to synthesize implicit argument U` in the call
   `fixedBasePullbackOpenOfIsPullback_restrict ... le_top`. Passing `(U := W)`
   resolved this. The subsequent `rw [ModuleCat.comp_apply, ModuleCat.comp_apply]`
   also failed with `Did not find an occurrence of the pattern
   (ConcreteCategory.hom (?f ≫ ?g)) ?x`; an explicit `change` of the evaluated
   restriction equation exposed the needed top-unit term and completed the
   rewrite.

The existing `affineLocalizationTopNatIso` is a comparison on top sections
for `Spec (Localization S) ⟶ Spec R` and a tilde module. It does not by itself
identify the scalar-extended sections of an arbitrary affine open `W` in a
Cartesian square with sections of its inverse image. The latter needs the
restricted square, the affine-section ring pushout (candidate:
`isIso_pushoutSection_of_isAffineOpen` in Mathlib `Morphisms/Flat.lean`), and
the module comparison on that square. For an arbitrary quasi-coherent module,
one must also transport through its affine `fromTildeΓ` isomorphism. None of
those extra identifications is asserted in this sidecar. In particular,
quasi-separatedness does not make `U ⊓ V` affine.
