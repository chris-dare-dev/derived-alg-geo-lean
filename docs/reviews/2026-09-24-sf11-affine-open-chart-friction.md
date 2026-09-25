# SF11 #1063 affine-open actual-unit sidecar

## Compiled boundary

`fixedBasePullbackOpenAfterExtension_compat_of_isPullback` derives the base-ring
action equation from `IsPullback.w`, `Scheme.Hom.comp_appTop`, and
`Scheme.ΓSpecIso_inv_naturality`. The resulting
`fixedBasePullbackOpenOfIsPullback` has a generator equation and commutes with
restriction on arbitrary opens. For a localization map of affine spectra,
`affineLocalizationTopNatIso_hom_localizedMk_square` identifies its value on a
top-section tensor generator with the existing localization comparison.

## Recovery point for an affine open

A proposed elementwise restriction of the last identity from `⊤` to
`W : (Spec R).Opens` was removed after three compile/revise cycles. The exact
Lean diagnostics were:

1. `Unknown constant AlgebraicGeometry.Scheme.Opens.map` and
   `TopologicalSpace.Opens.leTop W` has type `W ⟶ ⊤` where `homOfLE` expects
   `W ≤ ⊤`. Opening `TopologicalSpace` and using `le_top` resolved these.
2. `don't know how to synthesize implicit argument Y` in
   `presheaf.map (homOfLE le_top).op`. The explicit annotation
   `(homOfLE le_top : W ⟶ ⊤).op` resolved this.
3. `don't know how to synthesize implicit argument U` in the call
   `fixedBasePullbackOpenOfIsPullback_restrict ... le_top`. The next probe
   should pass `(U := W)` explicitly before checking the elementwise rewrite.

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
