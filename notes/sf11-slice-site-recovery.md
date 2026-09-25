# SF11 slice-site open-square recovery (2026-09-24)

Issue #1063 remains open. This bounded chunk is **underived**: it constructs the
slice-site pushforward comparison and proves four transport identities in
`Modules/Pullback/SliceSiteBaseChange.lean`. It does not prove the slice-site
unit square, relative base-change invertibility, derived Hom localization, a
heart statement, or Theorem 5.7(2).

## Compiled boundary

* `pushforwardOverIso f M U` compares `((f_* M).over U)` with
  `(pushforwardOverFunctor f U).obj (M.over (f ⁻¹ᵁ U))`. Its middle factor is the
  independently proved `pushforwardRestrictNatIso`; the others are
  `overFunctorEquiv` and the `overEquiv U` counit. No new isomorphism is assumed.
* `overEquiv_map_pushforwardOverIso_hom` identifies this comparison after the
  equivalence. `overEquiv_map_pullbackOverIso_hom` identifies the *existing*
  objectwise `pullbackOverIso` with the direct geometric
  `pullbackRestrictNatIso` and both equivalence factors.
* `overEquiv_map_pullbackOverAdjunction_unit` computes the composite
  adjunction's unit after applying `overEquiv U` and its counit.
  `pushforwardOverFunctor_map_transport` computes the image of a slice-site
  morphism through pushforward and the same counit.

The desired component square was typechecked as a **statement**, not proved:

```lean
(SheafOfModules.overFunctor Y.ringCatSheaf U).map
    ((pullbackPushforwardAdjunction f).unit.app N) ≫
  (pushforwardOverIso f ((pullback f).obj N) U).hom ≫
  (pushforwardOverFunctor f U).map (pullbackOverIso f N U).hom =
(pullbackOverAdjunction f U).unit.app (N.over U)
```

## Three critique/revise cycles and precise failure

1. Direct rewriting with naturality of `overFunctorEquiv`,
   `pullbackRestrictNatIso_unit_app`, and the transported pullback comparison
   failed even in a generic category probe: `rw` reconstructs a term involving
   `(F ⋙ G).obj A` at `instances` transparency but expects `G.obj (F.obj A)`.
   `exact`/`congrArg` and an explicitly typed categorical diagram chase avoid
   that generic mismatch.
2. In the scheme-specific proof, the generic chase elaborated, but the final
   equality still compared an `eU := overEquiv U`-typed morphism with the
   original `overEquiv U` morphism through `Sheaf.over Y.ringCatSheaf U`. An
   explicit `change` and typed counit-transport lemma did not make the final
   `simpa` accept these expressions; its diagnostic showed the mismatch in the
   `eU.counitIso` target `B := G.obj T` versus the unfolded target.
3. Raising *recursion depth only* to 2048 moved the proof past the earlier
   mismatch, but elaboration reached the default deterministic 200,000
   heartbeats at the theorem. A higher heartbeat cap would conceal this
   normalization problem; the unproved theorem and its unused generic chase
   were removed. The independently proved comparison and transport lemmas
   remain. No `sorry`, `admit`, or new axiom was committed.

The next research step is to test a small, explicitly typed normal-form lemma
for the final `overEquiv U` counit cancellation, keeping all sheaf-category
instances fixed, and then use `exact` on that lemma instead of `simpa` over a
large unfolded expression. The direct unit square
`pullbackRestrictNatIso_unit_app` and the objectwise pullback bridge supply the
mathematical ingredients, but their combination has not been compiled.

API/documentation traps: `pullbackOverUnitIso` in `Pullback/Restriction.lean`
identifies structure sheaves; it is **not** the adjunction unit. Lean accepts
stdin probes via `lake env lean /dev/stdin`; `lake env lean -` fails with “no
such file or directory” at this pin. Both details cost a probe and should be
recorded in future loop tooling guidance.

The first scoped `backward.isDefEq.respectTransparency false` remains necessary
for the composite-adjunction unit transport at the pinned Mathlib version; an
independent reviewer reproduced the `instances` transparency mismatch without
it. The same option on `pushforwardOverFunctor_map_transport` was unnecessary
and was removed after review.

The reviewer reproduced the **separate transparency probe** from the frozen
commit (not a fourth unit-square proof attempt) with:

```bash
git show d9b9ab04:DerivedAlgGeo/AlgebraicGeometry/Modules/Pullback/SliceSiteBaseChange.lean |
  sed -n '5p;17,25p;82,101p' | lake env lean /dev/stdin
```

The diagnostic starts `Tactic \`rewrite\` failed: Did not find an occurrence of
the pattern` at `/dev/stdin:29:40` and ends with the following verbatim cause:

```text
Note: The target expression is not type-correct under the `instances` transparency level,
which may have triggered the failure.
Application type mismatch: The argument
  Y.ringCatSheaf
has type
  TopCat.Sheaf RingCat ↑Y.toPresheafedSpace
but is expected to have type
  Sheaf (Opens.grothendieckTopology ↥Y) RingCat
in the application
  Sheaf.over Y.ringCatSheaf
```

The three capped unit-square attempts left prose symptoms but not verbatim
diagnostics or failed proof snippets in tracked files. Those cannot be
reconstructed from this commit without rerunning an attempt; future loop
tooling should retain a minimal failed probe before the recovery pivot.
