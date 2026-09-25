# SF11 #1063 open-square mate research recovery

Cutover: `6d966b64` on `agent/sf11-open-square-mate-research`.
Scope: the underived scheme-module open square. The formerly missing
identification of two independently defined comparisons now compiles. This
does not prove relative base change.

## Compiled part

`pullbackRestrictNatIso f U` is the direct pullback-side isomorphism. Its five
factors are `restrictFunctorIsoPullback` at the inverse-image open,
`pullbackComp` for `(f ⁻¹ᵁ U).ι ≫ f`, `pullbackCongr
(morphismRestrict_ι f U).symm`, inverse `pullbackComp` for
`f ∣_ U ≫ U.ι`, and inverse `restrictFunctorIsoPullback` at `U.ι`.
It does not refer to `pushforwardRestrictNatIso`.

`squarePushforwardIso f U` is a second direct comparison, assembled from
`pushforwardComp`, `pushforwardCongr (morphismRestrict_ι f U).symm`, and inverse
`pushforwardComp`. The compiled theorem `pushforwardRestrictNatIso_mate` proves

```lean
mateEquiv (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι)
  (Scheme.Modules.restrictAdjunction U.ι)
  (pushforwardRestrictNatIso f U).hom = (squarePushforwardIso f U).hom
```

Pointwise, that proof exposes the open-immersion unit, the independently
defined section transport, and the open-immersion counit. The result is a
composite of three `M.presheaf.map` calls; `Functor.map_comp` and uniqueness
of morphisms between opens close it. The proof uses an explicit `change` to
avoid a known `instances` transparency problem.

## Compiled identification

The theorem `pullbackRestrictNatIso_conjugate` proves the formerly missing
conjugate equality:

```lean
conjugateEquiv
  ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
    (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι))
  ((Scheme.Modules.restrictAdjunction U.ι).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)))
  (pullbackRestrictNatIso f U).inv = (squarePushforwardIso f U).hom
```

`pullbackRestrictNatIso_mate` then proves the requested horizontal mate
equality against the independently defined `pushforwardRestrictNatIso`:

```lean
mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
  (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U))
  (pullbackRestrictNatIso f U).inv = (pushforwardRestrictNatIso f U).hom
```

## Proof and friction

The conjugate proof names six adjunctions and splits the inverse geometric
iso into five factors. `conjugateEquiv_comp` reverses their order. The two
restriction/pullback factors become identity maps because
`restrictFunctorIsoPullback` is `leftAdjointUniq`. The two composition factors
become `pushforwardComp` and its inverse via pinned
`Scheme.Modules.conjugateEquiv_pullbackComp_inv` and
`conjugateEquiv_comm`. The equality-transport factor is proved separately:
after substituting the scheme-morphism equality,
`pullbackCongr` becomes identity, and `pushforwardCongr_hom_app_app`
becomes a presheaf map of an identity open morphism. `M.presheaf.map_id`
finishes its component calculation. The final normal form uses
`Iso.symm_hom` to match the direct pushforward iso.

`CategoryTheory.iterated_mateEquiv_conjugateEquiv`, the already compiled
`pushforwardRestrictNatIso_mate`, and injectivity of the second `mateEquiv`
give the horizontal equality. An explicit `change` aligns the iterated mate
with the displayed conjugate equality at the pinned API's transparency level.

The earlier direct pointwise attempt left the pullback unit, inverse
geometric pullback comparison, and pullback counit in the section-level goal.
The auxiliary pushforward mate initially failed with the exact Lean diagnostic:

> `simp made no progress` — `The target expression is not type-correct under
> the instances transparency level ... Application type mismatch ... presheaf
> has type TopCat.Presheaf Ab ... but is expected to have type (Opens ↥Y)ᵒᵖ ⥤ Ab`.

The auxiliary lemma was recovered with an explicit presheaf-map `change`.
The conjugate proof likewise keeps the equality transport explicit; there is
no comparison defined from `conjugateEquiv` and no placeholder theorem.

## Remaining follow-up

Transport the proved horizontal mate through the slice-site
`pullbackOverIso` and state its pointwise section/unit consequence. The
underived open-square mate alone does not establish relative or derived base
change, Hom localization, or Theorem 5.7(2).
