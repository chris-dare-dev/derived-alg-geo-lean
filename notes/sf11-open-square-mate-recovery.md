# SF11 #1063 open-square mate research recovery

Cutover: `6d966b64` on `agent/sf11-open-square-mate-research`.
Scope: the underived scheme-module open square. This note records the bounded
attempt to identify two independently defined comparisons; it is not a proof
of that identification or of relative base change.

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

## Missing identification

The requested chart bridge is still the equality

```lean
mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
  (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U))
  (pullbackRestrictNatIso f U).inv = (pushforwardRestrictNatIso f U).hom
```

This statement typechecks, but no proof is installed. The direct pointwise
attempt left the unit of `pullbackPushforwardAdjunction (f ∣_ U)`, the inverse
geometric pullback comparison, and the counit of
`pullbackPushforwardAdjunction f` in the section-level goal. Simplifying the
mate definition did not remove those genuinely nontrivial maps. An analogous
pointwise simplification of the auxiliary pushforward mate initially failed
with the exact Lean diagnostic:

> `simp made no progress` — `The target expression is not type-correct under
> the instances transparency level ... Application type mismatch ... presheaf
> has type TopCat.Presheaf Ab ... but is expected to have type (Opens ↥Y)ᵒᵖ ⥤ Ab`.

The auxiliary lemma was recovered with an explicit presheaf-map `change`.
The remaining, narrower obligation has been typechecked in Lean but has an
unsolved goal:

```lean
conjugateEquiv
  ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
    (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι))
  ((Scheme.Modules.restrictAdjunction U.ι).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)))
  (pullbackRestrictNatIso f U).inv = (squarePushforwardIso f U).hom
```

No placeholder theorem was added.

## Next proof route

1. Prove the displayed conjugate equality by pasting the five factors of
   `pullbackRestrictNatIso`. Use pinned
   `Adjunction.unit_leftAdjointUniq_hom_app` for both
   `restrictFunctorIsoPullback` factors,
   `Scheme.Modules.conjugateEquiv_pullbackComp_inv` for the two composition
   factors, and `pushforwardCongr_hom_app_app` for the scheme-morphism equality.
   `mateEquiv_hcomp`/`mateEquiv_vcomp` organize the pasting; evaluate any
   remaining pushforward components with `pushforwardComp_hom_app_app` and
   `image_morphismRestrict_preimage`.
2. Apply pinned `CategoryTheory.iterated_mateEquiv_conjugateEquiv` to the
   independent pullback iso. The compiled `pushforwardRestrictNatIso_mate`
   supplies the same target `squarePushforwardIso`; injectivity of the second
   `mateEquiv` then gives the requested equality.
3. Only after that equality compiles, transport through the slice-site
   `pullbackOverIso` and state its pointwise section/unit consequence. None of
   this by itself proves relative or derived base change, Hom localization,
   or Theorem 5.7(2).
