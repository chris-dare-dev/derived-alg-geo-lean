/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import DerivedAlgGeo.Topology.Sheaves.Basis

/-!
# The localisation criterion for the affine comparison theorem

For a commutative ring `R`, the affine comparison identifies a quasi-coherent sheaf on `Spec R`
with the sheaf associated to its global sections. This is Stacks
[01IA](https://stacks.math.columbia.edu/tag/01IA) and Hartshorne II.5.1. The pinned Mathlib
v4.32.1 supplies the quasi-coherent case as
`AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent` in
`Mathlib/AlgebraicGeometry/Modules/Tilde.lean`.

This file develops a more general localization criterion for the counit
`AlgebraicGeometry.Scheme.Modules.fromTildeΓ`: it is an isomorphism **if and only if** restriction
to every basic open is a localization. It does not reprove the upstream quasi-coherent comparison.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.basicOpenRestriction` is restriction of global sections to
  the basic open `D(f)`.

## Main results

* `AlgebraicGeometry.isIso_fromTildeΓ_app_basicOpen` — the component of the counit at `D(f)`
  is an isomorphism under the hypothesis that restriction is a localisation at the powers of `f`.
* `AlgebraicGeometry.isIso_fromTildeΓ_of_isLocalizedModule` — hence the counit is an
  isomorphism as soon as every such restriction is a localisation.
* `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestriction_tilde` — the base
  case, `M = N^~`, where that hypothesis holds. It is both the starting point of the general
  argument and the check that the hypothesis is satisfiable rather than vacuous.
* `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestriction_of_isIso` — the
  converse of the reduction, obtained by transporting the base case along the counit.
* `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestriction_of_presentation` —
  a presentation on `Spec R` makes restriction to each basic open a localization.
* `AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_iff_isLocalizedModule` — the two put
  together: **`IsIso M.fromTildeΓ ↔ ∀ f, IsLocalizedModule (powers f) (restriction to D(f))`.**
  This is the statement to quote.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules.fromTildeΓ` is *built* by
`TopCat.Sheaf.restrictHomEquivHom` along
`PrimeSpectrum.isBasis_basic_opens`, with its component at `D(f)` given by
`IsLocalizedModule.lift`. Mathlib's
`AlgebraicGeometry.Scheme.Modules.toOpen_fromTildeΓ_app` records the
resulting triangle: the component composed with `AlgebraicGeometry.tilde.toOpen` is the restriction
map. Since `AlgebraicGeometry.tilde.toOpen` at `D(f)` is a localisation at `Submonoid.powers f` —
Mathlib supplies that instance — the component is the comparison map between two candidate
localisations. Under the localization hypothesis, the component theorem proves this map is an
isomorphism. The separate converse and if-and-only-if statement concern the whole counit, not an
unconditional equivalence for a single component. The whole-counit result is
`AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_iff_isLocalizedModule`.

Nothing in this local criterion needs quasi-coherence. Mathlib states
`AlgebraicGeometry.Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen` for an *arbitrary*
`M : (AlgebraicGeometry.Spec R).Modules`,
not only for tildes. The quasi-coherent application is provided by Mathlib's pinned instance; the
local criterion remains available when a caller supplies the localization hypotheses directly.

### Relation to the local bridges

`AlgebraicGeometry.Modules.Affine.Gluing` documents the current division of work: Mathlib owns the
finite-cover proof of the quasi-coherent comparison, while the local file retains the
restriction-to-chart linear equivalence and wrappers for DerivedAlgGeo's explicit
quasi-coherent-data and localization APIs. In particular,
`AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestriction_of_isQuasicoherent` is a
bridge to the upstream result, not a second proof of it. The scheme/slice transport used by these
local bridges is in `AlgebraicGeometry.Modules.Restriction.OpenImmersion`.

## References

* [Stacks, Tag 01IA](https://stacks.math.columbia.edu/tag/01IA).
* See the [affine and projective spectrum placement map](../../../../docs/architecture/placement.md)
  for pinned Mathlib source links.

## Tags

affine scheme, quasi-coherent modules, global sections, basic-open localization, tilde, counit
-/

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

open _root_.PrimeSpectrum

variable {R : CommRingCat.{u}}

namespace Scheme.Modules

/-- Restriction of the global sections of an `𝒪_{Spec R}`-module to the basic open `D(f)`.

This is the map the affine comparison theorem asserts to be a localisation at
`Submonoid.powers f`. -/
noncomputable def basicOpenRestriction (M : (Spec R).Modules) (f : R) :
    (modulesSpecToSheaf.obj M).presheaf.obj (op ⊤) ⟶
      (modulesSpecToSheaf.obj M).presheaf.obj (op (PrimeSpectrum.basicOpen f)) :=
  (modulesSpecToSheaf.obj M).presheaf.map (homOfLE (fun _ _ => trivial)).op

/-- The counit composed with `tilde.toOpen` is restriction — Mathlib's
`toOpen_fromTildeΓ_app`, phrased through `basicOpenRestriction`. -/
lemma toOpen_comp_fromTildeΓ_app (M : (Spec R).Modules) (f : R) :
    tilde.toOpen ((modulesSpecToSheaf.obj M).presheaf.obj (op ⊤)) (PrimeSpectrum.basicOpen f) ≫
        (modulesSpecToSheaf.map M.fromTildeΓ).hom.app (op (PrimeSpectrum.basicOpen f)) =
      M.basicOpenRestriction f := by
  rw [toOpen_fromTildeΓ_app M (PrimeSpectrum.basicOpen f)]; rfl

/-- **The base case: for `M = N^~` the restriction to `D(f)` is a localisation.**

`AlgebraicGeometry.tilde.toOpen N ⊤` is an isomorphism, and its composite with restriction to
`D(f)` is `AlgebraicGeometry.tilde.toOpen N D(f)` by
`AlgebraicGeometry.tilde.toOpen_res`. Thus the restriction inherits the localization property
Mathlib proves for `AlgebraicGeometry.tilde.toOpen N D(f)`.

This is what the general statement — the hypothesis of
`AlgebraicGeometry.isIso_fromTildeΓ_of_isLocalizedModule` — has to be reduced to for a
quasi-coherent `M`. It also checks that the hypothesis is satisfiable rather than vacuous:
feeding this lemma to the reduction recovers
`CategoryTheory.IsIso (AlgebraicGeometry.tilde N).fromTildeΓ`, which Mathlib knows independently.
-/
instance isLocalizedModule_basicOpenRestriction_tilde (N : ModuleCat.{u} R) (f : R) :
    IsLocalizedModule (Submonoid.powers f) (basicOpenRestriction (tilde N) f).hom := by
  haveI : IsIso (tilde.toOpen N ⊤) := tilde.isIso_toOpen_top
  let e : N ≃ₗ[R] _ := (asIso (tilde.toOpen N ⊤)).toLinearEquiv
  haveI : IsLocalizedModule (Submonoid.powers f)
      ((basicOpenRestriction (tilde N) f).hom ∘ₗ (e : N →ₗ[R] _)) := by
    -- `tilde.toOpen_res` is `rfl`, so this is a definitional match.
    convert (inferInstance : IsLocalizedModule (Submonoid.powers f)
      (tilde.toOpen N (PrimeSpectrum.basicOpen f)).hom) using 1
    change (tilde.toOpen N ⊤ ≫ basicOpenRestriction (tilde N) f).hom =
      (tilde.toOpen N (PrimeSpectrum.basicOpen f)).hom
    exact congrArg ModuleCat.Hom.hom
      (tilde.toOpen_res N ⊤ (PrimeSpectrum.basicOpen f) _)
  have := IsLocalizedModule.of_linearEquiv_right (Submonoid.powers f)
    ((basicOpenRestriction (tilde N) f).hom ∘ₗ (e : N →ₗ[R] _)) e.symm
  simpa [LinearMap.comp_assoc] using this

end Scheme.Modules

/-- **The component of the counit at `D(f)` is an isomorphism when restriction to `D(f)` is a
localisation at the powers of `f`.**

Both `tilde.toOpen` and the restriction are then localisations of `Γ(M, ⊤)` at the same
submonoid, and the component is the comparison map between them. -/
theorem isIso_fromTildeΓ_app_basicOpen (M : (Spec R).Modules) (f : R)
    [IsLocalizedModule (Submonoid.powers f) (M.basicOpenRestriction f).hom] :
    IsIso ((modulesSpecToSheaf.map M.fromTildeΓ).hom.app (op (basicOpen f))) := by
  set N := (modulesSpecToSheaf.obj M).presheaf.obj (op ⊤) with hN
  have hunit := Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen (M := M) f le_rfl
  have key := Scheme.Modules.toOpen_comp_fromTildeΓ_app M f
  have heq : ((modulesSpecToSheaf.map M.fromTildeΓ).hom.app (op (basicOpen f))).hom
      = (IsLocalizedModule.linearEquiv (Submonoid.powers f)
          (tilde.toOpen N (basicOpen f)).hom (M.basicOpenRestriction f).hom).toLinearMap := by
    refine IsLocalizedModule.ext (Submonoid.powers f) (tilde.toOpen N (basicOpen f)).hom
      (fun s => ?_) ?_
    · obtain ⟨n, hn⟩ := s.2
      rw [← hn, map_pow]
      exact hunit.pow n
    · ext x
      have := congrArg (fun (g : N ⟶ _) => g.hom x) key
      simpa using this
  have hbij : Function.Bijective
      ((modulesSpecToSheaf.map M.fromTildeΓ).hom.app (op (basicOpen f))).hom := by
    rw [heq]
    exact (IsLocalizedModule.linearEquiv _ _ _).bijective
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hbij

/-- **The counit is an isomorphism as soon as restriction to every basic open is a
localisation.**

This is a basiswise reduction of the affine comparison. Mathlib's pinned quasi-coherent instance
proves the comparison for quasi-coherent modules by a finite basic-open-cover argument; this
criterion also applies to an arbitrary module sheaf when its localization hypotheses are supplied
directly. -/
theorem isIso_fromTildeΓ_of_isLocalizedModule (M : (Spec R).Modules)
    (h : ∀ f : R, IsLocalizedModule (Submonoid.powers f) (M.basicOpenRestriction f).hom) :
    IsIso M.fromTildeΓ := by
  haveI := (SpecModulesToSheafFullyFaithful (R := R)).full
  haveI := (SpecModulesToSheafFullyFaithful (R := R)).faithful
  suffices hiso : IsIso (modulesSpecToSheaf.map M.fromTildeΓ) from
    isIso_of_reflects_iso _ modulesSpecToSheaf
  refine TopCat.Sheaf.isIso_of_isIso_app_of_isBasis isBasis_basic_opens _ ?_
  rintro U ⟨f, rfl⟩
  haveI := h f
  exact isIso_fromTildeΓ_app_basicOpen M f

/-- `basicOpenRestriction` is a presheaf restriction map, so it is natural in `M`. -/
lemma Scheme.Modules.basicOpenRestriction_naturality {M N : (Spec R).Modules} (φ : M ⟶ N)
    (f : R) :
    M.basicOpenRestriction f ≫
        (modulesSpecToSheaf.map φ).hom.app (op (PrimeSpectrum.basicOpen f)) =
      (modulesSpecToSheaf.map φ).hom.app (op ⊤) ≫ N.basicOpenRestriction f :=
  (modulesSpecToSheaf.map φ).hom.naturality _

/-- **The converse of `AlgebraicGeometry.isIso_fromTildeΓ_of_isLocalizedModule`.**

If `M` is in the essential image of `~` — equivalently, if its counit is an isomorphism — then
restriction to each basic open is a localisation, by transporting
`AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestriction_tilde` across that
isomorphism. -/
theorem Scheme.Modules.isLocalizedModule_basicOpenRestriction_of_isIso (M : (Spec R).Modules)
    [IsIso M.fromTildeΓ] (f : R) :
    IsLocalizedModule (Submonoid.powers f) (M.basicOpenRestriction f).hom := by
  set N := (modulesSpecToSheaf.obj M).presheaf.obj (op ⊤) with hN
  -- `modulesSpecToSheaf` sends the counit to an isomorphism of sheaves; `sheafToPresheaf`
  -- carries that to the underlying natural transformation, and
  -- `CategoryTheory.NatIso.isIso_app_of_isIso`
  -- then makes every component invertible.
  haveI : IsIso (modulesSpecToSheaf.map M.fromTildeΓ) := inferInstance
  haveI : IsIso (modulesSpecToSheaf.map M.fromTildeΓ).hom := by
    change IsIso ((sheafToPresheaf _ _).map (modulesSpecToSheaf.map M.fromTildeΓ))
    infer_instance
  -- the naturality square, with both verticals invertible
  have key := Scheme.Modules.basicOpenRestriction_naturality (M := tilde N) (N := M)
    M.fromTildeΓ f
  let eTop := (asIso ((modulesSpecToSheaf.map M.fromTildeΓ).hom.app (op ⊤))).toLinearEquiv
  let eBas := (asIso ((modulesSpecToSheaf.map M.fromTildeΓ).hom.app
    (op (PrimeSpectrum.basicOpen f)))).toLinearEquiv
  -- restriction on `tilde N` is a localisation; push it across the two isomorphisms
  haveI h1 := IsLocalizedModule.of_linearEquiv (Submonoid.powers f)
    ((tilde N).basicOpenRestriction f).hom eBas
  haveI h2 := IsLocalizedModule.of_linearEquiv_right (Submonoid.powers f)
    (eBas.toLinearMap ∘ₗ ((tilde N).basicOpenRestriction f).hom) eTop.symm
  convert h2 using 1
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := eTop.surjective x
  have hy := congrArg (fun g => ModuleCat.Hom.hom g y) key
  simpa [eTop, eBas] using hy.symm

/-- A presentation on `Spec R` makes the counit an isomorphism by Mathlib's
`AlgebraicGeometry.isIso_fromTildeΓ_of_presentation`; the localization criterion
then shows that each basic-open restriction is a localization. -/
theorem Scheme.Modules.isLocalizedModule_basicOpenRestriction_of_presentation
    (M : (Spec R).Modules) (P : M.Presentation) (f : R) :
    IsLocalizedModule (Submonoid.powers f) (M.basicOpenRestriction f).hom := by
  letI := isIso_fromTildeΓ_of_presentation M P
  exact M.isLocalizedModule_basicOpenRestriction_of_isIso f

/-- **The affine comparison, as a characterisation.**

The counit is an isomorphism exactly when restriction to every basic open is a localisation.
Both directions are now available, so this is the statement to quote. -/
theorem Scheme.Modules.isIso_fromTildeΓ_iff_isLocalizedModule (M : (Spec R).Modules) :
    IsIso M.fromTildeΓ ↔
      ∀ f : R, IsLocalizedModule (Submonoid.powers f) (M.basicOpenRestriction f).hom :=
  ⟨fun _ f => M.isLocalizedModule_basicOpenRestriction_of_isIso f,
    isIso_fromTildeΓ_of_isLocalizedModule M⟩

end AlgebraicGeometry
