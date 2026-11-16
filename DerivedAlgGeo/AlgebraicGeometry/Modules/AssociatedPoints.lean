/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.AffineChart
import DerivedAlgGeo.AlgebraicGeometry.Modules.Quasicoherent.Stalk

/-!
# Associated points of a module sheaf

A point `x` of a scheme `X` is associated to a module sheaf `F` when the maximal ideal of the
local ring `𝒪_{X,x}` is an associated prime of the stalk `F_x` (Stacks 02OJ). On an affine open
`U` of `X`, for quasi-coherent `F`, an associated prime of the `Γ(X, U)`-module `Γ(U, F)` is an
associated point, and conversely for a finitely generated prime (Stacks 02OK). A coherent sheaf
on a locally Noetherian scheme has finitely many associated points in every quasi-compact subset
(Stacks 05AF). When `Γ(X, U)` is Noetherian, a function on `U` that is a unit at every associated
point in `U` acts injectively on every stalk of `F` over `U`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.associatedPoints`: the associated points of a module sheaf.

## Main results

* `AlgebraicGeometry.Scheme.Modules.fromSpec_mem_associatedPoints_of_mem_associatedPrimes`: an
  associated prime of `Γ(U, F)` is an associated point.
* `AlgebraicGeometry.Scheme.Modules.mem_associatedPrimes_of_fromSpec_mem_associatedPoints`: the
  converse, for a finitely generated prime.
* `AlgebraicGeometry.Scheme.Modules.fromSpec_mem_associatedPoints_iff`: the two together, when
  `Γ(X, U)` is Noetherian.
* `AlgebraicGeometry.Scheme.Modules.associatedPoints_inter_finite`: a coherent sheaf on a locally
  Noetherian scheme has finitely many associated points in every quasi-compact subset, and
  `AlgebraicGeometry.Scheme.Modules.associatedPoints_finite` on a Noetherian scheme.
* `AlgebraicGeometry.Scheme.Modules.isSMulRegular_germ`: a function on an affine open with a
  Noetherian coordinate ring that is a unit at every associated point there is a nonzerodivisor on
  every stalk there.

## Implementation notes

### Mathlib's associated primes carry a radical

Mathlib's `IsAssociatedPrime I M` asks that `I` be the *radical* of the annihilator of an
element, not the annihilator itself. At the maximal ideal of a local ring this says that `𝔪` is
minimal over the annihilator of an element, which is Stacks' *weakly* associated prime (Stacks
0547). So `associatedPoints F` is the set of weakly associated points of Stacks 056L. When `𝔪_x`
is finitely generated, in particular on a locally Noetherian scheme, the two notions agree
(Stacks 05AR). The finiteness and nonzerodivisor theorems here are stated in that setting.

### The affine comparison is a localization statement

For quasi-coherent `F` and affine `U`, the germ map `Γ(U, F) → F_x` is the localization at the
prime of `x` (`Scheme.Modules.isLocalizedModule_germLinearMap`), and `𝒪_{X,x}` is the
localization of `Γ(X, U)` there (`IsAffineOpen.isLocalization_stalk'`). Mathlib's comparison of
associated primes along a localization (Stacks 0310) then gives both directions; the converse
direction needs the prime to be finitely generated, as in Stacks 02OK.

## References

* [Stacks, Definition 31.2.1 (Tag 02OJ)](https://stacks.math.columbia.edu/tag/02OJ)
* [Stacks, Lemma 31.2.2 (Tag 02OK)](https://stacks.math.columbia.edu/tag/02OK)
* [Stacks, Lemma 31.2.5 (Tag 05AF)](https://stacks.math.columbia.edu/tag/05AF)
* [Stacks, Definition 31.5.1 (Tag 056L)](https://stacks.math.columbia.edu/tag/056L) and
  [Lemma 31.5.8 (Tag 05AR)](https://stacks.math.columbia.edu/tag/05AR)

## Tags

associated point, associated prime, coherent sheaf, Noetherian scheme, nonzerodivisor
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- **The associated points of a module sheaf** (Stacks 02OJ): the points `x` at which the
maximal ideal of `𝒪_{X,x}` is an associated prime of the stalk `F_x`.

Mathlib's `IsAssociatedPrime` asks for the radical of an annihilator, so off the locally
Noetherian setting these are Stacks' weakly associated points (Stacks 056L); when `𝔪_x` is
finitely generated the two agree (Stacks 05AR). -/
def associatedPoints (F : X.Modules) : Set X :=
  {x | IsAssociatedPrime (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    ((moduleStalkFunctor X x).obj F)}

theorem mem_associatedPoints_iff (F : X.Modules) (x : X) :
    x ∈ associatedPoints F ↔ IsAssociatedPrime (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      ((moduleStalkFunctor X x).obj F) :=
  Iff.rfl

/-- Isomorphic module sheaves have the same associated points. -/
theorem associatedPoints_eq_of_iso {F G : X.Modules} (e : F ≅ G) :
    associatedPoints F = associatedPoints G := by
  ext x
  exact LinearEquiv.isAssociatedPrime_iff ((moduleStalkFunctor X x).mapIso e).toLinearEquiv

section Affine

variable (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U)

include hU in
private theorem fromSpec_mem (y : PrimeSpectrum Γ(X, U)) : hU.fromSpec y ∈ U := by
  rw [← SetLike.mem_coe, ← hU.range_fromSpec]
  exact Set.mem_range_self y

/-- Mathlib's comparison of associated primes along the localization `Γ(U, F) → F_x`, at
`x = hU.fromSpec y`: a prime of `𝒪_{X,x}` whose contraction to `Γ(X, U)` is associated to
`Γ(U, F)` is associated to `F_x` (Stacks 0310, part 1). -/
private theorem mem_associatedPrimes_stalk (y : PrimeSpectrum Γ(X, U))
    (𝔮 : Ideal (X.presheaf.stalk (hU.fromSpec y)))
    (h : 𝔮.comap (X.presheaf.germ U _ (fromSpec_mem hU y)).hom ∈
      associatedPrimes Γ(X, U) Γ(F, U)) :
    𝔮 ∈ associatedPrimes (X.presheaf.stalk (hU.fromSpec y))
      ((moduleStalkFunctor X (hU.fromSpec y)).obj F) := by
  letI : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨_, fromSpec_mem hU y⟩
  haveI : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) y.asIdeal :=
    hU.isLocalization_stalk' y (fromSpec_mem hU y)
  haveI := isLocalizedModule_germLinearMap F hU y (fromSpec_mem hU y)
  letI : Module (X.presheaf.stalk (hU.fromSpec y))
      ((ModuleCat.restrictScalars (X.presheaf.germ U _ (fromSpec_mem hU y)).hom).obj
        ((moduleStalkFunctor X (hU.fromSpec y)).obj F)) :=
    inferInstanceAs (Module _ ((moduleStalkFunctor X (hU.fromSpec y)).obj F))
  haveI : IsScalarTower Γ(X, U) (X.presheaf.stalk (hU.fromSpec y))
      ((ModuleCat.restrictScalars (X.presheaf.germ U _ (fromSpec_mem hU y)).hom).obj
        ((moduleStalkFunctor X (hU.fromSpec y)).obj F)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact Module.associatedPrimes.mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
    y.asIdeal.primeCompl (germLinearMap F U _ (fromSpec_mem hU y)) 𝔮 h

/-- The converse comparison (Stacks 0310, part 2): the contraction of an associated prime of
`F_x` is associated to `Γ(U, F)` when it is finitely generated. -/
private theorem comap_mem_associatedPrimes (y : PrimeSpectrum Γ(X, U))
    (𝔮 : Ideal (X.presheaf.stalk (hU.fromSpec y)))
    (h : 𝔮 ∈ associatedPrimes (X.presheaf.stalk (hU.fromSpec y))
      ((moduleStalkFunctor X (hU.fromSpec y)).obj F))
    (hfg : (𝔮.comap (X.presheaf.germ U _ (fromSpec_mem hU y)).hom).FG) :
    𝔮.comap (X.presheaf.germ U _ (fromSpec_mem hU y)).hom ∈
      associatedPrimes Γ(X, U) Γ(F, U) := by
  letI : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨_, fromSpec_mem hU y⟩
  haveI : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) y.asIdeal :=
    hU.isLocalization_stalk' y (fromSpec_mem hU y)
  haveI := isLocalizedModule_germLinearMap F hU y (fromSpec_mem hU y)
  letI : Module (X.presheaf.stalk (hU.fromSpec y))
      ((ModuleCat.restrictScalars (X.presheaf.germ U _ (fromSpec_mem hU y)).hom).obj
        ((moduleStalkFunctor X (hU.fromSpec y)).obj F)) :=
    inferInstanceAs (Module _ ((moduleStalkFunctor X (hU.fromSpec y)).obj F))
  haveI : IsScalarTower Γ(X, U) (X.presheaf.stalk (hU.fromSpec y))
      ((ModuleCat.restrictScalars (X.presheaf.germ U _ (fromSpec_mem hU y)).hom).obj
        ((moduleStalkFunctor X (hU.fromSpec y)).obj F)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact
    Module.associatedPrimes.comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg
      y.asIdeal.primeCompl (germLinearMap F U _ (fromSpec_mem hU y)) 𝔮 h hfg

/-- The maximal ideal of `𝒪_{X,x}` contracts to the prime of `x` in `Γ(X, U)`. -/
private theorem comap_maximalIdeal (y : PrimeSpectrum Γ(X, U)) :
    (IsLocalRing.maximalIdeal (X.presheaf.stalk (hU.fromSpec y))).comap
      (X.presheaf.germ U _ (fromSpec_mem hU y)).hom = y.asIdeal := by
  letI : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨_, fromSpec_mem hU y⟩
  haveI : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) y.asIdeal :=
    hU.isLocalization_stalk' y (fromSpec_mem hU y)
  exact IsLocalization.AtPrime.under_maximalIdeal _ y.asIdeal

/-- **An associated prime of `Γ(U, F)` is an associated point of `F`** (Stacks 02OK, part 1), for
quasi-coherent `F` and an affine open `U`. No finiteness is needed in this direction. -/
theorem fromSpec_mem_associatedPoints_of_mem_associatedPrimes (y : PrimeSpectrum Γ(X, U))
    (hy : y.asIdeal ∈ associatedPrimes Γ(X, U) Γ(F, U)) :
    hU.fromSpec y ∈ associatedPoints F :=
  mem_associatedPrimes_stalk F hU y _ ((comap_maximalIdeal hU y).symm ▸ hy)

/-- **An associated point of `F` in an affine open `U` gives an associated prime of `Γ(U, F)`**
(Stacks 02OK, part 2), when that prime is finitely generated. -/
theorem mem_associatedPrimes_of_fromSpec_mem_associatedPoints (y : PrimeSpectrum Γ(X, U))
    (hfg : y.asIdeal.FG) (hy : hU.fromSpec y ∈ associatedPoints F) :
    y.asIdeal ∈ associatedPrimes Γ(X, U) Γ(F, U) := by
  rw [← comap_maximalIdeal hU y]
  exact comap_mem_associatedPrimes F hU y _ hy ((comap_maximalIdeal hU y).symm ▸ hfg)

/-- **On an affine open with a Noetherian coordinate ring, the associated points of a
quasi-coherent `F` are the associated primes of `Γ(U, F)`** (Stacks 02OK). -/
theorem fromSpec_mem_associatedPoints_iff [IsNoetherianRing Γ(X, U)]
    (y : PrimeSpectrum Γ(X, U)) :
    hU.fromSpec y ∈ associatedPoints F ↔ y.asIdeal ∈ associatedPrimes Γ(X, U) Γ(F, U) :=
  ⟨mem_associatedPrimes_of_fromSpec_mem_associatedPoints F hU y
      ((isNoetherianRing_iff_ideal_fg _).mp ‹_› _),
    fromSpec_mem_associatedPoints_of_mem_associatedPrimes F hU y⟩

include hU in
/-- **A function that is a unit at every associated point of `F` in `U` is a nonzerodivisor on
every stalk of `F` over `U`**, for quasi-coherent `F` and an affine open `U` with Noetherian
coordinate ring.

If `a` kills a nonzero element of `F_x`, its germ lies in an associated prime `𝔮` of `F_x` over
the Noetherian local ring `𝒪_{X,x}` (`biUnion_associatedPrimes_eq_zero_divisors`). The
contraction of `𝔮` to `Γ(X, U)` is an associated prime of `Γ(U, F)` (Stacks 0310), so its point
is an associated point of `F` in `U`, and `a` lies in its prime: `a` is not a unit there. -/
theorem isSMulRegular_germ [IsNoetherianRing Γ(X, U)] (a : Γ(X, U))
    (ha : ∀ z ∈ associatedPoints F, z ∈ U → z ∈ X.basicOpen a) {x : X} (hx : x ∈ U) :
    IsSMulRegular ((moduleStalkFunctor X x).obj F) (X.presheaf.germ U x hx a) := by
  obtain ⟨y, rfl⟩ : ∃ y : PrimeSpectrum Γ(X, U), hU.fromSpec y = x := ⟨_, hU.fromSpec_primeIdealOf ⟨x, hx⟩⟩
  letI : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨_, hx⟩
  haveI : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) y.asIdeal :=
    hU.isLocalization_stalk' y hx
  haveI : IsNoetherianRing (X.presheaf.stalk (hU.fromSpec y)) :=
    IsLocalization.isNoetherianRing y.asIdeal.primeCompl _ inferInstance
  intro m m' hmm'
  rw [← sub_eq_zero]
  by_contra hne
  have hzd : X.presheaf.germ U _ hx a ∈ {r : X.presheaf.stalk (hU.fromSpec y) |
      ∃ n : (moduleStalkFunctor X (hU.fromSpec y)).obj F, n ≠ 0 ∧ r • n = 0} :=
    ⟨m - m', hne, by rw [smul_sub, sub_eq_zero]; exact hmm'⟩
  rw [← biUnion_associatedPrimes_eq_zero_divisors] at hzd
  obtain ⟨𝔮, h𝔮, ha𝔮⟩ := Set.mem_iUnion₂.mp hzd
  have hprime : (𝔮.comap (X.presheaf.germ U _ (fromSpec_mem hU y)).hom).IsPrime :=
    (AssociatedPrimes.mem_iff.mp h𝔮).isPrime.comap _
  let z : PrimeSpectrum Γ(X, U) := ⟨_, hprime⟩
  have hz := comap_mem_associatedPrimes F hU y 𝔮 h𝔮
    ((isNoetherianRing_iff_ideal_fg _).mp ‹_› _)
  have hzX : hU.fromSpec z ∈ X.basicOpen a :=
    ha _ (fromSpec_mem_associatedPoints_of_mem_associatedPrimes F hU z hz) (fromSpec_mem hU z)
  have hzX' : z ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen a := hzX
  rw [hU.fromSpec_preimage_basicOpen] at hzX'
  exact hzX' ha𝔮

end Affine

/-- Sections of a coherent sheaf over an affine open form a finite module over the coordinate
ring. `moduleFinite_sections_restrict_of_isCoherent` gives this for the sections of the
restriction to `Spec Γ(X, U)`, which restrict onto `Γ(U, F)` linearly. -/
private theorem moduleFinite_sections (F : X.Modules) (hF : IsCoherent X F) {U : X.Opens}
    (hU : IsAffineOpen U) : Module.Finite Γ(X, U) Γ(F, U) := by
  have := moduleFinite_sections_restrict_of_isCoherent F U hU hF
  have htop' : hU.fromSpec ''ᵁ ⊤ ≤ U :=
    (hU.fromSpec.image_le_opensRange _).trans hU.opensRange_fromSpec.le
  have htop : U ≤ hU.fromSpec ''ᵁ ⊤ :=
    ((Scheme.Hom.image_top_eq_opensRange hU.fromSpec).trans hU.opensRange_fromSpec).ge
  let L : moduleSpecΓFunctor.obj (F.restrict hU.fromSpec) →ₗ[Γ(X, U)] Γ(F, U) :=
    { toFun := fun s ↦ F.presheaf.map (homOfLE htop).op (show Γ(F, hU.fromSpec ''ᵁ ⊤) from s)
      map_add' := fun s t ↦ map_add _ _ _
      map_smul' := fun r s ↦ by
        change F.presheaf.map (homOfLE htop).op ((hU.fromSpec.appIso ⊤).inv
          ((Spec Γ(X, U)).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso Γ(X, U)).inv r)) •
            (show Γ(F, hU.fromSpec ''ᵁ ⊤) from s)) = _
        rw [hU.fromSpec_appIso_inv_ΓSpecIso, Scheme.Modules.map_smul,
          ← ConcreteCategory.comp_apply, ← Functor.map_comp]
        change X.presheaf.map (𝟙 _) r • _ = _
        rw [CategoryTheory.Functor.map_id]
        rfl }
  refine Module.Finite.of_surjective L fun t ↦ ⟨F.presheaf.map (homOfLE htop').op t, ?_⟩
  change F.presheaf.map (homOfLE htop).op (F.presheaf.map (homOfLE htop').op t) = t
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  change F.presheaf.map (𝟙 _) t = t
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- **A coherent sheaf on a locally Noetherian scheme has finitely many associated points in every
quasi-compact subset** (Stacks 05AF).

Cover the subset by finitely many affine opens. On each, the associated points are the associated
primes of the sections (`fromSpec_mem_associatedPoints_iff`), and a finite module over a
Noetherian ring has finitely many (`associatedPrimes.finite`). -/
theorem associatedPoints_inter_finite [IsLocallyNoetherian X] (F : X.Modules)
    (hF : IsCoherent X F) {S : Set X} (hS : IsCompact S) :
    (associatedPoints F ∩ S).Finite := by
  haveI : SheafOfModules.IsQuasicoherent.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from F) := by
    haveI : SheafOfModules.IsFinitePresentation.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from F) := hF
    infer_instance
  have hchart (U : X.affineOpens) : (associatedPoints F ∩ (U : Set X)).Finite := by
    have hU := U.2
    haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
    haveI := moduleFinite_sections F hF hU
    have hfin : (PrimeSpectrum.asIdeal ⁻¹' associatedPrimes Γ(X, U) Γ(F, U)).Finite :=
      (associatedPrimes.finite Γ(X, U) Γ(F, U)).preimage fun a _ b _ h ↦ PrimeSpectrum.ext h
    refine (hfin.image hU.fromSpec).subset fun x ⟨hx, hxU⟩ ↦ ⟨hU.primeIdealOf ⟨x, hxU⟩, ?_, ?_⟩
    · change (hU.primeIdealOf ⟨x, hxU⟩).asIdeal ∈ associatedPrimes Γ(X, U) Γ(F, U)
      rw [← fromSpec_mem_associatedPoints_iff F hU, hU.fromSpec_primeIdealOf ⟨x, hxU⟩]
      exact hx
    · exact hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun U : X.affineOpens ↦ (U : Set X))
    (fun U ↦ U.1.isOpen) fun x _ ↦ by
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩
  refine (t.finite_toSet.biUnion fun U _ ↦ hchart U).subset fun x ⟨hx, hxS⟩ ↦ ?_
  obtain ⟨U, hU, hxU⟩ := Set.mem_iUnion₂.mp (ht hxS)
  exact Set.mem_iUnion₂.mpr ⟨U, hU, hx, hxU⟩

/-- **A coherent sheaf on a Noetherian scheme has finitely many associated points** (Stacks
05AF, for the quasi-compact open `X`).

`IsNoetherian X` is load-bearing: on `Spec A` for `A = k[x₁, x₂, …]/(xᵢ xⱼ)_{i ≠ j}`, the
structure sheaf has the infinitely many associated points `(xⱼ)_{j ≠ i}`, one for each `i`. -/
theorem associatedPoints_finite [IsNoetherian X] (F : X.Modules) (hF : IsCoherent X F) :
    (associatedPoints F).Finite := by
  simpa using associatedPoints_inter_finite F hF isCompact_univ

end AlgebraicGeometry.Scheme.Modules
