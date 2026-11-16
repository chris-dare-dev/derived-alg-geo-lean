/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Module.Submodule.Union
import DerivedAlgGeo.AlgebraicGeometry.Modules.AssociatedPoints
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.Hyperplane
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.ProjectiveSpace
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.TwistInverse
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveSpaceProperties
import DerivedAlgGeo.AlgebraicGeometry.Variety.Projective

/-!
# Hyperplane sections avoiding the associated points of a module sheaf

Let `k` be a field, `ℙ(ι) = Proj k[ι]` with `ι` finite, and `h` a linear form whose
`X j`-coefficient is nonzero. Solving `h = 0` for `X j` is a graded surjection
`k[ι] → k[{i // i ≠ j}]` with kernel `(h)`, so the hyperplane `V₊(h)` is the closed immersion
`i : ℙ({i // i ≠ j}) ⟶ ℙ(ι)`. For a quasi-coherent `F` on `ℙ(ι)` such that `h` lies in the prime of
no associated point of `F`,

`0 ⟶ F(-1) ⟶(·h) F ⟶ i_* i^* F ⟶ 0`

is short exact. Over an infinite field a coherent `F` has such an `h`: its associated points are
finite (`Scheme.Modules.associatedPoints_finite`) and `exists_linearForm_not_mem` avoids them.
Together these are Stacks 08A0, the restriction-to-a-hyperplane step of the inductions on the
dimension of `ℙ(ι)`.

## Main definitions

* `AlgebraicGeometry.Proj.linearHyperplaneHom`: the graded surjection solving a linear form for
  one variable.
* `AlgebraicGeometry.Proj.linearHyperplane`: its `Proj`, the hyperplane `V₊(h)` as projective
  space on the other variables.
* `AlgebraicGeometry.Proj.tensorTwistNegOneTwistIso`: `F(-1)(1) ≅ F`.
* `AlgebraicGeometry.Proj.hyperplaneSequence`: the complex `F(-1) ⟶ F ⟶ i_* i^* F`.

## Main results

* `AlgebraicGeometry.Proj.ker_linearHyperplaneHom`: the kernel of `linearHyperplaneHom` is `(h)`.
* `AlgebraicGeometry.Proj.exists_linearForm_not_mem`: over an infinite field, some nonzero
  linear form avoids finitely many points.
* `AlgebraicGeometry.Proj.hyperplaneSection_shortExact`: the hyperplane sequence is short exact
  when `h` avoids the associated points of `F`.

## Implementation notes

### The hyperplane is a `Proj.map`

The hyperplane is `Proj.map` of a graded surjection rather than the closed subscheme of an ideal
sheaf. This presents `V₊(h)` directly as `ℙ({i // i ≠ j})`, and it is the setting of
`isIso_unit_of_twistBy_eq_zero` in `Hyperplane.lean`. The price is the choice of a variable `j`
with nonzero coefficient, which `hyperplaneSequence` takes as an argument.

### Exactness away from the left needs no hypothesis

Multiplication by `h` is `twistBy h : G ⟶ G(1)` on `G = F(-1)`, read through `F(-1)(1) ≅ F`. On
the chart `D₊(s)`, `s` of degree one, `twistBy s` identifies the stalks of `G` and `G(1)`
(`isLocalBasis_sectionOfMem`), and `twistBy h` is `twistBy s` scaled by the germ of `h / s`
(`twistBy_app_eq_smul'`). The stalk map of `i` kills `h / s`, so the composite with the unit
vanishes; and `h / s` kills the cokernel `H` of `twistBy h`, so `twistBy h` vanishes on `H` and its
unit `H ⟶ i_* i^* H` is an isomorphism (`isIso_unit_of_twistBy_eq_zero`). The map
`H ⟶ i_* i^* G(1)` induced by the unit is then split by `i_* i^*` of the projection, and it is
onto because the unit of a closed immersion is onto on stalks. None of this uses a hypothesis on
`F`.

### Injectivity is where the associated points enter

On `D₊(X i)` multiplication by `h` is, on stalks, multiplication by `h / X i`. The function
`h / X i` is a unit at every point of `D₊(X i)` off `V₊(h)`, in particular at every associated
point of `F` there, so it is a nonzerodivisor on every stalk of `F` over `D₊(X i)`
(`Scheme.Modules.isSMulRegular_germ`); this uses that `F` is quasi-coherent and that the chart's
ring is Noetherian, which is where `Finite ι` enters.

### Hypotheses

* `[Infinite k]` in `exists_linearForm_not_mem` is load-bearing; its docstring records the
  witness on `ℙ¹` over `𝔽₂`.
* The avoidance hypothesis of `hyperplaneSection_shortExact` is load-bearing; its docstring
  records the witness `F = i_* 𝒪_H`.
* `hyperplaneSection_shortExact` asks for quasi-coherence, not coherence. Coherence enters only
  through the finiteness of the associated points, to produce `h`.

## References

* [Stacks, Lemma 33.35.3 (Tag 08A0)](https://stacks.math.columbia.edu/tag/08A0)
* N. Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590, §2, the paragraph
  before Lemma 2.1.

## Tags

hyperplane section, associated point, projective space, twisting sheaf, closed immersion
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace GradedModule HomogeneousIdeal
open scoped ChangeOfRings TensorProduct

namespace AlgebraicGeometry.Proj

/-! ### The unit of a closed immersion on stalks -/

section ClosedImmersion

variable {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- At a point `i q`, the stalk of the unit `G ⟶ i_* i^* G` is `m ↦ 1 ⊗ m` into
`𝒪_{Z,q} ⊗ G_{i q}`, read through an injective map. -/
private theorem exists_injective_unit_stalk (G : Y.Modules) (q : Z) :
    ∃ E : (Scheme.Modules.moduleStalkFunctor Y (i.base q)).obj
        ((Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj G)) →
        (ModuleCat.extendScalars (i.stalkMap q).hom).obj
          ((Scheme.Modules.moduleStalkFunctor Y (i.base q)).obj G),
      Function.Injective E ∧ ∀ g, E ((Scheme.Modules.moduleStalkFunctor Y (i.base q)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app G) g) =
          (ModuleCat.extendRestrictScalarsAdj (i.stalkMap q).hom).unit.app
            ((Scheme.Modules.moduleStalkFunctor Y (i.base q)).obj G) g := by
  let F := (Scheme.Modules.pullback i).obj G
  let T := TopCat.Presheaf.stalkPushforward AddCommGrpCat i.base F.presheaf q
  have hT : IsIso T := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
    AddCommGrpCat i.isClosedEmbedding.isInducing F.presheaf q
  let P := (Scheme.Modules.pullbackStalkIso i q).hom.app G
  refine ⟨fun y ↦ P (T y), (ConcreteCategory.bijective_of_isIso P).1.comp
    (ConcreteCategory.bijective_of_isIso T).1, fun g ↦ ?_⟩
  obtain ⟨V, hV, s, rfl⟩ := Scheme.Modules.exists_germ_eq G _ g
  have h1 := (Scheme.Modules.germ_app
    ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app G) _ hV s).symm
  have h2 := ConcreteCategory.congr_hom
    (TopCat.Presheaf.stalkPushforward_germ AddCommGrpCat i.base F.presheaf V q hV)
    (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app G).app V s)
  rw [ConcreteCategory.comp_apply] at h2
  refine (congrArg (fun z ↦ P (T z)) h1).trans ?_
  refine (congrArg P h2).trans ?_
  exact Scheme.Modules.pullbackStalkIso_hom_app_germ_unit i q G V hV s

/-- For a surjective ring map `φ : R → S`, every element of `S ⊗[R] M` is `1 ⊗ m`. -/
private theorem extendRestrictScalarsAdj_unit_surjective {R S : Type u} [CommRing R]
    [CommRing S] (φ : R →+* S) (hφ : Function.Surjective φ) (M : ModuleCat.{u} R) :
    Function.Surjective ((ModuleCat.extendRestrictScalarsAdj φ).unit.app M) := by
  let : Module R S := Module.compHom S φ
  intro z
  change TensorProduct R S M at z
  induction z using TensorProduct.inductionOn with
  | tmul s m =>
    obtain ⟨r, rfl⟩ := hφ s
    refine ⟨r • m, ?_⟩
    rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
    change (1 : S) ⊗ₜ[R] (r • m) = φ r ⊗ₜ[R] m
    rw [← TensorProduct.smul_tmul]
    congr 1
    change φ r * 1 = φ r
    rw [mul_one]
  | add z z' hz hz' =>
    obtain ⟨m, hm⟩ := hz
    obtain ⟨m', hm'⟩ := hz'
    exact ⟨m + m', (map_add _ m m').trans (by rw [hm, hm']; rfl)⟩

/-- **The unit `G ⟶ i_* i^* G` of a closed immersion is an epimorphism**, checked on stalks: off
the image the target stalk vanishes, and at `i q` the unit is `m ↦ 1 ⊗ m` into
`𝒪_{Z,q} ⊗ G_{i q}`, onto because `𝒪_{Y,i q} → 𝒪_{Z,q}` is. -/
private theorem epi_unit_of_isClosedImmersion (G : Y.Modules) :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app G) := by
  haveI (p : Y) := Scheme.Modules.moduleStalkFunctor_preservesFiniteColimits Y p
  suffices H : ∀ p, Function.Surjective ((Scheme.Modules.moduleStalkFunctor Y p).map
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app G)) by
    haveI (p : Y) := (ModuleCat.epi_iff_surjective _).mpr (H p)
    exact (Scheme.Modules.moduleStalkFunctors_jointlyReflectIsomorphisms Y)
      |>.jointlyReflectEpimorphisms.epi _
  intro p
  by_cases hp : p ∈ Set.range i.base
  · obtain ⟨q, rfl⟩ := hp
    obtain ⟨E, hE, hEη⟩ := exists_injective_unit_stalk i G q
    intro y
    obtain ⟨g, hg⟩ := extendRestrictScalarsAdj_unit_surjective _ (i.stalkMap_surjective q) _
      (E y)
    exact ⟨g, hE ((hEη g).trans hg)⟩
  · have htgt : Subsingleton ((Scheme.Modules.moduleStalkFunctor Y p).obj
        ((Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj G))) :=
      DerivedAlgGeo.Topology.subsingleton_stalk_pushforward _
        ⟨_, ((Scheme.Modules.pullback i).obj G).isSheaf⟩ i.isClosedEmbedding.isClosed_range p hp
    exact fun y ↦ ⟨0, @Subsingleton.elim _ htgt _ _⟩

end ClosedImmersion

/-- A morphism of module sheaves whose stalk maps all vanish is zero. -/
private theorem eq_zero_of_forall_stalk {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ p m, (Scheme.Modules.moduleStalkFunctor X p).map φ m = 0) : φ = 0 := by
  ext U t
  apply Scheme.Modules.section_ext
  intro p hp
  rw [Scheme.Modules.germ_app, h]
  change 0 = Scheme.Modules.germ N p hp 0
  exact (Scheme.Modules.germ_zero N p hp).symm

/-! ### Multiplication by a linear form on stalks -/

section Twist

variable {A σA : Type u} [CommRing A] [SetLike σA A] [AddSubgroupClass σA A]
variable (𝒜 : ℕ → σA) [GradedRing 𝒜]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- At a point of `D₊(s)`, `s` of degree one, multiplication by `s` on stalks is
`m ↦ m ⊗ s` into `G_p ⊗ 𝒪(1)_p`. -/
private theorem twistBy_stalk_eq_tmul {s : A} (hs : s ∈ 𝒜 1) (G : (Proj 𝒜).Modules)
    {p : Proj 𝒜} (hp : p ∈ ProjectiveSpectrum.basicOpen 𝒜 s)
    (m : (Scheme.Modules.moduleStalkFunctor (Proj 𝒜) p).obj G) :
    (Scheme.Modules.moduleStalkFunctor (Proj 𝒜) p).map (twistBy 𝒜 1 hs G) m =
      (Scheme.Modules.fixedLeftTensorStalkIso (Proj 𝒜) p G).hom.app
        (twistingSheaf 𝒜 ((1 : ℕ) : ℤ))
        (m ⊗ₜ Scheme.Modules.germ (twistingSheaf 𝒜 ((1 : ℕ) : ℤ)) p hp
          (sectionOfMem 𝒜 𝒜 (ProjectiveSpectrum.basicOpen 𝒜 s) 1 hs)) := by
  obtain ⟨W, hpW, t, rfl⟩ := Scheme.Modules.exists_germ_eq G p m
  have hpV : p ∈ ProjectiveSpectrum.basicOpen 𝒜 s ⊓ W := ⟨hp, hpW⟩
  have hVs : ProjectiveSpectrum.basicOpen 𝒜 s ⊓ W ≤ ProjectiveSpectrum.basicOpen 𝒜 s :=
    inf_le_left
  have hVW : ProjectiveSpectrum.basicOpen 𝒜 s ⊓ W ≤ W := inf_le_right
  have h1 := Scheme.Modules.germ_res G hVW p hpV t
  have h2 : Scheme.Modules.germ (twistingSheaf 𝒜 ((1 : ℕ) : ℤ)) p hpV
      (sectionOfMem 𝒜 𝒜 (ProjectiveSpectrum.basicOpen 𝒜 s ⊓ W) 1 hs) =
        Scheme.Modules.germ (twistingSheaf 𝒜 ((1 : ℕ) : ℤ)) p hp
          (sectionOfMem 𝒜 𝒜 (ProjectiveSpectrum.basicOpen 𝒜 s) 1 hs) := by
    rw [← Scheme.Modules.germ_res _ hVs p hpV]
    exact congrArg _ (res_sectionOfMem 𝒜 𝒜 hVs 1 hs).symm
  rw [← h1, ← h2, Scheme.Modules.fixedLeftTensorStalkIso_hom_app_germ_tmul,
    ← Scheme.Modules.germ_app]
  exact congrArg _ (twistBy_app 𝒜 1 hs G _ _)

/-- **At a point of `D₊(s)`, `s` of degree one, multiplication by `s` identifies `G_p` with
`(G ⊗ 𝒪(1))_p`**: `s` freely generates `𝒪(1)` there (`isLocalBasis_sectionOfMem`). -/
private theorem twistBy_stalk_bijective {s : A} (hs : s ∈ 𝒜 1) (G : (Proj 𝒜).Modules)
    {p : Proj 𝒜} (hp : p ∈ ProjectiveSpectrum.basicOpen 𝒜 s) :
    Function.Bijective
      ((Scheme.Modules.moduleStalkFunctor (Proj 𝒜) p).map (twistBy 𝒜 1 hs G)) := by
  have he := (isLocalBasis_sectionOfMem 𝒜 hs).bijective_stalk hp
  let E := LinearEquiv.ofBijective _ he
  let e := Scheme.Modules.germ (twistingSheaf 𝒜 ((1 : ℕ) : ℤ)) p hp
    (sectionOfMem 𝒜 𝒜 (ProjectiveSpectrum.basicOpen 𝒜 s) 1 hs)
  let L := (TensorProduct.rid ((Proj 𝒜).presheaf.stalk p)
      ((Scheme.Modules.moduleStalkFunctor (Proj 𝒜) p).obj G)).symm ≪≫ₗ
    TensorProduct.congr (LinearEquiv.refl _ _) E
  have hL (m) : L m = m ⊗ₜ e := by
    simp [L, E, e, LinearMap.toSpanSingleton_apply]
  have hcomp : ⇑((Scheme.Modules.moduleStalkFunctor (Proj 𝒜) p).map (twistBy 𝒜 1 hs G)) =
      ⇑((Scheme.Modules.fixedLeftTensorStalkIso (Proj 𝒜) p G).hom.app
        (twistingSheaf 𝒜 ((1 : ℕ) : ℤ))) ∘ ⇑L := by
    funext m
    rw [Function.comp_apply, hL]
    exact twistBy_stalk_eq_tmul 𝒜 hs G hp m
  rw [hcomp]
  exact (ConcreteCategory.bijective_of_isIso _).comp L.bijective

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- **On stalks over `D₊(s)`, multiplication by `x` is multiplication by `s` scaled by the germ
of `x / s`**, for `x`, `s` of degree one (`twistBy_app_eq_smul'`). -/
private theorem twistBy_stalk_eq_smul {x s : A} (hx : x ∈ 𝒜 1) (hs : s ∈ 𝒜 1)
    (G : (Proj 𝒜).Modules) {p : Proj 𝒜} (hp : p ∈ ProjectiveSpectrum.basicOpen 𝒜 s)
    (m : (Scheme.Modules.moduleStalkFunctor (Proj 𝒜) p).obj G) :
    (Scheme.Modules.moduleStalkFunctor (Proj 𝒜) p).map (twistBy 𝒜 1 hx G) m =
      (Proj 𝒜).presheaf.germ (ProjectiveSpectrum.basicOpen 𝒜 s) p hp
          (fracSection 𝒜 hx hs le_rfl) •
        (Scheme.Modules.moduleStalkFunctor (Proj 𝒜) p).map (twistBy 𝒜 1 hs G) m := by
  obtain ⟨W, hpW, t, rfl⟩ := Scheme.Modules.exists_germ_eq G p m
  have hpV : p ∈ ProjectiveSpectrum.basicOpen 𝒜 s ⊓ W := ⟨hp, hpW⟩
  have hVs : ProjectiveSpectrum.basicOpen 𝒜 s ⊓ W ≤ ProjectiveSpectrum.basicOpen 𝒜 s :=
    inf_le_left
  have hVW : ProjectiveSpectrum.basicOpen 𝒜 s ⊓ W ≤ W := inf_le_right
  rw [← Scheme.Modules.germ_res G hVW p hpV t]
  set t' := G.presheaf.map (homOfLE hVW).op t
  calc (Scheme.Modules.moduleStalkFunctor (Proj 𝒜) p).map (twistBy 𝒜 1 hx G)
        (Scheme.Modules.germ G p hpV t')
      = Scheme.Modules.germ _ p hpV ((twistBy 𝒜 1 hx G).app _ t') :=
        (Scheme.Modules.germ_app _ p hpV t').symm
    _ = Scheme.Modules.germ _ p hpV
          ((show Γ(Proj 𝒜, ProjectiveSpectrum.basicOpen 𝒜 s ⊓ W) from
            fracSection 𝒜 hx hs hVs) • (twistBy 𝒜 1 hs G).app _ t') :=
        congrArg _ (twistBy_app_eq_smul' 𝒜 hx hs G hVs t')
    _ = (Proj 𝒜).presheaf.germ _ p hpV (fracSection 𝒜 hx hs hVs) •
          Scheme.Modules.germ _ p hpV ((twistBy 𝒜 1 hs G).app _ t') :=
        Scheme.Modules.germ_smul _ p hpV _ _
    _ = _ := by
        rw [Scheme.Modules.germ_app]
        congr 1
        exact TopCat.Presheaf.germ_res_apply (Proj 𝒜).presheaf (homOfLE hVs) p hpV
          (fracSection 𝒜 hx hs le_rfl)

end Twist

/-! ### The hyperplane section of a module sheaf -/

section Hyperplane

open HomogeneousLocalization

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] [CommRing B]
  [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (ψ : 𝒜 →+*ᵍ ℬ) (hψ : Function.Surjective ψ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The germ of `x / s` is killed by the stalk map of `Proj.map ψ` when `ψ x = 0`. -/
private theorem stalkMap_germ_fracSection_eq_zero (h : ℬ₊ ≤ 𝒜₊.map ψ) {x s : A}
    (hx : x ∈ 𝒜 1) (hs : s ∈ 𝒜 1) (hψx : ψ x = 0) (q : Proj ℬ)
    (hp : (map ψ h).base q ∈ ProjectiveSpectrum.basicOpen 𝒜 s) :
    (map ψ h).stalkMap q ((Proj 𝒜).presheaf.germ (ProjectiveSpectrum.basicOpen 𝒜 s) _ hp
      (fracSection 𝒜 hx hs le_rfl)) = 0 := by
  set r := (Proj 𝒜).presheaf.germ (ProjectiveSpectrum.basicOpen 𝒜 s) _ hp
    (fracSection 𝒜 hx hs le_rfl)
  have hr : (stalkIso 𝒜 ((map ψ h).base q)).hom r = frac 𝒜 hx hs hp :=
    Proj.stalkIso'_germ 𝒜 _ _ hp (fracSection 𝒜 hx hs le_rfl)
  have hloc : localRingHom ψ _ _ rfl ((stalkIso 𝒜 ((map ψ h).base q)).hom r) = 0 := by
    rw [hr]
    apply val_injective
    rw [val_localRingHom, frac, val_mk, val_zero]
    erw [Localization.localRingHom_mk]
    simp [hψx, Localization.mk_zero]
  have h1 := localRingHom_comp_stalkIso_apply ψ h q r
  calc (map ψ h).stalkMap q r = (sheafedSpaceMap ψ h).hom.stalkMap q r := rfl
    _ = _ := h1.symm
    _ = 0 := (congrArg (fun z ↦ (stalkIso ℬ q).inv z) hloc).trans (map_zero _)

include hψ in
/-- **Multiplication by `x` followed by the unit `G(1) ⟶ i_* i^* G(1)` is zero**, for
`i = Proj.map ψ` and `ψ x = 0`, when every point of `Proj 𝒜` lies in some `D₊(s)` with `s` of
degree one. On stalks at `i q`, multiplication by `x` is multiplication by `x / s` (up to the
isomorphism `twistBy s`), and the stalk map of `i` kills `x / s`. -/
private theorem twistBy_comp_unit_eq_zero {x : A} (hx : x ∈ 𝒜 1) (hψx : ψ x = 0)
    (hcov : ∀ p : Proj 𝒜, ∃ s ∈ 𝒜 1, p ∈ ProjectiveSpectrum.basicOpen 𝒜 s)
    (G : (Proj 𝒜).Modules) :
    twistBy 𝒜 1 hx G ≫ (Scheme.Modules.pullbackPushforwardAdjunction
      (map ψ (irrelevant_le_map_of_surjective ψ hψ))).unit.app
        (Scheme.Modules.tensorObj G (twistingSheaf 𝒜 ((1 : ℕ) : ℤ))) = 0 := by
  have := isClosedImmersion_map ψ hψ
  set i := map ψ (irrelevant_le_map_of_surjective ψ hψ)
  apply eq_zero_of_forall_stalk
  intro p m
  rw [CategoryTheory.Functor.map_comp, ConcreteCategory.comp_apply]
  by_cases hp : p ∈ Set.range i.base
  · obtain ⟨q, rfl⟩ := hp
    obtain ⟨s, hs, hps⟩ := hcov (i.base q)
    obtain ⟨E, hE, hEη⟩ := exists_injective_unit_stalk i
      (Scheme.Modules.tensorObj G (twistingSheaf 𝒜 ((1 : ℕ) : ℤ))) q
    have key : E ((Scheme.Modules.moduleStalkFunctor (Proj 𝒜) (i.base q)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
          (Scheme.Modules.tensorObj G (twistingSheaf 𝒜 ((1 : ℕ) : ℤ))))
        ((Scheme.Modules.moduleStalkFunctor (Proj 𝒜) (i.base q)).map (twistBy 𝒜 1 hx G) m)) =
        E ((Scheme.Modules.moduleStalkFunctor (Proj 𝒜) (i.base q)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
            (Scheme.Modules.tensorObj G (twistingSheaf 𝒜 ((1 : ℕ) : ℤ)))) 0) := by
      rw [hEη, hEη, twistBy_stalk_eq_smul 𝒜 hx hs G hps m, map_smul, map_zero]
      refine (ModuleCat.restrictScalars.smul_def _ _ _).trans ?_
      have h0 := stalkMap_germ_fracSection_eq_zero ψ _ hx hs hψx q hps
      exact (congrArg (· • _) h0).trans (zero_smul _ _)
    rw [hE key, map_zero]
  · have htgt : Subsingleton ((Scheme.Modules.moduleStalkFunctor (Proj 𝒜) p).obj
        ((Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj
          (Scheme.Modules.tensorObj G (twistingSheaf 𝒜 ((1 : ℕ) : ℤ)))))) :=
      DerivedAlgGeo.Topology.subsingleton_stalk_pushforward _
        ⟨_, ((Scheme.Modules.pullback i).obj
          (Scheme.Modules.tensorObj G (twistingSheaf 𝒜 ((1 : ℕ) : ℤ)))).isSheaf⟩
        i.isClosedEmbedding.isClosed_range p hp
    exact @Subsingleton.elim _ htgt _ _

/-- **Multiplication by `x` vanishes on the cokernel of multiplication by `x`**, when every point
lies in some `D₊(s)` with `s` of degree one: on stalks over `D₊(s)` every element of `G(1)_p` is
`s` times one of `G_p`, and `x / s` times it is `x` times that one. -/
private theorem twistBy_cokernel_eq_zero {x : A} (hx : x ∈ 𝒜 1)
    (hcov : ∀ p : Proj 𝒜, ∃ s ∈ 𝒜 1, p ∈ ProjectiveSpectrum.basicOpen 𝒜 s)
    (G : (Proj 𝒜).Modules) :
    twistBy 𝒜 1 hx (cokernel (twistBy 𝒜 1 hx G)) = 0 := by
  haveI (p : Proj 𝒜) := Scheme.Modules.moduleStalkFunctor_preservesFiniteColimits (Proj 𝒜) p
  apply eq_zero_of_forall_stalk
  intro p n
  obtain ⟨s, hs, hps⟩ := hcov p
  rw [twistBy_stalk_eq_smul 𝒜 hx hs _ hps n, ← map_smul]
  suffices H : (Proj 𝒜).presheaf.germ (ProjectiveSpectrum.basicOpen 𝒜 s) p hps
      (fracSection 𝒜 hx hs le_rfl) • n = 0 by
    rw [H, map_zero]
  have hπ : Function.Surjective
      ((Scheme.Modules.moduleStalkFunctor (Proj 𝒜) p).map (cokernel.π (twistBy 𝒜 1 hx G))) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨m, rfl⟩ := hπ n
  obtain ⟨m', rfl⟩ := (twistBy_stalk_bijective 𝒜 hs G hps).2 m
  rw [← map_smul, ← twistBy_stalk_eq_smul 𝒜 hx hs G hps m', ← ConcreteCategory.comp_apply,
    ← CategoryTheory.Functor.map_comp, cokernel.condition, CategoryTheory.Functor.map_zero]
  rfl

include hψ in
/-- **The hyperplane sequence `G ⟶ G(1) ⟶ i_* i^* G(1)` is short exact once multiplication by `x`
is a monomorphism**, for `i = Proj.map ψ` the closed immersion of `V₊(x)`, `ψ` a surjective graded
map with kernel `(x)`, and every point lying in some `D₊(s)` with `s` of degree one.

The cokernel `H` of multiplication by `x` is killed by `x` (`twistBy_cokernel_eq_zero`), so its
unit `H ⟶ i_* i^* H` is an isomorphism (`isIso_unit_of_twistBy_eq_zero`). The map
`H ⟶ i_* i^* G(1)` induced by the unit of `G(1)` is then split by `i_* i^*` of the projection,
hence mono, and it is epi because the unit of a closed immersion is. -/
private theorem shortExact_twistBy_unit {x : A} (hx : x ∈ 𝒜 1)
    (hker : RingHom.ker (ψ : A →+* B) = Ideal.span {x})
    (hcov : ∀ p : Proj 𝒜, ∃ s ∈ 𝒜 1, p ∈ ProjectiveSpectrum.basicOpen 𝒜 s)
    (G : (Proj 𝒜).Modules) [Mono (twistBy 𝒜 1 hx G)] :
    (ShortComplex.mk (twistBy 𝒜 1 hx G) ((Scheme.Modules.pullbackPushforwardAdjunction
      (map ψ (irrelevant_le_map_of_surjective ψ hψ))).unit.app
        (Scheme.Modules.tensorObj G (twistingSheaf 𝒜 ((1 : ℕ) : ℤ))))
      (twistBy_comp_unit_eq_zero ψ hψ hx (RingHom.mem_ker.mp
        (hker ▸ Ideal.mem_span_singleton_self x : x ∈ RingHom.ker (ψ : A →+* B))) hcov G)).ShortExact := by
  have := isClosedImmersion_map ψ hψ
  set i := map ψ (irrelevant_le_map_of_surjective ψ hψ)
  set adj := Scheme.Modules.pullbackPushforwardAdjunction i
  set τ := twistBy 𝒜 1 hx G
  have hzero : τ ≫ adj.unit.app (Scheme.Modules.tensorObj G (twistingSheaf 𝒜 ((1 : ℕ) : ℤ))) =
      0 := twistBy_comp_unit_eq_zero ψ hψ hx (RingHom.mem_ker.mp
        (hker ▸ Ideal.mem_span_singleton_self x : x ∈ RingHom.ker (ψ : A →+* B))) hcov G
  haveI : IsIso (adj.unit.app (cokernel τ)) :=
    isIso_unit_of_twistBy_eq_zero ψ hψ hx hker _ (twistBy_cokernel_eq_zero hx hcov G)
  haveI := epi_unit_of_isClosedImmersion i
    (Scheme.Modules.tensorObj G (twistingSheaf 𝒜 ((1 : ℕ) : ℤ)))
  let φ := cokernel.desc τ _ hzero
  have hφ₁ : cokernel.π τ ≫ φ =
      adj.unit.app (Scheme.Modules.tensorObj G (twistingSheaf 𝒜 ((1 : ℕ) : ℤ))) :=
    cokernel.π_desc _ _ _
  have hφ₂ : φ ≫ (Scheme.Modules.pullback i ⋙ Scheme.Modules.pushforward i).map
      (cokernel.π τ) = adj.unit.app (cokernel τ) := by
    rw [← cancel_epi (cokernel.π τ), reassoc_of% hφ₁]
    exact (adj.unit.naturality (cokernel.π τ)).symm
  haveI : Mono φ := by
    have : Mono (φ ≫ (Scheme.Modules.pullback i ⋙ Scheme.Modules.pushforward i).map
        (cokernel.π τ)) := by rw [hφ₂]; infer_instance
    exact mono_of_mono φ ((Scheme.Modules.pullback i ⋙ Scheme.Modules.pushforward i).map
      (cokernel.π τ))
  haveI : Epi φ := epi_of_epi_fac hφ₁
  haveI : IsIso φ := isIso_of_mono_of_epi φ
  refine ShortComplex.shortExact_of_iso
    (S₁ := ShortComplex.mk τ (cokernel.π τ) (cokernel.condition τ))
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (asIso φ)
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl)
      (by simp only [Iso.refl_hom, Category.id_comp, asIso_hom]; exact hφ₁.symm)) ?_
  exact { exact := ShortComplex.exact_cokernel τ }

end Hyperplane

/-! ### The hyperplane of a linear form -/

section LinearForm

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {ι k : Type u} [Field k]

/-- A linear form is the sum of its coefficients times the variables. -/
private theorem eq_sum_coeff_smul_X [Fintype ι] {h : MvPolynomial ι k}
    (hh : h ∈ homogeneousSubmodule ι k 1) :
    h = ∑ i, h.coeff (Finsupp.single i 1) • X i := by
  classical
  rw [homogeneousSubmodule_one_eq_span_X, Submodule.mem_span_range_iff_exists_fun] at hh
  obtain ⟨a, rfl⟩ := hh
  refine Finset.sum_congr rfl fun i _ ↦ congrArg (· • X i) ?_
  simp [coeff_X, Finsupp.single_left_inj]

open Classical in
/-- `X i ↦ X i` for `i ≠ j` and `X j ↦ 0`, into the polynomial ring on the other variables. -/
def dropVariable (j : ι) (i : ι) : MvPolynomial {i // i ≠ j} k :=
  if hi : i = j then 0 else X ⟨i, hi⟩

theorem dropVariable_of_ne {j i : ι} (hi : i ≠ j) :
    dropVariable (k := k) j i = X ⟨i, hi⟩ := by
  simp [dropVariable, hi]

theorem dropVariable_self (j : ι) : dropVariable (k := k) j j = 0 := by
  simp [dropVariable]

open Classical in
/-- The substitution solving a linear form `h` for the variable `X j`: `X i ↦ X i` for `i ≠ j`,
and `X j ↦ -(c j)⁻¹ ∑_{i ≠ j} c i X i`, where `c i` is the coefficient of `X i` in `h`. The sum
is `h` with `X j` set to zero. -/
def linearHyperplaneSubst (h : MvPolynomial ι k) (j : ι) (i : ι) :
    MvPolynomial {i // i ≠ j} k :=
  if i = j then -(h.coeff (Finsupp.single j 1))⁻¹ • aeval (dropVariable j) h
  else dropVariable j i

theorem linearHyperplaneSubst_of_ne (h : MvPolynomial ι k) {j i : ι} (hi : i ≠ j) :
    linearHyperplaneSubst h j i = X ⟨i, hi⟩ := by
  simp [linearHyperplaneSubst, hi, dropVariable_of_ne hi]

theorem linearHyperplaneSubst_self (h : MvPolynomial ι k) (j : ι) :
    linearHyperplaneSubst h j j = -(h.coeff (Finsupp.single j 1))⁻¹ • aeval (dropVariable j) h := by
  simp [linearHyperplaneSubst]

/-- **The graded surjection `k[ι] → k[{i // i ≠ j}]` solving a linear form `h` for `X j`.** For
`h` with nonzero `X j`-coefficient its kernel is `(h)` (`ker_linearHyperplaneHom`), so its `Proj`
is the hyperplane `V₊(h)`, presented as projective space on the other variables. -/
def linearHyperplaneHom {h : MvPolynomial ι k} (hh : h ∈ homogeneousSubmodule ι k 1) (j : ι) :
    polynomialGrading ι k →+*ᵍ polynomialGrading {i // i ≠ j} k where
  toRingHom := (aeval (linearHyperplaneSubst h j)).toRingHom
  map_mem {n p} hp := by
    have hdrop (i : ι) : (dropVariable (k := k) j i).IsHomogeneous 1 := by
      by_cases hi : i = j
      · rw [hi, dropVariable_self]; exact isHomogeneous_zero _ _ _
      · rw [dropVariable_of_ne hi]; exact isHomogeneous_X _ _
    have hσ (i : ι) : (linearHyperplaneSubst h j i).IsHomogeneous 1 := by
      by_cases hi : i = j
      · rw [hi, linearHyperplaneSubst_self]
        have h0 := ((mem_homogeneousSubmodule _ _).mp hh).aeval (dropVariable j) (n := 1) hdrop
        rw [one_mul] at h0
        exact (mem_homogeneousSubmodule _ _).mp
          (Submodule.smul_mem _ _ ((mem_homogeneousSubmodule _ _).mpr h0))
      · rw [linearHyperplaneSubst_of_ne h hi]; exact isHomogeneous_X _ _
    have := hp.aeval (linearHyperplaneSubst h j) (n := 1) hσ
    simpa using this

theorem linearHyperplaneHom_apply {h : MvPolynomial ι k} (hh : h ∈ homogeneousSubmodule ι k 1)
    (j : ι) (p : MvPolynomial ι k) :
    linearHyperplaneHom hh j p = aeval (linearHyperplaneSubst h j) p :=
  rfl

/-- `linearHyperplaneHom` is surjective: `rename Subtype.val` is a section of it. -/
theorem linearHyperplaneHom_surjective {h : MvPolynomial ι k}
    (hh : h ∈ homogeneousSubmodule ι k 1) (j : ι) :
    Function.Surjective (linearHyperplaneHom hh j) := by
  intro p
  refine ⟨rename Subtype.val p, ?_⟩
  rw [linearHyperplaneHom_apply, aeval_rename,
    show linearHyperplaneSubst h j ∘ Subtype.val = X from
      funext fun i ↦ linearHyperplaneSubst_of_ne h i.2, aeval_X_left_apply]

/-- The linear form `h` itself is killed by solving it for `X j`. -/
theorem linearHyperplaneHom_self [Finite ι] {h : MvPolynomial ι k}
    (hh : h ∈ homogeneousSubmodule ι k 1) {j : ι} (hj : h.coeff (Finsupp.single j 1) ≠ 0) :
    linearHyperplaneHom hh j h = 0 := by
  classical
  cases nonempty_fintype ι
  have hsum := eq_sum_coeff_smul_X hh
  have hdrop : aeval (dropVariable (k := k) j) h =
      ∑ i : {i // i ≠ j}, h.coeff (Finsupp.single i.1 1) • X i := by
    have e : aeval (dropVariable (k := k) j) (∑ i, h.coeff (Finsupp.single i 1) • (X i : MvPolynomial ι k)) =
        ∑ i, h.coeff (Finsupp.single i 1) • dropVariable j i := by
      simp only [map_sum, map_smul, aeval_X]
    rw [← hsum] at e
    rw [e, Fintype.sum_eq_add_sum_subtype_ne _ j, dropVariable_self, smul_zero, zero_add]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [dropVariable_of_ne i.2]
  have e : aeval (linearHyperplaneSubst h j) (∑ i, h.coeff (Finsupp.single i 1) • (X i : MvPolynomial ι k)) =
      ∑ i, h.coeff (Finsupp.single i 1) • linearHyperplaneSubst h j i := by
    simp only [map_sum, map_smul, aeval_X]
  rw [← hsum] at e
  rw [linearHyperplaneHom_apply, e, Fintype.sum_eq_add_sum_subtype_ne _ j,
    linearHyperplaneSubst_self, hdrop, smul_smul, mul_neg, mul_inv_cancel₀ hj, neg_one_smul,
    neg_add_eq_zero]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [linearHyperplaneSubst_of_ne h i.2]

/-- **The kernel of `linearHyperplaneHom` is `(h)`**, for `h` with nonzero `X j`-coefficient.
Substituting back, `rename Subtype.val ∘ linearHyperplaneHom` fixes every `X i` modulo `h`:
it moves `X j` by `-(c j)⁻¹ h`. -/
theorem ker_linearHyperplaneHom [Finite ι] {h : MvPolynomial ι k}
    (hh : h ∈ homogeneousSubmodule ι k 1) {j : ι} (hj : h.coeff (Finsupp.single j 1) ≠ 0) :
    RingHom.ker (linearHyperplaneHom hh j : MvPolynomial ι k →+* MvPolynomial {i // i ≠ j} k) =
      Ideal.span {h} := by
  classical
  cases nonempty_fintype ι
  refine le_antisymm (fun p hp ↦ ?_) ((Ideal.span_le).mpr (Set.singleton_subset_iff.mpr ?_))
  · let I := Ideal.span {h}
    let τ : MvPolynomial ι k →ₐ[k] MvPolynomial ι k :=
      (rename Subtype.val).comp (aeval (linearHyperplaneSubst h j))
    have hτ : (Ideal.Quotient.mkₐ k I).comp τ = Ideal.Quotient.mkₐ k I := by
      refine MvPolynomial.algHom_ext fun i ↦ ?_
      by_cases hi : i = j
      · subst hi
        simp only [AlgHom.comp_apply, τ, aeval_X, Ideal.Quotient.mkₐ_eq_mk]
        rw [linearHyperplaneSubst_self, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
        have hsum := eq_sum_coeff_smul_X hh
        have hren : rename Subtype.val (aeval (dropVariable (k := k) i) h) = h -
            h.coeff (Finsupp.single i 1) • X i := by
          have e : rename Subtype.val (aeval (dropVariable (k := k) i)
              (∑ i, h.coeff (Finsupp.single i 1) • (X i : MvPolynomial ι k))) =
              ∑ i', h.coeff (Finsupp.single i' 1) • rename Subtype.val (dropVariable (k := k) i i') := by
            simp only [map_sum, map_smul, aeval_X]
          rw [← hsum] at e
          rw [e, eq_sub_iff_add_eq]
          conv_rhs => rw [hsum]
          rw [Fintype.sum_eq_add_sum_subtype_ne _ i, Fintype.sum_eq_add_sum_subtype_ne _ i,
            dropVariable_self, map_zero, smul_zero, zero_add]
          refine (add_comm _ _).trans (congrArg _ ?_)
          exact Finset.sum_congr rfl fun i' _ ↦ by rw [dropVariable_of_ne i'.2, rename_X]
        have h1 : -(h.coeff (Finsupp.single i 1))⁻¹ • (h - h.coeff (Finsupp.single i 1) • X i) -
            X i = C (-(h.coeff (Finsupp.single i 1))⁻¹) * h := by
          rw [smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ hj, neg_one_smul, sub_neg_eq_add,
            add_sub_cancel_right, smul_eq_C_mul]
        rw [map_smul, hren, h1]
        exact I.mul_mem_left _ (Ideal.subset_span rfl)
      · simp only [AlgHom.comp_apply, τ, aeval_X, linearHyperplaneSubst_of_ne h hi, rename_X]
    have hp' : linearHyperplaneHom hh j p = 0 := hp
    rw [linearHyperplaneHom_apply] at hp'
    have := congrArg (fun q ↦ q p) hτ
    simp only [AlgHom.comp_apply, τ, hp', map_zero] at this
    exact (Ideal.Quotient.eq_zero_iff_mem).mp (by simpa using this.symm)
  · exact linearHyperplaneHom_self hh hj

/-- **The hyperplane `V₊(h)` of a linear form `h`**, presented as projective space on the variables
other than `j`, for `h` with nonzero `X j`-coefficient (`ker_linearHyperplaneHom`). -/
def linearHyperplane {h : MvPolynomial ι k} (hh : h ∈ homogeneousSubmodule ι k 1) (j : ι) :
    projectiveSpace {i // i ≠ j} k ⟶ projectiveSpace ι k :=
  map (linearHyperplaneHom hh j)
    (irrelevant_le_map_of_surjective _ (linearHyperplaneHom_surjective hh j))

/-- The hyperplane of a linear form is a closed immersion. -/
instance {h : MvPolynomial ι k} (hh : h ∈ homogeneousSubmodule ι k 1) (j : ι) :
    IsClosedImmersion (linearHyperplane hh j) :=
  isClosedImmersion_map _ (linearHyperplaneHom_surjective hh j)

end LinearForm

/-! ### Projective space over a field -/

section ProjectiveSpace

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {ι k : Type u} [Field k]

/-- Every point of `ℙ(ι)` lies in a standard chart `D₊(X i)`. -/
private theorem exists_mem_basicOpen_X (p : projectiveSpace ι k) :
    ∃ i, p ∈ ProjectiveSpectrum.basicOpen (homogeneousSubmodule ι k) (X i) := by
  have hp : p ∈ ⨆ i : ι, ProjectiveSpectrum.basicOpen (polynomialGrading ι k) (X i) := by
    rw [polynomialVariableBasicOpen_cover]; trivial
  exact TopologicalSpace.Opens.mem_iSup.mp hp

/-- Every point of `ℙ(ι)` lies in `D₊(s)` for some `s` of degree one. -/
private theorem exists_mem_basicOpen_one (p : projectiveSpace ι k) :
    ∃ s ∈ homogeneousSubmodule ι k 1, p ∈ ProjectiveSpectrum.basicOpen (homogeneousSubmodule ι k) s :=
  let ⟨i, hi⟩ := exists_mem_basicOpen_X p
  ⟨X i, isHomogeneous_X k i, hi⟩

/-- **Over an infinite field some nonzero linear form avoids finitely many points of `ℙ(ι)`**:
it lies in none of their homogeneous primes.

The linear forms in the prime of a point form a proper subspace of the forms of degree one,
since some variable `X i` is not in it, and over an infinite field a finite union of proper
subspaces is not the whole space (`Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt`).

`[Infinite k]` is load-bearing: over `𝔽₂` on `ℙ¹`, the three rational points
`(1 : 0)`, `(0 : 1)` and `(1 : 1)` have the primes `(X₁)`, `(X₀)` and `(X₀ + X₁)`, which between them
contain the three nonzero linear forms `X₀`, `X₁`, `X₀ + X₁`. `[Nonempty ι]` excludes the empty
projective space, where the only linear form is `0`. -/
theorem exists_linearForm_not_mem [Infinite k] [Nonempty ι] (Z : Finset (projectiveSpace ι k)) :
    ∃ h ∈ homogeneousSubmodule ι k 1, h ≠ 0 ∧ ∀ z ∈ Z, h ∉ z.asHomogeneousIdeal := by
  classical
  let V := homogeneousSubmodule ι k 1
  let P : Option (projectiveSpace ι k) → Submodule k V
    | none => ⊥
    | some z => (z.asHomogeneousIdeal.toIdeal.restrictScalars k).comap V.subtype
  have hP (o : Option (projectiveSpace ι k)) : P o ≠ ⊤ := by
    intro htop
    cases o with
    | none =>
      obtain ⟨i⟩ := ‹Nonempty ι›
      have hXi : (⟨X i, isHomogeneous_X k i⟩ : V) ∈ P none := htop ▸ Submodule.mem_top
      exact X_ne_zero i (congrArg Subtype.val ((Submodule.mem_bot k).mp hXi))
    | some z =>
      obtain ⟨i, hi⟩ := exists_mem_basicOpen_X z
      have hXi : (⟨X i, isHomogeneous_X k i⟩ : V) ∈ P (some z) := htop ▸ Submodule.mem_top
      exact hi hXi
  obtain ⟨v, -, hv⟩ := Set.exists_of_ssubset
    (Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt
      (insert none (Z.map Function.Embedding.some)) P hP (by simp [ENat.card_eq_top_of_infinite]))
  refine ⟨v.1, v.2, fun h0 ↦ hv ?_, fun z hz hvz ↦ hv ?_⟩
  · refine Set.mem_iUnion₂.mpr ⟨none, Finset.mem_insert_self _ _, ?_⟩
    exact (Submodule.mem_bot k).mpr (Subtype.ext h0)
  · refine Set.mem_iUnion₂.mpr ⟨some z, Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ hz), ?_⟩
    exact hvz

/-- **`F(-1)(1) ≅ F`** on `ℙ(ι)`: the associator, `𝒪(-1) ⊗ 𝒪(1) ≅ 𝒪`, and the right unitor
(`tensorTwistNegIso`). -/
def tensorTwistNegOneTwistIso (F : (projectiveSpace ι k).Modules) :
    Scheme.Modules.tensorObj (tensorTwist (homogeneousSubmodule ι k) F (-1))
      (twistingSheaf (homogeneousSubmodule ι k) ((1 : ℕ) : ℤ)) ≅ F :=
  Scheme.Modules.tensorObjIso (Iso.refl _) (eqToIso (congrArg _ (by norm_num))) ≪≫
    tensorTwistNegIso (homogeneousSubmodule ι k) (fun i : ι ↦ ⟨X i, isHomogeneous_X k i⟩)
      (polynomialVariable_adjoin_eq_top ι k) F (-1)

/-- Multiplication by a linear form `h` on `F(-1)` is a monomorphism when no associated point of
`F` lies on `V₊(h)`. On the chart `D₊(X i)` it is multiplication by `h / X i` on stalks, which
`F(-1)(1) ≅ F` turns into multiplication on the stalks of `F`, and that is injective by
`Scheme.Modules.isSMulRegular_germ`. -/
private theorem mono_twistBy_tensorTwist [Finite ι] (F : (projectiveSpace ι k).Modules)
    [F.IsQuasicoherent] {h : MvPolynomial ι k} (hh : h ∈ homogeneousSubmodule ι k 1)
    (hass : ∀ z ∈ Scheme.Modules.associatedPoints F, h ∉ z.asHomogeneousIdeal) :
    Mono (twistBy (homogeneousSubmodule ι k) 1 hh
      (tensorTwist (homogeneousSubmodule ι k) F (-1))) := by
  haveI (p : projectiveSpace ι k) :=
    Scheme.Modules.moduleStalkFunctor_preservesFiniteLimits (projectiveSpace ι k) p
  suffices H : ∀ p, Function.Injective ((Scheme.Modules.moduleStalkFunctor _ p).map
      (twistBy (homogeneousSubmodule ι k) 1 hh (tensorTwist (homogeneousSubmodule ι k) F (-1)))) by
    haveI (p : projectiveSpace ι k) := (ModuleCat.mono_iff_injective _).mpr (H p)
    exact (Scheme.Modules.moduleStalkFunctors_jointlyReflectIsomorphisms _)
      |>.jointlyReflectMonomorphisms.mono _
  intro p
  obtain ⟨i, hpi⟩ := exists_mem_basicOpen_X p
  have hXi : (X i : MvPolynomial ι k) ∈ homogeneousSubmodule ι k 1 := isHomogeneous_X k i
  let G := tensorTwist (homogeneousSubmodule ι k) F (-1)
  let e := (Scheme.Modules.moduleStalkFunctor _ p).mapIso (tensorTwistNegOneTwistIso F)
  have hU : IsAffineOpen (X := projectiveSpace ι k)
      (ProjectiveSpectrum.basicOpen (homogeneousSubmodule ι k) (X i)) :=
    Proj.isAffineOpen_basicOpen _ _ hXi one_pos
  haveI : IsNoetherianRing Γ(projectiveSpace ι k,
      ProjectiveSpectrum.basicOpen (homogeneousSubmodule ι k) (X i)) :=
    IsLocallyNoetherian.component_noetherian ⟨_, hU⟩
  have hreg := Scheme.Modules.isSMulRegular_germ F hU (fracSection _ hh hXi le_rfl)
    (fun z hz hzU ↦ ?_) hpi
  · intro m m' hmm'
    have key : (projectiveSpace ι k).presheaf.germ
          (ProjectiveSpectrum.basicOpen (homogeneousSubmodule ι k) (X i)) p hpi
          (fracSection _ hh hXi le_rfl) •
        e.hom ((Scheme.Modules.moduleStalkFunctor _ p).map
          (twistBy (homogeneousSubmodule ι k) 1 hXi G) m) =
        (projectiveSpace ι k).presheaf.germ
          (ProjectiveSpectrum.basicOpen (homogeneousSubmodule ι k) (X i)) p hpi
          (fracSection _ hh hXi le_rfl) •
        e.hom ((Scheme.Modules.moduleStalkFunctor _ p).map
          (twistBy (homogeneousSubmodule ι k) 1 hXi G) m') := by
      rw [← map_smul (ConcreteCategory.hom e.hom), ← map_smul (ConcreteCategory.hom e.hom)]
      refine congrArg _ ((twistBy_stalk_eq_smul _ hh hXi G hpi m).symm.trans ?_)
      exact hmm'.trans (twistBy_stalk_eq_smul _ hh hXi G hpi m')
    exact (twistBy_stalk_bijective _ hXi G hpi).1
      ((ConcreteCategory.bijective_of_isIso e.hom).1 (hreg key))
  · have hzh : z ∈ ProjectiveSpectrum.basicOpen (homogeneousSubmodule ι k) h := hass z hz
    have hzW : z ∈ ProjectiveSpectrum.basicOpen (homogeneousSubmodule ι k) (X i) ⊓
        ProjectiveSpectrum.basicOpen (homogeneousSubmodule ι k) h := ⟨hzU, hzh⟩
    have hmul := fracSection_mul_fracSection_symm _ hh hXi
      (inf_le_left : ProjectiveSpectrum.basicOpen (homogeneousSubmodule ι k) (X i) ⊓
        ProjectiveSpectrum.basicOpen (homogeneousSubmodule ι k) h ≤ _) inf_le_right
    refine ((projectiveSpace ι k).mem_basicOpen
      (show Γ(projectiveSpace ι k, ProjectiveSpectrum.basicOpen (homogeneousSubmodule ι k) (X i))
        from fracSection _ hh hXi le_rfl) z hzU).mpr ?_
    have hres := TopCat.Presheaf.germ_res_apply (projectiveSpace ι k).presheaf
      (homOfLE (inf_le_left : ProjectiveSpectrum.basicOpen (homogeneousSubmodule ι k) (X i) ⊓
        ProjectiveSpectrum.basicOpen (homogeneousSubmodule ι k) h ≤ _)) z hzW
      (fracSection _ hh hXi le_rfl)
    rw [← hres]
    refine IsUnit.of_mul_eq_one ((projectiveSpace ι k).presheaf.germ _ z hzW
      (fracSection _ hXi hh inf_le_right)) ?_
    exact (map_mul _ _ _).symm.trans ((congrArg _ hmul).trans (map_one _))

/-- **The hyperplane sequence `F(-1) ⟶ F ⟶ i_* i^* F`** of a module sheaf `F` on `ℙ(ι)`, for a
linear form `h` with nonzero `X j`-coefficient. The first map is multiplication by `h`,
`twistBy h` on `F(-1)` read through `F(-1)(1) ≅ F`; the second is the unit of the
pullback/pushforward adjunction along the hyperplane `i : V₊(h) ⟶ ℙ(ι)`, presented as
`ℙ({i // i ≠ j}) ⟶ ℙ(ι)` (`linearHyperplane`). -/
def hyperplaneSequence [Finite ι] (F : (projectiveSpace ι k).Modules) {h : MvPolynomial ι k}
    (hh : h ∈ homogeneousSubmodule ι k 1) (j : ι) (hj : h.coeff (Finsupp.single j 1) ≠ 0) :
    ShortComplex (projectiveSpace ι k).Modules :=
  ShortComplex.mk
    (twistBy (homogeneousSubmodule ι k) 1 hh (tensorTwist (homogeneousSubmodule ι k) F (-1)) ≫
      (tensorTwistNegOneTwistIso F).hom)
    ((Scheme.Modules.pullbackPushforwardAdjunction (linearHyperplane hh j)).unit.app F) (by
      rw [Category.assoc, ← Adjunction.unit_naturality, ← Category.assoc]
      exact (congrArg (· ≫ _) (twistBy_comp_unit_eq_zero (linearHyperplaneHom hh j)
        (linearHyperplaneHom_surjective hh j) hh (linearHyperplaneHom_self hh hj)
        exists_mem_basicOpen_one _)).trans zero_comp)

/-- **Restriction to a hyperplane avoiding the associated points is short exact** (Stacks 08A0):
for a quasi-coherent `F` on `ℙ(ι)` and a linear form `h` lying in the prime of no associated point
of `F`,

`0 ⟶ F(-1) ⟶(·h) F ⟶ i_* i^* F ⟶ 0`

is short exact, with `i : V₊(h) ⟶ ℙ(ι)` the hyperplane (`linearHyperplane`). `Finite ι` makes the
charts Noetherian.

Exactness on the right and in the middle holds for every module sheaf: the cokernel of
multiplication by `h` is killed by `h`, hence pushed forward from `V₊(h)`
(`isIso_unit_of_twistBy_eq_zero`). Only injectivity on the left uses `hass`: on the chart `D₊(X i)`
it is multiplication by `h / X i` on stalks, and a function that is a unit at every associated
point is a nonzerodivisor on every stalk (`Scheme.Modules.isSMulRegular_germ`).

`hass` is load-bearing: for `F = i_* 𝒪_H` itself, with at least two variables, the hyperplane
contains every point of the support, multiplication by `h` is zero on the nonzero `F(-1)`, and
the sequence is not left exact. Coherence
is not needed here; it is what makes the associated points finite
(`Scheme.Modules.associatedPoints_finite`), so that `exists_linearForm_not_mem` supplies such an
`h` over an infinite field. -/
theorem hyperplaneSection_shortExact [Finite ι] (F : (projectiveSpace ι k).Modules)
    [F.IsQuasicoherent] {h : MvPolynomial ι k} (hh : h ∈ homogeneousSubmodule ι k 1) (j : ι)
    (hj : h.coeff (Finsupp.single j 1) ≠ 0)
    (hass : ∀ z ∈ Scheme.Modules.associatedPoints F, h ∉ z.asHomogeneousIdeal) :
    (hyperplaneSequence F hh j hj).ShortExact := by
  haveI := mono_twistBy_tensorTwist F hh hass
  have core := shortExact_twistBy_unit (linearHyperplaneHom hh j)
    (linearHyperplaneHom_surjective hh j) hh (ker_linearHyperplaneHom hh hj)
    exists_mem_basicOpen_one (tensorTwist (homogeneousSubmodule ι k) F (-1))
  refine ShortComplex.shortExact_of_iso ?_ core
  refine ShortComplex.isoMk (Iso.refl _) (tensorTwistNegOneTwistIso F)
    ((Scheme.Modules.pullback (linearHyperplane hh j) ⋙
      Scheme.Modules.pushforward (linearHyperplane hh j)).mapIso (tensorTwistNegOneTwistIso F))
    (by simp [hyperplaneSequence]) ?_
  exact ((Scheme.Modules.pullbackPushforwardAdjunction (linearHyperplane hh j)).unit_naturality
    (tensorTwistNegOneTwistIso F).hom).symm

end ProjectiveSpace

end AlgebraicGeometry.Proj
