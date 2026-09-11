/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.Generator
import DerivedAlgGeo.Topology.Sheaves.Cech.BasisComparison
import DerivedAlgGeo.Topology.Sheaves.Cech.InjectiveFlasque
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.Topology.Sheaves.Flasque

/-!
# Flasque sheaves: acyclicity, and injective sheaves of modules

## Flasque abelian sheaves are acyclic

For a flasque sheaf of abelian groups `F` on a topological space, `Sheaf.H F n` vanishes
for every `n ≥ 1`. This is Hartshorne III.2.5, proved by dimension shifting: embed `F` in
an injective sheaf `I`, which is flasque by `Sheaf.isFlasque_of_injective`; the quotient `Q`
is flasque by `IsFlasque.of_shortExact_of_isFlasque₁₂`; global sections of `I` surject onto
those of `Q` by `IsFlasque.epi_of_shortExact`, which kills `H¹ F`
(`Sheaf.H_one_subsingleton_of_sections_epi`); and `H^(n+2) F` vanishes once `H^(n+1) Q`
does (`Sheaf.H_succ_subsingleton_of_shortExact`), so the induction closes.

Nothing here is Čech-theoretic; compare `Sites/SheafCohomology/Cech/Comparison.lean`,
which obtains vanishing from Čech exactness instead.

## Injective sheaves of modules are flasque

For a sheaf of rings `R` on a space, an injective sheaf of `R`-modules `I` has flasque
underlying abelian sheaf. The proof is the one for abelian sheaves
(`Sheaf.isFlasque_of_injective`) with the free abelian sheaf on an open replaced by the free
sheaf of modules on an open, `SheafOfModules.freeYonedaSheaf`: a section over `V` is a map
`freeYonedaSheaf R V ⟶ I`, an inclusion `V ⊆ U` induces a monomorphism
`freeYonedaSheaf R V ⟶ freeYonedaSheaf R U`, and injectivity of `I` extends the map. Together
with the first half this makes `I` acyclic for `Sheaf.H`, which is the acyclicity input of
`extComparisonAddEquiv` for the forgetful functor from module sheaves to abelian sheaves.

## Main results

* `TopCat.Sheaf.subsingleton_H_of_isFlasque`.
* `SheafOfModules.freeYonedaSheafHomEquiv`, `SheafOfModules.freeYonedaSheafHomEquiv_comp`,
  `SheafOfModules.freeYonedaSheafMap_mono`.
* `SheafOfModules.isFlasque_toSheaf_of_injective`.
-/

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace

namespace TopCat.Sheaf

variable {X : TopCat.{u}} [hExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X)]

/-- **Flasque sheaves are acyclic.** For a flasque sheaf of abelian groups `F` on a
topological space, `Sheaf.H F (n + 1)` is trivial for every `n`. -/
theorem subsingleton_H_of_isFlasque
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) [F.IsFlasque] (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.derivedH hExt F (n + 1)) := by
  induction n generalizing F with
  | zero =>
    let ip : InjectivePresentation F := Classical.arbitrary _
    haveI : TopCat.Sheaf.IsFlasque ip.shortComplex.X₁ := ‹F.IsFlasque›
    exact CategoryTheory.Sheaf.H_one_subsingleton_of_sections_epi ip
      (IsFlasque.epi_of_shortExact ip.shortExact_shortComplex)
  | succ n ih =>
    let ip : InjectivePresentation F := Classical.arbitrary _
    haveI : TopCat.Sheaf.IsFlasque ip.shortComplex.X₁ := ‹F.IsFlasque›
    haveI : TopCat.Sheaf.IsFlasque ip.shortComplex.X₂ :=
      CategoryTheory.Sheaf.isFlasque_of_injective ip.J
    haveI : TopCat.Sheaf.IsFlasque ip.shortComplex.X₃ :=
      IsFlasque.of_shortExact_of_isFlasque₁₂ ip.shortExact_shortComplex
    haveI : Injective ip.shortComplex.X₂ := ip.injective
    haveI := ih ip.shortComplex.X₃
    exact CategoryTheory.Sheaf.H_succ_subsingleton_of_shortExact ip.shortExact_shortComplex
      (n + 1)

end TopCat.Sheaf

namespace SheafOfModules

variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

set_option backward.isDefEq.respectTransparency false in
/-- Sections of a sheaf of modules over an open `U` are the maps out of the free sheaf of
modules on `U`: the sheafification adjunction followed by `PresheafOfModules.freeYonedaEquiv`. -/
noncomputable def freeYonedaSheafHomEquiv (U : Opens X) (M : SheafOfModules.{u} R) :
    (freeYonedaSheaf R U ⟶ M) ≃ M.val.obj (op U) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _).trans
    PresheafOfModules.freeYonedaEquiv

/-- The map of free sheaves of modules induced by an inclusion of opens. -/
noncomputable def freeYonedaSheafMap {V U : Opens X} (i : V ⟶ U) :
    freeYonedaSheaf R V ⟶ freeYonedaSheaf R U :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).map
    ((PresheafOfModules.free R.obj).map (yoneda.map i))

set_option backward.isDefEq.respectTransparency false in
/-- Precomposition with the free presheaf map induced by `i` is restriction of sections
along `i`, for presheaves of modules. -/
lemma freeYonedaEquiv_free_map_yoneda_map_comp {V U : Opens X}
    (i : V ⟶ U) (N : PresheafOfModules.{u} R.obj)
    (f : (PresheafOfModules.free R.obj).obj (yoneda.obj U) ⟶ N) :
    PresheafOfModules.freeYonedaEquiv ((PresheafOfModules.free R.obj).map (yoneda.map i) ≫ f) =
      N.map i.op (PresheafOfModules.freeYonedaEquiv f) := by
  have h1 : PresheafOfModules.freeHomEquiv ((PresheafOfModules.free R.obj).map (yoneda.map i) ≫ f)
      = yoneda.map i ≫ PresheafOfModules.freeHomEquiv f := by
    rw [← PresheafOfModules.freeAdjunction_homEquiv, ← PresheafOfModules.freeAdjunction_homEquiv]
    exact Adjunction.homEquiv_naturality_left _ _ _
  change yonedaEquiv (PresheafOfModules.freeHomEquiv (_ ≫ f)) = _
  rw [h1]
  exact (yonedaEquiv_naturality _ _).symm

set_option backward.isDefEq.respectTransparency false in
/-- Precomposition with `freeYonedaSheafMap R i` is restriction of sections along `i`. -/
lemma freeYonedaSheafHomEquiv_comp {V U : Opens X} (i : V ⟶ U) (M : SheafOfModules.{u} R)
    (e : freeYonedaSheaf R U ⟶ M) :
    freeYonedaSheafHomEquiv R V M (freeYonedaSheafMap R i ≫ e) =
      M.val.map i.op (freeYonedaSheafHomEquiv R U M e) := by
  have h1 : (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _
      (freeYonedaSheafMap R i ≫ e) =
      (PresheafOfModules.free R.obj).map (yoneda.map i) ≫
        (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _ e :=
    Adjunction.homEquiv_naturality_left _ _ _
  exact (congrArg PresheafOfModules.freeYonedaEquiv h1).trans
    (freeYonedaEquiv_free_map_yoneda_map_comp R i _ _)

/-- The map of free sheaves of modules induced by an inclusion of opens is a monomorphism:
on presheaves it is objectwise the free module map on an injection of (subsingleton) hom
types, and sheafification preserves monomorphisms. -/
instance freeYonedaSheafMap_mono {V U : Opens X} (i : V ⟶ U) :
    Mono (freeYonedaSheafMap R i) := by
  haveI : Mono ((PresheafOfModules.free R.obj).map (yoneda.map i)) := by
    apply PresheafOfModules.mono_of_injective
    intro W x y hxy
    haveI : Subsingleton ((yoneda.obj V).obj W) := inferInstanceAs (Subsingleton (unop W ⟶ V))
    change Finsupp.mapDomain ((yoneda.map i).app W) x =
      Finsupp.mapDomain ((yoneda.map i).app W) y at hxy
    exact Finsupp.mapDomain_injective (fun a b _ ↦ Subsingleton.elim a b) hxy
  exact Functor.map_mono _ _

set_option backward.isDefEq.respectTransparency false in
/-- **Injective sheaves of modules are flasque.** -/
theorem isFlasque_toSheaf_of_injective (I : SheafOfModules.{u} R) [Injective I] :
    TopCat.Sheaf.IsFlasque ((toSheaf R).obj I) := by
  constructor
  intro U V i
  rw [AddCommGrpCat.epi_iff_surjective]
  intro s
  let g : freeYonedaSheaf R V.unop ⟶ I := (freeYonedaSheafHomEquiv R V.unop I).symm s
  let e : freeYonedaSheaf R U.unop ⟶ I :=
    Injective.factorThru g (freeYonedaSheafMap R i.unop)
  refine ⟨freeYonedaSheafHomEquiv R U.unop I e, ?_⟩
  have key : I.val.map i.unop.op (freeYonedaSheafHomEquiv R U.unop I e) = s := by
    rw [← freeYonedaSheafHomEquiv_comp, Injective.comp_factorThru]
    exact (freeYonedaSheafHomEquiv R V.unop I).apply_symm_apply s
  exact key

end SheafOfModules
