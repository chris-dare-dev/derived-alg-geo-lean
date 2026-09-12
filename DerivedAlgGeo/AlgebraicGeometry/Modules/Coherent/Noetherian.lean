/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Category.FGModuleCat.Noetherian
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Abelian.Basic
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.Comparison
import DerivedAlgGeo.CategoryTheory.Subobject.NoetherianObject
import Mathlib.Topology.Sheaves.Stalks

/-!
# Noetherian coherent sheaves

Every coherent sheaf on a Noetherian scheme is a Noetherian object. The proof has three layers.

1. A finite module over a Noetherian ring is a Noetherian object of `FGModuleCat`, hence the affine
   equivalence makes every object of `Coh (Spec R)` Noetherian.
2. Restriction of coherent sheaves along an open immersion preserves monomorphisms. Restrictions
   to an open cover jointly reflect isomorphisms: this is checked on stalks using
   `Scheme.Modules.restrictStalkNatIso`.
3. On a finite cover, take the maximum of the local stabilization indices. The categorical
   finite-family theorem then reflects the resulting local isomorphisms to a global one.

The quasi-compactness in `IsNoetherian X` is essential. Local Noetherianity alone would allow an
infinite disjoint union, whose coherent sheaves need not satisfy a global ascending-chain
condition.

This discharges the `MuHNInput.noetherian` obligation for proper varieties. It does not assert
Grothendieck slope boundedness, which remains the other field of `MuHNInput`.

## Main results

* `Coh.restrict` — coherent restriction along an open immersion.
* `Coh.restrict_jointlyReflectsIsomorphisms` — an open cover detects isomorphisms.
* `Coh.isNoetherianObject_of_finite_openCover` — the finite-cover reduction.
* `Coh.isNoetherianObject` — coherent sheaves on a Noetherian scheme are Noetherian objects.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Coh

variable {X Y : Scheme.{u}}

/-- Restriction of coherent sheaves along an open immersion. -/
noncomputable def restrict (f : X ⟶ Y) [IsOpenImmersion f] : Coh Y ⥤ Coh X :=
  (Scheme.coherent X).lift (ι Y ⋙ Scheme.Modules.restrictFunctor f)
    (fun M ↦ Scheme.Modules.IsCoherent.restrict_of_isOpenImmersion f M.obj M.property)

/-- Forgetting coherence after coherent restriction is module-sheaf restriction after forgetting
coherence. -/
noncomputable def restrictCompι (f : X ⟶ Y) [IsOpenImmersion f] :
    restrict f ⋙ ι X ≅ ι Y ⋙ Scheme.Modules.restrictFunctor f :=
  (Scheme.coherent X).liftCompιIso _ _

/-- Restriction along an open immersion preserves monomorphisms of coherent sheaves when the
ambient scheme is locally Noetherian. -/
noncomputable instance restrict_preservesMonomorphisms
    (f : X ⟶ Y) [IsOpenImmersion f] [IsLocallyNoetherian Y] :
    (restrict f).PreservesMonomorphisms where
  preserves {A B} g _ := by
    letI : (ι X).Faithful := by
      change (Scheme.coherent X).ι.Faithful
      infer_instance
    letI : (ι X).ReflectsMonomorphisms :=
      Functor.reflectsMonomorphisms_of_faithful (ι X)
    apply (ι X).mono_of_mono_map
    change Mono ((Scheme.Modules.restrictFunctor f).map ((ι Y).map g))
    infer_instance

/-- **Restriction to the members of an open cover jointly reflects isomorphisms of coherent
sheaves.**

At a point of `X`, choose a preimage in one cover member. Restriction commutes with the stalk at
that preimage, so an isomorphism after restriction gives an isomorphism on the original stalk.
The stalk criterion then gives an isomorphism of module sheaves, and the fully faithful coherent
inclusion reflects it. -/
theorem restrict_jointlyReflectsIsomorphisms
    (Uc : Scheme.OpenCover.{u} X) [IsLocallyNoetherian X]
    {M N : Coh X} (f : M ⟶ N)
    (hf : ∀ i, IsIso ((restrict (Uc.f i)).map f)) : IsIso f := by
  let M' : TopCat.Sheaf AddCommGrpCat.{u} X :=
    ⟨M.obj.presheaf, M.obj.isSheaf⟩
  let N' : TopCat.Sheaf AddCommGrpCat.{u} X :=
    ⟨N.obj.presheaf, N.obj.isSheaf⟩
  let g : M' ⟶ N' := { hom := ((ι X).map f).mapPresheaf }
  haveI hg : IsIso g := by
    rw [TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
    intro x
    change IsIso
      ((Scheme.Modules.toPresheaf X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ((ι X).map f))
    let i := Uc.idx x
    obtain ⟨y, hy⟩ := Uc.covers x
    haveI hfi : IsIso ((restrict (Uc.f i)).map f) := hf i
    haveI hres : IsIso
        ((Scheme.Modules.restrictFunctor (Uc.f i)).map ((ι X).map f)) := by
      change IsIso ((ι (Uc.X i)).map ((restrict (Uc.f i)).map f))
      infer_instance
    haveI hresPresheaf : IsIso
        ((Scheme.Modules.toPresheaf (Uc.X i)).map
          ((Scheme.Modules.restrictFunctor (Uc.f i)).map ((ι X).map f))) :=
      Functor.map_isIso _ _
    haveI hresStalk : IsIso
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
          ((Scheme.Modules.toPresheaf (Uc.X i)).map
            ((Scheme.Modules.restrictFunctor (Uc.f i)).map ((ι X).map f)))) :=
      Functor.map_isIso _ _
    haveI hresComposite : IsIso
        ((Scheme.Modules.restrictFunctor (Uc.f i) ⋙
          Scheme.Modules.toPresheaf (Uc.X i) ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map ((ι X).map f)) := by
      change IsIso
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
          ((Scheme.Modules.toPresheaf (Uc.X i)).map
            ((Scheme.Modules.restrictFunctor (Uc.f i)).map ((ι X).map f))))
      infer_instance
    let e := Scheme.Modules.restrictStalkNatIso (Uc.f i) y
    haveI hcomp : IsIso
        (e.hom.app ((ι X).obj M) ≫
          ((Scheme.Modules.toPresheaf X ⋙
            TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} ((Uc.f i) y)).map
              ((ι X).map f))) := by
      rw [← e.hom.naturality ((ι X).map f)]
      infer_instance
    have horig : IsIso
        ((Scheme.Modules.toPresheaf X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} ((Uc.f i) y)).map
            ((ι X).map f)) :=
      IsIso.of_isIso_comp_left (e.hom.app ((ι X).obj M)) _
    have hiy : (Uc.f i) y = x := by simpa only [i] using hy
    rw [← hiy]
    exact horig
  haveI hmod : IsIso ((ι X).map f) := by
    rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
    intro U
    change IsIso (((TopCat.Sheaf.forget AddCommGrpCat.{u} X).map g).app (op U))
    infer_instance
  letI : (ι X).Full := by
    change (Scheme.coherent X).ι.Full
    infer_instance
  letI : (ι X).Faithful := by
    change (Scheme.coherent X).ι.Faithful
    infer_instance
  exact isIso_of_reflects_iso f (ι X)

/-- Every coherent sheaf on an affine Noetherian scheme is a Noetherian object. -/
instance isNoetherianObject_affine {R : CommRingCat.{u}} [IsNoetherianRing R]
    (M : Coh (Spec R)) : IsNoetherianObject M := by
  let e := affineEquivalence (R := R)
  exact CategoryTheory.isNoetherianObject_of_reflectsIsomorphisms e.functor

/-- **Finite-open-cover reduction for Noetherian coherent sheaves.** If the restriction of `M`
to every member of a finite open cover is Noetherian, then `M` is Noetherian. -/
theorem isNoetherianObject_of_finite_openCover
    (Uc : Scheme.OpenCover.{u} X) [Finite Uc.I₀] [IsLocallyNoetherian X]
    (M : Coh X)
    (hlocal : ∀ i, IsNoetherianObject ((restrict (Uc.f i)).obj M)) :
    IsNoetherianObject M := by
  apply CategoryTheory.isNoetherianObject_of_finite_jointlyReflectsIsomorphisms
    (fun i ↦ restrict (Uc.f i)) hlocal
  intro Y Z f hf
  exact restrict_jointlyReflectsIsomorphisms Uc f hf

/-- **Every coherent sheaf on a Noetherian scheme is a Noetherian object.** -/
instance isNoetherianObject [IsNoetherian X] (M : Coh X) : IsNoetherianObject M := by
  let Uc := X.affineOpenCover.openCover.finiteSubcover
  letI : Fintype Uc.I₀ := by
    dsimp only [Uc]
    infer_instance
  apply isNoetherianObject_of_finite_openCover Uc M
  intro i
  dsimp only [Uc, Scheme.OpenCover.finiteSubcover_X]
  letI : IsLocallyNoetherian (Uc.X i) :=
    isLocallyNoetherian_of_isOpenImmersion (Uc.f i)
  let R := X.affineOpenCover.X (X.affineOpenCover.openCover.idx i.1)
  change IsNoetherianObject ((restrict (Uc.f i)).obj M : Coh (Spec R))
  have hSpec : IsLocallyNoetherian (Spec R) := by
    change IsLocallyNoetherian (Uc.X i)
    infer_instance
  letI : IsLocallyNoetherian (Spec R) := hSpec
  letI : IsNoetherianRing R := by
    rw [← isLocallyNoetherian_Spec]
    infer_instance
  let F : Coh (Spec R) := (restrict (Uc.f i)).obj M
  change IsNoetherianObject F
  infer_instance

end AlgebraicGeometry.Coh
