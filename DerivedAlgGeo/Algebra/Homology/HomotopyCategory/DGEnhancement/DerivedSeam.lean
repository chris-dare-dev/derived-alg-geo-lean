/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.DGEnhancement.KInjective
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.DGEnhancement.Seam

/-!
# The derived seam: `H⁰(D^dg A)` and `DerivedCategory A`

`dg-enhancements-e9`, the theorem the DG track was opened for. The comparison
functor is built here, its full faithfulness is proved unconditionally, and the
equivalence is derived from one named external input.

## The route

`D^dg A` is the full dg subcategory of `C^dg A` on the K-injective complexes
(`dg-enhancements-e8`). So the comparison factors through work that already
exists:

```
H⁰(D^dg A) --(ι).h0--> H⁰(C^dg A) --h0Functor--> K(A) --Qh--> D(A)
```

The middle arrow is `dg-enhancements-e4`'s `Cdg.seam`, already an equivalence.
The first is `H⁰` of the inclusion dg functor, and it is fully faithful because
the inclusion acts as `AddMonoidHom.id` on Hom-complexes. Only the last arrow
carries new content, and it is where K-injectivity is spent.

## What is unconditional, and what is not

**Full faithfulness is unconditional.** Mathlib's
`CochainComplex.IsKInjective.Qh_map_bijective` says `Qh` is bijective on
morphisms *into* a K-injective complex. Both objects here are K-injective, so
that applies directly and nothing further is assumed.

**Essential surjectivity is not, and cannot be at this pin.** It asks that
every object of `D(A)` be represented by a K-injective complex, i.e. that
K-injective resolutions exist. That is Spaltenstein's theorem, and **Mathlib
does not have it**: `Mathlib/Algebra/Homology/HomotopyCategory/KInjective.lean`
cites [spaltenstein1998] in its references and proves no existence statement,
and there is no `EnoughKInjectives`, no `kInjectiveResolution` and no
`HasKInjective` anywhere in the library at `mathlib_rev`.

## The input, and the line it must not cross

`HasKInjectiveResolutions` asks exactly for the missing mathematics: every
cochain complex admits a quasi-isomorphism to a K-injective one. It is a real,
externally checkable statement about `A` — true for Grothendieck abelian
categories — and a caller supplying it is asserting a theorem, not a
convenience.

What it deliberately is **not** is a field asserting that the comparison
functor is an equivalence. That would be assuming the conclusion, which is the
failure mode `dg-enhancements-e8`'s acceptance names when it forbids a
resolution theorem represented by a caller-supplied conclusion field. The
distinction is the whole design of this file: the input is upstream of the
theorem and the theorem is derived from it.

When someone formalizes Spaltenstein's construction, this class becomes an
instance and `derivedSeam` becomes unconditional with no change to any
consumer. That is the seam the design is protecting.

## References

* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65
  (1988) — the existence theorem `HasKInjectiveResolutions` stands in for.
* `Mathlib/Algebra/Homology/DerivedCategory/KInjective.lean` — the full
  faithfulness half, which Mathlib does supply.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open CochainComplex CategoryTheory.Limits

namespace Cdg

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The inclusion of the K-injective model into the dg category of all cochain
complexes, as a dg functor. -/
abbrev ddgInclusion : DGFunctor (Ddg A) (Cdg A) :=
  DGFullSubcategory.iota (IsKInjectiveObj (A := A))

variable (A) in
/-- **Every cochain complex admits a K-injective resolution.**

The one external input of this file, and the exact statement Mathlib lacks at
`mathlib_rev`. It holds for Grothendieck abelian categories by Spaltenstein's
construction.

Stated as a quasi-isomorphism into a K-injective complex — the mathematics —
rather than as any claim about the comparison functor below. See the module
docstring on why that distinction is load-bearing. -/
class HasKInjectiveResolutions : Prop where
  /-- Every cochain complex receives a quasi-isomorphism from a K-injective
  one. -/
  exists_kInjective_quasiIso (K : CochainComplex A ℤ) :
    ∃ (L : CochainComplex A ℤ) (_ : L.IsKInjective) (f : K ⟶ L), QuasiIso f

variable [HasDerivedCategory.{v} A]

/-- **The derived seam functor** `H⁰(D^dg A) ⥤ D(A)`.

Composite of `H⁰` of the inclusion, `dg-enhancements-e4`'s seam, and Mathlib's
`Qh`. The direction is explicit and is the only one this file constructs:
nothing here builds a functor out of `D(A)`. -/
noncomputable def derivedSeamFunctor :
    H0 (Ddg A) ⥤ DerivedCategory A :=
  (ddgInclusion (A := A)).h0 ⋙ h0Functor ⋙ DerivedCategory.Qh

/-! ### `H⁰` of the inclusion is fully faithful

Both are definitional. `DGFullSubcategory` gives `Ddg A` the ambient
Hom-complexes unchanged, so `cocycles` and `coboundaries` between two
K-injective objects are literally the ambient ones, and `H⁰` of the inclusion
is the identity map between two quotients of the same group by the same
subgroup. -/

instance ddgInclusion_h0_faithful : (ddgInclusion (A := A)).h0.Faithful where
  map_injective {_ _} f g h := by
    induction f using Quotient.ind with
    | _ f =>
      induction g using Quotient.ind with
      | _ g => exact QuotientAddGroup.eq.mpr (QuotientAddGroup.eq.mp h)

instance ddgInclusion_h0_full : (ddgInclusion (A := A)).h0.Full where
  map_surjective {_ _} φ := by
    induction φ using Quotient.ind with
    | _ h => exact ⟨QuotientAddGroup.mk ⟨h.1, h.2⟩, rfl⟩

/-! ### The composite is fully faithful, unconditionally

The three arrows are bijective on Hom for three different reasons, and only the
last one spends K-injectivity. `Qh` is **not** fully faithful in general; it is
bijective into a K-injective target, which is exactly what the objects of
`D^dg A` are. -/

/-- The underlying cochain complex of an object of `H⁰(D^dg A)`. -/
abbrev underlying (X : H0 (Ddg A)) : CochainComplex A ℤ :=
  Cdg.of A ((H0.of (Ddg A) X).obj)

instance underlying_isKInjective (X : H0 (Ddg A)) :
    (underlying X).IsKInjective :=
  (H0.of (Ddg A) X).prop

-- `omit` goes before the docstring; after it is a parse error.
omit [HasDerivedCategory.{v} A] in
/-- The seam functor lands on the quotient of the underlying complex; `rfl`,
and it is what lets Mathlib's bijectivity lemma apply. -/
lemma h0Functor_obj_ddgInclusion (X : H0 (Ddg A)) :
    h0Functor.obj ((ddgInclusion (A := A)).h0.obj X) =
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (underlying X) :=
  rfl

/-- A fully faithful functor is bijective on each Hom-set. Stated locally
because the composite below is assembled from three bijections of which only
two come from full faithfulness. -/
private lemma bijective_map_of_fullyFaithful {C D : Type*} [Category C]
    [Category D] (F : C ⥤ D) [F.Full] [F.Faithful] (X Y : C) :
    Function.Bijective (F.map : (X ⟶ Y) → _) :=
  ⟨fun _ _ h => F.map_injective h, fun g => F.map_surjective g⟩

/-- **The derived seam functor is bijective on Hom-sets.**

Three bijections, three different reasons: `H⁰` of the inclusion because the
Hom-complexes are the ambient ones, `h0Functor` because `dg-enhancements-e4`
proved it an equivalence, and `Qh` because the target is K-injective. Only the
last is about resolutions, and it assumes nothing. -/
lemma derivedSeamFunctor_map_bijective (X Y : H0 (Ddg A)) :
    Function.Bijective ((derivedSeamFunctor (A := A)).map : (X ⟶ Y) → _) :=
  (CochainComplex.IsKInjective.Qh_map_bijective _ (underlying Y)).comp
    ((bijective_map_of_fullyFaithful h0Functor _ _).comp
      (bijective_map_of_fullyFaithful (ddgInclusion (A := A)).h0 X Y))

instance derivedSeamFunctor_faithful :
    (derivedSeamFunctor (A := A)).Faithful where
  map_injective {X Y} := (derivedSeamFunctor_map_bijective X Y).injective

instance derivedSeamFunctor_full : (derivedSeamFunctor (A := A)).Full where
  map_surjective {X Y} := (derivedSeamFunctor_map_bijective X Y).surjective

/-! ### Essential surjectivity, and the one place the input is spent -/

/-- `Q` is essentially surjective because it is a localization functor.
Named rather than anonymous: an audited generated name breaks silently on a
rename. -/
instance derivedCategoryQ_essSurj : (DerivedCategory.Q (C := A)).EssSurj :=
  Localization.essSurj _ (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))

/-- **The derived seam functor is essentially surjective**, given K-injective
resolutions.

This is the only declaration in the file that uses
`HasKInjectiveResolutions`, and the use is exactly the expected one: resolve a
representing complex, then transport along the resulting quasi-isomorphism. -/
instance derivedSeamFunctor_essSurj [HasKInjectiveResolutions A] :
    (derivedSeamFunctor (A := A)).EssSurj where
  mem_essImage Y := by
    obtain ⟨L, hL, f, hf⟩ :=
      HasKInjectiveResolutions.exists_kInjective_quasiIso (A := A)
        ((DerivedCategory.Q (C := A)).objPreimage Y)
    haveI := hL
    haveI := hf
    refine ⟨(DGFullSubcategory.mk (P := IsKInjectiveObj (A := A)) (L : Cdg A) hL :
      Ddg A), ⟨?_⟩⟩
    exact (DerivedCategory.quotientCompQhIso A).app L ≪≫
      (asIso (DerivedCategory.Q.map f)).symm ≪≫
      (DerivedCategory.Q (C := A)).objObjPreimageIso Y

/-- Full, faithful and essentially surjective, so an equivalence. Stated the
same way `dg-enhancements-e4` states it for `Cdg.seam`. -/
instance derivedSeamFunctor_isEquivalence [HasKInjectiveResolutions A] :
    (derivedSeamFunctor (A := A)).IsEquivalence where

/-- **The derived seam.** `H⁰(D^dg A) ≌ D(A)`.

Full faithfulness is unconditional; only essential surjectivity consumes
`HasKInjectiveResolutions`. The direction is `H⁰(D^dg A) ⟶ D(A)`, and it is
`derivedSeamFunctor`. -/
noncomputable def derivedSeam [HasKInjectiveResolutions A] :
    H0 (Ddg A) ≌ DerivedCategory A :=
  (derivedSeamFunctor (A := A)).asEquivalence

end Cdg

end CategoryTheory
