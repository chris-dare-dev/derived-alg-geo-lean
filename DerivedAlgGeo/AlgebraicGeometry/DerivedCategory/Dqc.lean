/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.CompactlyGenerated
import DerivedAlgGeo.CategoryTheory.Triangulated.CohomologyObjectProperty
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Quasicoherent.Extensions
import DerivedAlgGeo.AlgebraicGeometry.CoherentSheaf.Quasicoherent.Coproducts
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BoundedGeometry

/-!
# The quasi-coherent cohomology locus in a scheme-derived category

The ambient `SchemeDerivedCategory X` is the derived category of **all**
`𝒪_X`-module sheaves.  The category conventionally denoted `Dqc(X)` is the
full subcategory whose cohomology sheaves are quasi-coherent.  This file makes
that distinction part of the Lean type.

`Dqc(X)` **is** a triangulated subcategory, and this file proves it rather than
assuming it (#721).  The route does not need quasi-coherent sheaves to be an
abelian subcategory of `X.Modules` — an earlier version of this docstring named
that as the blocker.  What is needed is only the **weak Serre** property:
closure under kernels, cokernels and extensions, which
`CoherentSheaf/Quasicoherent/Kernels.lean` and
`Cohomology/Quasicoherent/Extensions.lean` supply on an arbitrary scheme
(#720).  `DerivedCategory.cohomologyIn` turns that into closure under cones via
the five-term long exact homology sequence, so `Pretriangulated` on the locus
and triangulatedness of the inclusion both follow from Mathlib.

Comparison statements a later geometric realization must still prove — the
bounded-coherent identification and the compact/perfect comparison — remain
propositions with no unsupported inhabitant, so unsupported geometric cases are
still not silently identified with the all-sheaf derived category.
-/

namespace CategoryTheory.Triangulated.StabilityCondition.Families

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated AlgebraicGeometry

noncomputable section

universe u v w

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Coh.ι_additive Coh.ι_preservesFiniteLimits
  Coh.ι_preservesFiniteColimits

/-- An object of the all-module-sheaf derived category has quasi-coherent
cohomology when every one of its canonical cohomology sheaves is
quasi-coherent. -/
def schemeQuasicoherentCohomology (X : Scheme.{u}) :
    ObjectProperty (SchemeDerivedCategory X) :=
  fun E ↦ ∀ n : ℤ,
    (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      ((DerivedCategory.homologyFunctor X.Modules n).obj E)

instance (X : Scheme.{u}) :
    (schemeQuasicoherentCohomology X).IsClosedUnderIsomorphisms where
  of_iso e hE n :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((DerivedCategory.homologyFunctor X.Modules n).mapIso e) (hE n)

/-- **`Dqc(X)` is a triangulated subcategory of the all-sheaf derived
category** (#721).

Quasi-coherence is a weak Serre subcategory of `X.Modules` — closed under
kernels, cokernels and extensions, and containing zero — on an arbitrary
scheme, with no noetherian or quasi-compactness hypothesis.  That is exactly
the input `DerivedCategory.cohomologyIn_isTriangulated` asks for, and it is why
closure under cones holds without quasi-coherent sheaves forming an abelian
subcategory: the five-term homology sequence pays for the missing subobject and
quotient closure.

Note that quasi-coherence is *not* a Serre class here — a subsheaf of a
quasi-coherent sheaf need not be quasi-coherent — so `IsSerreClass` and
Mathlib's three-term `prop_X₂_of_exact` are unavailable, and nothing below
uses them. -/
instance (X : Scheme.{u}) : (schemeQuasicoherentCohomology X).IsTriangulated :=
  inferInstanceAs ((DerivedCategory.cohomologyIn
    (SheafOfModules.isQuasicoherent X.ringCatSheaf)).IsTriangulated)

/-- The honest `Dqc(X)` object class: the full subcategory of the derived
category of all module sheaves cut out by quasi-coherent cohomology. -/
abbrev SchemeQuasicoherentDerivedCategory (X : Scheme.{u}) :=
  (schemeQuasicoherentCohomology X).FullSubcategory

namespace SchemeQuasicoherentDerivedCategory

variable (X : Scheme.{u})

/-- The inclusion of the quasi-coherent cohomology locus into the derived
category of all module sheaves. -/
abbrev ι : SchemeQuasicoherentDerivedCategory X ⥤ SchemeDerivedCategory X :=
  (schemeQuasicoherentCohomology X).ι

/-- **The inclusion `Dqc(X) ⥤ D(X.Modules)` is a triangulated functor.**  This
is a Mathlib instance once the object property is a triangulated subcategory; it
is recorded here because it is what `Dqc(X)` has to have for "compact object in `Dqc(X)`" to be a statement one
may make.  (`Pretriangulated` is data, not a proposition, so it is left as the
Mathlib instance rather than restated here.) -/
theorem ι_isTriangulated : (SchemeQuasicoherentDerivedCategory.ι X).IsTriangulated :=
  inferInstance

/-- **The abelian-side inputs to `Dqc(X)`'s coproduct structure are in place**
(#721, third bullet).

Quasi-coherence is closed under `ι`-indexed coproducts on an arbitrary scheme
(`CoherentSheaf/Quasicoherent/Coproducts.lean`), and `X.Modules` has those
coproducts. Closure under isomorphism is Mathlib's and is recorded alongside it.
Together with `DerivedCategory.cohomologyIn_prop_coproduct` these are everything
the third bullet needs **except** its derived-category half.

That half is not available at this Mathlib pin and is not asserted anywhere:
`SchemeDerivedCategory X` is not known to have small coproducts, and `Hⁿ` on it is
not known to preserve them. Mathlib's `DerivedCategory` files contain no coproduct
results at all. Until that lands, a consumer wanting closure of `Dqc(X)` under a
coproduct must supply the existence and the preservation itself and call
`DerivedCategory.cohomologyIn_prop_coproduct` directly. -/
theorem quasicoherent_isClosedUnderIsomorphisms :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderIsomorphisms :=
  inferInstance

theorem quasicoherent_isClosedUnderCoproducts (ι : Type u) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderColimitsOfShape
      (Discrete ι) :=
  inferInstance

/-- **`Dqc(X)` is closed under a coproduct that cohomology preserves** (#721).

Both hypotheses are carried explicitly rather than installed as instances, because
neither holds by instance search at this pin: `SchemeDerivedCategory X` is not known
to have small coproducts, and `Hⁿ` on it is not known to preserve them.  Supplying
them unconditionally — equivalently, proving that `D(A)` has small coproducts and that
homology preserves them for a Grothendieck `A` — is the open half of this issue's
third bullet.

Two pieces of plumbing here are deliberate and both cost real time to find.

The `letI` is this file's house idiom, not an incantation: `Families/SchemeDerived.lean`
carries the same line in every declaration that mentions the derived category.  The
file-level `attribute [local instance]` does not reach a fresh mention of
`DerivedCategory.cohomologyIn`, which is why `schemeQuasicoherentCohomology` — routed
through the `SchemeDerivedCategory` abbrev, which carries its own `letI` — elaborates
while a direct mention does not.

The `@` and the named `quasicoherent_isClosedUnderCoproducts` are the second piece.
Instance search cannot find that instance through this application even though
`quasicoherent_isClosedUnderCoproducts` two declarations above finds it by
`inferInstance`: unifying `A := X.Modules` routes the category through
`Scheme.Modules.instCategory`, and the goal it then poses no longer matches the
instance's own head.  Supplying it by name is not a workaround for an unproved fact —
it is the same instance, named. -/
theorem sigma_mem {ι : Type u} (E : ι → SchemeDerivedCategory X) [HasCoproduct E]
    (hpres : ∀ n : ℤ, PreservesColimitsOfShape (Discrete ι)
      (DerivedCategory.homologyFunctor X.Modules n))
    (hE : ∀ i, schemeQuasicoherentCohomology X (E i)) :
    schemeQuasicoherentCohomology X (∐ E) :=
  letI := HasDerivedCategory.standard X.Modules
  @DerivedCategory.cohomologyIn_prop_coproduct X.Modules _ _ _
    (SheafOfModules.isQuasicoherent X.ringCatSheaf) ι
    (quasicoherent_isClosedUnderCoproducts X ι) E _ hpres hE

/-- Membership in `Dqc(X)` is exactly quasi-coherence of every cohomology
sheaf. -/
theorem mem_iff (E : SchemeDerivedCategory X) :
    schemeQuasicoherentCohomology X E ↔
      ∀ n : ℤ, (SheafOfModules.isQuasicoherent X.ringCatSheaf)
        ((DerivedCategory.homologyFunctor X.Modules n).obj E) :=
  Iff.rfl

end SchemeQuasicoherentDerivedCategory

/-- Exact functors commute with cohomology after passage to derived
categories.  The isomorphism is constructed from a representative complex,
the two localization comparison isomorphisms, and preservation of homology.
-/
noncomputable def mapDerivedCategoryHomologyIso
    {A : Type u} {B : Type v} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w} B] (F : A ⥤ B)
    (hadd : F.Additive) (hlim : PreservesFiniteLimits F)
    (hcolim : PreservesFiniteColimits F)
    (E : DerivedCategory A) (n : ℤ) :
    (DerivedCategory.homologyFunctor B n).obj (F.mapDerivedCategory.obj E) ≅
      F.obj ((DerivedCategory.homologyFunctor A n).obj E) :=
  by
    letI : F.Additive := hadd
    letI : PreservesFiniteLimits F := hlim
    letI : PreservesFiniteColimits F := hcolim
    let K := DerivedCategory.Q.objPreimage E
    exact (DerivedCategory.homologyFunctor B n).mapIso
        (F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso E).symm) ≪≫
      (DerivedCategory.homologyFunctor B n).mapIso
        (F.mapDerivedCategoryFactors.app K) ≪≫
      (DerivedCategory.homologyFunctorFactors B n).app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≪≫
      (K.sc n).mapHomologyIso F ≪≫
      F.mapIso ((DerivedCategory.homologyFunctorFactors A n).app K).symm ≪≫
      F.mapIso ((DerivedCategory.homologyFunctor A n).mapIso
        (DerivedCategory.Q.objObjPreimageIso E))

/-- The exact inclusion of coherent sheaves induces a concrete functor from
their unbounded derived category to the all-module-sheaf derived category. -/
noncomputable def coherentDerivedInclusion
    (X : Scheme.{u}) [IsLocallyNoetherian X] :
    SchemeCoherentDerivedCategory X ⥤ SchemeDerivedCategory X :=
  by
    exact @Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (Coh.ι X)
      (Coh.ι_additive X) (Coh.ι_preservesFiniteLimits X)
      (Coh.ι_preservesFiniteColimits X)

/-- The derived coherent-sheaf inclusion has quasi-coherent cohomology in
every degree.  This is proved by exactness of `Coh.ι`, not postulated as a
geometric realization. -/
theorem coherentDerivedInclusion_mem_dqc
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (E : SchemeCoherentDerivedCategory X) :
    schemeQuasicoherentCohomology X ((coherentDerivedInclusion X).obj E) := by
  intro n
  let H := (DerivedCategory.homologyFunctor (Coh X) n).obj E
  have hfp : (SheafOfModules.isFinitePresentation X.ringCatSheaf)
      ((Coh.ι X).obj H) := H.property
  letI : (SheafOfModules.isFinitePresentation X.ringCatSheaf)
      ((Coh.ι X).obj H) := hfp
  have hqc : (SheafOfModules.isQuasicoherent X.ringCatSheaf) ((Coh.ι X).obj H) :=
    inferInstance
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (mapDerivedCategoryHomologyIso (Coh.ι X) (Coh.ι_additive X)
      (Coh.ι_preservesFiniteLimits X) (Coh.ι_preservesFiniteColimits X) E n).symm hqc

/-- The genuine lift of the coherent derived category into the
quasi-coherent-cohomology locus. -/
noncomputable def coherentDerivedToDqc
    (X : Scheme.{u}) [IsLocallyNoetherian X] :
    SchemeCoherentDerivedCategory X ⥤ SchemeQuasicoherentDerivedCategory X :=
  (schemeQuasicoherentCohomology X).lift
    (coherentDerivedInclusion X) (coherentDerivedInclusion_mem_dqc X)

/-- Forgetting the quasi-coherent-cohomology proof recovers the derived
coherent-sheaf inclusion definitionally. -/
noncomputable def coherentDerivedToDqcCompInclusion
    (X : Scheme.{u}) [IsLocallyNoetherian X] :
    coherentDerivedToDqc X ⋙ SchemeQuasicoherentDerivedCategory.ι X ≅
      coherentDerivedInclusion X :=
  (schemeQuasicoherentCohomology X).liftCompιIso
    (coherentDerivedInclusion X) (coherentDerivedInclusion_mem_dqc X)

/-- Bounded objects in the honest `Dqc(X)` locus are detected by the
canonical t-structure of the ambient all-sheaf derived category. -/
def schemeBoundedQuasicoherent
    (X : Scheme.{u}) : ObjectProperty (SchemeQuasicoherentDerivedCategory X) :=
  fun E ↦ (DerivedCategory.TStructure.t (C := X.Modules)).bounded E.obj

instance (X : Scheme.{u}) :
    (schemeBoundedQuasicoherent X).IsClosedUnderIsomorphisms where
  of_iso e hE :=
    (DerivedCategory.TStructure.t (C := X.Modules)).bounded.prop_of_iso
      ((SchemeQuasicoherentDerivedCategory.ι X).mapIso e) hE

/-- The bounded part of `Dqc(X)`, defined by ambient cohomological
boundedness. -/
abbrev SchemeBoundedQuasicoherentDerivedCategory (X : Scheme.{u}) :=
  (schemeBoundedQuasicoherent X).FullSubcategory

namespace SchemeBoundedQuasicoherentDerivedCategory

variable (X : Scheme.{u})

/-- The inclusion of bounded quasi-coherent complexes into `Dqc(X)`. -/
abbrev ι : SchemeBoundedQuasicoherentDerivedCategory X ⥤
    SchemeQuasicoherentDerivedCategory X :=
  (schemeBoundedQuasicoherent X).ι

/-- Boundedness is detected after the two honest inclusions into the ambient
derived category. -/
theorem mem_iff (E : SchemeQuasicoherentDerivedCategory X) :
    schemeBoundedQuasicoherent X E ↔
      (DerivedCategory.TStructure.t (C := X.Modules)).bounded E.obj :=
  Iff.rfl

end SchemeBoundedQuasicoherentDerivedCategory

/-- The intrinsic bounded-coherent locus in `Dqc(X)`: ambient boundedness and
finite presentation of every cohomology sheaf.  On a locally Noetherian
scheme this is the expected objectwise description of `Dᵇ(Coh X)`. -/
def schemeBoundedCoherentCohomology
    (X : Scheme.{u}) :
    ObjectProperty (SchemeQuasicoherentDerivedCategory X) :=
  fun E ↦
    (DerivedCategory.TStructure.t (C := X.Modules)).bounded E.obj ∧
      ∀ n : ℤ, (SheafOfModules.isFinitePresentation X.ringCatSheaf)
        ((DerivedCategory.homologyFunctor X.Modules n).obj E.obj)

instance (X : Scheme.{u}) :
    (schemeBoundedCoherentCohomology X).IsClosedUnderIsomorphisms where
  of_iso e hE := by
    constructor
    · exact (DerivedCategory.TStructure.t (C := X.Modules)).bounded.prop_of_iso
        ((SchemeQuasicoherentDerivedCategory.ι X).mapIso e) hE.1
    · intro n
      exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
        ((DerivedCategory.homologyFunctor X.Modules n).mapIso
          ((SchemeQuasicoherentDerivedCategory.ι X).mapIso e)) (hE.2 n)

/-- The full subcategory of `Dqc(X)` with bounded coherent cohomology. -/
abbrev SchemeBoundedCoherentDqcCategory
    (X : Scheme.{u}) :=
  (schemeBoundedCoherentCohomology X).FullSubcategory

/-- Bounded coherent cohomology implies ambient boundedness. -/
theorem schemeBoundedCoherentCohomology_le_bounded
    (X : Scheme.{u}) :
    schemeBoundedCoherentCohomology X ≤ schemeBoundedQuasicoherent X :=
  fun _ hE ↦ hE.1

/-- The bounded coherent category maps concretely into the intrinsic
bounded-coherent locus in `Dqc(X)`. -/
noncomputable def boundedCoherentDerivedToDqc
    (X : Scheme.{u}) [IsLocallyNoetherian X] :
    SchemeBoundedCoherentDerivedCategory X ⥤
      SchemeBoundedCoherentDqcCategory X :=
  by
    exact (schemeBoundedCoherentCohomology X).lift
      (DerivedCategory.Bounded.ι ⋙ coherentDerivedToDqc X)
      (fun E ↦ by
        constructor
        · exact @mapDerivedCategory_bounded _ _ _ _ _ _ _ _ (Coh.ι X)
            (Coh.ι_additive X) (Coh.ι_preservesFiniteLimits X)
            (Coh.ι_preservesFiniteColimits X) E.obj E.property
        · intro n
          let H := (DerivedCategory.homologyFunctor (Coh X) n).obj E.obj
          have hfp : (SheafOfModules.isFinitePresentation X.ringCatSheaf)
              ((Coh.ι X).obj H) := H.property
          exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
            (mapDerivedCategoryHomologyIso (Coh.ι X) (Coh.ι_additive X)
              (Coh.ι_preservesFiniteLimits X) (Coh.ι_preservesFiniteColimits X)
              E.obj n).symm hfp)

/-- Forget bounded-coherent cohomology to the ambient `Dqc(X)` locus. -/
abbrev SchemeBoundedCoherentDqcCategory.ι
    (X : Scheme.{u}) :
    SchemeBoundedCoherentDqcCategory X ⥤
      SchemeQuasicoherentDerivedCategory X :=
  (schemeBoundedCoherentCohomology X).ι

/-- The perfect thick envelope maps through bounded coherent complexes into
the bounded coherent `Dqc` locus. -/
noncomputable def perfectDerivedToDqc
    (X : Scheme.{u}) [IsLocallyNoetherian X] :
    SchemePerfectDerivedCategory X ⥤
      SchemeBoundedCoherentDqcCategory X :=
  SchemePerfectDerivedCategory.toBounded X ⋙ boundedCoherentDerivedToDqc X

/-- Perfect objects inside `Dqc(X)`, defined without circular use of
compactness as the essential image of the repository's finite-locally-free
thick envelope. -/
def schemePerfectInDqc
    (X : Scheme.{u}) [IsLocallyNoetherian X] :
    ObjectProperty (SchemeQuasicoherentDerivedCategory X) :=
  (perfectDerivedToDqc X ⋙ SchemeBoundedCoherentDqcCategory.ι X).essImage

/-- The exact missing general-scheme identification behind the standard
notation `Dᵇ(Coh X) ⊂ Dqc(X)`.  The comparison field forces the equivalence
to be the concrete derived inclusion constructed above.  No unsupported
scheme is marked as satisfying this proposition. -/
structure BoundedCoherentDqcIdentification
    (X : Scheme.{u}) [IsLocallyNoetherian X] where
  /-- The bounded coherent derived category is equivalent to the intrinsic
  bounded coherent cohomology locus. -/
  equivalence : SchemeBoundedCoherentDerivedCategory X ≌
    SchemeBoundedCoherentDqcCategory X
  /-- The equivalence is the concrete exact derived inclusion. -/
  comparison : equivalence.functor ≅ boundedCoherentDerivedToDqc X

/-- Existence of the general-scheme bounded-coherent identification, kept as
an explicit proposition rather than a typeclass instance. -/
def HasBoundedCoherentDqcIdentification
    (X : Scheme.{u}) [IsLocallyNoetherian X] : Prop :=
  Nonempty (BoundedCoherentDqcIdentification X)

/-- The exact compact/perfect comparison still required by the scheme-level
A.14 realization. This file supplies no unsupported inhabitant; construction
of the needed large triangulated and coproduct structure is a separate
obligation. -/
def PerfectObjectsAreCompactInDqc
    (X : Scheme.{u}) [IsLocallyNoetherian X] : Prop :=
  schemePerfectInDqc X = ObjectProperty.compactObjects.{0}

end

end CategoryTheory.Triangulated.StabilityCondition.Families
