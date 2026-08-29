/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.Flat.Basic
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.OpenImmersionPullback

/-!
# Relative-perfect and universally-gluable complexes

This file starts the scheme-object layer of the moduli problem of relative
perfect complexes.  Its objects live in the honest quasi-coherent-cohomology
locus `SchemeQuasicoherentDerivedCategory X`, not in the derived category of
all module sheaves under a different name.

At the current Mathlib pin there is no general derived tensor product for
module sheaves.  Finite Tor amplitude is therefore expressed by the standard
local model that can be checked without such an API: around every point the
complex is represented by a bounded complex of module sheaves whose stalks
are flat over the base.  The bounds and the representing isomorphism are data,
not an arbitrary proposition supplied by a caller.

For the same reason, a geometric fiber is computed only from an explicit
globally flat model. The repository now has an interface characterizing
arbitrary pullback by its left-derived universal property, but it does not yet
construct that interface along arbitrary fiber inclusions. This is enough to
define and inhabit the zero model and to state fiberwise negative-Ext
vanishing honestly; comparison with a future K-flat construction remains a
separate theorem.
-/

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open CategoryTheory.Triangulated.StabilityCondition.Families
open scoped ZeroObject

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Scheme

/-- A module sheaf on `X` is flat over `S` when every stalk, restricted along
the local-ring map induced by `p`, is a flat module over the corresponding
stalk of `S`. -/
def Modules.IsFlatOver {X S : Scheme.{u}} (p : X ⟶ S)
    (M : X.Modules) : Prop :=
  ∀ x : X, Module.Flat (S.presheaf.stalk (p x))
    ((ModuleCat.restrictScalars (p.stalkMap x).hom).obj
      ((SchemeBaseChange.moduleStalkFunctor X x).obj M))

end Scheme

/-- The locally Noetherian cohomological criterion for pseudo-coherence:
bounded above with finitely presented cohomology in every degree.

SCOPE (2026-08-18 review, P2-12): on a locally Noetherian scheme this
criterion is pseudo-coherence; on a general scheme the two notions diverge
in both directions, and the affine family pseudofunctor instantiates this
predicate over arbitrary test algebras. Any theorem that quantifies over
non-Noetherian bases is therefore about THIS predicate, not about standard
pseudo-coherence; the #554 preservation program must either restrict its
index to the Noetherian locus or prove preservation for this criterion and
say which. -/
def schemePseudoCoherent (X : Scheme.{u}) :
    ObjectProperty (SchemeQuasicoherentDerivedCategory X) :=
  fun E ↦
    (DerivedCategory.TStructure.t (C := X.Modules)).minus E.obj ∧
      ∀ n : ℤ, (SheafOfModules.isFinitePresentation X.ringCatSheaf)
        ((DerivedCategory.homologyFunctor X.Modules n).obj E.obj)

instance schemePseudoCoherent_isClosedUnderIsomorphisms (X : Scheme.{u}) :
    (schemePseudoCoherent X).IsClosedUnderIsomorphisms where
  of_iso e hE := by
    constructor
    · exact (DerivedCategory.TStructure.t (C := X.Modules)).minus.prop_of_iso
        ((SchemeQuasicoherentDerivedCategory.ι X).mapIso e) hE.1
    · intro n
      exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
        ((DerivedCategory.homologyFunctor X.Modules n).mapIso
          ((SchemeQuasicoherentDerivedCategory.ι X).mapIso e)) (hE.2 n)

/-- The object of `Over S` obtained by restricting `p : X ⟶ S` to an open
subscheme of `X`. -/
def relativeOpenBaseChange {X S : Scheme.{u}} (p : X ⟶ S)
    (U : X.Opens) : SchemeBaseChange S :=
  Over.mk (U.ι ≫ p)

/-- The canonical open-immersion morphism from a restricted family to the
original family over `S`. -/
def relativeOpenTo {X S : Scheme.{u}} (p : X ⟶ S) (U : X.Opens) :
    relativeOpenBaseChange p U ⟶ Over.mk p :=
  Over.homMk U.ι (by rfl)

@[simp]
theorem relativeOpenTo_left {X S : Scheme.{u}} (p : X ⟶ S)
    (U : X.Opens) : (relativeOpenTo p U).left = U.ι :=
  rfl

instance relativeOpenTo_isOpenImmersion {X S : Scheme.{u}}
    (p : X ⟶ S) (U : X.Opens) :
    IsOpenImmersion (relativeOpenTo p U).left := by
  change IsOpenImmersion U.ι
  infer_instance

/-- A bounded flat local model for one object near one point.  The target of
`represents` is the actual exact derived restriction along the open immersion;
no nonexact derived pullback is used. -/
structure LocalFiniteTorAmplitudeChart {X S : Scheme.{u}} (p : X ⟶ S)
    (E : SchemeQuasicoherentDerivedCategory X) (x : X) where
  /-- An open neighbourhood on which the flat model is defined. -/
  openSubset : X.Opens
  /-- The chosen point lies in the neighbourhood. -/
  mem_openSubset : x ∈ openSubset
  /-- Lower cohomological bound for the model. -/
  lower : ℤ
  /-- Upper cohomological bound for the model. -/
  upper : ℤ
  /-- The interval of possible nonzero terms is ordered. -/
  lower_le_upper : lower ≤ upper
  /-- A complex of module sheaves on the open neighbourhood. -/
  model : CochainComplex openSubset.toScheme.Modules ℤ
  /-- The model has no terms below `lower`. -/
  strictlyGE : model.IsStrictlyGE lower
  /-- The model has no terms above `upper`. -/
  strictlyLE : model.IsStrictlyLE upper
  /-- Every term is stalkwise flat over the base. -/
  flatOverBase (i : ℤ) :
    Scheme.Modules.IsFlatOver (openSubset.ι ≫ p) (model.X i)
  /-- The model represents the exact restriction of the original object. -/
  represents : (SchemeDerivedCategory.Q openSubset.toScheme).obj model ≅
    (SchemeBaseChange.derivedPullback (relativeOpenTo p openSubset)).obj E.obj

/-- Local finite Tor amplitude over `S`, witnessed pointwise by bounded
stalkwise-flat models on actual open neighbourhoods. -/
def schemeLocallyFiniteTorAmplitudeOver {X S : Scheme.{u}} (p : X ⟶ S) :
    ObjectProperty (SchemeQuasicoherentDerivedCategory X) :=
  fun E ↦ ∀ x : X, Nonempty (LocalFiniteTorAmplitudeChart p E x)

instance schemeLocallyFiniteTorAmplitudeOver_isClosedUnderIsomorphisms
    {X S : Scheme.{u}} (p : X ⟶ S) :
    (schemeLocallyFiniteTorAmplitudeOver p).IsClosedUnderIsomorphisms where
  of_iso e hE x := by
    obtain ⟨h⟩ := hE x
    refine ⟨{
      openSubset := h.openSubset
      mem_openSubset := h.mem_openSubset
      lower := h.lower
      upper := h.upper
      lower_le_upper := h.lower_le_upper
      model := h.model
      strictlyGE := h.strictlyGE
      strictlyLE := h.strictlyLE
      flatOverBase := h.flatOverBase
      represents := h.represents ≪≫
        (SchemeBaseChange.derivedPullback
          (relativeOpenTo p h.openSubset)).mapIso
            ((SchemeQuasicoherentDerivedCategory.ι X).mapIso e) }⟩

/-- The relative-perfect predicate: `schemePseudoCoherent` objects with
locally finite Tor amplitude over the base.

The definition takes an arbitrary morphism; the intended moduli context is a
flat, locally finitely presented family, and geometric theorems state those
hypotheses where they use them rather than here (see
`SchemeRelativePerfectCategory`). The pseudo-coherence component carries the
locally Noetherian scope note on `schemePseudoCoherent`. -/
def schemeRelativePerfect {X S : Scheme.{u}} (p : X ⟶ S) :
    ObjectProperty (SchemeQuasicoherentDerivedCategory X) :=
  fun E ↦ schemePseudoCoherent X E ∧
    schemeLocallyFiniteTorAmplitudeOver p E

instance schemeRelativePerfect_isClosedUnderIsomorphisms
    {X S : Scheme.{u}} (p : X ⟶ S) :
    (schemeRelativePerfect p).IsClosedUnderIsomorphisms where
  of_iso e hE := ⟨
    (schemePseudoCoherent X).prop_of_iso e hE.1,
    (schemeLocallyFiniteTorAmplitudeOver p).prop_of_iso e hE.2⟩

/-- The full category cut out by relative perfection over `p`.  Geometric
theorems about this category state flatness, finite-presentation, and
Noetherian hypotheses where they are actually used rather than storing inert
typeclass arguments in the category abbreviation. -/
abbrev SchemeRelativePerfectCategory {X S : Scheme.{u}} (p : X ⟶ S) :=
  (schemeRelativePerfect p).FullSubcategory

/-- A global stalkwise-flat model used to compute one geometric fiber. This
does not inhabit the arbitrary left-derived pullback interface: it records the
precise model from which the displayed fiber object is computed. -/
structure GeometricFiberModel {X S : Scheme.{u}} (p : X ⟶ S)
    (E : SchemeQuasicoherentDerivedCategory X) (s : S) where
  /-- A complex representing the total object. -/
  totalModel : CochainComplex X.Modules ℤ
  /-- The total model represents `E`. -/
  represents : (SchemeDerivedCategory.Q X).obj totalModel ≅ E.obj
  /-- Every term is stalkwise flat over `S`. -/
  flatOverBase (i : ℤ) : Scheme.Modules.IsFlatOver p (totalModel.X i)

namespace GeometricFiberModel

/-- The degreewise pullback of a chosen flat model to the scheme-theoretic
fiber. -/
def fiberComplex {X S : Scheme.{u}} {p : X ⟶ S}
    {E : SchemeQuasicoherentDerivedCategory X} {s : S}
    (M : GeometricFiberModel p E s) :
    CochainComplex (p.fiber s).Modules ℤ :=
  ((Scheme.Modules.pullback (p.fiberι s)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj M.totalModel

/-- The geometric fiber object computed in the ambient derived category.
No claim identifies the ambient category with `Dqc`; quasi-coherence of this
object is a separate comparison theorem once arbitrary left-derived pullback
has been constructed. -/
def fiberObject {X S : Scheme.{u}} {p : X ⟶ S}
    {E : SchemeQuasicoherentDerivedCategory X} {s : S}
    (M : GeometricFiberModel p E s) : SchemeDerivedCategory (p.fiber s) :=
  (SchemeDerivedCategory.Q (p.fiber s)).obj M.fiberComplex

end GeometricFiberModel

/-- Explicit geometric fibers of a relative-perfect object together with
negative self-Ext vanishing on every fiber. -/
structure UniversallyGluableData {X S : Scheme.{u}} (p : X ⟶ S)
    (E : SchemeQuasicoherentDerivedCategory X) where
  /-- A flat model computing every geometric fiber. -/
  fiberModel (s : S) : GeometricFiberModel p E s
  /-- Negative self-extensions vanish on every geometric fiber. -/
  negativeExtVanishes (s : S) (n : ℤ) (hn : n < 0)
      (f : (fiberModel s).fiberObject ⟶
        (fiberModel s).fiberObject⟦n⟧) : f = 0

/-- The relative-perfect, universally-gluable locus. -/
def schemeUniversallyGluableRelativePerfect {X S : Scheme.{u}}
    (p : X ⟶ S) : ObjectProperty (SchemeQuasicoherentDerivedCategory X) :=
  fun E ↦ schemeRelativePerfect p E ∧ Nonempty (UniversallyGluableData p E)

namespace UniversallyGluableData

/-- Transport universally-gluable fiber data along an isomorphism of total
objects.  The same flat models compute the fibers; only their representing
isomorphisms change. -/
def ofIso {X S : Scheme.{u}} {p : X ⟶ S}
    {E F : SchemeQuasicoherentDerivedCategory X} (e : E ≅ F)
    (h : UniversallyGluableData p E) : UniversallyGluableData p F where
  fiberModel s := {
    totalModel := (h.fiberModel s).totalModel
    represents := (h.fiberModel s).represents ≪≫
      (SchemeQuasicoherentDerivedCategory.ι X).mapIso e
    flatOverBase := (h.fiberModel s).flatOverBase }
  negativeExtVanishes s n hn f := h.negativeExtVanishes s n hn f

end UniversallyGluableData

instance schemeUniversallyGluableRelativePerfect_isClosedUnderIsomorphisms
    {X S : Scheme.{u}} (p : X ⟶ S) :
    (schemeUniversallyGluableRelativePerfect p).IsClosedUnderIsomorphisms where
  of_iso e hE := ⟨
    (schemeRelativePerfect p).prop_of_iso e hE.1,
    hE.2.map (UniversallyGluableData.ofIso e)⟩

/-- The full category of relative-perfect universally-gluable complexes. -/
abbrev SchemeUniversallyGluableCategory {X S : Scheme.{u}} (p : X ⟶ S) :=
  (schemeUniversallyGluableRelativePerfect p).FullSubcategory

/-! ## A concrete zero model -/

/-- The zero cochain complex of module sheaves, named explicitly because the
object-level `0` notation is not exported by every derived-category import. -/
def zeroModuleComplex (X : Scheme.{u}) : CochainComplex X.Modules ℤ :=
  HomologicalComplex.zero

/-- The zero complex is a zero object. -/
theorem zeroModuleComplex_isZero (X : Scheme.{u}) :
    IsZero (zeroModuleComplex X) :=
  HomologicalComplex.isZero_zero

/-- The localized zero complex. -/
def zeroSchemeDerivedObject (X : Scheme.{u}) : SchemeDerivedCategory X :=
  (SchemeDerivedCategory.Q X).obj (zeroModuleComplex X)

/-- The localized zero complex is a zero object in the derived category. -/
theorem zeroSchemeDerivedObject_isZero (X : Scheme.{u}) :
    IsZero (zeroSchemeDerivedObject X) :=
  (SchemeDerivedCategory.Q X).map_isZero (zeroModuleComplex_isZero X)

/-- The zero complex of coherent sheaves. -/
def zeroCoherentComplex (X : Scheme.{u}) [IsLocallyNoetherian X] :
    CochainComplex (Coh X) ℤ :=
  HomologicalComplex.zero

/-- The localized zero coherent complex. -/
def zeroCoherentDerivedObject (X : Scheme.{u}) [IsLocallyNoetherian X] :
    SchemeCoherentDerivedCategory X :=
  DerivedCategory.Q.obj (zeroCoherentComplex X)

/-- The localized zero coherent complex is a zero object. -/
theorem zeroCoherentDerivedObject_isZero
    (X : Scheme.{u}) [IsLocallyNoetherian X] :
    IsZero (zeroCoherentDerivedObject X) :=
  DerivedCategory.Q.map_isZero HomologicalComplex.isZero_zero

/-- The zero coherent complex as a bounded object. -/
def zeroBoundedCoherentDerivedObject
    (X : Scheme.{u}) [IsLocallyNoetherian X] :
    SchemeBoundedCoherentDerivedCategory X :=
  ⟨zeroCoherentDerivedObject X,
    ⟨⟨0, (DerivedCategory.TStructure.t (C := Coh X)).isGE_of_isZero
      (zeroCoherentDerivedObject_isZero X) 0⟩,
     ⟨0, (DerivedCategory.TStructure.t (C := Coh X)).isLE_of_isZero
      (zeroCoherentDerivedObject_isZero X) 0⟩⟩⟩

/-- The bounded zero coherent complex is a zero object. -/
theorem zeroBoundedCoherentDerivedObject_isZero
    (X : Scheme.{u}) [IsLocallyNoetherian X] :
    IsZero (zeroBoundedCoherentDerivedObject X) :=
  IsZero.of_full_of_faithful_of_isZero DerivedCategory.Bounded.ι _
    (zeroCoherentDerivedObject_isZero X)

/-- The zero object in the honest quasi-coherent-cohomology locus. -/
def SchemeQuasicoherentDerivedCategory.zero
    (X : Scheme.{u}) [IsLocallyNoetherian X] :
    SchemeQuasicoherentDerivedCategory X :=
  (boundedCoherentDerivedToDqc X ⋙
    SchemeBoundedCoherentDqcCategory.ι X).obj
      (zeroBoundedCoherentDerivedObject X)

/-- The honest `Dqc` zero model is a zero object after forgetting to the
ambient all-sheaf derived category. -/
theorem schemeQuasicoherentDerivedCategory_zero_obj_isZero
    (X : Scheme.{u}) [IsLocallyNoetherian X] :
    IsZero (SchemeQuasicoherentDerivedCategory.zero X).obj :=
  by
    change IsZero ((coherentDerivedInclusion X).obj
      (zeroCoherentDerivedObject X))
    letI : (coherentDerivedInclusion X).Additive := by
      dsimp [coherentDerivedInclusion]
      infer_instance
    exact (coherentDerivedInclusion X).map_isZero
      (zeroCoherentDerivedObject_isZero X)

/-- The zero object is pseudo-coherent. -/
theorem schemePseudoCoherent_zero
    (X : Scheme.{u}) [IsLocallyNoetherian X] :
    schemePseudoCoherent X (SchemeQuasicoherentDerivedCategory.zero X) := by
  let Z := (boundedCoherentDerivedToDqc X).obj
    (zeroBoundedCoherentDerivedObject X)
  constructor
  · exact Z.property.1.2
  · exact Z.property.2

/-- The zero object has a local finite-Tor-amplitude chart at every point. -/
def zeroLocalFiniteTorAmplitudeChart {X S : Scheme.{u}}
    [IsLocallyNoetherian X] (p : X ⟶ S) (x : X) :
    LocalFiniteTorAmplitudeChart p
      (SchemeQuasicoherentDerivedCategory.zero X) x where
  openSubset := ⊤
  mem_openSubset := trivial
  lower := 0
  upper := 0
  lower_le_upper := le_rfl
  model := zeroModuleComplex ((⊤ : X.Opens).toScheme)
  strictlyGE := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact isZero_zero _
  strictlyLE := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact isZero_zero _
  flatOverBase i y := by
    letI : PreservesFiniteLimits
        (SchemeBaseChange.moduleStalkFunctor ((⊤ : X.Opens).toScheme) y) :=
      SchemeBaseChange.moduleStalkFunctor_preservesFiniteLimits
        ((⊤ : X.Opens).toScheme) y
    let Z :=
      (ModuleCat.restrictScalars (((⊤ : X.Opens).ι ≫ p).stalkMap y).hom).obj
        ((SchemeBaseChange.moduleStalkFunctor ((⊤ : X.Opens).toScheme) y).obj
          ((zeroModuleComplex ((⊤ : X.Opens).toScheme)).X i))
    have hZ : IsZero Z :=
      (ModuleCat.restrictScalars (((⊤ : X.Opens).ι ≫ p).stalkMap y).hom).map_isZero
        ((SchemeBaseChange.moduleStalkFunctor ((⊤ : X.Opens).toScheme) y).map_isZero
          (by dsimp [zeroModuleComplex]; exact isZero_zero _))
    letI : Subsingleton Z := ModuleCat.isZero_iff_subsingleton.mp hZ
    exact Module.Flat.of_free
  represents := IsZero.iso
    ((SchemeDerivedCategory.Q ((⊤ : X.Opens).toScheme)).map_isZero
      (zeroModuleComplex_isZero ((⊤ : X.Opens).toScheme)))
    ((SchemeBaseChange.derivedPullback
      (relativeOpenTo p ⊤)).map_isZero
        (schemeQuasicoherentDerivedCategory_zero_obj_isZero X))

/-- The zero object has locally finite Tor amplitude over every base. -/
theorem schemeLocallyFiniteTorAmplitudeOver_zero {X S : Scheme.{u}}
    [IsLocallyNoetherian X] (p : X ⟶ S) :
    schemeLocallyFiniteTorAmplitudeOver p
      (SchemeQuasicoherentDerivedCategory.zero X) :=
  fun x ↦ ⟨zeroLocalFiniteTorAmplitudeChart p x⟩

/-- The zero object is relative perfect. -/
theorem schemeRelativePerfect_zero {X S : Scheme.{u}}
    [IsLocallyNoetherian X] (p : X ⟶ S) :
    schemeRelativePerfect p (SchemeQuasicoherentDerivedCategory.zero X) :=
  ⟨schemePseudoCoherent_zero X, schemeLocallyFiniteTorAmplitudeOver_zero p⟩

/-- The zero total complex computes the zero object on every geometric
fiber. -/
def zeroGeometricFiberModel {X S : Scheme.{u}} [IsLocallyNoetherian X]
    (p : X ⟶ S) (s : S) :
    GeometricFiberModel p (SchemeQuasicoherentDerivedCategory.zero X) s where
  totalModel := zeroModuleComplex X
  represents := IsZero.iso
    ((SchemeDerivedCategory.Q X).map_isZero (zeroModuleComplex_isZero X))
    (schemeQuasicoherentDerivedCategory_zero_obj_isZero X)
  flatOverBase i x := by
    letI : PreservesFiniteLimits (SchemeBaseChange.moduleStalkFunctor X x) :=
      SchemeBaseChange.moduleStalkFunctor_preservesFiniteLimits X x
    let Z := (ModuleCat.restrictScalars (p.stalkMap x).hom).obj
      ((SchemeBaseChange.moduleStalkFunctor X x).obj
        ((zeroModuleComplex X).X i))
    have hZ : IsZero Z :=
      (ModuleCat.restrictScalars (p.stalkMap x).hom).map_isZero
        ((SchemeBaseChange.moduleStalkFunctor X x).map_isZero
          (by dsimp [zeroModuleComplex]; exact isZero_zero _))
    letI : Subsingleton Z := ModuleCat.isZero_iff_subsingleton.mp hZ
    exact Module.Flat.of_free

/-- The zero relative-perfect object is universally gluable. -/
def universallyGluableDataZero {X S : Scheme.{u}} [IsLocallyNoetherian X]
    (p : X ⟶ S) :
    UniversallyGluableData p
      (SchemeQuasicoherentDerivedCategory.zero X) where
  fiberModel := zeroGeometricFiberModel p
  negativeExtVanishes s n hn f := by
    exact ((SchemeDerivedCategory.Q (p.fiber s)).map_isZero
      (((Scheme.Modules.pullback (p.fiberι s)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map_isZero
          (zeroModuleComplex_isZero X))).eq_of_src f 0

/-- The relative-perfect universally-gluable locus is nonempty: it contains
the zero complex for every flat locally finitely presented family. -/
theorem schemeUniversallyGluableRelativePerfect_zero
    {X S : Scheme.{u}} [IsLocallyNoetherian X] (p : X ⟶ S) :
    schemeUniversallyGluableRelativePerfect p
      (SchemeQuasicoherentDerivedCategory.zero X) :=
  ⟨schemeRelativePerfect_zero p, ⟨universallyGluableDataZero p⟩⟩

end

end AlgebraicGeometry
