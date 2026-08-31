/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Sites.Cech.Comparison
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.CategoryTheory.Sites.Spaces

/-!
# Choosing the injective resolution on a small site

`DerivedAlgGeo.CategoryTheory.Sites.Cech.Bicomplex` and
`DerivedAlgGeo.CategoryTheory.Sites.Cech.Comparison` thread an explicit
`InjectiveResolution F` through every construction, because no `EnoughInjectives` instance is
available for abelian sheaves over an *arbitrary* site.  That restriction is narrower than it
looks.  The pinned Mathlib derives enough injectives from `CategoryTheory.IsGrothendieckAbelian`,
and its sheaf instance requires the site to be small in the universe of the sheaf values.

Concretely, `Comparison` carries `C : Type u` with `Category.{a} C` and sheaves valued in
`AddCommGrpCat.{a}`; the missing hypothesis is exactly `u = a`, that is, `SmallCategory C`.
Every site this library computes on has that form -- in particular `Opens.grothendieckTopology X`
for a topological space `X`, where the opens form a `Type a` with `Category.{a}` structure.

So on a small site the resolution argument is redundant, and this file discharges it:
`canonicalInjectiveResolution` chooses one, and the wrappers below restate the Cech
spectral-sequence interface without an `InjectiveResolution` parameter.

Nothing here is an axiom, and no new instance enters the graph.  `enoughInjectives_of_small` is
`inferInstance` against Mathlib's existing chain

`AddCommGrpCat.{a}` Grothendieck abelian
  -> `Sheaf J AddCommGrpCat.{a}` Grothendieck abelian
  -> `Sheaf J AddCommGrpCat.{a}` has enough injectives (`@[stacks 079H]`).

The remaining Cech-to-derived boundaries recorded in `Comparison` are unaffected: identifying the
degree-zero row of the initial page with the Cech complex, and proving abutment against the named
total complex, are still open.
-/

universe h a

open CategoryTheory Category Limits Opposite

namespace CategoryTheory.Sheaf

variable {C : Type a} [SmallCategory.{a} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{a}]

/-- On a small site, abelian sheaves have enough injectives.

This is not a new instance; it names the conclusion of Mathlib's Grothendieck-abelian chain so
that the axiom audit can see it, and so that the smallness hypothesis is stated once. -/
theorem enoughInjectives_of_small :
    EnoughInjectives (Sheaf J AddCommGrpCat.{a}) :=
  inferInstance

/-- On a small site, every abelian sheaf admits an injective resolution. -/
theorem hasInjectiveResolutions_of_small :
    HasInjectiveResolutions (Sheaf J AddCommGrpCat.{a}) :=
  inferInstance

/-- The site of opens of a topological space is small, so its abelian sheaves have enough
injectives.  This is the instantiation the coherent-sheaf cohomology layer actually uses. -/
theorem enoughInjectives_opens (T : Type a) [TopologicalSpace T] :
    EnoughInjectives (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{a}) :=
  inferInstance

/-- An injective resolution chosen on a small site, rather than supplied as a hypothesis. -/
noncomputable def canonicalInjectiveResolution (F : Sheaf J AddCommGrpCat.{a}) :
    InjectiveResolution F :=
  injectiveResolution F

variable [HasExt.{h} (Sheaf J AddCommGrpCat.{a})]

/-- The cohomology of the sections of the canonical injective resolution computes `H'`.

Resolution-free form of `injectiveResolutionSectionsCohomologyAddEquivHPrime`. -/
noncomputable def canonicalSectionsCohomologyAddEquivHPrime
    (X : C) (F : Sheaf J AddCommGrpCat.{a}) (n : ℕ) :
    (injectiveResolutionSectionsComplex X (canonicalInjectiveResolution F)).homology (n : ℤ) ≃+
      F.H' n X :=
  injectiveResolutionSectionsCohomologyAddEquivHPrime X (canonicalInjectiveResolution F) n

variable [HasFiniteProducts C] {ι : Type a}

/-- The Cech bicomplex of the canonical injective resolution.

Resolution-free form of `cechInjectiveBicomplex`. -/
noncomputable def canonicalCechBicomplex (U : ι → C) (F : Sheaf J AddCommGrpCat.{a}) :
    HomologicalComplex₂ AddCommGrpCat.{a} (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  cechInjectiveBicomplex U (canonicalInjectiveResolution F)

/-- The column-filtration spectral sequence of the Cech bicomplex, with no resolution argument.

Resolution-free form of `cechInjectiveSpectralSequence`. -/
noncomputable def canonicalCechSpectralSequence (U : ι → C) (F : Sheaf J AddCommGrpCat.{a}) :
    SpectralSequence AddCommGrpCat.{a}
      (fun r ↦ ComplexShape.up' (⟨r - 1, 2 - r⟩ : ℤ × ℤ)) 2 :=
  cechInjectiveSpectralSequence U (canonicalInjectiveResolution F)

/-- The initial page of the canonical spectral sequence is vertical homology of the fixed Cech
column: `E₂^{p,q} ≅ H^q(C^{p,*})`.

Resolution-free form of `cechInjectiveInitialPageColumnHomologyIso`. -/
noncomputable def canonicalCechInitialPageColumnHomologyIso
    (U : ι → C) (F : Sheaf J AddCommGrpCat.{a}) (p q : ℤ) :
    ((canonicalCechSpectralSequence U F).page 2).X (p, q) ≅
      ((canonicalCechBicomplex U F).X p).homology q :=
  cechInjectiveInitialPageColumnHomologyIso U (canonicalInjectiveResolution F) p q

/-- Under local acyclicity, every positive-resolution-degree entry on the initial page vanishes.

Resolution-free form of `isZero_cechInjectiveInitialPage_of_isCechAcyclicFor`; the acyclicity
hypothesis is a statement about `F` alone, so no resolution appears anywhere in this signature. -/
lemma isZero_canonicalCechInitialPage_of_isCechAcyclicFor
    (U : ι → C) {F : Sheaf J AddCommGrpCat.{a}} (hacyclic : IsCechAcyclicFor U F)
    (p q : ℕ) (hq : 0 < q) :
    IsZero (((canonicalCechSpectralSequence U F).page 2).X ((p : ℤ), (q : ℤ))) :=
  isZero_cechInjectiveInitialPage_of_isCechAcyclicFor
    U (canonicalInjectiveResolution F) hacyclic p q hq

/-- Elementwise form of `isZero_canonicalCechInitialPage_of_isCechAcyclicFor`. -/
lemma subsingleton_canonicalCechInitialPage_of_isCechAcyclicFor
    (U : ι → C) {F : Sheaf J AddCommGrpCat.{a}} (hacyclic : IsCechAcyclicFor U F)
    (p q : ℕ) (hq : 0 < q) :
    Subsingleton (((canonicalCechSpectralSequence U F).page 2).X ((p : ℤ), (q : ℤ))) :=
  AddCommGrpCat.subsingleton_of_isZero
    (isZero_canonicalCechInitialPage_of_isCechAcyclicFor U hacyclic p q hq)

end CategoryTheory.Sheaf
