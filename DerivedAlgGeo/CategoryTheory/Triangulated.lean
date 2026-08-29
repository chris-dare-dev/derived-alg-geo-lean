/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.PretriangulatedAxioms
import DerivedAlgGeo.CategoryTheory.Monoidal.Triangulated
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure
import DerivedAlgGeo.CategoryTheory.Triangulated.CompactlyGenerated.Polishchuk
import DerivedAlgGeo.CategoryTheory.Triangulated.PostnikovTower
import DerivedAlgGeo.CategoryTheory.Triangulated.QuasiAbelian
import DerivedAlgGeo.CategoryTheory.Triangulated.ExtensionClosure
import DerivedAlgGeo.CategoryTheory.Triangulated.SemiorthogonalDecomposition
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.EulerForm
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.HomFiniteWitness
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai
import DerivedAlgGeo.CategoryTheory.Triangulated.BoundedHomotopyCategory
import DerivedAlgGeo.CategoryTheory.Triangulated.CohomologyObjectProperty
import DerivedAlgGeo.CategoryTheory.Triangulated.LinearCoyoneda
import DerivedAlgGeo.CategoryTheory.Triangulated.LinearOpposite
import DerivedAlgGeo.CategoryTheory.Triangulated.LinearYoneda
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement
import DerivedAlgGeo.CategoryTheory.Triangulated.Families
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition
import DerivedAlgGeo.CategoryTheory.Triangulated.CompactlyGenerated

/-! # Triangulated categories

The compatibility interface for monoidal tensor products, the
pretriangulated axioms with rotation only forward, t-structures, compact
generation, Postnikov towers, strict morphisms, semiorthogonal sequences,
extension closures, the Grothendieck group, the spherical twist on `K₀`,
Fourier--Mukai kernel functors, dg enhancements, and stability conditions on
triangulated categories.

Everything above `StabilityCondition` in this list is generic: it mentions no
stability condition, and a module that needs it does not have to import the
stability track to get it. `QuasiAbelian` and `ExtensionClosure` joined that
group in #488, on the same ground as `PostnikovTower` and `GrothendieckGroup`
in #454 — their namespace was already `CategoryTheory.Triangulated` while their
path said `StabilityCondition/Foundation/`.
-/
