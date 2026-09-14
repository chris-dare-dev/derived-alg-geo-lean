import DerivedAlgGeo.CategoryTheory.Triangulated.SerreFunctor.Objects
import DerivedAlgGeo.CategoryTheory.Triangulated.SerreFunctor.Enriques
import DerivedAlgGeo.CategoryTheory.Triangulated.SerreFunctor.Classification
import DerivedAlgGeo.CategoryTheory.Triangulated.SerreFunctor.Matching
import DerivedAlgGeo.CategoryTheory.Triangulated.SerreFunctor.ProjectionObjects
import DerivedAlgGeo.CategoryTheory.Triangulated.SerreFunctor.Transport

/-! # Serre functors on a triangulated category

The shift-dependent refinements: Ext profiles and spherical/pseudoprojective
objects, the Enriques relation between `S²` and a shift, the classification it
supports, transport along an equivalence, and the semiorthogonal projection
consequences.

The `k`-linear duality data these build on, and its uniqueness, belong to
`DerivedAlgGeo.CategoryTheory.Linear.SerreFunctor`, which needs no shift. -/
