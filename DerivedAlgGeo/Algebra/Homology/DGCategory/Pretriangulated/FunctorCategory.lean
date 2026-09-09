/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.NaturalTransformationCone

/-!
# Towards a pretriangulated structure on the dg category of dg functors

`DGFunctor C D` is a dg category, and `IsPretriangulated` asks it for three
things: a zero object, a shift of every object in every degree, and a cone on
every closed degree-zero morphism.

Two of the three are settled.

* **Cones.**  `HomogeneousNatTrans.ConeData.isConeOf` is the cone, built from
  the objectwise cones of a closed degree-zero dg natural transformation.  Its
  splitting is natural because the cone projections are natural, which is what
  `ConeData.fst` and `ConeData.snd` record.  This is the statement that the
  repository's objectwise twist is a cone *of functors*, which is the form
  Anno--Logvinenko's triangle `SR ⟶ Id_B ⟶ T` takes.
* **The zero object.**  It is the constant dg functor at a dg zero object of
  the target, below.

## What is still missing, and what its answer looks like

The shift.  `IsPretriangulated.exists_shift` for `DGFunctor C D` needs, for
each `F` and each `n`, a dg functor whose value at `X` is a shift of `F.obj X`
by `n`.  Choosing the objects and witnesses pointwise is immediate from
`IsPretriangulated D`; making the choice into a dg *functor* is where the
content is, and it is not the naive formula.

Writing `s X : IsShiftBy (F.obj X) n (Y X)` for the chosen witnesses, the map
on a degree-`p` morphism must be

`(F[n]).map p f = (-1)^(n * p) • (s X).inv ≫ F.map p f ≫ (s Y).hom`.

The sign is forced, not chosen.  Both `(s X).inv` and `(s Y).hom` are closed,
so the Leibniz rule leaves one term, and with the repository's convention
`δ(a ≫ b) = a ≫ δb + (-1)^|b| δa ≫ b` and `|(s Y).hom| = -n` that term carries
`(-1)^n`.  A functor must satisfy `map (p+1) (δ f) = δ (map p f)`, so the
coefficient `ε` must satisfy `ε (p+1) = (-1)^n ε p`; a constant sign cannot,
and `ε p = (-1)^(n * p)` is the solution.  With it, `map_id` is the unit law,
`map_comp` is `(-1)^(n p) (-1)^(n q) = (-1)^(n (p+q))`, and the shift witness
is the family `(s X).hom`, whose graded naturality is exactly the same sign
cancelling against `(-1)^(-n p)`.

Nothing below asserts any of that; it is written here because the derivation
is the whole of the remaining work and should not have to be redone.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u'

namespace CategoryTheory

open DGCategoryStruct DGCategory

namespace DGFunctor

variable {C : Type u} {D : Type u'} [DGCategory.{v} C] [DGCategory.{v} D]

/-- The dg functor constant at an object with vanishing dg identity.

Only a *zero* object gives a dg functor this way: `map_id` asks for
`0 = dgId Z`, which is exactly the hypothesis. -/
def constZero (Z : D) (hZ : dgId Z = 0) : DGFunctor C D where
  obj _ := Z
  map _ := 0
  map_d _ _ _ := by simp
  map_id _ := by simp [hZ]
  map_comp _ _ _ _ _ _ := by simp

@[simp]
theorem constZero_obj (Z : D) (hZ : dgId Z = 0) (X : C) :
    (constZero (C := C) Z hZ).obj X = Z :=
  rfl

-- Not `@[simp]`: the constant functor's action is the zero map by definition,
-- so `simp` reduces the left-hand side without help.
theorem constZero_map (Z : D) (hZ : dgId Z = 0) {X Y : C} (p : ℤ)
    (f : (dgHom X Y).X p) :
    (constZero (C := C) Z hZ).map p f = 0 :=
  rfl

/-- **The dg category of dg functors has a zero object**, as soon as the
target has one: the constant functor at it. -/
theorem dgId_constZero_eq_zero (Z : D) (hZ : dgId Z = 0) :
    dgId (constZero (C := C) Z hZ) = 0 := by
  apply HomogeneousNatTrans.ext
  intro X
  exact hZ

/-- The dg category of dg functors has a zero object whenever the target is
pretriangulated. -/
theorem exists_zero_dgFunctor [IsPretriangulated D] :
    ∃ Z : DGFunctor C D, dgId Z = 0 := by
  obtain ⟨Z, hZ⟩ := IsPretriangulated.exists_zero (C := D)
  exact ⟨constZero Z hZ, dgId_constZero_eq_zero Z hZ⟩

/-- **Every closed degree-zero dg natural transformation has a cone in the dg
category of dg functors**, whenever the target is pretriangulated.

This is `ConeData.isConeOf` applied to the objectwise cones the target
supplies, and it is the `exists_cone` field of a pretriangulated structure on
`DGFunctor C D`.  The remaining field is the shift; see the module
docstring. -/
theorem exists_cone_dgFunctor [IsPretriangulated D] {F G : DGFunctor C D}
    (α : (dgHom F G).X 0) (hα : α ∈ cocycles F G) :
    ∃ Z : DGFunctor C D, Nonempty (IsConeOf α Z) := by
  have hclosed : HomogeneousNatTrans.IsClosed α := by
    apply HomogeneousNatTrans.ext
    intro X
    exact congrArg (fun σ => HomogeneousNatTrans.app σ X) hα
  refine ⟨(HomogeneousNatTrans.chosenConeData α hclosed).functor,
    ⟨(HomogeneousNatTrans.chosenConeData α hclosed).isConeOf⟩⟩

end DGFunctor

end CategoryTheory
