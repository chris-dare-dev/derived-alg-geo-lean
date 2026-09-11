/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.EulerCharacteristic.Additivity

/-!
# The connecting map of coherent cohomology is base-field linear

`coherentConnectingMap` is Mathlib's `Ext` connecting homomorphism, an additive map. The base
field acts on `Hⁱ(X, F)` through the endomorphism of `F` that a scalar induces
(`coherentHModule`), and the connecting map commutes with that action because the scalar
endomorphisms of the three terms of a short exact sequence form a morphism of short exact
sequences, and `extClass_naturality` says the extension class is natural in such morphisms.

So the canonical linear realization `linearCoherentH` carries a *linear* connecting map, and the
covariant `Ext` long exact sequence is exact as a sequence of `k`-vector spaces. This is the
input the dévissage on projective space needs: `Hⁱ(G) → Hⁱ(F) → Hⁱ⁺¹(K)` exact and linear, with
the outer terms finite-dimensional, forces `Hⁱ(F)` finite-dimensional. An additive exact sequence
would not do: an additive injection into a finite-dimensional space bounds nothing over an
infinite field.

`EulerCharacteristic/Additivity.lean` records the same exactness for an arbitrary
`FiniteCohomology` realization whose connecting maps are *supplied* as `LinearConnectingMaps`.
Here nothing is supplied: the realization is the canonical one and the connecting map is
`coherentConnectingMap` itself, shown linear.
-/

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Cohomology

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsVariety k X]

/-- **A scalar acts on a short complex of coherent sheaves by a morphism of short complexes.**
The three components are the scalar endomorphisms, and they commute with the differentials by
`coherentScalarAction_naturality`. -/
noncomputable def coherentScalarShortComplexHom (S : ShortComplex (Coh X)) (r : k) : S ⟶ S where
  τ₁ := coherentScalarAction X S.X₁ r
  τ₂ := coherentScalarAction X S.X₂ r
  τ₃ := coherentScalarAction X S.X₃ r
  comm₁₂ := coherentScalarAction_naturality X S.f r
  comm₂₃ := coherentScalarAction_naturality X S.g r

/-- **The connecting map commutes with the base-field action.**

Both sides are `Ext` composites: `r • x` is `x` postcomposed with the scalar endomorphism, and
the connecting map is postcomposition with the extension class. Associativity moves the two
postcompositions together and `extClass_naturality`, applied to the morphism of short exact
sequences the scalar defines, swaps their order. -/
theorem coherentConnectingMap_smul [IsLocallyNoetherian X] (S : ShortComplex (Coh X))
    (hS : S.ShortExact) (i : ℕ) (r : k) (x : (coherentH X i).obj S.X₃) :
    letI := coherentHModule k X i S.X₃
    letI := coherentHModule k X (i + 1) S.X₁
    coherentConnectingMap S hS i (r • x) = r • coherentConnectingMap S hS i x := by
  letI : HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    HasExt.standard _
  let hT := coherentSheafShortComplex_shortExact hS
  have hnat := hT.extClass_naturality hT
    ((Scheme.Modules.toSheaf X).mapShortComplex.map
      ((Coh.ι X).mapShortComplex.map (coherentScalarShortComplexHom S r)))
  change (x.comp (Abelian.Ext.mk₀ _) (add_zero i)).comp hT.extClass rfl
    = (x.comp hT.extClass rfl).comp (Abelian.Ext.mk₀ _) (add_zero (i + 1))
  refine (Abelian.Ext.comp_assoc_of_second_deg_zero x (Abelian.Ext.mk₀ _) hT.extClass
    rfl).trans ?_
  refine Eq.trans ?_ (Abelian.Ext.comp_assoc_of_third_deg_zero x hT.extClass
    (Abelian.Ext.mk₀ _) rfl).symm
  exact congrArg (fun β => x.comp β rfl) hnat.symm

/-- **The linear connecting map of the canonical realization.** -/
noncomputable def linearCoherentConnectingMap [IsLocallyNoetherian X] (S : ShortComplex (Coh X))
    (hS : S.ShortExact) (i : ℕ) :
    (linearCoherentH k X i).obj S.X₃ ⟶ (linearCoherentH k X (i + 1)).obj S.X₁ := by
  letI := coherentHModule k X i S.X₃
  letI := coherentHModule k X (i + 1) S.X₁
  exact ModuleCat.ofHom
    { toFun := coherentConnectingMap S hS i
      map_add' := map_add _
      map_smul' := fun r x => coherentConnectingMap_smul S hS i r x }

omit [IsVariety k X] in
/-- Exactness at the middle cohomology group in each degree, for the canonical realization. -/
theorem linearCoherentH_exact₂ [IsLocallyNoetherian X] (S : ShortComplex (Coh X))
    (hS : S.ShortExact) (i : ℕ) :
    Function.Exact ((linearCoherentH k X i).map S.f) ((linearCoherentH k X i).map S.g) := by
  letI : HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    HasExt.standard _
  have hExt := Abelian.Ext.covariant_sequence_exact₂'
    ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ))) (coherentSheafShortComplex_shortExact hS) i
  rw [ShortComplex.ab_exact_iff_function_exact] at hExt
  exact hExt

/-- Exactness between the quotient map in degree `i` and the connecting morphism. -/
theorem linearCoherentH_exact₃ [IsLocallyNoetherian X] (S : ShortComplex (Coh X))
    (hS : S.ShortExact) (i : ℕ) :
    Function.Exact ((linearCoherentH k X i).map S.g) (linearCoherentConnectingMap S hS i) := by
  letI : HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    HasExt.standard _
  have hExt := Abelian.Ext.covariant_sequence_exact₃'
    ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ))) (coherentSheafShortComplex_shortExact hS) i (i + 1) rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at hExt
  exact hExt

/-- Exactness between the connecting morphism out of degree `i` and the inclusion map in degree
`i + 1`. -/
theorem linearCoherentH_exact₁ [IsLocallyNoetherian X] (S : ShortComplex (Coh X))
    (hS : S.ShortExact) (i : ℕ) :
    Function.Exact (linearCoherentConnectingMap S hS i) ((linearCoherentH k X (i + 1)).map S.f) := by
  letI : HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    HasExt.standard _
  have hExt := Abelian.Ext.covariant_sequence_exact₁'
    ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ))) (coherentSheafShortComplex_shortExact hS) i (i + 1) rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at hExt
  exact hExt

/-- **The canonical realization is additive**: forgetting scalars is faithful and additive, and
the composite is `coherentH`, which is additive. -/
noncomputable instance linearCoherentH_additive (i : ℕ) : (linearCoherentH k X i).Additive :=
  haveI : (linearCoherentH k X i ⋙
      forget₂ (ModuleCat.{u + 1} k) AddCommGrpCat.{u + 1}).Additive :=
    Functor.additive_of_iso (linearCoherentHComparison k X i).symm
  Functor.additive_of_comp_faithful (linearCoherentH k X i)
    (forget₂ (ModuleCat.{u + 1} k) AddCommGrpCat.{u + 1})

end AlgebraicGeometry.Cohomology
