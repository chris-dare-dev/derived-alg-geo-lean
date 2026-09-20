/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Invertible
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Tensor.Unbounded

/-!
# A left-derived tensor interface on scheme-module complexes

## Main definitions

* `TensorAcyclicResolution` packages a functorial tensor-acyclic replacement and the
  one-sided comparison data needed for both fixed-argument universal properties.
* `LeftDerivedTensor` is the actual bifunctor on the localized derived category, with a
  counit and Mathlib's `Functor.IsLeftDerivedFunctor` field in each variable.
* `singleComplex` and `singleLeftTensorIso` identify tensoring against a degree-zero left
  factor with the induced complex functor.

## Main results

`TensorAcyclicResolution.toLeftDerivedTensor` proves both universal properties from the
resolution data. `exactLeftFunctor` and `fixedLeftComparison` expose the exact
invertible-left-factor case, while `ofTensorInverts` remains the separate genuinely
two-variable identity-resolution construction.

## Implementation notes

Mathlib's derived-functor API is single-variable only. The bifunctor interface therefore
states the universal property once for each fixed complex. The exact fixed-left comparison is
proved through the existing exact functor on module sheaves and the single-complex tensor
comparison; it does not assert that arbitrary tensor factors preserve quasi-isomorphisms.

This module owns the localization-facing interface for the unbounded tensor product.  It does not
assert a monoidal structure on either complexes or the derived category.

There are two tempting routes which are deliberately recorded here as dead ends.  First,
`MorphismProperty.IsMonoidal W` (see
`Mathlib/CategoryTheory/Localization/Monoidal/Basic.lean:44`) requires whiskering every
`W`-morphism on the left by every object.  For quasi-isomorphisms this is false: tensoring the
quasi-isomorphism `[𝒪 →ˢ 𝒪] → 𝒪/s` with `𝒪/s` produces homology in two degrees.  Thus
`IsMonoidal quasiIso` is neither proved nor carried as a field here; K-flat replacement exists
precisely because this naive localization-descent route is unavailable.  In particular, the
dependent `functorMonoidalOfComp` route (`Localization/Monoidal/Functor.lean:134`) is unavailable
too, since it requires a monoidal localized functor.

Second, `HomologicalComplex.monoidalCategory`
(`Mathlib/Algebra/Homology/Monoidal.lean:274-281`) requires
`[∀ (X₁ X₂ : GradedObject I C), GradedObject.HasTensor X₁ X₂]`.  For `I = ℤ` this asks for
coproducts over countably infinite anti-diagonals, whereas `Coh X` has only finite biproducts.
Mathlib's worked example in that file is `ChainComplex D ℕ`, whose anti-diagonals are finite;
there is no ℤ-indexed instance at this pin.  Accordingly no declaration below asserts either
of those dead routes.

`TensorAcyclicResolution` is a tensor-specific interface around the already-existing generic
K-flat localization construction.  Its two resolved-comparison fields are intentional: a
generic two-sided K-flat replacement proves the localized bifunctor, but does not by itself make
the comparison for an arbitrary fixed, non-K-flat factor invertible after resolving only the
other factor.  The missing comparison is therefore a hypothesis, not a marker or an axiom.

## References

* `Mathlib/CategoryTheory/Functor/Derived/LeftDerived.lean`
* `Mathlib/CategoryTheory/Localization/Bifunctor.lean`
* `DerivedAlgGeo/AlgebraicGeometry/DerivedCategory/Families/PullbackAcyclicResolution.lean`
* `DerivedAlgGeo/AlgebraicGeometry/Modules/Tensor/Invertible.lean`

## Tags

localization, left-derived-functor, tensor, K-flat, quasi-isomorphism
-/

namespace AlgebraicGeometry.DerivedCategory

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

/-- The complexes used by the unbounded scheme tensor interface. -/
abbrev SchemeTensorComplex (X : Scheme.{u}) := CochainComplex X.Modules ℤ

/-- The quasi-isomorphisms used by the unbounded scheme tensor interface. -/
abbrev SchemeTensorQuasiIso (X : Scheme.{u}) :
    MorphismProperty (SchemeTensorComplex X) :=
  HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ)

/-- The degree-zero complex used to expose an exact fixed left tensor factor. -/
abbrev singleComplex (X : Scheme.{u}) (L : X.Modules) : SchemeTensorComplex X :=
  (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L

private noncomputable def singleLeftTensorComponentMap (X : Scheme.{u}) (L : X.Modules)
    (K : CochainComplex X.Modules ℤ) (n i j : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (i, j) = n) :
    ((curriedTensor X.Modules).obj
        (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L).X i)).obj
      (K.X j) ⟶ ((curriedTensor X.Modules).obj L).obj (K.X n) := by
  by_cases hi : i = 0
  · subst i
    have hj : j = n := by simpa [ComplexShape.π] using h
    subst j
    exact ((curriedTensor X.Modules).map
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 L).hom).app (K.X n)
  · exact 0

private noncomputable def singleLeftTensorHom (X : Scheme.{u}) (L : X.Modules)
    (K : CochainComplex X.Modules ℤ) (n : ℤ) :
    (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L).mapBifunctor K
      (curriedTensor X.Modules) (ComplexShape.up ℤ)).X n ⟶
      ((curriedTensor X.Modules).obj L).obj (K.X n) :=
  HomologicalComplex.mapBifunctorDesc (K₁ :=
    (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L) (K₂ := K)
      (F := curriedTensor X.Modules) (c := ComplexShape.up ℤ)
      (fun i j h => singleLeftTensorComponentMap X L K n i j h)

private noncomputable def singleLeftTensorInv (X : Scheme.{u}) (L : X.Modules)
    (K : CochainComplex X.Modules ℤ) (n : ℤ) :
    ((curriedTensor X.Modules).obj L).obj (K.X n) ⟶
      (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L).mapBifunctor K
        (curriedTensor X.Modules) (ComplexShape.up ℤ)).X n :=
  ((curriedTensor X.Modules).map
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 L).inv).app (K.X n) ≫
    HomologicalComplex.ιMapBifunctor
      ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L) K
      (curriedTensor X.Modules) (ComplexShape.up ℤ) 0 n n (by
        dsimp [ComplexShape.π]
        omega)

private lemma singleLeftTensorHom_zero (X : Scheme.{u}) (L : X.Modules)
    (K : CochainComplex X.Modules ℤ) (n : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (0, n) = n) :
    ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L).ιMapBifunctor K
        (curriedTensor X.Modules) (ComplexShape.up ℤ) 0 n n h ≫
        singleLeftTensorHom X L K n =
      ((curriedTensor X.Modules).map
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 L).hom).app (K.X n) := by
  dsimp only [singleLeftTensorHom]
  rw [HomologicalComplex.ι_mapBifunctorDesc
    (K₁ := (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L)
    (K₂ := K) (F := curriedTensor X.Modules) (c := ComplexShape.up ℤ)
    (fun i j h => singleLeftTensorComponentMap X L K n i j h) 0 n h]
  dsimp [singleLeftTensorComponentMap]

private noncomputable def singleLeftTensorDegreeIso (X : Scheme.{u}) (L : X.Modules)
    (K : CochainComplex X.Modules ℤ) (n : ℤ) :
    (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L).mapBifunctor K
      (curriedTensor X.Modules) (ComplexShape.up ℤ)).X n ≅
      ((curriedTensor X.Modules).obj L).obj (K.X n) := by
  refine ⟨singleLeftTensorHom X L K n, singleLeftTensorInv X L K n, ?_, ?_⟩
  · apply HomologicalComplex.mapBifunctor.hom_ext
    intro i j hij
    by_cases hi : i = 0
    · subst i
      have hj : j = n := by simpa [ComplexShape.π] using hij
      subst j
      calc
        _ = ((curriedTensor X.Modules).map
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 L).hom).app
              (K.X n) ≫ singleLeftTensorInv X L K n := by
          exact congrArg (fun f => f ≫ singleLeftTensorInv X L K n)
            (singleLeftTensorHom_zero X L K n hij)
        _ = _ := by
          dsimp only [singleLeftTensorInv]
          rw [← Category.assoc, ← NatTrans.comp_app, ← (curriedTensor X.Modules).map_comp,
            Iso.hom_inv_id, (curriedTensor X.Modules).map_id, NatTrans.id_app]
          simp only [Category.id_comp, Category.comp_id]
    · have hzero : IsZero (((curriedTensor X.Modules).obj
          (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L).X i)).obj
          (K.X j)) := by
        exact Functor.map_isZero ((curriedTensor X.Modules).flip.obj (K.X j))
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 L i hi)
      exact hzero.eq_of_src _ _
  · calc
      _ = ((curriedTensor X.Modules).map
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 L).inv).app
            (K.X n) ≫
          (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L).ιMapBifunctor K
            (curriedTensor X.Modules) (ComplexShape.up ℤ) 0 n n _) ≫
          singleLeftTensorHom X L K n := by
        dsimp only [singleLeftTensorInv]
        exact Category.assoc _ _ _
      _ = ((curriedTensor X.Modules).map
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 L).inv).app
            (K.X n) ≫
          ((curriedTensor X.Modules).map
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 L).hom).app
            (K.X n) := by
        exact congrArg
          (fun f =>
            ((curriedTensor X.Modules).map
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 L).inv).app
              (K.X n) ≫ f)
          (singleLeftTensorHom_zero X L K n (by
            dsimp [ComplexShape.π]
            omega))
      _ = _ := by
        rw [← NatTrans.comp_app, ← (curriedTensor X.Modules).map_comp,
          Iso.inv_hom_id, (curriedTensor X.Modules).map_id, NatTrans.id_app]

@[reassoc]
private lemma singleLeftTensorDegreeIso_hom_zero (X : Scheme.{u}) (L : X.Modules)
    (K : CochainComplex X.Modules ℤ) (n : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (0, n) = n) :
    ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L).ιMapBifunctor K
        (curriedTensor X.Modules) (ComplexShape.up ℤ) 0 n n h ≫
        (singleLeftTensorDegreeIso X L K n).hom =
      ((curriedTensor X.Modules).map
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 L).hom).app (K.X n) := by
  exact singleLeftTensorHom_zero X L K n h

private noncomputable def singleLeftTensorComponent (X : Scheme.{u}) (L : X.Modules)
    (K : CochainComplex X.Modules ℤ) :
    ((Scheme.Modules.totalTensor X).obj
      ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L)).obj K ≅
      (((curriedTensor X.Modules).obj L).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K := by
  refine HomologicalComplex.Hom.isoOfComponents (fun n => ?_) ?_
  · exact singleLeftTensorDegreeIso X L K n
  · intro i j hij
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i₁ i₂ hsum
    by_cases hi : i₁ = 0
    · subst i₁
      have hi₂ : i₂ = i := by simpa [ComplexShape.π] using hsum
      subst i₂
      change
        (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L).ιMapBifunctor K
          (curriedTensor X.Modules) (ComplexShape.up ℤ) 0 i i hsum) ≫
            (singleLeftTensorDegreeIso X L K i).hom ≫
              ((curriedTensor X.Modules).obj L).map (K.d i j) =
        (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L).ιMapBifunctor K
          (curriedTensor X.Modules) (ComplexShape.up ℤ) 0 i i hsum) ≫
            (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L).mapBifunctor K
              (curriedTensor X.Modules) (ComplexShape.up ℤ)).d i j ≫
              (singleLeftTensorDegreeIso X L K j).hom
      rw [singleLeftTensorDegreeIso_hom_zero_assoc X L K i hsum]
      rw [HomologicalComplex.mapBifunctor.d_eq]
      simp only [Preadditive.add_comp, Preadditive.comp_add]
      rw [HomologicalComplex.mapBifunctor.ι_D₁_assoc,
        HomologicalComplex.mapBifunctor.ι_D₂_assoc]
      have h01 : (ComplexShape.up ℤ).Rel 0 1 := by
        exact ComplexShape.up_mk 0 1 (by omega)
      have h1 : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (1, i) = j := by
        have hij' : i + 1 = j := by
          simpa [ComplexShape.up, ComplexShape.up'] using hij
        change (1 : ℤ) + i = j
        omega
      have h2 : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (0, j) = j := by
        change (0 : ℤ) + j = j
        omega
      rw [HomologicalComplex.mapBifunctor.d₁_eq
        (K₁ := (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L)
        (K₂ := K) (F := curriedTensor X.Modules) (c := ComplexShape.up ℤ) h01 i j h1]
      rw [HomologicalComplex.mapBifunctor.d₂_eq
        (K₁ := (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L)
        (K₂ := K) (F := curriedTensor X.Modules) (c := ComplexShape.up ℤ) 0 hij j h2]
      simp only [HomologicalComplex.single_obj_d, Functor.map_zero, zero_app,
        zero_comp, smul_zero, zero_add]
      have hε : ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (0, i) = 1 := by
        change (ComplexShape.up ℤ).ε 0 = 1
        exact ComplexShape.ε_zero (c := ComplexShape.up ℤ)
      rw [hε, one_smul]
      calc
        _ = ((curriedTensor X.Modules).obj
              (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L).X 0)).map
              (K.d i j) ≫
            ((curriedTensor X.Modules).map
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 L).hom).app
              (K.X j) :=
          (((curriedTensor X.Modules).map
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 L).hom).naturality
              (K.d i j)).symm
        _ = (((curriedTensor X.Modules).obj
              (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L).X 0)).map
              (K.d i j) ≫
            ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L).ιMapBifunctor K
              (curriedTensor X.Modules) (ComplexShape.up ℤ) 0 j j h2) ≫
            (singleLeftTensorDegreeIso X L K j).hom := by
          calc
            _ = ((curriedTensor X.Modules).obj
                  (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L).X 0)).map
                  (K.d i j) ≫
                (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L).ιMapBifunctor K
                  (curriedTensor X.Modules) (ComplexShape.up ℤ) 0 j j h2 ≫
                  (singleLeftTensorDegreeIso X L K j).hom) :=
              (congrArg
                (fun f ↦ ((curriedTensor X.Modules).obj
                  (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L).X 0)).map
                  (K.d i j) ≫ f)
                (singleLeftTensorDegreeIso_hom_zero X L K j h2)).symm
            _ = _ := (Category.assoc _ _ _).symm
    · have hzero : IsZero (((curriedTensor X.Modules).obj
          (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L).X i₁)).obj
          (K.X i₂)) := by
        exact Functor.map_isZero ((curriedTensor X.Modules).flip.obj (K.X i₂))
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 L i₁ hi)
      exact hzero.eq_of_src _ _

/-- The comparison between tensoring by a degree-zero complex and the corresponding fixed-left
functor on complexes.  The component proof uses the actual total-complex coproduct and is natural
in the remaining complex argument; it does not assume that arbitrary tensor factors preserve
quasi-isomorphisms. -/
noncomputable def singleLeftTensorIso (X : Scheme.{u}) (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L)] :
    (Scheme.Modules.totalTensor X).obj (singleComplex X L) ≅
      (Scheme.Modules.tensorLeftFunctor L).mapHomologicalComplex (ComplexShape.up ℤ) := by
  change (Scheme.Modules.totalTensor X).obj (singleComplex X L) ≅
    (((curriedTensor X.Modules).obj L).mapHomologicalComplex (ComplexShape.up ℤ))
  refine NatIso.ofComponents (fun K ↦ singleLeftTensorComponent X L K) ?_
  intro K K' f
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hsum
  change
    ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L).ιMapBifunctor K
        (curriedTensor X.Modules) (ComplexShape.up ℤ) i j n hsum ≫
      (((Scheme.Modules.totalTensor X).obj (singleComplex X L)).map f).f n ≫
      (singleLeftTensorComponent X L K').hom.f n =
    ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L).ιMapBifunctor K
        (curriedTensor X.Modules) (ComplexShape.up ℤ) i j n hsum ≫
      (singleLeftTensorComponent X L K).hom.f n ≫
      ((((curriedTensor X.Modules).obj L).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f).f n
  change
    ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L).ιMapBifunctor K
        (curriedTensor X.Modules) (ComplexShape.up ℤ) i j n hsum ≫
      (HomologicalComplex.mapBifunctorMap
        (K₁ := (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L)
        (K₂ := K) (L₁ := (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L)
        (L₂ := K') (f₁ := 𝟙 _) (f₂ := f) (F := curriedTensor X.Modules)
        (c := ComplexShape.up ℤ)).f n ≫
      (singleLeftTensorDegreeIso X L K' n).hom =
    ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L).ιMapBifunctor K
        (curriedTensor X.Modules) (ComplexShape.up ℤ) i j n hsum ≫
      (singleLeftTensorDegreeIso X L K n).hom ≫
      ((curriedTensor X.Modules).obj L).map (f.f n)
  by_cases hi : i = 0
  · subst i
    have hj : j = n := by simpa [ComplexShape.π] using hsum
    subst j
    rw [← Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
    simp only [HomologicalComplex.id_f]
    have hId :
        ((curriedTensor X.Modules).map
          (𝟙 (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L).X 0))).app
          (K.X n) =
        𝟙 (((curriedTensor X.Modules).obj
          (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L).X 0)).obj
          (K.X n)) := by
      simpa only [NatTrans.id_app] using congrArg (fun η => η.app (K.X n))
        ((curriedTensor X.Modules).map_id
          (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L).X 0))
    rw [hId, Category.id_comp]
    calc
      _ = ((curriedTensor X.Modules).obj
            (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L).X 0)).map
            (f.f n) ≫
          (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L).ιMapBifunctor K'
            (curriedTensor X.Modules) (ComplexShape.up ℤ) 0 n n hsum ≫
            (singleLeftTensorDegreeIso X L K' n).hom) := Category.assoc _ _ _
      _ = ((curriedTensor X.Modules).obj
            (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L).X 0)).map
            (f.f n) ≫
          ((curriedTensor X.Modules).map
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 L).hom).app
            (K'.X n) :=
        congrArg
          (fun g => ((curriedTensor X.Modules).obj
            (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L).X 0)).map
            (f.f n) ≫ g)
          (singleLeftTensorDegreeIso_hom_zero X L K' n hsum)
      _ = ((curriedTensor X.Modules).map
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 L).hom).app
            (K.X n) ≫ ((curriedTensor X.Modules).obj L).map (f.f n) :=
        (((curriedTensor X.Modules).map
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 L).hom).naturality
            (f.f n))
      _ = (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L).ιMapBifunctor K
            (curriedTensor X.Modules) (ComplexShape.up ℤ) 0 n n hsum ≫
            (singleLeftTensorDegreeIso X L K n).hom) ≫
          ((curriedTensor X.Modules).obj L).map (f.f n) :=
        (congrArg (fun g => g ≫ ((curriedTensor X.Modules).obj L).map (f.f n))
          (singleLeftTensorDegreeIso_hom_zero X L K n hsum)).symm
  · have hzero : IsZero (((curriedTensor X.Modules).obj
        (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj L).X i)).obj
        (K.X j)) := by
      exact Functor.map_isZero ((curriedTensor X.Modules).flip.obj (K.X j))
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 L i hi)
    exact hzero.eq_of_src _ _

/-- The derived functor induced by tensoring on the left with an invertible module sheaf. -/
noncomputable def exactLeftFunctor (X : Scheme.{u}) (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L)] :
    SchemeDerivedCategory X ⥤ SchemeDerivedCategory X :=
  (Scheme.Modules.tensorLeftFunctor L).mapDerivedCategory

/-- The counit comparing the exact fixed-left derived functor with total tensor on a degree-zero
left factor. -/
noncomputable def exactLeftCounit (X : Scheme.{u}) (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L)] :
  (SchemeDerivedCategory.Q X) ⋙ exactLeftFunctor X L ⟶
      (Scheme.Modules.totalTensor X).obj (singleComplex X L) ⋙ SchemeDerivedCategory.Q X :=
  (Scheme.Modules.tensorLeftFunctor L).mapDerivedCategoryFactors.hom ≫
    (Functor.isoWhiskerRight (singleLeftTensorIso X L).symm (SchemeDerivedCategory.Q X)).hom

noncomputable instance exactLeftCounit_isIso (X : Scheme.{u}) (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L)] :
    IsIso (exactLeftCounit X L) := by
  dsimp [exactLeftCounit]
  infer_instance

/-- The exact fixed-left adapter is a left-derived functor for the total tensor restricted to a
degree-zero invertible left factor. -/
theorem exactLeftIsLeftDerived (X : Scheme.{u}) (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L)] :
    (exactLeftFunctor X L).IsLeftDerivedFunctor
      (exactLeftCounit X L) (SchemeTensorQuasiIso X) :=
  Functor.isLeftDerivedFunctor_of_inverts
    (SchemeTensorQuasiIso X) (exactLeftFunctor X L)
    (asIso (exactLeftCounit X L))

/-- A tensor-acyclic replacement of complexes of `𝒪_X`-modules.

The first four fields are the functorial replacement, its quasi-isomorphic comparison, and the
two-sided localization-inversion datum needed by `Localization.lift₂`.  The last two fields are
the one-sided acyclicity needed for the two fixed-argument left-derived universal properties.
They are stronger than the generic `KFlatResolution` fields in exactly the place where a fixed
arbitrary tensor factor need not preserve quasi-isomorphisms. -/
structure TensorAcyclicResolution (X : Scheme.{u}) where
  /-- Functorial replacement of complexes. -/
  resolution : SchemeTensorComplex X ⥤ SchemeTensorComplex X
  /-- Comparison from the replacement to the original complex. -/
  comparison : resolution ⟶ 𝟭 (SchemeTensorComplex X)
  /-- Every comparison component is a quasi-isomorphism. -/
  comparison_quasiIso (K : SchemeTensorComplex X) :
    SchemeTensorQuasiIso X (comparison.app K)
  /-- Resolving both inputs makes total tensor invert quasi-isomorphisms after localization. -/
  tensor_inverts :
    MorphismProperty.IsInvertedBy₂ (SchemeTensorQuasiIso X) (SchemeTensorQuasiIso X)
      (resolution ⋙ Scheme.Modules.totalTensor X ⋙
        (Functor.whiskeringLeft _ _ _).obj resolution ⋙
        (Functor.whiskeringRight _ _ _).obj (SchemeDerivedCategory.Q X))
  /-- The comparison is acyclic for a fixed first argument after resolving the second twice. -/
  left_resolved_comparison_isIso (K L : SchemeTensorComplex X) :
    IsIso ((SchemeDerivedCategory.Q X).map
      (((Scheme.Modules.totalTensor X).map (comparison.app K)).app
          (resolution.obj (resolution.obj L)) ≫
        ((Scheme.Modules.totalTensor X).obj K).map
          (comparison.app (resolution.obj L))))
  /-- The comparison is acyclic for a fixed second argument after resolving the first. -/
  right_resolved_comparison_isIso (K L : SchemeTensorComplex X) :
    IsIso ((SchemeDerivedCategory.Q X).map
      (((Scheme.Modules.totalTensor X).map (comparison.app (resolution.obj K))).app
          (resolution.obj L) ≫
        ((Scheme.Modules.totalTensor X).obj (resolution.obj K)).map
          (comparison.app L)))

namespace TensorAcyclicResolution

variable {X : Scheme.{u}}

/-- The resolved tensor functor belonging to an acyclic resolution. -/
def resolvedTensor (R : TensorAcyclicResolution X) :
    SchemeTensorComplex X ⥤ SchemeTensorComplex X ⥤ SchemeDerivedCategory X :=
  R.resolution ⋙ Scheme.Modules.totalTensor X ⋙
    (Functor.whiskeringLeft _ _ _).obj R.resolution ⋙
    (Functor.whiskeringRight _ _ _).obj (SchemeDerivedCategory.Q X)

/-- The comparison component with the identity functor normalized. -/
def comparisonApp (R : TensorAcyclicResolution X) (K : SchemeTensorComplex X) :
    R.resolution.obj K ⟶ K :=
  R.comparison.app K

/-- Naturality of the normalized replacement-to-identity comparison, used below to move a map
through the resolved tensor before applying the localization comparison. -/
@[reassoc]
lemma comparisonApp_naturality (R : TensorAcyclicResolution X)
    {K L : SchemeTensorComplex X} (f : K ⟶ L) :
    R.resolution.map f ≫ R.comparisonApp L = R.comparisonApp K ≫ f := by
  simpa only [comparisonApp, Functor.id_obj, Functor.id_map] using R.comparison.naturality f

/-- The comparison from resolved total tensor to ordinary total tensor followed by localization. -/
def resolvedTensorComparison (R : TensorAcyclicResolution X) :
    R.resolvedTensor ⟶
      Scheme.Modules.totalTensor X ⋙
        (Functor.whiskeringRight _ _ _).obj (SchemeDerivedCategory.Q X) where
  app K :=
    { app := fun L ↦ (SchemeDerivedCategory.Q X).map
        (((Scheme.Modules.totalTensor X).map (R.comparisonApp K)).app
            (R.resolution.obj L) ≫
          ((Scheme.Modules.totalTensor X).obj K).map (R.comparisonApp L))
      naturality := fun {L M} f ↦ by
        change (SchemeDerivedCategory.Q X).map
              (((Scheme.Modules.totalTensor X).obj (R.resolution.obj K)).map
                (R.resolution.map f)) ≫
            (SchemeDerivedCategory.Q X).map
              (((Scheme.Modules.totalTensor X).map (R.comparisonApp K)).app
                  (R.resolution.obj M) ≫
                ((Scheme.Modules.totalTensor X).obj K).map (R.comparisonApp M)) =
          (SchemeDerivedCategory.Q X).map
              (((Scheme.Modules.totalTensor X).map (R.comparisonApp K)).app
                  (R.resolution.obj L) ≫
                ((Scheme.Modules.totalTensor X).obj K).map (R.comparisonApp L)) ≫
            (SchemeDerivedCategory.Q X).map
              (((Scheme.Modules.totalTensor X).obj K).map f)
        rw [← Functor.map_comp, ← Functor.map_comp]
        congr 1
        simp only [Category.assoc, NatTrans.naturality_assoc, ← Functor.map_comp]
        rw [R.comparisonApp_naturality] }
  naturality {K L} f := by
    ext M
    change (SchemeDerivedCategory.Q X).map
          (((Scheme.Modules.totalTensor X).map (R.resolution.map f)).app
              (R.resolution.obj M)) ≫
        (SchemeDerivedCategory.Q X).map
          (((Scheme.Modules.totalTensor X).map (R.comparisonApp L)).app
              (R.resolution.obj M) ≫
            ((Scheme.Modules.totalTensor X).obj L).map (R.comparisonApp M)) =
      (SchemeDerivedCategory.Q X).map
          (((Scheme.Modules.totalTensor X).map (R.comparisonApp K)).app
              (R.resolution.obj M) ≫
            ((Scheme.Modules.totalTensor X).obj K).map (R.comparisonApp M)) ≫
        (SchemeDerivedCategory.Q X).map
          (((Scheme.Modules.totalTensor X).map f).app M)
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    rw [← Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp,
      R.comparisonApp_naturality]
    simp only [Functor.map_comp, NatTrans.comp_app]
    simp only [Category.assoc]
    rw [(Scheme.Modules.totalTensor X).map f |>.naturality]

/-- The bifunctor on the derived category obtained by resolving both variables. -/
def derivedTensor (R : TensorAcyclicResolution X) :
    SchemeDerivedCategory X ⥤ SchemeDerivedCategory X ⥤ SchemeDerivedCategory X :=
  Localization.lift₂ R.resolvedTensor R.tensor_inverts
    (SchemeDerivedCategory.Q X) (SchemeDerivedCategory.Q X)

/-- Pulling the derived tensor back to complexes recovers the resolved tensor. -/
def derivedTensorFactors (R : TensorAcyclicResolution X) :
    (((Functor.whiskeringLeft₂ (SchemeDerivedCategory X)).obj
        (SchemeDerivedCategory.Q X)).obj (SchemeDerivedCategory.Q X)).obj
          R.derivedTensor ≅ R.resolvedTensor := by
  change
    (((Functor.whiskeringLeft₂ (SchemeDerivedCategory X)).obj
        (SchemeDerivedCategory.Q X)).obj (SchemeDerivedCategory.Q X)).obj
        (Localization.lift₂ R.resolvedTensor R.tensor_inverts
          (SchemeDerivedCategory.Q X) (SchemeDerivedCategory.Q X)) ≅ R.resolvedTensor
  exact Localization.Lifting₂.iso (SchemeDerivedCategory.Q X) (SchemeDerivedCategory.Q X)
    (SchemeTensorQuasiIso X) (SchemeTensorQuasiIso X) R.resolvedTensor
    (Localization.lift₂ R.resolvedTensor R.tensor_inverts
      (SchemeDerivedCategory.Q X) (SchemeDerivedCategory.Q X))

/-- The counit from the localized derived tensor to degreewise total tensor. -/
def counit (R : TensorAcyclicResolution X) :
    (((Functor.whiskeringLeft₂ (SchemeDerivedCategory X)).obj
        (SchemeDerivedCategory.Q X)).obj (SchemeDerivedCategory.Q X)).obj
          R.derivedTensor ⟶
      Scheme.Modules.totalTensor X ⋙
        (Functor.whiskeringRight _ _ _).obj (SchemeDerivedCategory.Q X) :=
  R.derivedTensorFactors.hom ≫ R.resolvedTensorComparison

/-- The localization comparison induced by the quasi-isomorphic replacement. -/
private def localizationComparison (R : TensorAcyclicResolution X) :
    R.resolution ⋙ SchemeDerivedCategory.Q X ≅ SchemeDerivedCategory.Q X := by
  refine NatIso.ofComponents
    (fun K ↦ by
      exact @CategoryTheory.asIso _ _ _ _ _
        (Localization.inverts (SchemeDerivedCategory.Q X) (SchemeTensorQuasiIso X)
          (R.comparison.app K) (R.comparison_quasiIso K))) ?_
  intro K L f
  change (SchemeDerivedCategory.Q X).map (R.resolution.map f) ≫
      (SchemeDerivedCategory.Q X).map (R.comparison.app L) =
    (SchemeDerivedCategory.Q X).map (R.comparison.app K) ≫
      (SchemeDerivedCategory.Q X).map f
  have hc : R.resolution.map f ≫ R.comparison.app L =
      R.comparison.app K ≫ f := by
    simpa only [Functor.id_map] using! R.comparison.naturality f
  simpa only [← Functor.map_comp] using!
    congrArg (fun k ↦ (SchemeDerivedCategory.Q X).map k) hc

private def resolvedCounitIso (R : TensorAcyclicResolution X)
    {G : SchemeDerivedCategory X ⥤ SchemeDerivedCategory X}
    {F : SchemeTensorComplex X ⥤ SchemeDerivedCategory X}
    (α : (SchemeDerivedCategory.Q X) ⋙ G ⟶ F)
    (hα : ∀ K : SchemeTensorComplex X, IsIso (α.app (R.resolution.obj K))) :
    R.resolution ⋙ (SchemeDerivedCategory.Q X) ⋙ G ≅ R.resolution ⋙ F := by
  refine NatIso.ofComponents
    (fun K ↦ @CategoryTheory.asIso _ _ _ _ _ (hα K)) ?_
  intro K L f
  change (SchemeDerivedCategory.Q X ⋙ G).map (R.resolution.map f) ≫
      α.app (R.resolution.obj L) =
    α.app (R.resolution.obj K) ≫ F.map (R.resolution.map f)
  exact α.naturality (R.resolution.map f)

private def whiskeredLift (R : TensorAcyclicResolution X)
    {G : SchemeDerivedCategory X ⥤ SchemeDerivedCategory X}
    {F : SchemeTensorComplex X ⥤ SchemeDerivedCategory X}
    (α : (SchemeDerivedCategory.Q X) ⋙ G ⟶ F)
    (hα : ∀ K : SchemeTensorComplex X, IsIso (α.app (R.resolution.obj K)))
    (H : SchemeDerivedCategory X ⥤ SchemeDerivedCategory X)
    (β : (SchemeDerivedCategory.Q X) ⋙ H ⟶ F) :
    (SchemeDerivedCategory.Q X) ⋙ H ⟶ (SchemeDerivedCategory.Q X) ⋙ G :=
  (Functor.isoWhiskerRight (localizationComparison R) H).inv ≫
    (Functor.associator R.resolution (SchemeDerivedCategory.Q X) H).hom ≫
    Functor.whiskerLeft R.resolution β ≫
    (resolvedCounitIso R α hα).inv ≫
    (Functor.isoWhiskerRight (localizationComparison R) G).hom

private def lift (R : TensorAcyclicResolution X)
    {G : SchemeDerivedCategory X ⥤ SchemeDerivedCategory X}
    {F : SchemeTensorComplex X ⥤ SchemeDerivedCategory X}
    (α : (SchemeDerivedCategory.Q X) ⋙ G ⟶ F)
    (hα : ∀ K : SchemeTensorComplex X, IsIso (α.app (R.resolution.obj K)))
    (H : SchemeDerivedCategory X ⥤ SchemeDerivedCategory X)
    (β : (SchemeDerivedCategory.Q X) ⋙ H ⟶ F) : H ⟶ G := by
  letI := Localization.full_whiskeringLeft
    (SchemeDerivedCategory.Q X) (SchemeTensorQuasiIso X) (SchemeDerivedCategory X)
  exact ((Functor.whiskeringLeft _ _ _).obj (SchemeDerivedCategory.Q X)).preimage
    (whiskeredLift R α hα H β)

@[reassoc]
private lemma whiskerLeft_lift (R : TensorAcyclicResolution X)
    {G : SchemeDerivedCategory X ⥤ SchemeDerivedCategory X}
    {F : SchemeTensorComplex X ⥤ SchemeDerivedCategory X}
    (α : (SchemeDerivedCategory.Q X) ⋙ G ⟶ F)
    (hα : ∀ K : SchemeTensorComplex X, IsIso (α.app (R.resolution.obj K)))
    (H : SchemeDerivedCategory X ⥤ SchemeDerivedCategory X)
    (β : (SchemeDerivedCategory.Q X) ⋙ H ⟶ F) :
    Functor.whiskerLeft (SchemeDerivedCategory.Q X) (lift R α hα H β) =
      whiskeredLift R α hα H β := by
  letI := Localization.full_whiskeringLeft
    (SchemeDerivedCategory.Q X) (SchemeTensorQuasiIso X) (SchemeDerivedCategory X)
  apply ((Functor.whiskeringLeft _ _ _).obj (SchemeDerivedCategory.Q X)).map_preimage

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
private lemma whiskeredLift_fac (R : TensorAcyclicResolution X)
    {G : SchemeDerivedCategory X ⥤ SchemeDerivedCategory X}
    {F : SchemeTensorComplex X ⥤ SchemeDerivedCategory X}
    (α : (SchemeDerivedCategory.Q X) ⋙ G ⟶ F)
    (hα : ∀ K : SchemeTensorComplex X, IsIso (α.app (R.resolution.obj K)))
    (H : SchemeDerivedCategory X ⥤ SchemeDerivedCategory X)
    (β : (SchemeDerivedCategory.Q X) ⋙ H ⟶ F) :
    whiskeredLift R α hα H β ≫ α = β := by
  ext K
  change (whiskeredLift R α hα H β).app K ≫ α.app K = β.app K
  apply (cancel_epi (H.map ((localizationComparison R).hom.app K))).mp
  have hβ : H.map ((SchemeDerivedCategory.Q X).map (R.comparison.app K)) ≫
      β.app K = β.app (R.resolution.obj K) ≫ F.map (R.comparison.app K) := by
    simpa only [Functor.comp_map, Functor.id_obj] using!
      β.naturality (R.comparison.app K)
  have hα' : G.map ((SchemeDerivedCategory.Q X).map (R.comparison.app K)) ≫
      α.app K = α.app (R.resolution.obj K) ≫ F.map (R.comparison.app K) := by
    simpa only [Functor.comp_map, Functor.id_obj] using!
      α.naturality (R.comparison.app K)
  have hH : H.map ((localizationComparison R).hom.app K) ≫
      H.map ((localizationComparison R).inv.app K) = 𝟙 _ := by
    rw [← H.map_comp, (localizationComparison R).hom_inv_id_app, H.map_id]
  have hloc : H.map ((localizationComparison R).hom.app K) ≫
      (whiskeredLift R α hα H β).app K =
        β.app (R.resolution.obj K) ≫
          (resolvedCounitIso R α hα).inv.app K ≫
            G.map ((localizationComparison R).hom.app K) := by
    dsimp [whiskeredLift]
    rw [← Category.assoc, hH, Category.id_comp]
    simp
  have hlocComparison :
      G.map ((localizationComparison R).hom.app K) ≫ α.app K =
        α.app (R.resolution.obj K) ≫ F.map (R.comparison.app K) := by
    simpa only [localizationComparison, NatIso.ofComponents_hom_app,
      CategoryTheory.asIso_hom,
      Functor.comp_obj] using hα'
  have hcounit :
      (resolvedCounitIso R α hα).inv.app K ≫ α.app (R.resolution.obj K) = 𝟙 _ := by
    dsimp [resolvedCounitIso]
    simp
  have hlocα :
      H.map ((localizationComparison R).hom.app K) ≫
          ((whiskeredLift R α hα H β).app K ≫ α.app K) =
        (β.app (R.resolution.obj K) ≫
          (resolvedCounitIso R α hα).inv.app K ≫
            G.map ((localizationComparison R).hom.app K)) ≫ α.app K := by
    simpa only [Category.assoc] using congrArg
      (fun k ↦ k ≫ α.app K) hloc
  have hrest :
      (β.app (R.resolution.obj K) ≫
        (resolvedCounitIso R α hα).inv.app K ≫
          G.map ((localizationComparison R).hom.app K)) ≫ α.app K =
        β.app (R.resolution.obj K) ≫ F.map (R.comparison.app K) := by
    simp only [Category.assoc]
    rw [hlocComparison]
    rw [← Category.assoc ((resolvedCounitIso R α hα).inv.app K)
      (α.app (R.resolution.obj K)) (F.map (R.comparison.app K))]
    rw [hcounit, Category.id_comp]
  rw [hlocα, hrest]
  simpa only [localizationComparison, NatIso.ofComponents_hom_app,
    CategoryTheory.asIso_hom,
    Functor.comp_obj] using hβ.symm

@[reassoc]
private lemma lift_fac (R : TensorAcyclicResolution X)
    {G : SchemeDerivedCategory X ⥤ SchemeDerivedCategory X}
    {F : SchemeTensorComplex X ⥤ SchemeDerivedCategory X}
    (α : (SchemeDerivedCategory.Q X) ⋙ G ⟶ F)
    (hα : ∀ K : SchemeTensorComplex X, IsIso (α.app (R.resolution.obj K)))
    (H : SchemeDerivedCategory X ⥤ SchemeDerivedCategory X)
    (β : (SchemeDerivedCategory.Q X) ⋙ H ⟶ F) :
    Functor.whiskerLeft (SchemeDerivedCategory.Q X) (lift R α hα H β) ≫ α = β := by
  rw [whiskerLeft_lift, whiskeredLift_fac]

private lemma counit_hom_ext (R : TensorAcyclicResolution X)
    {G : SchemeDerivedCategory X ⥤ SchemeDerivedCategory X}
    {F : SchemeTensorComplex X ⥤ SchemeDerivedCategory X}
    (α : (SchemeDerivedCategory.Q X) ⋙ G ⟶ F)
    (hα : ∀ K : SchemeTensorComplex X, IsIso (α.app (R.resolution.obj K)))
    (H : SchemeDerivedCategory X ⥤ SchemeDerivedCategory X)
    (γ₁ γ₂ : H ⟶ G)
    (hγ : Functor.whiskerLeft (SchemeDerivedCategory.Q X) γ₁ ≫ α =
      Functor.whiskerLeft (SchemeDerivedCategory.Q X) γ₂ ≫ α) :
    γ₁ = γ₂ := by
  letI := Localization.faithful_whiskeringLeft
    (SchemeDerivedCategory.Q X) (SchemeTensorQuasiIso X) (SchemeDerivedCategory X)
  apply ((Functor.whiskeringLeft _ _ _).obj (SchemeDerivedCategory.Q X)).map_injective
  ext K
  change γ₁.app ((SchemeDerivedCategory.Q X).obj K) =
    γ₂.app ((SchemeDerivedCategory.Q X).obj K)
  rw [← cancel_epi (H.map ((localizationComparison R).hom.app K))]
  rw [γ₁.naturality, γ₂.naturality]
  rw [cancel_mono (G.map ((localizationComparison R).hom.app K))]
  change γ₁.app ((SchemeDerivedCategory.Q X).obj (R.resolution.obj K)) =
    γ₂.app ((SchemeDerivedCategory.Q X).obj (R.resolution.obj K))
  apply (cancel_mono (α.app (R.resolution.obj K))).mp
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app] using!
    NatTrans.congr_app hγ (R.resolution.obj K)

/-- The fixed-argument universal property supplied by a resolved counit. -/
private theorem isLeftDerived_of_resolved (R : TensorAcyclicResolution X)
    {G : SchemeDerivedCategory X ⥤ SchemeDerivedCategory X}
    {F : SchemeTensorComplex X ⥤ SchemeDerivedCategory X}
    (α : (SchemeDerivedCategory.Q X) ⋙ G ⟶ F)
    (hα : ∀ K : SchemeTensorComplex X, IsIso (α.app (R.resolution.obj K))) :
    G.IsLeftDerivedFunctor α (SchemeTensorQuasiIso X) where
  isRightKanExtension := by
    refine ⟨⟨?_⟩⟩
    refine IsTerminal.ofUniqueHom (fun E ↦
      CostructuredArrow.homMk (lift R α hα E.left E.hom)
        (lift_fac R α hα E.left E.hom)) ?_
    intro E m
    apply CostructuredArrow.hom_ext
    apply counit_hom_ext R α hα
    exact (CostructuredArrow.w m).trans (lift_fac R α hα E.left E.hom).symm

end TensorAcyclicResolution

/-- A genuine bifunctorial left-derived tensor on the unbounded scheme-derived category.

The two universal-property fields are deliberately indexed by complexes representing the fixed
argument.  This makes the comparison against the actual degreewise tensor visible and prevents
an unrelated bifunctor from satisfying the interface. -/
structure LeftDerivedTensor (X : Scheme.{u}) where
  /-- The derived tensor bifunctor. -/
  functor : SchemeDerivedCategory X ⥤ SchemeDerivedCategory X ⥤ SchemeDerivedCategory X
  /-- Comparison from localization followed by the derived tensor to degreewise total tensor. -/
  counit :
    (((Functor.whiskeringLeft₂ (SchemeDerivedCategory X)).obj
        (SchemeDerivedCategory.Q X)).obj (SchemeDerivedCategory.Q X)).obj functor ⟶
      Scheme.Modules.totalTensor X ⋙
        (Functor.whiskeringRight _ _ _).obj (SchemeDerivedCategory.Q X)
  /-- The fixed-first-argument left-derived universal property. -/
  isLeftDerived_left (K : SchemeTensorComplex X) :
    (functor.obj ((SchemeDerivedCategory.Q X).obj K)).IsLeftDerivedFunctor
      (counit.app K) (SchemeTensorQuasiIso X)
  /-- The fixed-second-argument left-derived universal property. -/
  isLeftDerived_right (L : SchemeTensorComplex X) :
    (functor.flip.obj ((SchemeDerivedCategory.Q X).obj L)).IsLeftDerivedFunctor
      (counit.flipApp L) (SchemeTensorQuasiIso X)

namespace TensorAcyclicResolution

variable {X : Scheme.{u}}

/-- A tensor-acyclic resolution constructs the bifunctor and proves both fixed-argument
universal properties. -/
def toLeftDerivedTensor (R : TensorAcyclicResolution X) : LeftDerivedTensor X where
  functor := R.derivedTensor
  counit := R.counit
  isLeftDerived_left K := by
    refine isLeftDerived_of_resolved R (R.counit.app K) ?_
    intro L
    change IsIso
      (((R.derivedTensorFactors.hom.app K).app (R.resolution.obj L)) ≫
        (R.resolvedTensorComparison.app K).app (R.resolution.obj L))
    haveI : IsIso ((R.derivedTensorFactors.hom.app K).app (R.resolution.obj L)) := by
      infer_instance
    haveI : IsIso ((R.resolvedTensorComparison.app K).app (R.resolution.obj L)) := by
      change IsIso ((SchemeDerivedCategory.Q X).map
        (((Scheme.Modules.totalTensor X).map (R.comparison.app K)).app
            (R.resolution.obj (R.resolution.obj L)) ≫
          ((Scheme.Modules.totalTensor X).obj K).map
            (R.comparison.app (R.resolution.obj L))))
      exact R.left_resolved_comparison_isIso K L
    infer_instance
  isLeftDerived_right L := by
    let α : SchemeDerivedCategory.Q X ⋙
        R.derivedTensor.flip.obj ((SchemeDerivedCategory.Q X).obj L) ⟶
        (Scheme.Modules.totalTensor X ⋙
          (Functor.whiskeringRight _ _ _).obj (SchemeDerivedCategory.Q X)).flip.obj L := by
      exact R.counit.flipApp L
    refine isLeftDerived_of_resolved R α ?_
    intro K
    change IsIso ((R.counit.app (R.resolution.obj K)).app L)
    change IsIso
      (((R.derivedTensorFactors.hom.app (R.resolution.obj K)).app L) ≫
        (R.resolvedTensorComparison.app (R.resolution.obj K)).app L)
    haveI : IsIso ((R.derivedTensorFactors.hom.app (R.resolution.obj K)).app L) := by
      infer_instance
    haveI : IsIso ((R.resolvedTensorComparison.app (R.resolution.obj K)).app L) := by
      change IsIso ((SchemeDerivedCategory.Q X).map
        (((Scheme.Modules.totalTensor X).map
            (R.comparison.app (R.resolution.obj K))).app (R.resolution.obj L) ≫
          ((Scheme.Modules.totalTensor X).obj (R.resolution.obj K)).map
            (R.comparison.app L)))
      exact R.right_resolved_comparison_isIso K L
    infer_instance

end TensorAcyclicResolution

namespace LeftDerivedTensor

variable {X : Scheme.{u}}

/-- The canonical comparison of two left-derived tensors, for a fixed complex representative.

It is the unique comparison induced by their common counit to
`Scheme.Modules.totalTensor X` after applying `Functor.leftDerivedUnique` to the fixed-first
argument functors. -/
noncomputable def leftDerivedUnique (P Q : LeftDerivedTensor X)
    (K : SchemeTensorComplex X) :
    P.functor.obj ((SchemeDerivedCategory.Q X).obj K) ≅
      Q.functor.obj ((SchemeDerivedCategory.Q X).obj K) := by
  let F : SchemeTensorComplex X ⥤ SchemeDerivedCategory X :=
    (Scheme.Modules.totalTensor X).obj K ⋙ SchemeDerivedCategory.Q X
  let αP : SchemeDerivedCategory.Q X ⋙
      P.functor.obj ((SchemeDerivedCategory.Q X).obj K) ⟶ F := by
    exact P.counit.app K
  let αQ : SchemeDerivedCategory.Q X ⋙
      Q.functor.obj ((SchemeDerivedCategory.Q X).obj K) ⟶ F := by
    exact Q.counit.app K
  letI :
      (P.functor.obj ((SchemeDerivedCategory.Q X).obj K)).IsLeftDerivedFunctor
        αP (SchemeTensorQuasiIso X) := by
    exact P.isLeftDerived_left K
  letI :
      (Q.functor.obj ((SchemeDerivedCategory.Q X).obj K)).IsLeftDerivedFunctor
        αQ (SchemeTensorQuasiIso X) := by
    exact Q.isLeftDerived_left K
  exact CategoryTheory.Functor.leftDerivedUnique
    (Q.functor.obj ((SchemeDerivedCategory.Q X).obj K))
    (P.functor.obj ((SchemeDerivedCategory.Q X).obj K))
    αP αQ (SchemeTensorQuasiIso X)

/-- The fixed-left comparison with the exact functor induced by an invertible module sheaf. -/
noncomputable def fixedLeftComparison (P : LeftDerivedTensor X) (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L)] :
    P.functor.obj ((SchemeDerivedCategory.Q X).obj (singleComplex X L)) ≅
      exactLeftFunctor X L := by
  let K : SchemeTensorComplex X := singleComplex X L
  let F : SchemeTensorComplex X ⥤ SchemeDerivedCategory X :=
    (Scheme.Modules.totalTensor X).obj K ⋙ SchemeDerivedCategory.Q X
  let αP : SchemeDerivedCategory.Q X ⋙
      P.functor.obj ((SchemeDerivedCategory.Q X).obj K) ⟶ F := by
    exact P.counit.app K
  let αE : SchemeDerivedCategory.Q X ⋙ exactLeftFunctor X L ⟶ F := by
    exact exactLeftCounit X L
  letI :
      (P.functor.obj ((SchemeDerivedCategory.Q X).obj K)).IsLeftDerivedFunctor
        αP (SchemeTensorQuasiIso X) := by
    exact P.isLeftDerived_left K
  letI :
      (exactLeftFunctor X L).IsLeftDerivedFunctor
        αE (SchemeTensorQuasiIso X) := by
    exact exactLeftIsLeftDerived X L
  exact CategoryTheory.Functor.leftDerivedUnique
    (exactLeftFunctor X L)
    (P.functor.obj ((SchemeDerivedCategory.Q X).obj K))
    αP αE (SchemeTensorQuasiIso X)

/-- The analogous comparison after fixing the second argument. It uses the common counit and
`Functor.leftDerivedUnique` for the fixed-second-variable functors. -/
noncomputable def leftDerivedUniqueFlip (P Q : LeftDerivedTensor X)
    (L : SchemeTensorComplex X) :
    P.functor.flip.obj ((SchemeDerivedCategory.Q X).obj L) ≅
      Q.functor.flip.obj ((SchemeDerivedCategory.Q X).obj L) := by
  let F : SchemeTensorComplex X ⥤ SchemeDerivedCategory X :=
    (Scheme.Modules.totalTensor X ⋙
      (Functor.whiskeringRight _ _ _).obj (SchemeDerivedCategory.Q X)).flip.obj L
  let αP : SchemeDerivedCategory.Q X ⋙
      P.functor.flip.obj ((SchemeDerivedCategory.Q X).obj L) ⟶ F := by
    exact P.counit.flipApp L
  let αQ : SchemeDerivedCategory.Q X ⋙
      Q.functor.flip.obj ((SchemeDerivedCategory.Q X).obj L) ⟶ F := by
    exact Q.counit.flipApp L
  letI :
      (P.functor.flip.obj ((SchemeDerivedCategory.Q X).obj L)).IsLeftDerivedFunctor
        αP (SchemeTensorQuasiIso X) := by
    exact P.isLeftDerived_right L
  letI :
      (Q.functor.flip.obj ((SchemeDerivedCategory.Q X).obj L)).IsLeftDerivedFunctor
        αQ (SchemeTensorQuasiIso X) := by
    exact Q.isLeftDerived_right L
  exact CategoryTheory.Functor.leftDerivedUnique
    (Q.functor.flip.obj ((SchemeDerivedCategory.Q X).obj L))
    (P.functor.flip.obj ((SchemeDerivedCategory.Q X).obj L))
    αP αQ (SchemeTensorQuasiIso X)

end LeftDerivedTensor

namespace TensorAcyclicResolution

variable {X : Scheme.{u}}

/-- The identity resolution is available only when the supplied tensor already inverts both
variables' quasi-isomorphisms after localization. -/
def ofTensorInverts (X : Scheme.{u})
    (hTensor :
      MorphismProperty.IsInvertedBy₂ (SchemeTensorQuasiIso X) (SchemeTensorQuasiIso X)
        (Scheme.Modules.totalTensor X ⋙
          (Functor.whiskeringRight _ _ _).obj (SchemeDerivedCategory.Q X))) :
    TensorAcyclicResolution X where
  resolution := 𝟭 (SchemeTensorComplex X)
  comparison := 𝟙 (𝟭 (SchemeTensorComplex X))
  comparison_quasiIso K := by
    change HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ) (𝟙 _)
    rw [HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  tensor_inverts := by
    change MorphismProperty.IsInvertedBy₂ (SchemeTensorQuasiIso X) (SchemeTensorQuasiIso X)
      (Scheme.Modules.totalTensor X ⋙
        (Functor.whiskeringRight _ _ _).obj (SchemeDerivedCategory.Q X))
    exact hTensor
  left_resolved_comparison_isIso K L := by
    simp only [Functor.id_obj, NatTrans.id_app]
    infer_instance
  right_resolved_comparison_isIso K L := by
    simp only [Functor.id_obj, NatTrans.id_app]
    infer_instance

/-- Compatibility name for the exact identity resolution. -/
abbrev identity (X : Scheme.{u})
    (hTensor :
      MorphismProperty.IsInvertedBy₂ (SchemeTensorQuasiIso X) (SchemeTensorQuasiIso X)
        (Scheme.Modules.totalTensor X ⋙
          (Functor.whiskeringRight _ _ _).obj (SchemeDerivedCategory.Q X))) :
    TensorAcyclicResolution X :=
  ofTensorInverts X hTensor

/-- Adapt the generic `SchemeKFlatResolution`.  The explicit left acyclicity hypothesis is the
additional comparison that generic K-flatness does not provide for an arbitrary fixed factor. -/
def ofKFlat (R : SchemeKFlatResolution X)
    (hleft : ∀ K L : SchemeTensorComplex X,
      IsIso ((SchemeDerivedCategory.Q X).map
        (((Scheme.Modules.totalTensor X).map (R.comparison.app K)).app
            (R.resolution.obj (R.resolution.obj L)) ≫
          ((Scheme.Modules.totalTensor X).obj K).map
            (R.comparison.app (R.resolution.obj L))))) :
    TensorAcyclicResolution X where
  resolution := R.resolution
  comparison := R.comparison
  comparison_quasiIso := R.comparison_quasiIso
  tensor_inverts := by
    simpa only [resolvedTensor, CategoryTheory.KFlatResolution.resolvedTensor] using
      R.resolvedTensor_inverts
  left_resolved_comparison_isIso := hleft
  right_resolved_comparison_isIso K L := by
    haveI h₁ : IsIso ((SchemeDerivedCategory.Q X).map
        (((Scheme.Modules.totalTensor X).map
            (R.comparison.app (R.resolution.obj K))).app
          (R.resolution.obj L))) := by
      change IsIso ((SchemeDerivedCategory.Q X).map
        (((Scheme.Modules.totalTensor X).flip.obj (R.resolution.obj L)).map
          (R.comparison.app (R.resolution.obj K))))
      exact (R.isKFlat L).tensorRight_inverts _
        (R.comparison_quasiIso (R.resolution.obj K))
    haveI h₂ : IsIso ((SchemeDerivedCategory.Q X).map
        (((Scheme.Modules.totalTensor X).obj (R.resolution.obj K)).map
          (R.comparison.app L))) :=
      (R.isKFlat K).tensorLeft_inverts
        (R.comparison.app L) (R.comparison_quasiIso L)
    change IsIso ((SchemeDerivedCategory.Q X).map (_ ≫ _))
    rw [Functor.map_comp]
    exact IsIso.comp_isIso' h₁ h₂

/-- A general resolution and the exact identity construction agree by the fixed-argument
`Functor.leftDerivedUnique` comparison. -/
noncomputable def exactComparison (R : TensorAcyclicResolution X)
    (hTensor :
      MorphismProperty.IsInvertedBy₂ (SchemeTensorQuasiIso X) (SchemeTensorQuasiIso X)
        (Scheme.Modules.totalTensor X ⋙
          (Functor.whiskeringRight _ _ _).obj (SchemeDerivedCategory.Q X)))
    (K : SchemeTensorComplex X) :
    R.toLeftDerivedTensor.functor.obj ((SchemeDerivedCategory.Q X).obj K) ≅
      (ofTensorInverts X hTensor).toLeftDerivedTensor.functor.obj
        ((SchemeDerivedCategory.Q X).obj K) :=
  LeftDerivedTensor.leftDerivedUnique R.toLeftDerivedTensor
    (ofTensorInverts X hTensor).toLeftDerivedTensor K

/-- The exact identity comparison intertwines the two constructions' common tensor counits.
The proof is the `Functor.leftDerivedNatTrans_fac` equation for the universal-property
comparison, specialized to the identity natural transformation of the ordinary tensor target. -/
@[reassoc]
lemma exactComparison_hom_counit (R : TensorAcyclicResolution X)
    (hTensor :
      MorphismProperty.IsInvertedBy₂ (SchemeTensorQuasiIso X) (SchemeTensorQuasiIso X)
        (Scheme.Modules.totalTensor X ⋙
          (Functor.whiskeringRight _ _ _).obj (SchemeDerivedCategory.Q X)))
    (K : SchemeTensorComplex X) :
    Functor.whiskerLeft (SchemeDerivedCategory.Q X)
        (exactComparison R hTensor K).hom ≫
      ((ofTensorInverts X hTensor).toLeftDerivedTensor.counit.app K) =
        R.toLeftDerivedTensor.counit.app K := by
  let E := (ofTensorInverts X hTensor).toLeftDerivedTensor
  let P := R.toLeftDerivedTensor
  let F : SchemeTensorComplex X ⥤ SchemeDerivedCategory X :=
    (Scheme.Modules.totalTensor X).obj K ⋙ SchemeDerivedCategory.Q X
  let αE : SchemeDerivedCategory.Q X ⋙ E.functor.obj ((SchemeDerivedCategory.Q X).obj K) ⟶ F := by
    exact E.counit.app K
  let αP : SchemeDerivedCategory.Q X ⋙ P.functor.obj ((SchemeDerivedCategory.Q X).obj K) ⟶ F := by
    exact P.counit.app K
  letI :
      (E.functor.obj ((SchemeDerivedCategory.Q X).obj K)).IsLeftDerivedFunctor
        αE (SchemeTensorQuasiIso X) := by
    exact E.isLeftDerived_left K
  letI :
      (P.functor.obj ((SchemeDerivedCategory.Q X).obj K)).IsLeftDerivedFunctor
        αP (SchemeTensorQuasiIso X) := by
    exact P.isLeftDerived_left K
  change Functor.whiskerLeft (SchemeDerivedCategory.Q X)
      (Functor.leftDerivedNatTrans
        (LF' := P.functor.obj ((SchemeDerivedCategory.Q X).obj K))
        (LF := E.functor.obj ((SchemeDerivedCategory.Q X).obj K))
        (α' := αP) (α := αE) (W := SchemeTensorQuasiIso X) (𝟙 F)) ≫ αE = αP
  simpa only [Category.comp_id] using
    (Functor.leftDerivedNatTrans_fac
      (LF' := P.functor.obj ((SchemeDerivedCategory.Q X).obj K))
      (LF := E.functor.obj ((SchemeDerivedCategory.Q X).obj K))
      (α' := αP) (α := αE) (W := SchemeTensorQuasiIso X) (𝟙 F))

end TensorAcyclicResolution

end

end AlgebraicGeometry.DerivedCategory
