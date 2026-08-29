/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Tilting.TorsionPair.Heart
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.HeartBridge
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Original-heart cohomology of objects in an HRS-tilted heart

This file supplies the two-term cohomology bridge used by weak tilting
arguments.  It has two independent parts:

* `originalHeartCohFunctor t n` constructs degree-`n` cohomology in the heart
  of an arbitrary t-structure.  Unlike `HeartStabilityData.heartCohFunctor`,
  it does not require a stability function or HN data.
* for a torsion pair `P` and an object `X` of the tilted heart, the canonical
  truncation triangle is exposed as

  `H⁻¹_t(X)⟦1⟧ ⟶ X ⟶ H⁰_t(X)`.

The first term is torsion-free, the last is torsion, and the triangle induces
a short exact sequence in the tilted heart.  The final two theorems expose
the inclusion as a kernel and the projection as a cokernel, so downstream
semistability proofs can use abelian kernel/image language without reopening
the ambient triangulated-category argument.
-/

namespace CategoryTheory.Triangulated.Tilting

open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated
open scoped ZeroObject

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-! ## Cohomology attached only to a t-structure -/

/-- Degree-`n` cohomology in the heart of `t`, constructed from the pure
truncation `τ^[n,n]` and the shift which places it in degree zero. -/
noncomputable def originalHeartCohFunctor [IsTriangulated C]
    (t : TStructure C) (n : ℤ) :
    C ⥤ t.heart.FullSubcategory :=
  ObjectProperty.lift _ ((t.truncGELE n n) ⋙ shiftFunctor C n) (fun E ↦ by
    rw [t.mem_heart_iff]
    constructor
    · simpa using t.isLE_shift ((t.truncGELE n n).obj E) n n 0 (by lia)
    · simpa using t.isGE_shift ((t.truncGELE n n).obj E) n n 0 (by lia))

instance originalHeartCohFunctor_additive [IsTriangulated C]
    (t : TStructure C) (n : ℤ) :
    Functor.Additive (originalHeartCohFunctor t n) where
  map_add := by
    intro X Y f g
    ext
    change (shiftFunctor C n).map ((t.truncGE n).map ((t.truncLE n).map (f + g))) =
      (shiftFunctor C n).map ((t.truncGE n).map ((t.truncLE n).map f)) +
        (shiftFunctor C n).map ((t.truncGE n).map ((t.truncLE n).map g))
    simp [Functor.map_add]

/-- The object-level notation for `originalHeartCohFunctor`. -/
noncomputable abbrev originalHeartCoh [IsTriangulated C]
    (t : TStructure C) (n : ℤ) (E : C) :
    t.heart.FullSubcategory :=
  (originalHeartCohFunctor t n).obj E

/-- Degree-zero cohomology recovers an object already in the heart.  This
applies equally to the original t-structure and to an HRS tilt. -/
noncomputable def originalHeartCohIsoOfHeart [IsTriangulated C]
    (t : TStructure C) (E : t.heart.FullSubcategory) :
    originalHeartCoh t 0 E.obj ≅ E := by
  have hLE : t.IsLE E.obj 0 := (t.mem_heart_iff E.obj).mp E.property |>.1
  have hGE : t.IsGE E.obj 0 := (t.mem_heart_iff E.obj).mp E.property |>.2
  let eLE : (t.truncLE 0).obj E.obj ≅ E.obj :=
    @asIso _ _ _ _ ((t.truncLEι 0).app E.obj)
      ((t.isLE_iff_isIso_truncLEι_app 0 E.obj).mp hLE)
  let eGE : E.obj ≅ (t.truncGE 0).obj E.obj :=
    @asIso _ _ _ _ ((t.truncGEπ 0).app E.obj)
      ((t.isGE_iff_isIso_truncGEπ_app 0 E.obj).mp hGE)
  refine ObjectProperty.isoMk _ ?_
  simpa [originalHeartCoh, originalHeartCohFunctor, TStructure.truncGELE] using
    ((shiftFunctor C 0).mapIso ((t.truncGE 0).mapIso eLE ≪≫ eGE.symm) ≪≫
      (shiftFunctorZero C ℤ).app E.obj)

/-! ## Canonical factors of a tilted-heart object -/

variable {t : TStructure C} (P : HeartTorsionPair t)

/-- Cohomology for the tilted t-structure.  This abbreviation makes explicit
that the same t-structure-only construction is available in both hearts. -/
noncomputable abbrev HeartTorsionPair.tiltedHeartCohFunctor [IsTriangulated C]
    (n : ℤ) : C ⥤ (P.tilt).heart.FullSubcategory :=
  originalHeartCohFunctor P.tilt n

/-- The zero object belongs to the torsion class. -/
theorem HeartTorsionPair.tors_zero : P.tors (0 : C) := by
  refine P.tors_of_orthogonal (by infer_instance) (by infer_instance) ?_
  intro F hF f
  exact (isZero_zero C).eq_zero_of_src f

/-- The zero object belongs to the torsion-free class. -/
theorem HeartTorsionPair.free_zero : P.free (0 : C) := by
  refine P.free_of_orthogonal (by infer_instance) (by infer_instance) ?_
  intro T hT f
  exact (isZero_zero C).eq_zero_of_tgt f

/-- A tilted-heart object has original cohomological upper bound zero. -/
theorem HeartTorsionPair.isLE_zero_of_tilt_heart [IsTriangulated C] {X : C}
    (hX : (P.tilt).heart X) : t.IsLE X 0 := by
  rw [TStructure.mem_heart_iff] at hX
  obtain ⟨⟨hLE, _⟩, _⟩ := hX
  exact hLE

/-- A tilted-heart object has original cohomological lower bound minus one. -/
theorem HeartTorsionPair.isGE_neg_one_of_tilt_heart [IsTriangulated C] {X : C}
    (hX : (P.tilt).heart X) : t.IsGE X (-1) := by
  rw [TStructure.mem_heart_iff] at hX
  obtain ⟨_, ⟨hGE, _⟩⟩ := hX
  simpa using hGE

/-- The original degree-zero truncation of a tilted-heart object is torsion. -/
theorem HeartTorsionPair.tors_truncGE_zero_of_tilt_heart [IsTriangulated C] {X : C}
    (hX : (P.tilt).heart X) : P.tors ((t.truncGE 0).obj X) := by
  rw [TStructure.mem_heart_iff] at hX
  obtain ⟨⟨hLE, hOrth⟩, _⟩ := hX
  exact (P.torsOrth_iff_tors_truncGE hLE).mp
    (ObjectProperty.prop_of_iso P.torsOrth ((shiftFunctorZero C ℤ).app X) hOrth)

/-- The original degree-minus-one truncation of a tilted-heart object,
shifted into the original heart, is torsion-free. -/
theorem HeartTorsionPair.free_truncLT_zero_shift_of_tilt_heart [IsTriangulated C]
    {X : C} (hX : (P.tilt).heart X) :
    P.free (((t.truncLT 0).obj X)⟦(-1 : ℤ)⟧) := by
  rw [TStructure.mem_heart_iff] at hX
  obtain ⟨⟨hXLE, _⟩, ⟨hXGE, hFreeOrth⟩⟩ := hX
  haveI := hXLE
  haveI := hXGE
  have hDist := t.triangleLTGE_distinguished 0 X
  have hObj₁ : ((t.triangleLTGE 0).obj X).obj₁ = (t.truncLT 0).obj X := rfl
  haveI : t.IsLE (((t.triangleLTGE 0).obj X).obj₁) (0 - 1) := inferInstance
  haveI : t.IsGE (((t.triangleLTGE 0).obj X).obj₁) (0 - 1) := by
    rw [hObj₁]
    infer_instance
  have hLE : t.IsLE ((((t.triangleLTGE 0).obj X).obj₁)⟦(-1 : ℤ)⟧) 0 :=
    t.isLE_shift _ (0 - 1) (-1) 0 (by lia)
  have hGE : t.IsGE ((((t.triangleLTGE 0).obj X).obj₁)⟦(-1 : ℤ)⟧) 0 :=
    t.isGE_shift _ (0 - 1) (-1) 0 (by lia)
  refine P.free_of_orthogonal hLE hGE ?_
  intro T hT u
  have hDist' := Triangle.shift_distinguished _ hDist (-1)
  obtain ⟨k, hk⟩ := Triangle.coyoneda_exact₂ _ (inv_rot_of_distTriang _ hDist') u
    (hFreeOrth T hT _)
  have hk0 : k = 0 := by
    have hObj₃ : ((shiftFunctor (Triangle C) (-1 : ℤ)).obj
          ((t.triangleLTGE 0).obj X)).obj₃ = ((t.truncGE 0).obj X)⟦(-1 : ℤ)⟧ := rfl
    haveI : t.IsGE (((shiftFunctor (Triangle C) (-1 : ℤ)).obj
        ((t.triangleLTGE 0).obj X)).obj₃) 1 := by
      rw [hObj₃]
      exact t.isGE_shift _ 0 (-1) 1 (by lia)
    exact t.zero_of_isLE_of_isGE k 0 2 (by lia) (P.tors_isLE T hT)
      (t.isGE_shift _ 1 (-1) 2 (by lia))
  rw [hk, hk0]
  exact zero_comp

/-- The original `H⁻¹` factor of a tilted-heart object.  Its underlying
object is `τ^{<0}X⟦-1⟧`. -/
noncomputable def HeartTorsionPair.originalHMinusOne [IsTriangulated C] {X : C}
    (hX : (P.tilt).heart X) : t.heart.FullSubcategory :=
  ⟨((t.truncLT 0).obj X)⟦(-1 : ℤ)⟧, by
    have hFree := P.free_truncLT_zero_shift_of_tilt_heart hX
    exact (t.mem_heart_iff _).mpr
      ⟨P.free_isLE _ hFree, P.free_isGE _ hFree⟩⟩

/-- The original `H⁰` factor of a tilted-heart object.  Its underlying object
is `τ^{≥0}X`. -/
noncomputable def HeartTorsionPair.originalHZero [IsTriangulated C] {X : C}
    (hX : (P.tilt).heart X) : t.heart.FullSubcategory :=
  ⟨(t.truncGE 0).obj X, by
    have hTors := P.tors_truncGE_zero_of_tilt_heart hX
    exact (t.mem_heart_iff _).mpr
      ⟨P.tors_isLE _ hTors, P.tors_isGE _ hTors⟩⟩

theorem HeartTorsionPair.originalHMinusOne_free [IsTriangulated C] {X : C}
    (hX : (P.tilt).heart X) : P.free (P.originalHMinusOne hX).obj :=
  P.free_truncLT_zero_shift_of_tilt_heart hX

theorem HeartTorsionPair.originalHZero_tors [IsTriangulated C] {X : C}
    (hX : (P.tilt).heart X) : P.tors (P.originalHZero hX).obj :=
  P.tors_truncGE_zero_of_tilt_heart hX

/-- The truncation model of `H⁻¹` agrees with the generic original-heart
cohomology functor. -/
noncomputable def HeartTorsionPair.originalHeartCohIsoHMinusOne [IsTriangulated C]
    {X : C} (hX : (P.tilt).heart X) :
    originalHeartCoh t (-1) X ≅ P.originalHMinusOne hX := by
  haveI : t.IsGE X (-1) := P.isGE_neg_one_of_tilt_heart hX
  haveI : t.IsGE ((t.truncLT 0).obj X) (-1) := inferInstance
  let eLE : (t.truncLE (-1)).obj X ≅ (t.truncLT 0).obj X :=
    (t.truncLEIsoTruncLT (-1) 0 (by lia)).app X
  let eGE : (t.truncLT 0).obj X ≅ (t.truncGE (-1)).obj ((t.truncLT 0).obj X) :=
    @asIso _ _ _ _ ((t.truncGEπ (-1)).app ((t.truncLT 0).obj X))
      ((t.isGE_iff_isIso_truncGEπ_app (-1) _).mp (by infer_instance))
  refine ObjectProperty.isoMk _ ?_
  simpa [originalHeartCoh, originalHeartCohFunctor, HeartTorsionPair.originalHMinusOne,
    TStructure.truncGELE] using
      ((shiftFunctor C (-1)).mapIso ((t.truncGE (-1)).mapIso eLE ≪≫ eGE.symm))

/-- The truncation model of `H⁰` agrees with the generic original-heart
cohomology functor. -/
noncomputable def HeartTorsionPair.originalHeartCohIsoHZero [IsTriangulated C]
    {X : C} (hX : (P.tilt).heart X) :
    originalHeartCoh t 0 X ≅ P.originalHZero hX := by
  have hLE : t.IsLE X 0 := P.isLE_zero_of_tilt_heart hX
  let eLE : (t.truncLE 0).obj X ≅ X :=
    @asIso _ _ _ _ ((t.truncLEι 0).app X)
      ((t.isLE_iff_isIso_truncLEι_app 0 X).mp hLE)
  refine ObjectProperty.isoMk _ ?_
  simpa [originalHeartCoh, originalHeartCohFunctor, HeartTorsionPair.originalHZero,
    TStructure.truncGELE] using
      ((shiftFunctor C 0).mapIso ((t.truncGE 0).mapIso eLE) ≪≫
        (shiftFunctorZero C ℤ).app ((t.truncGE 0).obj X))

/-! ## The canonical short exact sequence in the tilted heart -/

/-- The shift-cancellation isomorphism used to put the first term of the
level-zero truncation triangle in `H⁻¹(X)⟦1⟧` form. -/
noncomputable def originalCohomologyShiftIso (t : TStructure C) (X : C) :
    ((t.truncLT 0).obj X)⟦(-1 : ℤ)⟧⟦(1 : ℤ)⟧ ≅ (t.truncLT 0).obj X :=
  (shiftFunctorCompIsoId C (-1 : ℤ) (1 : ℤ) (by lia)).app ((t.truncLT 0).obj X)

/-- The canonical original-cohomology triangle of `X`, obtained from the
level-zero truncation triangle by writing its first term as `H⁻¹(X)⟦1⟧`. -/
noncomputable def originalCohomologyTriangle (t : TStructure C) (X : C) : Triangle C :=
  let e := originalCohomologyShiftIso t X
  Triangle.mk (e.hom ≫ ((t.triangleLTGE 0).obj X).mor₁)
    ((t.triangleLTGE 0).obj X).mor₂
    (((t.triangleLTGE 0).obj X).mor₃ ≫ e.inv⟦(1 : ℤ)⟧')

/-- The canonical original-cohomology triangle is distinguished. -/
theorem originalCohomologyTriangle_distinguished
    (t : TStructure C) (X : C) : originalCohomologyTriangle t X ∈ distTriang C := by
  dsimp [originalCohomologyTriangle]
  refine isomorphic_distinguished _ (t.triangleLTGE_distinguished 0 X) _ ?_
  exact Triangle.isoMk _ _ (originalCohomologyShiftIso t X)
    (Iso.refl _) (Iso.refl _) (by simp) (by simp)
    (by simp [← Functor.map_comp])

/-- A shifted torsion-free object belongs to the tilted heart. -/
theorem HeartTorsionPair.free_shift_mem_tilt_heart [IsTriangulated C] {F : C}
    (hF : P.free F) : (P.tilt).heart (F⟦(1 : ℤ)⟧) :=
  P.tilt_heart_of_triangle hF P.tors_zero (contractible_distinguished _)

/-- A torsion object belongs to the tilted heart. -/
theorem HeartTorsionPair.tors_mem_tilt_heart [IsTriangulated C] {T : C}
    (hT : P.tors T) : (P.tilt).heart T := by
  have hDist :
      Triangle.mk (0 : (0 : C)⟦(1 : ℤ)⟧ ⟶ T) (𝟙 T)
        (0 : T ⟶ ((0 : C)⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧) ∈ distTriang C := by
    refine isomorphic_distinguished (Triangle.mk (0 : (0 : C) ⟶ T) (𝟙 T) 0)
      (contractible_distinguished₁ T)
      (Triangle.mk (0 : (0 : C)⟦(1 : ℤ)⟧ ⟶ T) (𝟙 T) 0) ?_
    exact Triangle.isoMk
      (Triangle.mk (0 : (0 : C)⟦(1 : ℤ)⟧ ⟶ T) (𝟙 T) 0)
      (Triangle.mk (0 : (0 : C) ⟶ T) (𝟙 T) 0)
      (Functor.mapZeroObject (shiftFunctor C (1 : ℤ)))
      (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp)
  exact P.tilt_heart_of_triangle P.free_zero hT hDist

/-- The `H⁻¹(X)⟦1⟧` term, regarded as an object of the tilted heart. -/
noncomputable def HeartTorsionPair.originalHMinusOneShiftInTiltHeart
    [IsTriangulated C] {X : C} (hX : (P.tilt).heart X) :
    (P.tilt).heart.FullSubcategory :=
  ⟨(P.originalHMinusOne hX).obj⟦(1 : ℤ)⟧,
    P.free_shift_mem_tilt_heart (P.originalHMinusOne_free hX)⟩

/-- `X`, regarded as an object of the tilted heart. -/
def HeartTorsionPair.objectInTiltHeart [IsTriangulated C] {X : C}
    (hX : (P.tilt).heart X) : (P.tilt).heart.FullSubcategory :=
  ⟨X, hX⟩

/-- The `H⁰(X)` term, regarded as an object of the tilted heart. -/
noncomputable def HeartTorsionPair.originalHZeroInTiltHeart [IsTriangulated C]
    {X : C} (hX : (P.tilt).heart X) : (P.tilt).heart.FullSubcategory :=
  ⟨(P.originalHZero hX).obj, P.tors_mem_tilt_heart (P.originalHZero_tors hX)⟩

/-- The canonical two-term original-cohomology complex in the tilted heart. -/
noncomputable def HeartTorsionPair.originalCohomologyShortComplex
    [IsTriangulated C] {X : C} (hX : (P.tilt).heart X) :
    ShortComplex (P.tilt).heart.FullSubcategory :=
  ShortComplex.mk
    (ObjectProperty.homMk (originalCohomologyTriangle t X).mor₁ :
      P.originalHMinusOneShiftInTiltHeart hX ⟶ P.objectInTiltHeart hX)
    (ObjectProperty.homMk (originalCohomologyTriangle t X).mor₂ :
      P.objectInTiltHeart hX ⟶ P.originalHZeroInTiltHeart hX)
    (by
      ext
      exact comp_distTriang_mor_zero₁₂ _
        (originalCohomologyTriangle_distinguished t X))

/-- The canonical sequence
`0 ⟶ H⁻¹_t(X)⟦1⟧ ⟶ X ⟶ H⁰_t(X) ⟶ 0` is short exact in the tilted heart. -/
theorem HeartTorsionPair.originalCohomologyShortComplex_shortExact
    [IsTriangulated C] {X : C} (hX : (P.tilt).heart X) :
    (P.originalCohomologyShortComplex hX).ShortExact := by
  apply CategoryTheory.Triangulated.TStructure.heartFullSubcategory_shortExact_of_distTriang
    (C := C) (P.tilt)
  exact originalCohomologyTriangle_distinguished t X

/-- The left map of the canonical tilted-heart sequence is a kernel of the
right map. -/
theorem HeartTorsionPair.originalCohomologyShortComplex_f_isKernel
    [IsTriangulated C] {X : C} (hX : (P.tilt).heart X) :
    Nonempty (IsLimit (KernelFork.ofι (P.originalCohomologyShortComplex hX).f
      (P.originalCohomologyShortComplex hX).zero)) := by
  letI : Abelian (P.tilt).heart.FullSubcategory :=
    CategoryTheory.Triangulated.TStructure.heartFullSubcategoryAbelian P.tilt
  have hShort := P.originalCohomologyShortComplex_shortExact hX
  exact (ShortComplex.exact_and_mono_f_iff_f_is_kernel
    (P.originalCohomologyShortComplex hX)).mp ⟨hShort.exact, hShort.mono_f⟩

/-- The right map of the canonical tilted-heart sequence is a cokernel of the
left map. -/
theorem HeartTorsionPair.originalCohomologyShortComplex_g_isCokernel
    [IsTriangulated C] {X : C} (hX : (P.tilt).heart X) :
    Nonempty (IsColimit (CokernelCofork.ofπ (P.originalCohomologyShortComplex hX).g
      (P.originalCohomologyShortComplex hX).zero)) := by
  letI : Abelian (P.tilt).heart.FullSubcategory :=
    CategoryTheory.Triangulated.TStructure.heartFullSubcategoryAbelian P.tilt
  have hShort := P.originalCohomologyShortComplex_shortExact hX
  exact (ShortComplex.exact_and_epi_g_iff_g_is_cokernel
    (P.originalCohomologyShortComplex hX)).mp ⟨hShort.exact, hShort.epi_g⟩

/-! ## Pure shifted objects -/

/-- The original degree-minus-one cohomology of a torsion object vanishes. -/
theorem HeartTorsionPair.originalHMinusOne_isZero_of_tors
    [IsTriangulated C] {T : C} (hT : P.tors T) :
    IsZero (P.originalHMinusOne (P.tors_mem_tilt_heart hT)) := by
  haveI : t.IsGE T 0 := P.tors_isGE T hT
  refine CategoryTheory.ObjectProperty.FullSubcategory.isZero_of_obj_isZero (C := C) ?_
  exact (shiftFunctor C (-1 : ℤ)).map_isZero
    (t.isZero_truncLT_obj_of_isGE 0 T)

/-- The original `H⁰` of a torsion object is canonically the object itself. -/
noncomputable def HeartTorsionPair.originalHZeroIsoOfTors
    [IsTriangulated C] {T : C} (hT : P.tors T) :
    P.originalHZero (P.tors_mem_tilt_heart hT) ≅
      ⟨T, (t.mem_heart_iff T).mpr ⟨P.tors_isLE T hT, P.tors_isGE T hT⟩⟩ :=
  (P.originalHeartCohIsoHZero (P.tors_mem_tilt_heart hT)).symm ≪≫
    originalHeartCohIsoOfHeart t
      ⟨T, (t.mem_heart_iff T).mpr ⟨P.tors_isLE T hT, P.tors_isGE T hT⟩⟩

/-- The original degree-zero cohomology of a shifted torsion-free object
vanishes.  This is the endpoint calculation used when a quotient in the
tilted heart is shown to remain a pure shifted object. -/
theorem HeartTorsionPair.originalHZero_isZero_of_free_shift
    [IsTriangulated C] {F : C} (hF : P.free F) :
    IsZero (P.originalHZero (P.free_shift_mem_tilt_heart hF)) := by
  haveI : t.IsLE F 0 := P.free_isLE F hF
  haveI : t.IsLE (F⟦(1 : ℤ)⟧) (-1) :=
    t.isLE_shift F 0 1 (-1) (by lia)
  refine CategoryTheory.ObjectProperty.FullSubcategory.isZero_of_obj_isZero (C := C) ?_
  exact t.isZero_truncGE_obj_of_isLE (-1) 0 (by lia) (F⟦(1 : ℤ)⟧)

/-- If the original `H⁰` of a tilted-heart object vanishes, its canonical
`H⁻¹[1]` subobject is an isomorphism. -/
noncomputable def HeartTorsionPair.originalHMinusOneShiftIsoOfHZeroIsZero
    [IsTriangulated C] {X : C} (hX : P.tilt.heart X)
    (hzero : IsZero (P.originalHZero hX)) :
    P.originalHMinusOneShiftInTiltHeart hX ≅ P.objectInTiltHeart hX := by
  letI : Abelian P.tilt.heart.FullSubcategory :=
    CategoryTheory.Triangulated.TStructure.heartFullSubcategoryAbelian P.tilt
  let S := P.originalCohomologyShortComplex hX
  have hS : S.ShortExact := P.originalCohomologyShortComplex_shortExact hX
  have hzero' : IsZero S.X₃ := by
    apply CategoryTheory.ObjectProperty.FullSubcategory.isZero_of_obj_isZero (C := C)
    exact (t.heart).ι.map_isZero hzero
  exact @asIso _ _ _ _ S.f ((hS.isIso_f_iff).2 hzero')

/-- The original `H⁻¹` of `F[1]` is canonically isomorphic to `F` when
`F` is torsion-free. -/
noncomputable def HeartTorsionPair.originalHMinusOneIsoOfFreeShift
    [IsTriangulated C] {F : C} (hF : P.free F) :
    P.originalHMinusOne (P.free_shift_mem_tilt_heart hF) ≅
      ⟨F, (t.mem_heart_iff F).mpr ⟨P.free_isLE F hF, P.free_isGE F hF⟩⟩ := by
  let hFshift := P.free_shift_mem_tilt_heart hF
  let eTilt := P.originalHMinusOneShiftIsoOfHZeroIsZero hFshift
    (P.originalHZero_isZero_of_free_shift hF)
  let eAmbient := P.tilt.heart.ι.mapIso eTilt
  let eShift := (shiftFunctor C (-1 : ℤ)).mapIso eAmbient
  let eLeft :=
    (shiftFunctorCompIsoId C (1 : ℤ) (-1 : ℤ) (by lia)).app
      (P.originalHMinusOne hFshift).obj
  let eRight :=
    (shiftFunctorCompIsoId C (1 : ℤ) (-1 : ℤ) (by lia)).app F
  refine ObjectProperty.isoMk _ ?_
  exact eLeft.symm ≪≫ eShift ≪≫ eRight

end CategoryTheory.Triangulated.Tilting
