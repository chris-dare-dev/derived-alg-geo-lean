/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.BoundedAboveProjective
import DerivedAlgGeo.RingTheory.Flat.Basic

/-!
# The derived tensor product of a bounded-above complex of modules with a module

For a commutative ring `R` and an `R`-module `M`, `ModuleCat.derivedTensorRight M` is
`K ↦ K ⊗^L_R M` on the bounded-above derived category `DerivedCategory.Minus (ModuleCat R)`:
`- ⊗_R M` applied to a bounded-above projective replacement of `K`
(`minusKProjectiveDerivedFunctor`).

A strictly bounded-above complex of flat modules computes it. Stacks reaches this through
K-flatness (Stacks 064K, 064L); here it is proved directly: tensoring an acyclic strictly
bounded-above complex of flat modules with `M` keeps it acyclic, because its kernels are flat
(Stacks 00HM) and so the short exact sequences it splits into stay exact. Hence a
quasi-isomorphism between such complexes stays one after `- ⊗_R M`, by its mapping cone.

## Main definitions

* `ModuleCat.derivedTensorRight`: `K ⊗^L_R M` for bounded-above `K`.
* `ModuleCat.derivedTensorRightObjIso`: its value on a bounded-above complex of projectives.

## Main results

* `ModuleCat.flat_ker_d_of_exactAt`: in a strictly bounded-above complex of flat modules exact
  above `n`, the kernel of the differential leaving degree `n` is flat.
* `ModuleCat.acyclic_tensorRight_of_flat`: an acyclic strictly bounded-above complex of flat
  modules stays acyclic after `- ⊗_R M`.
* `ModuleCat.quasiIso_tensorRight_map_of_flat`: a quasi-isomorphism between strictly
  bounded-above complexes of flat modules stays one after `- ⊗_R M`.
* `ModuleCat.nonempty_derivedTensorRight_obj_iso_of_flat`: a strictly bounded-above complex
  of flat modules computes `⊗^L`.

## Implementation notes

The source is `D⁻` rather than all of `D(R)`: no unbounded derived tensor product, and no
K-flat resolution of an unbounded complex, is constructed or assumed. The tensor product is
taken on the right, `K ⊗ M`, so the complex keeps its position in `tensorRight M`.

## References

* [Stacks: Tag 064K](https://stacks.math.columbia.edu/tag/064K)
* [Stacks: Tag 064L](https://stacks.math.columbia.edu/tag/064L)
* [Stacks: Tag 00HM](https://stacks.math.columbia.edu/tag/00HM)
-/

universe u

open CategoryTheory Limits MonoidalCategory

noncomputable section

attribute [local instance] HasDerivedCategory.standard

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- Exactness at `j` of a cochain complex of modules, as exactness of the two adjacent
differentials as linear maps. -/
theorem exactAt_iff_function_exact (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j k : ℤ) (hij : i + 1 = j) (hjk : j + 1 = k) :
    P.ExactAt j ↔ Function.Exact (P.d i j).hom (P.d j k).hom := by
  rw [HomologicalComplex.exactAt_iff' P i j k (by simp; omega) (by simp; omega),
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  rfl

/-- Two consecutive differentials of a cochain complex of modules compose to zero, pointwise. -/
theorem d_comp_d_apply (P : CochainComplex (ModuleCat.{u} R) ℤ) (i j k : ℤ) (x : P.X i) :
    (P.d j k).hom ((P.d i j).hom x) = 0 := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, P.d_comp_d]
  rfl

/-- In a strictly bounded-above complex that is exact in every degree above `n` and whose
terms in degrees `≥ n` are flat, the kernel of the differential leaving degree `n` is flat. -/
theorem flat_ker_d_of_exactAt (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    [P.IsStrictlyLE b] (n : ℤ) (hP : ∀ i, n ≤ i → Module.Flat R (P.X i))
    (hexact : ∀ i, n < i → P.ExactAt i) :
    Module.Flat R (LinearMap.ker (P.d n (n + 1)).hom) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, b ≤ n + m := ⟨(b - n).toNat, by omega⟩
  induction m generalizing n with
  | zero =>
    have hzero : P.d n (n + 1) = 0 :=
      (P.isZero_of_isStrictlyLE b (n + 1) (by omega)).eq_of_tgt _ _
    have htop : LinearMap.ker (P.d n (n + 1)).hom = ⊤ := by
      rw [hzero]
      exact LinearMap.ker_zero
    have := hP n le_rfl
    exact Module.Flat.of_linearEquiv ((LinearEquiv.ofEq _ _ htop).trans Submodule.topEquiv)
  | succ m ih =>
    have hflat := ih (n + 1) (fun i hi ↦ hP i (by omega)) (fun i hi ↦ hexact i (by omega))
      (by omega)
    have hex := (exactAt_iff_function_exact P n (n + 1) (n + 1 + 1) rfl rfl).mp
      (hexact (n + 1) (by omega))
    let φ := (P.d n (n + 1)).hom.codRestrict (LinearMap.ker (P.d (n + 1) (n + 1 + 1)).hom)
      (fun x ↦ d_comp_d_apply P _ _ _ x)
    have hφ : Function.Surjective φ := by
      rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := (hex y).mp hy
      exact ⟨x, rfl⟩
    have := hP n le_rfl
    have hker : LinearMap.ker φ = LinearMap.ker (P.d n (n + 1)).hom :=
      LinearMap.ker_codRestrict _ _ _
    have := Module.Flat.ker_of_surjective φ hφ
    exact Module.Flat.of_linearEquiv (LinearEquiv.ofEq _ _ hker.symm)

/-- Tensoring an acyclic strictly bounded-above complex of flat modules with any module
keeps it acyclic. Each differential factors through its image, a flat kernel (Stacks 00HM),
so right exactness of `- ⊗ M` and injectivity of the inclusion after `- ⊗ M` give exactness. -/
theorem acyclic_tensorRight_of_flat (M : ModuleCat.{u} R) (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (b : ℤ) [P.IsStrictlyLE b] (hP : ∀ i, Module.Flat R (P.X i)) (hacyc : P.Acyclic) :
    (((tensorRight M).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).Acyclic := by
  intro n
  rw [exactAt_iff_function_exact _ (n - 1) n (n + 1) (by omega) rfl]
  change Function.Exact (P.d (n - 1) n ▷ M).hom (P.d n (n + 1) ▷ M).hom
  rw [ModuleCat.hom_whiskerRight, ModuleCat.hom_whiskerRight]
  have hex₀ := (exactAt_iff_function_exact P (n - 1) n (n + 1) (by omega) rfl).mp (hacyc n)
  have hex₁ := (exactAt_iff_function_exact P n (n + 1) (n + 1 + 1) rfl rfl).mp (hacyc (n + 1))
  -- `ψ` is the differential leaving degree `n + 1`, onto the cycles in degree `n + 2`.
  let ψ := (P.d (n + 1) (n + 1 + 1)).hom.codRestrict
    (LinearMap.ker (P.d (n + 1 + 1) (n + 1 + 1 + 1)).hom) (fun x ↦ d_comp_d_apply P _ _ _ x)
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := ((exactAt_iff_function_exact P (n + 1) (n + 1 + 1) (n + 1 + 1 + 1) rfl
      rfl).mp (hacyc (n + 1 + 1)) y).mp hy
    exact ⟨x, rfl⟩
  have hflat := flat_ker_d_of_exactAt P b (n + 1 + 1) (fun i _ ↦ hP i) (fun i _ ↦ hacyc i)
  have := hP (n + 1)
  -- the differential leaving degree `n`, onto `ker ψ`
  let φ := (P.d n (n + 1)).hom.codRestrict (LinearMap.ker ψ) (fun x ↦ by
    change ψ _ = 0
    ext
    exact d_comp_d_apply P _ _ _ x)
  have hφ : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    have hy' : (P.d (n + 1) (n + 1 + 1)).hom y = 0 :=
      congrArg Subtype.val (LinearMap.mem_ker.mp hy)
    obtain ⟨x, rfl⟩ := (hex₁ y).mp hy'
    exact ⟨x, rfl⟩
  have hd : (P.d n (n + 1)).hom = (LinearMap.ker ψ).subtype ∘ₗ φ := rfl
  have hinj : Function.Injective ((LinearMap.ker ψ).subtype.rTensor M) := by
    rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
    exact LinearMap.lTensor_injective_of_exact_of_flat ψ hψ _ (LinearMap.ker ψ).subtype_injective
      (LinearMap.exact_subtype_ker_map ψ) M
  have hexφ : Function.Exact (P.d (n - 1) n).hom φ := by
    intro x
    rw [← hex₀ x]
    exact ⟨fun h ↦ by simpa [φ] using congrArg Subtype.val h, fun h ↦ by ext; simpa [φ] using h⟩
  rw [hd, LinearMap.rTensor_comp, hinj.comp_exact_iff_exact]
  exact rTensor_exact M hexφ hφ

/-- Exactness at a degree of a cochain complex transfers along an isomorphism. -/
private lemma acyclic_of_iso {C : Type*} [Category* C] [Abelian C]
    {K L : CochainComplex C ℤ} (e : K ≅ L) (hK : K.Acyclic) : L.Acyclic :=
  fun n ↦ (hK n).of_iso e

/-- A morphism of cochain complexes is a quasi-isomorphism iff its mapping cone is acyclic. -/
private lemma quasiIso_iff_acyclic_mappingCone {C : Type*} [Category* C] [Abelian C]
    {K L : CochainComplex C ℤ} (g : K ⟶ L) :
    QuasiIso g ↔ (CochainComplex.mappingCone g).Acyclic := by
  rw [← HomologicalComplex.mem_quasiIso_iff,
    ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact ((HomotopyCategory.subcategoryAcyclic C).trW_iff_of_distinguished
    (CochainComplex.mappingCone.triangleh g)
    (HomotopyCategory.mappingCone_triangleh_distinguished g)).trans
      (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _)

/-- A quasi-isomorphism between strictly bounded-above complexes of flat modules stays a
quasi-isomorphism after tensoring with any module. Its mapping cone is an acyclic strictly
bounded-above complex of flat modules. -/
theorem quasiIso_tensorRight_map_of_flat (M : ModuleCat.{u} R)
    {P P' : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ P') [QuasiIso f] (b : ℤ)
    [P.IsStrictlyLE b] [P'.IsStrictlyLE b]
    (hP : ∀ i, Module.Flat R (P.X i)) (hP' : ∀ i, Module.Flat R (P'.X i)) :
    QuasiIso (((tensorRight M).mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  have hcone : (CochainComplex.mappingCone f).IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact (CochainComplex.mappingCone.isZero_X_iff f i).mpr
      ⟨P.isZero_of_isStrictlyLE b (i + 1) (by omega), P'.isZero_of_isStrictlyLE b i hi⟩
  have hflat (i : ℤ) : Module.Flat R ((CochainComplex.mappingCone f).X i) := by
    have := hP (i + 1)
    have := hP' i
    exact Module.Flat.of_linearEquiv
      ((HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) rfl) ≪≫
        ModuleCat.biprodIsoProd _ _).toLinearEquiv
  rw [quasiIso_iff_acyclic_mappingCone]
  exact acyclic_of_iso (CochainComplex.mappingCone.mapHomologicalComplexIso f (tensorRight M))
    (acyclic_tensorRight_of_flat M _ b hflat ((quasiIso_iff_acyclic_mappingCone f).mp ‹_›))

/-- `K ⊗^L_R M` for a bounded-above complex `K`: `- ⊗_R M` applied to a bounded-above
projective replacement of `K`, on the bounded-above derived category. -/
def derivedTensorRight (M : ModuleCat.{u} R) :
    DerivedCategory.Minus (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R) :=
  minusKProjectiveDerivedFunctor (tensorRight M)

/-- On a strictly bounded-above complex of projective modules, `⊗^L` is the degreewise
tensor product. -/
def derivedTensorRightObjIso (M : ModuleCat.{u} R) (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (b : ℤ) [P.IsStrictlyLE b] [∀ i, Projective (P.X i)] :
    (derivedTensorRight M).obj ⟨DerivedCategory.Q.obj P, b, inferInstance⟩ ≅
      DerivedCategory.Q.obj (((tensorRight M).mapHomologicalComplex _).obj P) :=
  minusKProjectiveDerivedFunctorObjIso (tensorRight M) P b

/-- A strictly bounded-above complex of flat modules computes `⊗^L`: its degreewise
tensor product with `M` is isomorphic to `K ⊗^L_R M`. -/
theorem nonempty_derivedTensorRight_obj_iso_of_flat (M : ModuleCat.{u} R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ) [P.IsStrictlyLE b]
    (hP : ∀ i, Module.Flat R (P.X i)) :
    Nonempty ((derivedTensorRight M).obj ⟨DerivedCategory.Q.obj P, b, inferInstance⟩ ≅
      DerivedCategory.Q.obj (((tensorRight M).mapHomologicalComplex _).obj P)) := by
  obtain ⟨Q, q, hQ, hProj, hq⟩ := CochainComplex.exists_boundedAbove_projective_replacement P b
  have hQflat (i : ℤ) : Module.Flat R (Q.X i) := by
    have := hProj i
    have : Module.Projective R (Q.X i) := (IsProjective.iff_projective (Q.X i)).mpr ‹_›
    infer_instance
  let e : (⟨DerivedCategory.Q.obj Q, b, inferInstance⟩ : DerivedCategory.Minus _) ≅
      ⟨DerivedCategory.Q.obj P, b, inferInstance⟩ :=
    ObjectProperty.isoMk _ (asIso (DerivedCategory.Q.map q))
  have := quasiIso_tensorRight_map_of_flat M q b hQflat hP
  exact ⟨(derivedTensorRight M).mapIso e.symm ≪≫ derivedTensorRightObjIso M Q b ≪≫
    asIso (DerivedCategory.Q.map (((tensorRight M).mapHomologicalComplex _).map q))⟩

end ModuleCat
