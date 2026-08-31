/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import DerivedAlgGeo.AlgebraicGeometry.CoherentSheaf.Abelian.Basic
import DerivedAlgGeo.AlgebraicGeometry.CoherentSheaf.Quasicoherent.Kernels
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Derived.AffineVanishing
import DerivedAlgGeo.CategoryTheory.Sites.Sheaves.CohomologyShortExact

/-!
# Quasi-coherence is closed under extensions

With the kernel and cokernel closure of
`CoherentSheaf/Quasicoherent/Kernels.lean`, this completes the **weak Serre
property** for quasi-coherent sheaves on an arbitrary scheme — what `Dqc(X)`
needs before it can carry a triangulated structure.

Through the **five-term** homology long exact sequence, closure under cones
needs closure under kernels, cokernels and extensions — not under subobjects and
quotients, which quasi-coherence does not have.  See
`CategoryTheory/Abelian/WeakSerre.lean`; an earlier version of this paragraph
claimed the stronger closure, and it is not what the argument uses.

## Why cohomology, when the coherent case needed none

`Abelian/Extensions.lean` proves the finite-presentation analogue with a
horseshoe and no cohomology at all. That route does not survive here: its
`simultaneousImageCover` takes a `Finset.univ.inf` of covering sieves — a
**finite** intersection — so finitely many generators lift on one refinement and
arbitrarily many do not. Quasi-coherent presentations have arbitrary index sets.
So this file takes the classical route and pays the cohomological price once.

## The argument

On `Spec R`, for `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` with `M₁` and `M₃` quasi-coherent:

1. `M₁` is quasi-coherent, hence `H¹(Spec R, M₁) = 0`
   (`Cohomology.modules_H_subsingleton_of_isQuasicoherent`).
2. So `Γ` carries the sequence to a short exact sequence of `R`-modules — left
   exactness is formal, and the surjectivity is step 1 fed through
   `Sheaf.sections_surjective_of_subsingleton_H_one`.
3. `tilde` is exact, so it carries that back to module sheaves. Right exactness
   was free; left exactness is the kernel closure, since `tilde` factors through
   `tildeEquiv` and the quasi-coherent inclusion.
4. `fromTildeΓ` compares the two sequences and is iso at both ends. The short
   five lemma makes it iso in the middle, which is quasi-coherence of `M₂`.

Then `isQuasicoherent_iff_restrict_affineOpenCover` transports it to any scheme.

## On `Γ`

Written `affineΓ R = moduleSpecSectionsFunctor R ⊤`, not `moduleSpecΓFunctor`.
The two are defeq, but only the first has domain `(Spec R).Modules`, which is
where the geometry lives, and an instance proved for one is not found for the
other. `Abelian/Kernels.lean` already had this functor and kept it `private`; it
is public as of this change. `Modules/Affine/Equivalence.lean` records the same
wrapper problem for `Scheme.Modules` itself.

## Main results

* `AlgebraicGeometry.tilde_preservesFiniteLimits`;
* `AlgebraicGeometry.shortExact_map_affineΓ`;
* `AlgebraicGeometry.isQuasicoherent_middle_affine` and `isQuasicoherent_middle`;
* `AlgebraicGeometry.quasicoherent_isClosedUnderExtensions`.
-/universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

variable {R : CommRingCat.{u}}

/-! ### Exactness of `tilde` -/

/-- Finite products on affine quasi-coherent sheaves, transported across the
tilde equivalence rather than postulated on the full subcategory. -/
noncomputable local instance qcHasFiniteProducts :
    HasFiniteProducts
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory :=
  ⟨fun _ ↦ Adjunction.hasLimitsOfShape_of_equivalence (tildeEquiv (R := R)).inverse⟩

noncomputable local instance qcHasBinaryBiproducts :
    HasBinaryBiproducts
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory :=
  HasBinaryBiproducts.of_hasBinaryProducts

/-- Quasi-coherent sheaves on an affine spectrum are abelian, by the proved tilde
equivalence with modules over the coordinate ring. -/
noncomputable local instance qcAbelian :
    Abelian (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory :=
  abelianOfEquivalence (tildeEquiv (R := R)).inverse

/-- The inclusion of quasi-coherent sheaves preserves kernels — this is the
kernel closure of `Quasicoherent/Kernels.lean`, in the form limit-preservation
wants it. -/
noncomputable instance qcι_preservesKernel
    {M N : (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory}
    (g : M ⟶ N) :
    PreservesLimit (parallelPair g 0)
      (ObjectProperty.ι (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)) :=
  (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).preservesKernels_ι g

/-- The inclusion of quasi-coherent sheaves into all module sheaves on an affine
spectrum preserves finite limits. -/
noncomputable instance quasicoherentι_preservesFiniteLimits :
    PreservesFiniteLimits
      (ObjectProperty.ι (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)) :=
  Functor.preservesFiniteLimits_of_preservesKernels _

/-- **`tilde` is exact.**

Right exactness is free — `tilde.adjunction` makes it a left adjoint. Left
exactness is this: `tilde` factors through `tildeEquiv` and the inclusion of
quasi-coherent sheaves, and that inclusion is left exact because quasi-coherence
is closed under ambient kernels. -/
noncomputable instance tilde_preservesFiniteLimits :
    PreservesFiniteLimits (tilde.functor R) := by
  letI : PreservesFiniteLimits ((tildeEquiv (R := R)).functor ⋙
      ObjectProperty.ι (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)) :=
    comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso
    (F := (tildeEquiv (R := R)).functor ⋙
      ObjectProperty.ι (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf))
    (G := tilde.functor R) (Iso.refl _)


/-! ### The affine five lemma -/

attribute [local instance] HasExt.standard

/-! ### Global sections on an affine spectrum

`Γ` is written `moduleSpecSectionsFunctor R ⊤` rather than `moduleSpecΓFunctor`.
The two are defeq, but only the first has domain `(Spec R).Modules`, which is
what a short complex of the geometry here actually lives in. -/

/-- Global sections on `Spec R`, retyped over `(Spec R).Modules`. -/
noncomputable abbrev affineΓ (R : CommRingCat.{u}) :
    (Spec R).Modules ⥤ ModuleCat.{u} R :=
  moduleSpecSectionsFunctor R ⊤

/-- **Global sections of a short exact sequence of module sheaves on `Spec R` are
short exact**, as soon as the sub is quasi-coherent.

Left exactness is formal — `Γ` preserves finite limits. The surjectivity is the
cohomological input, and the only one in this file: `H¹(Spec R, M₁) = 0`. -/
theorem shortExact_map_affineΓ
    {S : ShortComplex (Spec R).Modules} (hS : S.ShortExact)
    (h₁ : S.X₁.IsQuasicoherent) :
    (S.map (affineΓ R)).ShortExact := by
  letI := h₁
  letI : HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u}) :=
    HasExt.standard _
  haveI : Subsingleton ((S.map (Scheme.Modules.toSheaf (Spec R))).X₁.H 1) :=
    Cohomology.modules_H_subsingleton_of_isQuasicoherent S.X₁ 1 Nat.one_pos
  have hsurj :=
    Sheaf.sections_surjective_of_subsingleton_H_one (T := ⊤) Limits.isTerminalTop
      (Scheme.Modules.shortExact_map_toSheaf hS)
  haveI := hS.mono_f
  letI : (affineΓ R).PreservesMonomorphisms :=
    NormalEpiCategory.preservesMonomorphisms_of_preservesKernels (affineΓ R)
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · exact hS.exact.map_of_mono_of_preservesKernel (affineΓ R) hS.mono_f inferInstance
  · exact Functor.map_mono (affineΓ R) S.f
  · rw [ModuleCat.epi_iff_surjective]
    exact hsurj


/-! ### The affine five lemma -/

/-- The comparison `Γ(−)~ ⟶ −`, as a morphism of short complexes. -/
@[simps]
noncomputable def fromTildeΓShortComplexHom (S : ShortComplex (Spec R).Modules) :
    (S.map (affineΓ R)).map (tilde.functor R) ⟶ S where
  τ₁ := Scheme.Modules.fromTildeΓ S.X₁
  τ₂ := Scheme.Modules.fromTildeΓ S.X₂
  τ₃ := Scheme.Modules.fromTildeΓ S.X₃
  comm₁₂ := ((Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality S.f).symm
  comm₂₃ := ((Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality S.g).symm

/-- **Quasi-coherence is closed under extensions on an affine spectrum.**

The four steps: `H¹` of the sub vanishes, so `Γ` of the sequence is short exact;
`tilde` is exact, so it carries that back to a short exact sequence of module
sheaves; `fromTildeΓ` compares the two, and is iso at both ends because both ends
are quasi-coherent; the short five lemma makes it iso in the middle, which is
quasi-coherence of the middle. -/
theorem isQuasicoherent_middle_affine
    {S : ShortComplex (Spec R).Modules} (hS : S.ShortExact)
    (h₁ : S.X₁.IsQuasicoherent) (h₃ : S.X₃.IsQuasicoherent) :
    S.X₂.IsQuasicoherent := by
  letI := h₁
  letI := h₃
  have hΓ : (S.map (affineΓ R)).ShortExact := shortExact_map_affineΓ hS h₁
  have hTilde : ((S.map (affineΓ R)).map (tilde.functor R)).ShortExact :=
    hΓ.map_of_exact (tilde.functor R)
  letI : IsIso (Scheme.Modules.fromTildeΓ S.X₁) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent S.X₁
  letI : IsIso (Scheme.Modules.fromTildeΓ S.X₃) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent S.X₃
  letI : IsIso (fromTildeΓShortComplexHom S).τ₁ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent S.X₁
  letI : IsIso (fromTildeΓShortComplexHom S).τ₃ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent S.X₃
  have h₂ : IsIso (fromTildeΓShortComplexHom S).τ₂ :=
    ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ _ hTilde hS
  letI : IsIso (Scheme.Modules.fromTildeΓ S.X₂) := h₂
  exact (isQuasicoherent_iff_isIso_fromTildeΓ S.X₂).mpr inferInstance


/-! ### Any scheme -/

/-- **Quasi-coherence is closed under extensions**, on an arbitrary scheme.

The affine case transported along `X.affineOpenCover` by the affine-local
criterion. Restriction along an open immersion is exact, so the restricted
sequence is again short exact, and its two ends are again quasi-coherent. -/
theorem isQuasicoherent_middle {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (h₁ : S.X₁.IsQuasicoherent) (h₃ : S.X₃.IsQuasicoherent) :
    S.X₂.IsQuasicoherent := by
  letI := h₁
  letI := h₃
  let 𝒰 := X.affineOpenCover
  rw [Scheme.Modules.isQuasicoherent_iff_restrict_affineOpenCover S.X₂ 𝒰]
  intro i
  have hSi : (S.map (Scheme.Modules.restrictFunctor (𝒰.f i))).ShortExact :=
    hS.map_of_exact _
  haveI h₁i : ((Scheme.Modules.restrictFunctor (𝒰.f i)).obj S.X₁).IsQuasicoherent :=
    inferInstance
  haveI h₃i : ((Scheme.Modules.restrictFunctor (𝒰.f i)).obj S.X₃).IsQuasicoherent :=
    inferInstance
  exact isQuasicoherent_middle_affine hSi h₁i h₃i

/-- Quasi-coherent module sheaves on an arbitrary scheme are closed under
extensions. With `quasicoherent_isClosedUnderKernels` and
`quasicoherent_isClosedUnderCokernels`, this is the weak Serre property. -/
noncomputable instance quasicoherent_isClosedUnderExtensions (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ := isQuasicoherent_middle hS h₁ h₃


/-- **The zero sheaf is quasi-coherent.**

`SheafOfModules.isFinitePresentation_containsZero` already exhibits a zero sheaf
as finitely presented, and Mathlib turns finite presentation into
quasi-coherence, so this needs no `QuasicoherentData` of its own.

It is the fourth ingredient of the triangulated structure and the only one that
is not a closure property: `ObjectProperty.IsTriangulated` extends
`ContainsZero`, and closure under kernels cannot produce a first member of the
class from nothing. -/
noncomputable instance quasicoherent_containsZero (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ContainsZero where
  exists_zero := by
    obtain ⟨Z, hZ, hP⟩ :=
      (SheafOfModules.isFinitePresentation X.ringCatSheaf).exists_prop_of_containsZero
    letI : Z.IsFinitePresentation := hP
    exact ⟨Z, hZ, inferInstance⟩

/-- **The weak Serre property, assembled.**

Kernels and cokernels come from `CoherentSheaf/Quasicoherent/Kernels.lean`,
extensions and the zero object from this file. Stated as a check rather than a
definition: the point is that all four now resolve by instance search on an
arbitrary scheme, with no noetherian or quasi-compactness hypothesis, which is
exactly what `Dqc(X)`'s triangulated structure asks for. -/
example (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ContainsZero ∧
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderKernels ∧
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderCokernels ∧
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderExtensions :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

end

end AlgebraicGeometry
