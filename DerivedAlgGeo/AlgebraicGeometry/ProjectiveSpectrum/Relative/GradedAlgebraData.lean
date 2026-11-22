/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Quasicoherent.BasicOpen
import DerivedAlgGeo.LinearAlgebra.SymmetricAlgebra.Grading
import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
import Mathlib.RingTheory.GradedAlgebra.RingHom

/-!
# Quasi-coherent graded algebras as affine-local data

A quasi-coherent sheaf `𝒜` of `ℕ`-graded `𝒪_S`-algebras on a scheme `S` is recorded by its
sections over affine opens: a graded `Γ(S, U)`-algebra `𝒜(U)` for every affine open `U`, with
restriction maps to basic opens, such that `𝒜(D(f)) = 𝒜(U)_f`. This is the input of the relative
`Proj` construction (Stacks, Section 27.15).

## Main definitions

* `AlgebraicGeometry.Scheme.QuasicoherentGradedAlgebraData S`: the affine-local data of a
  quasi-coherent graded `𝒪_S`-algebra.
* `AlgebraicGeometry.Scheme.QuasicoherentGradedAlgebraData.sym E`: the symmetric algebra
  `Sym(E)` of a quasi-coherent module sheaf `E`, with `Sym(E)(U) = Sym_{Γ(S, U)} Γ(E, U)`.

## Implementation notes

The carrier follows Mathlib's `AlgebraicGeometry.Scheme.IdealSheafData`, which records an ideal
sheaf by its ideals over affine opens and the condition `I(D(f)) = I(U)_f` on basic opens only.
A graded algebra is not a subobject of `𝒪_S`, so its sections over different affine opens are
different rings, and the restriction maps are data. They are indexed by Mathlib's small affine
Zariski site `AlgebraicGeometry.Scheme.AffineZariskiSite`, whose arrows `V ⟶ U` are the basic
opens `V = D(f)` of `U`. The localization condition is required on those arrows alone, as for
`IdealSheafData.map_ideal_basicOpen` and for Mathlib's quasi-coherent `𝒪_S`-algebras
(`AlgebraicGeometry.Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway`);
arbitrary inclusions of affine opens carry no data. The degree-`d` pieces are recorded only as
the submodules `𝒜(U)_d`; gluing them into quasi-coherent module sheaves is not done here.

The carrier asks nothing about generation in degree one: `Proj` of a graded ring needs no such
hypothesis. The twisting sheaves `𝒪(d)`, which do, take it as the hypothesis
`GeneratedInDegreeOne` in `Relative/Twisting.lean`.

The independent consumers of the carrier are the projective bundles `P(E) = Proj_S(Sym(E))` built
from `sym`, projective morphisms, and the Plücker and Quot constructions. The reconstruction of a
scheme as the relative `Proj` of its section ring `⊕ f_* L^{⊗d}` (Stacks 0C6J) is a later
consumer.

## References

* [Stacks, Situation 27.15.1 (Tag 01NN)](https://stacks.math.columbia.edu/tag/01NN): the input
  of relative `Proj`.
* [Stacks, Section 17.21 (Tag 01CF)](https://stacks.math.columbia.edu/tag/01CF): the symmetric
  algebra of a sheaf of modules; Lemma 17.21.6 (Tag 01CL): it is quasi-coherent when the module
  is.
* EGA II, §3.1.

## Tags

relative Proj, quasi-coherent graded algebra, symmetric algebra, affine Zariski site
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

open AffineZariskiSite

/-- **A quasi-coherent sheaf of `ℕ`-graded `𝒪_S`-algebras**, as affine-local data
(Stacks 01NN): a graded `Γ(S, U)`-algebra `𝒜(U)` for every affine open `U`, and restriction maps
along the arrows `D(f) ⟶ U` of the affine Zariski site, such that `𝒜(D(f)) = 𝒜(U)_f`.

The localization condition is the only field-level claim; it is the quasi-coherence of `𝒜`.
Following `AlgebraicGeometry.Scheme.IdealSheafData`, it is asked on basic opens only. -/
structure QuasicoherentGradedAlgebraData (S : Scheme.{u}) where
  /-- The ring of sections `𝒜(U)` over an affine open `U`. -/
  carrier : S.AffineZariskiSite → Type u
  [commRing (U : S.AffineZariskiSite) : CommRing (carrier U)]
  [algebra (U : S.AffineZariskiSite) : Algebra Γ(S, U.toOpens) (carrier U)]
  /-- The degree-`d` part `𝒜(U)_d`. -/
  grading (U : S.AffineZariskiSite) : ℕ → Submodule Γ(S, U.toOpens) (carrier U)
  [gradedAlgebra (U : S.AffineZariskiSite) : GradedAlgebra (grading U)]
  /-- The restriction `𝒜(U) → 𝒜(V)` along an arrow `V ⟶ U` of the affine Zariski site, that is,
  for `V` a basic open of `U`. -/
  restrict {U V : S.AffineZariskiSite} (h : V ≤ U) : grading U →+*ᵍ grading V
  restrict_id (U : S.AffineZariskiSite) (x : carrier U) : restrict le_rfl x = x
  restrict_comp {U V W : S.AffineZariskiSite} (hVU : V ≤ U) (hWV : W ≤ V) (x : carrier U) :
    restrict hWV (restrict hVU x) = restrict (hWV.trans hVU) x
  restrict_algebraMap {U V : S.AffineZariskiSite} (h : V ≤ U) (r : Γ(S, U.toOpens)) :
    restrict h (algebraMap Γ(S, U.toOpens) (carrier U) r) =
      algebraMap Γ(S, V.toOpens) (carrier V) (S.presheaf.map (homOfLE (toOpens_mono h)).op r)
  /-- Quasi-coherence: `𝒜(D(f)) = 𝒜(U)_f`. -/
  isLocalization_basicOpen (U : S.AffineZariskiSite) (f : Γ(S, U.toOpens)) :
    letI := (restrict (U.basicOpen_le f)).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap Γ(S, U.toOpens) (carrier U) f) (carrier (U.basicOpen f))

attribute [instance] QuasicoherentGradedAlgebraData.commRing
  QuasicoherentGradedAlgebraData.algebra QuasicoherentGradedAlgebraData.gradedAlgebra

namespace QuasicoherentGradedAlgebraData

variable {S : Scheme.{u}}

section Sym

variable (E : S.Modules) {U V W : S.Opens}

/-- `Γ(S, U)` acts on `Γ(S, V)` by restriction, for `V ≤ U`. -/
private noncomputable abbrev resAlgebra (h : V ≤ U) : Algebra Γ(S, U) Γ(S, V) :=
  (S.presheaf.map (homOfLE h).op).hom.toAlgebra

/-- `Γ(S, U)` acts on `Γ(E, V)` by restriction of scalars, for `V ≤ U`. -/
private noncomputable abbrev resModule (h : V ≤ U) : Module Γ(S, U) Γ(E, V) :=
  Module.compHom _ (S.presheaf.map (homOfLE h).op).hom

private lemma resIsScalarTower (h : V ≤ U) :
    letI := resAlgebra h
    letI := resModule E h
    IsScalarTower Γ(S, U) Γ(S, V) Γ(E, V) :=
  letI := resAlgebra h
  letI := resModule E h
  ⟨fun r s x ↦ mul_smul (S.presheaf.map (homOfLE h).op r) s x⟩

/-- The restriction `Γ(E, U) → Γ(E, V)`, linear over `Γ(S, U)`. -/
private noncomputable def resLinearMap (h : V ≤ U) :
    letI := resModule E h
    Γ(E, U) →ₗ[Γ(S, U)] Γ(E, V) :=
  letI := resModule E h
  { toFun := E.presheaf.map (homOfLE h).op
    map_add' := map_add _
    map_smul' := fun r x ↦ E.map_smul (homOfLE h) r x }

/-- The restriction `Sym_{Γ(S, U)} Γ(E, U) → Sym_{Γ(S, V)} Γ(E, V)`. -/
private noncomputable def symRestrict (h : V ≤ U) :
    SymmetricAlgebra Γ(S, U) Γ(E, U) →+* SymmetricAlgebra Γ(S, V) Γ(E, V) :=
  letI := resAlgebra h
  letI := resModule E h
  haveI := resIsScalarTower E h
  (SymmetricAlgebra.map Γ(S, V) (resLinearMap E h)).toRingHom

private lemma symRestrict_ι (h : V ≤ U) (x : Γ(E, U)) :
    symRestrict E h (SymmetricAlgebra.ι _ _ x) =
      SymmetricAlgebra.ι _ _ (E.presheaf.map (homOfLE h).op x) :=
  letI := resAlgebra h
  letI := resModule E h
  haveI := resIsScalarTower E h
  SymmetricAlgebra.map_ι (resLinearMap E h) x

private lemma symRestrict_algebraMap (h : V ≤ U) (r : Γ(S, U)) :
    symRestrict E h (algebraMap _ _ r) = algebraMap _ _ (S.presheaf.map (homOfLE h).op r) :=
  letI := resAlgebra h
  letI := resModule E h
  haveI := resIsScalarTower E h
  SymmetricAlgebra.map_algebraMap (resLinearMap E h) r

private lemma symRestrict_mem (h : V ≤ U) {n : ℕ} {x : SymmetricAlgebra Γ(S, U) Γ(E, U)}
    (hx : x ∈ SymmetricAlgebra.gradedPiece Γ(S, U) Γ(E, U) n) :
    symRestrict E h x ∈ SymmetricAlgebra.gradedPiece Γ(S, V) Γ(E, V) n :=
  letI := resAlgebra h
  letI := resModule E h
  haveI := resIsScalarTower E h
  SymmetricAlgebra.map_mem_gradedPiece (resLinearMap E h) hx

private lemma symRestrict_id (x : SymmetricAlgebra Γ(S, U) Γ(E, U)) :
    symRestrict E le_rfl x = x := by
  suffices symRestrict E (le_refl U) = RingHom.id _ from congr($this x)
  refine SymmetricAlgebra.ringHom_ext (RingHom.ext fun r ↦ ?_) fun x ↦ ?_
  · simp [symRestrict_algebraMap]
  · simp [symRestrict_ι]

private lemma symRestrict_comp (hVU : V ≤ U) (hWV : W ≤ V)
    (x : SymmetricAlgebra Γ(S, U) Γ(E, U)) :
    symRestrict E hWV (symRestrict E hVU x) = symRestrict E (hWV.trans hVU) x := by
  suffices (symRestrict E hWV).comp (symRestrict E hVU) = symRestrict E (hWV.trans hVU) from
    congr($this x)
  refine SymmetricAlgebra.ringHom_ext (RingHom.ext fun r ↦ ?_) fun x ↦ ?_
  · simp only [RingHom.comp_apply, symRestrict_algebraMap]
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  · simp only [RingHom.comp_apply, symRestrict_ι]
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl

/-- **The symmetric algebra of a quasi-coherent module sheaf** (Stacks 01CF, 01CL), as a
quasi-coherent graded algebra: `Sym(E)(U) = Sym_{Γ(S, U)} Γ(E, U)`, graded by degree. -/
noncomputable def sym [E.IsQuasicoherent] : S.QuasicoherentGradedAlgebraData where
  carrier U := SymmetricAlgebra Γ(S, U.toOpens) Γ(E, U.toOpens)
  grading U := SymmetricAlgebra.gradedPiece Γ(S, U.toOpens) Γ(E, U.toOpens)
  restrict h :=
    { toRingHom := symRestrict E (toOpens_mono h)
      map_mem := symRestrict_mem E (toOpens_mono h) }
  restrict_id U x := symRestrict_id E x
  restrict_comp hVU hWV x := symRestrict_comp E _ _ x
  restrict_algebraMap h r := symRestrict_algebraMap E _ r
  isLocalization_basicOpen U f := by
    let _ := resAlgebra (S.basicOpen_le f)
    let _ := resModule E (S.basicOpen_le f)
    have := resIsScalarTower E (S.basicOpen_le f)
    have : IsLocalization.Away f Γ(S, S.basicOpen f) := U.2.isLocalization_basicOpen f
    have := E.isLocalizedModule_basicOpen U.2 f (resLinearMap E (S.basicOpen_le f)) fun _ ↦ rfl
    exact SymmetricAlgebra.isLocalization_away_map (R' := Γ(S, S.basicOpen f))
      (resLinearMap E (S.basicOpen_le f)) f

theorem sym_carrier [E.IsQuasicoherent] (U : S.AffineZariskiSite) :
    (sym E).carrier U = SymmetricAlgebra Γ(S, U.toOpens) Γ(E, U.toOpens) :=
  rfl

theorem sym_grading [E.IsQuasicoherent] (U : S.AffineZariskiSite) :
    (sym E).grading U = SymmetricAlgebra.gradedPiece Γ(S, U.toOpens) Γ(E, U.toOpens) :=
  rfl

/-- The restriction maps of `sym E` send a generator `x` to the generator `x|_V`. -/
theorem sym_restrict_ι [E.IsQuasicoherent] {U V : S.AffineZariskiSite} (h : V ≤ U)
    (x : Γ(E, U.toOpens)) :
    (sym E).restrict h (SymmetricAlgebra.ι _ _ x) =
      SymmetricAlgebra.ι _ _ (E.presheaf.map (homOfLE (toOpens_mono h)).op x) :=
  symRestrict_ι E _ x

end Sym

end QuasicoherentGradedAlgebraData

end AlgebraicGeometry.Scheme
