/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Epi
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Relative.Functoriality

/-!
# Projective bundles

The projective bundle of a quasi-coherent module sheaf `E` on a scheme `S` is
`P(E) = Proj_S(Sym E)` (Stacks 01OB). It is separated over `S` (Stacks 01OD), and a surjection
`E ↠ F` of quasi-coherent modules induces a closed immersion `P(F) ⟶ P(E)` over `S`.

## Main definitions

* `QuasicoherentGradedAlgebraData.symMap p`: the map `Sym(E) ⟶ Sym(F)` of quasi-coherent graded
  algebras induced by `p : E ⟶ F`.
* `Scheme.projectiveBundle E`: the projective bundle `P(E) = Proj_S(Sym E)`, with its structure
  morphism `P(E) ↘ S`.
* `Scheme.projectiveBundleMapOfEpi p`: for an epimorphism `p : E ⟶ F` of quasi-coherent modules,
  the morphism `P(F) ⟶ P(E)` over `S`.

## Main results

* `QuasicoherentGradedAlgebraData.symMap_app_surjective`: `Sym(p)` is surjective over an affine
  open on which `p` is surjective.
* `Scheme.projectiveBundle.isSeparated`: `P(E) → S` is separated (Stacks 01OD).
* `Scheme.projectiveBundleMapOfEpi.isClosedImmersion`: `P(F) ⟶ P(E)` is a closed immersion.

## Implementation notes

`P(E)` follows Grothendieck (EGA II 4.1.1): it is built from `Sym E`, not from `Sym(E^∨)`, and
`E` is not required to be finite locally free. Stacks 01O8 identifies the `T`-points of `P(E)`
with the invertible quotients of the pullback of `E` to `T`; that description is not proved here.

An epimorphism of quasi-coherent module sheaves is surjective on sections over every affine open
(`AlgebraicGeometry.Scheme.Modules.surjective_app_of_epi_of_isAffineOpen`), so `Sym(p)` is
surjective chart by chart and `P(F) ⟶ P(E)` is the chartwise closed immersion of
`QuasicoherentGradedAlgebraData.isClosedImmersion_relativeProjMap`.

## References

* [Stacks, Section 27.21 (Tag 01OA)](https://stacks.math.columbia.edu/tag/01OA): projective
  bundles, Definition 27.21.1 (Tag 01OB) and Lemma 27.21.4 (Tag 01OD).
* [Stacks, Lemma 27.18.3 (Tag 07ZI)](https://stacks.math.columbia.edu/tag/07ZI): a surjection of
  graded algebras gives a closed immersion.
* EGA II, §4.1.

## Tags

projective bundle, relative Proj, symmetric algebra, closed immersion
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

open AffineZariskiSite

namespace QuasicoherentGradedAlgebraData

variable {S : Scheme.{u}} {E F : S.Modules}

section SymMap

/-- The sections `Γ(E, U) → Γ(F, U)` of a map of module sheaves, as a `Γ(S, U)`-linear map. -/
private noncomputable def appLinearMap (p : E ⟶ F) (U : S.Opens) :
    Γ(E, U) →ₗ[Γ(S, U)] Γ(F, U) where
  toFun x := p.app U x
  map_add' := map_add _
  map_smul' := p.app_smul

/-- `Sym_{Γ(S, U)}` of `p(U) : Γ(E, U) → Γ(F, U)`, as a ring map. -/
private noncomputable def symMapRingHom (p : E ⟶ F) (U : S.Opens) :
    SymmetricAlgebra Γ(S, U) Γ(E, U) →+* SymmetricAlgebra Γ(S, U) Γ(F, U) :=
  (SymmetricAlgebra.map Γ(S, U) (appLinearMap p U)).toRingHom

private theorem symMapRingHom_ι (p : E ⟶ F) (U : S.Opens) (x : Γ(E, U)) :
    symMapRingHom p U (SymmetricAlgebra.ι _ _ x) = SymmetricAlgebra.ι _ _ (p.app U x) :=
  SymmetricAlgebra.map_ι _ x

private theorem symMapRingHom_algebraMap (p : E ⟶ F) (U : S.Opens) (r : Γ(S, U)) :
    symMapRingHom p U (algebraMap _ _ r) = algebraMap _ _ r :=
  AlgHom.commutes _ r

/-- The restriction maps of `sym M`, as ring maps between symmetric algebras. -/
private noncomputable def symRes (M : S.Modules) [M.IsQuasicoherent]
    {U V : S.AffineZariskiSite} (h : V ≤ U) :
    SymmetricAlgebra Γ(S, U.toOpens) Γ(M, U.toOpens) →+*
      SymmetricAlgebra Γ(S, V.toOpens) Γ(M, V.toOpens) :=
  ((sym M).restrict h).toRingHom

private theorem symRes_ι (M : S.Modules) [M.IsQuasicoherent] {U V : S.AffineZariskiSite}
    (h : V ≤ U) (x : Γ(M, U.toOpens)) :
    symRes M h (SymmetricAlgebra.ι _ _ x) =
      SymmetricAlgebra.ι _ _ (M.presheaf.map (homOfLE (toOpens_mono h)).op x) :=
  sym_restrict_ι M h x

private theorem symRes_algebraMap (M : S.Modules) [M.IsQuasicoherent]
    {U V : S.AffineZariskiSite} (h : V ≤ U) (r : Γ(S, U.toOpens)) :
    symRes M h (algebraMap _ _ r) =
      algebraMap _ _ (S.presheaf.map (homOfLE (toOpens_mono h)).op r) :=
  (sym M).restrict_algebraMap h r

variable [E.IsQuasicoherent] [F.IsQuasicoherent]

private theorem symMapRingHom_comp_symRes (p : E ⟶ F) {U V : S.AffineZariskiSite} (h : V ≤ U) :
    (symMapRingHom p V.toOpens).comp (symRes E h) =
      (symRes F h).comp (symMapRingHom p U.toOpens) := by
  refine SymmetricAlgebra.ringHom_ext (RingHom.ext fun r ↦ ?_) fun y ↦ ?_
  · simp only [RingHom.comp_apply, symRes_algebraMap, symMapRingHom_algebraMap]
  · simp only [RingHom.comp_apply, symRes_ι, symMapRingHom_ι]
    congr 1
    exact NatTrans.naturality_apply p.mapPresheaf (homOfLE (toOpens_mono h)).op y

/-- **`Sym` is functorial**: a map `p : E ⟶ F` of quasi-coherent module sheaves induces the map
`Sym(E) ⟶ Sym(F)` of quasi-coherent graded algebras given over an affine open `U` by
`Sym_{Γ(S, U)}(p(U))`. -/
noncomputable def symMap (p : E ⟶ F) : sym E ⟶ sym F where
  app U :=
    { toRingHom := symMapRingHom p U.toOpens
      map_mem := SymmetricAlgebra.map_mem_gradedPiece _ }
  app_algebraMap U r := symMapRingHom_algebraMap p U.toOpens r
  app_restrict h x := DFunLike.congr_fun (symMapRingHom_comp_symRes p h) x

/-- `Sym(p)` is surjective over an affine open on which `p` is surjective. -/
theorem symMap_app_surjective (p : E ⟶ F) {U : S.AffineZariskiSite}
    (hp : Function.Surjective (p.app U.toOpens)) :
    Function.Surjective ((symMap p).app U) :=
  SymmetricAlgebra.map_surjective (g := appLinearMap p U.toOpens) hp

end SymMap

end QuasicoherentGradedAlgebraData

open QuasicoherentGradedAlgebraData

variable {S : Scheme.{u}}

/-- **The projective bundle** `P(E) = Proj_S(Sym E)` of a quasi-coherent module sheaf `E`
(Stacks 01OB, EGA II 4.1.1). It is built from `Sym E`, not from `Sym(E^∨)`, and `E` need not be
finite locally free. -/
noncomputable def projectiveBundle (E : S.Modules) [E.IsQuasicoherent] : Scheme.{u} :=
  (sym E).relativeProj

namespace projectiveBundle

variable (E : S.Modules) [E.IsQuasicoherent]

/-- The structure morphism `P(E) ⟶ S`. -/
@[simps -isSimp]
noncomputable instance over : (projectiveBundle E).CanonicallyOver S where
  hom := (sym E).relativeProjToBase

/-- **`P(E) → S` is separated** (Stacks 01OD). -/
instance isSeparated : IsSeparated (projectiveBundle E ↘ S) :=
  inferInstanceAs (IsSeparated (sym E).relativeProjToBase)

end projectiveBundle

variable {E F : S.Modules} [E.IsQuasicoherent] [F.IsQuasicoherent] (p : E ⟶ F) [Epi p]

/-- **A surjection of quasi-coherent modules gives a morphism of projective bundles**: for an
epimorphism `p : E ⟶ F`, the morphism `P(F) ⟶ P(E)` over `S` induced by `Sym(p)`. It is a closed
immersion (`projectiveBundleMapOfEpi.isClosedImmersion`). -/
noncomputable def projectiveBundleMapOfEpi : projectiveBundle F ⟶ projectiveBundle E :=
  relativeProjMap (symMap p) fun U ↦ Proj.irrelevant_le_map_of_surjective _
    (symMap_app_surjective p (Modules.surjective_app_of_epi_of_isAffineOpen p U.toOpens U.2))

namespace projectiveBundleMapOfEpi

/-- `P(F) ⟶ P(E)` lies over `S`. -/
instance isOver : (projectiveBundleMapOfEpi p).IsOver S where
  comp_over := relativeProjMap_toBase _ _

/-- **`P(F) ⟶ P(E)` is a closed immersion** for an epimorphism `E ⟶ F` of quasi-coherent
modules: over an affine open `U` it is `Proj` of the surjection `Sym Γ(E, U) → Sym Γ(F, U)`
(Stacks 07ZI, 01N0). -/
instance isClosedImmersion : IsClosedImmersion (projectiveBundleMapOfEpi p) :=
  isClosedImmersion_relativeProjMap _ _ fun U ↦
    symMap_app_surjective p (Modules.surjective_app_of_epi_of_isAffineOpen p U.toOpens U.2)

end projectiveBundleMapOfEpi

end AlgebraicGeometry.Scheme
