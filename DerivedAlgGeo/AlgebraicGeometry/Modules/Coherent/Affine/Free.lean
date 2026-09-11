/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Category.FGModuleCat.Projective
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.Comparison
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# Free coherent sheaves on an affine noetherian scheme

`𝒪^k` on `Spec R`, as the coherent sheaf `tilde (Fin k → R)`, with the three facts the
affine `Ext` comparison consumes:

* it is projective among coherent sheaves, because `Fin k → R` is projective among finitely
  generated modules and `affineTilde` is a left adjoint whose right adjoint is an
  equivalence (`Adjunction.map_projective`);
* its underlying module sheaf is a biproduct of `k` copies of `𝒪`, because tilde is additive
  and `tilde R = 𝒪`;
* every coherent sheaf is a quotient of some `𝒪^k`, because every finitely generated module
  is a quotient of a free module of finite rank and `Coh (Spec R) ≌ FGModuleCat R`.

`Coh.affineFree` is an abbreviation so that instance search sees through it to
`affineTilde.obj _`.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}} [IsNoetherianRing R]

/-- `𝒪^k` as a coherent sheaf on `Spec R`: tilde of the free module of rank `k`. -/
noncomputable abbrev Coh.affineFree (k : ℕ) : Coh (Spec R) :=
  FGModuleCat.affineTilde.obj (FGModuleCat.of R (Fin k → R))

/-- `𝒪^k` is projective among coherent sheaves on an affine noetherian scheme. -/
theorem Coh.projective_affineFree (k : ℕ) : Projective (Coh.affineFree (R := R) k) :=
  haveI : (Coh.affineGlobalSections R).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (Coh.affineEquivalence (R := R)).toAdjunction
  (Coh.affineAdjunction (R := R)).map_projective _ (FGModuleCat.projective_of_finFree k)

attribute [local instance] Abelian.hasFiniteBiproducts in
/-- The underlying module sheaf of `𝒪^k` is a biproduct of `k` copies of `𝒪`. -/
noncomputable def Coh.ιAffineFreeIso (k : ℕ) :
    (Coh.ι (Spec R)).obj (Coh.affineFree k) ≅
      ⨁ (fun _ : Fin k ↦ (tilde.functor R).obj (ModuleCat.of R R)) :=
  (tilde.functor R).mapIso (ModuleCat.biproductIsoPi (fun _ : Fin k ↦ ModuleCat.of R R)).symm ≪≫
    (tilde.functor R).mapBiproduct (fun _ : Fin k ↦ ModuleCat.of R R)

/-- Every coherent sheaf on `Spec R` is a quotient of some `𝒪^k`. -/
theorem Coh.exists_affineFree_epi (X : Coh (Spec R)) :
    ∃ (P : Coh (Spec R)) (p : P ⟶ X), (∃ k, P = Coh.affineFree k) ∧ Epi p := by
  obtain ⟨k, q, hq⟩ := FGModuleCat.exists_finFree_epi ((Coh.affineGlobalSections R).obj X)
  haveI : (FGModuleCat.affineTilde (R := R)).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (Coh.affineAdjunction (R := R))
  haveI := hq
  haveI : Epi (FGModuleCat.affineTilde.map q) := Functor.map_epi _ q
  obtain ⟨u⟩ : Nonempty (FGModuleCat.affineTilde.obj ((Coh.affineGlobalSections R).obj X) ≅ X) :=
    ⟨(Coh.affineEquivalence (R := R)).unitIso.symm.app X⟩
  exact ⟨Coh.affineFree k, FGModuleCat.affineTilde.map q ≫ u.hom, ⟨k, rfl⟩, epi_comp _ _⟩

end AlgebraicGeometry
