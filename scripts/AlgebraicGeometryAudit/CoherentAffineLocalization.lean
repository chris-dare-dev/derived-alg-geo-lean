import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.Localization

/-! # Affine coherent localization audits and direct clients -/

open CategoryTheory

universe u

#print axioms AlgebraicGeometry.Coh.fixedTargetArrowExtension_pullbackSpecMap_of_isLocalization
#print axioms AlgebraicGeometry.Coh.exists_fixedTerminalThreeTerm_pullbackSpecMap_of_isLocalization
#print axioms AlgebraicGeometry.Coh.exists_finite_window_complex_model_pullbackSpecMap_of_isLocalization

-- Import only the owner leaf and use its public theorem on an arbitrary arrow.
example {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] (S : Submonoid R) [IsLocalization S A]
    (E : AlgebraicGeometry.Coh (AlgebraicGeometry.Spec (CommRingCat.of R)))
    (Z : AlgebraicGeometry.Coh (AlgebraicGeometry.Spec (CommRingCat.of A)))
    (β : Z ⟶ (AlgebraicGeometry.Coh.pullback
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj E) :
    ∃ (Y : AlgebraicGeometry.Coh (AlgebraicGeometry.Spec (CommRingCat.of R)))
      (f : Y ⟶ E)
      (e : Z ≅ (AlgebraicGeometry.Coh.pullback
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj Y),
      β = e.hom ≫ (AlgebraicGeometry.Coh.pullback
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R A)))).map f := by
  exact AlgebraicGeometry.Coh.fixedTargetArrowExtension_pullbackSpecMap_of_isLocalization
    S E β

-- The terminal coherent sheaf is arbitrary and remains fixed; the source and middle
-- coherent sheaves are merely isomorphic to pullbacks of the descended objects.
example {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] (S : Submonoid R) [IsLocalization S A]
    (E : AlgebraicGeometry.Coh (AlgebraicGeometry.Spec (CommRingCat.of R)))
    (N₀ N₁ : AlgebraicGeometry.Coh (AlgebraicGeometry.Spec (CommRingCat.of A)))
    (d : N₀ ⟶ N₁)
    (β : N₁ ⟶ (AlgebraicGeometry.Coh.pullback
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj E)
    (hz : d ≫ β = 0) :
    ∃ (L₀ L₁ : AlgebraicGeometry.Coh (AlgebraicGeometry.Spec (CommRingCat.of R)))
      (d₀ : L₀ ⟶ L₁) (f : L₁ ⟶ E)
      (e₀ : N₀ ≅ (AlgebraicGeometry.Coh.pullback
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj L₀)
      (e₁ : N₁ ≅ (AlgebraicGeometry.Coh.pullback
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj L₁),
      d₀ ≫ f = 0 ∧
      d ≫ e₁.hom = e₀.hom ≫ (AlgebraicGeometry.Coh.pullback
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R A)))).map d₀ ∧
      β = e₁.hom ≫ (AlgebraicGeometry.Coh.pullback
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R A)))).map f := by
  exact AlgebraicGeometry.Coh.exists_fixedTerminalThreeTerm_pullbackSpecMap_of_isLocalization
    S E N₀ N₁ d β hz

-- The complex-object theorem needs only strict bounds and no target finiteness hypothesis.
example {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] (S : Submonoid R) [IsLocalization S A]
    (lo hi : ℤ)
    (K : CochainComplex
      (AlgebraicGeometry.Coh (AlgebraicGeometry.Spec (CommRingCat.of A))) ℤ)
    [K.IsStrictlyGE lo] [K.IsStrictlyLE hi] :
    ∃ (L : CochainComplex
      (AlgebraicGeometry.Coh (AlgebraicGeometry.Spec (CommRingCat.of R))) ℤ),
      L.IsStrictlyGE lo ∧ L.IsStrictlyLE hi ∧
      Nonempty (K ≅ ((AlgebraicGeometry.Coh.pullback
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R A)))).mapHomologicalComplex
          (.up ℤ)).obj L) := by
  exact AlgebraicGeometry.Coh.exists_finite_window_complex_model_pullbackSpecMap_of_isLocalization
    S lo hi K
