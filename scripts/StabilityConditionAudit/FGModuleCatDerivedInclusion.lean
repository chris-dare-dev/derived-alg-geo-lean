import DerivedAlgGeo.Algebra.Homology.DerivedCategory.FGModuleCatInclusion

/-! Audit and direct clients for bounded derived inclusion of finite modules. -/

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

#print axioms FGModuleCat.derivedInclusion
#print axioms FGModuleCat.boundedDerivedInclusion_map_bijective

noncomputable section

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  (E E' : DerivedCategory.Bounded (FGModuleCat.{u} R))

example (g : (DerivedCategory.Bounded.ι ⋙
    (FGModuleCat.derivedInclusion (R := R))).obj E ⟶
      (DerivedCategory.Bounded.ι ⋙
        (FGModuleCat.derivedInclusion (R := R))).obj E') :
    ∃ f : E ⟶ E',
      (DerivedCategory.Bounded.ι ⋙
        (FGModuleCat.derivedInclusion (R := R))).map f = g :=
  (FGModuleCat.boundedDerivedInclusion_map_bijective E E').2 g

example (f g : E ⟶ E')
    (h : (DerivedCategory.Bounded.ι ⋙
      (FGModuleCat.derivedInclusion (R := R))).map f =
        (DerivedCategory.Bounded.ι ⋙
          (FGModuleCat.derivedInclusion (R := R))).map g) : f = g :=
  (FGModuleCat.boundedDerivedInclusion_map_bijective E E').1 h

end
