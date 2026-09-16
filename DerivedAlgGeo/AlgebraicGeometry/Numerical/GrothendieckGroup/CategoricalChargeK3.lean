/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.GrothendieckGroup.CentralChargeK3
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.CentralCharge.Quadratic
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Mukai.Charge

/-!
# The categorical Mukai charge is the numerical charge of the object's class

`MukaiChargeData C W` carries a hom `K₀Ab A →+ RealExtension W` and nothing ties
it to any geometry: an arbitrary hom typechecks, so `charge` need not be the
charge of anything.  Separately, `AdditiveMukaiData.numericalCharge` computes the
same shape from a **numerical** class in `N`, and the two were never related by
any lemma.

That gap is why the support-property theorems proved on the numerical side —
`numericalCharge_ne_zero_of_nonneg`, `mukaiForm_neg_of_numericalCharge_eq_zero`,
`mem_wall_iff_numericalCharge_eq_zero` — were unreachable from an object of a
heart, which is exactly what a stability function's positivity obligation holds.

## What this file does

`toMukaiChargeData` builds the class map as a **composition of homs**

```
K₀Ab A --cl--> N --mukaiVectorHom--> MukaiLattice Λ --extendMapHom--> RealExtension W
```

so `charge_toMukaiChargeData` is definitional: the categorical charge of an object *is*
the numerical charge of its class.  Nothing along the chain re-proves additivity,
and a `MukaiChargeData` built this way cannot be unrelated to the geometry,
because the geometry is what it is made of.

## What is still supplied, not proved

`cl : K₀Ab A →+ N` is an argument.  Nothing in this repository constructs one —
The generic `K₀.Realization` root likewise treats such a class map as supplied,
so this file makes the comparison available without pretending it exists.

The **numerical quotient** is also still bypassed.  `N` is documented as
`K(X)/≡`, but the lane quotients it again by `leftRadical`, and the only
geometric class map in the tree lands in that quotient while `numericalCharge`
is defined on `N`.  Until `leftRadical ≤ ker mukaiVectorHom` is proved, the
support-property theorems keep their `extendMap … ≠ 0` hypotheses instead of the
`E ≠ 0` a consumer can actually discharge.
-/

universe w' w v u

open CategoryTheory CategoryTheory.Triangulated

namespace AlgebraicGeometry.Numerical.K3

noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {R N Λ : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup N] [AddCommGroup Λ]
variable {V : NumericalVarietyData 2 R N}
variable {W : Type w'} [NormedAddCommGroup W] [NormedSpace ℝ W]

namespace AdditiveMukaiData

variable (D : AdditiveMukaiData V Λ) (f : Λ →ₗ[ℤ] W) (cl : K₀Ab C →+ N)

/-- **The categorical Mukai charge carrier built from numerical data.**

The class map is the composite of three homs, so the three formal properties a
charge needs are inherited rather than restated. -/
def toMukaiChargeData : MukaiChargeData C W where
  mukai := (Mukai.extendMapHom f).comp (D.mukaiVectorHom.comp cl)

@[simp]
theorem toMukaiChargeData_mukai (x : K₀Ab C) :
    (D.toMukaiChargeData f cl).mukai x
      = Mukai.extendMap f (D.mukaiVectorHom (cl x)) := rfl

variable (bR : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (β ω : W)

/-- **The lemma that was missing**: the categorical charge of an object is the
numerical charge of its class.

Definitional, because the class map is a composition of homs rather than a
separately-postulated function. Its use is that every support-property theorem
stated about `numericalCharge` now applies to an object of an abelian category
through its class. -/
theorem charge_toMukaiChargeData (E : C) :
    (D.toMukaiChargeData f cl).charge bR β ω E
      = D.numericalCharge bR f β ω (cl (K₀Ab.of E)) :=
  rfl

variable {D bR f β ω}

/-- **A wall is a vanishing charge**, for the class of an object.  This
interpretation lives in the categorical stability adapter so the underlying
numerical charge remains independent of wall loci. -/
theorem mem_wall_iff_numericalCharge_eq_zero (hb : ∀ x y : W, bR x y = bR y x)
    (hω : 0 < bR ω ω) (E : N) :
    PeriodDomain.pairSpan (Mukai.expRe bR β ω) (Mukai.expIm bR β ω) ∈
        PeriodDomain.orthogonalityLocus (Mukai.realForm bR) (Mukai.extendMap f (D.mukaiVectorHom E)) ↔
      D.numericalCharge bR f β ω E = 0 :=
  Mukai.mem_orthogonalityLocus_iff_expCharge_eq_zero bR β ω hb hω

end AdditiveMukaiData

end

end AlgebraicGeometry.Numerical.K3
