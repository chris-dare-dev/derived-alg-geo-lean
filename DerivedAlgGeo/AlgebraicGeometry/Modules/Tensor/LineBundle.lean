/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Monoidal
import DerivedAlgGeo.Algebra.Category.ModuleCat.Presheaf.Sections

/-!
# Line-bundle data

This file is the neutral home for a line bundle together with a chosen tensor inverse. The
definition belongs with the scheme-level tensor product: it does not depend on divisors,
determinants, exterior powers, or the Picard group.

Downstream geometric theories may attach their own interpretations to this common root. For
example, `Divisors.Determinant` constructs Picard-group classes and fixed-rank locally free data,
while pullback and projection-formula APIs can use the underlying line-bundle structure directly.

The chosen inverse also makes tensoring by the line bundle an equivalence, with tensoring by the
inverse as a specified quasi-inverse. Its adjunction supplies the expected equivalence
`Hom(L ⊗ M, N) ≃ Hom(M, L⁻¹ ⊗ N)`. Specializing `M` to the tensor unit identifies
`Hom(L, N)` with the global sections of `L⁻¹ ⊗ N`.

These are equivalences of types. A finite-dimensionality argument over a base field additionally
needs their scalar-linearity. That is deliberately not asserted here: the present sheafified
tensor API has no `MonoidalLinear` instance on `X.Modules`. Thus this file closes the categorical
part of the line-bundle Hom comparison while leaving the exact linear compatibility obligation
visible to the Serre/Hom-finiteness lane.
-/

open CategoryTheory Limits MonoidalCategory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

noncomputable section

/-- An invertible sheaf together with an explicit tensor inverse.

The two intrinsic invertibility certificates make the underlying sheaves available to generic
module-theoretic consumers. The explicit tensor inverse is retained as structure, so downstream
Picard and duality constructions do not have to choose it again. -/
structure LineBundleData (X : Scheme.{u}) where
  line : X.Modules
  inverse : X.Modules
  lineIsInvertible :
    SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from line)
  inverseIsInvertible :
    SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from inverse)
  tensorInverseIso :
    tensorObj line inverse ≅ SheafOfModules.unit X.ringCatSheaf

/-- Maps from the tensor unit are the sections over the top open.

Mathlib first identifies a map from the unit with a compatible family of sections. Since `⊤` is
terminal in the category of opens, such a family is equivalent to its component over `⊤`. -/
noncomputable def unitHomTopEquiv (M : X.Modules) :
    ((SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M) ≃ Γ(M, ⊤) :=
  (show SheafOfModules X.ringCatSheaf from M).unitHomEquiv.trans
    ((show SheafOfModules X.ringCatSheaf from M).val.sectionsEquivOfIsTerminal
      isTerminalTop)

namespace LineBundleData

instance (L : LineBundleData X) :
    SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L.line) :=
  L.lineIsInvertible

instance (L : LineBundleData X) :
    SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L.inverse) :=
  L.inverseIsInvertible

section Unit

local instance : Category X.Opens :=
  inferInstanceAs (Category (TopologicalSpace.Opens X))

private theorem unitIsInvertible (X : Scheme.{u}) :
    SheafOfModules.IsInvertible.{u, u, u}
      (SheafOfModules.unit X.ringCatSheaf) := by
  let q₀ := (SheafOfModules.free.generatingSections
    (R := X.ringCatSheaf) PUnit.{u + 1}).localGeneratorsData
  let e : SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1} ≅
      SheafOfModules.unit X.ringCatSheaf := SheafOfModules.freePUnitIsoUnit
  letI : q₀.IsLocallyFreeData := by
    dsimp [q₀]
    infer_instance
  exact
    { exists_rankOneData := ⟨q₀.ofIso e, inferInstance, by
        intro i
        change Nonempty PUnit ∧ Subsingleton PUnit
        exact ⟨inferInstance, inferInstance⟩⟩ }

/-- The structure sheaf with itself as tensor inverse. -/
noncomputable def unit (X : Scheme.{u}) : LineBundleData X where
  line := SheafOfModules.unit X.ringCatSheaf
  inverse := SheafOfModules.unit X.ringCatSheaf
  lineIsInvertible := unitIsInvertible X
  inverseIsInvertible := unitIsInvertible X
  tensorInverseIso := tensorUnitLeftIso _

end Unit

/-- The inverse line bundle, with the two recorded representatives exchanged. -/
noncomputable def dual (L : LineBundleData X) : LineBundleData X where
  line := L.inverse
  inverse := L.line
  lineIsInvertible := L.inverseIsInvertible
  inverseIsInvertible := L.lineIsInvertible
  tensorInverseIso := tensorCommIso L.inverse L.line ≪≫ L.tensorInverseIso

/-- Tensoring by a line bundle is an equivalence, with tensoring by its recorded inverse as the
specified quasi-inverse.

The two composites are reduced to tensoring by `L⁻¹ ⊗ L` and `L ⊗ L⁻¹` using the
associator, then to the identity using the two tensor-inverse isomorphisms and the left unitor.
`Equivalence.mk` performs the standard normalization needed for the triangle identity; no rigid
or closed monoidal structure is assumed. -/
noncomputable def tensorLeftEquivalence (L : LineBundleData X) : X.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk
    (tensorLeft L.line)
    (tensorLeft L.inverse)
    ((leftUnitorNatIso X.Modules).symm ≪≫
      (tensoringLeft X.Modules).mapIso L.dual.tensorInverseIso.symm ≪≫
      tensorLeftTensor L.inverse L.line)
    ((tensorLeftTensor L.line L.inverse).symm ≪≫
      (tensoringLeft X.Modules).mapIso L.tensorInverseIso ≪≫
      leftUnitorNatIso X.Modules)

/-- Moving a line-bundle factor across a Hom uses the recorded tensor inverse.

This is the Hom equivalence of `tensorLeftEquivalence`; in particular it is natural in `M` and
`N` through the adjunction API. -/
noncomputable def tensorLeftHomEquiv (L : LineBundleData X) (M N : X.Modules) :
    (tensorObj L.line M ⟶ N) ≃ (M ⟶ tensorObj L.inverse N) :=
  L.tensorLeftEquivalence.toAdjunction.homEquiv M N

/-- The forward Hom equivalence is the adjunction unit followed by tensoring the morphism with
the identity of the inverse line bundle. -/
@[simp]
theorem tensorLeftHomEquiv_apply (L : LineBundleData X) (M N : X.Modules)
    (f : tensorObj L.line M ⟶ N) :
    L.tensorLeftHomEquiv M N f =
      L.tensorLeftEquivalence.unit.app M ≫ tensorHom (𝟙 L.inverse) f := by
  exact L.tensorLeftEquivalence.toAdjunction.homEquiv_unit M N f

/-- The inverse Hom equivalence tensors the morphism with the identity of the line bundle and
then applies the adjunction counit. -/
@[simp]
theorem tensorLeftHomEquiv_symm_apply (L : LineBundleData X) (M N : X.Modules)
    (f : M ⟶ tensorObj L.inverse N) :
    (L.tensorLeftHomEquiv M N).symm f =
      tensorHom (𝟙 L.line) f ≫ L.tensorLeftEquivalence.counit.app N := by
  exact L.tensorLeftEquivalence.toAdjunction.homEquiv_counit M N f

/-- The line-bundle Hom/sections comparison:
`Hom(L, N) ≃ Γ(X, L⁻¹ ⊗ N)`.

This is the reusable categorical reduction behind the usual proof that Hom spaces between
coherent sheaves on a projective variety are finite-dimensional. The remaining input for that
application is a scalar-linear refinement of this equivalence, together with coherence and Serre
finiteness for `L⁻¹ ⊗ N`. -/
noncomputable def lineHomTopEquiv (L : LineBundleData X) (N : X.Modules) :
    (L.line ⟶ N) ≃ Γ(tensorObj L.inverse N, ⊤) :=
  (Iso.homCongr (tensorUnitRightIso L.line).symm (Iso.refl N)).trans
    ((L.tensorLeftHomEquiv (SheafOfModules.unit X.ringCatSheaf) N).trans
      (unitHomTopEquiv (tensorObj L.inverse N)))

/-- Tensor product of explicitly invertible line bundles. -/
noncomputable def tensor (L M : LineBundleData X) : LineBundleData X where
  line := tensorObj L.line M.line
  inverse := tensorObj M.inverse L.inverse
  lineIsInvertible := isInvertible_tensorObj L.line M.line
  inverseIsInvertible := isInvertible_tensorObj M.inverse L.inverse
  tensorInverseIso :=
    tensorAssocIso L.line M.line (tensorObj M.inverse L.inverse) ≪≫
      tensorObjIso (Iso.refl L.line)
        ((tensorAssocIso M.line M.inverse L.inverse).symm ≪≫
          tensorObjIso M.tensorInverseIso (Iso.refl L.inverse) ≪≫
          tensorUnitLeftIso L.inverse) ≪≫
      L.tensorInverseIso

end LineBundleData

end

end AlgebraicGeometry.Scheme.Modules
