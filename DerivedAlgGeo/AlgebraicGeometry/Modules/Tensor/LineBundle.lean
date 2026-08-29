/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Monoidal

/-!
# Line-bundle data

This file is the neutral home for a line bundle together with a chosen tensor inverse. The
definition belongs with the scheme-level tensor product: it does not depend on divisors,
determinants, exterior powers, or the Picard group.

Downstream geometric theories may attach their own interpretations to this common root. For
example, `Divisors.Determinant` constructs Picard-group classes and fixed-rank locally free data,
while pullback and projection-formula APIs can use the underlying line-bundle structure directly.
-/

open CategoryTheory Limits

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
