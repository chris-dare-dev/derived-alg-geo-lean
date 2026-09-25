import DerivedAlgGeo.CategoryTheory.Subobject.JointReflection

/-! Axiom audit and direct-import client for joint reflection of subobject order. -/

#print axioms CategoryTheory.Subobject.le_iff_mapFunctor_le_of_jointlyReflectsIsomorphisms
#print axioms CategoryTheory.Subobject.eq_iff_mapFunctor_eq_of_jointlyReflectsIsomorphisms

open CategoryTheory CategoryTheory.Limits

universe w v u v' u'

variable {I : Type w} {C : Type u} [Category.{v} C] [HasPullbacks C]
  {D : I → Type u'} [∀ i, Category.{v'} (D i)]
  (F : ∀ i, C ⥤ D i)
  [∀ i, PreservesLimitsOfShape WalkingCospan (F i)]
  [∀ i, (F i).PreservesMonomorphisms]
  (hF : JointlyReflectIsomorphisms F) {X : C} (P Q : Subobject X)

example : P ≤ Q ↔ ∀ i, Subobject.mapFunctor (F i) P ≤
    Subobject.mapFunctor (F i) Q :=
  Subobject.le_iff_mapFunctor_le_of_jointlyReflectsIsomorphisms F hF P Q

example : P = Q ↔ ∀ i, Subobject.mapFunctor (F i) P =
    Subobject.mapFunctor (F i) Q :=
  Subobject.eq_iff_mapFunctor_eq_of_jointlyReflectsIsomorphisms F hF P Q
