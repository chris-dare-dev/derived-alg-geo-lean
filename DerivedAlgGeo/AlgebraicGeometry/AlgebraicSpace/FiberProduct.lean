/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.AlgebraicSpace.Basic

/-!
# Fibre products of algebraic spaces

The fibre product `F ×_H G` of presheaves on `Over S` is an algebraic space when `F` and `G` are
algebraic spaces and `H` is an fppf sheaf with diagonal representable by schemes (Stacks 04T9).
In particular algebraic spaces over `S` have fibre products, computed in presheaves (Stacks
02X2), and a terminal object, the scheme `S` itself; together these give products (Stacks 02X0).

## Main definitions

None: this file proves closure properties of `AlgebraicGeometry.isAlgebraicSpace`.

## Main results

* `AlgebraicGeometry.isAlgebraicSpace_pullback`: Stacks 04T9.
* `AlgebraicGeometry.isAlgebraicSpace` is closed under limits of cospans and of the empty diagram,
  so `AlgebraicGeometry.AlgebraicSpace S` has pullbacks and a terminal object, both created by the
  inclusion into presheaves.

## Implementation notes

The diagonal condition is handled through Mathlib's relative diagonal
`MorphismProperty.diagonal` of `Functor.relativelyRepresentable yoneda`: a presheaf has
representable diagonal exactly when its map to the terminal presheaf has representable relative
diagonal, and relative diagonals are stable under base change and composition. Only the fibre
product's atlas uses the hypothesis on the diagonal of `H`; its sheaf condition uses that `H` is a
sheaf.

## References

* [Stacks, Section 65.7 (Tag 04T8)](https://stacks.math.columbia.edu/tag/04T8)

## Tags

algebraic space, fibre product
-/

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/-- The diagonal of a presheaf is representable exactly when the relative diagonal of its map to
the terminal presheaf is. -/
private lemma relativelyRepresentable_diag_iff_diagonal (X : (Over S)ᵒᵖ ⥤ Type u) :
    yoneda.relativelyRepresentable (diag X) ↔
      yoneda.relativelyRepresentable.diagonal (terminal.from X) := by
  rw [diagonal_iff, show diag X = pullback.diagonal (terminal.from X) ≫ (prodIsoPullback X X).inv
    by cat_disch]
  exact cancel_right_of_respectsIso _ _ _

/-- The fibre product of two algebraic spaces over an fppf sheaf with representable diagonal is an
algebraic space (Stacks 04T9). -/
theorem isAlgebraicSpace_pullback {F G H : (Over S)ᵒᵖ ⥤ Type u}
    (hF : isAlgebraicSpace S F) (hG : isAlgebraicSpace S G)
    (hH : Presieve.IsSheaf (Scheme.fppfTopology.over S) H)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag H)) (f : F ⟶ H) (g : G ⟶ H) :
    isAlgebraicSpace S (Limits.pullback f g) := by
  refine ⟨?_, ?_, ?_⟩
  · have hsheaf : ∀ j, Presheaf.IsSheaf (Scheme.fppfTopology.over S) ((cospan f g).obj j) := by
      rintro (_ | _ | _) <;> rw [isSheaf_iff_isSheaf_of_type]
      exacts [hH, hF.1, hG.1]
    rw [← isSheaf_iff_isSheaf_of_type]
    exact ObjectProperty.prop_limit (Presheaf.IsSheaf (Scheme.fppfTopology.over S)) _ hsheaf
  · rw [relativelyRepresentable_diag_iff_diagonal, ← terminal.comp_from (pullback.fst f g)]
    refine comp_mem _ _ _ (pullback_fst f g ?_)
      ((relativelyRepresentable_diag_iff_diagonal F).1 hF.2.1)
    have h := (relativelyRepresentable_diag_iff_diagonal G).1 hG.2.1
    rw [← terminal.comp_from g, diagonal_iff, pullback.diagonal_comp] at h
    exact yoneda.relativelyRepresentable.of_postcomp (W' := monomorphisms _) _ _
      (monomorphisms.infer_property _) h
  · obtain ⟨V, p, hp⟩ := hF.2.2
    obtain ⟨W, q, hq⟩ := hG.2.2
    obtain ⟨b, snd, fst, sq⟩ := Functor.relativelyRepresentable.of_diag hΔ (p ≫ f) (q ≫ g)
    let P : MorphismProperty Scheme.{u} := @Etale ⊓ @Surjective
    have : P.IsMultiplicative := IsMultiplicative.inf (P := @Etale) (Q := @Surjective)
    have : (P.over (X := S)).IsStableUnderComposition :=
      inferInstanceAs (P.inverseImage (Over.forget S)).IsStableUnderComposition
    have := relative_isStableUnderBaseChange (F := yoneda) (P.over (X := S))
    refine ⟨b, sq.isoPullback.hom ≫
      pullback.map (p ≫ f) (q ≫ g) f g p q (𝟙 H) (by simp) (by simp), ?_⟩
    exact RespectsIso.precomp _ _ _ (pullbackMap hp hq rfl rfl)

variable (S)

instance : (isAlgebraicSpace S).IsClosedUnderLimitsOfShape WalkingCospan :=
  .mk' <| by
    rintro _ ⟨F, hF⟩
    exact (isAlgebraicSpace S).prop_of_iso (HasLimit.isoOfNatIso (diagramIsoCospan F)).symm
      (isAlgebraicSpace_pullback (hF _) (hF _) (hF .one).1 (hF .one).2.1 _ _)

instance : (isAlgebraicSpace S).IsClosedUnderLimitsOfShape (Discrete PEmpty) :=
  .mk' <| by
    rintro _ ⟨F, hF⟩
    have hX : IsTerminal (limit F) :=
      isLimitEmptyConeEquiv _ (limit.cone F) (asEmptyCone (limit F)) (Iso.refl _) (limit.isLimit F)
    exact (isAlgebraicSpace S).prop_of_iso
      ((Over.mkIdTerminal.isTerminalObj yoneda).uniqueUpToIso hX) (isAlgebraicSpace_yoneda S _)

/-- Algebraic spaces over `S` have fibre products, computed in presheaves (Stacks 02X2). -/
instance : HasPullbacks (AlgebraicSpace S) := inferInstance

/-- The scheme `S` is a terminal algebraic space over `S`; with fibre products this gives
products of algebraic spaces (Stacks 02X0). -/
instance : HasTerminal (AlgebraicSpace S) := inferInstance

end AlgebraicGeometry
