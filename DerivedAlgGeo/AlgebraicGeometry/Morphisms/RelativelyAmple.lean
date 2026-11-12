/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Ample

/-!
# Relatively ample invertible sheaves

An invertible sheaf `L` on `X` is relatively ample for `f : X ⟶ S` (Stacks 01VH) when `f` is
quasi-compact and the restriction of `L` to `f⁻¹ V` is ample for every affine open `V ⊆ S`.

## Main definitions

* `AlgebraicGeometry.IsRelativelyAmple f L`: `L` is `f`-ample.

## Main results

* `AlgebraicGeometry.isRelativelyAmple_tensorPow_iff`: `L` is `f`-ample if and only if a positive
  tensor power of it is (Stacks 02NN).
* `AlgebraicGeometry.isRelativelyAmple_iff_isAmple`: over an affine base, relative ampleness is
  ampleness (Stacks 01VK).
* `AlgebraicGeometry.IsRelativelyAmple.isSeparated`: a morphism with a relatively ample sheaf is
  separated (Stacks 01VI).
* `AlgebraicGeometry.IsRelativelyAmple.comp_of_isAffineHom`,
  `AlgebraicGeometry.IsRelativelyAmple.of_isClosedImmersion`: relative ampleness pulls back along
  affine morphisms, in particular to closed subschemes (the relative form of Stacks 01PU).
* `AlgebraicGeometry.IsRelativelyAmple.pullback`, `IsRelativelyAmple.of_isPullback`: relative
  ampleness is stable under base change (Stacks 0893).

## Implementation notes

The definition restricts `L` to the open subscheme `f⁻¹ V`, as Stacks does. Every proof works with
`Scheme.Modules.IsAmpleOn L (f⁻¹ V)` instead, ampleness on an open of `X` itself, through
`Scheme.Modules.isAmple_restrict_iff`.

Base change goes through locality on the base: over an affine `V' ⊆ S'`, the preimage of `V'` is
quasi-compact and quasi-separated (the morphism is separated), and it is covered by preimages of
basic opens of `V'` mapping into affine opens of `S`, on which ampleness pulls back along an affine
morphism. Sections over those basic opens extend after multiplying by a power of the function
(`Scheme.Modules.exists_pow_smul_eq_res`).

## References

* [Stacks, Section 29.38 (Tag 01VG)](https://stacks.math.columbia.edu/tag/01VG).

## Tags

relatively ample, invertible sheaf, separated morphism
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

open Scheme.Modules

variable {X S : Scheme.{u}}

/-- **Relatively ample invertible sheaf** (Stacks 01VH): `f` is quasi-compact and for every affine
open `V ⊆ S` the restriction of `L` to `f⁻¹ V` is ample. -/
def IsRelativelyAmple (f : X ⟶ S) (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} (show SheafOfModules X.ringCatSheaf from L)] : Prop :=
  QuasiCompact f ∧ ∀ V ∈ S.affineOpens, Scheme.Modules.IsAmple (L.restrict (f ⁻¹ᵁ V).ι)

section

variable {f : X ⟶ S} {L : X.Modules}
  [SheafOfModules.IsInvertible.{u, u, u} (show SheafOfModules X.ringCatSheaf from L)]

/-- Relative ampleness is ampleness on the preimage of every affine open. -/
theorem isRelativelyAmple_iff_isAmpleOn :
    IsRelativelyAmple f L ↔ QuasiCompact f ∧ ∀ V ∈ S.affineOpens, IsAmpleOn L (f ⁻¹ᵁ V) := by
  simp only [IsRelativelyAmple, isAmple_restrict_iff]

/-- A morphism with a relatively ample sheaf is quasi-compact. -/
theorem IsRelativelyAmple.quasiCompact (h : IsRelativelyAmple f L) : QuasiCompact f :=
  h.1

/-- A relatively ample sheaf is ample on the preimage of every affine open. -/
theorem IsRelativelyAmple.isAmpleOn (h : IsRelativelyAmple f L) {V : S.Opens}
    (hV : IsAffineOpen V) : IsAmpleOn L (f ⁻¹ᵁ V) :=
  (isRelativelyAmple_iff_isAmpleOn.1 h).2 V hV

/-- Relative ampleness is invariant under isomorphism. -/
theorem IsRelativelyAmple.of_iso {M : X.Modules}
    [SheafOfModules.IsInvertible.{u, u, u} (show SheafOfModules X.ringCatSheaf from M)]
    (φ : L ≅ M) (h : IsRelativelyAmple f L) : IsRelativelyAmple f M :=
  isRelativelyAmple_iff_isAmpleOn.2 ⟨h.1, fun _ hV ↦ (h.isAmpleOn hV).of_iso φ⟩

/-- **Relative ampleness of a power** (Stacks 02NN): for `n ≥ 1`, `L^{⊗ n}` is `f`-ample if and
only if `L` is. -/
theorem isRelativelyAmple_tensorPow_iff {n : ℕ} (hn : 1 ≤ n) :
    IsRelativelyAmple f (tensorPow L n) ↔ IsRelativelyAmple f L := by
  simp only [isRelativelyAmple_iff_isAmpleOn, isAmpleOn_tensorPow_iff hn]

/-- **Over an affine base, relative ampleness is ampleness** (Stacks 01VK). Over an affine
`V ⊆ S`, a point of `X_s ∩ f⁻¹ V` lies in some `f⁻¹ D(g) ⊆ f⁻¹ V`, and `g • s` cuts `X_s` down to
the basic open `X_s ∩ f⁻¹ D(g)` of the affine `X_s`. -/
theorem isRelativelyAmple_iff_isAmple [IsAffine S] : IsRelativelyAmple f L ↔ IsAmple L := by
  refine ⟨fun h ↦ isAmple_iff_isAmpleOn_top.2 (h.isAmpleOn (isAffineOpen_top S)), fun h ↦ ?_⟩
  have := h.1
  have hf : QuasiCompact f := inferInstance
  refine isRelativelyAmple_iff_isAmpleOn.2 ⟨hf, fun V hV ↦ ⟨f.isCompact_preimage hV.isCompact,
    fun x hx ↦ ?_⟩⟩
  obtain ⟨n, hn, s, hxs, hs⟩ := h.2 x
  obtain ⟨g, hgV, hxg⟩ := (isAffineOpen_top S).exists_basicOpen_le (V := V) ⟨f x, hx⟩
    (Opens.mem_top _)
  let a := f.appTop g
  have ha : X.basicOpen a ≤ f ⁻¹ᵁ V := by
    rw [← Scheme.preimage_basicOpen_top]
    exact f.preimage_mono hgV
  let σ := X.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ V ≤ ⊤)).op a •
    (tensorPow L n).presheaf.map (homOfLE (le_top : f ⁻¹ᵁ V ≤ ⊤)).op s
  have hσ : nonvanishingLocus (tensorPow L n) σ = X.basicOpen a ⊓ nonvanishingLocus _ s := by
    rw [nonvanishingLocus_smul, nonvanishingLocus_res, Scheme.basicOpen_res]
    ext y
    simp only [Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe]
    exact ⟨fun ⟨⟨_, h1⟩, h2, _⟩ ↦ ⟨h1, h2⟩, fun ⟨h1, h2⟩ ↦ ⟨⟨ha h1, h1⟩, h2, ha h1⟩⟩
  refine ⟨n, hn, σ, ?_, ?_⟩
  · rw [hσ]
    refine ⟨?_, hxs⟩
    rw [← Scheme.preimage_basicOpen_top]
    exact hxg
  · rw [hσ, inf_comm, ← Scheme.basicOpen_res X a (homOfLE (le_top : nonvanishingLocus _ s ≤ ⊤)).op]
    exact hs.basicOpen _

/-- **Relative ampleness pulls back along affine morphisms**: if `L` is `f`-ample and `i` is
affine, then `i^* L` is `(i ≫ f)`-ample. -/
theorem IsRelativelyAmple.comp_of_isAffineHom {Y : Scheme.{u}} (i : Y ⟶ X) [IsAffineHom i]
    (h : IsRelativelyAmple f L) :
    IsRelativelyAmple (i ≫ f) ((Scheme.Modules.pullback i).obj L) := by
  have := h.1
  exact isRelativelyAmple_iff_isAmpleOn.2 ⟨inferInstance, fun V hV ↦ (h.isAmpleOn hV).pullback i⟩

/-- **Relative ampleness restricts to closed subschemes** (the relative form of Stacks 01PU). -/
theorem IsRelativelyAmple.of_isClosedImmersion {Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]
    (h : IsRelativelyAmple f L) : IsRelativelyAmple (i ≫ f) ((Scheme.Modules.pullback i).obj L) :=
  h.comp_of_isAffineHom i

/-- **A morphism with a relatively ample sheaf is separated** (Stacks 01VI): separatedness is local
on the base, and over an affine `V` the scheme `f⁻¹ V` carries an ample sheaf. -/
theorem IsRelativelyAmple.isSeparated (h : IsRelativelyAmple f L) : IsSeparated f := by
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsSeparated) _
    (iSup_affineOpens_eq_top S)).2 fun V ↦ ?_
  have := (h.2 V V.2).isSeparated
  infer_instance

end

section BaseChange

open Limits

variable {X S S' Y : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {p : Y ⟶ X} {f' : Y ⟶ S'}

/-- In a pullback square, ampleness of `L` on `f⁻¹ V` for an affine `V ⊆ S` gives ampleness of
the pullback of `L` on `f'⁻¹ V'` for every affine `V' ⊆ g⁻¹ V`: the restriction of `p` to
`f'⁻¹ V' ⟶ f⁻¹ V` is a base change of the affine morphism `V' ⟶ V`. -/
private lemma isAmpleOn_of_isPullback_of_le (H : IsPullback p f' f g) {L : X.Modules}
    [SheafOfModules.IsInvertible.{u, u, u} (show SheafOfModules X.ringCatSheaf from L)]
    {V : S.Opens} (hV : IsAffineOpen V) {V' : S'.Opens} (hV' : IsAffineOpen V')
    (hle : V' ≤ g ⁻¹ᵁ V) (h : IsAmple (L.restrict (f ⁻¹ᵁ V).ι)) :
    IsAmpleOn ((Scheme.Modules.pullback p).obj L) (f' ⁻¹ᵁ V') := by
  have hle' : f' ⁻¹ᵁ V' ≤ p ⁻¹ᵁ (f ⁻¹ᵁ V) := by
    intro y hy
    change f (p y) ∈ V
    rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply]
    exact hle hy
  obtain ⟨r, hr⟩ : ∃ r : V'.toScheme ⟶ V.toScheme, r ≫ V.ι = V'.ι ≫ g :=
    ⟨S'.homOfLE hle ≫ g ∣_ V, by simp [morphismRestrict_ι]⟩
  obtain ⟨q, hq⟩ : ∃ q : (f' ⁻¹ᵁ V').toScheme ⟶ (f ⁻¹ᵁ V).toScheme,
      q ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ V').ι ≫ p :=
    ⟨Y.homOfLE hle' ≫ p ∣_ (f ⁻¹ᵁ V), by simp [morphismRestrict_ι]⟩
  have hsq : IsPullback (f' ∣_ V') q r (f ∣_ V) := by
    refine IsPullback.of_bot ?_ ?_ (isPullback_morphismRestrict f V)
    · rw [hq, hr]
      exact (isPullback_morphismRestrict f' V').paste_vert H.flip
    · rw [← cancel_mono V.ι]
      simp only [Category.assoc, hr, morphismRestrict_ι_assoc, morphismRestrict_ι,
        reassoc_of% hq, H.w]
  have : IsAffine V'.toScheme := hV'
  have : IsAffine V.toScheme := hV
  have : IsAffineHom q := MorphismProperty.of_isPullback hsq (inferInstance : IsAffineHom r)
  refine (isAmple_restrict_iff _ _).1 ((h.pullback q).of_iso ?_)
  exact (Scheme.Modules.pullback q).mapIso
      ((restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app L) ≪≫
    (pullbackComp q (f ⁻¹ᵁ V).ι).app L ≪≫ (pullbackCongr hq).app L ≪≫
    ((pullbackComp (f' ⁻¹ᵁ V').ι p).app L).symm ≪≫
    ((restrictFunctorIsoPullback (f' ⁻¹ᵁ V').ι).app _).symm

/-- **Relative ampleness is stable under base change** (Stacks 0893), for an arbitrary pullback
square: if `L` is `f`-ample and `p, f'` exhibit `Y` as `X ×_S S'`, then `p^* L` is `f'`-ample. -/
theorem IsRelativelyAmple.of_isPullback (H : IsPullback p f' f g) {L : X.Modules}
    [SheafOfModules.IsInvertible.{u, u, u} (show SheafOfModules X.ringCatSheaf from L)]
    (h : IsRelativelyAmple f L) : IsRelativelyAmple f' ((Scheme.Modules.pullback p).obj L) := by
  have := h.quasiCompact
  have := h.isSeparated
  have : QuasiCompact f' := MorphismProperty.of_isPullback H (inferInstance : QuasiCompact f)
  have : QuasiSeparated f' := MorphismProperty.of_isPullback H (inferInstance : QuasiSeparated f)
  refine isRelativelyAmple_iff_isAmpleOn.2 ⟨inferInstance, fun V' hV' ↦ ?_⟩
  refine isAmpleOn_of_forall_isAmpleOn_basicOpen (f'.isCompact_preimage hV'.isCompact)
    (f'.isQuasiSeparated_preimage hV'.isQuasiSeparated) fun y hy ↦ ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hgy, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g (f' y))) isOpen_univ
  obtain ⟨b, hb, hyb⟩ := hV'.exists_basicOpen_le (V := g ⁻¹ᵁ V) ⟨f' y, hgy⟩ hy
  refine ⟨f'.app V' b, ?_, ?_⟩
  · rw [← Scheme.preimage_basicOpen]
    exact hyb
  · rw [← Scheme.preimage_basicOpen]
    exact isAmpleOn_of_isPullback_of_le H hV (hV'.basicOpen b) hb (h.2 V hV)

/-- **Relative ampleness is stable under base change** (Stacks 0893): if `L` is `f`-ample, then
its pullback to `X ×_S S'` is ample relative to the second projection. -/
theorem IsRelativelyAmple.pullback {X S S' : Scheme.{u}} {f : X ⟶ S} {L : X.Modules}
    [SheafOfModules.IsInvertible.{u, u, u} (show SheafOfModules X.ringCatSheaf from L)]
    (h : IsRelativelyAmple f L) (g : S' ⟶ S) :
    IsRelativelyAmple (Limits.pullback.snd f g)
      ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj L) :=
  h.of_isPullback (IsPullback.of_hasPullback f g)

end BaseChange

end AlgebraicGeometry
