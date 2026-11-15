/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.KInjective.AcyclicSubcomplex
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.KInjective.Criterion
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.KInjective.Factorization

/-!
# K-injective resolutions in Grothendieck abelian categories

Let `C` be a Grothendieck abelian category. Every cochain complex `M` over `C` has a
quasi-isomorphism `M ⟶ I`, a monomorphism in each degree, into a K-injective complex `I`
with injective terms, functorially in `M`. This is Stacks, Theorem 19.12.6 (Tag 079P),
due to Spaltenstein in this generality.

## Main definitions

* `CochainComplex.kInjectiveResolution`: the functor `M ↦ I`.
* `CochainComplex.kInjectiveResolutionι`: the natural comparison `M ⟶ I`.

## Main results

* `CochainComplex.isKInjective_of_rightOrthogonal_smallAcyclic`: Stacks, Lemma 19.12.3
  (Tag 079L) for the family of bounded-above acyclic complexes of bounded size.
* `CochainComplex.exists_isKInjective_quasiIso`: Tag 079P.
* Instances: `kInjectiveResolutionι` is a monomorphism and a quasi-isomorphism, and its
  target is K-injective with injective terms.

## Implementation notes

The resolution is `CochainComplex.injectiveReplacement` for the `w`-small family
`CochainComplex.smallAcyclic C` of Stacks, Lemma 19.12.2 (Tag 079K). Its members are
acyclic, so the comparison is a monomorphic quasi-isomorphism into a complex with
injective terms (Tags 079M and 079N), and every morphism from a member to the target is
null-homotopic. The family detects acyclic complexes, so the criterion of Tag 079L makes
the target K-injective.

## References

* [The Stacks project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988)
* M. Serpé, *Resolution of unbounded complexes in Grothendieck categories*,
  J. Pure Appl. Algebra 177 (2003)

## Tags

K-injective resolution, K-injective complex, Grothendieck abelian category
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe w v u

open CategoryTheory Limits

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- **Stacks, Lemma 19.12.3 (Tag 079L)** for the family `smallAcyclic C` of Tag 079K: a
complex of injective objects that is right orthogonal in the homotopy category to every
bounded-above acyclic complex of bounded size is K-injective. -/
theorem isKInjective_of_rightOrthogonal_smallAcyclic (I : CochainComplex C ℤ)
    [∀ n, Injective (I.X n)]
    (hI : ∀ (i : SmallAcyclicIndex C)
      (f : (HomotopyCategory.quotient C (.up ℤ)).obj (smallAcyclic C i) ⟶
        (HomotopyCategory.quotient C (.up ℤ)).obj I), f = 0) :
    I.IsKInjective :=
  isKInjective_of_injective_of_rightOrthogonal (acyclic_smallAcyclic C)
    (fun _ hM hM0 => exists_mono_smallAcyclic hM hM0) hI

variable (C) in
/-- **Stacks, Theorem 19.12.6 (Tag 079P)**, functorially: a K-injective resolution
`M ⟶ kInjectiveResolution C M` of every cochain complex `M`, through the natural
transformation `kInjectiveResolutionι C`. -/
noncomputable def kInjectiveResolution : CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
  injectiveReplacement (smallAcyclic C)

variable (C) in
/-- The comparison `M ⟶ kInjectiveResolution C M`: a degreewise monomorphism and a
quasi-isomorphism. -/
noncomputable def kInjectiveResolutionι : 𝟭 (CochainComplex C ℤ) ⟶ kInjectiveResolution C :=
  injectiveReplacementι (smallAcyclic C)

instance mono_kInjectiveResolutionι_app (M : CochainComplex C ℤ) :
    Mono ((kInjectiveResolutionι C).app M) :=
  mono_injectiveReplacementι_app _ M

instance quasiIso_kInjectiveResolutionι_app (M : CochainComplex C ℤ) :
    QuasiIso ((kInjectiveResolutionι C).app M) :=
  quasiIso_injectiveReplacementι_app _ (acyclic_smallAcyclic C) M

instance injective_kInjectiveResolution_X (M : CochainComplex C ℤ) (n : ℤ) :
    Injective (((kInjectiveResolution C).obj M).X n) :=
  injective_injectiveReplacement_X _ M n

instance isKInjective_kInjectiveResolution (M : CochainComplex C ℤ) :
    ((kInjectiveResolution C).obj M).IsKInjective :=
  isKInjective_of_injective_of_homotopy_zero (acyclic_smallAcyclic C)
    (fun _ hM hM0 => exists_mono_smallAcyclic hM hM0)
    (nonempty_homotopy_zero_injectiveReplacement _ M)

/-- **Stacks, Theorem 19.12.6 (Tag 079P).** In a Grothendieck abelian category, every
cochain complex has a quasi-isomorphism, a monomorphism in each degree, into a
K-injective complex with injective terms. -/
@[stacks 079P]
theorem exists_isKInjective_quasiIso (M : CochainComplex C ℤ) :
    ∃ (I : CochainComplex C ℤ) (i : M ⟶ I),
      I.IsKInjective ∧ (∀ n, Injective (I.X n)) ∧ (∀ n, Mono (i.f n)) ∧ QuasiIso i :=
  ⟨_, (kInjectiveResolutionι C).app M, inferInstance, inferInstance, fun _ => inferInstance,
    inferInstance⟩

end CochainComplex
