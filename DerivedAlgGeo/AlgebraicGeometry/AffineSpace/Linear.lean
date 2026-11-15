/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# The solution scheme of a finite linear system

Let `S` be a scheme, `m` a finite type and `A : Matrix n m Γ(S, ⊤)`. The scheme
`AffineSpace.linearKernel A` represents, on schemes over `S`, the functor sending `X` to the
vectors `v : m → Γ(X, ⊤)` with `∑ j, A i j * v j = 0` for every `i`, where the entries of `A` are
pulled back along `X ↘ S`. It is the pullback of the linear map `𝔸(m; S) ⟶ 𝔸(n; S)` given by `A`
along the zero section of `𝔸(n; S)`, so it is a closed subscheme of `𝔸(m; S)`. Its structure
morphism to `S` is affine, and it is locally of finite presentation when `n` is finite as well.

This is the last step of the proofs of Stacks 0DLC and 08JX. There the functor in question has been
identified with `V ↦ Ker(Hom(𝒪_V^{m}, 𝒪_V) → Hom(𝒪_V^{n}, 𝒪_V))` for a map `𝒪^{n} → 𝒪^{m}`, and
the last paragraph of the proof of 0DLC writes it as the fibre product of `𝔸(m; S) → 𝔸(n; S)`
with the zero section. No cohomology or sheaf of modules is involved.

## Main definitions

* `AffineSpace.linearMap A : 𝔸(m; S) ⟶ 𝔸(n; S)`, whose `i`-th coordinate is
  `∑ j, A i j * coord S j`.
* `AffineSpace.zeroSection n S : S ⟶ 𝔸(n; S)`.
* `AffineSpace.linearKernel A`: the pullback of `linearMap A` along `zeroSection n S`, over `S`,
  with the inclusion `linearKernel.ι A : linearKernel A ⟶ 𝔸(m; S)` (the first projection) and the
  universal solution `linearKernel.coord A`.
* `AffineSpace.linearKernel.homOverEquiv`: `S`-morphisms `X ⟶ linearKernel A` are the solutions
  of `A · v = 0` in `Γ(X, ⊤)`.
* `AffineSpace.linearKernel.pullbackIso`: `linearKernel` commutes with base change of `S`.

## Main results

* `IsClosedImmersion (linearKernel.ι A)`: the solution scheme is a closed subscheme of
  `𝔸(m; S)`.
* `IsAffineHom (linearKernel A ↘ S)`.
* `LocallyOfFinitePresentation (linearKernel A ↘ S)` for finite `n`.

## Implementation notes

The zero section is a closed immersion because it is a section of the separated morphism
`𝔸(n; S) ↘ S`. Mathlib's closed-immersion instance for equalizers needs an absolutely separated
target, and `S` is arbitrary here. The zero section is locally of finite presentation by
`LocallyOfFinitePresentation.of_comp`, since it is a section of the finitely presented
`𝔸(n; S) ↘ S`. Both properties pass to the base change `linearKernel.ι A` and then to its composite
with `𝔸(m; S) ↘ S`, so no affine-local presentation of `linearKernel A` is computed.

`linearKernel.ι A` is `pullback.fst (linearMap A) (zeroSection n S)` by definition, and the
structure morphism `linearKernel A ↘ S` is `pullback.snd`. Mathlib's base-change instance already
makes that `pullback.fst` a closed immersion. The coordinates `linearKernel.coord A` are the
universal solution, and morphisms into `linearKernel A` are compared through them
(`linearKernel.hom_ext`).

## The module form

Let `S = Spec R` and let `Q` be a finitely presented `R`-module with presentation
`Rⁿ → Rᵐ → Q → 0` given by `P : Matrix m n R`, whose columns are the relations. An `R`-linear map
`Q → M` is a vector `v : m → M` with `∑ j, P j i • v j = 0` for every `i`. Taking `A` to be the
transpose of `P`, `linearKernel.homOverEquiv` therefore identifies `S`-morphisms
`X ⟶ linearKernel A` with `Hom_R(Q, Γ(X, ⊤))`. That identification is not stated here.

## Finiteness

`Fintype m` is needed to form the sums. Finiteness is also load-bearing for finite presentation.
Rows with finite support make sense for infinite `m`, but for `S = Spec k`, `m = ℕ` and `A = 0`
the solution scheme would be `𝔸(ℕ; k)`, which is not locally of finite type over `k`. For `n`,
take `S = Spec k[y₀, y₁, …]`, `m` a point and `A i = yᵢ` with `n = ℕ`: the solution scheme is
`Spec (k[y₀, y₁, …][x] ⧸ (yᵢ x)ᵢ)`, whose ideal is not finitely generated. Everything except
finite presentation holds for arbitrary `n`.

## References

* [Stacks, Lemma 99.16.1 (Tag 0DLC)](https://stacks.math.columbia.edu/tag/0DLC), the last
  paragraph of the proof.
* [Stacks, Lemma 99.3.8 (Tag 08JX)](https://stacks.math.columbia.edu/tag/08JX).
* [Stacks, Lemma 29.22.11 (Tag 02FV)](https://stacks.math.columbia.edu/tag/02FV).

## Tags

affine space, linear system, zero section, functor of points, finite presentation
-/

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.AffineSpace

variable {S : Scheme.{u}} {m n : Type u}

section zeroSection

/-- The zero section of `𝔸(n; S) ⟶ S`: every coordinate vanishes. -/
def zeroSection (n : Type u) (S : Scheme.{u}) : S ⟶ 𝔸(n; S) :=
  homOfVector (𝟙 S) 0

@[reassoc, simp]
lemma zeroSection_over : zeroSection n S ≫ 𝔸(n; S) ↘ S = 𝟙 S :=
  homOfVector_over _ _

@[simp]
lemma zeroSection_appTop_coord (i : n) : (zeroSection n S).appTop (coord S i) = 0 :=
  homOfVector_appTop_coord _ _ _

@[reassoc]
lemma comp_zeroSection {X : Scheme.{u}} (f : X ⟶ S) : f ≫ zeroSection n S = homOfVector f 0 := by
  rw [zeroSection, comp_homOfVector, Category.comp_id]
  congr 1
  ext i
  simp

/-- The zero section is a closed immersion: it is a section of the separated `𝔸(n; S) ↘ S`. -/
instance : IsClosedImmersion (zeroSection n S) :=
  have : IsClosedImmersion (zeroSection n S ≫ 𝔸(n; S) ↘ S) := by
    rw [zeroSection_over]
    infer_instance
  .of_comp _ (𝔸(n; S) ↘ S)

instance [Finite n] : LocallyOfFinitePresentation (zeroSection n S) :=
  have : LocallyOfFinitePresentation (zeroSection n S ≫ 𝔸(n; S) ↘ S) := by
    rw [zeroSection_over]
    infer_instance
  .of_comp _ (𝔸(n; S) ↘ S)

end zeroSection

section linearMap

variable [Fintype m] (A : Matrix n m Γ(S, ⊤))

/-- The `S`-morphism `𝔸(m; S) ⟶ 𝔸(n; S)` given by the matrix `A`: its `i`-th coordinate is
`∑ j, A i j * coord S j`. -/
def linearMap : 𝔸(m; S) ⟶ 𝔸(n; S) :=
  homOfVector (𝔸(m; S) ↘ S) fun i ↦ ∑ j, (𝔸(m; S) ↘ S).appTop (A i j) * coord S j

@[reassoc]
lemma linearMap_over : linearMap A ≫ 𝔸(n; S) ↘ S = 𝔸(m; S) ↘ S :=
  homOfVector_over _ _

@[simp]
lemma linearMap_appTop_coord (i : n) :
    (linearMap A).appTop (coord S i) = ∑ j, (𝔸(m; S) ↘ S).appTop (A i j) * coord S j :=
  homOfVector_appTop_coord _ _ _

instance : (linearMap A).IsOver S :=
  ⟨linearMap_over A⟩

@[reassoc]
lemma homOfVector_linearMap {X : Scheme.{u}} (f : X ⟶ S) (v : m → Γ(X, ⊤)) :
    homOfVector f v ≫ linearMap A = homOfVector f fun i ↦ ∑ j, f.appTop (A i j) * v j := by
  ext1
  · simp
  · simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, linearMap_appTop_coord,
      homOfVector_appTop_coord, map_sum, map_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, homOfVector_over]

end linearMap

variable [Fintype m] (A : Matrix n m Γ(S, ⊤))

/-- The scheme of solutions of the linear system `A · v = 0`: the pullback of `linearMap A`
along the zero section. -/
def linearKernel : Scheme.{u} :=
  pullback (linearMap A) (zeroSection n S)

namespace linearKernel

instance canonicallyOver : (linearKernel A).CanonicallyOver S where
  hom := pullback.snd (linearMap A) (zeroSection n S)

/-- The inclusion of the solution scheme into `𝔸(m; S)`: the first projection of the
pullback. -/
def ι : linearKernel A ⟶ 𝔸(m; S) :=
  pullback.fst (linearMap A) (zeroSection n S)

lemma ι_eq_fst : ι A = pullback.fst (linearMap A) (zeroSection n S) := rfl

lemma over_eq_snd : linearKernel A ↘ S = pullback.snd (linearMap A) (zeroSection n S) := rfl

@[reassoc]
lemma condition : ι A ≫ linearMap A = linearKernel A ↘ S ≫ zeroSection n S :=
  pullback.condition

@[reassoc, simp]
lemma ι_over : ι A ≫ 𝔸(m; S) ↘ S = linearKernel A ↘ S := by
  rw [← linearMap_over A, condition_assoc, zeroSection_over, Category.comp_id]

/-- The solution scheme is a closed subscheme of `𝔸(m; S)`. The same instance on
`pullback.fst (linearMap A) (zeroSection n S)` is Mathlib's base change of the closed immersion
`zeroSection n S`. -/
instance : IsClosedImmersion (ι A) :=
  inferInstanceAs (IsClosedImmersion (pullback.fst _ _))

instance : IsAffineHom (linearKernel A ↘ S) := by
  rw [← ι_over]
  infer_instance

/-- The solution scheme is locally of finite presentation over `S`. Finiteness of `m` (from
`Fintype m`) and of `n` is load-bearing; see the module docstring. -/
instance [Finite n] : LocallyOfFinitePresentation (linearKernel A ↘ S) := by
  have : LocallyOfFinitePresentation (ι A) :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.fst _ _))
  rw [← ι_over]
  infer_instance

/-- The universal solution: the `j`-th coordinate of `𝔸(m; S)` restricted to the solution
scheme. -/
def coord (j : m) : Γ(linearKernel A, ⊤) :=
  (ι A).appTop (AffineSpace.coord S j)

@[simp]
lemma ι_appTop_coord (j : m) : (ι A).appTop (AffineSpace.coord S j) = coord A j := rfl

lemma ι_appTop_over (a : Γ(S, ⊤)) :
    (ι A).appTop ((𝔸(m; S) ↘ S).appTop a) = (linearKernel A ↘ S).appTop a := by
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using
    congrArg (fun φ ↦ φ.appTop a) (ι_over A)

/-- The universal solution solves the system. -/
lemma sum_mul_coord (i : n) : ∑ j, (linearKernel A ↘ S).appTop (A i j) * coord A j = 0 := by
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, linearMap_appTop_coord,
    zeroSection_appTop_coord, map_sum, map_mul, map_zero, ι_appTop_over, ι_appTop_coord] using
    congrArg (fun φ ↦ φ.appTop (AffineSpace.coord S i)) (condition A)

variable {A}

/-- The morphism into the solution scheme given by `f : X ⟶ S` and a solution `v` of the system
pulled back along `f`. -/
def lift {X : Scheme.{u}} (f : X ⟶ S) (v : m → Γ(X, ⊤))
    (hv : ∀ i, ∑ j, f.appTop (A i j) * v j = 0) : X ⟶ linearKernel A :=
  pullback.lift (homOfVector f v) f <| by
    rw [homOfVector_linearMap, comp_zeroSection]
    congr 1
    exact funext hv

section lift

variable {X : Scheme.{u}} (f : X ⟶ S) (v : m → Γ(X, ⊤))
  (hv : ∀ i, ∑ j, f.appTop (A i j) * v j = 0)

@[reassoc (attr := simp)]
lemma lift_ι : lift f v hv ≫ ι A = homOfVector f v :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma lift_over : lift f v hv ≫ linearKernel A ↘ S = f :=
  pullback.lift_snd _ _ _

@[simp]
lemma lift_appTop_coord (j : m) : (lift f v hv).appTop (coord A j) = v j := by
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ι_appTop_coord,
    homOfVector_appTop_coord] using
    congrArg (fun φ ↦ φ.appTop (AffineSpace.coord S j)) (lift_ι f v hv)

end lift

@[ext 1100]
lemma hom_ext {X : Scheme.{u}} {f g : X ⟶ linearKernel A}
    (h₁ : f ≫ linearKernel A ↘ S = g ≫ linearKernel A ↘ S)
    (h₂ : ∀ j, f.appTop (coord A j) = g.appTop (coord A j)) : f = g := by
  refine pullback.hom_ext ?_ h₁
  change f ≫ ι A = g ≫ ι A
  refine AffineSpace.hom_ext (by simpa using h₁) fun j ↦ ?_
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ι_appTop_coord] using h₂ j

/-- The coordinates of any morphism into the solution scheme solve the system pulled back along
its composite to `S`. -/
lemma appTop_sum_mul_coord {X : Scheme.{u}} (f : X ⟶ linearKernel A) (i : n) :
    ∑ j, (f ≫ linearKernel A ↘ S).appTop (A i j) * f.appTop (coord A j) = 0 := by
  simpa only [map_sum, map_mul, map_zero, Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using
    congrArg f.appTop (sum_mul_coord A i)

variable (A) in
/-- The functor of points of the solution scheme: `S`-morphisms `X ⟶ linearKernel A` are the
solutions in `Γ(X, ⊤)` of `A · v = 0`, with `A` pulled back along `X ↘ S`. -/
@[simps]
def homOverEquiv {X : Scheme.{u}} [X.Over S] :
    { f : X ⟶ linearKernel A // f.IsOver S } ≃
      { v : m → Γ(X, ⊤) // ∀ i, ∑ j, (X ↘ S).appTop (A i j) * v j = 0 } where
  toFun f := ⟨fun j ↦ f.1.appTop (coord A j),
    fun i ↦ by simpa only [f.2.1] using appTop_sum_mul_coord f.1 i⟩
  invFun v := ⟨lift (X ↘ S) v.1 v.2, ⟨lift_over _ _ _⟩⟩
  left_inv f := by
    have := f.2
    ext1
    apply hom_ext <;> simp
  right_inv v := by
    ext j
    simp

variable (A) in
/-- Formation of the solution scheme commutes with base change along `g : S' ⟶ S`. -/
def pullbackIso {S' : Scheme.{u}} (g : S' ⟶ S) :
    linearKernel (A.map g.appTop) ≅ pullback (linearKernel A ↘ S) g where
  hom := pullback.lift
    (lift (linearKernel (A.map g.appTop) ↘ S' ≫ g) (coord (A.map g.appTop)) fun i ↦ by
      simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Matrix.map_apply] using
        sum_mul_coord (A.map g.appTop) i)
    (linearKernel (A.map g.appTop) ↘ S') (lift_over _ _ _)
  inv := lift (pullback.snd _ _) (fun j ↦ (pullback.fst (linearKernel A ↘ S) g).appTop (coord A j))
    fun i ↦ by
      simpa only [pullback.condition, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        Matrix.map_apply] using appTop_sum_mul_coord (pullback.fst (linearKernel A ↘ S) g) i
  hom_inv_id := by
    have key {T : Scheme.{u}} (a : T ⟶ linearKernel A) (b : T ⟶ S') (h) (x) :
        (pullback.lift a b h).appTop ((pullback.fst (linearKernel A ↘ S) g).appTop x) =
          a.appTop x := by
      simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using
        congrArg (fun φ ↦ φ.appTop x) (pullback.lift_fst a b h)
    ext1
    · simp
    · simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, lift_appTop_coord, key,
        Scheme.Hom.id_appTop, CommRingCat.id_apply]
  inv_hom_id := by
    ext1
    · ext1
      · simp [pullback.condition (f := linearKernel A ↘ S) (g := g)]
      · simp only [Category.assoc, pullback.lift_fst, Category.id_comp, Scheme.Hom.comp_appTop,
          CommRingCat.comp_apply, lift_appTop_coord]
    · simp

@[reassoc (attr := simp)]
lemma pullbackIso_hom_snd {S' : Scheme.{u}} (g : S' ⟶ S) :
    (pullbackIso A g).hom ≫ pullback.snd (linearKernel A ↘ S) g =
      linearKernel (A.map g.appTop) ↘ S' :=
  pullback.lift_snd _ _ _

@[simp]
lemma pullbackIso_inv_appTop_coord {S' : Scheme.{u}} (g : S' ⟶ S) (j : m) :
    (pullbackIso A g).inv.appTop (coord (A.map g.appTop) j) =
      (pullback.fst (linearKernel A ↘ S) g).appTop (coord A j) := by
  simp [pullbackIso]

end linearKernel

end AlgebraicGeometry.AffineSpace
