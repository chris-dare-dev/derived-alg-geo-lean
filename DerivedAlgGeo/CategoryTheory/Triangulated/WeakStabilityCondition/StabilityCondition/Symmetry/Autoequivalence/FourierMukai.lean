/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.Adjunction
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.Witness
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.GrothendieckGroup
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry.Autoequivalence.Stability.ClassMap
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry.Autoequivalence.Stability.Composition
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry.Autoequivalence.Stability.Transport

/-!
# Kernel functors acting on stability conditions

`Symmetry/Autoequivalence/Stability/Transport` transports a stability condition
along an autoequivalence. `Triangulated.FourierMukai` builds kernel functors.
This file joins them: a kernel functor that happens to be an autoequivalence
acts on `StabilityCondition.WithClassMap`, and its action on classes is
computed by its kernel.

That second half is the point. `actStabAut` already takes any autoequivalence;
what a `KernelAutoequivalence` adds is that the induced map on `K₀` is
`transformK₀ K` — so the action on the central charge is determined by the
kernel rather than by the functor's construction.

## Direction of dependence

This file lives in the stability track and imports the generic
Fourier--Mukai modules, never the reverse. `actStabAut`, `Slicing` and
`WithClassMap` are all stability-track declarations, so a file under
`CategoryTheory/Triangulated/FourierMukai/` could not state any of this
without pointing a generic module at a specialized one — the layering that
issue #453 removed.

`K₀.map` used to be on that list too, under its stability-track twin
`K₀.mapF`; #487 retired the twin, so the class-map half of the argument now
rests on `actStabAut` alone. That is enough: the *transport* is what is
specialized here, not the Grothendieck-group functoriality.

## What this file does not assert

* **Nothing constructs a `KernelAutoequivalence`.** The equivalence and the
  isomorphism to a transform are both supplied. That a Fourier--Mukai transform
  with a suitable kernel *is* an equivalence is the classical theorem, and it
  needs the geometry the abstract `Correspondence` does not carry.
* **Nothing constructs a `DualKernel` from geometry.** That the quasi-inverse
  of a Fourier--Mukai equivalence is again one — with the derived-dual kernel
  `P^∨ ⊗ p^*ω[dim]` — is classical, and supplying it is geometry. What this
  file does is make the *consequences* of having one available: given a
  `DualKernel`, the class-lattice compatibility `actStab` needs is stated in
  terms of the dual kernel's own class map rather than the opaque
  `K₀.map Φ.inverse` (`actStabOfDual`), and the two kernels' class maps are
  proved mutually inverse (`transformK₀_dual_comp`).

  Since #559's adjunction stage there is one *abstract* constructor:
  `DualKernel.ofLeftAdjointKernel` builds a dual kernel from a
  `LeftAdjointKernelData`, by uniqueness of adjoints, and
  `ofRightAdjointKernel` does the same on the other side. That moves the
  supplied datum, it does not discharge it — `LeftAdjointKernelData` is itself
  supplied in `FourierMukai/Adjunction.lean`, and
  `DualKernel.toLeftAdjointKernelData` goes back, so for a kernel
  autoequivalence the two are interderivable and neither is weaker.
* **No group of kernel autoequivalences, and no monoid map into one.** The
  bundled group action on stability conditions exists elsewhere:
  `GroupAction.AutPairQuot v` in `Stability/ClassMap.lean` is a `Group` with a
  `MulAction` on `WithClassMap C v`, for autoequivalence–`lam` pairs with
  `lam` invertible. `toAutPair` sends a kernel autoequivalence equipped with a
  `DualKernel` and a compatible `lam : Λ ≃+ Λ` to one element of
  `GroupAction.AutPair v`, and `mk_toAutPair_smul` identifies that element's
  `AutPairQuot` action with `actStabOfDual`. That is a map on *elements* only.
  It is not a monoid homomorphism and is not claimed to be one: there is no
  multiplication on the source to preserve, because composing two kernel
  autoequivalences needs a `ConvolutionData` supplied per pair (`trans`), and
  no distinguished unit either, because `id` needs a supplied
  `UnitKernelData`. `trans`/`actStab_trans` give the associativity clause and
  `UnitKernelData`/`id`/`toDualKernel` give a unit *object*, but no identity
  **law** relating the two is proved here — that would need convolution data
  comparing a correspondence with itself, which nothing supplies.
* **Nothing constructs a `UnitKernelData`.** That `𝒪_Δ` presents the identity
  as a transform is the classical statement, and it needs the geometry the
  abstract `Correspondence` does not carry.
* **Nothing constructs a non-trivial `LeftAdjointKernelData` or
  `RightAdjointKernelData`.** `UnitKernelData.toLeftAdjointKernelData` produces
  one from a unit kernel, but it is the statement that `𝟭 C` is its own
  adjoint, transported across `unitIso`; it says nothing about `corr`. That a
  general `Φ_P` has kernel-presented adjoints is Grothendieck duality.
* Nothing about Bridgeland's `Stab(X)` as a manifold, and no continuity or
  local-homeomorphism claim for the induced map.
-/

universe w u u' x t x₁ x₂ x₃ t₁ t₂ t₃

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated CategoryTheory.Triangulated.FourierMukai
open CategoryTheory.Triangulated.StabilityCondition

noncomputable section

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
  {𝒲 : Type t} [Category.{x} 𝒲] [HasZeroObject 𝒲] [HasShift 𝒲 ℤ]
  [Preadditive 𝒲] [∀ n : ℤ, (shiftFunctor 𝒲 n).Additive] [Pretriangulated 𝒲]

/-- A **kernel autoequivalence**: an autoequivalence of `C` presented as a
Fourier--Mukai transform.

The correspondence, the kernel, the equivalence, and the isomorphism between
them are all supplied. Nothing here proves that any transform is an
equivalence — that is the classical theorem and it needs geometry. -/
structure KernelAutoequivalence (C : Type u) [Category.{w} C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (𝒲 : Type t) [Category.{x} 𝒲] [HasZeroObject 𝒲]
    [HasShift 𝒲 ℤ] [Preadditive 𝒲] [∀ n : ℤ, (shiftFunctor 𝒲 n).Additive]
    [Pretriangulated 𝒲] where
  /-- The correspondence from `C` to itself. -/
  corr : Correspondence C C 𝒲
  /-- The kernel. -/
  kernel : 𝒲
  /-- The autoequivalence. -/
  equiv : C ≌ C
  /-- Its functor is the transform with that kernel. -/
  iso : equiv.functor ≅ corr.transform kernel

namespace KernelAutoequivalence

variable (A : KernelAutoequivalence C 𝒲)

omit [IsTriangulated C] in
/-- On classes of objects, the autoequivalence and its transform agree.

Stated this way round rather than as a `simp` lemma about `K₀.map`: the
existing `K₀.map_of` already rewrites that left-hand side, so a lemma phrased
against it would not be in simp-normal form. -/
theorem of_obj_eq (E : C) :
    K₀.of C (A.equiv.functor.obj E) =
      K₀.of C ((A.corr.transform A.kernel).obj E) :=
  K₀.of_iso C (A.iso.app E)

section ClassMap

variable [A.corr.pull.CommShift ℤ] [(A.corr.tensor.obj A.kernel).CommShift ℤ]
  [A.corr.push.CommShift ℤ] [A.corr.pull.IsTriangulated]
  [(A.corr.tensor.obj A.kernel).IsTriangulated] [A.corr.push.IsTriangulated]
  [A.equiv.functor.CommShift ℤ] [A.equiv.functor.IsTriangulated]

omit [IsTriangulated C] in
/-- **The action on classes is computed by the kernel.**

Exactly `Correspondence.K₀_map_eq_transformK₀` at the supplied isomorphism. It
is what makes the kernel, rather than the functor's construction, the thing
that determines the transported charge.

Until #487 this proof had a step in it: the stability track carried its own
endofunctor-only `K₀.mapF`, definitionally equal to `K₀.map` but a different
constant, and the theorem had to cross that identification. `mapF` is retired
and the crossing is gone. -/
theorem map_eq_transformK₀ :
    K₀.map A.equiv.functor = A.corr.transformK₀ A.kernel :=
  A.corr.K₀_map_eq_transformK₀ A.kernel A.equiv.functor A.iso

end ClassMap

section Dual

/-- A **dual kernel** for a kernel autoequivalence: a kernel presenting the
*quasi-inverse* as a transform of the same correspondence.

Classically this is the derived dual `P^∨ ⊗ p^*ω_X[dim X]`, and its existence is
a theorem about smooth projective varieties. Here it is supplied. What it buys
is that both directions of the equivalence become kernel-computable, which is
what turns `actStab`'s remaining hypothesis into kernel data. -/
structure DualKernel (A : KernelAutoequivalence C 𝒲) where
  /-- The kernel of the quasi-inverse. -/
  dual : 𝒲
  /-- The quasi-inverse is the transform with that kernel. -/
  invIso : A.equiv.inverse ≅ A.corr.transform dual

namespace DualKernel

variable {A} (D : DualKernel A)

variable [A.corr.pull.CommShift ℤ] [A.corr.push.CommShift ℤ]
  [A.corr.pull.IsTriangulated] [A.corr.push.IsTriangulated]
  [(A.corr.tensor.obj D.dual).CommShift ℤ]
  [(A.corr.tensor.obj D.dual).IsTriangulated]
  [A.equiv.inverse.CommShift ℤ] [A.equiv.inverse.IsTriangulated]

omit [IsTriangulated C] in
/-- **The quasi-inverse's action on classes is computed by the dual kernel.**
The mirror of `map_eq_transformK₀`, and the reason `actStabOfDual` can state
its hypothesis in kernel terms. -/
theorem map_inverse_eq_transformK₀ :
    K₀.map A.equiv.inverse = A.corr.transformK₀ D.dual :=
  A.corr.K₀_map_eq_transformK₀ D.dual A.equiv.inverse D.invIso

variable [(A.corr.tensor.obj A.kernel).CommShift ℤ]
  [(A.corr.tensor.obj A.kernel).IsTriangulated]
  [A.equiv.functor.CommShift ℤ] [A.equiv.functor.IsTriangulated]

omit [IsTriangulated C] in
/-- **The two kernels' class maps are mutually inverse.**

Proved from `K₀.map_comp_map_eq_id` on the equivalence's unit, then transported
across both kernel identifications. Neither convolution nor an identity kernel
is involved: the inverse relation comes from the supplied equivalence, not from
`conv P P^∨ ≅ 𝒪_Δ`. -/
theorem transformK₀_dual_comp :
    (A.corr.transformK₀ D.dual).comp (A.corr.transformK₀ A.kernel) =
      AddMonoidHom.id (K₀ C) := by
  rw [← A.map_eq_transformK₀, ← D.map_inverse_eq_transformK₀]
  exact K₀.map_comp_map_eq_id A.equiv.functor A.equiv.inverse
    A.equiv.unitIso.symm

omit [IsTriangulated C] in
/-- The composite in the other order is also the identity. -/
theorem transformK₀_comp_dual :
    (A.corr.transformK₀ A.kernel).comp (A.corr.transformK₀ D.dual) =
      AddMonoidHom.id (K₀ C) := by
  rw [← A.map_eq_transformK₀, ← D.map_inverse_eq_transformK₀]
  exact K₀.map_comp_map_eq_id A.equiv.inverse A.equiv.functor
    A.equiv.counitIso

omit [IsTriangulated C] in
/-- **The kernel's class map, as an automorphism of `K₀ C`.**

The two `comp` lemmas above are exactly the two round-trip identities
`AddMonoidHom.toAddEquiv` asks for, so the bundling is bookkeeping. What it
records is that having a `DualKernel` is what makes the class map invertible:
`transformK₀` on its own is not claimed invertible anywhere
(`FourierMukai/GrothendieckGroup.lean` says so explicitly), and the inverse
here is the *dual kernel's* class map, not an abstract inverse.

The equivalence is on `K₀ C`, not on a class lattice `Λ`. Nothing here maps
`Λ` — `toAutPair` still takes its `lam` as supplied data. -/
def transformK₀AddEquiv : K₀ C ≃+ K₀ C :=
  AddMonoidHom.toAddEquiv (A.corr.transformK₀ A.kernel)
    (A.corr.transformK₀ D.dual) D.transformK₀_dual_comp D.transformK₀_comp_dual

omit [IsTriangulated C] in
@[simp]
theorem transformK₀AddEquiv_apply (x : K₀ C) :
    D.transformK₀AddEquiv x = A.corr.transformK₀ A.kernel x := rfl

omit [IsTriangulated C] in
@[simp]
theorem transformK₀AddEquiv_symm_apply (x : K₀ C) :
    D.transformK₀AddEquiv.symm x = A.corr.transformK₀ D.dual x := rfl

end DualKernel

end Dual

section Adjoint

/-! ### Dual kernels derived from adjunction data

`FourierMukai/Adjunction.lean` supplies `LeftAdjointKernelData` and
`RightAdjointKernelData`: a kernel for the opposite correspondence together
with an adjunction between the two transforms. For a kernel autoequivalence
those give a `DualKernel` outright, by uniqueness of adjoints — the
quasi-inverse of an equivalence is both its left and its right adjoint, so an
adjoint presented by a kernel is isomorphic to it.

`toLeftAdjointKernelData` and `toRightAdjointKernelData` go back, so for a
kernel autoequivalence the three data are interderivable and the constructors
below buy no new *existence*. What they buy is the shape of the input:
`LeftAdjointKernelData` is stated for an arbitrary kernel with no equivalence
in sight, which is the form a geometric adjunction theorem has, whereas
`DualKernel.invIso` presupposes the equivalence and names its inverse. -/

/-- **A dual kernel derived from left-adjoint kernel data.**

`A.equiv.inverse` is left adjoint to `A.equiv.functor`, hence — across `A.iso`
— to `A.corr.transform A.kernel`. `L.adj` says the same of
`A.corr.transform L.adjKernel`. Uniqueness of left adjoints identifies the
two, and that identification is exactly `DualKernel.invIso`.

This is the first constructor of a `DualKernel` from something other than a
directly supplied `invIso`. It is not a *geometric* construction: the
adjunction is still supplied. -/
def DualKernel.ofLeftAdjointKernel
    (L : LeftAdjointKernelData A.corr A.corr A.kernel) : DualKernel A where
  dual := L.adjKernel
  invIso := L.isoOfAdj (A.equiv.symm.toAdjunction.ofNatIsoRight A.iso)

omit [IsTriangulated C] in
@[simp]
theorem DualKernel.ofLeftAdjointKernel_dual
    (L : LeftAdjointKernelData A.corr A.corr A.kernel) :
    (DualKernel.ofLeftAdjointKernel A L).dual = L.adjKernel := rfl

/-- **A dual kernel derived from right-adjoint kernel data.**

The mirror of `ofLeftAdjointKernel`, through `Adjunction.rightAdjointUniq`.
Both exist because the quasi-inverse of an equivalence is an adjoint on both
sides; classically the two adjoint kernels of a general `Φ_P` differ by the
dualizing twist, and it is Serre duality that collapses the difference when
`Φ_P` is an equivalence.

The collapse *is* reachable here — `(ofLeftAdjointKernel A L).toRightAdjointKernelData`
is right-adjoint data with the same kernel `L.adjKernel` — but read where it
comes from: the supplied `A.equiv`, whose inverse is an adjoint on both sides
by construction. No dualizing object and no duality theorem is involved, and
for a kernel with no equivalence attached `FourierMukai/Adjunction.lean` still
relates the two sides not at all. -/
def DualKernel.ofRightAdjointKernel
    (R : RightAdjointKernelData A.corr A.corr A.kernel) : DualKernel A where
  dual := R.adjKernel
  invIso := R.isoOfAdj (A.equiv.toAdjunction.ofNatIsoLeft A.iso)

omit [IsTriangulated C] in
@[simp]
theorem DualKernel.ofRightAdjointKernel_dual
    (R : RightAdjointKernelData A.corr A.corr A.kernel) :
    (DualKernel.ofRightAdjointKernel A R).dual = R.adjKernel := rfl

/-- **A dual kernel already carries the left adjunction.**

The converse of `ofLeftAdjointKernel`, and the reason its docstring does not
claim to weaken the hypothesis: transporting `A.equiv.symm.toAdjunction` along
`A.iso` and `D.invIso` recovers the adjunction. So for a kernel
autoequivalence the two data are interderivable. -/
def DualKernel.toLeftAdjointKernelData (D : DualKernel A) :
    LeftAdjointKernelData A.corr A.corr A.kernel where
  adjKernel := D.dual
  adj := (A.equiv.symm.toAdjunction.ofNatIsoRight A.iso).ofNatIsoLeft D.invIso

omit [IsTriangulated C] in
@[simp]
theorem DualKernel.toLeftAdjointKernelData_adjKernel (D : DualKernel A) :
    (D.toLeftAdjointKernelData).adjKernel = D.dual := rfl

/-- **A dual kernel already carries the right adjunction**, mirroring
`toLeftAdjointKernelData`. -/
def DualKernel.toRightAdjointKernelData (D : DualKernel A) :
    RightAdjointKernelData A.corr A.corr A.kernel where
  adjKernel := D.dual
  adj := (A.equiv.toAdjunction.ofNatIsoLeft A.iso).ofNatIsoRight D.invIso

omit [IsTriangulated C] in
@[simp]
theorem DualKernel.toRightAdjointKernelData_adjKernel (D : DualKernel A) :
    (D.toRightAdjointKernelData).adjKernel = D.dual := rfl

omit [IsTriangulated C] in
/-- The left round trip is the identity **on the kernel**.

Only on the kernel. The reconstructed dual kernel's `invIso` is `D.invIso`
carried across two transports and `Adjunction.leftAdjointUniq`; it is not
claimed equal to `D.invIso`, and proving it so would need that lemma's
coherence statements, which nothing here consumes. -/
theorem DualKernel.ofLeftAdjointKernel_toLeftAdjointKernelData_dual
    (D : DualKernel A) :
    (DualKernel.ofLeftAdjointKernel A D.toLeftAdjointKernelData).dual = D.dual :=
  rfl

omit [IsTriangulated C] in
/-- The right round trip is the identity on the kernel, with the same
caveat. -/
theorem DualKernel.ofRightAdjointKernel_toRightAdjointKernelData_dual
    (D : DualKernel A) :
    (DualKernel.ofRightAdjointKernel A D.toRightAdjointKernelData).dual = D.dual :=
  rfl

end Adjoint

section Action

variable {Λ : Type u'} [AddCommGroup Λ] (v : K₀ C →+ Λ)
  [A.equiv.functor.Additive] [A.equiv.inverse.Additive]
  [A.equiv.functor.CommShift ℤ] [A.equiv.inverse.CommShift ℤ]
  [A.equiv.functor.IsTriangulated] [A.equiv.inverse.IsTriangulated]

/-- The underlying triangulated autoequivalence, with the ambient instances
packed into `TriEquiv`'s fields.

Nothing is added and nothing is proved: `TriEquiv` bundles instances that the
use site already has, and this is the repackaging. `@[reducible]` for the same
reason as `trans` — the fields must stay visible to instance search and to the
defeq checks that `toAutPair_act` relies on. -/
@[reducible]
def toTriEquiv : GroupAction.TriEquiv C where
  e := A.equiv
  fAdd := inferInstance
  iAdd := inferInstance
  fCS := inferInstance
  iCS := inferInstance
  fTri := inferInstance
  iTri := inferInstance

/-- **A kernel autoequivalence transports a stability condition.**

A thin specialisation of `actStabAut`, and deliberately so: the content is that
the Fourier--Mukai side can supply the autoequivalence at all, not that the
transport needs redoing.

`hlam` is stated for the *quasi-inverse*, following `actStabAut`. Classically
the quasi-inverse of a Fourier--Mukai equivalence is again one, with the
derived-dual kernel, and `hlam` would follow from `map_eq_transformK₀` for
that kernel; nothing here supplies it. -/
def actStab (lam : Λ →+ Λ)
    (hlam : ∀ x : K₀ C, v (K₀.map A.equiv.inverse x) = lam (v x))
    (σ : StabilityCondition.WithClassMap C v) :
    StabilityCondition.WithClassMap C v :=
  actStabAut A.equiv v lam hlam σ

@[simp]
theorem actStab_slicing (lam : Λ →+ Λ) (hlam) (σ) :
    (A.actStab v lam hlam σ).slicing =
      CategoryTheory.Triangulated.Slicing.mapEquiv σ.slicing A.equiv :=
  rfl

@[simp]
theorem actStab_Z (lam : Λ →+ Λ) (hlam) (σ) (x : Λ) :
    (A.actStab v lam hlam σ).Z x = σ.Z (lam x) :=
  rfl

section OfDual

variable (D : DualKernel A)
  [A.corr.pull.CommShift ℤ] [A.corr.push.CommShift ℤ]
  [A.corr.pull.IsTriangulated] [A.corr.push.IsTriangulated]
  [(A.corr.tensor.obj D.dual).CommShift ℤ]
  [(A.corr.tensor.obj D.dual).IsTriangulated]

/-- **Transport with the compatibility stated in kernel terms.**

Identical to `actStab` except for its hypothesis: `hlam` is asked against
`transformK₀ D.dual`, which is computed from the dual kernel, rather than
against `K₀.map A.equiv.inverse`, which is opaque. `map_inverse_eq_transformK₀`
identifies the two, so this is the same transport with a checkable premise. -/
def actStabOfDual (lam : Λ →+ Λ)
    (hlam : ∀ x : K₀ C, v (A.corr.transformK₀ D.dual x) = lam (v x))
    (σ : StabilityCondition.WithClassMap C v) :
    StabilityCondition.WithClassMap C v :=
  A.actStab v lam (fun x => by
    rw [show K₀.map A.equiv.inverse = A.corr.transformK₀ D.dual from
      D.map_inverse_eq_transformK₀]
    exact hlam x) σ

@[simp]
theorem actStabOfDual_slicing (lam : Λ →+ Λ) (hlam) (σ) :
    (A.actStabOfDual v D lam hlam σ).slicing =
      CategoryTheory.Triangulated.Slicing.mapEquiv σ.slicing A.equiv :=
  rfl

@[simp]
theorem actStabOfDual_Z (lam : Λ →+ Λ) (hlam) (σ) (x : Λ) :
    (A.actStabOfDual v D lam hlam σ).Z x = σ.Z (lam x) :=
  rfl

/-! ### Entry into the group

`Stability/ClassMap.lean` builds a genuine `Group` — `AutPairQuot v` — acting
on `WithClassMap C v`, out of pairs `(Φ, lam)` with `lam` invertible. The
three declarations below put a kernel autoequivalence into it and check that
nothing changes: the group element's action *is* `actStabOfDual`.

The strengthening relative to `actStabOfDual` is `lam`'s invertibility, and it
is a real hypothesis, not repackaging — `AutPair`'s own docstring makes the
point. A kernel autoequivalence with a non-invertible compatible `lam` still
transports stability conditions via `actStabOfDual`; it just is not a member
of this group. -/

/-- **A kernel autoequivalence with a dual kernel is an element of the acting
group.**

Every input is already on the table: `A` supplies the autoequivalence, `D`
makes both directions kernel-computable, and `lam` is the class-lattice
automorphism — supplied, exactly as in `AutPair`, because `v` is arbitrary and
nothing recovers `lam` from `A`.

The hypothesis is in kernel terms, matching `actStabOfDual` rather than
`actStab`: `AutPair.compat` is stated against the opaque
`K₀.map A.equiv.inverse`, and `map_inverse_eq_transformK₀` is what turns the
checkable premise into it. That identification is the whole content of this
definition. -/
def toAutPair (lam : Λ ≃+ Λ)
    (hlam : ∀ x : K₀ C, v (A.corr.transformK₀ D.dual x) = lam (v x)) :
    GroupAction.AutPair v where
  Φ := A.toTriEquiv
  lam := lam
  compat x := by
    show v (K₀.map A.equiv.inverse x) = lam (v x)
    rw [show K₀.map A.equiv.inverse = A.corr.transformK₀ D.dual from
      D.map_inverse_eq_transformK₀]
    exact hlam x

omit [IsTriangulated C] in
@[simp]
theorem toAutPair_lam (lam : Λ ≃+ Λ) (hlam) :
    (A.toAutPair v D lam hlam).lam = lam := rfl

/-- **The group element acts by the transport it came from.**

`rfl`: `AutPair.act` is `actStabAut` with the datum bundled, `actStabOfDual`
is `actStabAut` with a rewritten premise, and the premises are propositions.
Stated anyway, because "the element exists" and "the element acts the way you
expect" are different claims and only the second is worth citing. -/
theorem toAutPair_act (lam : Λ ≃+ Λ) (hlam) (σ) :
    (A.toAutPair v D lam hlam).act σ =
      A.actStabOfDual v D lam.toAddMonoidHom (fun x => hlam x) σ :=
  rfl

/-- The same statement at the quotient, where the `MulAction` actually lives.

This is the sentence the round-2 review found missing: the transported
stability condition is the image of `σ` under a group element, not merely the
value of a map. -/
theorem mk_toAutPair_smul (lam : Λ ≃+ Λ) (hlam) (σ) :
    GroupAction.AutPairQuot.mk (A.toAutPair v D lam hlam) • σ =
      A.actStabOfDual v D lam.toAddMonoidHom (fun x => hlam x) σ :=
  rfl

end OfDual

end Action

end KernelAutoequivalence

section Trans

-- Independent universes for the three kernel categories, matching the
-- polymorphism of the generic `FourierMukai` modules: nothing about
-- composition forces two transforms' kernels to live at the same size.
variable {𝒲₁ : Type t₁} {𝒲₂ : Type t₂} {𝒲₃ : Type t₃}
  [Category.{x₁} 𝒲₁] [HasZeroObject 𝒲₁] [HasShift 𝒲₁ ℤ] [Preadditive 𝒲₁]
  [∀ n : ℤ, (shiftFunctor 𝒲₁ n).Additive] [Pretriangulated 𝒲₁]
  [Category.{x₂} 𝒲₂] [HasZeroObject 𝒲₂] [HasShift 𝒲₂ ℤ] [Preadditive 𝒲₂]
  [∀ n : ℤ, (shiftFunctor 𝒲₂ n).Additive] [Pretriangulated 𝒲₂]
  [Category.{x₃} 𝒲₃] [HasZeroObject 𝒲₃] [HasShift 𝒲₃ ℤ] [Preadditive 𝒲₃]
  [∀ n : ℤ, (shiftFunctor 𝒲₃ n).Additive] [Pretriangulated 𝒲₃]

/-- **Composing two kernel autoequivalences, given convolution data.**

The composite is again a kernel autoequivalence, and its kernel is the
*convolution* of the two. The isomorphism is the one
`ConvolutionData.isKernelFunctor_comp` already uses: whisker each supplied
isomorphism into place, then apply `compIso`.

`corr₃` and the convolution data are supplied — this constructs the composite
from them, it does not produce a correspondence for the composite out of
nothing.

Marked `@[reducible]` so that instance search sees `equiv` as
`A₁.equiv.trans A₂.equiv` and picks up the six `Equivalence.trans` instances
from `Stability/Composition`. Declaring them by hand for the composite instead
does not work: `IsTriangulated` is indexed by the `CommShift` instance, so a
hand-rolled copy is a different term from the one the use site finds. -/
@[reducible]
def KernelAutoequivalence.trans (A₁ : KernelAutoequivalence C 𝒲₁)
    (A₂ : KernelAutoequivalence C 𝒲₂) (corr₃ : Correspondence C C 𝒲₃)
    (D : ConvolutionData A₁.corr A₂.corr corr₃) : KernelAutoequivalence C 𝒲₃ where
  corr := corr₃
  kernel := D.conv A₁.kernel A₂.kernel
  equiv := A₁.equiv.trans A₂.equiv
  iso := Functor.isoWhiskerRight A₁.iso A₂.equiv.functor ≪≫
    Functor.isoWhiskerLeft (A₁.corr.transform A₁.kernel) A₂.iso ≪≫
      D.compIso A₁.kernel A₂.kernel

omit [IsTriangulated C] in
@[simp]
theorem KernelAutoequivalence.trans_kernel (A₁ : KernelAutoequivalence C 𝒲₁)
    (A₂ : KernelAutoequivalence C 𝒲₂) (corr₃ : Correspondence C C 𝒲₃)
    (D : ConvolutionData A₁.corr A₂.corr corr₃) :
    (A₁.trans A₂ corr₃ D).kernel = D.conv A₁.kernel A₂.kernel := rfl

omit [IsTriangulated C] in
@[simp]
theorem KernelAutoequivalence.trans_equiv (A₁ : KernelAutoequivalence C 𝒲₁)
    (A₂ : KernelAutoequivalence C 𝒲₂) (corr₃ : Correspondence C C 𝒲₃)
    (D : ConvolutionData A₁.corr A₂.corr corr₃) :
    (A₁.trans A₂ corr₃ D).equiv = A₁.equiv.trans A₂.equiv := rfl

variable {Λ : Type u'} [AddCommGroup Λ] (v : K₀ C →+ Λ)

/-- **Transporting along two kernel autoequivalences is transporting along the
convolved one.**

The composition law the lane was aimed at: the kernel that computes the
composite action is `conv P Q`, so the action on stability conditions is
tracked by kernels the whole way. The proof is `actStabAut_trans` — the
transport does not know it came from a kernel — plus the fact that
`(A₁.trans A₂ corr₃ D).equiv` is `A₁.equiv.trans A₂.equiv` definitionally. -/
theorem KernelAutoequivalence.actStab_trans (A₁ : KernelAutoequivalence C 𝒲₁)
    (A₂ : KernelAutoequivalence C 𝒲₂) (corr₃ : Correspondence C C 𝒲₃)
    (D : ConvolutionData A₁.corr A₂.corr corr₃)
    [A₁.equiv.functor.Additive] [A₁.equiv.inverse.Additive]
    [A₂.equiv.functor.Additive] [A₂.equiv.inverse.Additive]
    [A₁.equiv.functor.CommShift ℤ] [A₁.equiv.inverse.CommShift ℤ]
    [A₂.equiv.functor.CommShift ℤ] [A₂.equiv.inverse.CommShift ℤ]
    [A₁.equiv.functor.IsTriangulated] [A₁.equiv.inverse.IsTriangulated]
    [A₂.equiv.functor.IsTriangulated] [A₂.equiv.inverse.IsTriangulated]
    {lam₁ lam₂ : Λ →+ Λ}
    (h₁ : ∀ x : K₀ C, v (K₀.map A₁.equiv.inverse x) = lam₁ (v x))
    (h₂ : ∀ x : K₀ C, v (K₀.map A₂.equiv.inverse x) = lam₂ (v x))
    (σ : StabilityCondition.WithClassMap C v) :
    A₂.actStab v lam₂ h₂ (A₁.actStab v lam₁ h₁ σ)
      = (A₁.trans A₂ corr₃ D).actStab v (lam₁.comp lam₂)
          (hlam_trans v A₁.equiv A₂.equiv h₁ h₂) σ :=
  actStabAut_trans v A₁.equiv A₂.equiv h₁ h₂ σ

end Trans

section Identity

/-- A **unit kernel**: a kernel presenting the identity functor as a transform.

Classically this is `𝒪_Δ ∈ D(X × X)`, and that its transform is the identity is
a theorem about the diagonal. Here it is supplied, like every other geometric
input to this file. -/
structure UnitKernelData (corr : Correspondence C C 𝒲) where
  /-- The kernel. -/
  unitKernel : 𝒲
  /-- It presents `𝟭 C` as a transform of `corr`. -/
  unitIso : 𝟭 C ≅ corr.transform unitKernel

/-- **The identity kernel autoequivalence**, from a unit kernel.

`Equivalence.refl.functor` and `Equivalence.refl.inverse` are both `𝟭 C`
definitionally, so the one supplied isomorphism serves as `iso` here and as
`invIso` in `UnitKernelData.toDualKernel`.

`@[reducible]` for the same reason as `trans`: a use site's instance search
has to see `equiv` as `Equivalence.refl`.

This produces the unit **object**, and only that. It is not proved to be a
unit for `trans`, and cannot be without convolution data comparing `corr` with
itself — see the module docstring. -/
@[reducible]
def KernelAutoequivalence.id (corr : Correspondence C C 𝒲)
    (U : UnitKernelData corr) : KernelAutoequivalence C 𝒲 where
  corr := corr
  kernel := U.unitKernel
  equiv := CategoryTheory.Equivalence.refl
  iso := U.unitIso

omit [IsTriangulated C] in
@[simp]
theorem KernelAutoequivalence.id_kernel (corr : Correspondence C C 𝒲)
    (U : UnitKernelData corr) :
    (KernelAutoequivalence.id corr U).kernel = U.unitKernel := rfl

omit [IsTriangulated C] in
@[simp]
theorem KernelAutoequivalence.id_equiv (corr : Correspondence C C 𝒲)
    (U : UnitKernelData corr) :
    (KernelAutoequivalence.id corr U).equiv = CategoryTheory.Equivalence.refl := rfl

omit [IsTriangulated C] in
@[simp]
theorem KernelAutoequivalence.id_corr (corr : Correspondence C C 𝒲)
    (U : UnitKernelData corr) :
    (KernelAutoequivalence.id corr U).corr = corr := rfl

/-- **The identity's dual kernel is the unit kernel itself.**

The one place the identity costs nothing extra: `Equivalence.refl.inverse` is
`𝟭 C`, so the same supplied isomorphism discharges `DualKernel.invIso`. Every
`DualKernel` consequence — `transformK₀AddEquiv`, `actStabOfDual`,
`toAutPair` — therefore applies to `KernelAutoequivalence.id` with no further
geometric input. -/
def UnitKernelData.toDualKernel {corr : Correspondence C C 𝒲}
    (U : UnitKernelData corr) :
    KernelAutoequivalence.DualKernel (KernelAutoequivalence.id corr U) where
  dual := U.unitKernel
  invIso := U.unitIso

omit [IsTriangulated C] in
@[simp]
theorem UnitKernelData.toDualKernel_dual {corr : Correspondence C C 𝒲}
    (U : UnitKernelData corr) :
    U.toDualKernel.dual = U.unitKernel := rfl

/-- **The unit kernel is a left adjoint kernel for itself.**

`𝟭 C ⊣ 𝟭 C`, transported along `U.unitIso` on both sides. This is the only
`LeftAdjointKernelData` this repository produces, and it is the trivial one:
it says the identity is its own adjoint, which is true in any category and
carries no information about `corr`.

Its point is that `LeftAdjointKernelData` is inhabited from data the tree
already has, so the adjunction layer is not an interface nothing can reach.
A non-trivial instance is Grothendieck duality and is not available here. -/
def UnitKernelData.toLeftAdjointKernelData {corr : Correspondence C C 𝒲}
    (U : UnitKernelData corr) :
    LeftAdjointKernelData corr corr U.unitKernel where
  adjKernel := U.unitKernel
  adj := (Adjunction.id.ofNatIsoLeft U.unitIso).ofNatIsoRight U.unitIso

-- `LeftAdjointKernelData` asks for no triangulated structure, so this statement
-- uses none of the ambient hypotheses beyond the two categories.
omit [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  [HasZeroObject 𝒲] [HasShift 𝒲 ℤ] [Preadditive 𝒲]
  [∀ n : ℤ, (shiftFunctor 𝒲 n).Additive] [Pretriangulated 𝒲] in
@[simp]
theorem UnitKernelData.toLeftAdjointKernelData_adjKernel
    {corr : Correspondence C C 𝒲} (U : UnitKernelData corr) :
    U.toLeftAdjointKernelData.adjKernel = U.unitKernel := rfl

omit [IsTriangulated C] in
/-- **The derived dual kernel of the identity is the supplied one.**

On the kernel object. Running `U.toLeftAdjointKernelData` through
`DualKernel.ofLeftAdjointKernel` lands on `U.unitKernel`, which is what
`toDualKernel` supplies directly. The two `invIso` fields are not claimed
equal — `toDualKernel` uses `U.unitIso` itself, while the derived one is the
image of an adjunction under `Adjunction.leftAdjointUniq`. -/
theorem UnitKernelData.ofLeftAdjointKernel_dual {corr : Correspondence C C 𝒲}
    (U : UnitKernelData corr) :
    (KernelAutoequivalence.DualKernel.ofLeftAdjointKernel
        (KernelAutoequivalence.id corr U) U.toLeftAdjointKernelData).dual =
      U.toDualKernel.dual := rfl

/-- **`UnitKernelData` is satisfiable.**

The trivial correspondence's transform is the identity definitionally, so the
identity functor is presented by every kernel and `unitIso` is `Iso.refl`.

Satisfiability only, exactly as in `FourierMukai/Witness.lean`: this says the
structure's fields can be met simultaneously. It says nothing about `𝒪_Δ`,
nothing about any diagonal, and nothing about whether
`Families.geometricUnitKernelData`'s contracts are dischargeable. -/
def trivialUnitKernelData (K : C) :
    UnitKernelData (FourierMukai.trivialCorrespondence C) where
  unitKernel := K
  unitIso := Iso.refl _

omit [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  [HasZeroObject 𝒲] [HasShift 𝒲 ℤ] [Preadditive 𝒲]
  [∀ n : ℤ, (shiftFunctor 𝒲 n).Additive] [Pretriangulated 𝒲] in
@[simp]
theorem trivialUnitKernelData_unitKernel (K : C) :
    (trivialUnitKernelData K).unitKernel = K := rfl

end Identity

section FromAdjoint

/-! ### The equivalence, derived rather than supplied

`KernelAutoequivalence` takes its equivalence and the comparison isomorphism as
supplied fields, and every consequence in this file is conditional on them. This
section removes that particular supply point: a `RightAdjointKernelData` whose
adjunction has invertible unit and counit already *is* an equivalence, by
`Adjunction.toEquivalence`, and its functor is the transform definitionally — so
the comparison isomorphism is `Iso.refl`.

**This is not a weakening, and `isIso_unit`/`isIso_counit` below prove it.**
Given a kernel autoequivalence together with a right adjoint kernel, the
adjunction's unit and counit are invertible: Mathlib supplies that as instances
once the functors are equivalences. So the two data are interderivable, exactly
as `DualKernel` and `LeftAdjointKernelData` are.

What changes is the *shape of the hypothesis*, and that is the whole point.
"There exists an equivalence and an isomorphism to the transform" is not
something a geometric theorem produces. "The unit and counit of this adjunction
are isomorphisms" is: it is pointwise, it is checkable, and its two halves are
full faithfulness and essential surjectivity — which is the form the
Bondal--Orlov criterion actually takes. `ofFullyFaithful` below is that split,
using Mathlib's `unit_isIso_of_L_fully_faithful`.

Nothing here supplies the invertibility. That is the second half of the layer-3
work and it needs geometry this repository does not have. -/

variable (corr : Correspondence C C 𝒲) (K : 𝒲)

/-- **A kernel autoequivalence, from an adjoint kernel with invertible unit and
counit.**

`Adjunction.toEquivalence` on the supplied adjunction. Its `functor` field is
`corr.transform K` definitionally, so `iso` is `Iso.refl` and nothing is
transported.

The first constructor of a `KernelAutoequivalence` from anything other than a
directly supplied equivalence. -/
@[reducible] noncomputable def KernelAutoequivalence.ofRightAdjointKernel
    (R : RightAdjointKernelData corr corr K)
    [∀ X, IsIso (R.adj.unit.app X)] [∀ Y, IsIso (R.adj.counit.app Y)] :
    KernelAutoequivalence C 𝒲 where
  corr := corr
  kernel := K
  -- `functor` and `inverse` are given LITERALLY rather than left as
  -- `R.adj.toEquivalence`'s fields. `toEquivalence` is not reducible, so
  -- `.equiv.functor` would not reduce for instance search, and every exactness
  -- argument downstream (`actStab`, `actStabOfDual`, `toAutPair`) is
  -- synthesised rather than rewritten. Written this way the projection lands on
  -- `corr.transform _`, an abbrev, so the composite's own instances apply --
  -- with the CommShift indexing that `IsTriangulated` depends on intact, which
  -- a hand-rolled instance could not reproduce.
  equiv :=
    { functor := corr.transform K
      inverse := corr.transform R.adjKernel
      unitIso := R.adj.toEquivalence.unitIso
      counitIso := R.adj.toEquivalence.counitIso
      functor_unitIso_comp := R.adj.toEquivalence.functor_unitIso_comp }
  iso := Iso.refl _

omit [IsTriangulated C] in
@[simp]
theorem KernelAutoequivalence.ofRightAdjointKernel_corr
    (R : RightAdjointKernelData corr corr K)
    [∀ X, IsIso (R.adj.unit.app X)] [∀ Y, IsIso (R.adj.counit.app Y)] :
    (KernelAutoequivalence.ofRightAdjointKernel corr K R).corr = corr := rfl

omit [IsTriangulated C] in
@[simp]
theorem KernelAutoequivalence.ofRightAdjointKernel_kernel
    (R : RightAdjointKernelData corr corr K)
    [∀ X, IsIso (R.adj.unit.app X)] [∀ Y, IsIso (R.adj.counit.app Y)] :
    (KernelAutoequivalence.ofRightAdjointKernel corr K R).kernel = K := rfl

/-- **The same datum also gives the dual kernel, for free.**

`toEquivalence`'s `inverse` is the adjunction's right adjoint, which is
`corr.transform R.adjKernel` definitionally — so `invIso` is `Iso.refl` and
`DualKernel.ofRightAdjointKernel`'s trip through `Adjunction.rightAdjointUniq`
is not needed here. One `RightAdjointKernelData` with invertible unit and counit
yields the equivalence *and* its dual kernel. -/
@[reducible] noncomputable def KernelAutoequivalence.dualKernelOfRightAdjointKernel
    (R : RightAdjointKernelData corr corr K)
    [∀ X, IsIso (R.adj.unit.app X)] [∀ Y, IsIso (R.adj.counit.app Y)] :
    KernelAutoequivalence.DualKernel
      (KernelAutoequivalence.ofRightAdjointKernel corr K R) where
  dual := R.adjKernel
  invIso := Iso.refl _

omit [IsTriangulated C] in
@[simp]
theorem KernelAutoequivalence.dualKernelOfRightAdjointKernel_dual
    (R : RightAdjointKernelData corr corr K)
    [∀ X, IsIso (R.adj.unit.app X)] [∀ Y, IsIso (R.adj.counit.app Y)] :
    (KernelAutoequivalence.dualKernelOfRightAdjointKernel corr K R).dual =
      R.adjKernel := rfl

/-- **The hypothesis split the way a criterion would deliver it.**

Full faithfulness of the transform gives the unit, by Mathlib's
`unit_isIso_of_L_fully_faithful`; the counit is still asked for, and it is the
essential-surjectivity half. Stated because this is the shape Bondal--Orlov has
— fully faithful, plus a condition — and a geometric criterion would land here
rather than on the raw unit. -/
noncomputable def KernelAutoequivalence.ofFullyFaithful
    (R : RightAdjointKernelData corr corr K)
    [(corr.transform K).Full] [(corr.transform K).Faithful]
    [∀ Y, IsIso (R.adj.counit.app Y)] :
    KernelAutoequivalence C 𝒲 :=
  have : IsIso R.adj.unit := R.adj.unit_isIso_of_L_fully_faithful
  have : ∀ X, IsIso (R.adj.unit.app X) := fun X => inferInstanceAs (IsIso (R.adj.unit.app X))
  KernelAutoequivalence.ofRightAdjointKernel corr K R

omit [IsTriangulated C] in
@[simp]
theorem KernelAutoequivalence.ofFullyFaithful_kernel
    (R : RightAdjointKernelData corr corr K)
    [(corr.transform K).Full] [(corr.transform K).Faithful]
    [∀ Y, IsIso (R.adj.counit.app Y)] :
    (KernelAutoequivalence.ofFullyFaithful corr K R).kernel = K := rfl

/-! ### The converse: nothing above weakens the hypothesis

If a kernel autoequivalence and a right adjoint kernel for the same kernel are
both on the table, the adjunction's unit and counit are already invertible. So
`ofRightAdjointKernel` does not lower the bar — it restates it in a form a
geometric criterion can attack. This is the same honesty check
`DualKernel.toLeftAdjointKernelData` performs one layer down. -/

omit [IsTriangulated C] in
/-- The transform of a kernel autoequivalence is an equivalence.  Transport of
`A.equiv` along the supplied `A.iso`, and the hinge of both lemmas below. -/
theorem KernelAutoequivalence.transform_isEquivalence
    (A : KernelAutoequivalence C 𝒲) :
    (A.corr.transform A.kernel).IsEquivalence :=
  have : A.equiv.functor.IsEquivalence := inferInstance
  Functor.isEquivalence_of_iso A.iso

omit [IsTriangulated C] in
/-- **The counit of any right adjoint kernel is invertible**, given the
equivalence. -/
theorem KernelAutoequivalence.isIso_counit (A : KernelAutoequivalence C 𝒲)
    (R : RightAdjointKernelData A.corr A.corr A.kernel) : IsIso R.adj.counit :=
  have := A.transform_isEquivalence
  inferInstance

omit [IsTriangulated C] in
/-- **The unit of any right adjoint kernel is invertible**, given the
equivalence.

Through `isEquivalence_right_of_isEquivalence_left`: the right adjoint of an
equivalence is an equivalence, and Mathlib's instance then gives the unit. -/
theorem KernelAutoequivalence.isIso_unit (A : KernelAutoequivalence C 𝒲)
    (R : RightAdjointKernelData A.corr A.corr A.kernel) : IsIso R.adj.unit :=
  have := A.transform_isEquivalence
  have := R.adj.isEquivalence_right_of_isEquivalence_left
  inferInstance


end FromAdjoint

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry
