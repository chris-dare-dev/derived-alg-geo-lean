/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-!
# The stalk of a tensor product of presheaves of modules

Let `R` be a presheaf of commutative rings on a topological space `X`, and let `M` and `P` be
presheaves of `R`-modules. This file proves

`stalkTensorEquiv : Mₓ ⊗[Rₓ] Pₓ ≃ₗ[Rₓ] (M ⊗ P)ₓ`,

the statement that taking stalks commutes with the tensor product of presheaves of modules.

## Main definitions

* `PresheafOfModules.stalkTensorBackward` — `Mₓ ⊗[Rₓ] Pₓ → (M ⊗ P)ₓ`, built from the biadditive
  `germTmulBiadd` by `TensorProduct.lift`;
* `PresheafOfModules.stalkTensorForward` — `(M ⊗ P)ₓ → Mₓ ⊗[Rₓ] Pₓ`, the colimit map of the
  cocone whose legs send `m ⊗ p` to `germ m ⊗ germ p`;
* `PresheafOfModules.stalkTensorEquiv` — the two assembled into an `Rₓ`-linear equivalence;
* `PresheafOfModules.stalkMap` — the stalk map of a morphism of presheaves of modules, as an
  `Rₓ`-linear map;
* `PresheafOfModules.isIso_stalkMapAdd_whiskerLeft` — **whiskering preserves stalkwise
  isomorphisms**, for an arbitrary whiskering factor. Tensoring is only right exact, but
  tensoring with an isomorphism is an isomorphism, and `stalkTensorEquiv` is what makes that
  visible on stalks.

## Implementation notes

The backward map is the harder direction: a section of `M ⊗ P` near `x` is a sum of pure tensors
whose two factors live over *different* neighbourhoods, so the map is built in two colimit stages
(`germTmulRight`, then `germTmulBiadd`), additively first and upgraded to `Rₓ`-bilinear afterwards.
The key input is `PresheafOfModules.germ_smul`, which makes germs `Rₓ`-linear.
-/

universe u
open CategoryTheory Opposite TopologicalSpace TensorProduct Limits MonoidalCategory

namespace PresheafOfModules

variable {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}
variable (M P : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) (x : X)

attribute [local instance] PresheafOfModules.monoidalCategory


/-- `Mₓ ⊗ Pₓ`, the target of the comparison. -/
abbrev StalkTensor : Type u :=
  ↑(TopCat.Presheaf.stalk M.presheaf x) ⊗[R.stalk x] ↑(TopCat.Presheaf.stalk P.presheaf x)

/-- `Mₓ ⊗ Pₓ` viewed over `R(U)` for a neighbourhood `U` of `x`, via the germ map. -/
@[reducible] noncomputable def stalkTensorModuleAt (U : Opens X) (hx : x ∈ U) :
    Module (R.obj (op U)) (StalkTensor M P x) :=
  Module.compHom _ (R.germ U x hx).hom

/-- The `R(U)`-bilinear map `(m, p) ↦ germ m ⊗ germ p`. -/
noncomputable def stalkTensorBilin (U : Opens X) (hx : x ∈ U) :
    letI := stalkTensorModuleAt M P x U hx
    M.obj (op U) →ₗ[R.obj (op U)] P.obj (op U) →ₗ[R.obj (op U)] StalkTensor M P x :=
  letI := stalkTensorModuleAt M P x U hx
  LinearMap.mk₂ (R.obj (op U))
    (fun m p => TopCat.Presheaf.germ M.presheaf U x hx m ⊗ₜ
      TopCat.Presheaf.germ P.presheaf U x hx p)
    (fun m m' p => by
      have h : TopCat.Presheaf.germ M.presheaf U x hx (m + m')
          = TopCat.Presheaf.germ M.presheaf U x hx m
            + TopCat.Presheaf.germ M.presheaf U x hx m' := map_add _ _ _
      rw [h, TensorProduct.add_tmul])
    (fun a m p => by
      have h : TopCat.Presheaf.germ M.presheaf U x hx (a • m)
          = R.germ U x hx a • TopCat.Presheaf.germ M.presheaf U x hx m := germ_smul M x U hx a m
      rw [h]
      exact (TensorProduct.smul_tmul' _ _ _).symm)
    (fun m p p' => by
      have h : TopCat.Presheaf.germ P.presheaf U x hx (p + p')
          = TopCat.Presheaf.germ P.presheaf U x hx p
            + TopCat.Presheaf.germ P.presheaf U x hx p' := map_add _ _ _
      rw [h, TensorProduct.tmul_add])
    (fun a m p => by
      have h : TopCat.Presheaf.germ P.presheaf U x hx (a • p)
          = R.germ U x hx a • TopCat.Presheaf.germ P.presheaf U x hx p := germ_smul P x U hx a p
      rw [h]
      exact TensorProduct.tmul_smul (R := ↑(R.stalk x)) _ _ _)



/-- Restriction of a section, stated at the plain module type rather than through
`restrictScalars`. Reducible, so that `rw` still sees through it. -/
@[reducible] noncomputable def resSec {N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    {U V : Opens X} (h : V ≤ U) (n : N.obj (op U)) : N.obj (op V) :=
  N.map (homOfLE h).op n

/-- For a section `m` of `M` over `U` and a section `p` of `P` over `V`, the germ at `x` of
`m ⊗ p` restricted to `U ⊓ V`. This is the value the backward map must take on germs. -/
noncomputable def germTmul {U V : Opens X} (hxU : x ∈ U) (hxV : x ∈ V)
    (m : M.obj (op U)) (p : P.obj (op V)) :
    ToType (TopCat.Presheaf.stalk
      (MonoidalCategory.tensorObj (C := PresheafOfModules.{u} _) M P).presheaf x) :=
  TopCat.Presheaf.germ
    (MonoidalCategory.tensorObj (C := PresheafOfModules.{u} _) M P).presheaf
    (U ⊓ V) x ⟨hxU, hxV⟩
      (M.map (homOfLE inf_le_left).op m ⊗ₜ P.map (homOfLE inf_le_right).op p)

/-- Shrinking the neighbourhood of `m` does not change the germ of `m ⊗ p`. -/
lemma germTmul_res_left {U U' V : Opens X} (h : U' ≤ U) (hxU' : x ∈ U') (hxV : x ∈ V)
    (m : M.obj (op U)) (p : P.obj (op V)) :
    germTmul M P x (h hxU') hxV m p
      = germTmul M P x hxU' hxV (M.map (homOfLE h).op m) p := by
  unfold germTmul
  rw [← TopCat.Presheaf.germ_res_apply
    (MonoidalCategory.tensorObj (C := PresheafOfModules.{u} _) M P).presheaf
    (homOfLE (inf_le_inf_right V h)) x ⟨hxU', hxV⟩]
  congr 1
  erw [Monoidal.tensorObj_map_tmul]
  congr 1
  · show M.presheaf.map _ (M.presheaf.map _ m) = M.presheaf.map _ (M.presheaf.map _ m)
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    congr 2
  · show P.presheaf.map _ (P.presheaf.map _ p) = P.presheaf.map _ p
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl

/-- Shrinking the neighbourhood of `p` does not change the germ of `m ⊗ p`. -/
lemma germTmul_res_right {U V V' : Opens X} (h : V' ≤ V) (hxU : x ∈ U) (hxV' : x ∈ V')
    (m : M.obj (op U)) (p : P.obj (op V)) :
    germTmul M P x hxU (h hxV') m p
      = germTmul M P x hxU hxV' m (P.map (homOfLE h).op p) := by
  unfold germTmul
  rw [← TopCat.Presheaf.germ_res_apply
    (MonoidalCategory.tensorObj (C := PresheafOfModules.{u} _) M P).presheaf
    (homOfLE (inf_le_inf_left U h)) x ⟨hxU, hxV'⟩]
  congr 1
  erw [Monoidal.tensorObj_map_tmul]
  congr 1
  · show M.presheaf.map _ (M.presheaf.map _ m) = M.presheaf.map _ m
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  · show P.presheaf.map _ (P.presheaf.map _ p) = P.presheaf.map _ (P.presheaf.map _ p)
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    congr 2

/-- `germTmul` depends only on the two germs, not on the sections representing them. -/
lemma germTmul_congr {U U' V V' : Opens X} (hxU : x ∈ U) (hxU' : x ∈ U')
    (hxV : x ∈ V) (hxV' : x ∈ V')
    (m : M.obj (op U)) (m' : M.obj (op U')) (p : P.obj (op V)) (p' : P.obj (op V'))
    (hm : TopCat.Presheaf.germ M.presheaf U x hxU m
        = TopCat.Presheaf.germ M.presheaf U' x hxU' m')
    (hp : TopCat.Presheaf.germ P.presheaf V x hxV p
        = TopCat.Presheaf.germ P.presheaf V' x hxV' p') :
    germTmul M P x hxU hxV m p = germTmul M P x hxU' hxV' m' p' := by
  obtain ⟨W, hxW, iU, iU', hW⟩ := TopCat.Presheaf.germ_eq M.presheaf x hxU hxU' m m' hm
  obtain ⟨W', hxW', iV, iV', hW'⟩ := TopCat.Presheaf.germ_eq P.presheaf x hxV hxV' p p' hp
  have l : germTmul M P x hxU hxV m p
      = germTmul M P x hxW hxW' (M.map iU.op m) (P.map iV.op p) :=
    (germTmul_res_left M P x (leOfHom iU) hxW hxV m p).trans
      (germTmul_res_right M P x (leOfHom iV) hxW hxW' (M.map iU.op m) p)
  have r : germTmul M P x hxU' hxV' m' p'
      = germTmul M P x hxW hxW' (M.map iU'.op m') (P.map iV'.op p') :=
    (germTmul_res_left M P x (leOfHom iU') hxW hxV' m' p').trans
      (germTmul_res_right M P x (leOfHom iV') hxW hxW' (M.map iU'.op m') p')
  rw [l, r]
  -- `congr` discharges the two component goals with `hW` and `hW'` from context
  congr 1

/-- Over a single neighbourhood, `germTmul` is just the germ of the pure tensor. -/
lemma germTmul_self {U : Opens X} (hxU : x ∈ U)
    (m : M.obj (op U)) (p : P.obj (op U)) :
    germTmul M P x hxU hxU m p
      = TopCat.Presheaf.germ
          (MonoidalCategory.tensorObj (C := PresheafOfModules.{u} _) M P).presheaf
          U x hxU (m ⊗ₜ p) := by
  unfold germTmul
  rw [← TopCat.Presheaf.germ_res_apply
    (MonoidalCategory.tensorObj (C := PresheafOfModules.{u} _) M P).presheaf
    (homOfLE (inf_le_left : U ⊓ U ≤ U)) x ⟨hxU, hxU⟩ (m ⊗ₜ p)]
  congr 1

/-- The scalar action on the stalk, over a single neighbourhood: this is the `Rₓ`-linearity
of the backward map, before the three neighbourhoods are separated. -/
lemma germ_smul_germTmul_self {U : Opens X} (hxU : x ∈ U)
    (r : R.obj (op U)) (m : M.obj (op U)) (p : P.obj (op U)) :
    R.germ U x hxU r • germTmul M P x hxU hxU m p
      = germTmul M P x hxU hxU (r • m) p := by
  rw [germTmul_self, germTmul_self,
    ← germ_smul (MonoidalCategory.tensorObj (C := PresheafOfModules.{u} _) M P) x U hxU r
      (m ⊗ₜ p)]
  -- what remains is `r • (m ⊗ₜ p) = (r • m) ⊗ₜ p`, definitional for the `ModuleCat` tensor
  congr 1

/-- `Rₓ`-linearity of `germTmul` in the `M` slot, with the scalar, the section of `M` and the
section of `P` over three different neighbourhoods. -/
lemma germ_smul_germTmul {W U V : Opens X} (hxW : x ∈ W) (hxU : x ∈ U) (hxV : x ∈ V)
    (r : R.obj (op W)) (m : M.obj (op U)) (p : P.obj (op V)) :
    R.germ W x hxW r • germTmul M P x hxU hxV m p
      = germTmul M P x (show x ∈ W ⊓ U from ⟨hxW, hxU⟩) hxV
          ((R ⋙ forget₂ CommRingCat RingCat).map
              (homOfLE (inf_le_left : W ⊓ U ≤ W)).op r •
            resSec (N := M) (inf_le_right : W ⊓ U ≤ U) m) p := by
  have hZ : x ∈ (W ⊓ U) ⊓ V := ⟨⟨hxW, hxU⟩, hxV⟩
  -- bring the right-hand side down to the common neighbourhood
  rw [germTmul_res_left M P x (inf_le_left : (W ⊓ U) ⊓ V ≤ W ⊓ U) hZ hxV,
    germTmul_res_right M P x (inf_le_right : (W ⊓ U) ⊓ V ≤ V) hZ hZ]
  -- and the left-hand side too
  rw [germTmul_res_left M P x
      (le_trans (inf_le_left : (W ⊓ U) ⊓ V ≤ W ⊓ U) inf_le_right) hZ hxV,
    germTmul_res_right M P x (inf_le_right : (W ⊓ U) ⊓ V ≤ V) hZ hZ,
    ← TopCat.Presheaf.germ_res_apply R
      (homOfLE (le_trans (inf_le_left : (W ⊓ U) ⊓ V ≤ W ⊓ U) inf_le_left)) x hZ r,
    germ_smul_germTmul_self M P x hZ]
  congr 2
  unfold resSec
  erw [M.map_smul]
  congr 1
  · -- the two composites of restrictions along `Opens` inclusions agree, hom-sets being
    -- subsingletons; the spellings differ only by `R` versus `R ⋙ forget₂`
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    congr 2
  · -- `M.map` is semilinear, so `Functor.map_comp` only applies after passing to `M.presheaf`
    show M.presheaf.map _ m = M.presheaf.map _ (M.presheaf.map _ m)
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl

/-- `germTmul` is additive in the `M` slot, over a fixed pair of neighbourhoods. -/
lemma germTmul_add_left {U V : Opens X} (hxU : x ∈ U) (hxV : x ∈ V)
    (m m' : M.obj (op U)) (p : P.obj (op V)) :
    germTmul M P x hxU hxV (m + m') p
      = germTmul M P x hxU hxV m p + germTmul M P x hxU hxV m' p := by
  unfold germTmul
  have h : M.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op (m + m')
      = M.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op m
        + M.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op m' := map_add _ _ _
  have h2 := TensorProduct.add_tmul
    (R := ↑((R ⋙ forget₂ CommRingCat RingCat).obj (op (U ⊓ V))))
    (M.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op m)
    (M.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op m')
    (P.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op p)
  rw [h]
  exact (congrArg _ h2).trans (map_add _ _ _)

/-- `germTmul` is additive in the `P` slot, over a fixed pair of neighbourhoods. -/
lemma germTmul_add_right {U V : Opens X} (hxU : x ∈ U) (hxV : x ∈ V)
    (m : M.obj (op U)) (p p' : P.obj (op V)) :
    germTmul M P x hxU hxV m (p + p')
      = germTmul M P x hxU hxV m p + germTmul M P x hxU hxV m p' := by
  unfold germTmul
  have h : P.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op (p + p')
      = P.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op p
        + P.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op p' := map_add _ _ _
  have h2 := TensorProduct.tmul_add
    (R := ↑((R ⋙ forget₂ CommRingCat RingCat).obj (op (U ⊓ V))))
    (M.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op m)
    (P.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op p)
    (P.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op p')
  rw [h]
  exact (congrArg _ h2).trans (map_add _ _ _)

/-- For a fixed section `m` of `M` over `U`, the germs `m ⊗ p` form a cocone on the `P`-diagram:
the legs are additive by `germTmul_add_right` and natural by `germTmul_res_right`. -/
noncomputable def germTmulCoconeRight (U : Opens X) (hxU : x ∈ U) (m : M.obj (op U)) :
    Limits.Cocone ((OpenNhds.inclusion x).op ⋙ P.presheaf) where
  pt := AddCommGrpCat.of (ToType (TopCat.Presheaf.stalk
    (MonoidalCategory.tensorObj (C := PresheafOfModules.{u} _) M P).presheaf x))
  ι :=
    { app := fun V => AddCommGrpCat.ofHom
        (AddMonoidHom.mk' (fun p => germTmul M P x hxU V.unop.2 m p)
          (fun p p' => germTmul_add_right M P x hxU V.unop.2 m p p'))
      naturality := fun V V' i => by
        ext p
        exact (germTmul_res_right M P x
          (show (V'.unop.1 : Opens X) ≤ V.unop.1 from i.unop.down.down)
          hxU V'.unop.2 m p).symm }

/-- Tensoring a fixed section `m` of `M` against the stalk of `P`. -/
noncomputable def germTmulRight (U : Opens X) (hxU : x ∈ U) (m : M.obj (op U)) :
    TopCat.Presheaf.stalk P.presheaf x ⟶
      AddCommGrpCat.of (ToType (TopCat.Presheaf.stalk
        (MonoidalCategory.tensorObj (C := PresheafOfModules.{u} _) M P).presheaf x)) :=
  Limits.colimit.desc _ (germTmulCoconeRight M P x U hxU m)

/-- The defining computation rule for `germTmulRight`, which is a `colimit.desc` and so is
pinned down entirely by its values on germs. Every later proof about it goes through here. -/
@[simp]
lemma germTmulRight_germ (U V : Opens X) (hxU : x ∈ U) (hxV : x ∈ V)
    (m : M.obj (op U)) (p : P.obj (op V)) :
    germTmulRight M P x U hxU m (TopCat.Presheaf.germ P.presheaf V x hxV p)
      = germTmul M P x hxU hxV m p :=
  ConcreteCategory.congr_hom
    (Limits.colimit.ι_desc (germTmulCoconeRight M P x U hxU m) (op ⟨V, hxV⟩)) p

/-- `germTmulRight` is unchanged by shrinking the neighbourhood of `m`: the naturality the outer
cocone needs, now at the level of the induced morphism rather than of germs. -/
lemma germTmulRight_res_left {U U' : Opens X} (h : U' ≤ U) (hxU' : x ∈ U')
    (m : M.obj (op U)) :
    germTmulRight M P x U (h hxU') m = germTmulRight M P x U' hxU' (resSec h m) := by
  refine TopCat.Presheaf.stalk_hom_ext P.presheaf (fun V hxV => ?_)
  ext p
  show germTmulRight M P x U (h hxU') m
      (TopCat.Presheaf.germ P.presheaf V x hxV p) = _
  show _ = germTmulRight M P x U' hxU' (resSec h m)
      (TopCat.Presheaf.germ P.presheaf V x hxV p)
  rw [germTmulRight_germ, germTmulRight_germ]
  exact germTmul_res_left M P x h hxU' hxV m p

/-- `germTmulRight` is additive in `m`, pointwise on the stalk of `P`. -/
lemma germTmulRight_add (U : Opens X) (hxU : x ∈ U) (m m' : M.obj (op U))
    (ξ : ToType (TopCat.Presheaf.stalk P.presheaf x)) :
    germTmulRight M P x U hxU (m + m') ξ
      = germTmulRight M P x U hxU m ξ + germTmulRight M P x U hxU m' ξ := by
  obtain ⟨V, hxV, p, rfl⟩ := TopCat.Presheaf.exists_germ_eq P.presheaf ξ
  rw [germTmulRight_germ, germTmulRight_germ, germTmulRight_germ]
  exact germTmul_add_left M P x hxU hxV m m' p

/-- The outer cocone, in the `M` variable: legs additive by `germTmulRight_add`, natural by
`germTmulRight_res_left`. Its point is the additive maps out of the stalk of `P`. -/
noncomputable def germTmulCoconeLeft :
    Limits.Cocone ((OpenNhds.inclusion x).op ⋙ M.presheaf) where
  pt := AddCommGrpCat.of (ToType (TopCat.Presheaf.stalk P.presheaf x) →+
    ToType (TopCat.Presheaf.stalk
      (MonoidalCategory.tensorObj (C := PresheafOfModules.{u} _) M P).presheaf x))
  ι :=
    { app := fun U => AddCommGrpCat.ofHom (AddMonoidHom.mk'
        (fun m => (germTmulRight M P x U.unop.1 U.unop.2 m).hom)
        (fun m m' => AddMonoidHom.ext fun ξ =>
          germTmulRight_add M P x U.unop.1 U.unop.2 m m' ξ))
      naturality := fun U U' i => by
        ext m
        exact congrArg AddCommGrpCat.Hom.hom
          (germTmulRight_res_left M P x
            (show (U'.unop.1 : Opens X) ≤ U.unop.1 from i.unop.down.down)
            U'.unop.2 m).symm }

/-- The biadditive map `Mₓ → Pₓ → (M ⊗ P)ₓ` underlying the backward comparison. -/
noncomputable def germTmulBiadd :
    TopCat.Presheaf.stalk M.presheaf x ⟶
      AddCommGrpCat.of (ToType (TopCat.Presheaf.stalk P.presheaf x) →+
        ToType (TopCat.Presheaf.stalk
          (MonoidalCategory.tensorObj (C := PresheafOfModules.{u} _) M P).presheaf x)) :=
  Limits.colimit.desc _ (germTmulCoconeLeft M P x)

/-- Both colimit stages unwound at once. Since every element of a stalk is a germ, this and
additivity determine `germTmulBiadd` completely — it is the only handle the bilinearity and
inverse proofs use. -/
@[simp]
lemma germTmulBiadd_germ (U V : Opens X) (hxU : x ∈ U) (hxV : x ∈ V)
    (m : M.obj (op U)) (p : P.obj (op V)) :
    germTmulBiadd M P x (TopCat.Presheaf.germ M.presheaf U x hxU m)
        (TopCat.Presheaf.germ P.presheaf V x hxV p)
      = germTmul M P x hxU hxV m p := by
  have h : germTmulBiadd M P x (TopCat.Presheaf.germ M.presheaf U x hxU m)
      = (germTmulRight M P x U hxU m).hom :=
    ConcreteCategory.congr_hom
      (Limits.colimit.ι_desc (germTmulCoconeLeft M P x) (op ⟨U, hxU⟩)) m
  rw [h]
  exact germTmulRight_germ M P x U V hxU hxV m p

/-- Right-slot analogue of `germ_smul_germTmul_self`: over a single neighbourhood the scalar
may be moved into the `P` factor. Unlike the `M` slot this is not definitional — it is
`TensorProduct.tmul_smul`, and so uses commutativity of `R(U)`. -/
lemma germ_smul_germTmul_self_right {U : Opens X} (hxU : x ∈ U)
    (r : R.obj (op U)) (m : M.obj (op U)) (p : P.obj (op U)) :
    R.germ U x hxU r • germTmul M P x hxU hxU m p
      = germTmul M P x hxU hxU m (r • p) := by
  rw [germTmul_self, germTmul_self,
    ← germ_smul (MonoidalCategory.tensorObj (C := PresheafOfModules.{u} _) M P) x U hxU r
      (m ⊗ₜ p)]
  congr 1
  exact (TensorProduct.tmul_smul (R := ↑(R.obj (op U))) r m p).symm

/-- `germTmulBiadd` is `Rₓ`-linear in the `M` slot. -/
lemma germTmulBiadd_smul_left (r : R.stalk x)
    (ξ : ToType (TopCat.Presheaf.stalk M.presheaf x))
    (η : ToType (TopCat.Presheaf.stalk P.presheaf x)) :
    germTmulBiadd M P x (r • ξ) η = r • germTmulBiadd M P x ξ η := by
  obtain ⟨W, hxW, r₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq R r
  obtain ⟨U, hUW, hxU, m, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq M.presheaf ξ hxW
  obtain ⟨V, hVU, hxV, p, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq P.presheaf η hxU
  rw [← TopCat.Presheaf.germ_res_apply R (homOfLE (hVU.trans hUW)) x hxV r₀,
    ← TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE hVU) x hxV m,
    ← germ_smul M x V hxV, germTmulBiadd_germ, germTmulBiadd_germ,
    germ_smul_germTmul_self]

/-- `germTmulBiadd` is `Rₓ`-linear in the `P` slot. -/
lemma germTmulBiadd_smul_right (r : R.stalk x)
    (ξ : ToType (TopCat.Presheaf.stalk M.presheaf x))
    (η : ToType (TopCat.Presheaf.stalk P.presheaf x)) :
    germTmulBiadd M P x ξ (r • η) = r • germTmulBiadd M P x ξ η := by
  obtain ⟨W, hxW, r₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq R r
  obtain ⟨U, hUW, hxU, p, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq P.presheaf η hxW
  obtain ⟨V, hVU, hxV, m, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq M.presheaf ξ hxU
  rw [← TopCat.Presheaf.germ_res_apply R (homOfLE (hVU.trans hUW)) x hxV r₀,
    ← TopCat.Presheaf.germ_res_apply P.presheaf (homOfLE hVU) x hxV p,
    ← germ_smul P x V hxV, germTmulBiadd_germ, germTmulBiadd_germ,
    germ_smul_germTmul_self_right]

/-- `germTmulBiadd` is additive in the `M` slot, at the level of stalks. -/
lemma germTmulBiadd_add_left (ξ ξ' : ToType (TopCat.Presheaf.stalk M.presheaf x))
    (η : ToType (TopCat.Presheaf.stalk P.presheaf x)) :
    germTmulBiadd M P x (ξ + ξ') η
      = germTmulBiadd M P x ξ η + germTmulBiadd M P x ξ' η := by
  have h : germTmulBiadd M P x (ξ + ξ')
      = germTmulBiadd M P x ξ + germTmulBiadd M P x ξ' := map_add _ _ _
  exact congrArg (fun f : ToType (TopCat.Presheaf.stalk P.presheaf x) →+ _ => f η) h

/-- The `Rₓ`-bilinear map `Mₓ → Pₓ → (M ⊗ P)ₓ`. -/
noncomputable def germTmulBilin :
    ToType (TopCat.Presheaf.stalk M.presheaf x) →ₗ[R.stalk x]
      ToType (TopCat.Presheaf.stalk P.presheaf x) →ₗ[R.stalk x]
        ToType (TopCat.Presheaf.stalk
          (MonoidalCategory.tensorObj (C := PresheafOfModules.{u} _) M P).presheaf x) :=
  LinearMap.mk₂ (R.stalk x) (fun ξ η => germTmulBiadd M P x ξ η)
    (fun ξ ξ' η => germTmulBiadd_add_left M P x ξ ξ' η)
    (fun r ξ η => germTmulBiadd_smul_left M P x r ξ η)
    (fun _ _ _ => map_add _ _ _)
    (fun r ξ η => germTmulBiadd_smul_right M P x r ξ η)

/-- The backward comparison `Mₓ ⊗[Rₓ] Pₓ → (M ⊗ P)ₓ`. -/
noncomputable def stalkTensorBackward :
    StalkTensor M P x →ₗ[R.stalk x]
      ToType (TopCat.Presheaf.stalk
        (MonoidalCategory.tensorObj (C := PresheafOfModules.{u} _) M P).presheaf x) :=
  TensorProduct.lift (germTmulBilin M P x)

/-- The backward map computes on a pure tensor of stalk elements. -/
@[simp]
lemma stalkTensorBackward_tmul (ξ : ToType (TopCat.Presheaf.stalk M.presheaf x))
    (η : ToType (TopCat.Presheaf.stalk P.presheaf x)) :
    stalkTensorBackward M P x (ξ ⊗ₜ η) = germTmulBiadd M P x ξ η := rfl

/-- The backward map sends a pure tensor of germs to the germ of the pure tensor,
taken over the intersection of the two neighbourhoods. -/
@[simp]
lemma stalkTensorBackward_germ_tmul_germ (U V : Opens X) (hxU : x ∈ U) (hxV : x ∈ V)
    (m : M.obj (op U)) (p : P.obj (op V)) :
    stalkTensorBackward M P x
        (TopCat.Presheaf.germ M.presheaf U x hxU m ⊗ₜ
          TopCat.Presheaf.germ P.presheaf V x hxV p)
      = germTmul M P x hxU hxV m p :=
  germTmulBiadd_germ M P x U V hxU hxV m p

/-- The leg of the forward cocone at a neighbourhood `U` of `x`: the map
`(M ⊗ P)(U) → Mₓ ⊗ Pₓ` sending `m ⊗ p` to `germ m ⊗ germ p`. -/
noncomputable def stalkTensorLeg (U : Opens X) (hx : x ∈ U) :
    (MonoidalCategory.tensorObj (C := PresheafOfModules.{u} _) M P).presheaf.obj (op U) ⟶
      AddCommGrpCat.of (StalkTensor M P x) :=
  AddCommGrpCat.ofHom
    (letI := stalkTensorModuleAt M P x U hx;
      (TensorProduct.lift (stalkTensorBilin M P x U hx)).toAddMonoidHom)

/-- The forward leg computes on a pure tensor of sections. -/
@[simp]
lemma stalkTensorLeg_tmul (U : Opens X) (hx : x ∈ U)
    (m : M.obj (op U)) (p : P.obj (op U)) :
    stalkTensorLeg M P x U hx (m ⊗ₜ p)
      = TopCat.Presheaf.germ M.presheaf U x hx m ⊗ₜ
        TopCat.Presheaf.germ P.presheaf U x hx p := rfl

/-- The forward legs are compatible with restriction: this is the naturality the cocone needs. -/
lemma stalkTensorLeg_res {U V : Opens X} (h : V ≤ U) (hxV : x ∈ V)
    (z : (MonoidalCategory.tensorObj (C := PresheafOfModules.{u} _) M P).presheaf.obj (op U)) :
    stalkTensorLeg M P x V hxV
        ((MonoidalCategory.tensorObj (C := PresheafOfModules.{u} _) M P).presheaf.map
          (homOfLE h).op z)
      = stalkTensorLeg M P x U (h hxV) z := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · exact ((congrArg _ (map_zero _)).trans (map_zero _)).trans (map_zero _).symm
  · intro m p
    show TopCat.Presheaf.germ M.presheaf V x hxV (M.presheaf.map (homOfLE h).op m) ⊗ₜ
        TopCat.Presheaf.germ P.presheaf V x hxV (P.presheaf.map (homOfLE h).op p)
      = TopCat.Presheaf.germ M.presheaf U x (h hxV) m ⊗ₜ
        TopCat.Presheaf.germ P.presheaf U x (h hxV) p
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
  · intro a b ha hb
    have e : (MonoidalCategory.tensorObj (C := PresheafOfModules.{u} _) M P).presheaf.map
        (homOfLE h).op (a + b)
        = (MonoidalCategory.tensorObj (C := PresheafOfModules.{u} _) M P).presheaf.map
            (homOfLE h).op a
          + (MonoidalCategory.tensorObj (C := PresheafOfModules.{u} _) M P).presheaf.map
            (homOfLE h).op b := map_add _ _ _
    rw [e]
    exact (map_add _ _ _).trans (((congrArg₂ (· + ·) ha hb)).trans (map_add _ _ _).symm)

/-- The cocone on the `(M ⊗ P)`-diagram whose legs are `stalkTensorLeg`. -/
noncomputable def stalkTensorForwardCocone :
    Limits.Cocone ((OpenNhds.inclusion x).op ⋙
      (MonoidalCategory.tensorObj (C := PresheafOfModules.{u} _) M P).presheaf) where
  pt := AddCommGrpCat.of (StalkTensor M P x)
  ι :=
    { app := fun U => stalkTensorLeg M P x U.unop.1 U.unop.2
      naturality := fun U U' i => by
        ext z
        exact stalkTensorLeg_res M P x
          (show (U'.unop.1 : Opens X) ≤ U.unop.1 from i.unop.down.down) U'.unop.2 z }

/-- The forward comparison `(M ⊗ P)ₓ → Mₓ ⊗[Rₓ] Pₓ`. -/
noncomputable def stalkTensorForward :
    TopCat.Presheaf.stalk
        (MonoidalCategory.tensorObj (C := PresheafOfModules.{u} _) M P).presheaf x ⟶
      AddCommGrpCat.of (StalkTensor M P x) :=
  Limits.colimit.desc _ (stalkTensorForwardCocone M P x)

/-- The forward map computes on a germ, by the leg at that neighbourhood. -/
@[simp]
lemma stalkTensorForward_germ (U : Opens X) (hxU : x ∈ U)
    (z : (MonoidalCategory.tensorObj (C := PresheafOfModules.{u} _) M P).presheaf.obj (op U)) :
    stalkTensorForward M P x
        (TopCat.Presheaf.germ
          (MonoidalCategory.tensorObj (C := PresheafOfModules.{u} _) M P).presheaf U x hxU z)
      = stalkTensorLeg M P x U hxU z :=
  ConcreteCategory.congr_hom
    (Limits.colimit.ι_desc (stalkTensorForwardCocone M P x) (op ⟨U, hxU⟩)) z

/-- The forward map computes on the germs of pure tensors: this is the exact converse of
`stalkTensorBackward_germ_tmul_germ`. -/
@[simp]
lemma stalkTensorForward_germTmul {U V : Opens X} (hxU : x ∈ U) (hxV : x ∈ V)
    (m : M.obj (op U)) (p : P.obj (op V)) :
    stalkTensorForward M P x (germTmul M P x hxU hxV m p)
      = TopCat.Presheaf.germ M.presheaf U x hxU m ⊗ₜ
        TopCat.Presheaf.germ P.presheaf V x hxV p := by
  unfold germTmul
  rw [stalkTensorForward_germ]
  show TopCat.Presheaf.germ M.presheaf (U ⊓ V) x ⟨hxU, hxV⟩
        (M.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op m) ⊗ₜ
      TopCat.Presheaf.germ P.presheaf (U ⊓ V) x ⟨hxU, hxV⟩
        (P.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op p)
    = TopCat.Presheaf.germ M.presheaf U x hxU m ⊗ₜ
      TopCat.Presheaf.germ P.presheaf V x hxV p
  rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]

/-- The forward map is a retraction of the backward map. -/
lemma stalkTensorForward_backward (t : StalkTensor M P x) :
    stalkTensorForward M P x (stalkTensorBackward M P x t) = t := by
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · exact (congrArg _ (map_zero _)).trans (map_zero _)
  · intro ξ η
    obtain ⟨U, hxU, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf ξ
    obtain ⟨V, hxV, p, rfl⟩ := TopCat.Presheaf.exists_germ_eq P.presheaf η
    rw [stalkTensorBackward_germ_tmul_germ, stalkTensorForward_germTmul]
  · intro a b ha hb
    rw [map_add]
    have e : stalkTensorForward M P x
          (stalkTensorBackward M P x a + stalkTensorBackward M P x b)
        = stalkTensorForward M P x (stalkTensorBackward M P x a)
          + stalkTensorForward M P x (stalkTensorBackward M P x b) := map_add _ _ _
    rw [e, ha, hb]

/-- The backward map is a retraction of the forward map. -/
lemma stalkTensorBackward_forward
    (s : ToType (TopCat.Presheaf.stalk
      (MonoidalCategory.tensorObj (C := PresheafOfModules.{u} _) M P).presheaf x)) :
    stalkTensorBackward M P x (stalkTensorForward M P x s) = s := by
  obtain ⟨U, hxU, z, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (MonoidalCategory.tensorObj (C := PresheafOfModules.{u} _) M P).presheaf s
  rw [stalkTensorForward_germ]
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · exact ((congrArg _ (map_zero _)).trans (map_zero _)).trans (map_zero _).symm
  · intro m p
    show stalkTensorBackward M P x
        (TopCat.Presheaf.germ M.presheaf U x hxU m ⊗ₜ
          TopCat.Presheaf.germ P.presheaf U x hxU p) = _
    rw [stalkTensorBackward_germ_tmul_germ, germTmul_self]
  · intro a b ha hb
    have el : stalkTensorLeg M P x U hxU (a + b)
        = stalkTensorLeg M P x U hxU a + stalkTensorLeg M P x U hxU b := map_add _ _ _
    have eg : TopCat.Presheaf.germ
          (MonoidalCategory.tensorObj (C := PresheafOfModules.{u} _) M P).presheaf U x hxU (a + b)
        = TopCat.Presheaf.germ
            (MonoidalCategory.tensorObj (C := PresheafOfModules.{u} _) M P).presheaf U x hxU a
          + TopCat.Presheaf.germ
            (MonoidalCategory.tensorObj (C := PresheafOfModules.{u} _) M P).presheaf U x hxU b :=
      map_add _ _ _
    rw [el, eg, map_add, ha, hb]

/-- **The stalk of a tensor product of presheaves of modules is the tensor product of the
stalks**, over the stalk of the ring: `(M ⊗ P)ₓ ≅ Mₓ ⊗[Rₓ] Pₓ`. -/
noncomputable def stalkTensorEquiv :
    StalkTensor M P x ≃ₗ[R.stalk x]
      ToType (TopCat.Presheaf.stalk
        (MonoidalCategory.tensorObj (C := PresheafOfModules.{u} _) M P).presheaf x) :=
  { stalkTensorBackward M P x with
    invFun := stalkTensorForward M P x
    left_inv := stalkTensorForward_backward M P x
    right_inv := stalkTensorBackward_forward M P x }

/-- `stalkTensorEquiv` computes on a pure tensor of germs. -/
@[simp]
lemma stalkTensorEquiv_germ_tmul_germ (U V : Opens X) (hxU : x ∈ U) (hxV : x ∈ V)
    (m : M.obj (op U)) (p : P.obj (op V)) :
    stalkTensorEquiv M P x
        (TopCat.Presheaf.germ M.presheaf U x hxU m ⊗ₜ
          TopCat.Presheaf.germ P.presheaf V x hxV p)
      = germTmul M P x hxU hxV m p :=
  germTmulBiadd_germ M P x U V hxU hxV m p

/-- The inverse of `stalkTensorEquiv` computes on a germ. -/
@[simp]
lemma stalkTensorEquiv_symm_germ (U : Opens X) (hxU : x ∈ U)
    (z : (MonoidalCategory.tensorObj (C := PresheafOfModules.{u} _) M P).presheaf.obj (op U)) :
    (stalkTensorEquiv M P x).symm
        (TopCat.Presheaf.germ
          (MonoidalCategory.tensorObj (C := PresheafOfModules.{u} _) M P).presheaf U x hxU z)
      = stalkTensorLeg M P x U hxU z :=
  stalkTensorForward_germ M P x U hxU z

section StalkMap

variable {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)} (g : M ⟶ N) (x : X)

/-- The stalk map of a morphism of presheaves of modules, as a morphism of abelian groups. -/
noncomputable abbrev stalkMapAdd :
    TopCat.Presheaf.stalk M.presheaf x ⟶ TopCat.Presheaf.stalk N.presheaf x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ((PresheafOfModules.toPresheaf _).map g)

/-- The stalk map is computed by applying the morphism to a representing section: this is
`TopCat.Presheaf.stalkFunctor_map_germ_apply`, restated at the spelling
`PresheafOfModules` uses so that `rw` can see it. -/
lemma stalkMapAdd_germ (U : Opens X) (hxU : x ∈ U) (m : M.obj (op U)) :
    stalkMapAdd g x (TopCat.Presheaf.germ M.presheaf U x hxU m)
      = TopCat.Presheaf.germ N.presheaf U x hxU (g.app (op U) m) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
    ((PresheafOfModules.toPresheaf _).map g) m

/-- The stalk map of a morphism of presheaves of modules is `Rₓ`-linear. -/
noncomputable def stalkMap :
    ToType (TopCat.Presheaf.stalk M.presheaf x) →ₗ[R.stalk x]
      ToType (TopCat.Presheaf.stalk N.presheaf x) where
  toFun := stalkMapAdd g x
  map_add' a b := map_add _ a b
  map_smul' r ξ := by
    obtain ⟨W, hxW, r₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq R r
    obtain ⟨U, hUW, hxU, m, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq M.presheaf ξ hxW
    show stalkMapAdd g x _ = (RingHom.id _ _) • stalkMapAdd g x _
    rw [RingHom.id_apply, ← TopCat.Presheaf.germ_res_apply R (homOfLE hUW) x hxU r₀,
      ← germ_smul M x U hxU, stalkMapAdd_germ, stalkMapAdd_germ, ← germ_smul N x U hxU]
    congr 1
    exact map_smul (g.app (op U)).hom _ _

/-- `stalkMap` has the same computation rule as `stalkMapAdd`; the two differ only in carrying
the `Rₓ`-module structure. -/
@[simp]
lemma stalkMap_germ (U : Opens X) (hxU : x ∈ U) (m : M.obj (op U)) :
    stalkMap g x (TopCat.Presheaf.germ M.presheaf U x hxU m)
      = TopCat.Presheaf.germ N.presheaf U x hxU (g.app (op U) m) :=
  stalkMapAdd_germ g x U hxU m

end StalkMap

section Whisker

variable (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
  {P Q : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)} (g : P ⟶ Q) (x : X)

/-- Whiskering acts on a pure tensor of sections in the obvious way. -/
lemma whiskerLeft_app_tmul (W : Opens X) (m : M.obj (op W)) (p : P.obj (op W)) :
    (M ◁ g).app (op W) (m ⊗ₜ p) = m ⊗ₜ g.app (op W) p := rfl

/-- **`stalkTensorEquiv` is natural in the second variable.** Under the identification of
`(M ⊗ P)ₓ` with `Mₓ ⊗ Pₓ`, the stalk map of `M ◁ g` is `Mₓ ⊗ (stalk map of g)`. This is what
turns a stalkwise iso into a stalkwise iso after whiskering. -/
lemma stalkMapAdd_whiskerLeft (t : StalkTensor M P x) :
    stalkMapAdd (M ◁ g) x (stalkTensorEquiv M P x t)
      = stalkTensorEquiv M Q x (LinearMap.lTensor _ (stalkMap g x) t) := by
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · exact ((congrArg _ (map_zero _)).trans (map_zero _)).trans
      ((congrArg _ (map_zero _)).trans (map_zero _)).symm
  · intro ξ η
    obtain ⟨U, hxU, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf ξ
    obtain ⟨V, hxV, p, rfl⟩ := TopCat.Presheaf.exists_germ_eq P.presheaf η
    rw [LinearMap.lTensor_tmul, stalkMap_germ, stalkTensorEquiv_germ_tmul_germ,
      stalkTensorEquiv_germ_tmul_germ]
    show stalkMapAdd (M ◁ g) x (TopCat.Presheaf.germ
        (MonoidalCategory.tensorObj (C := PresheafOfModules.{u} _) M P).presheaf
        (U ⊓ V) x ⟨hxU, hxV⟩
        (M.map (homOfLE inf_le_left).op m ⊗ₜ P.map (homOfLE inf_le_right).op p)) = _
    rw [stalkMapAdd_germ]
    show TopCat.Presheaf.germ
        (MonoidalCategory.tensorObj (C := PresheafOfModules.{u} _) M Q).presheaf
        (U ⊓ V) x ⟨hxU, hxV⟩
        (M.map (homOfLE inf_le_left).op m ⊗ₜ
          g.app (op (U ⊓ V)) (P.map (homOfLE inf_le_right).op p)) = _
    rw [naturality_apply]
    rfl
  · intro a b ha hb
    simp only [map_add, ha, hb]


/-- **Whiskering preserves stalkwise isomorphisms.** If `g` is a stalk isomorphism at `x`, so is
`M ◁ g` — for *any* `M`, with no flatness or local-freeness hypothesis. Tensoring is only right
exact in general, but tensoring with an isomorphism is an isomorphism, and `stalkTensorEquiv`
is what makes that visible on stalks. -/
lemma isIso_stalkMapAdd_whiskerLeft [IsIso (stalkMapAdd g x)] :
    IsIso (stalkMapAdd (M ◁ g) x) := by
  have hbij : Function.Bijective (stalkMap g x) :=
    (ConcreteCategory.isIso_iff_bijective (stalkMapAdd g x)).mp inferInstance
  let e : ToType (TopCat.Presheaf.stalk P.presheaf x) ≃ₗ[R.stalk x]
      ToType (TopCat.Presheaf.stalk Q.presheaf x) := LinearEquiv.ofBijective (stalkMap g x) hbij
  have hcomp : ⇑(stalkMapAdd (M ◁ g) x)
      = ⇑(stalkTensorEquiv M Q x) ∘ ⇑(LinearEquiv.lTensor _ e) ∘
        ⇑(stalkTensorEquiv M P x).symm := by
    funext s
    obtain ⟨t, rfl⟩ := (stalkTensorEquiv M P x).surjective s
    show stalkMapAdd (M ◁ g) x (stalkTensorEquiv M P x t) = _
    rw [stalkMapAdd_whiskerLeft]
    simp only [Function.comp_apply, LinearEquiv.symm_apply_apply]
    rfl
  rw [ConcreteCategory.isIso_iff_bijective, hcomp]
  exact (stalkTensorEquiv M Q x).bijective.comp
    ((LinearEquiv.lTensor _ e).bijective.comp (stalkTensorEquiv M P x).symm.bijective)

end Whisker

end PresheafOfModules
