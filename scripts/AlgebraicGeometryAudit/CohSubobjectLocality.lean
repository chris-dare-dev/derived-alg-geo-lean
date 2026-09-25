import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.SubobjectLocality

/-! Axiom audit and direct clients for coherent subobject locality. -/

#print axioms AlgebraicGeometry.Coh.subobject_le_iff_restrict_openCover
#print axioms AlgebraicGeometry.Coh.subobject_eq_iff_restrict_openCover

open CategoryTheory AlgebraicGeometry

universe u

variable {U : Scheme.{u}} [IsLocallyNoetherian U]
  (𝒰 : Scheme.OpenCover.{u} U) (E : Coh U) (P Q : Subobject E)

example : P ≤ Q ↔ ∀ i : 𝒰.I₀,
    Subobject.mapFunctor (Coh.restrict (𝒰.f i)) P ≤
      Subobject.mapFunctor (Coh.restrict (𝒰.f i)) Q :=
  Coh.subobject_le_iff_restrict_openCover 𝒰 E P Q

example : P = Q ↔ ∀ i : 𝒰.I₀,
    Subobject.mapFunctor (Coh.restrict (𝒰.f i)) P =
      Subobject.mapFunctor (Coh.restrict (𝒰.f i)) Q :=
  Coh.subobject_eq_iff_restrict_openCover 𝒰 E P Q

private def twoBasicOpenFamily {R : CommRingCat.{u}} (r s : R) :
    Bool → (Spec R).Opens :=
  fun b => cond b (PrimeSpectrum.basicOpen r) (PrimeSpectrum.basicOpen s)

private noncomputable def twoBasicOpenCover {R : CommRingCat.{u}} (r s : R) :
    Scheme.OpenCover ((⨆ b : Bool, twoBasicOpenFamily r s b).toScheme) :=
  Scheme.Opens.iSupOpenCover (twoBasicOpenFamily r s)

example {R : CommRingCat.{u}} (r s : R) :
    (⨆ b : Bool, twoBasicOpenFamily r s b) =
      PrimeSpectrum.basicOpen r ⊔ PrimeSpectrum.basicOpen s := by
  simp [twoBasicOpenFamily, iSup_bool_eq]
  rfl

-- These are two restrictions of existing global subobjects, not a gluing claim.
example {R : CommRingCat.{u}} [IsNoetherianRing R] (r s : R)
    (E : Coh ((⨆ b : Bool, twoBasicOpenFamily r s b).toScheme))
    (P Q : Subobject E) :
    P ≤ Q ↔ ∀ b : Bool,
      Subobject.mapFunctor (Coh.restrict ((twoBasicOpenCover r s).f b)) P ≤
        Subobject.mapFunctor (Coh.restrict ((twoBasicOpenCover r s).f b)) Q :=
  by
    let 𝒰 := twoBasicOpenCover r s
    change P ≤ Q ↔ ∀ b : 𝒰.I₀,
      Subobject.mapFunctor (Coh.restrict (𝒰.f b)) P ≤
        Subobject.mapFunctor (Coh.restrict (𝒰.f b)) Q
    exact Coh.subobject_le_iff_restrict_openCover 𝒰 E P Q
