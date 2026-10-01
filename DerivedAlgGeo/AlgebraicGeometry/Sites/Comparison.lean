/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import DerivedAlgGeo.AlgebraicGeometry.Sites.QuasiCompact

/-!
# Comparing the big Zariski, étale, fppf and fpqc sites

Mathlib defines `Scheme.zariskiTopology`, `Scheme.etaleTopology`,
`Scheme.fppfTopology` and `Scheme.fpqcTopology`, proves the fpqc topology
subcanonical, and derives the fppf case from it.  At the pin it records the
comparisons `zariskiTopology ≤ etaleTopology`,
`zariskiPrecoverage ≤ fppfPrecoverage` and `fppfTopology ≤ fpqcTopology`, but
not the étale-to-fppf comparison, so the étale site has no `Subcanonical`
instance and the Zariski-to-fppf comparison is available only at the
precoverage level.

This file supplies the missing edges of that square.  Every étale morphism is
smooth, hence flat and locally of finite presentation, so an étale covering
family is an fppf covering family; subcanonicity then descends along that
inequality by `GrothendieckTopology.Subcanonical.of_le`.  No new descent
theorem is proved here: the content is Mathlib's fpqc descent for
representables, transported along topology inequalities.

These are direct extensions of Mathlib's site API, stated about Mathlib's own
topologies.  Nothing here is about stacks, moduli, or algebraicity.

The fppf and étale precoverages also agree with their quasi-compact property precoverages:
flat morphisms locally of finite presentation, and étale morphisms, are open maps. The resulting
topology equalities extend Mathlib's `AlgebraicGeometry/Sites/Fpqc.lean` and
`AlgebraicGeometry/Sites/Etale.lean`, their respective upstream owners.
-/

namespace AlgebraicGeometry.Scheme

open CategoryTheory MorphismProperty

universe u

/-- The fppf precoverage already satisfies the quasi-compact covering condition. -/
lemma fppfPrecoverage_eq_propQCPrecoverage :
    fppfPrecoverage.{u} = propQCPrecoverage (@Flat ⊓ @LocallyOfFinitePresentation) :=
  precoverage_eq_propQCPrecoverage_of_isOpenMap fun _ _ f ⟨_, _⟩ ↦ f.isOpenMap

/-- The fppf topology is the quasi-compact topology for flat, locally finitely presented maps. -/
lemma fppfTopology_eq_propQCTopology :
    fppfTopology.{u} = propQCTopology (@Flat ⊓ @LocallyOfFinitePresentation) :=
  congrArg Precoverage.toGrothendieck fppfPrecoverage_eq_propQCPrecoverage

/-- The étale precoverage already satisfies the quasi-compact covering condition. -/
lemma etalePrecoverage_eq_propQCPrecoverage :
    etalePrecoverage.{u} = propQCPrecoverage @Etale :=
  precoverage_eq_propQCPrecoverage_of_isOpenMap fun _ _ f _ ↦ f.isOpenMap

/-- The étale topology is the quasi-compact topology for étale maps. -/
lemma etaleTopology_eq_propQCTopology :
    etaleTopology.{u} = propQCTopology @Etale :=
  congrArg Precoverage.toGrothendieck etalePrecoverage_eq_propQCPrecoverage

/-- Every étale covering family is an fppf covering family: an étale morphism
is smooth, hence flat and locally of finite presentation. -/
lemma etalePrecoverage_le_fppfPrecoverage :
    etalePrecoverage.{u} ≤ fppfPrecoverage.{u} :=
  precoverage_mono fun _ _ _ _ ↦ ⟨inferInstance, inferInstance⟩

/-- The étale topology is coarser than the fppf topology. -/
lemma etaleTopology_le_fppfTopology : etaleTopology.{u} ≤ fppfTopology.{u} :=
  Precoverage.toGrothendieck_mono etalePrecoverage_le_fppfPrecoverage

/-- The étale topology is coarser than the fpqc topology. -/
lemma etaleTopology_le_fpqcTopology : etaleTopology.{u} ≤ fpqcTopology.{u} :=
  le_trans etaleTopology_le_fppfTopology fppfTopology_le_fpqcTopology

/-- The big Zariski topology is coarser than the fppf topology.  Mathlib has
this comparison at the level of precoverages only. -/
lemma zariskiTopology_le_fppfTopology : zariskiTopology.{u} ≤ fppfTopology.{u} :=
  Precoverage.toGrothendieck_mono zariskiPrecoverage_le_fppfPrecoverage

/-- The étale site is subcanonical, because the fppf site is and the étale
topology is coarser.  This is Mathlib's fpqc descent theorem for
representables restricted along `etaleTopology_le_fppfTopology`; it is not a
new descent result. -/
instance subcanonical_etaleTopology : etaleTopology.{u}.Subcanonical :=
  .of_le etaleTopology_le_fppfTopology

end AlgebraicGeometry.Scheme
