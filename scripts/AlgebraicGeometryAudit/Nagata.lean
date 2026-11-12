/-
Japanese, universally Japanese and Nagata rings and schemes (Stacks 032F, 032R, 033S), Stacks 00P8
for local subrings, and Lemmas 11.15 and 11.19, Definition 11.16 and Remark 11.17 of
arXiv:1902.08184v4. The ring-theoretic records come from `RingTheory/`; no stack, moduli or
stability module is an input.
-/
import DerivedAlgGeo.RingTheory.LocalRing
import DerivedAlgGeo.AlgebraicGeometry.Nagata

#print axioms LocalSubring.exists_le_ringKrullDim_eq_one

#print axioms IsJapanese
#print axioms IsJapanese.finite_integralClosure
#print axioms IsJapanese.finite_integralClosure_of_isFractionRing
#print axioms IsJapanese.of_isLocalization
#print axioms IsJapanese.of_ringEquiv
#print axioms IsJapanese.of_span_eq_top
#print axioms Field.isJapanese
#print axioms IsUniversallyJapanese
#print axioms IsUniversallyJapanese.isJapanese
#print axioms IsUniversallyJapanese.isJapanese_self
#print axioms IsUniversallyJapanese.of_essFiniteType
#print axioms IsUniversallyJapanese.isJapanese_of_essFiniteType
#print axioms IsUniversallyJapanese.of_span_eq_top
#print axioms IsUniversallyJapanese.of_charZero
#print axioms IsNagataRing
#print axioms IsNagataRing.isNoetherianRing
#print axioms IsNagataRing.isJapanese
#print axioms IsNagataRing.of_isUniversallyJapanese
#print axioms IsNagataRing.of_isLocalization
#print axioms IsNagataRing.localization
#print axioms IsNagataRing.of_span_eq_top
#print axioms exists_dvr_dominating_essFiniteType

#print axioms AlgebraicGeometry.EssentiallyLocallyOfFiniteType
#print axioms AlgebraicGeometry.EssentiallyOfFiniteType
#print axioms AlgebraicGeometry.EssentiallyOfFiniteType.essentiallyLocallyOfFiniteType
#print axioms AlgebraicGeometry.essentiallyOfFiniteType_iff_essentiallyLocallyOfFiniteType
#print axioms AlgebraicGeometry.essentiallyOfFiniteType_spec_map_comp
#print axioms AlgebraicGeometry.essentiallyOfFiniteType_spec_map_iff

#print axioms AlgebraicGeometry.Scheme.IsUniversallyJapanese
#print axioms AlgebraicGeometry.Scheme.IsUniversallyJapanese.isUniversallyJapanese
#print axioms AlgebraicGeometry.Scheme.IsNagata
#print axioms AlgebraicGeometry.Scheme.IsNagata.isNagataRing
#print axioms AlgebraicGeometry.Scheme.isUniversallyJapanese_of_affine_cover
#print axioms AlgebraicGeometry.Scheme.isNagata_of_affine_cover
#print axioms AlgebraicGeometry.Scheme.IsNagata.isLocallyNoetherian
#print axioms AlgebraicGeometry.Scheme.isNagata_of_isUniversallyJapanese
#print axioms AlgebraicGeometry.Scheme.IsUniversallyJapanese.of_locallyOfFiniteType
#print axioms AlgebraicGeometry.isUniversallyJapanese_Spec
#print axioms AlgebraicGeometry.exists_dvr_of_specializes
#print axioms AlgebraicGeometry.exists_valuativeCommSq_of_specializes
