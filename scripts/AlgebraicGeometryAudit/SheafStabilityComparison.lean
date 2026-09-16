/-
Comparison slice of the AlgebraicGeometry audit: the statements that mention both the Gieseker
order and the mu-slope (#903, #905). They are recorded apart from either theory because neither
theory is defined in terms of the other and neither imports the other; the source module is
`AlgebraicGeometry/Stability/Comparison.lean`, which MO1.08 (#1319) created for them.
-/
import DerivedAlgGeo.AlgebraicGeometry.Stability.Comparison

/-! ## Gieseker semistability implies weak mu-semistability (#903)

The slope is the normalized Hilbert coefficient one below the top, so the Gieseker order between
sheaves of positive multiplicity implies the slope inequality. ONE DIRECTION ONLY: nothing here
claims that mu-semistability implies Gieseker semistability, and nothing here relates the two
strict notions. The implication is FALSE without purity -- a nonzero multiplicity-zero subobject
has slope `⊤` and satisfies the Gieseker order vacuously -- so the purity conjunct of
`IsGiesekerSemistable` is doing visible work in the proof. -/

#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.giesekerSemistable_implies_muSemistable
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.topSlope_le_of_giesekerLE
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.weakSlopeData_slope_eq_normalizedCoefficient
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.weakSlopeData_topSlope_eq_normalizedCoefficient

/-! ## The one-step filtration of a Gieseker-semistable sheaf (#905)

A semistable object is its own Harder-Narasimhan filtration, so the implication above exhibits a
filtration directly and needs no `MuHNInput`. This is the only place the Gieseker order appears in
a Harder-Narasimhan statement; the existence theorem itself, in `SheafSlope.lean`, is about the
mu-slope and is not a Gieseker Harder-Narasimhan theorem. -/

#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.hnTrivialOfGiesekerSemistable
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.giesekerSemistable_implies_hn_trivial
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.giesekerSemistable_hn_trivial_n
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.giesekerSemistable_hn_trivial_muPlus
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.giesekerSemistable_hn_trivial_muMinus
