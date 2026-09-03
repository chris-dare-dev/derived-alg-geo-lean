/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.Adjunction
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.AdjointAssembly
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.Autoequivalence
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.Convolution
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.ExceptionalExtension
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.ExceptionalInduction
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.GrothendieckGroup
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.Witness

/-! # Fourier--Mukai transforms

Kernel functors between triangulated categories, stated for an abstract
correspondence; the convolution of kernels as supplied data; kernel-presented
adjoints of a transform, also as supplied data, together with the ledger that
splits one such adjoint into the three constituent adjunctions plus a
projection-formula identification; and the induced maps on the triangulated
Grothendieck group.  No geometry, and no theorem asserting that a
functor is of this form or that it has an adjoint.

-/
