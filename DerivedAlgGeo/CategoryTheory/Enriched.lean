/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
import DerivedAlgGeo.CategoryTheory.Monoidal
import DerivedAlgGeo.CategoryTheory.Enriched.DGCategory

/-!
# Enriched category theory

Categories with enriched morphism objects. An enriched category is defined
over a monoidal base category. The present subsystem also develops dg
categories, whose morphism objects are cochain complexes of abelian groups.

At the pinned Mathlib revision the required tensor product on the relevant
unbounded complexes is unavailable, so `DGCategory` is an equivalent explicit
encoding rather than an `EnrichedOrdinaryCategory` instance. Its mathematical
place in the dependency hierarchy is nevertheless the enriched layer.
-/
