/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/

import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.Functorial

/-! # The triangulated Grothendieck group

`K₀` of a triangulated category, its presentation by generators and
three-term relations, and its functoriality in triangulated functors.

Nothing here mentions a slicing, a phase, or a stability condition. These
modules lived under `StabilityCondition/Foundation/` for historical reasons,
which made every consumer of a Grothendieck group inherit the stability track
as a dependency; they are generic triangulated theory and now sit where the
subject hierarchy puts them.
-/
