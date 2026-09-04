/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Topology.Sheaves.Cech.BasisComparison
import DerivedAlgGeo.Topology.Sheaves.Cech.Boundedness
import DerivedAlgGeo.Topology.Sheaves.Cech.FreeAbelianYonedaStalk
import DerivedAlgGeo.Topology.Sheaves.Cech.GlobalComparison
import DerivedAlgGeo.Topology.Sheaves.Cech.InjectiveAcyclic
import DerivedAlgGeo.Topology.Sheaves.Cech.InjectiveFlasque

/-!
# Čech cohomology of sheaves on a topological space

The topological half of the Čech theory: compact-open bases and the basis
comparison, finite-cover boundedness, stalks of the free abelian Yoneda sheaf,
global sections against the Čech zero term, and acyclicity of injective and
flasque sheaves. Every signature here mentions a topological space and its
opens; the site-level theory lives in
`CategoryTheory/Sites/SheafCohomology/Cech/`.
-/
