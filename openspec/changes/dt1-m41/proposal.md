# Proposal

## Why

Milestone #41 is the first place where the repository's derived tensor story
must move from interfaces and bounded-category infrastructure to an inhabited
construction. The issue text still names the former `Families/` ownership, so
this change freezes the current `DerivedCategory/Tensor/` owner and makes the
dependency from #929 to #928 explicit before implementation begins.

## What Changes

- Construct the left-derived tensor and tensor-acyclic-resolution interface in
  the canonical derived-category tensor owner for #929.
- Transfer the ambient unbounded exactness and coherent monoidal structure to
  the bounded coherent tier for #928.
- Keep the two issues as complete, sequential chunks with independent
  mathematical, repository-boundary, abstraction, and Mathlib-style reviews.
- Record repository inconsistencies and agent-friction observations in the
  checked-in loop plan so future work does not rediscover them.

## Capabilities

### New Capabilities

- `dt1-derived-tensor`: an inhabited left-derived tensor and coherent bounded
  derived tensor assembly for the supported repository interfaces.

### Modified Capabilities

- None.

## Impact

This change adds derived-category tensor declarations under the current
canonical ownership tree and updates its umbrella imports. It must not add
surrogate roots under `Families/`, edit the module-sheaf tensor implementation,
or weaken the no-sorry/no-axiom trust boundary.
