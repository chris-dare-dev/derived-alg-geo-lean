---
name: Formalization issue
about: One unit of Lean work a loop run can take to a merged PR without asking anyone
title: '<CODE>.<n>: <the result, in words>'
labels: []
---

<!-- This body is the specification a loop run works from. Write WHAT and WHY,
never HOW: no review rounds, OpenSpec, manifests, controllers, CI platforms or
merge steps. The run-loop skill owns process, and process text goes stale.
Check every name, path and line at the pins below, and write "absent at the pin"
rather than guessing. Dependencies are GitHub issue numbers, never roadmap ids.
The run records progress in a loop-state comment, not in this body.
From the command line: copy this file, fill it in, delete the front matter
above this comment, and run
gh issue create --title '<title>' --body-file <file>
(gh issue create --body ignores templates). -->

## Outcome
<!-- The result in mathematical words, and its first consumer (issue, theorem or milestone). -->

**Kind:** complete (one PR, `Closes`) / progress (several PRs, each `Progress toward #<this>`)

## Source
- **Reference:** arXiv:XXXX.XXXXXvN (always versioned) / Stacks tag XXXX / author, title, edition
- **Location:** section; theorem, lemma, definition or equation numbers
- **Proof route:** the steps of the source proof, by number
- **Conventions:** indexing, signs, shifts, variance, and how the Lean statement matches them
- **Where to read it:** versioned URL, local copy, or "repository-internal"

## Verified API
Checked at the Mathlib revision pinned in `lake-manifest.json` (`<rev>`) and at `main@<sha>` on <date>.

| Name | Kind | Where (path:line) | Role here |
|---|---|---|---|
| `<Namespace.decl>` | def / theorem / abbrev / class | `Mathlib/<path>.lean:<line>` | <what this issue uses it for> |
| `<Name>` | none | absent at the pin | built here |

## Statements
<!-- Lean-shaped signatures. Mark each hypothesis "load-bearing: <witness that the
conclusion fails without it>" or "believed needed; may be weakened". A claim that
something fails needs a witness (an object, and why the conclusion fails for it),
not an upper bound. -->

## Placement
- **Tier:** 1, extends `<Mathlib API>` owned by `<Mathlib path>` / 2, new subject, precedent `<path>`
- **Files and namespaces:** new `DerivedAlgGeo/<...>/<File>.lean` in `<namespace>`
- **Shared files:** `<umbrella>`, `scripts/<Audit>/<Slice>.lean`, created by #n; this issue appends
- **Must not import or edit:** <...>

## Definition of done
<!-- Each line names a Lean declaration, a docstring or a gate. -->
- [ ] `<Namespace.decl>` in `<path>`: <statement in words>
- [ ] The docstring of `<decl>` records <counterexample / convention / non-claim>
- [ ] Every new public declaration is in `scripts/<Audit>/<Slice>.lean`, and `<umbrella>` imports the new file
- [ ] No `sorry`, `admit` or new axiom

## Non-goals and trust boundaries
- Not proved here: <...> (owned by #n)
- Not taken as a field, instance or hypothesis: <the result itself, existence, preservation, descent, algebraicity>

## Dependencies
- Blocked by #n: <what it supplies>. On a roadmap-owned milestone, open the
  matching `.claude/roadmap/*.yaml` PR as soon as you add the GitHub blocked-by
  link; CI's `roadmap` job fails every open PR until they agree.
- Independent of #m: <why, where it might look dependent>
- Consumed by #k

## Known traps
- <the most likely defect, e.g. an off-by-one between two indexings>
- <a route that looks right and fails, and why>
