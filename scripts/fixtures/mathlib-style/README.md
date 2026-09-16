# Mathlib-style fixtures

Known-answer tests for `scripts/check_mathlib_style.py --self-test`. The layout
is `<code>/allowed/*.leansrc` and `<code>/forbidden/*.leansrc`, where `<code>`
is the lowercased finding code under test. Every `allowed` fixture must produce
no finding with that code and every `forbidden` fixture must produce at least
one, so an edit that silently stops rejecting something is caught here rather
than by the next regression.

Only the named code is asserted on. A fixture is therefore about exactly one
question and does not have to be a Mathlib-clean file in every other respect.

A fixture is Lean source text but deliberately **not** a `.lean` file. It must
reach neither `lake`, `lake exe lint-style`, the declaration sweep, nor the
checker's own `in_scope`, which excludes `scripts/` anyway.
`scripts/fixtures/layering` keeps its hypothetical modules out of the build the
same way, with `*.imports`.

## `conflict` — unresolved merge-conflict markers

Added after #1359 (issue #1315): a rebase left markers in two files, `git add
-A` staged them, and nothing local caught it. Every structural gate in
`scripts/` parses `import` lines and ignores the rest, so a conflicted file
passes all of them; the defect surfaced ~13 minutes into CI as
`unexpected token '<<<'; expected command`.

| Fixture | What it pins |
| --- | --- |
| `forbidden/RebaseLeftInImports` | the shape #1359 shipped: markers around an import block |
| `forbidden/Diff3BaseSection` | `\|\|\|\|\|\|\|`, the base section `merge.conflictStyle = diff3` writes |
| `forbidden/InsideModuleDocstring` | markers inside a `/-! ... -/` block, which `code_only` blanks — so the check must read raw lines |
| `allowed/SetextAndRules` | `=======` as a Markdown setext heading underline, and a longer rule of `=`, in a file with no anchor |
| `allowed/IndentedMarkerProse` | a docstring quoting all three markers, indented; the check is anchored to column 0 |

`=======` and `|||||||` are reported only when `<<<<<<<` or `>>>>>>>` also
appears at the start of a line somewhere in the same file — the condition git
guarantees whenever it writes either of them. The two `allowed` fixtures are
what keeps that guard honest.

Add a fixture whenever a check is added or a boundary moves; a check with no
forbidden fixture is a check nobody has seen fire.
