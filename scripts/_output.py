#!/usr/bin/env python3
"""Console encoding for the gate scripts, and the check that they all use it.

WHY THIS EXISTS. On the self-hosted Windows runner `sys.stdout` is cp1252. A
gate that prints a non-ASCII character raises `UnicodeEncodeError` *inside its
own reporting path*, so it dies with a `charmap` traceback instead of the
finding it had already computed. That is the worst failure a reporting gate
has: the diagnosis is correct, and then thrown away in the act of displaying
it. #868 fixed it in `check_roadmap.py`, whose findings quote roadmap titles;
#869 is the observation that every other gate prints declaration names, and
Lean names routinely carry `δ`, `₁`, `₂`, `Γ`, `ω`, `χ`. It stopped being
hypothetical on 2026-09-11, when `check_audit_complete.py` crashed printing
`BilinearRiemannRochStatement.chi₂_eq` on PR #1158.

ONE IMPLEMENTATION. Every `scripts/check_*.py` (and `pr_queue.py`, which prints
pull-request titles) calls `force_utf8_output()` as the first statement of its
`if __name__ == "__main__":` block. Sixteen pasted copies would drift; this
module is the one copy, and `python3 scripts/_output.py` is the gate that keeps
every script on it -- structurally, by reading each script, and behaviourally,
by reproducing the crash in a subprocess and confirming the helper prevents it.

REPORTING ONLY. Nothing here touches a gate's verdict. A script that would have
failed still fails, with the same exit code; it now says why.
"""

from __future__ import annotations

import os
import re
import subprocess
import sys
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent

#: The scripts that must route their console output through this module.
#: `check_*.py` is every gate; `pr_queue.py` prints pull-request titles, which
#: carry the same characters.
CALLERS = sorted(SCRIPTS.glob("check_*.py")) + [SCRIPTS / "pr_queue.py"]

#: A declaration-name-shaped probe: Greek, a subscript, a superscript, an arrow.
PROBE = "Foo.δ.stepX₂.Hⁱ → Γ"


def force_utf8_output() -> None:
    """Make stdout and stderr able to carry the text the gates print.

    Every finding a gate prints may quote a Lean declaration name or a roadmap
    title, and those contain non-ASCII: subscripts, superscripts, Greek, arrows,
    dashes. On the self-hosted Windows runner `sys.stdout` defaults to cp1252,
    so printing one of those raises `UnicodeEncodeError` *inside* the reporting
    path, and the gate dies with a traceback instead of reporting the finding it
    had already made.

    `errors="replace"` rather than `strict`: a report that renders one character
    as `?` is still a report, and no name is worth losing a finding over.
    """
    for stream in (sys.stdout, sys.stderr):
        reconfigure = getattr(stream, "reconfigure", None)
        if reconfigure is None:  # not a TextIOWrapper; nothing to fix
            continue
        try:
            reconfigure(encoding="utf-8", errors="replace")
        except (ValueError, OSError):
            # Already detached, or a stream that refuses reconfiguration. The
            # gate is still worth running; only the rendering is at risk.
            pass


IMPORT_RE = re.compile(r"^from _output import force_utf8_output$", re.MULTILINE)
#: Either the first statement of the entry-point block, or -- for a flat script
#: with no such block, `check_pin.py` -- the module-level statement right after
#: the import.
CALL_RE = re.compile(
    r'^if __name__ == "__main__":\n[ \t]+force_utf8_output\(\)\n'
    r'|^from _output import force_utf8_output\n\nforce_utf8_output\(\)\n', re.MULTILINE)


def structural_findings() -> list[str]:
    """Every caller imports the helper and calls it first thing under `__main__`."""
    out = []
    for path in CALLERS:
        text = path.read_text(encoding="utf-8")
        rel = path.relative_to(SCRIPTS.parent).as_posix()
        if not IMPORT_RE.search(text):
            out.append(f"{rel}: does not import force_utf8_output from scripts/_output.py")
        if not CALL_RE.search(text):
            out.append(f"{rel}: force_utf8_output() is not the first statement of its "
                       f"`if __name__ == \"__main__\":` block (or, for a flat script, "
                       f"the statement right after its import)")
    return out


def run_probe(with_fix: bool) -> subprocess.CompletedProcess[bytes]:
    """Print the probe from a fresh interpreter whose console is forced to cp1252."""
    prelude = ("import sys; sys.path.insert(0, sys.argv[1]); "
               "from _output import force_utf8_output; force_utf8_output(); "
               if with_fix else "")
    code = f"{prelude}print({PROBE!r}); print({PROBE!r}, file=sys.stderr)"
    env = dict(os.environ, PYTHONIOENCODING="cp1252", PYTHONUTF8="0")
    return subprocess.run([sys.executable, "-c", "import sys\n" + code, str(SCRIPTS)],
                          capture_output=True, env=env, timeout=60)


def behavioural_findings() -> list[str]:
    out = []
    crash = run_probe(with_fix=False)
    if crash.returncode == 0 or b"UnicodeEncodeError" not in crash.stderr:
        out.append("the cp1252 crash did not reproduce without the helper; the check "
                   "below would be vacuous (has the interpreter stopped honouring "
                   "PYTHONIOENCODING?)")
    fixed = run_probe(with_fix=True)
    if fixed.returncode != 0:
        out.append("printing the probe still fails with force_utf8_output(): "
                   + fixed.stderr.decode("utf-8", "replace").strip().splitlines()[-1])
    else:
        want = PROBE.encode("utf-8")
        if want not in fixed.stdout or want not in fixed.stderr:
            out.append("force_utf8_output() ran, but the probe did not come out as "
                       "UTF-8 on both stdout and stderr")
    return out


def main() -> int:
    force_utf8_output()
    findings = structural_findings() + behavioural_findings()
    for f in findings:
        print(f"::error::{f}")
    if findings:
        return 1
    print(f"ok: {len(CALLERS)} scripts route console output through "
          f"scripts/_output.py, and the probe {PROBE!r} survives a cp1252 console")
    return 0


if __name__ == "__main__":
    sys.exit(main())
