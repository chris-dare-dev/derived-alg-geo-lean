#!/usr/bin/env python3
"""Spec-driven controller for bounded, review-heavy repository loops.

This tool deliberately keeps the control plane small and explicit.  It validates
an immutable batch specification, performs a read-only preflight, records
independent reviews for frozen code chunks, and exposes remote mutations only
when an owner-controlled source authorizes them: a manifest merged to the
default branch, or that branch's standing authority file.  A manifest written on a
work branch travels with its PR and can narrow that authority, never widen it.

The controller is not a substitute for mathematical or repository review.  It
is the ledger and safety boundary that makes those reviews auditable and keeps
an unattended run from silently widening its scope.
"""

from __future__ import annotations

import argparse
import ast
import contextlib
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from datetime import datetime, timezone
from importlib.metadata import PackageNotFoundError, version as package_version
from pathlib import Path
from typing import Any, Iterable

import loop_recovery

try:
    from markdown_it import MarkdownIt
except ImportError as exc:  # pragma: no cover - covered by the documented dependency setup
    raise SystemExit(
        "markdown-it-py==3.0.0 is required; install scripts/requirements-loop.txt"
    ) from exc

try:
    MARKDOWN_IT_VERSION = package_version("markdown-it-py")
except PackageNotFoundError as exc:  # pragma: no cover - guarded by the import above
    raise SystemExit(
        "markdown-it-py==3.0.0 is required; install scripts/requirements-loop.txt"
    ) from exc
if MARKDOWN_IT_VERSION != "3.0.0":
    raise SystemExit(
        "loop ledger digests require markdown-it-py==3.0.0; "
        f"found {MARKDOWN_IT_VERSION}. Install scripts/requirements-loop.txt"
    )

COMMONMARK_PARSER = MarkdownIt("commonmark")

try:
    import yaml
except ImportError as exc:  # pragma: no cover - repository CI installs PyYAML
    raise SystemExit(f"PyYAML is required to run loop_engine.py: {exc}") from exc


try:
    from _output import force_utf8_output
except ImportError:  # pragma: no cover - direct invocation from another cwd
    def force_utf8_output() -> None:
        """Best-effort UTF-8 output fallback for standalone invocation."""


RUN_SCHEMA = "derived-alg-geo-lean.loop-run/v1"
MAX_ALLOWED_ROUNDS = 5
REQUIRED_ADVERSARIES = {
    "mathematics-adversary",
    "repository-boundary-adversary",
    "abstraction-adversary",
}
# The style reviewer is required by the spec delta but is not an adversarial
# lens; keep the sets distinct so the adversary requirement stays meaningful.
REQUIRED_REVIEWERS = REQUIRED_ADVERSARIES | {"mathlib-reviewer"}
ACTION_TO_MUTATION = {
    "comment": "comment_issue",
    "close": "close_issue",
    "push": "push_branch",
    "create-pr": "create_pr",
    "ready": "ready_pr",
    "follow-up": "create_issue",
    "approve": "approve_pr",
    "merge": "merge_pr",
}
MUTATION_KEYS = (
    "comment_issue",
    "close_issue",
    "push_branch",
    "create_pr",
    "ready_pr",
    "create_issue",
    "approve_pr",
    "merge_pr",
)
# Provider authority has owner-controlled sources only. The controller reads
# them from the repository's default branch through the provider API, never
# from a local ref, so a branch cannot grant itself an action; when the file is
# absent every action is denied. A manifest merged to that branch keeps its own
# reviewed grants. A manifest authored on a work branch can only narrow what
# this file grants.
STANDING_AUTHORITY_PATH = ".claude/loop-authority.yaml"
STANDING_AUTHORITY_SCHEMA = "derived-alg-geo-lean.loop-authority/v1"
# Manifests the owner reviewed and merged through a planning PR before plans
# moved into work PRs, by content digest. Their explicit grants and policies
# stand, except where the standing file explicitly revokes a grant. Every
# legacy-only privilege checks that the digest appears in the provider's
# default-branch copy of this controller, so a plan branch cannot activate a
# digest it just added locally. Merging a manifest later confers nothing: a
# work PR ships its own manifest, so "on the default branch" alone does not
# mean "reviewed by the owner".
LEGACY_REVIEWED_MANIFESTS = frozenset(
    {
        "7d7fde4cef8154044665c68b8aee9a063fd19d9dd3f4b8af9aebfc3c53146ebd",  # aut1-570-doc-hygiene
        "905e18f36e86c38742617c40cafdc910fa0cec5c4c935fcf665fbdfcd3c532c7",  # aut1-6-proper-discontinuity
        "fc164af7f47d5946dcdd6bc889f716f70d56d7e018e8b60aa0adc2ec3d663ae8",  # dt1-928-exact-bifunctor-restriction
        "48bf488268ca24e74f144146fd656eadc5b36279c0909f07a0b9fee051626421",  # dt1-m41
        "27454f1dc3ece91abd73439046c64c5764aca571e2a98c712323b9b15ad1620e",  # sf11-1-followup
        "cad0e7072175af28b924196c6241ba89d6d430a0d4bde1c4535c9bd9187c4a38",  # sf11-1-witnesses
        "7d6b7d5fd602e815a9e1ede2d7ebcb871119e47c11dde63dbd58ffed96580184",  # sf11-2-locality
        "87fe3f5891da1d935056d69282b3bc5b2b978a7704b6d8388e5c4e56d74bb38a",  # sf11-3-followup-v4-current
        "633e71a729be7aab37432313aace624d9e2765632748a495ffd92832f8267863",  # sf11-3-theorem53
        "161403899a361be7266a8f7b011928e90eea5525f0d37ed246a532ca2b8bd7d3",  # sf11-pilot
        "3e6decf24291404867b90849dd84e75ea273a018b312c070fe38e12a4d522e3f",  # sf8-5-affine-resolution-pullback
        "0a22b5bdf3d841aa6bda71126233fb12c5a97166a10c04117e3792374b66cabf",  # sf8-5-nonflat-derived-effect
        "a00cfa7a3006a8354033e9ccc87b620fb707ec92f395bf920d2125c213c24d1e",  # sf8-5-tor-witness-comparison
        "d3b27c3bcd91b0a332127dfb86cf24c9e3c8c187c425e8cb904937f680202322",  # sf8-5-affine-kprojective-scheme-comparison
        "69b451bac920101e28dff6c2f0c524f29f48146966ee9bdfc6a4e5ce0497606a",  # sf8-sf9-pilot
        "38d0d07e7f4e237af5e13c96149caa7e0b6926ddf6a051270a9c0fc8ae10e5fa",  # sf8-5-task12-kflat-pullback (#554)
        "315637cf2347791dce3abb9fdd1b57a6fcf83f63f5c0cb5ffab986ef9cb57419",  # rou1-919-rouquier-dimension (#1478)
        "b9c85b5909a68b5fc120d8be3073e5f391288b08beb4ef2319cd9ed3cfb6ff37",  # controller-publication-integrity-repair (#1482; zero provider grants)
    }
)
# A branch-authored run's frozen chunk may never touch its own authority, the
# code that gates or hosts it, or the instructions later agents follow; those
# change only through owner-reviewed PRs. Three things are covered:
# - agent configuration and instructions (all of `.claude/`, `.agents/`,
#   `.codex/`, `.mcp.json`, and every CLAUDE.md or AGENTS.md at any depth);
# - the gates, hooks and CI (`scripts/`, `.github/`);
# - the pins and the retired trust-guard surface.
# Two exceptions: the run's own manifest, and the audit and census records
# that new public declarations must extend.
PROTECTED_PATH_PREFIXES = (
    ".claude",
    ".agents",
    ".codex",
    ".mcp.json",
    ".github",
    "scripts",
    "exe",
    "registry",
    "lakefile.toml",
    "lakefile.lean",
    "lean-toolchain",
    "lake-manifest.json",
    "pins.json",
    "CLAUDE.local.md",
    "DerivedAlgGeoSweep.lean",
    # Other runs' OpenSpec contracts and the accepted specs; a run's own
    # change directory is exempt through its plan paths.
    "openspec",
    "docs/architecture/loop-recovery.md",
)
# Instructions at any depth, and git's own path-level behaviour: a
# `.gitattributes` can hide a Lean diff from the reviewers as "binary".
PROTECTED_BASENAMES = frozenset({"claude.md", "agents.md", ".gitattributes", ".gitmodules", ".gitignore"})
# Records a maths chunk must extend. The audit and census slices take new
# public declarations. RM-08 in the required `ci` check needs a closing PR to
# advance its roadmap entry. The gates that judge both stay protected.
UNPROTECTED_RECORD_RES = (
    re.compile(r"scripts/[A-Za-z]+(?:Audit|Census)(?:\.lean|/[A-Za-z0-9_./-]+\.lean)?"),
    re.compile(r"\.claude/roadmap(?:/[A-Za-z0-9_.-]+\.yaml)?"),
)
# Revalidation rounds re-review a passed change whose content moved (a rebase
# that had to resolve a conflict, say). They need the full panel but do not
# spend the critique/improve cap; this bounds how often a pass can be reopened.
MAX_REVALIDATION_ROUNDS = 2
# v1 hashes every artifact with universal-newline text reads. v2 adds the
# original regex-based task normalization. v3 uses CommonMark structure.
OPENSPEC_DIGEST_VERSION = 3
SUPPORTED_OPENSPEC_DIGEST_VERSIONS = frozenset({1, 2, 3})
LOG_ARTIFACT_NAMES = {"agent-observations.md"}
ISSUE_ID_RE = re.compile(r"^[a-z0-9]+(?:-[a-z0-9]+)*$")
BRANCH_RE = re.compile(r"^agent/[a-z0-9][a-z0-9._/-]*$")
TASK_LIST_CHECKBOX_RE = re.compile(r"^([ \t]*[-*+][ \t]+)\[[ xX]\]")
TASK_INLINE_CHECKBOX_RE = re.compile(r"^\[[ xX]\](?:[ \t\n]|$)")
# Preserve the semantics used by already-written v2 ledgers. Do not use this
# regex for new ledgers: CommonMark parsing distinguishes task boxes from links.
TASK_CHECKBOX_RE_V2 = re.compile(r"^(\s*[-*+] )\[[ xX]\]", re.MULTILINE)
MARKDOWN_LINE_END_RE = re.compile(r"\r\n|\r|\n")
MARKDOWN_BLOCK_CONTENT_TYPES = {
    "blockquote_open",
    "bullet_list_open",
    "code_block",
    "fence",
    "heading_open",
    "html_block",
    "hr",
    "ordered_list_open",
    "paragraph_open",
}
CLOSING_KEYWORD_RE = re.compile(r"\b(?:close[sd]?|fix(?:e[sd])?|resolve[sd]?)\s+#(\d+)\b", re.I)
# Common non-closing issue-link phrases accepted for progress PRs.
NON_CLOSING_REFERENCE_RE = re.compile(
    r"\b(?:ref(?:s)?|references?|related\s+to|part\s+of|progress\s+on|see)\s+#(\d+)\b",
    re.I,
)
SUCCESS_CONCLUSIONS = {"SUCCESS", "success", "PASSED", "passed"}
MERGE_METHODS = {"merge", "squash", "rebase"}
CHUNK_CLOSURES = {"complete", "progress"}
FULL_GIT_SHA_RE = re.compile(r"^[0-9a-fA-F]{40}$")
DIGEST_RE = re.compile(r"^[0-9a-fA-F]{64}$")
PREDECESSOR_ATTESTATION_PREFIX = "<!-- derived-alg-geo-lean.loop-predecessor:v1 "
PREDECESSOR_ATTESTATION_SUFFIX = " -->"
DEFAULT_MERGE_POLICY = {
    "method": "squash",
    # A squash-merged branch left on the remote blocks the next run that plans
    # the same `agent/<slug>` name: its commits are not ancestors of main.
    "delete_branch": True,
    "allow_method_override": False,
    "allow_delete_branch_override": False,
    "allow_auto": False,
    "allow_admin": False,
}


class LoopError(loop_recovery.RecoveryError, RuntimeError):
    """A user-actionable validation, ledger, or preflight error."""


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def canonical_json(value: Any) -> str:
    # YAML turns an unquoted date into a date object; stringify it rather than
    # crash. No digest changes: such a value could not be serialized before.
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True, default=str)


def canonical_repo_path(path: str) -> str:
    """Collapse the spellings one path can take: `./`, `//`, `\\`, a trailing slash."""

    value = re.sub(r"/+", "/", path.replace("\\", "/"))
    while value.startswith("./"):
        value = value[2:]
    return value.rstrip("/")


def is_protected_path(path: str, exempt: Iterable[str] = ()) -> bool:
    """True for a path a branch-authored run may not change.

    `exempt` holds the run's own plan paths: its manifest and its OpenSpec
    change directory, matched exactly as recorded. Everything else compares
    case-insensitively, since on a case-insensitive checkout `Scripts/...` and
    `scripts/...` are one file.
    """

    value = canonical_repo_path(path)
    folded = value.casefold()
    parts = value.split("/")
    if ".." in parts or "." in parts:
        return True
    if folded.rsplit("/", 1)[-1] in PROTECTED_BASENAMES:
        return True
    for own in exempt:
        own = canonical_repo_path(own)
        if own and (value == own or value.startswith(own + "/")):
            return False
    if any(pattern.fullmatch(value) for pattern in UNPROTECTED_RECORD_RES):
        return False
    return any(
        folded == prefix.casefold() or folded.startswith(prefix.casefold() + "/") for prefix in PROTECTED_PATH_PREFIXES
    )


def protected_paths(paths: Iterable[str], exempt: Iterable[str] = ()) -> list[str]:
    """Return the paths a branch-authored run may not change."""

    exempt = list(exempt)
    return [path for path in paths if is_protected_path(path, exempt)]


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode("utf-8")).hexdigest()


def openspec_change_dir(root: Path, spec: dict[str, Any]) -> Path:
    openspec = require_mapping(spec.get("openspec"), "spec.openspec")
    change = require_string(openspec, "change", "spec.openspec")
    return ensure_inside(root, root / "openspec" / "changes" / change)


def has_openspec(spec: dict[str, Any]) -> bool:
    """A single issue may be planned by its own body; OpenSpec is then absent."""

    return spec.get("openspec") is not None


def split_markdown_lines(markdown: str, *, keepends: bool = False) -> list[str]:
    """Split only on Markdown line endings, preserving every other code point."""

    lines: list[str] = []
    start = 0
    for match in MARKDOWN_LINE_END_RE.finditer(markdown):
        end = match.end() if keepends else match.start()
        lines.append(markdown[start:end])
        start = match.end()
    if start < len(markdown):
        lines.append(markdown[start:])
    return lines


def _parse_markdown(markdown: str) -> list[Any]:
    """Parse with the pinned CommonMark grammar used by the ledger digest."""

    return COMMONMARK_PARSER.parse(markdown)


def normalize_task_checkboxes(markdown: str) -> str:
    """Normalize checkbox state only in actual Markdown list-item paragraphs.

    The first direct block of a list item must be a paragraph whose inline
    content starts with the checkbox. Source maps then tie that parsed item
    back to the exact line being normalized; checkbox-shaped code and links
    stay fixed.
    """

    lines = split_markdown_lines(markdown, keepends=True)
    tokens = _parse_markdown(markdown)

    list_items: list[dict[str, Any]] = []
    for token in tokens:
        if token.type == "list_item_open":
            list_items.append(
                {
                    "level": token.level,
                    "first_block_seen": False,
                    "paragraph_level": None,
                }
            )
            continue

        if token.type == "list_item_close":
            while list_items and list_items[-1]["level"] >= token.level:
                list_items.pop()
            continue

        if not list_items:
            continue
        item = list_items[-1]
        if (
            not item["first_block_seen"]
            and token.level == item["level"] + 1
            and token.type in MARKDOWN_BLOCK_CONTENT_TYPES
        ):
            item["first_block_seen"] = True
            if token.type == "paragraph_open":
                item["paragraph_level"] = token.level
            continue

        if item["paragraph_level"] is not None:
            if (
                token.type == "inline"
                and token.level == item["paragraph_level"] + 1
                and token.map
                and token.children
                and token.children[0].type == "text"
                and TASK_INLINE_CHECKBOX_RE.match(token.children[0].content)
            ):
                line_number = token.map[0]
                if (
                    0 <= line_number < len(lines)
                    and TASK_LIST_CHECKBOX_RE.match(lines[line_number])
                ):
                    lines[line_number] = TASK_LIST_CHECKBOX_RE.sub(
                        r"\1[ ]", lines[line_number], count=1
                    )
            if token.type == "paragraph_close" and token.level == item["paragraph_level"]:
                item["paragraph_level"] = None
    return "".join(lines)


def has_visible_why_heading(markdown: str) -> bool:
    """Recognize a root-level ATX h2 whose rendered inline text is exactly Why."""

    tokens = _parse_markdown(markdown)
    for index, token in enumerate(tokens):
        if (
            token.type != "heading_open"
            or token.tag != "h2"
            or token.level != 0
            or token.markup != "##"
            or index + 1 >= len(tokens)
            or tokens[index + 1].type != "inline"
        ):
            continue
        inline = tokens[index + 1]
        children = inline.children or []
        # Raw HTML can hide text through attributes such as `hidden` or inline
        # styles. Do not call that text visibly present; unrelated HTML outside
        # this candidate heading remains irrelevant.
        if any(child.type in {"html_inline", "image"} for child in children):
            continue
        visible_text = "".join(child.content for child in children if child.type in {"text", "code_inline"}).strip()
        if visible_text == "Why":
            return True
    return False


def checked_openspec_digest_version(version: Any) -> int:
    if type(version) is not int or version not in SUPPORTED_OPENSPEC_DIGEST_VERSIONS:
        raise LoopError(f"unsupported OpenSpec digest version: {version!r}")
    return version


def openspec_digest(root: Path, spec: dict[str, Any], version: int = OPENSPEC_DIGEST_VERSION) -> str:
    """Hash planning content; the registered digest freezes it, not its Git path.

    Version 2 preserves its original regex normalization so existing ledgers
    keep verifying. Version 3 freezes the contract with CommonMark-aware task
    checkbox normalization. Version 1 and 2 remain available for old ledgers.
    """

    version = checked_openspec_digest_version(version)
    if not has_openspec(spec):
        return digest([])
    change_dir = openspec_change_dir(root, spec)
    openspec = require_mapping(spec.get("openspec"), "spec.openspec")
    parts: list[dict[str, str]] = []
    for relative in openspec["required_artifacts"]:
        path = ensure_inside(root, change_dir / relative)
        # Only the change's own top-level log and task list are progress
        # records; a file of the same name under specs/ is contract.
        if version >= 2 and relative in LOG_ARTIFACT_NAMES:
            continue
        try:
            if version >= 3:
                content = path.read_bytes().decode("utf-8")
            else:
                # Keep historical universal-newline normalization for v1/v2.
                content = path.read_text(encoding="utf-8")
        except UnicodeDecodeError as exc:
            raise LoopError(f"OpenSpec artifact is not valid UTF-8: {relative}") from exc
        if version == 2 and relative == "tasks.md":
            content = TASK_CHECKBOX_RE_V2.sub(r"\1[ ]", content)
        elif version >= 3 and relative == "tasks.md":
            content = normalize_task_checkboxes(content)
        parts.append({"path": relative, "content": content})
    return digest(parts)


def ledger_digest_version(state: dict[str, Any]) -> int:
    """Ledgers written before v2 recorded no version and hashed with v1."""

    return checked_openspec_digest_version(state.get("openspec_digest_version", 1))


def ledger_openspec_matches(root: Path, spec: dict[str, Any], state: dict[str, Any]) -> bool:
    return state.get("openspec_digest") == openspec_digest(root, spec, ledger_digest_version(state))


def validate_openspec_artifacts(root: Path, spec: dict[str, Any]) -> None:
    """Check the OpenSpec change shape without requiring a global Node install.

    The OpenSpec CLI remains the authoritative richer validator when available;
    this portable structural check keeps repository gates usable on Lean-only
    runners that do not install npm tooling.
    """

    if not has_openspec(spec):
        return
    openspec_root = ensure_inside(root, root / "openspec")
    if not (openspec_root / "config.yaml").is_file():
        raise LoopError("openspec/config.yaml is missing; initialize OpenSpec before enabling a run")
    change_dir = openspec_change_dir(root, spec)
    if not change_dir.is_dir():
        raise LoopError(f"OpenSpec change does not exist: {change_dir.relative_to(root)}")
    openspec = require_mapping(spec.get("openspec"), "spec.openspec")
    for relative in openspec["required_artifacts"]:
        path = ensure_inside(root, change_dir / relative)
        if not path.is_file():
            raise LoopError(f"OpenSpec artifact is missing: {path.relative_to(root)}")
        if not path.read_text(encoding="utf-8").strip():
            raise LoopError(f"OpenSpec artifact is empty: {path.relative_to(root)}")
    proposal = ensure_inside(root, change_dir / "proposal.md")
    if "proposal.md" in openspec["required_artifacts"] and not has_visible_why_heading(
        proposal.read_text(encoding="utf-8")
    ):
        raise LoopError("OpenSpec proposal must contain a Why section")
    spec_texts = [
        ensure_inside(root, change_dir / relative).read_text(encoding="utf-8")
        for relative in openspec["required_artifacts"]
        if "/specs/" in f"/{relative}" or relative.startswith("specs/")
    ]
    if not any("### Requirement:" in text and "#### Scenario:" in text for text in spec_texts):
        raise LoopError("OpenSpec delta must contain at least one requirement and one scenario")
    requirement_names = {
        match.group(1).strip()
        for text in spec_texts
        for match in re.finditer(r"^### Requirement:\s*(.+?)\s*$", text, re.MULTILINE)
    }
    missing_requirements = {
        requirement
        for issue in spec["issues"]
        for chunk in issue["chunks"]
        for requirement in chunk["requirements"]
        if requirement not in requirement_names
    }
    if missing_requirements:
        raise LoopError(
            "run chunks reference OpenSpec requirements that are absent: "
            + ", ".join(sorted(missing_requirements))
        )
    if "tasks.md" in openspec["required_artifacts"]:
        tasks = ensure_inside(root, change_dir / "tasks.md").read_text(encoding="utf-8")
        if not re.search(r"^- \[[ xX]\] \d+\.\d+\s+.+", tasks, re.MULTILINE):
            raise LoopError("OpenSpec tasks.md must contain numbered checkbox tasks")


def repo_path(root: Path, value: str | Path) -> Path:
    path = Path(value)
    if not path.is_absolute():
        path = root / path
    return path.resolve()


def ensure_inside(root: Path, path: Path) -> Path:
    root = root.resolve()
    path = path.resolve()
    try:
        path.relative_to(root)
    except ValueError as exc:
        raise LoopError(f"path must stay inside repository: {path}") from exc
    return path


def run_command(root: Path, args: list[str], *, check: bool = False) -> subprocess.CompletedProcess[str]:
    command = list(args)
    # PowerShell resolves the npm-generated openspec.ps1 shim, but Python's
    # Windows process launcher needs an executable extension.  The .cmd shim
    # has the same behavior and is available wherever the CLI is installed.
    if sys.platform == "win32" and command and command[0] == "openspec":
        command[0] = "openspec.cmd"
    result = subprocess.run(
        command,
        cwd=root,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=False,
    )
    if check and result.returncode != 0:
        detail = (result.stderr or result.stdout).strip()
        raise LoopError(f"command failed ({result.returncode}): {' '.join(command)}\n{detail}")
    return result


def git(root: Path, *args: str, check: bool = True) -> str:
    result = run_command(root, ["git", *args], check=check)
    return result.stdout.strip()


def gh_json(root: Path, args: list[str]) -> Any:
    result = run_command(root, ["gh", *args], check=False)
    if result.returncode != 0:
        detail = (result.stderr or result.stdout).strip()
        raise LoopError(f"gh command failed ({result.returncode}): gh {' '.join(args)}\n{detail}")
    try:
        return json.loads(result.stdout)
    except json.JSONDecodeError as exc:
        raise LoopError(f"gh command returned invalid JSON: gh {' '.join(args)}") from exc


def load_spec(
    path: Path, root: Path | None = None, *, verify_owner_review: bool = True
) -> dict[str, Any]:
    try:
        data = yaml.safe_load(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise LoopError(f"specification does not exist: {path}") from exc
    except OSError as exc:
        raise LoopError(f"could not read specification {path}: {exc}") from exc
    except yaml.YAMLError as exc:
        raise LoopError(f"specification {path} is not valid YAML: {exc}") from exc
    if not isinstance(data, dict):
        raise LoopError("specification root must be a YAML mapping")
    owner_reviewed = (
        owner_reviewed_legacy_manifest(root, data)
        if root is not None and verify_owner_review
        else False
    )
    validate_spec(data, owner_reviewed_legacy=owner_reviewed)
    if root is not None:
        validate_openspec_artifacts(root, data)
    return data


def require_mapping(value: Any, name: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise LoopError(f"{name} must be a mapping")
    return value


def require_string(mapping: dict[str, Any], key: str, name: str) -> str:
    value = mapping.get(key)
    if not isinstance(value, str) or not value.strip():
        raise LoopError(f"{name}.{key} must be a non-empty string")
    return value.strip()


def require_bool(mapping: dict[str, Any], key: str, name: str) -> bool:
    value = mapping.get(key)
    if not isinstance(value, bool):
        raise LoopError(f"{name}.{key} must be a boolean")
    return value


def manifest_mutations(spec: dict[str, Any]) -> dict[str, bool]:
    """Return the manifest's own explicit provider grants and refusals."""

    configured = spec.get("mutations", {})
    if not isinstance(configured, dict):
        raise LoopError("spec.mutations must be a mapping")
    unknown = set(configured) - set(MUTATION_KEYS)
    if unknown:
        raise LoopError("spec.mutations has unsupported keys: " + ", ".join(sorted(unknown)))
    for key, value in configured.items():
        if not isinstance(value, bool):
            raise LoopError(f"spec.mutations.{key} must be a boolean")
    return dict(configured)


def gh_not_found(result: subprocess.CompletedProcess[str]) -> bool:
    detail = f"{result.stderr}\n{result.stdout}"
    return "HTTP 404" in detail or "Not Found" in detail


def read_owner_file(root: Path, spec: dict[str, Any], path: str) -> str | None:
    """Read a file from the repository's default branch on the provider.

    Local refs are writable by whoever runs the controller, including a
    remote-tracking ref, so an owner-controlled file is read from the provider
    itself. With no `ref`, the contents API serves the default branch.
    """

    result = run_command(
        root,
        ["gh", "api", "-H", "Accept: application/vnd.github.raw+json", f"repos/{spec['repository']}/contents/{path}"],
    )
    if result.returncode == 0:
        return result.stdout
    # A 404 means "absent" only when the repository itself is readable; an
    # unreachable repository must not read as "no revocations".
    if gh_not_found(result) and run_command(root, ["gh", "api", f"repos/{spec['repository']}"]).returncode == 0:
        return None
    detail = (result.stderr or result.stdout).strip()
    raise LoopError(f"could not read {path} from {spec['repository']}'s default branch: {detail}")


def standing_authority(root: Path, spec: dict[str, Any]) -> dict[str, bool]:
    """Return the owner's explicit standing grants and revocations; empty when absent."""

    text = read_owner_file(root, spec, STANDING_AUTHORITY_PATH)
    if text is None:
        return {}
    try:
        data = yaml.safe_load(text)
    except yaml.YAMLError as exc:
        raise LoopError(f"{STANDING_AUTHORITY_PATH} on the base branch is not valid YAML: {exc}") from exc
    if not isinstance(data, dict) or data.get("schema") != STANDING_AUTHORITY_SCHEMA:
        raise LoopError(f"{STANDING_AUTHORITY_PATH} must declare schema {STANDING_AUTHORITY_SCHEMA!r}")
    grants = data.get("mutations", {})
    if not isinstance(grants, dict) or set(grants) - set(MUTATION_KEYS) or any(
        not isinstance(value, bool) for value in grants.values()
    ):
        raise LoopError(f"{STANDING_AUTHORITY_PATH} mutations must map known actions to booleans")
    return dict(grants)


def owner_reviewed_legacy_manifest(root: Path, spec: dict[str, Any]) -> bool:
    """Check that the exact legacy digest is allowlisted on the default branch.

    A planning branch necessarily contains its proposed allowlist entry before
    that entry has been reviewed and merged. Reading the default branch's
    controller copy prevents that local entry from authorizing the branch
    which introduced it.
    """

    source = read_owner_file(root, spec, "scripts/loop_engine.py")
    if source is None:
        return False
    try:
        tree = ast.parse(source)
    except SyntaxError as exc:
        raise LoopError("scripts/loop_engine.py on the default branch is not valid Python") from exc
    for node in tree.body:
        if not isinstance(node, ast.Assign):
            continue
        if not any(isinstance(target, ast.Name) and target.id == "LEGACY_REVIEWED_MANIFESTS" for target in node.targets):
            continue
        value = node.value
        if (
            not isinstance(value, ast.Call)
            or not isinstance(value.func, ast.Name)
            or value.func.id != "frozenset"
            or len(value.args) != 1
        ):
            raise LoopError("LEGACY_REVIEWED_MANIFESTS on the default branch has an unsupported format")
        try:
            digests = ast.literal_eval(value.args[0])
        except (ValueError, TypeError) as exc:
            raise LoopError("LEGACY_REVIEWED_MANIFESTS on the default branch is not a literal set") from exc
        if not isinstance(digests, (set, frozenset, tuple, list)) or any(
            not isinstance(item, str) for item in digests
        ):
            raise LoopError("LEGACY_REVIEWED_MANIFESTS on the default branch must contain string digests")
        return digest(spec) in digests
    raise LoopError("LEGACY_REVIEWED_MANIFESTS is missing from the default-branch controller")


def effective_mutations(root: Path, spec: dict[str, Any]) -> dict[str, bool]:
    """Resolve provider authority for this manifest from owner-controlled sources.

    A branch-authored manifest gets the standing grant, narrowed by its own
    explicit `false`s. A legacy reviewed manifest keeps its explicit grants,
    falls back to the standing grant for keys it omits, and yields to an
    explicit standing `false`, which is the owner's kill switch for every run.
    """

    configured = manifest_mutations(spec)
    standing = standing_authority(root, spec)
    if owner_reviewed_legacy_manifest(root, spec):
        return {
            key: standing.get(key) is not False and configured.get(key, standing.get(key, False))
            for key in MUTATION_KEYS
        }
    return {key: standing.get(key, False) and configured.get(key, True) for key in MUTATION_KEYS}


def merge_policy(spec: dict[str, Any]) -> dict[str, Any]:
    """Return the explicit merge policy, retaining safe v1 defaults."""

    configured = spec.get("merge", {})
    if not isinstance(configured, dict):
        raise LoopError("spec.merge must be a mapping")
    policy = {**DEFAULT_MERGE_POLICY, **configured}
    if policy["method"] not in MERGE_METHODS:
        raise LoopError("spec.merge.method must be merge, squash, or rebase")
    for key in (
        "delete_branch",
        "allow_method_override",
        "allow_delete_branch_override",
        "allow_auto",
        "allow_admin",
    ):
        if not isinstance(policy[key], bool):
            raise LoopError(f"spec.merge.{key} must be a boolean")
    return policy


def predecessor_attestation_policy(spec: dict[str, Any]) -> dict[str, bool]:
    """Return the optional source-PR attestation policy after validation."""

    configured = spec.get("predecessor_attestation", {})
    if not isinstance(configured, dict):
        raise LoopError("spec.predecessor_attestation must be a mapping")
    emit = configured.get("emit", False)
    if not isinstance(emit, bool):
        raise LoopError("spec.predecessor_attestation.emit must be a boolean")
    unknown = set(configured) - {"emit"}
    if unknown:
        raise LoopError(
            "spec.predecessor_attestation has unsupported keys: "
            + ", ".join(sorted(unknown))
        )
    return {"emit": emit}


def predecessor_prs(spec: dict[str, Any]) -> list[dict[str, Any]]:
    """Validate and return durable predecessor-PR bindings for a successor."""

    entries = spec.get("predecessor_prs", [])
    if not isinstance(entries, list):
        raise LoopError("spec.predecessor_prs must be a list")
    numbers: set[int] = set()
    required = {
        "number",
        "manifest_id",
        "chunk_id",
        "spec_digest",
        "openspec_digest",
        "max_review_rounds",
        "issue_number",
        "source_branch",
        "closure",
        "reviewed_head",
        "merge_commit",
    }
    for index, entry in enumerate(entries):
        name = f"spec.predecessor_prs[{index}]"
        if not isinstance(entry, dict):
            raise LoopError(f"{name} must be a mapping")
        missing = required - set(entry)
        if missing:
            raise LoopError(f"{name} is missing keys: " + ", ".join(sorted(missing)))
        unknown = set(entry) - required
        if unknown:
            raise LoopError(f"{name} has unsupported keys: " + ", ".join(sorted(unknown)))
        number = entry["number"]
        if not isinstance(number, int) or isinstance(number, bool) or number <= 0:
            raise LoopError(f"{name}.number must be a positive pull-request number")
        if number in numbers:
            raise LoopError(f"spec.predecessor_prs must not repeat pull request #{number}")
        numbers.add(number)
        manifest_id = entry["manifest_id"]
        if not isinstance(manifest_id, str) or not ISSUE_ID_RE.fullmatch(manifest_id):
            raise LoopError(f"{name}.manifest_id must use lowercase kebab-case")
        if not isinstance(entry["chunk_id"], str) or not entry["chunk_id"].strip():
            raise LoopError(f"{name}.chunk_id must be a non-empty string")
        issue_number = entry["issue_number"]
        if not isinstance(issue_number, int) or isinstance(issue_number, bool) or issue_number <= 0:
            raise LoopError(f"{name}.issue_number must be a positive issue number")
        source_branch = entry["source_branch"]
        if not isinstance(source_branch, str) or not BRANCH_RE.fullmatch(source_branch):
            raise LoopError(f"{name}.source_branch must be a dedicated agent branch")
        if entry["closure"] not in CHUNK_CLOSURES:
            raise LoopError(f"{name}.closure must be 'complete' or 'progress'")
        for field in ("spec_digest", "openspec_digest"):
            value = entry[field]
            if not isinstance(value, str) or not DIGEST_RE.fullmatch(value):
                raise LoopError(f"{name}.{field} must be a full SHA-256 digest")
        cap = entry["max_review_rounds"]
        if not isinstance(cap, int) or isinstance(cap, bool) or not 1 <= cap <= MAX_ALLOWED_ROUNDS:
            raise LoopError(
                f"{name}.max_review_rounds must be an integer from 1 to {MAX_ALLOWED_ROUNDS}"
            )
        for field in ("reviewed_head", "merge_commit"):
            value = entry[field]
            if not isinstance(value, str) or not FULL_GIT_SHA_RE.fullmatch(value):
                raise LoopError(f"{name}.{field} must be a full 40-character Git SHA")
    return entries


def validate_spec(spec: dict[str, Any], *, owner_reviewed_legacy: bool = False) -> None:
    """Validate the stable, intentionally small v1 specification schema."""

    if spec.get("schema") != RUN_SCHEMA:
        raise LoopError(f"schema must be {RUN_SCHEMA!r}")
    require_string(spec, "id", "spec")
    require_string(spec, "repository", "spec")
    require_string(spec, "remote", "spec")
    require_string(spec, "actor", "spec")
    base_branch = require_string(spec, "base_branch", "spec")
    base_ref = require_string(spec, "base_ref", "spec")
    if base_branch in {"main", "master"} and not base_ref:
        raise LoopError("spec.base_ref is required for the protected base branch")
    mode = spec.get("mode")
    if mode not in {"stack", "independent"}:
        raise LoopError("spec.mode must be 'stack' or 'independent'")
    require_bool(spec, "enabled", "spec")
    predecessor_attestation_policy(spec)
    predecessor_prs(spec)

    if has_openspec(spec):
        openspec = require_mapping(spec.get("openspec"), "spec.openspec")
        change = require_string(openspec, "change", "spec.openspec")
        if not ISSUE_ID_RE.fullmatch(change):
            raise LoopError("spec.openspec.change must use lowercase kebab-case")
        artifacts = openspec.get("required_artifacts")
        if not isinstance(artifacts, list) or not artifacts or any(
            not isinstance(artifact, str)
            or not artifact.strip()
            or Path(artifact).is_absolute()
            or ".." in Path(artifact).parts
            for artifact in artifacts
        ):
            raise LoopError("spec.openspec.required_artifacts must be non-empty safe relative paths")
        if "proposal.md" not in artifacts or "design.md" not in artifacts or "tasks.md" not in artifacts:
            raise LoopError("OpenSpec run references must include proposal.md, design.md, and tasks.md")
        if not any(artifact.startswith("specs/") and artifact.endswith(".md") for artifact in artifacts):
            raise LoopError("OpenSpec run references must include a delta under specs/")
        validation_mode = openspec.get("validation", "structural")
        if validation_mode not in {"structural", "cli-advisory", "cli-required"}:
            raise LoopError("spec.openspec.validation must be structural, cli-advisory, or cli-required")

    limits = require_mapping(spec.get("limits", {}), "spec.limits")
    min_issues = limits.get("min_issues", 1)
    max_issues = limits.get("max_issues", 3)
    max_rounds = limits.get("max_review_rounds_per_chunk", MAX_ALLOWED_ROUNDS)
    for value, name in (
        (min_issues, "limits.min_issues"),
        (max_issues, "limits.max_issues"),
        (max_rounds, "limits.max_review_rounds_per_chunk"),
    ):
        if not isinstance(value, int) or isinstance(value, bool) or value < 1:
            raise LoopError(f"{name} must be a positive integer")
    if max_issues > 3:
        raise LoopError("limits.max_issues cannot exceed 3 for an unattended pilot")
    if max_rounds > MAX_ALLOWED_ROUNDS:
        raise LoopError(
            f"limits.max_review_rounds_per_chunk cannot exceed {MAX_ALLOWED_ROUNDS}"
        )
    if min_issues > max_issues:
        raise LoopError("limits.min_issues cannot exceed limits.max_issues")

    issues = spec.get("issues")
    if not isinstance(issues, list):
        raise LoopError("spec.issues must be a list")
    if not min_issues <= len(issues) <= max_issues:
        raise LoopError(
            f"spec.issues must contain between {min_issues} and {max_issues} issues; got {len(issues)}"
        )
    numbers: set[int] = set()
    issue_ids: set[str] = set()
    for index, issue in enumerate(issues):
        name = f"spec.issues[{index}]"
        issue = require_mapping(issue, name)
        number = issue.get("number")
        if not isinstance(number, int) or isinstance(number, bool) or number <= 0:
            raise LoopError(f"{name}.number must be a positive integer")
        if number in numbers:
            raise LoopError(f"duplicate issue number: {number}")
        numbers.add(number)
        slug = require_string(issue, "slug", name)
        if not ISSUE_ID_RE.fullmatch(slug):
            raise LoopError(f"{name}.slug must use lowercase kebab-case")
        if slug in issue_ids:
            raise LoopError(f"duplicate issue slug: {slug}")
        issue_ids.add(slug)
        dependencies = issue.get("depends_on", [])
        if not isinstance(dependencies, list) or any(
            not isinstance(dependency, int) or isinstance(dependency, bool) or dependency <= 0
            for dependency in dependencies
        ):
            raise LoopError(f"{name}.depends_on must be a list of positive issue numbers")
        chunks = issue.get("chunks")
        if not isinstance(chunks, list) or not chunks:
            raise LoopError(f"{name}.chunks must contain at least one frozen chunk")
        chunk_ids: set[str] = set()
        for chunk_index, chunk in enumerate(chunks):
            chunk_name = f"{name}.chunks[{chunk_index}]"
            chunk = require_mapping(chunk, chunk_name)
            chunk_id = require_string(chunk, "id", chunk_name)
            if not ISSUE_ID_RE.fullmatch(chunk_id):
                raise LoopError(f"{chunk_name}.id must use lowercase kebab-case")
            if chunk_id in chunk_ids:
                raise LoopError(f"duplicate chunk id {chunk_id} in issue {number}")
            chunk_ids.add(chunk_id)
            require_string(chunk, "scope", chunk_name)
            files = chunk.get("files")
            if not isinstance(files, list) or not files or any(
                not isinstance(file, str) or not file.strip() for file in files
            ):
                raise LoopError(f"{chunk_name}.files must be a non-empty list of paths")
            lift_targets = chunk.get("lift_targets", [])
            if not isinstance(lift_targets, list) or any(
                not isinstance(target, str) or not target.strip() for target in lift_targets
            ):
                raise LoopError(f"{chunk_name}.lift_targets must be a list of paths")
            for target in lift_targets:
                if target in files:
                    raise LoopError(
                        f"{chunk_name}.lift_targets entry {target!r} is already in files; "
                        "a lift target names an ancestor the chunk may not touch yet"
                    )
            acceptance = chunk.get("acceptance")
            if not isinstance(acceptance, list) or not acceptance or any(
                not isinstance(item, str) or not item.strip() for item in acceptance
            ):
                raise LoopError(f"{chunk_name}.acceptance must be a non-empty list of statements")
            # Without OpenSpec the issue body is the specification, and the
            # chunk's acceptance statements restate its definition of done.
            requirements = chunk.get("requirements", None if has_openspec(spec) else [])
            if not isinstance(requirements, list) or any(
                not isinstance(item, str) or not item.strip() for item in requirements
            ) or (has_openspec(spec) and not requirements):
                raise LoopError(f"{chunk_name}.requirements must name at least one OpenSpec requirement")
            closure = chunk.get("closure", "complete")
            if closure not in CHUNK_CLOSURES:
                raise LoopError(f"{chunk_name}.closure must be 'complete' or 'progress'")

    eligibility = spec.get("eligibility", {})
    if not isinstance(eligibility, dict):
        raise LoopError("spec.eligibility must be a mapping")
    allow_epic_issues = eligibility.get("allow_epic_issues", [])
    if not isinstance(allow_epic_issues, list) or any(
        not isinstance(number, int) or isinstance(number, bool) or number <= 0
        for number in allow_epic_issues
    ):
        raise LoopError("spec.eligibility.allow_epic_issues must be a list of positive issue numbers")
    if len(set(allow_epic_issues)) != len(allow_epic_issues):
        raise LoopError("spec.eligibility.allow_epic_issues must not contain duplicates")
    unselected_epic_opt_ins = set(allow_epic_issues) - numbers
    if unselected_epic_opt_ins:
        raise LoopError(
            "spec.eligibility.allow_epic_issues must be a subset of selected issues: "
            + ", ".join(str(number) for number in sorted(unselected_epic_opt_ins))
        )

    reviewer_spec = require_mapping(spec.get("review"), "spec.review")
    reviewers = reviewer_spec.get("reviewers")
    if not isinstance(reviewers, list) or not reviewers or any(
        not isinstance(reviewer, str) or not reviewer.strip() for reviewer in reviewers
    ):
        raise LoopError("spec.review.reviewers must be a non-empty list of names")
    reviewer_set = set(reviewers)
    missing = REQUIRED_REVIEWERS - reviewer_set
    if missing:
        raise LoopError(f"spec.review.reviewers is missing required roles: {', '.join(sorted(missing))}")
    if len(reviewer_set) != len(reviewers):
        raise LoopError("spec.review.reviewers must not contain duplicate names")
    advisors = reviewer_spec.get("advisors", [])
    if not isinstance(advisors, list) or any(
        not isinstance(advisor, str) or not advisor.strip() for advisor in advisors
    ):
        raise LoopError("spec.review.advisors must be a list of names")
    advisor_set = set(advisors)
    if len(advisor_set) != len(advisors):
        raise LoopError("spec.review.advisors must not contain duplicate names")
    overlap = advisor_set & reviewer_set
    if overlap:
        # Naming an advisor in `reviewers` would silently make it a veto:
        # adjudication refuses until every roster member submits, and refuses to
        # pass unless every one of them passed. Advisors have no ledger authority
        # by construction, and that is the point of them.
        raise LoopError(
            "spec.review.advisors must be disjoint from reviewers; "
            f"an advisor cannot also gate adjudication: {', '.join(sorted(overlap))}"
        )
    reviewer_spec.get("independent", True)
    if reviewer_spec.get("independent", True) is not True:
        raise LoopError("spec.review.independent must remain true")

    mutations = manifest_mutations(spec)
    if predecessor_attestation_policy(spec)["emit"] and mutations.get("comment_issue") is False:
        raise LoopError(
            "spec.predecessor_attestation.emit requires spec.mutations.comment_issue=true"
        )
    merge_policy(spec)
    closure = require_mapping(spec.get("closure"), "spec.closure")
    if closure.get("code_issue") != "pr_merge_keyword":
        raise LoopError("spec.closure.code_issue must be 'pr_merge_keyword'")
    require_bool(closure, "allow_non_pr", "spec.closure")
    if "allow_progress_pr" in closure and not isinstance(closure["allow_progress_pr"], bool):
        raise LoopError("spec.closure.allow_progress_pr must be a boolean")
    has_progress_chunk = any(
        chunk.get("closure", "complete") == "progress"
        for issue in issues
        for chunk in issue["chunks"]
    )
    if has_progress_chunk and closure.get("allow_progress_pr") is not True:
        raise LoopError("progress chunks require spec.closure.allow_progress_pr=true")
    runner = require_mapping(spec.get("runner"), "spec.runner")
    checks = runner.get("required_checks")
    if not isinstance(checks, list) or not checks or any(
        not isinstance(check, str) or not check.strip() for check in checks
    ):
        raise LoopError("spec.runner.required_checks must be a non-empty list")
    roadmap = spec.get("roadmap_gate", "required")
    if roadmap not in {"required", "advisory", "disabled"}:
        raise LoopError("spec.roadmap_gate must be required, advisory, or disabled")

    if mode == "independent":
        issue_numbers = {issue["number"] for issue in issues}
        selected_dependencies = {
            dependency
            for issue in issues
            for dependency in issue.get("depends_on", [])
            if dependency in issue_numbers
        }
        if selected_dependencies:
            raise LoopError("independent mode cannot contain dependencies between selected issues")

    if not owner_reviewed_legacy and spec["enabled"]:
        # A branch-authored manifest cannot choose the base its change is
        # measured against, nor scope its chunk over its own authority. A
        # disabled manifest authorizes nothing and is kept only as history.
        expected_base = f"{spec['remote']}/{base_branch}"
        if base_ref != expected_base:
            raise LoopError(f"spec.base_ref must be {expected_base!r}, the remote base branch")
        for issue in issues:
            for chunk in issue["chunks"]:
                blocked = protected_paths(
                    list(chunk["files"]) + list(chunk.get("lift_targets", [])),
                    [f"openspec/changes/{spec['openspec']['change']}"] if has_openspec(spec) else [],
                )
                if blocked:
                    raise LoopError(
                        f"chunk {chunk['id']!r} names protected paths a run may not change: "
                        + ", ".join(blocked)
                    )

    if "recovery" in spec:
        loop_recovery.validate_policy(spec["recovery"])
        if len(issues) != 1 or len(issues[0]["chunks"]) != 1:
            raise LoopError("recovery requires one issue and one frozen chunk per objective")
        if max_rounds != 3:
            raise LoopError("recovery requires exactly three review rounds per attempt")


def recovery_directory(root: Path) -> Path:
    """Shared across worktrees: changing a checkout cannot replenish a budget."""
    common = git(root, "rev-parse", "--git-common-dir")
    return repo_path(root, common).resolve() / "loop-objectives"


def repository_worktree_roots(root: Path) -> list[Path]:
    """Return every live checkout sharing this repository's Git directory."""
    output = git(root, "worktree", "list", "--porcelain", check=False)
    roots: set[Path] = {root.resolve()}
    for line in output.splitlines():
        if not line.startswith("worktree "):
            continue
        candidate = Path(line[len("worktree "):])
        if not candidate.is_absolute():
            candidate = root / candidate
        if not candidate.is_dir():
            continue
        top = git(candidate, "rev-parse", "--show-toplevel", check=False)
        if top:
            roots.add(Path(top).resolve())
    return sorted(roots)


def canonical_ledger_root(root: Path) -> Path:
    """Return the real `.loop-runs` directory and reject a redirected root."""
    root = root.resolve()
    runs_root = root / ".loop-runs"
    if runs_root.is_symlink():
        raise LoopError("the repository's .loop-runs root must not be a symlink")
    return ensure_inside(root, runs_root)


def ordinary_ledger_files(root: Path) -> list[Path]:
    """Find ordinary ledgers in the ignored state trees of every worktree."""
    found: set[Path] = set()
    for worktree in repository_worktree_roots(root):
        runs_root = canonical_ledger_root(worktree)
        if runs_root.is_dir():
            for path in runs_root.rglob("*"):
                # pathlib does not recurse through symlinked directories. Fail
                # closed on the link itself so it cannot hide a ledger from
                # the identity scan and make ledger init replenish its cap.
                if path.is_symlink():
                    raise LoopError(f"ledger inventory does not allow symlinks below .loop-runs: {path}")
                if path.is_file():
                    found.add(path.resolve())
    return sorted(found)


def recovery_registry(root: Path) -> list[tuple[Path, dict[str, Any]]]:
    if not git(root, "rev-parse", "--git-common-dir", check=False):
        return []
    directory = recovery_directory(root)
    records = []
    for path in sorted(directory.glob("*.json")):
        record = read_json_object(path)
        if record.get("schema") != "loop-objective-registry/v1":
            raise LoopError(f"invalid recovery registry record: {path}")
        records.append((path, record))
    return records


def read_json_object(path: Path) -> dict[str, Any]:
    def unique(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise LoopError(f"duplicate JSON field {key!r} in {path}")
            result[key] = value
        return result

    try:
        value = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=unique)
    except (OSError, ValueError) as exc:
        raise LoopError(f"cannot read JSON object {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise LoopError(f"expected a JSON object: {path}")
    return value


def recovery_record(root: Path, spec: dict[str, Any]) -> tuple[Path, dict[str, Any]] | None:
    policy = loop_recovery.validate_policy(spec["recovery"])
    issue = spec["issues"][0]["number"]
    for path, record in recovery_registry(root):
        if record.get("repository", "").casefold() == spec["repository"].casefold() and (
            record.get("issue") == issue or record.get("objective_id") == policy["objective_id"]
        ):
            if record.get("issue") != issue or record.get("objective_id") != policy["objective_id"]:
                raise LoopError("registered objective identity cannot be renamed or moved to another issue")
            return path, record
    return None


def validate_registered_state(record: dict[str, Any], state: dict[str, Any]) -> None:
    root = Path(record["repo_root"])
    spec = load_spec(Path(record["spec_path"]), root, verify_owner_review=True)
    if "recovery" not in spec or digest(spec) != record["spec_digest"]:
        raise LoopError("registered recovery manifest changed; a reset is not a migration")
    if openspec_digest(root, spec, ledger_digest_version(state)) != record["openspec_digest"]:
        raise LoopError("registered objective's frozen OpenSpec requirements changed")
    if state.get("spec_digest") != record["spec_digest"] or state.get("spec_id") != spec["id"]:
        raise LoopError("recovery ledger manifest binding changed")
    if state.get("openspec_digest") != record["openspec_digest"]:
        raise LoopError("recovery ledger OpenSpec binding changed")
    if state.get("repo_root") != str(root):
        raise LoopError("recovery ledger checkout changed")
    issue = spec["issues"][0]
    chunk = issue["chunks"][0]
    expected = {key: chunk[key] for key in ("id", "scope", "files", "requirements", "acceptance")}
    expected.update(lift_targets=chunk.get("lift_targets", []), closure=chunk.get("closure", "complete"))
    if state.get("chunk") != expected or state.get("issue") != {"number": issue["number"], "slug": issue["slug"]}:
        raise LoopError("recovery cannot change the original frozen selection")
    if state.get("reviewers") != spec["review"]["reviewers"] or state.get("max_review_rounds") != 3:
        raise LoopError("recovery cannot change the required panel or attempt cap")
    if state.get("recovery", {}).get("policy") != loop_recovery.validate_policy(spec["recovery"]):
        raise LoopError("recovery policy differs from its registered manifest")
    loop_recovery.validate(state)


def registered_state_at(path: Path) -> tuple[Path, dict[str, Any]] | None:
    root_text = git(path.resolve().parent, "rev-parse", "--show-toplevel", check=False)
    if not root_text:
        return None
    for registry_path, record in recovery_registry(Path(root_text)):
        if Path(record["state_file"]).resolve() == path.resolve():
            return registry_path, record
    return None


@contextlib.contextmanager
def controller_lock(root: Path):
    """Process locks are released on crash; no stale lock-file removal is needed."""
    common = git(root, "rev-parse", "--git-common-dir", check=False)
    if not common:
        yield
        return
    lock_path = repo_path(root, common).resolve() / "loop-controller.lock"
    with lock_path.open("a+b") as lock:
        if os.name == "nt":  # pragma: no cover - Windows runners
            import msvcrt
            if lock.tell() == 0:
                lock.write(b"\0")
                lock.flush()
            lock.seek(0)
            msvcrt.locking(lock.fileno(), msvcrt.LK_LOCK, 1)
        else:
            import fcntl
            fcntl.flock(lock.fileno(), fcntl.LOCK_EX)
        try:
            yield
        finally:
            if os.name == "nt":  # pragma: no cover
                lock.seek(0)
                msvcrt.locking(lock.fileno(), msvcrt.LK_UNLCK, 1)
            else:
                fcntl.flock(lock.fileno(), fcntl.LOCK_UN)


def issue_entry(spec: dict[str, Any], number: int) -> dict[str, Any]:
    for issue in spec["issues"]:
        if issue["number"] == number:
            return issue
    raise LoopError(f"issue #{number} is not included in spec {spec['id']}")


def chunk_entry(spec: dict[str, Any], number: int, chunk_id: str) -> tuple[dict[str, Any], dict[str, Any]]:
    issue = issue_entry(spec, number)
    for chunk in issue["chunks"]:
        if chunk["id"] == chunk_id:
            return issue, chunk
    raise LoopError(f"chunk {chunk_id!r} is not included for issue #{number}")


def print_validation(path: Path, root: Path) -> int:
    try:
        spec = load_spec(path, root, verify_owner_review=True)
    except LoopError as exc:
        print(f"FAIL spec {path}: {exc}")
        return 1
    print(f"PASS spec {spec['id']} ({path})")
    if has_openspec(spec):
        print(f"  openspec change={spec['openspec']['change']} validation={spec['openspec'].get('validation', 'structural')}")
    else:
        print("  openspec=(none; the issue body is the specification)")
    print(f"  mode={spec['mode']} enabled={spec['enabled']} issues={len(spec['issues'])}")
    print(f"  reviewers={', '.join(spec['review']['reviewers'])}")
    advisors = spec["review"].get("advisors") or []
    print(f"  advisors={', '.join(advisors) if advisors else '(none)'} [non-blocking]")
    print(f"  max_review_rounds_per_chunk={spec['limits']['max_review_rounds_per_chunk']}")
    epic_opt_ins = spec.get("eligibility", {}).get("allow_epic_issues", [])
    if epic_opt_ins:
        print(f"  explicitly_authorized_epic_issues={','.join(str(number) for number in epic_opt_ins)}")
    policy = merge_policy(spec)
    print(
        "  merge="
        f"{policy['method']} delete_branch={policy['delete_branch']} "
        f"auto={policy['allow_auto']} admin={policy['allow_admin']}"
    )
    if not spec["enabled"]:
        print("  NOTE pilot is disabled; no remote mutation is authorized")
    return 0


def normalize_remote(url: str) -> str:
    value = url.strip()
    if value.startswith("git@github.com:"):
        value = "github.com/" + value.split(":", 1)[1]
    value = re.sub(r"^https?://", "", value)
    value = re.sub(r"^ssh://git@", "", value)
    value = value.removesuffix(".git").rstrip("/")
    value = re.sub(r"^github\.com/", "", value)
    return value.lower()


def require_manifest_remote(root: Path, spec: dict[str, Any]) -> None:
    """Bind provider reads and writes to every configured URL of the frozen remote."""
    remote = spec["remote"]
    repository = spec["repository"].lower()
    for flags in (["--all"], ["--push", "--all"]):
        urls = git(root, "remote", "get-url", *flags, remote).splitlines()
        if not urls:
            raise LoopError(f"remote {remote!r} has no configured URL")
        for url in urls:
            target = normalize_remote(url)
            if target != repository:
                raise LoopError(f"remote {remote!r} resolves to {target!r}, not {spec['repository']!r}")


def blocked_by_entries(issue: dict[str, Any]) -> list[Any]:
    """Normalize GitHub's blockedBy connection without treating an empty mapping as truthy."""

    blocked_by = issue.get("blockedBy")
    if isinstance(blocked_by, dict):
        nodes = blocked_by.get("nodes")
        if isinstance(nodes, list):
            if nodes:
                return nodes
            total = blocked_by.get("totalCount")
            return [{}] if isinstance(total, int) and total > 0 else []
        total = blocked_by.get("totalCount")
        return [{}] if isinstance(total, int) and total > 0 else []
    if isinstance(blocked_by, list):
        return blocked_by
    return []


def gh_authenticated(root: Path) -> str:
    data = gh_json(root, ["api", "user"])
    login = data.get("login") if isinstance(data, dict) else None
    if not isinstance(login, str) or not login:
        raise LoopError("gh api user did not return an authenticated login")
    return login


def existing_prs(root: Path, repository: str) -> list[dict[str, Any]]:
    data = gh_json(
        root,
        [
            "pr",
            "list",
            "--repo",
            repository,
            "--state",
            "all",
            "--limit",
            "200",
            "--json",
            "number,state,isDraft,headRefName,headRefOid,closingIssuesReferences,author",
        ],
    )
    if not isinstance(data, list):
        raise LoopError("gh pr list returned an unexpected response")
    return data


def issue_state(root: Path, repository: str, number: int) -> dict[str, Any]:
    data = gh_json(
        root,
        [
            "issue",
            "view",
            str(number),
            "--repo",
            repository,
            "--json",
            "number,state,title,labels,blockedBy",
        ],
    )
    if not isinstance(data, dict):
        raise LoopError(f"gh issue view #{number} returned an unexpected response")
    return data


def require_legacy_issue_open(root: Path, spec: dict[str, Any], number: int) -> None:
    """A legacy manifest's reviewed grants apply only to the unfinished work it was reviewed for.

    Several legacy manifests stay enabled after their issues closed, some with
    administrator merge or `.github/` in scope; their grants must not be
    reusable for new work.
    """

    if not owner_reviewed_legacy_manifest(root, spec):
        return
    state = str(issue_state(root, spec["repository"], number).get("state", "")).upper()
    if state != "OPEN":
        raise LoopError(
            f"issue #{number} is {state or 'unknown'}; a legacy manifest's grants cover only its open issues"
        )


def issue_body_digest(root: Path, spec: dict[str, Any], number: int) -> str:
    data = gh_json(root, ["issue", "view", str(number), "--repo", spec["repository"], "--json", "body"])
    body = data.get("body") if isinstance(data, dict) else None
    if not isinstance(body, str):
        raise LoopError(f"issue #{number} has no readable body to serve as the specification")
    return hashlib.sha256(body.encode("utf-8")).hexdigest()


def predecessor_attestation_payload(
    manifest_id: str,
    chunk_id: str,
    spec_digest: str,
    openspec_digest_value: str,
    max_review_rounds: int,
    issue_number: int,
    source_branch: str,
    closure: str,
    reviewed_head: str,
) -> dict[str, Any]:
    """Build the exact durable source-run evidence a successor must pin."""

    return {
        "schema": f"{RUN_SCHEMA}/predecessor-attestation",
        "manifest_id": manifest_id,
        "chunk_id": chunk_id,
        "spec_digest": spec_digest.lower(),
        "openspec_digest": openspec_digest_value.lower(),
        "max_review_rounds": max_review_rounds,
        "issue_number": issue_number,
        "source_branch": source_branch,
        "closure": closure,
        "reviewed_head": reviewed_head.lower(),
    }


def predecessor_attestation_from_binding(binding: dict[str, Any]) -> dict[str, Any]:
    return predecessor_attestation_payload(
        binding["manifest_id"],
        binding["chunk_id"],
        binding["spec_digest"],
        binding["openspec_digest"],
        binding["max_review_rounds"],
        binding["issue_number"],
        binding["source_branch"],
        binding["closure"],
        binding["reviewed_head"],
    )


def predecessor_attestation_from_state(state: dict[str, Any], reviewed_head: str) -> dict[str, Any]:
    """Build an attestation only from a passing, fully populated ledger."""

    if state.get("status") != "passed":
        raise LoopError("predecessor attestation requires a passing review ledger")
    current = latest_round(state)
    if current is None or current.get("adjudication", {}).get("verdict") not in PASSING_VERDICTS:
        raise LoopError("predecessor attestation requires a passing adjudicated review round")
    chunk_id = state.get("chunk", {}).get("id")
    if not isinstance(chunk_id, str) or not chunk_id:
        raise LoopError("predecessor attestation ledger has no frozen chunk id")
    manifest_id = state.get("spec_id")
    if not isinstance(manifest_id, str) or not ISSUE_ID_RE.fullmatch(manifest_id):
        raise LoopError("predecessor attestation ledger has an invalid manifest id")
    spec_digest_value = state.get("spec_digest")
    openspec_digest_value = state.get("openspec_digest")
    max_rounds = state.get("max_review_rounds")
    if not isinstance(spec_digest_value, str) or not DIGEST_RE.fullmatch(spec_digest_value):
        raise LoopError("predecessor attestation ledger has an invalid manifest digest")
    if not isinstance(openspec_digest_value, str) or not DIGEST_RE.fullmatch(openspec_digest_value):
        raise LoopError("predecessor attestation ledger has an invalid OpenSpec digest")
    if not isinstance(max_rounds, int) or isinstance(max_rounds, bool) or not 1 <= max_rounds <= MAX_ALLOWED_ROUNDS:
        raise LoopError("predecessor attestation ledger has an invalid review-round cap")
    issue = state.get("issue")
    issue_number = issue.get("number") if isinstance(issue, dict) else None
    slug = issue.get("slug") if isinstance(issue, dict) else None
    if not isinstance(issue_number, int) or isinstance(issue_number, bool) or issue_number <= 0:
        raise LoopError("predecessor attestation ledger has an invalid issue number")
    if not isinstance(slug, str) or not ISSUE_ID_RE.fullmatch(slug):
        raise LoopError("predecessor attestation ledger has an invalid issue branch slug")
    closure = state.get("chunk", {}).get("closure", "complete")
    if closure not in CHUNK_CLOSURES:
        raise LoopError("predecessor attestation ledger has an invalid closure mode")
    if not isinstance(reviewed_head, str) or not FULL_GIT_SHA_RE.fullmatch(reviewed_head):
        raise LoopError("predecessor attestation requires a full reviewed PR head SHA")
    return predecessor_attestation_payload(
        manifest_id,
        chunk_id,
        spec_digest_value,
        openspec_digest_value,
        max_rounds,
        issue_number,
        f"agent/{slug}",
        closure,
        reviewed_head,
    )


def predecessor_attestation_body(payload: dict[str, Any]) -> str:
    """Encode attestation data in a comment body with one unambiguous payload."""

    return PREDECESSOR_ATTESTATION_PREFIX + canonical_json(payload) + PREDECESSOR_ATTESTATION_SUFFIX


def parse_predecessor_attestation(body: Any) -> dict[str, Any] | None:
    """Parse exactly one controller marker; ordinary discussion remains inert."""

    if not isinstance(body, str):
        return None
    stripped = body.strip()
    if not stripped.startswith(PREDECESSOR_ATTESTATION_PREFIX) or not stripped.endswith(
        PREDECESSOR_ATTESTATION_SUFFIX
    ):
        return None
    encoded = stripped[len(PREDECESSOR_ATTESTATION_PREFIX) : -len(PREDECESSOR_ATTESTATION_SUFFIX)]
    try:
        payload = json.loads(encoded)
    except json.JSONDecodeError:
        return None
    return payload if isinstance(payload, dict) else None


def matching_predecessor_attestations(
    comments: Any, expected: dict[str, Any], actor: str
) -> list[dict[str, Any]]:
    """Return exact controller-marker comments authored by the manifest actor."""

    if not isinstance(comments, list):
        return []
    matches: list[dict[str, Any]] = []
    for comment in comments:
        if not isinstance(comment, dict):
            continue
        author = comment.get("author")
        login = author.get("login") if isinstance(author, dict) else None
        if login != actor:
            continue
        if parse_predecessor_attestation(comment.get("body")) == expected:
            matches.append(comment)
    return matches


def require_exact_predecessor_attestation(
    pr: dict[str, Any], expected: dict[str, Any], actor: str, pr_number: int
) -> None:
    matches = matching_predecessor_attestations(pr.get("comments"), expected, actor)
    if not matches:
        raise LoopError(
            f"PR #{pr_number} lacks the exact controller predecessor attestation from {actor!r}"
        )
    if len(matches) != 1:
        raise LoopError(
            f"PR #{pr_number} has {len(matches)} matching predecessor attestations; expected exactly one"
        )


def require_predecessor_merges_ancestor(
    root: Path, proofs: Iterable[dict[str, Any]], revision: str, label: str
) -> None:
    """Require each verified source merge in a further local or remote revision."""

    if not isinstance(revision, str) or not FULL_GIT_SHA_RE.fullmatch(revision):
        raise LoopError(f"cannot verify predecessor ancestry: {label} is not a full Git SHA")
    for proof in proofs:
        merge_commit = proof.get("merge_commit")
        number = proof.get("number")
        if not isinstance(merge_commit, str) or not FULL_GIT_SHA_RE.fullmatch(merge_commit):
            raise LoopError("predecessor proof has no full merge commit")
        ancestry = run_command(
            root,
            ["git", "merge-base", "--is-ancestor", merge_commit, revision],
            check=False,
        )
        if ancestry.returncode != 0:
            raise LoopError(
                f"predecessor PR #{number} merge commit is not an ancestor of {label}"
            )


def require_predecessor_prs(root: Path, spec: dict[str, Any]) -> list[dict[str, Any]]:
    """Fail closed unless every pinned source run remains in both required histories."""

    bindings = predecessor_prs(spec)
    if not bindings:
        return []
    base_head = git(root, "rev-parse", "--verify", spec["base_ref"])
    current_head = git(root, "rev-parse", "HEAD")
    proofs: list[dict[str, Any]] = []
    for binding in bindings:
        number = binding["number"]
        pr = gh_json(
            root,
            [
                "pr",
                "view",
                str(number),
                "--repo",
                spec["repository"],
                "--json",
                "state,mergedAt,baseRefName,headRefName,headRefOid,body,mergeCommit,comments",
            ],
        )
        if not isinstance(pr, dict):
            raise LoopError(f"gh pr view #{number} returned an unexpected response")
        if pr.get("state") != "MERGED" or not isinstance(pr.get("mergedAt"), str) or not pr["mergedAt"]:
            raise LoopError(f"predecessor PR #{number} is not merged")
        if pr.get("baseRefName") != spec["base_branch"]:
            raise LoopError(
                f"predecessor PR #{number} targets {pr.get('baseRefName')!r}, not {spec['base_branch']!r}"
            )
        if pr.get("headRefName") != binding["source_branch"]:
            raise LoopError(
                f"predecessor PR #{number} branch does not match its pinned source_branch"
            )
        body = pr.get("body")
        if not isinstance(body, str):
            raise LoopError(f"predecessor PR #{number} has no readable body")
        try:
            validate_pr_body_closure(body, binding["issue_number"], binding["closure"])
        except LoopError as exc:
            raise LoopError(f"predecessor PR #{number} body does not match its pinned closure: {exc}") from exc
        live_head = pr.get("headRefOid")
        if not isinstance(live_head, str) or live_head.lower() != binding["reviewed_head"].lower():
            raise LoopError(f"predecessor PR #{number} head does not match its pinned reviewed_head")
        merge = pr.get("mergeCommit")
        merge_oid = merge.get("oid") if isinstance(merge, dict) else None
        if not isinstance(merge_oid, str) or merge_oid.lower() != binding["merge_commit"].lower():
            raise LoopError(f"predecessor PR #{number} merge commit does not match its pinned merge_commit")
        require_exact_predecessor_attestation(
            pr, predecessor_attestation_from_binding(binding), spec["actor"], number
        )
        proofs.append(
            {
                "number": number,
                "manifest_id": binding["manifest_id"],
                "chunk_id": binding["chunk_id"],
                "spec_digest": binding["spec_digest"].lower(),
                "openspec_digest": binding["openspec_digest"].lower(),
                "max_review_rounds": binding["max_review_rounds"],
                "issue_number": binding["issue_number"],
                "source_branch": binding["source_branch"],
                "closure": binding["closure"],
                "reviewed_head": binding["reviewed_head"].lower(),
                "merge_commit": binding["merge_commit"].lower(),
                "verified_at": utc_now(),
            }
        )
    require_predecessor_merges_ancestor(root, proofs, base_head, "resolved base_ref")
    require_predecessor_merges_ancestor(root, proofs, current_head, "current HEAD")
    return proofs


def plan_paths(root: Path, spec_path: Path, spec: dict[str, Any]) -> list[str]:
    """Repository-relative paths holding this run's plan: its manifest and OpenSpec change."""

    paths: list[str] = []
    try:
        manifest = spec_path.resolve().relative_to(root.resolve()).as_posix()
    except ValueError:
        manifest = ""
    # Only a manifest where manifests live is plan; `--spec` naming some other
    # tracked file must not open that file to the PR.
    if manifest.startswith(".claude/loop-specs/") and manifest.endswith(".yaml") and manifest.count("/") == 2:
        paths.append(manifest)
    if has_openspec(spec):
        paths.append(f"openspec/changes/{spec['openspec']['change']}")
    return paths


def ledger_plan_paths(state: dict[str, Any]) -> list[str]:
    """Plan paths a ledger recorded; older ledgers recorded none and gain none."""

    recorded = state.get("plan_paths")
    if isinstance(recorded, list) and all(isinstance(path, str) for path in recorded):
        return list(recorded)
    return []


def ledger_manifest_path(state: dict[str, Any]) -> str | None:
    return next((path for path in ledger_plan_paths(state) if path.startswith(".claude/loop-specs/")), None)


def progress_record_paths(state: dict[str, Any]) -> list[str]:
    """Plan files a run may keep editing after review: its task list and log.

    Everything else in the plan, the manifest included, is part of the change
    the panel reviewed and stays inside the content fingerprint.
    """

    change = state.get("openspec_change")
    if not isinstance(change, str) or not change or not ledger_plan_paths(state):
        return []
    return [f"openspec/changes/{change}/tasks.md", f"openspec/changes/{change}/agent-observations.md"]


def dirty_paths(root: Path) -> list[str]:
    """Paths with uncommitted changes, untracked files included, renames split."""

    result = run_command(
        root, ["git", "status", "--porcelain=v1", "-z", "--untracked-files=all", "--no-renames"], check=True
    )
    return [entry[3:] for entry in result.stdout.split("\0") if len(entry) > 3]


def is_ancestor(root: Path, ancestor: str, descendant: str) -> bool:
    return run_command(root, ["git", "merge-base", "--is-ancestor", ancestor, descendant]).returncode == 0


def change_fingerprint(root: Path, base_ref: str, commit: str, exclude: Iterable[str]) -> str:
    """Hash what a commit changes relative to its merge base, not where it sits.

    Rebasing a reviewed change onto a moved base, or merging the base into it,
    alters the SHA but not the change. Line numbers and blob ids are dropped;
    ten lines of context and each hunk's enclosing-declaration heading are
    kept, so a change moved to another place in a file moves the fingerprint.
    The excluded paths are progress records, not the reviewed change.
    """

    merge_base = git(root, "merge-base", base_ref, commit)
    args = ["git", "diff", "--no-color", "--no-ext-diff", "--no-renames", "--binary", "-U10", merge_base, commit, "--", "."]
    args.extend(f":(exclude){path}" for path in exclude)
    diff = run_command(root, args, check=True).stdout
    sections: list[str] = []
    for section in re.split(r"(?m)^(?=diff --git )", diff):
        if not section.strip():
            continue
        lines = [
            re.sub(r"^@@ [^@]* @@", "@@", line)
            for line in section.splitlines()
            if not line.startswith("index ")
        ]
        sections.append("\n".join(lines))
    return hashlib.sha256("\n".join(sorted(sections)).encode("utf-8")).hexdigest()


def ensure_commit(root: Path, remote: str, commit: str) -> None:
    """Make a provider-reported commit available locally before comparing it."""

    if run_command(root, ["git", "cat-file", "-e", f"{commit}^{{commit}}"]).returncode == 0:
        return
    fetched = run_command(root, ["git", "fetch", "--no-tags", "--quiet", remote, commit])
    if fetched.returncode != 0 or run_command(root, ["git", "cat-file", "-e", f"{commit}^{{commit}}"]).returncode != 0:
        raise LoopError(f"commit {commit} is not available locally and could not be fetched from {remote}")


def trusted_base_commit(root: Path, spec: dict[str, Any]) -> str:
    """The base branch tip as the provider reports it, available locally.

    Content equivalence is measured against this commit, not the manifest's
    `base_ref` or a remote-tracking ref: both are writable by the run, and a
    base placed at the candidate head would make every descendant of a reviewed
    commit look unchanged.
    """

    data = gh_json(root, ["api", f"repos/{spec['repository']}/commits/{spec['base_branch']}"])
    sha = data.get("sha") if isinstance(data, dict) else None
    if not isinstance(sha, str) or not FULL_GIT_SHA_RE.fullmatch(sha):
        raise LoopError(f"provider did not report a commit for base branch {spec['base_branch']!r}")
    ensure_commit(root, spec["remote"], sha)
    return sha


def reviewed_content_matches(
    root: Path, spec: dict[str, Any], state: dict[str, Any], reviewed_commit: str, head: str
) -> bool:
    """True when `head` is the reviewed commit or carries exactly its reviewed change.

    Fails closed: a commit that cannot be fetched or compared does not match.
    """

    if not re.fullmatch(r"[0-9a-fA-F]{40}", head) or not re.fullmatch(r"[0-9a-fA-F]{7,40}", reviewed_commit):
        return False
    try:
        version = ledger_digest_version(state)
        if head.lower() == reviewed_commit.lower():
            return True
        if len(reviewed_commit) < 40 and reviewed_commit_matches_head(root, reviewed_commit, head):
            return True
        ensure_commit(root, spec["remote"], head)
        ensure_commit(root, spec["remote"], reviewed_commit)
        base = trusted_base_commit(root, spec)
        exclude = progress_record_paths(state)
        if change_fingerprint(root, base, reviewed_commit, exclude) != change_fingerprint(
            root, base, head, exclude
        ):
            return False
        for path in exclude:
            if Path(path).name == "tasks.md" and normalized_tasks(root, reviewed_commit, path, version) != normalized_tasks(
                root, head, path, version
            ):
                print("WARN task wording changed after review; only checkbox state may change")
                return False
        moved = base_changes_under_review(root, base, state, reviewed_commit, head)
        if moved:
            print(
                "WARN the base changed files the reviewed change depends on ("
                + ", ".join(moved[:5])
                + "); run a revalidation round"
            )
            return False
        return True
    except LoopError as exc:
        print(f"WARN could not compare {head} with reviewed {reviewed_commit}: {exc}")
        return False


def blob_at(root: Path, commit: str, path: str) -> str | None:
    result = run_command(root, ["git", "show", f"{commit}:{path}"])
    return result.stdout if result.returncode == 0 else None


def normalized_tasks(root: Path, commit: str, path: str, version: int) -> str:
    """Use the ledger's original task semantics when comparing reviewed heads."""

    version = checked_openspec_digest_version(version)
    result = subprocess.run(["git", "show", f"{commit}:{path}"], cwd=root, capture_output=True)
    if result.returncode != 0:
        return ""
    try:
        content = result.stdout.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise LoopError(f"reviewed task artifact is not valid UTF-8: {path}") from exc
    if version < 3:
        # v1/v2 read artifacts in text mode, which normalized line endings.
        content = content.replace("\r\n", "\n").replace("\r", "\n")
    if version == 2:
        return TASK_CHECKBOX_RE_V2.sub(r"\1[ ]", content)
    if version == 3:
        return normalize_task_checkboxes(content)
    return content


LEAN_IMPORT_RE = re.compile(r"^(?:(?:public|private|meta)\s+)*import\s+(.+?)\s*$", re.MULTILINE)
PIN_PATHS = ("lake-manifest.json", "lean-toolchain", "lakefile.toml")


def base_changes_under_review(
    root: Path, base: str, state: dict[str, Any], reviewed_commit: str, head: str
) -> list[str]:
    """Files the base changed between the two merge bases that the change leans on.

    A clean rebase keeps the diff but can still change what it means, when the
    base edits a reviewed file elsewhere, a module it imports, or the pins.
    Only direct imports are followed; CI rebuilds everything else.
    """

    reviewed_base = git(root, "merge-base", base, reviewed_commit)
    head_base = git(root, "merge-base", base, head)
    if reviewed_base == head_base:
        return []
    changed = run_command(root, ["git", "diff", "--name-only", "--no-renames", reviewed_base, head_base], check=True)
    watched = list(state.get("chunk", {}).get("files", [])) + authorized_lift_targets(state) + list(PIN_PATHS)
    for path in state.get("chunk", {}).get("files", []):
        if not path.endswith(".lean"):
            continue
        for match in LEAN_IMPORT_RE.finditer(blob_at(root, head, path) or ""):
            for module in match.group(1).split():
                watched.append(module.replace(".", "/") + ".lean")
    return [path for path in changed.stdout.splitlines() if path and path_is_in_frozen_chunk(path, watched)]


def roadmap_gate_args(base_ref: str) -> list[str]:
    """Scope roadmap consistency failures to entries authored after base_ref."""

    return [
        # The interpreter running the controller, not whatever `python` means
        # on this host: several hosts ship only `python3`.
        sys.executable or "python3",
        "scripts/check_roadmap.py",
        "--require-api",
        f"--scope-to-diff={base_ref}",
    ]


def preflight(root: Path, spec_path: Path) -> int:
    try:
        spec = load_spec(spec_path, root, verify_owner_review=True)
    except LoopError as exc:
        print(f"FAIL preflight: {exc}")
        return 1
    if not spec["enabled"]:
        print(f"DISABLED preflight: spec {spec['id']} is not enabled; no remote actions run")
        return 2

    failures: list[str] = []
    warnings: list[str] = []
    repository = spec["repository"]
    remote = spec["remote"]
    try:
        # The plan (this manifest and its OpenSpec change) travels in the work
        # PR, so it may be uncommitted or committed on this branch. Anything
        # else uncommitted is unfinished work that does not belong to the run.
        plan = plan_paths(root, spec_path, spec)
        unplanned = [
            path
            for path in dirty_paths(root)
            if not path_is_in_frozen_chunk(path, plan)
        ]
        if unplanned:
            failures.append(
                "worktree has uncommitted changes outside this run's plan: " + ", ".join(unplanned[:10])
            )
        current_branch = git(root, "branch", "--show-current")
        current_head = git(root, "rev-parse", "HEAD")
        base_head = git(root, "rev-parse", "--verify", spec["base_ref"])
        if current_head != base_head and not is_ancestor(root, base_head, current_head):
            failures.append(
                f"HEAD {current_head} does not contain {spec['base_ref']} ({base_head}); "
                f"rebase or merge {spec['base_ref']} into the work branch"
            )
        if current_branch in {spec["base_branch"], ""}:
            failures.append("preflight must run from a detached or dedicated agent branch, not the protected base")
        remote_url = normalize_remote(git(root, "remote", "get-url", remote))
        if remote_url != repository.lower():
            failures.append(f"remote {remote!r} points to {remote_url!r}, expected {repository!r}")
    except LoopError as exc:
        failures.append(str(exc))

    try:
        login = gh_authenticated(root)
        print(f"PASS gh authentication: {login}")
        if login != spec["actor"]:
            failures.append(f"authenticated actor {login!r} is not the manifest actor {spec['actor']!r}")
    except LoopError as exc:
        failures.append(str(exc))

    prs: list[dict[str, Any]] = []
    try:
        prs = existing_prs(root, repository)
    except LoopError as exc:
        failures.append(str(exc))

    try:
        protected_checks = protected_check_names(root, spec)
        missing_protection = set(spec["runner"]["required_checks"]) - protected_checks
        if missing_protection:
            # Branch protection is the live authority on required checks; a
            # manifest naming a retired check must not stall the run.
            warnings.append(
                "manifest names checks branch protection no longer requires: "
                + ", ".join(sorted(missing_protection))
                + "; merge will require the live protected checks "
                + (", ".join(sorted(protected_checks)) or "(none)")
            )
        else:
            print("PASS base branch protection: required checks are configured")
    except LoopError as exc:
        failures.append(f"could not verify base branch protection: {exc}")

    try:
        predecessor_proofs = require_predecessor_prs(root, spec)
        for proof in predecessor_proofs:
            print(
                "PASS predecessor PR "
                f"#{proof['number']}: attested {proof['manifest_id']}/{proof['chunk_id']}"
            )
    except LoopError as exc:
        failures.append(str(exc))

    selected_numbers = {issue["number"] for issue in spec["issues"]}
    selected_dependencies = {
        dependency
        for issue in spec["issues"]
        for dependency in issue.get("depends_on", [])
        if dependency in selected_numbers
    }
    merge_authorized = True
    if spec["mode"] == "stack" and selected_dependencies:
        try:
            merge_authorized = effective_mutations(root, spec)["merge_pr"]
        except LoopError as exc:
            failures.append(str(exc))
            merge_authorized = False
    if spec["mode"] == "stack" and selected_dependencies and not merge_authorized:
        failures.append(
            "stack mode includes selected issue dependencies but mutations.merge_pr is false; "
            "enable merge explicitly or use independent issues"
        )

    for issue in spec["issues"]:
        number = issue["number"]
        try:
            live = issue_state(root, repository, number)
        except LoopError as exc:
            failures.append(str(exc))
            continue
        if live.get("state") != "OPEN":
            failures.append(f"issue #{number} is not open (state={live.get('state')})")
        labels = {
            label.get("name", "").lower()
            for label in live.get("labels", [])
            if isinstance(label, dict)
        }
        forbidden = labels & {"blocked", "epic", "research", "type:spike"}
        # An epic opt-in is an owner's eligibility decision; a branch-authored
        # manifest cannot make it for itself.
        allow_epic_issues = (
            set(spec.get("eligibility", {}).get("allow_epic_issues", []))
            if owner_reviewed_legacy_manifest(root, spec)
            else set()
        )
        if "epic" in forbidden and number in allow_epic_issues:
            forbidden.remove("epic")
            print(f"PASS issue #{number}: epic label explicitly authorized by manifest")
        if forbidden:
            failures.append(f"issue #{number} has ineligible labels: {', '.join(sorted(forbidden))}")
        blocked_by = blocked_by_entries(live)
        if blocked_by:
            failures.append(f"issue #{number} has live blocked-by dependencies")
        for dependency in issue.get("depends_on", []):
            if dependency in selected_numbers:
                continue
            try:
                dependency_state = issue_state(root, repository, dependency)
            except LoopError as exc:
                failures.append(str(exc))
                continue
            if dependency_state.get("state") != "CLOSED":
                failures.append(f"issue #{number} depends on open issue #{dependency}")
        expected_branch = f"agent/{issue['slug']}"
        # An open PR on the planned branch is this run's own PR being resumed.
        # A merged or closed one is history: refusing it made every branch
        # name single-use, so each progress slice needed a new manifest.
        for pr in prs:
            own_branch = pr.get("headRefName") == expected_branch
            if own_branch and pr.get("state") == "OPEN":
                author = pr.get("author")
                login = author.get("login") if isinstance(author, dict) else None
                if login != spec["actor"]:
                    failures.append(
                        f"open PR #{pr.get('number')} on planned branch {expected_branch} is by {login!r}, "
                        f"not the manifest actor {spec['actor']!r}"
                    )
                else:
                    print(f"PASS resuming open PR #{pr.get('number')} on planned branch {expected_branch}")
            closing = pr.get("closingIssuesReferences") or []
            if any(reference.get("number") == number for reference in closing if isinstance(reference, dict)):
                if pr.get("state") == "OPEN" and not own_branch:
                    failures.append(
                        f"issue #{number} already has open PR #{pr.get('number')} "
                        f"from another branch ({pr.get('headRefName')})"
                    )

    openspec_validation = spec["openspec"].get("validation", "structural") if has_openspec(spec) else None
    if openspec_validation is None:
        print("PASS no OpenSpec change: the issue body and manifest acceptance are the specification")
    elif openspec_validation in {"cli-advisory", "cli-required"} and shutil.which("openspec") is None:
        # The structural check above already ran; a missing Node tool is a
        # host gap to log, not a reason to stop an otherwise valid run.
        warnings.append("OpenSpec CLI is not installed; structural validation passed and was used instead")
    elif openspec_validation in {"cli-advisory", "cli-required"}:
        cli = run_command(root, ["openspec", "validate", spec["openspec"]["change"], "--strict", "--no-interactive"], check=False)
        if cli.returncode != 0:
            detail = (cli.stdout or cli.stderr).strip().splitlines()
            message = detail[-1] if detail else "OpenSpec CLI validation failed"
            if openspec_validation == "cli-required":
                failures.append(f"OpenSpec CLI validation failed: {message}")
            else:
                warnings.append(f"OpenSpec CLI validation advisory failure: {message}")
        elif cli.stdout.strip():
            print("PASS OpenSpec CLI validation")
    elif openspec_validation == "structural":
        print("PASS OpenSpec structural validation")

    roadmap_gate = spec.get("roadmap_gate", "required")
    if roadmap_gate != "required" and not owner_reviewed_legacy_manifest(root, spec):
        warnings.append(f"roadmap_gate {roadmap_gate!r} is owner policy; a branch-authored manifest runs it as required")
        roadmap_gate = "required"
    if roadmap_gate != "disabled":
        roadmap = run_command(root, roadmap_gate_args(spec["base_ref"]), check=False)
        if roadmap.returncode != 0:
            message = (roadmap.stdout or roadmap.stderr).strip().splitlines()
            detail = message[-1] if message else "roadmap gate failed"
            if roadmap_gate == "required":
                failures.append(f"roadmap gate failed: {detail}")
            else:
                warnings.append(f"roadmap gate advisory failure: {detail}")

    if warnings:
        for warning in warnings:
            print(f"WARN {warning}")
    if failures:
        for failure in failures:
            print(f"FAIL {failure}")
        print(f"PREFLIGHT FAIL ({len(failures)} failure(s))")
        return 1
    print("PREFLIGHT PASS: branch contains base, authenticated provider, eligible issues, and gates are ready")
    return 0


def state_path(root: Path, spec: dict[str, Any], requested: str | None, chunk_id: str) -> Path:
    directory = repo_path(root, requested or spec.get("state_dir", ".loop-runs"))
    ensure_inside(root, directory)
    canonical_runs = canonical_ledger_root(root)
    try:
        directory.relative_to(canonical_runs)
    except ValueError as exc:
        raise LoopError("ledger state directories must remain under the repository's .loop-runs root") from exc
    target = ensure_inside(root, directory / f"{chunk_id}.json")
    try:
        target.relative_to(canonical_runs)
    except ValueError as exc:
        raise LoopError("ledger files must resolve under the repository's .loop-runs root") from exc
    return target


def refuse_renamed_ledger(
    root: Path,
    spec: dict[str, Any],
    requested_state_dir: str | None,
    number: int,
    chunk_id: str,
    expected: Path,
) -> None:
    """Refuse another ledger for this issue/slug/chunk in any linked worktree."""
    slug = issue_entry(spec, number)["slug"]
    for candidate in ordinary_ledger_files(root):
        if candidate.resolve() == expected.resolve():
            continue
        try:
            data = json.loads(candidate.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        if not isinstance(data, dict):
            continue
        if data.get("schema") != f"{RUN_SCHEMA}/ledger":
            continue
        issue_identity = data.get("issue")
        chunk_identity = data.get("chunk")
        identity_matches = (
            isinstance(issue_identity, dict)
            and issue_identity.get("number") == number
            and issue_identity.get("slug") == slug
            and isinstance(chunk_identity, dict)
            and chunk_identity.get("id") == chunk_id
        )
        if identity_matches:
            raise LoopError(
                f"chunk {chunk_id!r} for issue #{number} ({slug}) already has a ledger at "
                f"{candidate} with status {data.get('status')!r}; "
                "renaming a ledger or switching worktrees does not start a fresh review"
            )


def require_selected_dependencies_passed(
    root: Path,
    spec: dict[str, Any],
    issue: dict[str, Any],
    requested_state_dir: str | None,
) -> None:
    """Require every selected predecessor chunk to have a passing ledger."""

    selected_numbers = {entry["number"] for entry in spec["issues"]}
    for dependency in issue.get("depends_on", []):
        if dependency not in selected_numbers:
            continue
        dependency_issue = issue_entry(spec, dependency)
        for dependency_chunk in dependency_issue["chunks"]:
            path = state_path(root, spec, requested_state_dir, dependency_chunk["id"])
            if not path.is_file():
                raise LoopError(
                    f"issue #{issue['number']} depends on chunk {dependency_chunk['id']!r}, "
                    "but its review ledger does not exist"
                )
            dependency_state = load_state(path)
            if (
                dependency_state.get("spec_digest") != digest(spec)
                or not ledger_openspec_matches(root, spec, dependency_state)
            ):
                raise LoopError(
                    f"issue #{issue['number']} depends on a ledger for {dependency_chunk['id']!r} "
                    "that was created from a different manifest or OpenSpec plan"
                )
            if dependency_state.get("status") != "passed":
                raise LoopError(
                    f"issue #{issue['number']} depends on chunk {dependency_chunk['id']!r}, "
                    f"whose ledger status is {dependency_state.get('status')!r}"
                )
            if dependency_state.get("chunk", {}).get("closure") != "complete":
                raise LoopError(
                    f"issue #{issue['number']} depends on progress chunk {dependency_chunk['id']!r}; "
                    "a progress ledger cannot unlock a downstream issue"
                )
            dependency_live = issue_state(root, spec["repository"], dependency)
            if str(dependency_live.get("state", "")).upper() != "CLOSED":
                raise LoopError(
                    f"issue #{issue['number']} depends on issue #{dependency} remaining open; "
                    "the upstream complete chunk must be merged and closed first"
                )


def load_state(path: Path) -> dict[str, Any]:
    registered = registered_state_at(path)
    if registered is not None:
        _, record = registered
        state = record["ledger"]
        validate_registered_state(record, state)
        return state
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise LoopError(f"ledger state does not exist: {path}") from exc
    except (OSError, json.JSONDecodeError) as exc:
        raise LoopError(f"could not read ledger state {path}: {exc}") from exc
    if not isinstance(data, dict) or data.get("schema") != f"{RUN_SCHEMA}/ledger":
        raise LoopError(f"invalid ledger state schema: {path}")
    if "recovery" in data:
        raise LoopError("recovery ledger is not at its registered canonical path")
    root_text = git(path.resolve().parent, "rev-parse", "--show-toplevel", check=False)
    if root_text:
        for _, record in recovery_registry(Path(root_text)):
            if data.get("issue", {}).get("number") == record.get("issue"):
                raise LoopError("registered recovery objective cannot be accessed as a new legacy ledger")
    return data


def write_json(path: Path, value: Any) -> None:
    """Atomically persist canonical recovery state before its compatibility view."""
    if isinstance(value, dict) and "recovery" in value:
        registered = registered_state_at(path)
        if registered is None:
            raise LoopError("cannot write an unregistered recovery ledger")
        registry_path, record = registered
        validate_registered_state(record, value)
        record["ledger"] = value
        atomic_json(registry_path, record)
    atomic_json(path, value)


def atomic_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=path.parent, delete=False) as stream:
            temporary = Path(stream.name)
            stream.write(json.dumps(value, indent=2, sort_keys=True) + "\n")
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        if temporary is not None and temporary.exists():
            temporary.unlink()


def register_recovery(root: Path, spec_path: Path, spec: dict[str, Any], path: Path, state: dict[str, Any]) -> None:
    policy = loop_recovery.validate_policy(spec["recovery"])
    history = []
    for entry in policy["history"]:
        source = repo_path(root, entry["path"])
        raw = source.read_bytes()
        if hashlib.sha256(raw).hexdigest() != entry["sha256"]:
            raise LoopError(f"historical ledger digest mismatch: {source}")
        history.append(read_json_object(source))
    loop_recovery.initialize(state, policy, history=history)
    registry_path = recovery_directory(root) / (digest([spec["repository"].casefold(), state["issue"]["number"]]) + ".json")
    record = {
        "schema": "loop-objective-registry/v1",
        "repository": spec["repository"].casefold(),
        "issue": state["issue"]["number"],
        "objective_id": policy["objective_id"],
        "repo_root": str(root.resolve()),
        "state_file": str(path.resolve()),
        "spec_path": str(spec_path.resolve()),
        "spec_digest": digest(spec),
        "openspec_digest": openspec_digest(root, spec, ledger_digest_version(state)),
        "ledger": state,
    }
    validate_registered_state(record, state)
    # The shared record owns the state; the user-facing path is a recoverable view.
    atomic_json(registry_path, record)
    atomic_json(path, state)


def ledger_init(root: Path, spec_path: Path, number: int, chunk_id: str, requested_state_dir: str | None) -> int:
    try:
        spec = load_spec(spec_path, root, verify_owner_review=True)
        issue, chunk = chunk_entry(spec, number, chunk_id)
        require_legacy_issue_open(root, spec, number)
        predecessor_proofs = require_predecessor_prs(root, spec)
        require_selected_dependencies_passed(root, spec, issue, requested_state_dir)
        path = state_path(root, spec, requested_state_dir, chunk_id)
        if "recovery" in spec:
            registered = recovery_record(root, spec)
            if registered is not None:
                _, record = registered
                if Path(record["state_file"]).resolve() != path.resolve() or record["spec_digest"] != digest(spec):
                    raise LoopError("objective is already registered; changing path or manifest cannot reset it")
                validate_registered_state(record, record["ledger"])
                atomic_json(path, record["ledger"])
                print(f"PASS recovery objective already initialized: {path}")
                return 0
        else:
            for _, record in recovery_registry(root):
                if record["repository"].casefold() == spec["repository"].casefold() and record["issue"] == number:
                    raise LoopError("registered recovery objective cannot be restarted under a legacy manifest")
        refuse_renamed_ledger(root, spec, requested_state_dir, number, chunk_id, path)
        if path.exists():
            existing = load_state(path)
            if existing.get("spec_digest") != digest(spec) or not ledger_openspec_matches(root, spec, existing):
                raise LoopError(f"ledger already exists with a different spec: {path}")
            print(f"PASS ledger already initialized: {path}")
            return 0
        state = {
            "schema": f"{RUN_SCHEMA}/ledger",
            "spec_id": spec["id"],
            "spec_digest": digest(spec),
            "openspec_change": spec["openspec"]["change"] if has_openspec(spec) else None,
            "openspec_digest": openspec_digest(root, spec),
            "openspec_digest_version": OPENSPEC_DIGEST_VERSION,
            "base_ref": spec["base_ref"],
            "base_branch": spec["base_branch"],
            "repository": spec["repository"],
            "remote": spec["remote"],
            "base_commit_at_init": pinned_base_commit({"repo_root": str(root), "base_ref": spec["base_ref"]}),
            "plan_paths": plan_paths(root, spec_path, spec),
            # Without OpenSpec the issue body is the specification; record
            # which version of it the panel reviewed against.
            "issue_body_digest": None if has_openspec(spec) else issue_body_digest(root, spec, number),
            "predecessor_prs": predecessor_proofs,
            "issue": {"number": issue["number"], "slug": issue["slug"]},
            "chunk": {
                "id": chunk["id"],
                "scope": chunk["scope"],
                "files": list(chunk["files"]),
                "lift_targets": list(chunk.get("lift_targets", [])),
                "requirements": list(chunk["requirements"]),
                "acceptance": list(chunk["acceptance"]),
                "closure": chunk.get("closure", "complete"),
            },
            "repo_root": str(root),
            "reviewers": list(spec["review"]["reviewers"]),
            "max_review_rounds": spec["limits"]["max_review_rounds_per_chunk"],
            "no_rechunking": True,
            "status": "initialized",
            "created_at": utc_now(),
            "rounds": [],
            "ci_failure_repairs": [],
        }
        if "recovery" in spec:
            if path.exists():
                raise LoopError("legacy state must be adopted through the manifest's pinned history inventory")
            register_recovery(root, spec_path, spec, path, state)
        else:
            write_json(path, state)
        print(f"PASS ledger initialized: {path}")
        return 0
    except (LoopError, loop_recovery.RecoveryError) as exc:
        print(f"FAIL ledger init: {exc}")
        return 1


def backlog_records(state: dict[str, Any], lift_target: str) -> bool:
    """True when the generalization backlog already mentions this lift target.

    A lift recorded only in the gitignored ledger dies with the run. The backlog
    is tracked, so this is the check that makes a lift survive to the next one.
    """
    root = state.get("repo_root")
    if not root:
        # ledgers created before repo_root was recorded cannot be verified;
        # fail closed rather than silently accepting an unrecorded lift
        return False
    try:
        text = (Path(root) / BACKLOG_PATH).read_text(encoding="utf-8")
    except OSError:
        return False
    return lift_target.strip() in text


def latest_round(state: dict[str, Any]) -> dict[str, Any] | None:
    rounds = state.get("rounds", [])
    return rounds[-1] if rounds else None


def pinned_base_commit(state: dict[str, Any]) -> str | None:
    """The base commit a round was reviewed against, for the audit trail.

    Resolved locally, so it is evidence, not authority: publication measures
    the change against the provider's base tip instead.
    """

    root, base_ref = state.get("repo_root"), state.get("base_ref")
    if not root or not base_ref:
        return None
    result = run_command(Path(root), ["git", "rev-parse", "--verify", "--end-of-options", f"{base_ref}^{{commit}}"])
    return result.stdout.strip() if result.returncode == 0 else None


def is_revalidation(round_state: dict[str, Any]) -> bool:
    return round_state.get("kind") == "revalidation"


def improvement_rounds_used(state: dict[str, Any]) -> int:
    """Rounds charged to the critique/improve cap; revalidations are not."""

    return sum(1 for round_state in state.get("rounds", []) if not is_revalidation(round_state))


def require_revalidation_needed(state: dict[str, Any], commit: str) -> None:
    """Admit only the same reviewed change carried across an in-scope base move."""

    passed = latest_round(state)
    root_text = state.get("repo_root")
    if passed is None or not root_text:
        raise LoopError("ledger has no passing round or repository to revalidate against")
    root = Path(root_text)
    candidate = git(root, "rev-parse", "--verify", "--end-of-options", f"{commit}^{{commit}}", check=False)
    if not FULL_GIT_SHA_RE.fullmatch(candidate):
        raise LoopError(f"ledger is passed; commit {commit} is not a local commit to revalidate")
    reviewed_commit = str(passed.get("commit", ""))
    if not FULL_GIT_SHA_RE.fullmatch(reviewed_commit):
        reviewed_commit = git(root, "rev-parse", "--verify", "--end-of-options", f"{reviewed_commit}^{{commit}}", check=False)
    if not FULL_GIT_SHA_RE.fullmatch(reviewed_commit):
        raise LoopError("passed round does not identify a commit to revalidate")
    if reviewed_commit_matches_head(root, reviewed_commit, candidate):
        raise LoopError("ledger is passed for this exact commit; no further review is needed")

    provider = revalidation_provider(state)
    ensure_commit(root, provider["remote"], candidate)
    ensure_commit(root, provider["remote"], reviewed_commit)
    base = trusted_base_commit(root, provider)
    prior_base = str(passed.get("base_commit", ""))
    if not FULL_GIT_SHA_RE.fullmatch(prior_base) or prior_base.lower() == base.lower():
        raise LoopError(
            "changed implementation cannot use free revalidation; use exact required-check failure evidence "
            "to admit a charged CI repair"
        )
    ensure_commit(root, provider["remote"], prior_base)
    if not is_ancestor(root, prior_base, base):
        raise LoopError("protected base did not advance from the base recorded by the passing round")
    if not is_ancestor(root, base, candidate):
        raise LoopError("revalidation candidate does not carry the current protected base")

    exclude = progress_record_paths(state)
    if change_fingerprint(root, base, reviewed_commit, exclude) != change_fingerprint(
        root, base, candidate, exclude
    ):
        raise LoopError(
            "changed implementation cannot use free revalidation; use exact required-check failure evidence "
            "to admit a charged CI repair"
        )
    for path in exclude:
        if Path(path).name == "tasks.md" and normalized_tasks(
            root, reviewed_commit, path, ledger_digest_version(state)
        ) != normalized_tasks(root, candidate, path, ledger_digest_version(state)):
            raise LoopError("revalidation changed task wording; use the charged CI-repair path")
    moved = base_changes_under_review(root, base, state, reviewed_commit, candidate)
    if not moved:
        raise LoopError(
            "changed commit is not a protected-base revalidation; use exact required-check failure evidence "
            "to admit a charged CI repair"
        )
    used = sum(1 for round_state in state.get("rounds", []) if is_revalidation(round_state))
    if used >= MAX_REVALIDATION_ROUNDS:
        raise LoopError(f"revalidation limit reached ({MAX_REVALIDATION_ROUNDS}); the passed change cannot be reopened again")


def revalidation_provider(state: dict[str, Any]) -> dict[str, str]:
    """Read old ledger provider identity without rewriting its stored bytes."""
    root_text = state.get("repo_root")
    base_ref = state.get("base_ref")
    if not isinstance(root_text, str) or not isinstance(base_ref, str):
        raise LoopError("ledger predates provider identity and has no base ref for read-compatible revalidation")
    root = Path(root_text)
    remotes = git(root, "remote", check=False).splitlines()
    remote = state.get("remote")
    if not isinstance(remote, str) or not remote:
        matching = [name for name in remotes if base_ref.startswith(name + "/")]
        if matching:
            remote = max(matching, key=len)
        elif "/" in base_ref:
            remote = base_ref.split("/", 1)[0]
        else:
            raise LoopError("cannot derive the ledger remote from its recorded base ref")
    if not base_ref.startswith(remote + "/"):
        raise LoopError("ledger remote does not match its recorded base ref")
    base_branch = state.get("base_branch")
    if not isinstance(base_branch, str) or not base_branch:
        base_branch = base_ref[len(remote) + 1:]
    if not base_branch or base_ref != f"{remote}/{base_branch}":
        raise LoopError("ledger base branch does not match its recorded base ref")

    repository = state.get("repository")
    if not isinstance(repository, str) or not repository:
        urls = git(root, "remote", "get-url", "--all", remote, check=False).splitlines()
        urls += git(root, "remote", "get-url", "--push", "--all", remote, check=False).splitlines()
        repositories = {normalize_remote(url) for url in urls if url.strip()}
        if len(repositories) != 1:
            raise LoopError("cannot derive one repository identity from the ledger remote")
        repository = repositories.pop()
    return {"repository": repository, "remote": remote, "base_branch": base_branch}


def ensure_review_round(state: dict[str, Any], commit: str) -> dict[str, Any]:
    if state.get("status") == "repair_exhausted":
        raise LoopError("CI-repair review cap is exhausted; this chunk is terminal")
    if "recovery" in state:
        loop_recovery.reserve_round(state, commit)
        if state["recovery"]["phase"] == "parked":
            raise LoopError(state["recovery"]["park_reason"])
        return state["rounds"][-1]
    current = latest_round(state)
    if current is not None and current.get("adjudication") is None:
        if current.get("commit") != commit:
            raise LoopError(
                f"round {current.get('number')} is still open for commit {current.get('commit')}; "
                "adjudicate it before reviewing a different commit"
            )
        return current
    revalidation = state.get("status") == "passed"
    if revalidation:
        require_revalidation_needed(state, commit)
    elif improvement_rounds_used(state) + 1 > state["max_review_rounds"]:
        raise LoopError(
            "review round cap reached; no further critique/improve iteration is permitted"
        )
    current = {
        "number": (current.get("number", 0) + 1) if current else 1,
        "commit": commit,
        "reviews": [],
        "adjudication": None,
    }
    if revalidation:
        current["kind"] = "revalidation"
    if state.get("base_ref"):
        current["base_commit"] = pinned_base_commit(state)
    state["rounds"].append(current)
    state["status"] = "reviewing"
    return current


CONTRACT_VERDICT_TOKENS = {
    "pass": "PASS",
    "pass_with_lift": "PASS_WITH_LIFT",
    "needs_changes": "NEEDS_CHANGES",
    "blocked": "BLOCKED",
}
# Verdicts that let a chunk advance. `pass_with_lift` says the code under review
# is correct AND that a generalization was found whose target lies outside the
# frozen file list. Recovery mode charges every allocated panel, including lifts.
PASSING_VERDICTS = {"pass", "pass_with_lift"}
REVIEW_VERDICTS = set(CONTRACT_VERDICT_TOKENS)
BACKLOG_PATH = "docs/architecture/generalization-backlog.md"


def read_reviewer_output(finding_file: Path) -> tuple[str, str]:
    """Read a reviewer's verbatim final message and return (text, sha256).

    The reviewer's own output is the evidence. A summary written by the
    orchestrator is not, because it is indistinguishable from the orchestrator
    having reviewed the diff itself.
    """
    try:
        text = finding_file.read_text(encoding="utf-8")
    except OSError as exc:
        raise LoopError(f"cannot read reviewer output {str(finding_file)!r}: {exc}") from exc
    if not text.strip():
        raise LoopError(
            f"reviewer output {str(finding_file)!r} is empty; "
            "an unreadable reviewer message cannot pass; retain any reserved round and retry the missing role"
        )
    return text, hashlib.sha256(text.encode("utf-8")).hexdigest()


def ledger_record_review(
    state_file: Path,
    reviewer: str,
    commit: str,
    verdict: str,
    finding: str | None,
    finding_file: Path | None = None,
    lift_target: str | None = None,
    resolutions_file: Path | None = None,
) -> int:
    try:
        state = load_state(state_file)
        if state.get("status") in {"blocked", "repair_exhausted"} or (
            state.get("status") == "passed" and "recovery" in state
        ):
            raise LoopError(f"ledger is terminal with status {state['status']!r}; no further reviews are allowed")
        if reviewer not in state["reviewers"]:
            raise LoopError(f"reviewer {reviewer!r} is not authorized by this ledger")
        if verdict not in REVIEW_VERDICTS:
            raise LoopError(
                "review verdict must be " + ", ".join(sorted(REVIEW_VERDICTS))
            )
        if verdict == "pass_with_lift" and not (lift_target or "").strip():
            raise LoopError(
                "pass_with_lift requires --lift-target naming the module or path the "
                "generalization belongs in; an unaddressed lift is not a finding"
            )
        if verdict != "pass_with_lift" and (lift_target or "").strip():
            raise LoopError("--lift-target is only meaningful with verdict pass_with_lift")
        if not re.fullmatch(r"[0-9a-fA-F]{7,64}", commit):
            raise LoopError("commit must be a hexadecimal git object id")
        round_state = ensure_review_round(state, commit)
        if any(item.get("reviewer") == reviewer for item in round_state["reviews"]):
            raise LoopError(f"reviewer {reviewer!r} already submitted for round {round_state['number']}")
        finding_text = ""
        finding_digest = ""
        if finding_file is not None:
            finding_text, finding_digest = read_reviewer_output(finding_file)
            token = CONTRACT_VERDICT_TOKENS[verdict]
            if not re.search(rf"\b{token}\b", finding_text, re.I):
                raise LoopError(
                    f"reviewer output does not state the recorded verdict {token}; "
                    "record the verdict the reviewer actually reached"
                )
        resolutions = {}
        if "recovery" in state:
            loop_recovery.validate_review(commit, verdict, finding_text)
            if verdict == "pass_with_lift":
                canonical_recovery_path(str(lift_target))
            git(Path(state["repo_root"]), "cat-file", "-e", f"{commit}^{{commit}}")
            if resolutions_file is not None:
                resolutions = read_json_object(resolutions_file)
        elif resolutions_file is not None:
            raise LoopError("resolution evidence requires a recovery-managed objective")
        round_state["reviews"].append(
            {
                "reviewer": reviewer,
                "verdict": verdict,
                "finding": finding or "",
                "finding_text": finding_text,
                "finding_digest": finding_digest,
                "finding_source": str(finding_file) if finding_file is not None else "",
                "lift_target": (lift_target or "").strip(),
                "recorded_at": utc_now(),
                **({"resolutions": resolutions} if "recovery" in state else {}),
            }
        )
        write_json(state_file, state)
        print(f"PASS review recorded: {reviewer} round={round_state['number']} commit={commit}")
        return 0
    except (LoopError, loop_recovery.RecoveryError) as exc:
        print(f"FAIL ledger record-review: {exc}")
        return 1


def ledger_adjudicate(state_file: Path, verdict: str, note: str | None) -> int:
    try:
        state = load_state(state_file)
        if state.get("status") == "repair_exhausted":
            raise LoopError("CI-repair review cap is exhausted; this chunk is terminal")
        if verdict not in REVIEW_VERDICTS:
            raise LoopError(
                "adjudication must be " + ", ".join(sorted(REVIEW_VERDICTS))
            )
        current = latest_round(state)
        if current is None:
            raise LoopError("cannot adjudicate before reviews are recorded")
        if current.get("adjudication") is not None:
            raise LoopError(f"round {current['number']} is already adjudicated")
        recorded = {item.get("reviewer") for item in current["reviews"]}
        missing = set(state["reviewers"]) - recorded
        if missing:
            raise LoopError(f"cannot adjudicate; missing reviewers: {', '.join(sorted(missing))}")
        if verdict in PASSING_VERDICTS and any(
            item.get("verdict") not in PASSING_VERDICTS for item in current["reviews"]
        ):
            raise LoopError(
                "pass adjudication requires every reviewer verdict to be pass or pass_with_lift"
            )
        if "recovery" in state and verdict in PASSING_VERDICTS:
            require_recovery_lift_backlog(state)
        lifts = [
            item for item in current["reviews"] if item.get("verdict") == "pass_with_lift"
        ]
        if lifts and verdict == "pass":
            raise LoopError(
                "this round carries lift findings; adjudicate pass_with_lift so the "
                "handoff report and the backlog agree with the ledger"
            )
        if verdict == "pass_with_lift":
            if not lifts:
                raise LoopError(
                    "pass_with_lift adjudication requires at least one reviewer lift finding"
                )
            unrecorded = sorted(
                str(item.get("lift_target"))
                for item in lifts
                if "recovery" not in state and not backlog_records(state, str(item.get("lift_target")))
            )
            if unrecorded:
                raise LoopError(
                    "cannot adjudicate; these lift targets are absent from "
                    + BACKLOG_PATH
                    + ": "
                    + ", ".join(unrecorded)
                    + ". Append them before passing the chunk, or the finding dies "
                    "with this run"
                )
        if verdict != "blocked":
            uncaptured = sorted(
                str(item.get("reviewer"))
                for item in current["reviews"]
                if not item.get("finding_digest")
            )
            if uncaptured:
                raise LoopError(
                    "cannot adjudicate; no captured reviewer output for: "
                    + ", ".join(uncaptured)
                    + ". Re-dispatch the reviewer and record its verbatim message with "
                    "--finding-file, or adjudicate this round blocked"
                )
        if verdict == "needs_changes" and improvement_rounds_used(state) >= state["max_review_rounds"]:
            verdict = "blocked"
            note = (note + " | " if note else "") + "review-round cap reached; stop without another iteration"
        current["adjudication"] = {"verdict": verdict, "note": note or "", "recorded_at": utc_now()}
        state["status"] = {
            "pass": "passed",
            "pass_with_lift": "passed",
            "needs_changes": "improve_required",
            "blocked": "blocked",
        }[verdict]
        if "recovery" in state:
            loop_recovery.after_adjudication(state)
        write_json(state_file, state)
        print(f"PASS adjudicated: round={current['number']} verdict={verdict}")
        return 0
    except (LoopError, loop_recovery.RecoveryError) as exc:
        print(f"FAIL ledger adjudicate: {exc}")
        return 1


def ledger_show(state_file: Path) -> int:
    try:
        state = load_state(state_file)
    except LoopError as exc:
        print(f"FAIL ledger show: {exc}")
        return 1
    print(json.dumps(state, indent=2, sort_keys=True))
    return 0


def recovery_command(
    command: str, ledger: Path, *, commit: str | None = None,
    file: Path | None = None, reason: str | None = None,
) -> int:
    state = load_state(ledger)
    if "recovery" not in state:
        raise LoopError("objective has no recovery policy; adopt history through a new configured manifest")
    if command == "start-round":
        root = Path(state["repo_root"])
        if git(root, "rev-parse", "HEAD") != commit:
            raise LoopError("reserve the exact current commit before dispatching its panel")
        loop_recovery.reserve_round(state, str(commit))
    elif command == "submit-plan":
        loop_recovery.submit_plan(state, read_json_object(file))
    elif command == "review-plan":
        loop_recovery.review_plan(state, read_json_object(file))
    elif command == "resume":
        loop_recovery.resume(state)
    elif command == "exhaust":
        loop_recovery.abandon(state, str(reason))
    elif command != "next":
        raise LoopError(f"unknown recovery command: {command}")
    if command != "next":
        write_json(ledger, state)
    print(json.dumps(loop_recovery.next_action(state), indent=2, sort_keys=True))
    return 0


def recovery_publication_state(root: Path, spec: dict[str, Any], ledger: Path | None = None) -> dict[str, Any] | None:
    if "recovery" not in spec:
        # A changed/legacy manifest is not a way around a registered objective.
        selected = {item["number"] for item in spec["issues"]}
        for _, record in recovery_registry(root):
            if record["repository"].casefold() == spec["repository"].casefold() and record["issue"] in selected:
                raise LoopError("registered recovery objective requires its original manifest")
        return None
    registered = recovery_record(root, spec)
    if registered is None:
        raise LoopError("recovery objective is not initialized")
    _, record = registered
    if record["spec_digest"] != digest(spec) or Path(record["repo_root"]).resolve() != root.resolve():
        raise LoopError("publication must use the registered manifest and checkout")
    canonical = Path(record["state_file"])
    if ledger is not None and ledger.resolve() != canonical.resolve():
        raise LoopError("publication ledger is not the registered objective")
    state = load_state(canonical)
    loop_recovery.require_publishable(state)
    require_recovery_lift_backlog(state)
    remote = normalize_remote(git(root, "remote", "get-url", spec["remote"]))
    if remote != spec["repository"].lower():
        raise LoopError("publication remote does not match the authorized repository")
    return state


def canonical_recovery_path(path: str) -> str:
    value = path.rstrip("/")
    if (not value or value.startswith("/") or "\\" in value or ":" in value
            or any(part in {"", ".", ".."} for part in value.split("/"))):
        raise LoopError(f"non-canonical recovery scope path: {path!r}")
    return value


def recovery_lift_reviews(state: dict[str, Any]) -> list[dict[str, Any]]:
    envelope = state.get("recovery", {})
    snapshots = [entry["snapshot"] for kind in ("history", "attempts")
                 for entry in envelope.get(kind, [])] + [state]
    return [review for snapshot in snapshots for row in snapshot.get("rounds", [])
            for review in row["reviews"] if review.get("verdict") == "pass_with_lift"]


def read_reviewed_text(root: Path, commit: str, path: str) -> str:
    """Read an ordinary UTF-8 Git blob from an explicit reviewed commit only."""
    if not re.fullmatch(r"[0-9a-f]{40}", commit) or git(root, "cat-file", "-t", commit) != "commit":
        raise LoopError("reviewed artifact requires an exact commit object")
    path = canonical_recovery_path(path)
    tree = run_command(root, ["git", "ls-tree", "-z", commit, "--", path], check=True)
    entries = [entry for entry in tree.stdout.split("\0") if entry]
    if len(entries) != 1 or "\t" not in entries[0]:
        raise LoopError(f"reviewed artifact is absent: {commit}:{path}")
    metadata, actual_path = entries[0].split("\t", 1)
    parts = metadata.split()
    if actual_path != path or len(parts) != 3 or parts[0] not in {"100644", "100755"} or parts[1] != "blob":
        raise LoopError(f"reviewed artifact must be an ordinary tracked file: {path}")
    blob = subprocess.run(["git", "cat-file", "blob", parts[2]], cwd=root,
                          capture_output=True, check=False)
    if blob.returncode != 0:
        raise LoopError(f"cannot read reviewed artifact: {commit}:{path}")
    try:
        text = blob.stdout.decode("utf-8", errors="strict")
    except UnicodeDecodeError as exc:
        raise LoopError(f"reviewed artifact is not UTF-8 text: {path}") from exc
    if "\0" in text:
        raise LoopError(f"reviewed artifact contains binary text: {path}")
    return text


def recovery_backlog_targets(text: str) -> set[str]:
    """Recognize complete column-zero backlog rows, not prose or examples.

    Optional single backticks quote field values. Fenced code and HTML comments
    carry no dispositions. Balanced single-line inline code is inert for HTML
    detection (the canonical legend uses `<PR>` inside code). Other raw HTML is
    unsupported and fails closed; this schema is not an HTML renderer.
    Independent review still judges each row's substance.
    """
    required = {"chunk", "reviewing commit", "found by", "proposed ancestor", "weaker hypotheses", "state"}
    targets: set[str] = set()
    fields: dict[str, str] | None = None
    invalid = False
    fence: tuple[str, int] | None = None
    previous_field: str | None = None

    def finish() -> None:
        if fields is None or invalid or not required.issubset(fields) or not all(fields[key] for key in required):
            return
        if not re.fullmatch(r"[0-9a-fA-F]{7,40}", fields["reviewing commit"]):
            return
        if not re.fullmatch(r"UNVERIFIED|(?:CONFIRMED|FALSIFIED) \S.*", fields["state"]):
            return
        try:
            target = canonical_recovery_path(fields["proposed ancestor"])
        except LoopError:
            return
        targets.add(target)

    # Comments cannot contribute row fields. Other HTML is rejected below,
    # outside fences, rather than guessing which containers hide their content.
    text = re.sub(r"<!--.*?(?:-->|\Z)", "", text, flags=re.DOTALL)
    for line in text.splitlines():
        marker = re.match(r"^ {0,3}(`{3,}|~{3,})(.*)$", line)
        if fence is not None:
            if marker and marker[1][0] == fence[0] and len(marker[1]) >= fence[1] and not marker[2].strip():
                fence = None
            continue
        if marker:
            fence = (marker[1][0], len(marker[1]))
            continue
        html_source = re.sub(r"(?<![\\`])(`+)(?!`)(.*?)(?<!`)\1(?!`)", "", line)
        if re.search(r"<(?:/?[A-Za-z][A-Za-z0-9:-]*(?=[\s/>]|$)|[!?])", html_source):
            return set()
        if re.match(r"^#{1,6}\s", line):
            finish()
            fields = {} if re.match(r"^###\s+\S", line) else None
            invalid = False
            previous_field = None
            continue
        match = re.match(r"^- ([a-z ]+):\s*(.*?)\s*$", line)
        if fields is None or match is None:
            if fields is not None and previous_field == "proposed ancestor" and line[:1].isspace() and line.strip():
                invalid = True  # A descriptive continuation is not an exact target.
            continue
        key, value = match.groups()
        previous_field = key
        if key not in required:
            continue
        if key in fields:
            invalid = True
        if value.startswith("`") and value.endswith("`") and len(value) >= 2:
            value = value[1:-1]
        if "`" in value:
            invalid = True
        fields[key] = value
    finish()
    return targets


def require_recovery_lift_backlog(state: dict[str, Any]) -> None:
    """Bind every carried/current lift disposition to the reviewed Git tree."""
    reviews = recovery_lift_reviews(state)
    if not reviews:
        return
    current = latest_round(state)
    if current is None or not state.get("repo_root"):
        raise LoopError("recovery lift backlog requires a reviewed commit and repository")
    text = read_reviewed_text(Path(state["repo_root"]), current["commit"], BACKLOG_PATH)
    targets = recovery_backlog_targets(text)
    missing = {str(review.get("lift_target") or "") for review in reviews
               if not review.get("lift_target") or canonical_recovery_path(str(review["lift_target"])) not in targets}
    if missing:
        raise LoopError("recovery lift obligations are absent from the backlog: " + ", ".join(sorted(missing)))


def owner_reviewed_legacy_state(root: Path, spec: dict[str, Any], state: dict[str, Any]) -> bool:
    """A ledger inherits legacy privileges only for its exact owner-reviewed spec."""

    return (
        state.get("spec_id") == spec["id"]
        and state.get("spec_digest") == digest(spec)
        and owner_reviewed_legacy_manifest(root, spec)
    )


def require_unprotected(
    root: Path, spec: dict[str, Any], paths: Iterable[str], state: dict[str, Any]
) -> None:
    """Refuse a branch-authored run's change to its own authority or controller."""

    if owner_reviewed_legacy_state(root, spec, state):
        return
    blocked = protected_paths(paths, ledger_plan_paths(state))
    if blocked:
        raise LoopError("change touches protected paths a run may not modify: " + ", ".join(blocked))


def require_no_links(
    root: Path, spec: dict[str, Any], base: str, head: str, state: dict[str, Any]
) -> None:
    """Refuse symlinks and gitlinks a branch-authored change introduces.

    Each is judged by its own path, but a symlink writes through to its target
    on disk, and a later agent editing an ordinary-looking file would change a
    protected one.
    """

    if owner_reviewed_legacy_state(root, spec, state):
        return
    raw = run_command(root, ["git", "diff", "--raw", "--no-renames", "-z", f"{base}...{head}"], check=True).stdout
    fields = raw.split("\0")
    links = [
        fields[index + 1]
        for index in range(0, len(fields) - 1, 2)
        if fields[index].startswith(":") and fields[index].split()[1] in {"120000", "160000"}
    ]
    if links:
        raise LoopError("change adds symlinks or submodules, which a run may not introduce: " + ", ".join(links))


def require_published_head_has_no_links(root: Path, spec: dict[str, Any], state: dict[str, Any], head: str) -> None:
    if owner_reviewed_legacy_state(root, spec, state):
        return
    ensure_commit(root, spec["remote"], head)
    require_no_links(root, spec, trusted_base_commit(root, spec), head, state)


def recovery_scoped_paths(
    root: Path, spec: dict[str, Any], state: dict[str, Any], head: str, base: str | None = None
) -> None:
    """Check a recovery change's paths against `base`, the provider's base tip at publication."""

    safe = canonical_recovery_path

    allowed = [safe(path) for path in state["chunk"]["files"]] + [safe(path) for path in ledger_plan_paths(state)]
    lift_authority = [safe(path) for path in state["chunk"].get("lift_targets", [])]
    for path in authorized_lift_targets(state):
        value = safe(path)
        if not any(value == prefix or value.startswith(prefix + "/") for prefix in lift_authority):
            raise LoopError("review lift exceeds manifest path authority")
        allowed.append(value)
    result = run_command(
        root, ["git", "diff", "--no-renames", "--name-only", "-z", f"{base or spec['base_ref']}...{head}"], check=True
    )
    changed = list(filter(None, result.stdout.split("\0")))
    for path in changed:
        value = safe(path)
        if not any(value == prefix or value.startswith(prefix + "/") for prefix in allowed):
            raise LoopError(f"changed path lies outside frozen recovery scope: {path}")
    require_unprotected(root, spec, changed, state)
    require_no_links(root, spec, base or spec["base_ref"], head, state)


def authorize_action(root: Path, spec: dict[str, Any], action: str) -> None:
    if not spec["enabled"]:
        raise LoopError(f"spec {spec['id']} is disabled; enable it only after preflight review")
    mutation = ACTION_TO_MUTATION[action]
    if effective_mutations(root, spec).get(mutation) is not True:
        raise LoopError(
            f"remote action {action!r} is not authorized: neither a manifest merged to "
            f"{spec['base_branch']} nor the base branch's {STANDING_AUTHORITY_PATH} grants {mutation}"
        )


def selected_issue_for_action(spec: dict[str, Any], number: int) -> dict[str, Any]:
    return issue_entry(spec, number)


def action_comment(root: Path, spec: dict[str, Any], number: int, body: str, dry_run: bool) -> int:
    authorize_action(root, spec, "comment")
    selected_issue_for_action(spec, number)
    args = ["gh", "issue", "comment", str(number), "--repo", spec["repository"], "--body", body]
    if dry_run:
        print("DRY-RUN " + " ".join(args[:7]) + " <body>")
        return 0
    run_command(root, args, check=True)
    print(f"PASS issue comment written: #{number}")
    return 0


def action_close(
    root: Path,
    spec: dict[str, Any],
    number: int,
    merged_pr: int | None,
    comment: str | None,
    dry_run: bool,
    ledger_file: Path | None = None,
) -> int:
    authorize_action(root, spec, "close")
    if merged_pr is None and not owner_reviewed_legacy_manifest(root, spec):
        raise LoopError("a branch-authored manifest closes issues only through a verified merged PR")
    state = action_ledger_state(root, spec, ledger_file, issue_number=number)
    recovered = state if "recovery" in state else None
    selected_issue_for_action(spec, number)
    if recovered is None and state.get("status") != "passed":
        raise LoopError("issue closure requires a passing review ledger")
    if recovered is not None and merged_pr is None:
        raise LoopError("recovery issue closure requires the exact reviewed merged PR")
    if merged_pr is None and not spec["closure"]["allow_non_pr"]:
        raise LoopError("code issue closure requires --merged-pr; non-PR closure is disabled")
    if merged_pr is not None:
        pr = gh_json(
            root,
            [
                "pr",
                "view",
                str(merged_pr),
                "--repo",
                spec["repository"],
                "--json",
                "state,mergedAt,closingIssuesReferences,headRefName,headRefOid,baseRefName,body,files",
            ],
        )
        if pr.get("state") != "MERGED" or not pr.get("mergedAt"):
            raise LoopError(f"PR #{merged_pr} is not merged; refusing to close issue #{number}")
        closing = pr.get("closingIssuesReferences") or []
        if not any(reference.get("number") == number for reference in closing if isinstance(reference, dict)):
            raise LoopError(f"PR #{merged_pr} does not close issue #{number}; refusing to close it")
        if recovered is not None:
            require_pr_targets_base(pr, spec)
            require_pr_matches_frozen_issue(pr, recovered)
            verify_remote_chunk_files(root, spec, pr, recovered)
        else:
            require_pr_targets_base(pr, spec)
            require_pr_matches_frozen_issue(pr, state)
            verify_remote_chunk_files(root, spec, pr, state)
            require_repair_pr_binding(state, merged_pr, str(pr.get("headRefOid") or ""))
    args = ["gh", "issue", "close", str(number), "--repo", spec["repository"]]
    if comment:
        args.extend(["--comment", comment])
    if dry_run:
        print("DRY-RUN " + " ".join(args))
        return 0
    run_command(root, args, check=True)
    print(f"PASS issue closed: #{number}")
    return 0


def planned_branches(spec: dict[str, Any]) -> set[str]:
    return {f"agent/{issue['slug']}" for issue in spec["issues"]}


def action_push(
    root: Path,
    spec: dict[str, Any],
    branch: str | None,
    force_with_lease: bool,
    dry_run: bool,
    ledger_file: Path | None = None,
) -> int:
    authorize_action(root, spec, "push")
    if force_with_lease and not owner_reviewed_legacy_manifest(root, spec):
        raise LoopError("force-with-lease is not available to a branch-authored manifest")
    current = git(root, "branch", "--show-current")
    requested = branch or current
    if requested != current:
        raise LoopError(f"--branch {requested!r} does not match current branch {current!r}")
    state = action_ledger_state(root, spec, ledger_file)
    recovery_state = state if "recovery" in state else None
    recovery_head: str | None = None
    if recovery_state is not None:
        recovery_head = git(root, "rev-parse", "HEAD")
        if not reviewed_content_matches(root, spec, recovery_state, recovery_state["rounds"][-1]["commit"], recovery_head):
            raise LoopError("push must publish the reviewed recovery change")
    if not BRANCH_RE.fullmatch(current) or current not in planned_branches(spec):
        raise LoopError(f"push branch must be one of the spec's dedicated agent branches; got {current!r}")
    if current != f"agent/{state['issue']['slug']}":
        raise LoopError("push branch does not match the selected ledger issue")
    if git(root, "status", "--porcelain", "--untracked-files=all"):
        raise LoopError("refusing to push a dirty worktree; commit the frozen chunk first")
    if recovery_state is not None:
        assert recovery_head is not None
        recovery_scoped_paths(root, spec, recovery_state, recovery_head, trusted_base_commit(root, spec))
    else:
        verify_local_chunk_files(root, spec, state)
        if state.get("ci_failure_repairs"):
            if state.get("status") != "passed":
                raise LoopError("push after a CI-repair event requires a passing latest review round")
            current_round = latest_round(state)
            head = git(root, "rev-parse", "HEAD")
            if (
                current_round is None
                or not FULL_GIT_SHA_RE.fullmatch(str(current_round.get("commit", "")))
                or str(current_round.get("commit", "")).lower() != head.lower()
            ):
                raise LoopError("push after CI repair must publish the exact passing review commit")
            already_published = require_repair_push_binding(root, spec, state, current, head)
            if already_published:
                print(f"PASS reviewed CI repair is already published on PR #{state['ci_failure_repairs'][-1]['pr_number']}")
                return 0
        else:
            require_passing_reviewed_change(root, spec, state, "push")
    # Authority was read for spec.repository; the push must land there too.
    # A remote may carry several push URLs and `git push` delivers to all.
    require_manifest_remote(root, spec)
    if force_with_lease and not spec.get("allow_force_push", False):
        raise LoopError("force-with-lease is disabled by the specification")
    args = ["git", "push"]
    if recovery_state is not None:
        args.extend(["--no-follow-tags"])
    if force_with_lease:
        args.append("--force-with-lease")
    args.extend([spec["remote"], f"HEAD:refs/heads/{current}" if recovery_state is not None else current])
    if dry_run:
        print("DRY-RUN " + " ".join(args))
        return 0
    run_command(root, args, check=True)
    print(f"PASS branch pushed: {current}")
    return 0


def read_body_file(root: Path, value: str) -> str:
    path = ensure_inside(root, repo_path(root, value))
    try:
        body = path.read_text(encoding="utf-8")
    except OSError as exc:
        raise LoopError(f"could not read PR body file {path}: {exc}") from exc
    if not body.strip():
        raise LoopError("PR body must not be empty")
    return body


def normalize_scoped_path(value: str) -> str:
    """Normalize a repository-relative path without erasing dot directories."""

    normalized = value.replace("\\", "/")
    while normalized.startswith("./"):
        normalized = normalized[2:]
    return normalized.rstrip("/")


def authorized_lift_targets(state: dict[str, Any]) -> list[str]:
    """Lift-target prefixes a reviewer has actually asked this chunk to touch.

    Declaring a prefix in the manifest is the owner's standing permission; it
    opens nothing on its own. A prefix becomes writable only once a recorded
    `pass_with_lift` finding names a path under it, so a silent widening of the
    frozen list stays impossible while a reviewed one becomes legal.
    """
    declared = state.get("chunk", {}).get("lift_targets") or []
    if not declared:
        return []
    if "recovery" in state:
        # Preserve requests across attempts, but never import broader historical
        # authority than the current frozen manifest actually grants.
        requested = [canonical_recovery_path(str(review["lift_target"]))
                     for review in recovery_lift_reviews(state) if review.get("lift_target")]
        return [prefix for prefix in declared
                if any(path_is_in_frozen_chunk(target, [canonical_recovery_path(prefix)])
                       for target in requested)]
    requested = [
        str(item.get("lift_target"))
        for round_state in state.get("rounds", [])
        for item in round_state.get("reviews", [])
        if item.get("verdict") == "pass_with_lift" and item.get("lift_target")
    ]
    return [
        prefix
        for prefix in declared
        if any(path_is_in_frozen_chunk(target, [prefix]) for target in requested)
    ]


def chunk_allowed_paths(state: dict[str, Any]) -> list[str]:
    # The plan travels in the same PR as the code it plans.
    return list(state["chunk"]["files"]) + authorized_lift_targets(state) + ledger_plan_paths(state)


def path_is_in_frozen_chunk(path: str, allowed_prefixes: Iterable[str]) -> bool:
    normalized = normalize_scoped_path(path)
    return any(
        normalized == normalize_scoped_path(prefix)
        or normalized.startswith(normalize_scoped_path(prefix) + "/")
        for prefix in allowed_prefixes
    )


def validate_pr_body_closure(body: str, number: int, chunk_closure: str) -> None:
    """Enforce complete-vs-progress issue-link semantics before PR creation."""

    closing_numbers = {int(match.group(1)) for match in CLOSING_KEYWORD_RE.finditer(body)}
    extra_closures = closing_numbers - {number}
    if extra_closures:
        raise LoopError(
            "PR body closes issues outside the current frozen chunk: "
            + ", ".join(f"#{issue}" for issue in sorted(extra_closures))
        )
    if chunk_closure == "complete":
        if number not in closing_numbers:
            raise LoopError(f"complete PR body must contain a closing keyword for issue #{number}")
        return
    if chunk_closure != "progress":
        raise LoopError(f"unsupported chunk closure mode: {chunk_closure!r}")
    if closing_numbers:
        raise LoopError("progress PR body must not contain a closing keyword; use 'Refs #N' or similar")
    references = {int(match.group(1)) for match in NON_CLOSING_REFERENCE_RE.finditer(body)}
    if number not in references:
        raise LoopError(f"progress PR body must contain a non-closing reference to issue #{number}")


def reviewed_commit_matches_head(root: Path, reviewed_commit: str, head_oid: str) -> bool:
    """Resolve a short/full ledger revision, then compare full SHAs exactly."""

    if not re.fullmatch(r"[0-9a-fA-F]{7,40}", reviewed_commit):
        return False
    if not re.fullmatch(r"[0-9a-fA-F]{40}", head_oid):
        return False
    resolved = git(
        root,
        "rev-parse",
        "--verify",
        "--end-of-options",
        f"{reviewed_commit}^{{commit}}",
        check=False,
    )
    return resolved.lower() == head_oid.lower()


def verify_local_chunk_files(root: Path, spec: dict[str, Any], state: dict[str, Any]) -> None:
    base_ref = spec["base_ref"]
    result = run_command(root, ["git", "diff", "--name-only", f"{base_ref}...HEAD"], check=False)
    if result.returncode != 0:
        detail = (result.stderr or result.stdout).strip()
        raise LoopError(f"could not inspect the frozen chunk diff: {detail}")
    changed = [line.strip() for line in result.stdout.splitlines() if line.strip()]
    if not changed:
        raise LoopError("frozen chunk has no committed file changes relative to the protected base")
    require_unprotected(root, spec, changed, state)
    require_no_links(root, spec, base_ref, "HEAD", state)
    allowed = chunk_allowed_paths(state)
    outside = [path for path in changed if not path_is_in_frozen_chunk(path, allowed)]
    if outside:
        declared = state.get("chunk", {}).get("lift_targets") or []
        unrequested = [
            path
            for path in outside
            if path_is_in_frozen_chunk(path, declared)
        ]
        if unrequested:
            raise LoopError(
                "chunk diff touches declared lift targets that no reviewer has asked for: "
                + ", ".join(unrequested)
                + ". A lift target opens only after a pass_with_lift finding names it"
            )
        raise LoopError("chunk diff contains files outside the frozen list: " + ", ".join(outside))


def verify_remote_chunk_files(
    root: Path, spec: dict[str, Any], pr: dict[str, Any], state: dict[str, Any]
) -> None:
    if "recovery" in state:
        root = Path(state["repo_root"])
        records = [record for _, record in recovery_registry(root)
                   if record["objective_id"] == state["recovery"]["policy"]["objective_id"]]
        if len(records) != 1:
            raise LoopError("unregistered recovery publication")
        spec = load_spec(Path(records[0]["spec_path"]), root, verify_owner_review=True)
        head = str(pr.get("headRefOid") or "")
        if not reviewed_content_matches(root, spec, state, state["rounds"][-1]["commit"], head):
            raise LoopError("remote PR head does not carry the reviewed recovery change")
        recovery_scoped_paths(root, spec, state, head, trusted_base_commit(root, spec))
        return
    files = pr.get("files") or []
    paths = [file.get("path") for file in files if isinstance(file, dict) and isinstance(file.get("path"), str)]
    if not paths:
        raise LoopError("PR has no readable changed-file list; refusing to approve an unbound chunk")
    require_unprotected(root, spec, paths, state)
    outside = [path for path in paths if not path_is_in_frozen_chunk(path, chunk_allowed_paths(state))]
    if outside:
        raise LoopError("PR contains files outside the frozen list: " + ", ".join(outside))


def require_pr_targets_base(pr: dict[str, Any], spec: dict[str, Any]) -> None:
    """Refuse a PR retargeted away from the protected base after creation."""

    if pr.get("baseRefName") != spec["base_branch"]:
        raise LoopError(
            f"PR targets {pr.get('baseRefName')!r}, not protected base {spec['base_branch']!r}"
        )


def require_pr_matches_frozen_issue(pr: dict[str, Any], state: dict[str, Any]) -> None:
    """Bind every later action to the ledger's issue branch and closure body."""

    issue = state.get("issue")
    number = issue.get("number") if isinstance(issue, dict) else None
    slug = issue.get("slug") if isinstance(issue, dict) else None
    if not isinstance(number, int) or isinstance(number, bool) or number <= 0:
        raise LoopError("ledger has no valid frozen issue number")
    if not isinstance(slug, str) or not ISSUE_ID_RE.fullmatch(slug):
        raise LoopError("ledger has no valid frozen issue branch slug")
    expected_branch = f"agent/{slug}"
    if pr.get("headRefName") != expected_branch:
        raise LoopError(
            f"PR branch {pr.get('headRefName')!r} does not match frozen issue branch {expected_branch!r}"
        )
    body = pr.get("body")
    if not isinstance(body, str):
        raise LoopError("PR has no readable body for frozen closure validation")
    closure = state.get("chunk", {}).get("closure", "complete")
    try:
        validate_pr_body_closure(body, number, closure)
    except LoopError as exc:
        raise LoopError(f"PR body does not match the frozen {closure!r} closure: {exc}") from exc


def require_recovery_remote_head(root: Path, spec: dict[str, Any], branch: str, commit: str) -> None:
    remote = gh_json(root, ["api", f"repos/{spec['repository']}/git/ref/heads/{branch}"])
    obj = remote.get("object") if isinstance(remote, dict) else None
    if not isinstance(obj, dict) or obj.get("sha") != commit:
        raise LoopError("remote branch must contain the exact reviewed recovery commit before PR creation")


def action_create_pr(
    root: Path,
    spec: dict[str, Any],
    number: int,
    ledger_file: Path,
    title: str,
    body_file: str,
    draft: bool,
    dry_run: bool,
) -> int:
    authorize_action(root, spec, "create-pr")
    local_head = ""
    require_predecessor_prs(root, spec)
    state = action_ledger_state(root, spec, ledger_file, issue_number=number)
    if state.get("ci_failure_repairs"):
        raise LoopError("CI repair is bound to its existing PR; refusing to create a replacement PR")
    recovered = state if "recovery" in state else None
    if recovered is not None:
        local_head = git(root, "rev-parse", "HEAD")
        if not reviewed_content_matches(root, spec, recovered, recovered["rounds"][-1]["commit"], local_head):
            raise LoopError("PR creation requires the reviewed recovery change")
        if git(root, "status", "--porcelain", "--untracked-files=all"):
            raise LoopError("PR creation requires a clean frozen checkout")
        recovery_scoped_paths(root, spec, recovered, local_head, trusted_base_commit(root, spec))
    else:
        if not draft and state.get("status") != "passed":
            raise LoopError("PR creation before a passing review must remain a draft")
        require_passing_reviewed_change(root, spec, state, "PR creation")
    issue = selected_issue_for_action(spec, number)
    require_legacy_issue_open(root, spec, number)
    current = git(root, "branch", "--show-current")
    expected = f"agent/{issue['slug']}"
    if current != expected:
        raise LoopError(f"current branch {current!r} does not match issue branch {expected!r}")
    if state.get("status") == "blocked":
        raise LoopError("cannot create a PR from a blocked chunk ledger")
    verify_local_chunk_files(root, spec, state)
    body = read_body_file(root, body_file)
    chunk_closure = state.get("chunk", {}).get("closure", "complete")
    validate_pr_body_closure(body, number, chunk_closure)
    if recovered is not None:
        require_recovery_remote_head(root, spec, current, local_head)
    args = [
        "gh",
        "pr",
        "create",
        "--repo",
        spec["repository"],
        "--base",
        spec["base_branch"],
        "--head",
        current,
        "--title",
        title,
        "--body-file",
        str(ensure_inside(root, repo_path(root, body_file))),
    ]
    if draft:
        args.append("--draft")
    if dry_run:
        print("DRY-RUN " + " ".join(args))
        return 0
    created = run_command(root, args, check=True)
    if recovered is not None:
        url = created.stdout.strip()
        # GitHub creates by branch name, not a compare-and-swap SHA. Detect a
        # concurrent remote update and prohibit subsequent approval/closure.
        try:
            pr = gh_json(root, ["pr", "view", url, "--repo", spec["repository"],
                                "--json", "headRefName,headRefOid,baseRefName,body,files"])
            require_pr_targets_base(pr, spec)
            require_pr_matches_frozen_issue(pr, recovered)
            verify_remote_chunk_files(root, spec, pr, recovered)
        except (LoopError, loop_recovery.RecoveryError) as exc:
            raise LoopError(f"PR was created at {url}, but its recovery binding failed; do not approve or close: {exc}") from exc
    print(f"PASS PR created for issue #{number}")
    return 0


def action_attest_pr(
    root: Path,
    spec: dict[str, Any],
    number: int,
    pr_number: int,
    ledger_file: Path,
    dry_run: bool,
) -> int:
    """Write one durable, controller-derived predecessor marker to a source PR."""

    authorize_action(root, spec, "comment")
    if not predecessor_attestation_policy(spec)["emit"]:
        raise LoopError("spec.predecessor_attestation.emit is false; refusing to emit an unused marker")
    predecessor_proofs = require_predecessor_prs(root, spec)
    state = action_ledger_state(root, spec, ledger_file, issue_number=number)
    selected_issue_for_action(spec, number)
    current = latest_round(state)
    if state.get("status") != "passed" or current is None:
        raise LoopError("predecessor attestation requires a passing review ledger")
    if current.get("adjudication", {}).get("verdict") not in PASSING_VERDICTS:
        raise LoopError("predecessor attestation requires a passing adjudicated review round")
    pr = gh_json(
        root,
        [
            "pr",
            "view",
            str(pr_number),
            "--repo",
            spec["repository"],
            "--json",
            "headRefName,headRefOid,state,isDraft,baseRefName,body,files,comments",
        ],
    )
    if pr.get("state") != "OPEN" or pr.get("isDraft"):
        raise LoopError("predecessor attestation requires an open, non-draft PR")
    require_pr_targets_base(pr, spec)
    require_pr_matches_frozen_issue(pr, state)
    require_repair_pr_binding(state, pr_number, str(pr.get("headRefOid") or ""))
    require_predecessor_merges_ancestor(root, predecessor_proofs, pr.get("headRefOid", ""), "PR head")
    if not reviewed_content_matches(root, spec, state, str(current.get("commit", "")), str(pr.get("headRefOid", ""))):
        raise LoopError("PR head does not carry the change reviewed by the passing ledger")
    verify_remote_chunk_files(root, spec, pr, state)
    require_published_head_has_no_links(root, spec, state, str(pr.get("headRefOid", "")))
    payload = predecessor_attestation_from_state(state, pr["headRefOid"])
    matches = matching_predecessor_attestations(pr.get("comments"), payload, spec["actor"])
    if len(matches) == 1:
        print(f"PASS predecessor attestation already present: #{pr_number}")
        return 0
    if len(matches) > 1:
        raise LoopError(f"PR #{pr_number} already has duplicate matching predecessor attestations")
    body = predecessor_attestation_body(payload)
    args = ["gh", "pr", "comment", str(pr_number), "--repo", spec["repository"], "--body", body]
    if dry_run:
        print("DRY-RUN " + " ".join(args[:7]) + " <controller-attestation>")
        return 0
    run_command(root, args, check=True)
    print(f"PASS predecessor attestation written: #{pr_number}")
    return 0


def action_ready(root: Path, spec: dict[str, Any], pr_number: int, ledger_file: Path, dry_run: bool) -> int:
    """Mark a draft PR ready once the panel has passed the change it carries."""

    authorize_action(root, spec, "ready")
    state = action_ledger_state(root, spec, ledger_file)
    if state.get("spec_id") != spec["id"] or state.get("spec_digest") != digest(spec):
        raise LoopError("ledger was created from a different run manifest")
    if not ledger_openspec_matches(root, spec, state):
        raise LoopError("OpenSpec artifacts changed after ledger initialization; reinitialize the frozen chunk")
    current = latest_round(state)
    if state.get("status") != "passed" or current is None or current.get(
        "adjudication", {}
    ).get("verdict") not in PASSING_VERDICTS:
        raise LoopError("marking a PR ready requires a passing review ledger")
    pr = gh_json(
        root,
        [
            "pr",
            "view",
            str(pr_number),
            "--repo",
            spec["repository"],
            "--json",
            "headRefName,headRefOid,state,isDraft,baseRefName,body,files",
        ],
    )
    if pr.get("state") != "OPEN":
        raise LoopError("only an open PR can be marked ready")
    require_pr_targets_base(pr, spec)
    require_pr_matches_frozen_issue(pr, state)
    require_repair_pr_binding(state, pr_number, str(pr.get("headRefOid") or ""))
    if not reviewed_content_matches(root, spec, state, str(current.get("commit", "")), str(pr.get("headRefOid", ""))):
        raise LoopError("PR head does not carry the change reviewed by the passing ledger")
    verify_remote_chunk_files(root, spec, pr, state)
    require_published_head_has_no_links(root, spec, state, str(pr.get("headRefOid", "")))
    if pr.get("isDraft") is False:
        print(f"PASS PR already ready for review: #{pr_number}")
        return 0
    args = ["gh", "pr", "ready", str(pr_number), "--repo", spec["repository"]]
    if dry_run:
        print("DRY-RUN " + " ".join(args))
        return 0
    run_command(root, args, check=True)
    print(f"PASS PR marked ready for review: #{pr_number}")
    return 0


def action_follow_up(
    root: Path,
    spec: dict[str, Any],
    parent: int,
    title: str,
    body_file: str,
    labels: list[str],
    dry_run: bool,
) -> int:
    """File a follow-up issue for work a run found but must not absorb.

    A deferred finding, a stale dependency, an out-of-scope lift: each becomes
    tracked work linked to the selected issue and its milestone, instead of a
    reason to stop and ask.
    """

    authorize_action(root, spec, "follow-up")
    selected_issue_for_action(spec, parent)
    if not title.strip():
        raise LoopError("follow-up issue title must not be empty")
    body = read_body_file(root, body_file).rstrip() + f"\n\nFollow-up of #{parent} (filed by loop run `{spec['id']}`).\n"
    parent_issue = gh_json(
        root, ["issue", "view", str(parent), "--repo", spec["repository"], "--json", "milestone"]
    )
    milestone = parent_issue.get("milestone") if isinstance(parent_issue, dict) else None
    args = ["gh", "issue", "create", "--repo", spec["repository"], "--title", title, "--body", body]
    if isinstance(milestone, dict) and isinstance(milestone.get("title"), str) and milestone["title"]:
        args.extend(["--milestone", milestone["title"]])
    for label in labels:
        args.extend(["--label", label])
    if dry_run:
        print("DRY-RUN " + " ".join(args[:7]) + " <body> " + " ".join(args[9:]))
        return 0
    created = run_command(root, args, check=True)
    print(f"PASS follow-up issue created: {created.stdout.strip()}")
    return 0


def protected_check_names(root: Path, spec: dict[str, Any]) -> set[str]:
    protection = gh_json(
        root,
        [
            "api",
            f"repos/{spec['repository']}/branches/{spec['base_branch']}/protection/required_status_checks",
        ],
    )
    if not isinstance(protection, dict):
        raise LoopError("branch protection returned an unexpected response")
    names = {name for name in protection.get("contexts") or [] if isinstance(name, str)}
    names.update(
        item["context"]
        for item in protection.get("checks") or []
        if isinstance(item, dict) and isinstance(item.get("context"), str)
    )
    return names


def check_required_checks(root: Path, spec: dict[str, Any], pr_number: int) -> str:
    """Require green checks and return the PR head they were read for."""

    data = gh_json(
        root,
        ["pr", "view", str(pr_number), "--repo", spec["repository"], "--json", "headRefOid,statusCheckRollup"],
    )
    latest: dict[str, dict[str, Any]] = {}
    for check in data.get("statusCheckRollup") or []:
        if not isinstance(check, dict):
            continue
        name = check.get("name") or check.get("context")
        if not isinstance(name, str):
            continue
        timestamp = str(check.get("completedAt") or check.get("startedAt") or "")
        previous = latest.get(name)
        if previous is None or timestamp >= str(previous.get("_timestamp", "")):
            check = dict(check)
            check["_timestamp"] = timestamp
            latest[name] = check
    missing: list[str] = []
    failed: list[str] = []
    # Branch protection is the live list of required checks. A manifest check
    # still counts when the PR actually runs it; a name that neither the
    # protection nor the PR knows was retired after the manifest was written.
    try:
        live = protected_check_names(root, spec)
    except LoopError:
        live = set()
    # With no live list, a manifest check that has not started must not drop out.
    required_names = (
        live | {name for name in spec["runner"]["required_checks"] if name in latest}
        if live
        else set(spec["runner"]["required_checks"])
    )
    for required in sorted(required_names):
        check = latest.get(required)
        if check is None:
            missing.append(required)
            continue
        conclusion = check.get("conclusion") or check.get("state") or check.get("status")
        if conclusion not in SUCCESS_CONCLUSIONS:
            failed.append(f"{required}={conclusion}")
    if missing or failed:
        detail = []
        if missing:
            detail.append("missing " + ", ".join(missing))
        if failed:
            detail.append("not successful " + ", ".join(failed))
        raise LoopError("required checks are not green: " + "; ".join(detail))
    return str(data.get("headRefOid") or "")


def strict_protected_check_map(root: Path, spec: dict[str, Any]) -> dict[str, int | None]:
    """Read a complete, unambiguous live protection set for CI-repair admission."""

    protection = gh_json(
        root,
        [
            "api",
            f"repos/{spec['repository']}/branches/{spec['base_branch']}/protection/required_status_checks",
        ],
    )
    if not isinstance(protection, dict):
        raise LoopError("live branch protection returned an unexpected response")
    contexts = protection.get("contexts")
    checks = protection.get("checks")
    if not isinstance(contexts, list) or not isinstance(checks, list):
        raise LoopError("live branch protection is incomplete or ambiguous")
    required: dict[str, int | None] = {}
    for context in contexts:
        if not isinstance(context, str) or not context.strip():
            raise LoopError("live branch protection contains a malformed required context")
        required[context] = None
    for check in checks:
        if not isinstance(check, dict):
            raise LoopError("live branch protection contains a malformed required check")
        name, app_id = check.get("context"), check.get("app_id")
        if not isinstance(name, str) or not name.strip():
            raise LoopError("live branch protection contains a check with no context")
        if app_id is not None and (not isinstance(app_id, int) or isinstance(app_id, bool) or app_id <= 0):
            raise LoopError(f"live branch protection has an invalid app identity for {name!r}")
        previous = required.get(name)
        if name in required and previous is not None and app_id is not None and previous != app_id:
            raise LoopError(f"live branch protection has conflicting app identities for {name!r}")
        if app_id is not None:
            required[name] = app_id
    if not required:
        raise LoopError("live branch protection has no required status checks")
    return required


def provider_check_timestamp(check: dict[str, Any]) -> str:
    for field in ("completed_at", "updated_at", "started_at", "created_at"):
        value = check.get(field)
        if isinstance(value, str) and value:
            return value
    return ""


def latest_provider_check(records: list[dict[str, Any]], name: str) -> dict[str, Any] | None:
    """Select the newest same-head record; reject ties and unorderable duplicates."""

    matching = [record for record in records if record.get("name") == name]
    if not matching:
        return None
    if len(matching) == 1:
        return matching[0]
    if any(not record.get("timestamp") for record in matching):
        raise LoopError(f"check {name!r} has duplicate same-head results without comparable timestamps")
    newest_at = max(str(record["timestamp"]) for record in matching)
    newest = [record for record in matching if record["timestamp"] == newest_at]
    if len(newest) != 1:
        raise LoopError(f"check {name!r} has ambiguous latest results on the current head")
    return newest[0]


def required_check_failure_evidence(
    root: Path, spec: dict[str, Any], head_sha: str, protected: dict[str, int | None]
) -> dict[str, Any]:
    """Return one exact current required-check failure, never using green-check fallbacks."""

    manifest_checks = spec.get("runner", {}).get("required_checks")
    if not isinstance(manifest_checks, list) or any(not isinstance(name, str) or not name for name in manifest_checks):
        raise LoopError("manifest required-check list is malformed")
    common = sorted(set(manifest_checks) & set(protected))
    if not common:
        raise LoopError("no check is required by both the frozen manifest and live branch protection")

    check_response = gh_json(
        root,
        ["api", f"repos/{spec['repository']}/commits/{head_sha}/check-runs?per_page=100"],
    )
    if not isinstance(check_response, dict):
        raise LoopError("check-run response is malformed")
    check_runs = check_response.get("check_runs")
    total_count = check_response.get("total_count")
    if (
        not isinstance(check_runs, list)
        or not isinstance(total_count, int)
        or isinstance(total_count, bool)
        or total_count != len(check_runs)
    ):
        raise LoopError("check-run response is incomplete or ambiguous")
    status_response = gh_json(
        root,
        ["api", f"repos/{spec['repository']}/commits/{head_sha}/statuses?per_page=100"],
    )
    if not isinstance(status_response, list) or len(status_response) >= 100:
        raise LoopError("legacy status response is incomplete or ambiguous")

    records: list[dict[str, Any]] = []
    for check in check_runs:
        if not isinstance(check, dict):
            raise LoopError("check-run response contains a malformed row")
        if check.get("head_sha") != head_sha:
            raise LoopError("check-run evidence does not identify the exact pull-request head")
        name = check.get("name")
        if not isinstance(name, str) or not name.strip():
            raise LoopError("check-run response contains a result with no name")
        if name not in common:
            continue
        requirement_app = protected[name]
        app = check.get("app")
        app_id = app.get("id") if isinstance(app, dict) else None
        app_slug = app.get("slug") if isinstance(app, dict) else None
        if app_id is not None and (not isinstance(app_id, int) or isinstance(app_id, bool)):
            raise LoopError(f"check-run {name!r} has a malformed app identity")
        if app_slug is not None and not isinstance(app_slug, str):
            raise LoopError(f"check-run {name!r} has a malformed app slug")
        if requirement_app is not None and app_id != requirement_app:
            continue
        status, conclusion = check.get("status"), check.get("conclusion")
        if not isinstance(status, str):
            raise LoopError(f"check-run {name!r} has no status")
        if conclusion is not None and not isinstance(conclusion, str):
            raise LoopError(f"check-run {name!r} has a malformed conclusion")
        records.append(
            {
                "name": name,
                "timestamp": provider_check_timestamp(check),
                "state": status.lower(),
                "conclusion": conclusion.lower() if conclusion else None,
                "source": "check_run",
                "app_id": app_id,
                "app_slug": app_slug,
                "run_id": check.get("id"),
                "url": check.get("html_url"),
                "head_sha": head_sha,
            }
        )
    for status in status_response:
        if not isinstance(status, dict):
            raise LoopError("legacy status response contains a malformed row")
        if status.get("sha") != head_sha:
            raise LoopError("status evidence does not identify the exact pull-request head")
        name = status.get("context")
        if not isinstance(name, str) or not name.strip():
            raise LoopError("legacy status response contains a result with no context")
        if name not in common or protected[name] is not None:
            continue
        state = status.get("state")
        if not isinstance(state, str):
            raise LoopError(f"legacy status {name!r} has no state")
        creator = status.get("creator")
        creator_login = creator.get("login") if isinstance(creator, dict) else None
        if creator is not None and not isinstance(creator, dict):
            raise LoopError(f"legacy status {name!r} has a malformed creator identity")
        if creator_login is not None and not isinstance(creator_login, str):
            raise LoopError(f"legacy status {name!r} has a malformed creator login")
        records.append(
            {
                "name": name,
                "timestamp": provider_check_timestamp(status),
                "state": "completed",
                "conclusion": state.lower(),
                "source": "commit_status",
                "app_id": None,
                "creator_login": creator_login,
                "run_id": status.get("id"),
                "url": status.get("target_url"),
                "head_sha": head_sha,
            }
        )

    failures: list[dict[str, Any]] = []
    for name in common:
        latest = latest_provider_check(records, name)
        if latest is None:
            continue
        if latest.get("source") == "check_run":
            failed = latest.get("state") == "completed" and latest.get("conclusion") == "failure"
        else:
            failed = latest.get("conclusion") in {"failure", "error"}
        if failed:
            failures.append(latest)
    if not failures:
        raise LoopError("no current required check has a completed failure on the exact pull-request head")
    failures.sort(key=lambda item: (item["name"], item["source"], str(item.get("app_id") or ""), str(item.get("run_id") or "")))
    return failures[0]


def provider_ref_sha(root: Path, spec: dict[str, Any], branch: str) -> str:
    data = gh_json(root, ["api", f"repos/{spec['repository']}/git/ref/heads/{branch}"])
    obj = data.get("object") if isinstance(data, dict) else None
    sha = obj.get("sha") if isinstance(obj, dict) else None
    if not isinstance(sha, str) or not FULL_GIT_SHA_RE.fullmatch(sha):
        raise LoopError(f"provider did not report a full commit SHA for branch {branch!r}")
    return sha


def normalized_pull_request(data: Any, spec: dict[str, Any], state: dict[str, Any]) -> dict[str, Any]:
    if not isinstance(data, dict):
        raise LoopError("provider pull-request response is malformed")
    number = data.get("number")
    head, base = data.get("head"), data.get("base")
    if not isinstance(number, int) or isinstance(number, bool) or number <= 0:
        raise LoopError("provider pull-request response has no valid number")
    if not isinstance(head, dict) or not isinstance(base, dict):
        raise LoopError("provider pull-request response has no readable head or base")
    head_repo = head.get("repo")
    base_repo = base.get("repo")
    if not isinstance(head_repo, dict) or not isinstance(base_repo, dict):
        raise LoopError("pull-request source or base repository is unavailable")
    head_repo_name, base_repo_name = head_repo.get("full_name"), base_repo.get("full_name")
    if not isinstance(head_repo_name, str) or not isinstance(base_repo_name, str):
        raise LoopError("pull-request source or base repository identity is malformed")
    if head_repo_name.casefold() != spec["repository"].casefold():
        raise LoopError("pull-request source repository does not match the frozen manifest repository")
    if base_repo_name.casefold() != spec["repository"].casefold():
        raise LoopError("pull-request base repository does not match the frozen manifest repository")
    head_sha, base_sha = head.get("sha"), base.get("sha")
    if not isinstance(head_sha, str) or not FULL_GIT_SHA_RE.fullmatch(head_sha):
        raise LoopError("pull request does not report a full head SHA")
    if not isinstance(base_sha, str) or not FULL_GIT_SHA_RE.fullmatch(base_sha):
        raise LoopError("pull request does not report a full base SHA")
    head_ref, base_ref = head.get("ref"), base.get("ref")
    body = data.get("body")
    status = data.get("state")
    draft = data.get("draft")
    if not isinstance(head_ref, str) or not isinstance(base_ref, str) or not isinstance(body, str):
        raise LoopError("pull-request source, base, or issue-link metadata is malformed")
    if status != "open" or draft is not False:
        raise LoopError("CI-repair admission requires one open, non-draft pull request")
    expected_branch = f"agent/{state['issue']['slug']}"
    if head_ref != expected_branch:
        raise LoopError(f"pull-request branch {head_ref!r} does not match {expected_branch!r}")
    if base_ref != spec["base_branch"]:
        raise LoopError(f"pull request targets {base_ref!r}, not protected base {spec['base_branch']!r}")
    require_pr_matches_frozen_issue(
        {"headRefName": head_ref, "body": body}, state
    )
    return {
        "number": number,
        "state": status,
        "draft": draft,
        "head_repository": head_repo_name,
        "head_branch": head_ref,
        "head_sha": head_sha.lower(),
        "base_repository": base_repo_name,
        "base_branch": base_ref,
        "base_sha": base_sha.lower(),
        "body": body,
        "url": data.get("html_url") if isinstance(data.get("html_url"), str) else "",
    }


def matching_open_repair_pr(root: Path, spec: dict[str, Any], state: dict[str, Any]) -> dict[str, Any]:
    expected_branch = f"agent/{state['issue']['slug']}"
    matching: list[dict[str, Any]] = []
    for page in range(1, 21):
        rows = gh_json(
            root,
            ["api", f"repos/{spec['repository']}/pulls?state=open&per_page=100&page={page}"],
        )
        if not isinstance(rows, list) or any(not isinstance(row, dict) for row in rows):
            raise LoopError("open pull-request listing is malformed or ambiguous")
        if any(
            not isinstance(row.get("head"), dict)
            or not isinstance(row["head"].get("ref"), str)
            for row in rows
        ):
            raise LoopError("open pull-request listing contains a row with incomplete source identity")
        matching.extend(
            row for row in rows
            if isinstance(row.get("head"), dict) and row["head"].get("ref") == expected_branch
        )
        if len(rows) < 100:
            break
    else:
        raise LoopError("open pull-request listing is too large to establish a unique matching PR")
    if len(matching) != 1:
        raise LoopError(
            f"expected exactly one open pull request for branch {expected_branch!r}; found {len(matching)}"
        )
    return normalized_pull_request(matching[0], spec, state)


def reread_repair_provider_state(
    root: Path, spec: dict[str, Any], state: dict[str, Any], initial_pr: dict[str, Any], initial_base: str
) -> None:
    current_unique_pr = matching_open_repair_pr(root, spec, state)
    if current_unique_pr != initial_pr:
        raise LoopError("matching pull-request set changed during CI-failure admission")
    current_data = gh_json(
        root, ["api", f"repos/{spec['repository']}/pulls/{initial_pr['number']}"]
    )
    current_pr = normalized_pull_request(current_data, spec, state)
    if current_pr != initial_pr:
        raise LoopError("pull-request identity, issue links, base, or head moved during CI-failure admission")
    current_source = provider_ref_sha(root, spec, initial_pr["head_branch"])
    if current_source.lower() != initial_pr["head_sha"].lower():
        raise LoopError("source branch moved during CI-failure admission")
    current_base = provider_ref_sha(root, spec, spec["base_branch"])
    if current_base.lower() != initial_base.lower():
        raise LoopError("protected base moved during CI-failure admission")
    if current_pr["base_sha"].lower() != current_base.lower():
        raise LoopError("pull-request base snapshot is stale relative to the live protected base")


def validate_repair_candidate(root: Path, spec: dict[str, Any], state: dict[str, Any], failed_head: str, candidate: str) -> str:
    if not isinstance(candidate, str) or not FULL_GIT_SHA_RE.fullmatch(candidate):
        raise LoopError("CI-repair candidate must be a full 40-character commit SHA")
    resolved = git(root, "rev-parse", "--verify", "--end-of-options", f"{candidate}^{{commit}}", check=False)
    if not FULL_GIT_SHA_RE.fullmatch(resolved) or resolved.lower() != candidate.lower():
        raise LoopError("CI-repair candidate is not the exact local commit supplied")
    if candidate.lower() == failed_head.lower():
        raise LoopError("same-head CI reruns do not allocate a repair round")
    if not is_ancestor(root, failed_head, candidate):
        raise LoopError("CI-repair candidate must descend from the exact failed-check head")
    changed = git(root, "diff", "--name-only", "--no-renames", failed_head, candidate).splitlines()
    if not changed:
        raise LoopError("CI-repair candidate has no changed content relative to the failed-check head")
    outside = [path for path in changed if not path_is_in_frozen_chunk(path, chunk_allowed_paths(state))]
    if outside:
        raise LoopError("CI-repair candidate changes files outside the frozen chunk: " + ", ".join(outside))
    require_unprotected(root, spec, changed, state)
    require_no_links(root, spec, failed_head, candidate, state)
    return resolved.lower()


def require_canonical_ledger_identity(root: Path, ledger_file: Path, state: dict[str, Any]) -> None:
    path = ensure_inside(root, ledger_file)
    runs_root = canonical_ledger_root(root)
    try:
        path.relative_to(runs_root)
    except ValueError as exc:
        raise LoopError("ordinary loop ledgers must remain under the repository's .loop-runs root") from exc
    issue, chunk = state.get("issue"), state.get("chunk")
    if not isinstance(issue, dict) or not isinstance(chunk, dict):
        raise LoopError("ledger has no frozen issue and chunk identity")
    matches: list[Path] = []
    for candidate in ordinary_ledger_files(root):
        try:
            record = json.loads(candidate.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        if not isinstance(record, dict) or record.get("schema") != f"{RUN_SCHEMA}/ledger":
            continue
        record_issue, record_chunk = record.get("issue"), record.get("chunk")
        if (
            isinstance(record_issue, dict)
            and isinstance(record_chunk, dict)
            and record_issue.get("number") == issue.get("number")
            and record_issue.get("slug") == issue.get("slug")
            and record_chunk.get("id") == chunk.get("id")
        ):
            matches.append(candidate.resolve())
    if len(matches) != 1 or matches[0] != path:
        raise LoopError(
            "selected ledger is missing, ambiguous, or not the unique canonical ledger for this frozen issue/chunk"
        )


def require_ci_repairs_resolved(state: dict[str, Any]) -> None:
    rounds = state.get("rounds")
    if not isinstance(rounds, list):
        raise LoopError("ledger round history is malformed")
    if "ci_failure_repairs" not in state:
        has_repair_history = state.get("status") == "repair_exhausted" or any(
            isinstance(round_state, dict) and round_state.get("kind") == "ci_failure_repair"
            for round_state in rounds
        )
        if has_repair_history:
            raise LoopError("ledger is missing CI-repair evidence for recorded repair history")
        events = []
    else:
        events = state.get("ci_failure_repairs")
    if not isinstance(events, list):
        raise LoopError("ledger CI-repair event list is malformed")
    if state.get("status") == "repair_exhausted":
        raise LoopError("CI-repair review cap is exhausted; this chunk cannot be published or closed")
    for sequence, event in enumerate(events, start=1):
        if not isinstance(event, dict) or event.get("sequence") != sequence:
            raise LoopError("ledger CI-repair event history is malformed or reordered")
        disposition = event.get("disposition")
        if disposition == "cap_exhausted":
            raise LoopError("CI-repair review cap is exhausted; this chunk cannot be published or closed")
        if disposition != "review_allocated":
            raise LoopError("ledger CI-repair event has an unsupported disposition")
        repair_number = event.get("round")
        repair_round = next(
            (round_state for round_state in rounds if isinstance(round_state, dict) and round_state.get("number") == repair_number),
            None,
        )
        if (
            not isinstance(repair_number, int)
            or repair_round is None
            or repair_round.get("kind") != "ci_failure_repair"
            or repair_round.get("commit") != event.get("proposed_commit")
        ):
            raise LoopError("ledger CI-repair event does not match its immutable review round")
        resolved = any(
            isinstance(round_state, dict)
            and isinstance(round_state.get("number"), int)
            and round_state["number"] >= repair_number
            and isinstance(round_state.get("adjudication"), dict)
            and round_state["adjudication"].get("verdict") in PASSING_VERDICTS
            for round_state in rounds
        )
        if not resolved:
            raise LoopError("CI-repair panel is pending or needs changes; shipping is denied")


def require_passing_reviewed_change(root: Path, spec: dict[str, Any], state: dict[str, Any], action: str) -> None:
    """Keep post-pass shipping on the change the latest panel actually reviewed."""
    if state.get("status") != "passed":
        return
    current = latest_round(state)
    if current is None or current.get("adjudication", {}).get("verdict") not in PASSING_VERDICTS:
        raise LoopError(f"{action} requires a passing adjudicated review round")
    head = git(root, "rev-parse", "HEAD")
    if not reviewed_content_matches(root, spec, state, str(current.get("commit", "")), head):
        raise LoopError(
            f"{action} requires the current branch change to match the latest passing review. "
            "If protected-base movement invalidated that match, run a revalidation; if implementation "
            "changed, admit an exact required-check failure through the original ledger and review the repair"
        )


def require_repair_pr_binding(state: dict[str, Any], pr_number: int, head_sha: str) -> None:
    events = state.get("ci_failure_repairs", [])
    if not events:
        return
    latest = events[-1]
    current = latest_round(state)
    if latest.get("pr_number") != pr_number:
        raise LoopError("pull request does not match the PR bound to the latest CI-repair event")
    if current is None or current.get("adjudication", {}).get("verdict") not in PASSING_VERDICTS:
        raise LoopError("latest ledger round is not passing after CI repair")
    reviewed = str(current.get("commit", ""))
    if not FULL_GIT_SHA_RE.fullmatch(reviewed) or reviewed.lower() != str(head_sha).lower():
        raise LoopError("PR head must equal the full commit SHA reviewed after CI repair")


def require_repair_push_binding(
    root: Path, spec: dict[str, Any], state: dict[str, Any], branch: str, local_head: str
) -> bool:
    """Check the existing repair PR before pushing; return true when already published."""

    events = state.get("ci_failure_repairs", [])
    if not events:
        return False
    latest = events[-1]
    pr = matching_open_repair_pr(root, spec, state)
    if pr["number"] != latest.get("pr_number") or pr["head_branch"] != branch:
        raise LoopError("push does not target the open PR bound to the latest CI-repair event")
    source_sha = provider_ref_sha(root, spec, branch)
    if source_sha.lower() != pr["head_sha"].lower():
        raise LoopError("PR head and source branch moved apart before CI-repair push")
    if source_sha.lower() == local_head.lower():
        return True
    failed_head = latest.get("failed_head")
    if (
        not isinstance(failed_head, str)
        or not FULL_GIT_SHA_RE.fullmatch(failed_head)
        or not is_ancestor(root, failed_head, source_sha)
        or not is_ancestor(root, source_sha, local_head)
    ):
        raise LoopError("remote repair PR head is not an ancestor of the exact reviewed commit")
    return False


def action_ledger_state(
    root: Path,
    spec: dict[str, Any],
    ledger_file: Path | None,
    *,
    issue_number: int | None = None,
    branch: str | None = None,
) -> dict[str, Any]:
    """Resolve the one canonical ledger and apply common publication safeguards."""

    recovered = recovery_publication_state(root, spec, ledger_file)
    if recovered is not None:
        return recovered
    if ledger_file is None:
        raise LoopError("this action requires the selected ordinary ledger via --ledger")
    state = load_state(ledger_file)
    if "recovery" in state:
        raise LoopError("recovery ledger must be resolved through its registered recovery manifest")
    if state.get("spec_id") != spec["id"] or state.get("spec_digest") != digest(spec):
        raise LoopError("ledger was created from a different run manifest")
    if not ledger_openspec_matches(root, spec, state):
        raise LoopError("OpenSpec artifacts changed after ledger initialization; reinitialize the frozen chunk")
    issue = state.get("issue")
    if not isinstance(issue, dict) or not isinstance(issue.get("number"), int) or isinstance(issue.get("number"), bool):
        raise LoopError("ledger has no valid frozen issue identity")
    selected_issue, selected_chunk = chunk_entry(spec, issue["number"], str(state.get("chunk", {}).get("id", "")))
    chunk = state.get("chunk", {})
    if (
        issue.get("slug") != selected_issue["slug"]
        or chunk.get("closure", "complete") != selected_chunk.get("closure", "complete")
    ):
        raise LoopError("ledger issue or chunk identity does not match the frozen manifest")
    if (
        chunk.get("files") != selected_chunk.get("files")
        or chunk.get("requirements") != selected_chunk.get("requirements")
        or chunk.get("acceptance") != selected_chunk.get("acceptance")
        or chunk.get("scope") != selected_chunk.get("scope")
        or chunk.get("lift_targets", []) != selected_chunk.get("lift_targets", [])
        or state.get("max_review_rounds") != spec["limits"]["max_review_rounds_per_chunk"]
        or state.get("reviewers") != spec["review"]["reviewers"]
    ):
        raise LoopError("CI-repair ledger chunk, reviewers, or cap do not match the frozen manifest")
    if any(
        key in state and state[key] != spec[value]
        for key, value in (("repository", "repository"), ("remote", "remote"), ("base_branch", "base_branch"))
    ) or state.get("base_ref") != spec["base_ref"] or Path(str(state.get("repo_root", ""))).resolve() != root.resolve():
        raise LoopError("CI-repair ledger repository, base, or checkout does not match the frozen manifest")
    require_ci_repairs_resolved(state)
    # Pre-protocol ledgers are read with manifest-bound defaults in memory;
    # `ledger init` never rewrites their historical bytes as a migration.
    state.setdefault("repository", spec["repository"])
    state.setdefault("remote", spec["remote"])
    state.setdefault("base_branch", spec["base_branch"])
    state.setdefault("ci_failure_repairs", [])
    require_canonical_ledger_identity(root, ledger_file, state)
    if issue_number is not None and issue["number"] != issue_number:
        raise LoopError("selected ledger issue does not match the requested issue")
    if branch is not None and branch != f"agent/{issue['slug']}":
        raise LoopError("selected ledger issue does not match the current issue branch")
    return state


def ledger_admit_ci_repair(root: Path, spec: dict[str, Any], state_file: Path, candidate: str) -> int:
    """Append exact failed-check evidence and allocate one charged ordinary round."""

    raw_before = state_file.read_bytes()
    state = action_ledger_state(root, spec, state_file)
    if "recovery" in state:
        raise LoopError("CI-failure repair is not available to recovery-managed ledgers")
    require_canonical_ledger_identity(root, state_file, state)
    passed = latest_round(state)
    if state.get("status") != "passed" or passed is None or passed.get("adjudication", {}).get("verdict") not in PASSING_VERDICTS:
        raise LoopError("CI-failure repair requires the latest ordinary review round to have passed")
    number = state["issue"]["number"]
    require_legacy_issue_open(root, spec, number)
    selected_issue = issue_entry(spec, number)
    expected_branch = f"agent/{selected_issue['slug']}"
    require_manifest_remote(root, spec)
    pr = matching_open_repair_pr(root, spec, state)
    if pr["head_repository"].casefold() != spec["repository"].casefold():
        raise LoopError("pull request source repository does not match the manifest")
    source_sha = provider_ref_sha(root, spec, expected_branch)
    if source_sha.lower() != pr["head_sha"].lower():
        raise LoopError("pull-request head and live source-branch head disagree")
    base_sha = provider_ref_sha(root, spec, spec["base_branch"])
    if base_sha.lower() != pr["base_sha"].lower():
        raise LoopError("pull-request base snapshot is stale relative to the live protected base")
    repaired_commit = validate_repair_candidate(root, spec, state, pr["head_sha"], candidate)
    protected = strict_protected_check_map(root, spec)
    evidence = required_check_failure_evidence(root, spec, pr["head_sha"], protected)
    protected_after = strict_protected_check_map(root, spec)
    if protected_after != protected:
        raise LoopError("required-check protection changed during CI-failure admission")
    reread_repair_provider_state(root, spec, state, pr, base_sha)
    require_legacy_issue_open(root, spec, number)
    require_manifest_remote(root, spec)
    protected_before_write = strict_protected_check_map(root, spec)
    if protected_before_write != protected:
        raise LoopError("required-check protection changed during CI-failure admission")
    # A same-head rerun may turn the initial failure green while the other
    # provider snapshots are being reread. Use the final required-check
    # snapshot for the event and do not charge a review round after recovery.
    current_evidence = required_check_failure_evidence(root, spec, pr["head_sha"], protected_before_write)
    # The check-run query is a separate provider request. Revalidate the PR,
    # refs, issue, remotes, and protection after it so movement during that
    # query cannot bind the evidence to a stale head or policy.
    reread_repair_provider_state(root, spec, state, pr, base_sha)
    require_legacy_issue_open(root, spec, number)
    require_manifest_remote(root, spec)
    protected_after_evidence = strict_protected_check_map(root, spec)
    if protected_after_evidence != protected:
        raise LoopError("required-check protection changed during CI-failure admission")
    if state_file.read_bytes() != raw_before:
        raise LoopError("ledger changed while CI-failure evidence was being collected; no repair was admitted")

    events = state.get("ci_failure_repairs", [])
    if not isinstance(events, list):
        raise LoopError("ledger CI-repair event list is malformed")
    events = list(events)
    sequence = len(events) + 1
    event: dict[str, Any] = {
        "sequence": sequence,
        "prior_passing_round": passed["number"],
        "failed_head": pr["head_sha"],
        "required_check": current_evidence,
        "pr_number": pr["number"],
        "pr_url": pr["url"],
        "source_repository": pr["head_repository"],
        "source_branch": pr["head_branch"],
        "base_branch": pr["base_branch"],
        "base_sha": base_sha.lower(),
        "proposed_commit": repaired_commit,
        "recorded_at": utc_now(),
    }
    used = improvement_rounds_used(state)
    if used >= state["max_review_rounds"]:
        event.update({"disposition": "cap_exhausted", "round": None})
        events.append(event)
        state["ci_failure_repairs"] = events
        state["status"] = "repair_exhausted"
        write_json(state_file, state)
        print(f"CAP EXHAUSTED: CI failure recorded for PR #{pr['number']}; no review slot remains")
        return 0

    next_number = (state["rounds"][-1].get("number", 0) + 1) if state.get("rounds") else 1
    event.update({"disposition": "review_allocated", "round": next_number})
    events.append(event)
    state["ci_failure_repairs"] = events
    repair_round = {
        "number": next_number,
        "commit": repaired_commit,
        "reviews": [],
        "adjudication": None,
        "kind": "ci_failure_repair",
        "base_commit": base_sha.lower(),
    }
    state["rounds"].append(repair_round)
    state["status"] = "reviewing"
    write_json(state_file, state)
    print(f"PASS CI-failure repair admitted: PR #{pr['number']} round={next_number} commit={repaired_commit}")
    return 0


def action_approve(
    root: Path,
    spec: dict[str, Any],
    pr_number: int,
    ledger_file: Path,
    body: str,
    dry_run: bool,
) -> int:
    authorize_action(root, spec, "approve")
    predecessor_proofs = require_predecessor_prs(root, spec)
    state = action_ledger_state(root, spec, ledger_file)
    if state.get("spec_id") != spec["id"] or state.get("spec_digest") != digest(spec):
        raise LoopError("ledger was created from a different run manifest")
    if not ledger_openspec_matches(root, spec, state):
        raise LoopError("OpenSpec artifacts changed after ledger initialization; reinitialize the frozen chunk")
    if state.get("status") != "passed":
        raise LoopError(f"ledger status is {state.get('status')!r}; approval requires status 'passed'")
    current = latest_round(state)
    if current is None or current.get("adjudication", {}).get("verdict") not in PASSING_VERDICTS:
        raise LoopError("approval requires a passing adjudicated review round")
    pr = gh_json(
        root,
        [
            "pr",
            "view",
            str(pr_number),
            "--repo",
            spec["repository"],
            "--json",
            "headRefName,headRefOid,state,isDraft,baseRefName,body,files",
        ],
    )
    if pr.get("state") != "OPEN" or pr.get("isDraft"):
        raise LoopError("approval requires an open, non-draft PR")
    require_pr_targets_base(pr, spec)
    require_pr_matches_frozen_issue(pr, state)
    require_repair_pr_binding(state, pr_number, str(pr.get("headRefOid") or ""))
    require_predecessor_merges_ancestor(root, predecessor_proofs, pr.get("headRefOid", ""), "PR head")
    if not reviewed_content_matches(root, spec, state, str(current.get("commit", "")), str(pr.get("headRefOid", ""))):
        raise LoopError("PR head does not carry the change reviewed by the passing ledger")
    verify_remote_chunk_files(root, spec, pr, state)
    require_published_head_has_no_links(root, spec, state, str(pr.get("headRefOid", "")))
    check_required_checks(root, spec, pr_number)
    args = [
        "gh",
        "pr",
        "review",
        str(pr_number),
        "--repo",
        spec["repository"],
        "--approve",
        "--body",
        body,
    ]
    if dry_run:
        print("DRY-RUN " + " ".join(args[:7]) + " <body>")
        return 0
    run_command(root, args, check=True)
    print(f"PASS PR approved: #{pr_number}")
    return 0


def build_merge_command(
    spec: dict[str, Any],
    pr_number: int,
    head_sha: str,
    method: str | None,
    auto: bool,
    admin: bool,
    delete_branch: bool | None,
) -> list[str]:
    """Build a race-resistant merge command from an explicitly authorized policy."""

    policy = merge_policy(spec)
    selected_method = method or policy["method"]
    if selected_method not in MERGE_METHODS:
        raise LoopError("merge method must be merge, squash, or rebase")
    if method is not None and method != policy["method"] and not policy["allow_method_override"]:
        raise LoopError("merge method override is disabled by spec.merge.allow_method_override")
    if auto and not policy["allow_auto"]:
        raise LoopError("auto-merge is disabled by spec.merge.allow_auto")
    if admin and not policy["allow_admin"]:
        raise LoopError("admin merge is disabled by spec.merge.allow_admin")
    if auto and admin:
        raise LoopError("--auto and --admin are mutually exclusive")
    selected_delete_branch = policy["delete_branch"]
    if delete_branch is not None:
        if not policy["allow_delete_branch_override"]:
            raise LoopError(
                "branch-deletion override is disabled by "
                "spec.merge.allow_delete_branch_override"
            )
        selected_delete_branch = delete_branch

    args = [
        "gh",
        "pr",
        "merge",
        str(pr_number),
        "--repo",
        spec["repository"],
        f"--{selected_method}",
        "--match-head-commit",
        head_sha,
        "--delete-branch" if selected_delete_branch else "--delete-branch=false",
    ]
    if auto:
        args.append("--auto")
    if admin:
        args.append("--admin")
    return args


def action_merge(
    root: Path,
    spec: dict[str, Any],
    pr_number: int,
    ledger_file: Path,
    method: str | None,
    auto: bool,
    admin: bool,
    delete_branch: bool | None,
    dry_run: bool,
) -> int:
    authorize_action(root, spec, "merge")
    if admin and not owner_reviewed_legacy_manifest(root, spec):
        raise LoopError("administrator merge is never available to a branch-authored manifest")
    predecessor_proofs = require_predecessor_prs(root, spec)
    state = action_ledger_state(root, spec, ledger_file)
    merge_policy(spec)
    if state.get("spec_id") != spec["id"] or state.get("spec_digest") != digest(spec):
        raise LoopError("merge ledger was created from a different run manifest")
    if not ledger_openspec_matches(root, spec, state):
        raise LoopError("OpenSpec artifacts changed after ledger initialization; refusing to merge")
    if state.get("status") != "passed":
        raise LoopError("merge requires a passing review ledger")
    current = latest_round(state)
    if current is None or current.get("adjudication", {}).get("verdict") not in PASSING_VERDICTS:
        raise LoopError("merge requires a passing adjudicated review round")
    # Refuse a disallowed method, auto or admin request before any provider call.
    build_merge_command(spec, pr_number, str(current["commit"]), method, auto, admin, delete_branch)
    checked_head = (
        None
        if admin and not state.get("ci_failure_repairs")
        else check_required_checks(root, spec, pr_number)
    )
    pr = gh_json(
        root,
        [
            "pr",
            "view",
            str(pr_number),
            "--repo",
            spec["repository"],
            "--json",
            "state,isDraft,headRefName,headRefOid,baseRefName,body,files,comments",
        ],
    )
    if pr.get("state") != "OPEN" or pr.get("isDraft"):
        raise LoopError("merge requires an open, non-draft PR")
    require_pr_targets_base(pr, spec)
    require_pr_matches_frozen_issue(pr, state)
    require_repair_pr_binding(state, pr_number, str(pr.get("headRefOid") or ""))
    require_predecessor_merges_ancestor(root, predecessor_proofs, pr.get("headRefOid", ""), "PR head")
    if not reviewed_content_matches(root, spec, state, str(current.get("commit", "")), str(pr.get("headRefOid", ""))):
        raise LoopError("PR head does not carry the change reviewed by the passing ledger")
    verify_remote_chunk_files(root, spec, pr, state)
    require_published_head_has_no_links(root, spec, state, str(pr.get("headRefOid", "")))
    if predecessor_attestation_policy(spec)["emit"]:
        payload = predecessor_attestation_from_state(state, pr["headRefOid"])
        require_exact_predecessor_attestation(pr, payload, spec["actor"], pr_number)
    if isinstance(checked_head, str) and checked_head and checked_head.lower() != str(pr.get("headRefOid", "")).lower():
        raise LoopError("PR head moved between the check read and verification; rerun the merge")
    # Pin the head just verified to carry the reviewed change: a push after
    # this point makes the provider refuse the merge instead of landing it.
    args = build_merge_command(spec, pr_number, str(pr["headRefOid"]), method, auto, admin, delete_branch)
    if dry_run:
        print("DRY-RUN " + " ".join(args))
        return 0
    run_command(root, args, check=True)
    if auto:
        print(f"PASS PR queued for auto-merge: #{pr_number}")
    elif admin:
        print(f"PASS PR admin-merged: #{pr_number}")
    else:
        print(f"PASS PR merged: #{pr_number}")
    return 0


def add_common_spec_parser(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--spec", required=True, type=Path, help="path to the YAML loop specification")
    parser.add_argument("--repo-root", type=Path, default=Path.cwd(), help="repository root")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    validate_parser = sub.add_parser("validate", help="validate a loop specification")
    add_common_spec_parser(validate_parser)

    preflight_parser = sub.add_parser("preflight", help="run read-only repository/provider preflight")
    add_common_spec_parser(preflight_parser)

    ledger_parser = sub.add_parser("ledger", help="create and update the bounded review ledger")
    ledger_sub = ledger_parser.add_subparsers(dest="ledger_command", required=True)
    init_parser = ledger_sub.add_parser("init")
    add_common_spec_parser(init_parser)
    init_parser.add_argument("--issue", required=True, type=int)
    init_parser.add_argument("--chunk-id", required=True)
    init_parser.add_argument("--state-dir")
    record_parser = ledger_sub.add_parser("record-review")
    record_parser.add_argument("--state", required=True, type=Path)
    record_parser.add_argument("--reviewer", required=True)
    record_parser.add_argument("--commit", required=True)
    record_parser.add_argument(
        "--verdict", required=True, choices=sorted(CONTRACT_VERDICT_TOKENS)
    )
    record_parser.add_argument(
        "--lift-target",
        help="module or path the generalization belongs in; required with pass_with_lift",
    )
    record_parser.add_argument("--finding", help="one-line summary; not evidence and cannot stand alone")
    record_parser.add_argument("--resolutions-file", type=Path, help="JSON evidence map for every inherited recovery finding")
    record_parser.add_argument(
        "--finding-file",
        type=Path,
        help="path to the reviewer's verbatim final message; required before the round can be adjudicated",
    )
    adjudicate_parser = ledger_sub.add_parser("adjudicate")
    adjudicate_parser.add_argument("--state", required=True, type=Path)
    adjudicate_parser.add_argument(
        "--verdict", required=True, choices=sorted(CONTRACT_VERDICT_TOKENS)
    )
    adjudicate_parser.add_argument("--note")
    admit_parser = ledger_sub.add_parser(
        "admit-ci-repair", help="record exact required-check failure evidence and reserve a charged repair round"
    )
    add_common_spec_parser(admit_parser)
    admit_parser.add_argument("--state", required=True, type=Path)
    admit_parser.add_argument("--commit", required=True, help="full local repair candidate commit SHA")
    show_parser = ledger_sub.add_parser("show")
    show_parser.add_argument("--state", required=True, type=Path)

    recovery_parser = sub.add_parser("recovery", help="dispatch bounded research and resume the same objective")
    recovery_sub = recovery_parser.add_subparsers(dest="recovery_command", required=True)
    for command in ("next", "start-round", "submit-plan", "review-plan", "resume", "exhaust"):
        child = recovery_sub.add_parser(command)
        child.add_argument("--ledger", required=True, type=Path)
        if command == "start-round":
            child.add_argument("--commit", required=True)
        if command in {"submit-plan", "review-plan"}:
            child.add_argument("--file", required=True, type=Path)
        if command == "exhaust":
            child.add_argument("--reason", required=True)

    action_parser = sub.add_parser("action", help="perform an explicitly authorized remote action")
    action_sub = action_parser.add_subparsers(dest="action_command", required=True)
    comment_parser = action_sub.add_parser("comment")
    add_common_spec_parser(comment_parser)
    comment_parser.add_argument("--issue", required=True, type=int)
    comment_parser.add_argument("--body", required=True)
    comment_parser.add_argument("--dry-run", action="store_true")
    close_parser = action_sub.add_parser("close")
    add_common_spec_parser(close_parser)
    close_parser.add_argument("--issue", required=True, type=int)
    close_parser.add_argument("--merged-pr", type=int)
    close_parser.add_argument("--ledger", required=True, type=Path)
    close_parser.add_argument("--comment")
    close_parser.add_argument("--dry-run", action="store_true")
    push_parser = action_sub.add_parser("push")
    add_common_spec_parser(push_parser)
    push_parser.add_argument("--ledger", required=True, type=Path)
    push_parser.add_argument("--branch")
    push_parser.add_argument("--force-with-lease", action="store_true")
    push_parser.add_argument("--dry-run", action="store_true")
    create_parser = action_sub.add_parser("create-pr")
    add_common_spec_parser(create_parser)
    create_parser.add_argument("--issue", required=True, type=int)
    create_parser.add_argument("--ledger", required=True, type=Path)
    create_parser.add_argument("--title", required=True)
    create_parser.add_argument("--body-file", required=True)
    create_parser.add_argument("--draft", action="store_true")
    create_parser.add_argument("--dry-run", action="store_true")
    attest_parser = action_sub.add_parser(
        "attest-pr", help="write the controller-derived predecessor marker for a passing source PR"
    )
    add_common_spec_parser(attest_parser)
    attest_parser.add_argument("--issue", required=True, type=int)
    attest_parser.add_argument("--pr", required=True, type=int)
    attest_parser.add_argument("--ledger", required=True, type=Path)
    attest_parser.add_argument("--dry-run", action="store_true")
    ready_parser = action_sub.add_parser("ready", help="mark a draft PR ready once its ledger passes")
    add_common_spec_parser(ready_parser)
    ready_parser.add_argument("--pr", required=True, type=int)
    ready_parser.add_argument("--ledger", required=True, type=Path)
    ready_parser.add_argument("--dry-run", action="store_true")
    follow_up_parser = action_sub.add_parser(
        "follow-up", help="file a follow-up issue linked to a selected issue and its milestone"
    )
    add_common_spec_parser(follow_up_parser)
    follow_up_parser.add_argument("--issue", required=True, type=int, help="the selected parent issue")
    follow_up_parser.add_argument("--title", required=True)
    follow_up_parser.add_argument("--body-file", required=True)
    follow_up_parser.add_argument("--label", action="append", default=[])
    follow_up_parser.add_argument("--dry-run", action="store_true")
    approve_parser = action_sub.add_parser("approve")
    add_common_spec_parser(approve_parser)
    approve_parser.add_argument("--pr", required=True, type=int)
    approve_parser.add_argument("--ledger", required=True, type=Path)
    approve_parser.add_argument("--body", required=True)
    approve_parser.add_argument("--dry-run", action="store_true")
    merge_parser = action_sub.add_parser("merge")
    add_common_spec_parser(merge_parser)
    merge_parser.add_argument("--pr", required=True, type=int)
    merge_parser.add_argument("--ledger", required=True, type=Path)
    merge_parser.add_argument("--method", choices=sorted(MERGE_METHODS))
    merge_parser.add_argument("--auto", action="store_true", help="request provider auto-merge")
    merge_parser.add_argument("--admin", action="store_true", help="request an explicit administrator merge")
    delete_group = merge_parser.add_mutually_exclusive_group()
    delete_group.add_argument("--delete-branch", dest="delete_branch", action="store_true")
    delete_group.add_argument("--keep-branch", dest="delete_branch", action="store_false")
    merge_parser.set_defaults(delete_branch=None)
    merge_parser.add_argument("--dry-run", action="store_true")
    return parser


def dispatch(args: argparse.Namespace, parser: argparse.ArgumentParser) -> int:
    try:
        if args.command == "validate":
            root = args.repo_root.resolve()
            return print_validation(repo_path(root, args.spec), root)
        if args.command == "preflight":
            root = args.repo_root.resolve()
            return preflight(root, repo_path(root, args.spec))
        if args.command == "ledger":
            if args.ledger_command == "init":
                root = args.repo_root.resolve()
                return ledger_init(root, repo_path(root, args.spec), args.issue, args.chunk_id, args.state_dir)
            if args.ledger_command == "record-review":
                return ledger_record_review(
                    args.state.resolve(),
                    args.reviewer,
                    args.commit,
                    args.verdict,
                    args.finding,
                    args.finding_file.resolve() if args.finding_file else None,
                    args.lift_target,
                    args.resolutions_file,
                )
            if args.ledger_command == "adjudicate":
                return ledger_adjudicate(args.state.resolve(), args.verdict, args.note)
            if args.ledger_command == "admit-ci-repair":
                root = args.repo_root.resolve()
                spec = load_spec(repo_path(root, args.spec), root, verify_owner_review=True)
                return ledger_admit_ci_repair(root, spec, args.state.resolve(), args.commit)
            if args.ledger_command == "show":
                return ledger_show(args.state.resolve())
        if args.command == "recovery":
            return recovery_command(args.recovery_command, args.ledger.resolve(),
                commit=getattr(args, "commit", None), file=getattr(args, "file", None),
                reason=getattr(args, "reason", None))
        if args.command == "action":
            root = args.repo_root.resolve()
            spec = load_spec(repo_path(root, args.spec), root, verify_owner_review=True)
            if args.action_command == "comment":
                return action_comment(root, spec, args.issue, args.body, args.dry_run)
            if args.action_command == "close":
                return action_close(
                    root, spec, args.issue, args.merged_pr, args.comment, args.dry_run, args.ledger.resolve()
                )
            if args.action_command == "push":
                return action_push(
                    root, spec, args.branch, args.force_with_lease, args.dry_run, args.ledger.resolve()
                )
            if args.action_command == "create-pr":
                return action_create_pr(
                    root,
                    spec,
                    args.issue,
                    args.ledger.resolve(),
                    args.title,
                    args.body_file,
                    args.draft,
                    args.dry_run,
                )
            if args.action_command == "attest-pr":
                return action_attest_pr(
                    root,
                    spec,
                    args.issue,
                    args.pr,
                    args.ledger.resolve(),
                    args.dry_run,
                )
            if args.action_command == "ready":
                return action_ready(root, spec, args.pr, args.ledger.resolve(), args.dry_run)
            if args.action_command == "follow-up":
                return action_follow_up(
                    root, spec, args.issue, args.title, args.body_file, args.label, args.dry_run
                )
            if args.action_command == "approve":
                return action_approve(root, spec, args.pr, args.ledger.resolve(), args.body, args.dry_run)
            if args.action_command == "merge":
                return action_merge(
                    root,
                    spec,
                    args.pr,
                    args.ledger.resolve(),
                    args.method,
                    args.auto,
                    args.admin,
                    args.delete_branch,
                    args.dry_run,
                )
    except (LoopError, loop_recovery.RecoveryError) as exc:
        print(f"FAIL {exc}")
        return 1
    except (OSError, ValueError, TypeError) as exc:
        print(f"FAIL unexpected local controller error: {exc}")
        return 1
    parser.error("unhandled command")
    return 2


def main(argv: list[str] | None = None) -> int:
    force_utf8_output()
    parser = build_parser()
    args = parser.parse_args(argv)
    root = getattr(args, "repo_root", None)
    if root is None:
        ledger = getattr(args, "state", None) or getattr(args, "ledger", None)
        root = ledger.resolve().parent if ledger else Path.cwd()
    try:
        with controller_lock(root.resolve()):
            return dispatch(args, parser)
    except (OSError, ValueError, RuntimeError) as exc:
        print(f"FAIL controller: {exc}")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
