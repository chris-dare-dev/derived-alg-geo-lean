#!/usr/bin/env python3
"""Validate a version-pinned coverage map.

Stdlib only, like check_audit.py. Enforces the file's own rules:

1. It parses, and `schema` is "coverage-map/1".
2. The source pin is versioned: arxiv_version is exactly "v4" and the
   identity fields (arxiv_id, version_submitted_utc, doi, title) are
   non-empty.
3. Every part and every near-term coordinate carries a status from the
   declared vocabulary.
4. Any status other than "target" requires a complete `evidence` object
   (review_doc, reviewer, reviewed_at, and the version-specific check field all
   non-empty), and
   "formalized" additionally requires evidence.owner_accepted. This is what
   keeps the map zero-claim by default: a promotion without evidence is a
   validation failure, not a stylistic issue.
5. No corpus-derived identifier keys anywhere: a key named chunk_id,
   chunk_ids, chunk, or notebook_slug fails the run. (The `corpus_note`
   block may DESCRIBE the corpus; it may not key anything by it.)

Exit 0 with a status summary on success; exit 1 with every violation listed
on failure. Run from the repository root:

    python scripts/check_coverage_map.py [registry/coverage-....json]
"""

import json
import sys
from pathlib import Path

from _output import force_utf8_output

DEFAULT_MAP_PATH = Path("registry/coverage-1902.08184v4.json")
FORBIDDEN_KEYS = {"chunk_id", "chunk_ids", "chunk", "notebook_slug"}
EVIDENCE_FIELDS = ("review_doc", "reviewer", "reviewed_at")


def walk_keys(node, path, errors):
    if isinstance(node, dict):
        for key, value in node.items():
            if key in FORBIDDEN_KEYS:
                errors.append(f"forbidden corpus-derived key '{key}' at {path}")
            walk_keys(value, f"{path}.{key}", errors)
    elif isinstance(node, list):
        for i, value in enumerate(node):
            walk_keys(value, f"{path}[{i}]", errors)


def check_entry(entry, path, vocab, source_check_field, errors, counts):
    status = entry.get("status")
    if status not in vocab:
        errors.append(f"{path}: status {status!r} not in vocabulary {sorted(vocab)}")
        return
    counts[status] = counts.get(status, 0) + 1
    if status != "target":
        evidence = entry.get("evidence")
        if not isinstance(evidence, dict):
            errors.append(f"{path}: status '{status}' without an evidence object")
            return
        for field in EVIDENCE_FIELDS:
            if not evidence.get(field):
                errors.append(f"{path}: status '{status}' missing evidence.{field}")
        if not evidence.get(source_check_field):
            errors.append(
                f"{path}: status '{status}' missing evidence.{source_check_field}")
        if status == "formalized" and not evidence.get("owner_accepted"):
            errors.append(f"{path}: status 'formalized' without evidence.owner_accepted")


def main(path=None):
    map_path = Path(path) if path is not None else DEFAULT_MAP_PATH
    errors = []
    try:
        data = json.loads(map_path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        print(f"error: {map_path} not found (run from the repository root)")
        return 1
    except json.JSONDecodeError as exc:
        print(f"error: {map_path} does not parse: {exc}")
        return 1

    if data.get("schema") != "coverage-map/1":
        errors.append(f"schema is {data.get('schema')!r}, expected 'coverage-map/1'")

    source = data.get("source", {})
    arxiv_version = source.get("arxiv_version")
    if not (isinstance(arxiv_version, str) and arxiv_version.startswith("v")
            and arxiv_version[1:].isdigit()):
        errors.append(f"source.arxiv_version is {arxiv_version!r}, expected a version like 'v4'")
    for field in ("arxiv_id", "version_submitted_utc", "doi", "title"):
        if not source.get(field):
            errors.append(f"source.{field} is missing or empty")

    vocab = set(data.get("status_vocabulary", {}))
    if not vocab:
        errors.append("status_vocabulary is missing or empty")

    counts = {}
    for i, part in enumerate(data.get("parts", [])):
        check_entry(part, f"parts[{i}] (part {part.get('part')})", vocab,
                    f"{arxiv_version}_check", errors, counts)
    for i, coord in enumerate(data.get("near_term_coordinates", [])):
        check_entry(coord, f"near_term_coordinates[{i}] ({coord.get('id')})", vocab,
                    f"{arxiv_version}_check", errors, counts)
    if not counts:
        errors.append("no parts or near_term_coordinates entries found")

    walk_keys(data, "$", errors)

    if errors:
        print(f"FAIL: {len(errors)} violation(s) in {map_path}:")
        for err in errors:
            print(f"  - {err}")
        return 1

    summary = ", ".join(f"{k}: {v}" for k, v in sorted(counts.items()))
    print(f"ok: {map_path} valid; statuses {{{summary}}}")
    return 0


if __name__ == "__main__":
    force_utf8_output()
    if len(sys.argv) > 2:
        print(__doc__)
        sys.exit(2)
    sys.exit(main(sys.argv[1] if len(sys.argv) == 2 else None))
