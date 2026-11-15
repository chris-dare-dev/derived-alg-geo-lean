/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/

import DerivedAlgGeo
import DerivedAlgGeo.Development

/-!
# The sweep umbrella

The module `scripts/AxiomAudit.lean` imports, so that the audit's environment
contains every Lean module in this repository.

## Main definitions

None. The module declares nothing.

## Main results

None.

## Implementation notes

`DerivedAlgGeo.lean` is the public library, and development probes are kept out
of it. The axiom audit must still see them, so this root imports the public
umbrella and the probes. A module neither of them reaches is not audited;
`scripts/check_root_reachability.py` fails on one.

## References

None.

## Tags

axiom audit, sweep, umbrella
-/
