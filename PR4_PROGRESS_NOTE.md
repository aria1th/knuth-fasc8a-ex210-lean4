# PR4 progress note

This branch is moving the visible-factor certificate toward a closed Lean checker.

Current stable additions include:

- a pure byte parser core;
- canonical hex exports of the small visible-factor payloads;
- executable parsing of `KMP101` and `KMV101` payloads;
- a first `VerifiedBy`-based metadata certificate for the embedded visible payload.

The next repair step is to normalize the parser soundness witnesses and remove the experimental recurrence module from the build root.
