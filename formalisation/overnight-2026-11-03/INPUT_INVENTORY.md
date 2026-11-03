# Input inventory for the 3 November 2026 overnight task

Repository baseline: `eafb148815db9f216b5e0f5d7daee47cf32c149f`. Lean: `leanprover/lean4:v4.28.0`; Mathlib: `v4.28.0`, with the existing `lake-manifest.json` unchanged.

The exact task brief is in `REQUEST.md`, extracted verbatim from the user attachment. SHA-256 of the entire original attachment: `802afa5c32d4e7594078c1b53d732a42b09bffe0426f7bfaa6e7bf9eede83e53`.

## Available actual bank

- `Gate1B/R11/` (including `Bank.lean`, `CanonicalSource.lean`, `Reciprocity.lean`, `Determinant.lean`, and axiom/status modules).
- `Gate1B/R11/Frontier/` and `Gate1B/SafeAlgebra/`.
- Other Gate1B and physical-source modules; locate and check actual declarations. A distinct `PostR11Final` project is not presumed restored merely because the brief mentions it.

## Current GitHub source update

`papers/real1b-route-a-b-2026-11-03/` contains a 2 November Route A paper and a 3 November Route B paper, plus a README with their hashes. These papers concern roughness exponent `8/31`; their reported analytic claims are manuscript claims requiring verification, not new Lean theorems.

The attached Gold 5.0 brief instead uses roughness exponent `21/100`, the detector `(1-2t)^2`, and 151 cuts `u_j=21/100+j/2000`. Do not substitute the Route A/B source, error ledger, detector or normalization into Gold 5.0. Treat them as separate source families.

## Missing specification

The complete Gold 5.0 manuscript, the full definitions of A_h, M_h and P_{4,h}, and the exact transcendental/numerical enclosure ledger producing the ellipsis coefficient `0.000222501725768692...` are not supplied. Do not certify that coefficient from a truncated decimal or replace those quantities with unconstrained proxies.

Proceed with faithfully defined physical weights, exact finite sector/sign algebra, the 151-cut weight positivity and staircase results, and explicit conditional positivity implications that are fully specified. State every support and partition assumption. Register missing exact ledger / asymptotic inputs and open signed arithmetic explicitly.
