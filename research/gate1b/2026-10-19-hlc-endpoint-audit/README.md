# Gate 1B — HLC / endpoint audit, 19 October 2026

Research checkpoint only. Full R11, HSTAR, rough mixed Type-II cancellation and rough endpoint covariance remain OPEN.

The supplied report required one substantive repair: the detector-row Gram cross term was bounded using the complementary coefficient Gamma. REPORT.md replaces that step with a correct L1/L-infinity detector-row estimate. The sparse endpoint conclusion survives, uniformly under the explicitly stated source envelopes. This is not a new estimate for the remaining rough covariance.

| Item | Audit status |
|---|---|
| Fixed-K HLC literal slope exclusion | PASS, direct substitution only |
| Moment population loss | PASS with asymptotic-constant clarification |
| Endpoint scalar roughening | PASS with actual primorial-support inclusion |
| Endpoint Gram transport | REPAIR -> scoped paper-level PASS |
| No-long-Mobius prime-slot distinction | PASS, source-local same-argument scope only |
| Full occurrence/provider coverage | OPEN |
| Both terminal analytic owners | OPEN |

Run `python verify.py --output CERTIFICATE.json`. The checks are exact finite regressions, not asymptotic proofs or a Lean certificate. The original 4,276-count checker was also rerun, but its floating-point and support-only checks are not promoted to exact analytic certification.

Files: REPORT.md (complete proofs), CONTINUATION.md (next task), verify.py, CERTIFICATE.json, SOURCES.json. No authoritative repository source or compiler is modified by this checkpoint.
