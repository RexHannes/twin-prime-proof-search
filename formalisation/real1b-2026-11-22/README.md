# REAL 1B · independent Lean replay

**Twin-prime infinitude is open.** This replay checks 55 named results, including the exact weighted identities, a finite Vaughan decomposition on the physical source, a positive numerical margin, a prime-power error estimate, and two conditional implications for twin primes. The H2-B implication has five hypotheses. Their precise statements and mathematical status appear in the [dependency table](DEPENDENCIES.md).

## Run it in a browser

[Open the combined source in Live Lean](https://live.lean-lang.org/#project=mathlib-v4.28.0&url=https%3A%2F%2Fraw.githubusercontent.com%2FRexHannes%2Ftwin-prime-proof-search%2Fmain%2Fformalisation%2Freal1b-2026-11-22%2FReplay.lean). The replay includes every project definition it uses and imports Mathlib. To use the environment recorded in the verification file, paste the [single Lean file](Replay.lean) into [AXLE](https://axle.axiommath.ai/check), select `lean-4.28.0`, clear **ignore_imports**, and select **RUN**. Inspect the theorem types as well as the `#print axioms` output.

## Independently verify a checkout

From the repository root, the following command regenerates the expected replay in memory, compares it byte for byte with the committed file, checks its SHA-256, and submits a new AXLE request. It checks the returned source, diagnostics, and axiom dependencies of all 55 named results. Python 3.9+ and network access are sufficient.

```sh
python3 formalisation/real1b-2026-11-22/verify.py --online
```

To use the repository's pinned toolchain and your own Lean kernel, run the following command with Lake available. It obtains the Mathlib cache, builds the actual imported modules, and audits the exported declarations from a fresh Lean process. Running both modes checks both forms of the program.

```sh
python3 formalisation/real1b-2026-11-22/verify.py --lake
```

The Lake build target is `RequestProject.REAL1B_20261122`. For a repeatable review, use the **Copy permalink** action on this file and check out the corresponding commit. The [verification record](Verification.json) contains the replay digest, environment, request ID, declaration list and compiler output. It records the online run. Standard axioms allowed by the reviewer script are `propext`, `Classical.choice` and `Quot.sound`.

## Read the mathematical endpoints

- **H2-B.** [SieveInputs.lean](../../RequestProject/REAL1B_20261122/SieveInputs.lean) ends with `infinite_of_paper_inputs`. It consumes an H1 squarefree lower estimate with valid sieve rows, a rough triple cap, a Type-I calibration, a cutoff-collar estimate, and a full Type-II upper bound. [Vaughan.lean](../../RequestProject/REAL1B_20261122/Vaughan.lean) gives the actual coefficients of that last sum.
- **Ford–Maynard.** [FMSource.lean](../../RequestProject/REAL1B_20261122/FMSource.lean) ends with `infinite_of_source_residual`. It uses a lower comparison, a signed residual upper estimate, and eventual positivity of the comparator prime baseline. All three refer to the specified source sums.
- **Comparison with the historical GitHub detector.** [SourceBridge.lean](../../RequestProject/REAL1B_20261122/SourceBridge.lean) accounts separately for proper prime powers, the change of logarithmic weight, and both differences between the windows under the shift by two.

The aggregate [Lean entry point](../../RequestProject/REAL1B_20261122.lean) imports both routes. They are independent sufficient conditions. [Theorem and source map](DEPENDENCIES.md)
