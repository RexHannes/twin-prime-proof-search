# REAL 1B · independent Lean replay

**Twin-prime infinitude is open.** The Gold 4.66 direct route now includes a proof that the two good-set definitions are equivalent, exact large-owner accounting and a conditional implication from the whole outside-box bound. [Gold 4.66 source dictionary, constants and open premises](FM-DIRECT.md)

Earlier results include the exact weighted identities, a finite Vaughan decomposition on the physical source, a positive numerical margin, a prime-power error estimate, and the Gold 4.60 conditional implication from the signed FM complement. The H2-B implication has five hypotheses. Their precise statements and mathematical status appear in the [dependency table](DEPENDENCIES.md).

Gold 4.67 verifies the original-source prime-power and squareful-input estimates, good-set support, all four continuous positive-collar integrals, the exact omitted semiprime strip, the signed Vaughan and ledger decompositions, the exact five-prime divisor formula, integrability and strict positivity of its integral, and the six unweighted profile counts. [Analytic theorem inventory and remaining estimates](FM-ANALYTIC.md)

## Check out the analytic route

```sh
git clone --depth 1 --branch real1b-gold467-analytic https://github.com/RexHannes/twin-prime-proof-search.git
cd twin-prime-proof-search
```

## Run it in a browser

The historical Gold 4.60 replay is pinned to commit `6e6c65e`. The GitHub-hosted Lake job starts from a clean checkout, builds the imported modules, runs both finite verifiers and prints all 81 theorem types and axiom lists. [Open this replay in Chromium](https://live.lean-lang.org/#project=mathlib-v4.28.0&url=https%3A%2F%2Fraw.githubusercontent.com%2FRexHannes%2Ftwin-prime-proof-search%2F6e6c65e00d89861180516b85bbefa9f26935581d%2Fformalisation%2Freal1b-2026-11-22%2FReplay.lean) · [Native Lake run and log](https://github.com/RexHannes/twin-prime-proof-search/actions/runs/45055431579)

[Open the combined source in Live Lean](https://live.lean-lang.org/#project=mathlib-v4.28.0&url=https%3A%2F%2Fraw.githubusercontent.com%2FRexHannes%2Ftwin-prime-proof-search%2Freal1b-gold467-analytic%2Fformalisation%2Freal1b-2026-11-22%2FReplay.lean). The replay includes every project definition it uses and imports Mathlib. To use the environment recorded in the verification file, paste the [single Lean file](Replay.lean) into [AXLE](https://axle.axiommath.ai/check), select `lean-4.28.0`, clear **ignore_imports**, and select **RUN**. Inspect the theorem types as well as the `#print axioms` output.

## Independently verify a checkout

From the repository root, the following command regenerates the expected replay in memory, compares it byte for byte with the committed file, checks its SHA-256, reruns the original Gold 4.59 finite verifier against its registry, recalculates the Gold 4.60 boxwise margin, checks both Gold 4.65 full-box numerators and submits a new AXLE request. It checks the returned source, diagnostics, and axiom dependencies of every audited result. Python 3.9+ and network access are sufficient.

```sh
python3 formalisation/real1b-2026-11-22/verify.py --online
```

To check all 6,414,336 integer cells on a computer with the pinned Lean toolchain already installed, run the following command. It builds the same column proofs sequentially against Lean’s standard library in a temporary Lake project. It removes its temporary build files when it exits.

```sh
python3 formalisation/real1b-2026-11-22/verify.py --local-grid
```

To check the analytic modules, integral proof, and closing theorem together with your own Lean kernel, run the following command with Lake available. It obtains the Mathlib cache, builds the actual imported modules, and prints every exported theorem type and its axiom dependencies from a fresh Lean process. The native run also builds the complete 6,414,336-cell integer certificate and audits the analytic endpoint in `FMAnalyticEndpoint`.

```sh
python3 formalisation/real1b-2026-11-22/verify.py --lake
```

The native build at `9410dd6` checked all 252 declarations, including the complete mesh, the analytic endpoint, the rank-five collar integral and the exact omitted semiprime strip. [Archived axiom output](native-audits/9410dd6.txt) · [Complete native build log](https://github.com/RexHannes/twin-prime-proof-search/actions/runs/45217795816)

The native build at `43faced` checked 240 declarations, including the full grid and the signed endpoint. [Archived axiom output](native-audits/43faced.txt) · [Complete native build log](https://github.com/RexHannes/twin-prime-proof-search/actions/runs/45198042124)

The original Gold 4.67 native build at `af6872f` checked 193 declarations. [Archived axiom output](native-audits/af6872f.txt) · [Complete native build log](https://github.com/RexHannes/twin-prime-proof-search/actions/runs/45178500376)

The compact build target is `RequestProject.REAL1B_20261122`. For the analytic endpoint with kernel-checked cubature, import `RequestProject.REAL1B_20261122.FMAnalyticEndpoint` and inspect `#check @REAL1B.FM.Analytic.infinite_of_signed_estimates`. The online replay checks the integral-to-mesh bound with Lean and recomputes the numerical endpoints in Python. The native command checks the integer upper endpoint with the Lean kernel as well. For a repeatable review, use the **Copy permalink** action on this file and check out the corresponding commit. The [verification record](Verification.json) contains the replay digest, environment, request ID, declaration list and compiler output. It records the online run. Standard axioms allowed by the reviewer script are `propext`, `Classical.choice` and `Quot.sound`.

## Read the mathematical endpoints

- **Gold 4.66 direct FM.** The proof establishes the good-set equivalence and the five-prime integral upper enclosure. Its final mathematical hypothesis specific to the unpaid source is an independent outside-box upper with a fixed positive saving. [Direct route and dependency graph](FM-DIRECT.md)

- **Gold 4.60 joint signed FM.** Two endpoints preserve the original 0.00048 margin and the boxwise 0.00207 variant. Both derive a positive twin mass from an independent bound on the complete signed complement and their stated analytic inputs. [Proof obligations and exact semiprime balance](FM-CLOSING.md)

- **H2-B.** [SieveInputs.lean](../../RequestProject/REAL1B_20261122/SieveInputs.lean) ends with `infinite_of_paper_inputs`. It consumes an H1 squarefree lower estimate with valid sieve rows, a rough triple cap, a Type-I calibration, a cutoff-collar estimate, and a full Type-II upper bound. [Vaughan.lean](../../RequestProject/REAL1B_20261122/Vaughan.lean) gives the actual coefficients of that last sum.
- **Ford–Maynard.** [FMSource.lean](../../RequestProject/REAL1B_20261122/FMSource.lean) ends with `infinite_of_source_residual`. It uses a lower comparison, a signed residual upper estimate, and eventual positivity of the comparator prime baseline. All three refer to the specified source sums.
- **Comparison with the historical GitHub detector.** [SourceBridge.lean](../../RequestProject/REAL1B_20261122/SourceBridge.lean) accounts separately for proper prime powers, the change of logarithmic weight, and both differences between the windows under the shift by two.

The aggregate [Lean entry point](../../RequestProject/REAL1B_20261122.lean) imports all three displayed implications. Each supplies a sufficient condition. [Theorem and source map](DEPENDENCIES.md)
