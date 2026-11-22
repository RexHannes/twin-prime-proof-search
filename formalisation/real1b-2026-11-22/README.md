# REAL 1B runnable Lean proofs

This package checks the exact quarter-root Möbius identity on the shifted-prime source, the historical weighted-count decomposition, two conditional Ford–Maynard margin calculations, and the conditional H2 deduction of infinitely many twin primes.

## Run the proof

**In Chromium**, open the single-file replay in Live Lean. The file contains all repository-specific definitions and proofs and imports Mathlib. To reproduce the recorded AXLE check, paste the same file into AXLE, select `lean-4.28.0`, clear `ignore_imports`, and select **RUN**. The compiler output includes a `#print axioms` audit for each of the 13 public results. [Open replay in Live Lean](https://live.lean-lang.org/#project=mathlib-v4.28.0&url=https%3A%2F%2Fraw.githubusercontent.com%2FRexHannes%2Ftwin-prime-proof-search%2Fmain%2Fformalisation%2Freal1b-2026-11-22%2FReplay.lean) · [Single Lean file](Replay.lean) · [AXLE checker](https://axle.axiommath.ai/check) · [Recorded AXLE result](Verification.json)

From the repository root, the Lake target builds the three source modules and the final conditional theorem with the repository's pinned Lean and Mathlib.

```sh
lake exe cache get
lake build RequestProject.REAL1B_20261122
```

## What is proved

| Module | Mathematical content |
|---|---|
| [QuarterRough](../../RequestProject/REAL1B_20261122/QuarterRough.lean) | On the source weighted by the prime-only logarithm at $n-2$ over $X<n\leq 2X$, the finite identity is $2T=A_R-2C_3-M_R$. The proof establishes the possible prime-factor counts, the Möbius signs, and the two finite sum identities. |
| [WeightedDecomposition](../../RequestProject/REAL1B_20261122/WeightedDecomposition.lean) | The historical detector using the von Mangoldt weight at $p+2$ decomposes into its twin-prime contribution and its explicit proper-prime-power error. This supplies the proof required by the existing repository interface. |
| [FMResidual](../../RequestProject/REAL1B_20261122/FMResidual.lean) | The historical and current Gold 4.53-FM residual thresholds yield the respective coefficients $0.0018622$ and $0.0018622-10^{-58}$ under their comparison and residual assumptions. |
| [Aggregate entry point](../../RequestProject/REAL1B_20261122.lean) | `REAL1B.infinite_of_h2_bounds` combines the per-scale H2 lower bound and the dyadic infinitude criterion. |

**Open hypothesis.** The aggregate theorem assumes that beyond every natural bound there is a scale where the unsigned lower estimate and signed Möbius upper estimate hold together and their combined error leaves a strictly positive margin. It then proves that the set of primes $p$ with $p+2$ prime is infinite. Establishing these estimates for the genuine source remains open. The FM inequalities are independent conditional results.

The source is the 22 November 2026 REAL 1B Lean blueprint, pp. 2–4, the embedded Gold 4.50-B §10, equations (19)–(20), and the embedded Gold 4.53-FM §1, p. 47 of the Lean volume. The original GitHub detector and decomposition interface come from the repository at [4c36bc7](https://github.com/RexHannes/twin-prime-proof-search/tree/4c36bc7819c22cf6c84ec2a97a21637bc09dd4c1).
