# REAL 1B | FM research checkpoint, 23 November 2026 UTC

The proof-search goal is unconditional infinitude of primes p for which p+2 is prime. The conjecture remains open in this packet. The baseline formal source is commit 43facedcf40b2f998aa47f7198d6b9b5feb5b792. This branch adds an executable research journal, checked rational arithmetic, and written analytical results. The new inequalities do not have Lean declarations proving their analytic premises.

## Complete signed bounds

Write O=U_{Bᶜ}, where B is the original five-prime box union. The weighted twin count is T, the actual shifted-prime box mass is Aψ, and S_b is the native positive comparator. For each fixed 0<a<1, eventual inequalities with arbitrary o(1) tolerances give the following in units S_b.

| Quantity | Lower | Upper |
| --- | ---: | ---: |
| (U+T)/S_b | 0.9999542004011324850950 | 1.0000457704877562822661 |
| J, original ordered five-prime integral | 0.27547734178065116588 | 0.27560294635735393770 |
| U_B/S_b | −0.27560294635735393770 | 0.64307354150049252130 |
| (O+T)/S_b | 0.3568806589006399637950 | 1.2756487168451102199661 |
| (O+T+Aψ)/S_b | 1.2754315421817836509750 | 1.2756487168451102199661 |

The inequality for O alone follows by the positivity of T. The full-source comparison with the previous original certificate, reconstructed from its source constituents, is 1.28460707694425252602 down to at most 1.275648716845111. This meets the signed-upper milestone S2. The narrower independently registered comparison changes only the enclosure of J, yielding a fixed difference of 0.00889694708589858832. Success S1 (infinitely many twins), success S3 (an independent prime/composite advantage), and an independently positive twin reserve are all open.

The previous sufficient outside threshold 0.317014679964 was the difference between the previous entire lower coefficient 0.999892775499 and the previous box upper 0.682878095535. The ranks, signs, boxes, shift and normalization are identical in the new sufficient threshold. See proofs/complete_ledger.md and verification/complete_ledger.json for both directions with outward rounding. The bound concerns a limsup. At a strict intermediate value one has a fixed positive margin. The gap between the available upper and the sufficient threshold is the difference between two certificates and is not an observed value of O or T. The conditional native Lean declaration at the base commit uses the older threshold.

## Evidence and the next open step

The core transfer and native assumptions are in proofs/uniform_native_transfer.md, proofs/analytic_contracts.md, proofs/analytic_packet.md, proofs/collar_ledger.md and proofs/native_rough_sieve.md. The new angular integral and the exact full comparison are in proofs/integral_proof.md, proofs/upper_comparison_prior.md and proofs/upper_comparison_new.md. Written source, adverse and terminal reviews are recorded in the journal. The comparison credits each actual prime-box and twin term once.

Proofs/sharp_polynomial_presieve.md establishes arbitrarily accurate collective restriction on the original signed input to one fixed positive roughness exponent. The retuned, centered higher-rank expression in proofs/simultaneous_core.md removes the semiprime-input population with a controlled error and retains the higher-rank signed cost. The proof specifies the order of parameters. Additional sign-sensitive restrictions must preserve favorable terms. The subpower decompositions and their compensating opposite-sign terms are recorded in proofs/SUBPOWER_SIGNED_RESTORATION.md and proofs/subpower_two_signed.md. A sum on just the adverse small-factor population can diverge in these units. A strict estimate for the complete joint source is still missing.

## Replay

From this directory, Python 3.11+ and the standard library suffice.

```sh
python test_eth.py
python verification/moments_crosscheck.py
python verification/face_integral.py --subdivisions 4
python verification/check_complete_ledger.py
python eth.py --db /tmp/real1b.sqlite restore checkpoint.json
python eth.py --db /tmp/real1b.sqlite gate full-outside-cap S2
python eth.py --db /tmp/real1b.sqlite resume
```

The included artifact is the checkpoint, not an API key or configured paid model. Use the Work research workers for actual mathematical derivations. The local drive command also accepts an explicitly configured external worker, with a real-time budget and a handoff on lack of new evidence. The journal is not a proof assistant. An independently reviewed full cap can be recorded without claiming a strictly positive reserve.

The native Lean project at the base commit has its own toolchain, conditional theorem and replay workflow. For that separate code run lake in its pinned native environment. Checking the Python enclosure or the journal cannot replace a kernel proof of any new analytic lemma. In the source papers, older scratch-style path hints refer to the paper or verifier with the same basename under proofs or verification in this directory.

## Latest audit and signed payment

The original native Lean run at 43faced completed successfully, with 240 native declarations and 216 compact replay declarations. The conditional infinitude endpoint uses the standard three axioms. verification/ci.json records the run, exact declaration, job and log extract. This is separate from the new written inequalities. The harness regression suite now has 11 passing tests.

In the retuned full representation, the compulsory rank-three correction permits a genuine adverse population of rank at least five with lower bound .021 S_b/t at small fixed t. The same representation, with a fixed spare exponent below the half threshold, allows the *whole* identified population to be paired with its ordinary comparison to arbitrary precision at the S_b scale. Both terms are retained in the terminal ledger. The complete centered source on all inputs carrying at least one small prime is also payable. Its unknown is precisely the unmarked prime correlation on the zero-small-prime stratum, with both output signs. See proofs/centered_charge_payment.md, proofs/all_nonempty_centered.md and proofs/physical_covariance_and_rare_mass.md.

For the next live computation, write f=Φ−ψ, A(h)=Σθ(k)h(k+2), and Δ_±=A(f_±)/S_b−Π(f_±). Prove, on the same dyadic sequence and for some κ>0, limsup(Δ₊−Δ₋)≤0.3568806589006399637950−κ, or find an independently audited reduction to the complete upper. Keeping both terms joint is allowed. No result here proves this new inequality. A later epoch should start at this surviving joint prime correlation.


## Resumed FM research, 24 November 2026

On the same complete outside source the updated paper upper is **1.275621644463351478** in normalized units. The updated sufficient strict threshold is **0.356907731282398706**. The old numbers above describe the checkpoint at 528f762. The improvement comes from retaining the sign of omitted subsets in the four-factor term and pairing subsets before charging the exceptional small-coordinate face. Full derivation and independent exact computations are in [signed_rank_four.md](proofs/signed_rank_four.md), [check_signed_rank_four.py](verification/check_signed_rank_four.py), and [check_subset_signs.py](verification/check_subset_signs.py). The latter examined 13,942 finite profiles. The new paper inequality has no new Lean discharge.

[The three-to-five factor comparison](proofs/rank_changing_prime_switch.md) gives a different, genuine shifted-prime result. Matching a single residual prime against three prime factors changes the exact native output sign. Bombieri–Vinogradov and the dimension-one fundamental lemma compare both nonnegative channels on the enlarged outer cofactor set. The signed remainder on the physical two-prime outer cofactor is exactly opposed by its full rough complement in ordered limits; it is not bounded with favorable sign. The unmatched one-prime term is displayed. The local comparison supplies no extra numerical credit.

The journal remains ACTIVE. The portable checkpoint records the paper claim and next task; the strict signed covariance and unconditional infinitude endpoint remain open.
