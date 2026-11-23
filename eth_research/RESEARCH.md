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
