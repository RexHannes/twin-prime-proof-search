# Evolutionary Theorem Hunter

A Work coordinator and its research workers use this journal to carry a proof across sessions. The first mathematical consumer tracks the full signed Ford–Maynard twin-prime estimate. Independent proofs can use the direct infinitude gate. The Python standard library is sufficient for journal operations.

## Recover a campaign

Run these commands in the directory containing `eth.py`. Substitute the campaign's exported checkpoint filename.

```bash
python eth.py --db research.sqlite restore CHECKPOINT.json
python eth.py --db research.sqlite resume
python eth.py --db research.sqlite graph
python eth.py --db research.sqlite search OutsideBound
python test_eth.py
```

`resume` displays the most recent checkpoint, registered source and audited commit, latest attempt, missing debts, accepted claims and a work packet. The journal includes UTF-8 proof evidence and its SHA-256 digest. Read the `proof` and `latest_attempt` fields when resuming a derivation. Proposed inequalities receive zero certified credit until their complete consumers pass review.

To start from a new snapshot use `init seed.json`. The default seed preserves the *historical* 4.67 sixteen-item interface with an unknown verified commit. Replace it with the verified current contract for live mathematical work. The following seed illustrates the format.

```json
{
  "commit": null,
  "source_commit": null,
  "sources": [],
  "endpoint": {"declaration": "", "evidence": ""},
  "obligations": {"P1": {"statement": "Exact imported statement"}, "P7": "Exact quantified outside bound"},
  "outside_id": "P7",
  "outside_population": "full_fm_outside",
  "normalization": "S_b",
  "ledger": {"lower": "0.999892775499", "box": "0.682878095535"},
  "next": "Derive a bound for the signed native outside source."
}
```

Use full Git object IDs. `commit` denotes the verified baseline and `source_commit` optionally identifies a later separately inspected tree. Record a pinned declaration and CI job or proof evidence under `endpoint`. Supply every analytic obligation, source reference and physical definition before using an endpoint in an acceptance review. A source entry with `path` and `sha256` participates in filesystem replay. Store remote primary-source links and the contract checked in additional entries.

## Conduct a research session

```bash
python eth.py --db research.sqlite session --minutes 60
python eth.py --db research.sqlite packet frontier
python eth.py --db research.sqlite record proposals.json
python eth.py --db research.sqlite packet engineer --candidate C1
python eth.py --db research.sqlite packet synthesis --candidate C1,C2
python eth.py --db research.sqlite next --role adverse --candidate C1
python eth.py --db research.sqlite gate C1 S1
python eth.py --db research.sqlite export CHECKPOINT.json
```

The Work coordinator dispatches real workers using these packets. Give two initial workers the blind frontier packet and collect independent derivations. The synthesis packet exposes the original proposals and attempts to a third worker. A comparison records the useful result, the first distinct obstruction and the next lemma. A genuine hybrid has two named parents. The engineer deepens the best candidate. Source, mathematical and terminal referees examine the same exact proof revision. Use the Lean packet for exact statements and the finite checker for diagnostics. Every role can introduce a new method. Reallocate effort when a rigorous challenge or a credible competing derivation warrants it.

A session budget records a deadline. To run continuously with independently configured research processes, supply an authorised Python worker adapter.

```bash
python eth.py --db research.sqlite drive --minutes 60 --worker /path/to/authorised_adapter.py
```

The adapter reads one UTF-8 JSON request on standard input with `protocol`, `actor`, journal `head` and `packet`. It returns a JSON object on standard output with the same `head`, an `events` list and an optional `handoff` explanation. Events carry the assigned `actor`. The adapter owns context isolation and the actual research engine. Configure it only for resources already authorised. The distribution includes no model credentials or backend. Work can directly use its built-in workers and `record` without installing an adapter.

After a checkpoint, blind discovery uses the most recent checkpoint task and verified commit. A named active checkpoint candidate receives the first resumed derivation alongside a fresh independent proposal. The driver dispatches separate discovery and derivation processes, presents both derivations for comparison, and issues independent named reviews on a submitted proof. During deepening it adds an alternative discovery packet approximately once per five waves. A successful reply commits atomically. An expired budget, empty response, worker failure or handoff saves the successful packets and an immediately resumable checkpoint. A budget specifies maximum elapsed time. `observed_wall_seconds` measures the actual drive run. The driver requests no progress by waiting or replaying identical events.

## Record a proof and adverse review

`record` accepts a JSON event or an ordered JSON array. An optional `event_id` makes identical retries idempotent. Evidence file paths are relative to the submitted JSON file unless absolute. `artifact` embeds the UTF-8 file and its hash. Optional fields can preserve exact paper references, source tuples, cutoffs, tested counterexamples, errors or terminal accounting in the same event.

| Event | Fields used by the journal |
| --- | --- |
| `candidate` | `id, actor, statement, source, mechanism, next` with optional `parents, artifact` |
| `attempt` | `candidate, actor, result, missing, next`. Attach the full derivation |
| `rank` | Independent `actor, candidate, reason, scores`. Score truth, novelty, source, terminal and verification from 0 to 4 |
| `compare` | Independent `actor, candidate` for the selected proposal, `parents, finding, next` |
| `proof` | `candidate, actor, artifact, scope, method, result_type, deps, unpaid, contract`. Include `check_id` for finite or Lean replay |
| `review` | `candidate, actor, proof_hash, role, verdict, finding`. Roles are `adverse, source, terminal`, verdicts are `pass, block` |
| `challenge` | `candidate, actor, basis, scope, finding, artifact` |
| `answer` | Independent `actor, candidate, challenge_hash, finding, artifact` |
| `decision` | `candidate, actor, action, reason, next`. For a tombstone add the exact `scope` and the independent `challenge_hash` |
| `discharge` | `candidate, actor, obligation, proof_hash` binds the exact audited statement to a premise |
| `accept` | Independent `actor, candidate, proof_hash, goal, finding` records an explicit mathematical judgement |
| `native_ci` | `actor, source_commit, declaration, conclusion, run_url, job_url, axioms, artifact` records native endpoint evidence on the seeded source commit |
| `checkpoint` | `actor, status, next` with optionally `candidate` and the proof state or repository location |

A `native_ci` attestation names the exact registered declaration and source SHA, sets `conclusion` to `success`, provides a GitHub Actions run URL and a job URL from that run, and lists the axioms explicitly. Its evidence must contain the full source SHA and declaration. Include provider metadata and the relevant logs so another reader can verify the attestation. The journal retains the baseline seed and exposes the new observation under `latest_verified_native_commit` and `native_ci`. A verified conditional endpoint leaves its analytic premises open. Arbitrary checkpoint metadata has no effect on that gate.

This submission records an unfinished derivation.

```json
{
  "kind": "proof", "candidate": "C1", "actor": "engineer",
  "artifact": "derivation.md", "scope": "conditional", "method": "analytic",
  "result_type": "lemma", "deps": ["P7"], "unpaid": ["genuine prime boundary"],
  "contract": {}
}
```

Use `scope` equal to `conditional`, `finite` or `unconditional` and `method` equal to `analytic`, `finite` or `lean`. The proof hash is computed from the complete submission. A changed submission requires new reviews. The `deps` array names other claims or seeded obligations. Circular dependencies, unresolved challenges, blocked reviews, outstanding companions or an unfilled premise prevent promotion. The three passing roles must admit three distinct reviewers. A blocking review in any role prevents promotion. The Work reviewer judges the mathematical truth and checks source semantics. A declared identity or nonempty text cannot independently establish either.

Choose `deepen`, `repair`, `park`, `tombstone` or `reopen` as a decision. A tombstone requires separately examined evidence for a precise counterexample, source mismatch, capacity bound or information obstruction. A failed search may justify `park` with a comparison. Re-entering a tombstoned claim requires naming a new instrument. The full earlier record remains accessible.

## Verification and acceptance

```bash
python eth.py --db research.sqlite check sources --id source-check --cwd /repo
python eth.py --db research.sqlite check finite verify.py --id finite-example
python eth.py --db research.sqlite check lean theorem.lean --id formal-example --declaration Namespace.theorem --cwd /repo
```

The finite command runs the named trusted verifier. The Lean command uses the pinned `lake env lean`, appends `#check` and `#print axioms`, and records pin hashes, exit code, digest and a log excerpt. Unsupported axioms, missing tools and timeouts are recorded. A formal proof submission identifies the successful check of its exact file. A separate source reviewer still examines all theorem hypotheses. An exhaustive result on a declared finite domain may become an input to a later proof. Success at infinite scale requires a reviewed general theorem.

| Goal | Acceptance contract |
| --- | --- |
| S1 through FM | The signed `outside_upper` counterparty matches the population and unit. Its coefficient gives a strictly positive exact reserve. The analytic endpoint, every tracked premise, error payment and growth implication must be independently supported. |
| S1 directly | An unconditional `infinitude` proof has exactly the registered `goal_statement`, unbounded scales, reviewed dependencies and a separate terminal acceptance. |
| S2 | An independently certified old bound and a strictly better new complete bound have the same population, signed scope and normalization. |
| S3 | A source-specific `parity` proof identifies the genuine `prime_class`, the `escape_class`, its `new_signed_estimate` and exact `terminal_splice`. |

For complete upper bounds give an exact decimal or fraction in `coefficient` and specify `population, normalization, fixed_quantifiers, signed_companions, error_payment`. An outside upper also gives `masks_and_cutoffs`. An infinitude splice includes `unbounded_scales`. An S2 contract references the old candidate by `prior`. Give the actual arguments and references in these fields and the attached proof. The status field `reviewed_full_outside_upper` reports the smallest audited unconditional upper for the registered full population, even while the strict outside obligation is open. `verified_FM_reserve_lower` requires all named endpoint obligations to be discharged. Only explicit reviewed S1 closes the programme. S2 and S3 preserve an active endgame.

SQLite serializes concurrent mutations. New evidence or a changed premise can invalidate a previous acceptance on replay. Export the hash-chained JSON after each mathematical milestone. Restore fast-forwards a shared prefix and rejects divergent edits. Reconcile separate forks by reviewing and appending their new evidence. The hashes detect changed bytes and preserve sequencing. Author identity and theorem correctness require independent verification outside the journal.
