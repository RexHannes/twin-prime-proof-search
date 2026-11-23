"""No network or Lean installation is required to exercise the bookkeeping invariants."""

import importlib.util
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("eth_research", HERE / "eth.py")
eth = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(eth)


class GateTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.folder = Path(self.tmp.name)
        self.proof = self.folder / "proof.txt"
        self.proof.write_text("Synthetic regression fixture; this is not mathematical evidence.\n")
        self.seed = eth.normalize_seed({"commit": "a" * 40, "endpoint": {"declaration": "synthetic", "evidence": "synthetic"},
                                        "obligations": {"P1": "normalization lemma", "P7": "outside lemma"}})
        self.s = eth.State()
        self.s.apply(self.seed)

    def tearDown(self):
        self.tmp.cleanup()

    def candidate(self, key, statement="synthetic candidate"):
        self.s.apply({"kind": "candidate", "actor": "writer", "id": key, "statement": statement,
                      "source": "synthetic source", "mechanism": "fixture", "next": "check"})

    def submit(self, key, scope="unconditional", result_type="lemma", deps=None, contract=None):
        self.s.apply({"kind": "proof", "candidate": key, "actor": "writer", "scope": scope,
                      "method": "analytic", "result_type": result_type, "deps": deps or [], "unpaid": [],
                      "evidence": eth.evidence_at(self.proof), "contract": contract or {}})

    def reviews(self, key):
        for role in eth.REFEREES:
            self.review(key, role, role, "pass")

    def review(self, key, actor, role, verdict):
        self.s.apply({"kind": "review", "candidate": key, "actor": actor, "proof_hash": self.s.claims[key]["hash"],
                      "role": role, "verdict": verdict, "finding": "Synthetic evaluation for test."})

    def outside(self, coefficient, **kw):
        return {"population": "full_fm_outside", "normalization": "S_b",
                "fixed_quantifiers": "synthetic", "masks_and_cutoffs": "synthetic",
                "signed_companions": "synthetic", "error_payment": "synthetic",
                "unbounded_scales": "synthetic", "coefficient": coefficient, **kw}

    def assign(self, key, premise):
        self.s.apply({"kind": "discharge", "candidate": key, "actor": "referee", "obligation": premise,
                      "proof_hash": self.s.claims[key]["hash"]})

    def test_source_contract_strict_reserve_and_open_premises(self):
        self.candidate("O", "outside lemma")
        self.submit("O", result_type="outside_upper", contract=self.outside("0.317014679964"))
        self.reviews("O")
        with self.assertRaisesRegex(ValueError, "not strict"):
            self.assign("O", "P7")
        self.submit("O", result_type="outside_upper", contract=self.outside("0.2", normalization="wrong"))
        self.reviews("O")
        with self.assertRaisesRegex(ValueError, "normalization"):
            self.assign("O", "P7")
        self.submit("O", result_type="outside_upper", contract=self.outside("0.3"))
        self.reviews("O")
        self.assign("O", "P7")
        self.assertIn("endpoint still requires P1", self.s.gate("O", "S1"))
        self.assertIsNone(self.s.summary()["verified_FM_reserve_lower"])
        self.candidate("N", "normalization lemma")
        self.submit("N")
        self.reviews("N")
        self.assign("N", "P1")
        self.assertEqual(self.s.gate("O", "S1"), [])
        self.assertEqual(self.s.summary()["programme"], "ACTIVE")
        self.s.apply({"kind": "accept", "candidate": "O", "actor": "other", "goal": "S1",
                      "proof_hash": self.s.claims["O"]["hash"], "finding": "Synthetic fixture."})
        self.assertEqual(self.s.summary()["programme"], "CLOSED")
        self.review("N", "source", "source", "block")
        self.assertEqual(self.s.summary()["programme"], "ACTIVE")

    def test_direct_goal_finite_conditional_and_self_review(self):
        self.candidate("T", self.seed["goal_statement"])
        self.submit("T", scope="finite", result_type="infinitude", contract={"unbounded_scales": "asserted"})
        with self.assertRaisesRegex(ValueError, "own"):
            self.review("T", "writer", "source", "pass")
        self.reviews("T")
        self.assertTrue(self.s.gate("T", "S1"))
        self.submit("T", scope="conditional", result_type="infinitude", deps=["P7"], contract={"unbounded_scales": "asserted"})
        self.reviews("T")
        self.assertIn("P7 open", self.s.gate("T", "S1"))
        self.candidate("W", "finite assertion")
        self.submit("W", result_type="infinitude", contract={"unbounded_scales": "asserted"})
        self.reviews("W")
        self.assertTrue(self.s.gate("W", "S1"))

    def test_s2_requires_like_for_like_reviewed_comparator_without_closing(self):
        self.candidate("old")
        self.candidate("new")
        self.submit("old", result_type="outside_upper", contract=self.outside("1/2"))
        self.submit("new", result_type="outside_upper", contract=self.outside("2/5", prior="old"))
        self.reviews("new")
        self.assertTrue(self.s.gate("new", "S2"))
        self.reviews("old")
        self.assertEqual(self.s.gate("new", "S2"), [])
        self.assertTrue(self.s.gate("new", "S1"))
        self.s.apply({"kind": "accept", "candidate": "new", "actor": "final", "goal": "S2",
                      "proof_hash": self.s.claims["new"]["hash"], "finding": "Synthetic fixture."})
        self.assertEqual(self.s.summary()["programme"], "ACTIVE")

    def test_three_roles_require_distinct_people_even_with_extra_single_role_reviews(self):
        self.candidate("a")
        self.submit("a")
        for role in eth.REFEREES:
            self.review("a", "one", role, "pass")
        self.assertTrue(any("three distinct" in issue for issue in self.s.audit("a")))
        self.review("a", "two", "adverse", "pass")
        self.review("a", "three", "adverse", "pass")
        self.assertTrue(any("three distinct" in issue for issue in self.s.audit("a")))
        self.review("a", "two", "source", "pass")
        self.assertEqual(self.s.audit("a"), [])
        self.review("a", "four", "terminal", "block")
        self.assertTrue(self.s.audit("a"))

    def test_reviewed_outside_reports_best_valid_cap_without_endpoint_discharge(self):
        self.candidate("old")
        self.submit("old", result_type="outside_upper", contract=self.outside("1/2"))
        self.reviews("old")
        self.candidate("new")
        self.submit("new", result_type="outside_upper", contract=self.outside("2/5"))
        self.reviews("new")
        self.candidate("mismatched")
        self.submit("mismatched", result_type="outside_upper", contract=self.outside("1/4", normalization="wrong"))
        self.reviews("mismatched")
        self.candidate("conditional")
        self.submit("conditional", scope="conditional", result_type="outside_upper", contract=self.outside("1/5"))
        self.reviews("conditional")
        self.assertEqual(self.s.summary()["reviewed_full_outside_upper"], eth.exact(eth.number("2/5")))
        self.assertIsNone(self.s.summary()["verified_FM_reserve_lower"])
        self.assertIn("P7", self.s.summary()["open_obligations"])
        self.assertEqual(self.s.summary()["programme"], "ACTIVE")
        self.review("new", "source", "source", "block")
        self.assertEqual(self.s.summary()["reviewed_full_outside_upper"], eth.exact(eth.number("1/2")))

    def test_later_native_ci_pins_the_endpoint_without_discharging_any_premise(self):
        commit, declaration = "b" * 40, "Synthetic.sample"
        seed = {**self.seed, "source_commit": commit, "native_endpoint": declaration, "endpoint": {}}
        self.s = eth.State()
        self.s.apply(seed)
        first = eth.packet(self.s, "frontier", None)
        self.assertEqual((first["commit"], first["source_commit"], first["frontier"]),
                         (seed["commit"], commit, seed["next"]))
        run = "https://github.com/example/research/actions/runs/21"
        self.proof.write_text(f"Synthetic fixture\n{commit}\n{declaration}\n")
        evidence = eth.evidence_at(self.proof)
        ci = {"kind": "native_ci", "actor": "verifier", "source_commit": commit, "declaration": declaration,
              "conclusion": "success", "run_url": run, "job_url": run + "/job/34",
              "axioms": ["propext", "Classical.choice", "Quot.sound"], "evidence": evidence}
        self.s.apply({"kind": "checkpoint", "actor": "writer", "status": "ACTIVE", "next": "review",
                      "native_ci": ci, "latest_verified_native_commit": commit})
        self.assertIsNone(self.s.summary()["native_ci"])
        self.assertEqual(self.s.summary()["latest_verified_native_commit"], seed["commit"])
        for bad in ({"source_commit": "c" * 40}, {"declaration": "Synthetic.other"}, {"conclusion": "pending"},
                    {"job_url": run + "9/job/34"}, {"axioms": ["sorryAx"]}, {"axioms": None}):
            with self.assertRaises(ValueError):
                self.s.apply(ci | bad)
        self.candidate("O", "outside lemma")
        self.submit("O", result_type="outside_upper", contract=self.outside("1/4"))
        self.reviews("O")
        self.assertTrue(any("verified endpoint" in p for p in self.s.gate("O", "S1")))
        self.s.apply(ci)
        summary = self.s.summary()
        self.assertEqual(summary["commit"], "a" * 40)
        self.assertEqual(summary["latest_verified_native_commit"], commit)
        self.assertEqual(summary["native_ci"]["evidence_sha256"], evidence["sha256"])
        self.s.apply({"kind": "checkpoint", "actor": "coordinator", "status": "ACTIVE", "candidate": "O",
                      "next": "investigate the new prime boundary"})
        blind = eth.packet(self.s, "frontier", None)
        self.assertEqual((blind["frontier"], blind["commit"]), ("investigate the new prime boundary", commit))
        self.assertNotIn("source_commit", blind)
        self.assertEqual(eth.packet(self.s, "engineer", "O")["next"], blind["frontier"])
        self.assertIn(("engineer", "proof-engineer", "O"), eth.worker_wave(self.s, 0))
        self.assertIn(("frontier", "alternative-invention", None), eth.worker_wave(self.s, 0))
        self.assertFalse(any("verified endpoint" in p for p in self.s.gate("O", "S1")))
        self.assertEqual(set(summary["open_obligations"]), {"P1", "P7"})
        self.assertEqual(summary["programme"], "ACTIVE")
        self.assertIsNone(summary["verified_FM_reserve_lower"])
        seed_file, event_file = self.folder / "seed.json", self.folder / "ci.json"
        seed_file.write_text(json.dumps(seed))
        event_file.write_text(json.dumps(ci))
        db = self.folder / "ci.db"
        self.run_cli(db, "init", seed_file)
        self.run_cli(db, "record", event_file)
        self.assertEqual(self.run_cli(db, "resume")["native_ci"]["evidence"], evidence)

    def test_revision_stale_reviews_cycles_and_parity(self):
        self.candidate("a")
        self.candidate("b")
        self.submit("a", deps=["b"])
        self.submit("b", deps=["a"])
        self.reviews("a")
        self.reviews("b")
        self.assertTrue(any("cyclic" in x for x in self.s.audit("a")))
        old = self.s.claims["a"]["hash"]
        self.submit("a", result_type="parity")
        with self.assertRaisesRegex(ValueError, "stale"):
            self.s.apply({"kind": "review", "actor": "new", "candidate": "a", "proof_hash": old})
        self.reviews("a")
        self.assertTrue(self.s.gate("a", "S3"))

    def test_tombstone_needs_recorded_scoped_challenge_and_distinct_examiner(self):
        self.candidate("a")
        self.s.apply({"kind": "attempt", "actor": "writer", "candidate": "a", "result": "x", "missing": "y", "next": "z"})
        choice = {"kind": "decision", "candidate": "a", "action": "tombstone", "reason": "scoped",
                  "next": "change route", "scope": "one model", "actor": "other"}
        with self.assertRaisesRegex(ValueError, "scoped challenge"):
            self.s.apply(choice)
        witness = eth.evidence_at(self.proof)
        self.s.apply({"kind": "challenge", "actor": "writer", "candidate": "a", "basis": "counterexample",
                      "scope": "one model", "finding": "fixture", "evidence": witness})
        self.s.apply({**choice, "challenge_hash": witness["sha256"]})
        self.assertEqual(self.s.live(), [])
        self.assertEqual(eth.packet(self.s, "frontier", None)["scoped_tombstones"][0]["id"], "a")

    def run_cli(self, db, *args, ok=True):
        proc = subprocess.run([sys.executable, str(HERE / "eth.py"), "--db", str(db), *map(str, args)],
                              capture_output=True, text=True)
        if ok:
            self.assertEqual(proc.returncode, 0, proc.stderr)
            return json.loads(proc.stdout)
        self.assertNotEqual(proc.returncode, 0)
        return proc

    def test_cli_transactions_retries_checks_and_portable_resume(self):
        db = self.folder / "state.db"
        self.run_cli(db, "init")
        event = self.folder / "batch.json"
        candidate = {"kind": "candidate", "id": "c", "actor": "writer", "statement": "s",
                     "source": "u", "mechanism": "m", "next": "x", "event_id": "entry"}
        event.write_text(json.dumps([candidate, candidate | {"mechanism": "inconsistent"}]))
        self.run_cli(db, "record", event, ok=False)
        self.assertFalse(self.run_cli(db, "status")["candidates"])
        event.write_text(json.dumps(candidate))
        with ThreadPoolExecutor(max_workers=3) as pool:
            list(pool.map(lambda _: self.run_cli(db, "record", event), range(3)))
        self.assertEqual(self.run_cli(db, "status")["events"], 2)
        verifier = self.folder / "verify.py"
        verifier.write_text("assert sum(range(4)) == 6\n")
        self.run_cli(db, "check", "finite", verifier, "--id", "fixture")
        self.run_cli(db, "session", "--minutes", 60)
        backup = self.folder / "fingerprint.json"
        head = self.run_cli(db, "export", backup)["head"]
        copied = self.folder / "new.db"
        self.assertEqual(self.run_cli(copied, "restore", backup)["head"], head)
        self.assertEqual(self.run_cli(copied, "resume")["head"], head)
        self.assertEqual(self.run_cli(copied, "restore", backup)["restored"], 0)
        data = json.loads(backup.read_text())
        data["events"][1]["event"]["statement"] = "corrupted"
        backup.write_text(json.dumps(data))
        self.run_cli(self.folder / "corrupt.db", "restore", backup, ok=False)
        self.run_cli(db, "export", backup, ok=False)

    def test_external_adapter_blind_derivations_then_cross_read_and_handoff(self):
        db = self.folder / "active.db"
        self.run_cli(db, "init")
        adapter = self.folder / "fixture_adapter.py"
        adapter.write_text(
            "import json,sys\n"
            "x=json.load(sys.stdin); p=x['packet']; a=x['actor']; r=p['role']; end=None\n"
            "if r=='frontier':\n"
            " assert 'inputs' not in p and 'latest_attempt' not in p\n"
            " e=dict(kind='candidate',actor=a,id=a,statement='fixture',source='test',mechanism='fixture',next='derive')\n"
            "elif r=='engineer':\n"
            " e=dict(kind='attempt',actor=a,candidate=p['candidate'],result='fixture',missing='fixture',next='compare')\n"
            "else:\n"
            " assert r=='synthesis' and all(t['latest_attempt'] for t in p['inputs'])\n"
            " e=dict(kind='compare',actor=a,candidate=p['parents'][0],parents=p['parents'],finding='fixture',next='real work')\n"
            " end='fixture exhausted'\n"
            "print(json.dumps(dict(head=x['head'],events=[e],handoff=end)))\n"
        )
        out = self.run_cli(db, "drive", "--minutes", 60, "--worker", adapter)
        self.assertEqual(out["outcome"], "checkpointed_handoff")
        self.assertEqual(out["waves"], 3)
        self.assertEqual(out["registered_events"], 5)
        self.assertLess(out["observed_wall_seconds"], 20)
        state = self.run_cli(db, "resume")
        self.assertEqual(state["checkpoint"]["next"], "real work")
        self.assertEqual(state["status"]["reviewed_success"], [])

    def test_computation_only_certifies_its_exact_finite_input(self):
        self.candidate("finite", "sum on one fixed finite set")
        artifact = eth.evidence_at(self.proof)
        self.s.apply({"kind": "check", "id": "test", "method": "finite", "status": "passed",
                      "sha256": artifact["sha256"]})
        self.s.apply({"kind": "proof", "candidate": "finite", "actor": "writer", "scope": "finite",
                      "method": "finite", "result_type": "lemma", "deps": [], "unpaid": [],
                      "check_id": "test", "evidence": artifact,
                      "contract": {"finite_domain": "fixed set", "exhaustive_certificate": "full traversal"}})
        self.reviews("finite")
        self.assertEqual(self.s.audit("finite"), [])
        self.assertTrue(self.s.gate("finite", "S1"))
        self.candidate("paper")
        self.submit("paper", deps=["finite"])
        self.reviews("paper")
        self.assertEqual(self.s.audit("paper"), [])
        witness = self.folder / "challenge.txt"
        witness.write_text("Synthetic question about the finite check.")
        self.s.apply({"kind": "challenge", "candidate": "finite", "actor": "critic", "basis": "counterexample",
                      "scope": "fixed set", "finding": "fixture", "evidence": eth.evidence_at(witness)})
        self.assertTrue(self.s.audit("paper"))
        self.s.apply({"kind": "answer", "candidate": "finite", "actor": "examiner",
                      "challenge_hash": eth.evidence_at(witness)["sha256"], "finding": "resolved by fixture",
                      "evidence": artifact})
        self.assertEqual(self.s.audit("paper"), [])


if __name__ == "__main__":
    unittest.main(verbosity=2)
