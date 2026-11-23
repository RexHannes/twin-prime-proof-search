#!/usr/bin/env python3
"""Evolutionary Theorem Hunter. A research worker supplies mathematics to a replayable journal."""

import argparse
import contextlib
from concurrent.futures import ThreadPoolExecutor
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import sqlite3
import subprocess
import sys
import tempfile
import time
from fractions import Fraction
from itertools import product
from statistics import median

DEFAULT_OBLIGATIONS = {
    "P1": "Profile.Normalization",
    **{"P2." + key: "Ledger.Estimates." + key for key in
       ("goodMass", "pairs", "four", "tail", "calibratedMean", "comparator")},
    **{f"{group}.{key}": f"VaughanEstimates({weight}).{key}"
       for group, weight in (("P3", "phi"), ("P4", "psi"))
       for key in ("typeI_centered", "short", "squareful")},
    "P5": "Profile.MeanDensity",
    "P6": "Profile.RoughDensity",
    "P7": "OutsideBound",
}
DIMS = ("truth", "novelty", "source", "terminal", "verification")
REFEREES = ("adverse", "source", "terminal")
SCOPED_FAILURES = ("counterexample", "source_mismatch", "capacity", "information")
ZERO_HASH = "0" * 64
SCHEMA_VERSION = 1
ROLE_PROMPTS = {
    "frontier": "Give an independent mechanism for the displayed obligation. Derive its first testable lemma and a hostile input. Return a candidate and a mathematical attempt.",
    "synthesis": "Compare the supplied independent derivations against the same native source. Record a comparison or a repaired child candidate with both parents. Identify the first incompatible step before combining claims.",
    "engineer": "Carry the displayed proof through the first missing estimate. Record quantifiers, debts, time-uniform errors, a counterexample tried and a next proof step.",
    "adverse": "Try to refute the exact submitted theorem. Exhibit a witness, missing premise, or the derivation checked. Cite the proof hash in a review.",
    "source": "Match assumptions term by term to the native weights, cutoff, shift, prime boundary, modulus, quantifiers and error. Cite contracts and the proof hash.",
    "lean": "Check the pinned toolchain, theorem type, all hypotheses, and #print axioms. Run check lean or record external CI with its commit, job and declaration.",
    "terminal": "Reassemble both signs, boundary, overlap, error and growth in the same normalization. Check the entire consumer including alternatives. Cite the proof hash.",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def encoded(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()


def digest(blob):
    return hashlib.sha256(blob).hexdigest()


def required_text(event, *keys):
    for key in keys:
        require(isinstance(event.get(key), str) and event[key].strip(), f"missing text field {key}")


def strings(data):
    return isinstance(data, list) and all(isinstance(item, str) and item.strip() for item in data)


def number(value):
    require(isinstance(value, (str, int)) and not isinstance(value, bool), "use a quoted exact decimal or fraction")
    return Fraction(value)


def exact(value):
    return str(value)


def now():
    return dt.datetime.now(dt.timezone.utc).isoformat(timespec="microseconds")


def parse_time(value):
    parsed = dt.datetime.fromisoformat(value)
    require(parsed.tzinfo is not None, "journal time needs UTC offset")
    return parsed


def read_json(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def evidence_at(path):
    path = Path(path)
    data = path.read_bytes()
    return {"name": path.name, "sha256": digest(data), "text": data.decode("utf-8")}


def validate_evidence(evidence):
    require(isinstance(evidence, dict), "an attached UTF-8 proof or evidence file is required")
    required_text(evidence, "name", "text", "sha256")
    require(digest(evidence["text"].encode()) == evidence["sha256"], "evidence hash mismatch")


def attach(event, folder):
    event = dict(event)
    if "artifact" in event:
        require("evidence" not in event, "supply artifact or embedded evidence")
        event["evidence"] = evidence_at(folder / event.pop("artifact"))
    return event


def normalize_seed(data):
    seed = dict(data)
    seed["kind"] = "seed"
    seed.setdefault("version", SCHEMA_VERSION)
    seed.setdefault("commit", None)
    seed.setdefault("obligations", DEFAULT_OBLIGATIONS)
    seed.setdefault("sources", [])
    seed.setdefault("outside_id", "P7")
    seed.setdefault("outside_population", "full_fm_outside")
    seed.setdefault("normalization", "S_b")
    seed.setdefault("goal_statement", "For every natural number N there is a prime p >= N such that p+2 is prime.")
    seed.setdefault("next", "Derive an unconditional bound for the full signed outside source and identify the first unpaid term.")
    seed.setdefault("ledger", {"lower": "0.999892775499", "box": "0.682878095535"})
    return seed


class State:
    def __init__(self):
        self.seed = None
        self.records = []
        self.claims = {}
        self.discharges = {}
        self.terminal = []
        self.comparisons = []
        self.session = None

    def open_deps(self, candidate, stack=()):
        proof = self.claims[candidate].get("proof")
        if not proof:
            return [f"{candidate} lacks a proof packet"]
        problems = []
        for dep in proof["deps"]:
            if dep in self.claims:
                subject = dep
            else:
                assignment = self.discharges.get(dep)
                if not assignment:
                    problems.append(f"{dep} open")
                    continue
                subject, hash_at_discharge = assignment
                if self.claims[subject]["hash"] != hash_at_discharge:
                    problems.append(f"{dep} discharge changed")
                    continue
            problems.extend(self.audit(subject, stack))
        return problems

    def audit(self, candidate, stack=()):
        if candidate in stack:
            return ["cyclic dependency " + " -> ".join((*stack, candidate))]
        claim = self.claims[candidate]
        proof = claim.get("proof")
        if not proof:
            return [f"{candidate} lacks a proof packet"]
        problems = [
            f"{candidate} has unresolved scoped challenge {w['evidence']['sha256']}"
            for w in claim["challenges"] if w["evidence"]["sha256"] not in claim["answered"]
        ]
        if claim["action"] in ("tombstone", "park"):
            problems.append(f"{candidate} is {claim['action']}")
        if proof["scope"] == "conditional":
            problems.append(f"{candidate} depends on conditional premises")
        elif proof["scope"] == "finite":
            contract = proof.get("contract", {})
            if not all(contract.get(k) for k in ("finite_domain", "exhaustive_certificate")):
                problems.append(f"{candidate} has no exhaustive finite-domain certificate")
        elif proof["method"] == "finite":
            problems.append(f"{candidate} uses a finite computation for an unbounded claim")
        problems.extend(f"{candidate} has unpaid {item}" for item in proof["unpaid"])
        passing_by_role = []
        for role in REFEREES:
            reviews = [r for r in claim["reviews"].values() if r["role"] == role]
            passing = {r["actor"] for r in reviews if r["verdict"] == "pass"}
            passing_by_role.append(passing)
            if not passing:
                problems.append(f"{candidate} lacks passing {role} review")
            if any(r["verdict"] == "block" for r in reviews):
                problems.append(f"{candidate} has a blocking {role} review")
        if all(passing_by_role) and not any(
            len(set(actors)) == len(REFEREES) for actors in product(*passing_by_role)
        ):
            problems.append(f"{candidate} needs three distinct passing referees across adverse, source and terminal")
        problems.extend(self.open_deps(candidate, (*stack, candidate)))
        return sorted(set(problems))

    def assigned(self, obligation):
        assignment = self.discharges.get(obligation)
        return bool(assignment and self.claims[assignment[0]]["hash"] == assignment[1]
                    and not self.audit(assignment[0]))

    def outside_contract(self, proof):
        contract = proof.get("contract", {})
        problems = []
        for field, expected in (("population", self.seed["outside_population"]),
                                ("normalization", self.seed["normalization"])):
            if contract.get(field) != expected:
                problems.append(f"outside {field} differs from registered endpoint")
        for key in ("fixed_quantifiers", "masks_and_cutoffs", "signed_companions", "error_payment"):
            if not isinstance(contract.get(key), str) or not contract[key].strip():
                problems.append(f"outside source contract lacks {key}")
        return problems

    def gate(self, candidate, goal):
        claim = self.claims[candidate]
        proof = claim.get("proof")
        problems = self.audit(candidate)
        if not proof or goal == "lemma":
            return sorted(set(problems))
        if proof["scope"] != "unconditional" or proof["method"] == "finite":
            problems.append("success requires an unconditional analytic or formal theorem")
        contract = proof.get("contract", {})
        category = proof["result_type"]
        ledger = self.seed["ledger"]
        if goal == "S1":
            if category == "outside_upper":
                problems.extend(self.outside_contract(proof))
                endpoint = self.seed.get("endpoint", {})
                if not self.seed.get("commit") or not all(endpoint.get(k) for k in ("declaration", "evidence")):
                    problems.append("registered verified endpoint commit, declaration and evidence are required")
                threshold = number(ledger["lower"]) - number(ledger["box"])
                if number(contract["coefficient"]) >= threshold:
                    problems.append("outside upper leaves no strictly positive reserve")
                for obligation in self.seed["obligations"]:
                    if obligation == self.seed["outside_id"]:
                        if self.discharges.get(obligation) != (candidate, claim["hash"]):
                            problems.append("outside proof is not bound to the endpoint obligation")
                    if not self.assigned(obligation):
                        problems.append(f"endpoint still requires {obligation}")
            elif category != "infinitude":
                problems.append("no complete infinitude proof or qualifying FM outside upper")
            elif claim["proposal"]["statement"] != self.seed["goal_statement"]:
                problems.append("direct theorem does not state the registered infinitude goal")
            if category in ("infinitude", "outside_upper") and not contract.get("unbounded_scales"):
                problems.append("unbounded scales / infinitude implication undocumented")
        elif goal == "S2":
            if category not in ("outside_upper", "complete_upper"):
                problems.append("requires a complete normalized upper bound")
            else:
                if category == "outside_upper":
                    problems.extend(self.outside_contract(proof))
                for field in ("fixed_quantifiers", "signed_companions", "error_payment"):
                    if not contract.get(field):
                        problems.append(f"complete upper lacks {field}")
                old = contract.get("prior")
                if old not in self.claims or old == candidate:
                    problems.append("missing distinct independently certified comparator")
                else:
                    problems.extend(self.audit(old))
                    prior = self.claims[old].get("proof", {})
                    old_contract = prior.get("contract", {})
                    if prior.get("scope") != "unconditional" or prior.get("method") == "finite":
                        problems.append("comparator lacks an unconditional full-source bound")
                    if prior.get("result_type") == "outside_upper":
                        problems.extend(self.outside_contract(prior))
                    for field in ("fixed_quantifiers", "signed_companions", "error_payment"):
                        if not old_contract.get(field):
                            problems.append(f"old complete upper lacks {field}")
                    if (prior.get("result_type") != category or
                        any(old_contract.get(k) != contract.get(k) for k in ("population", "normalization"))):
                        problems.append("old bound covers a different source or normalization")
                    elif number(contract["coefficient"]) >= number(old_contract["coefficient"]):
                        problems.append("no strict upper-bound reduction")
        elif goal == "S3":
            if category != "parity":
                problems.append("no audited source-specific parity theorem")
            for field in ("prime_class", "escape_class", "new_signed_estimate", "terminal_splice"):
                if not contract.get(field):
                    problems.append(f"parity contract lacks {field}")
        else:
            raise ValueError(f"unknown success gate {goal}")
        return sorted(set(problems))

    def apply(self, e):
        kind = e["kind"]
        if e.get("evidence") is not None:
            validate_evidence(e["evidence"])
        if self.seed is None:
            require(kind == "seed", "initialize the journal first")
            require(e["version"] == SCHEMA_VERSION, "unsupported schema")
            require(e["commit"] is None or re.fullmatch(r"[0-9a-f]{40}", e["commit"]), "commit must be a full SHA or null")
            require(isinstance(e["obligations"], dict) and e["obligations"], "no endpoint obligations")
            for key, spec in e["obligations"].items():
                require(isinstance(key, str) and key, "invalid obligation ID")
                text = spec.get("statement") if isinstance(spec, dict) else spec
                require(isinstance(text, str) and text.strip(), f"empty statement for {key}")
            require(isinstance(e["sources"], list), "sources must be a list")
            for value in e["obligations"].values():
                if isinstance(value, dict) and "depends" in value:
                    require(strings(value["depends"]) and all(k in e["obligations"] for k in value["depends"]), "unknown obligation graph dependency")
            number(e["ledger"]["lower"])
            number(e["ledger"]["box"])
            self.seed = e
        elif kind == "candidate":
            required_text(e, "id", "actor", "statement", "source", "mechanism", "next")
            require(e["id"] not in self.claims and e["id"] not in self.seed["obligations"], "ID already exists")
            parents = e.get("parents", [])
            require(strings(parents) and all(p in self.claims for p in parents), "unknown parent")
            if len(parents) > 1:
                require(len({self.claims[p]["proposal"]["actor"] for p in parents}) > 1, "synthesis requires distinct originators")
            self.claims[e["id"]] = {"proposal": e, "attempts": [], "scores": {}, "reviews": {},
                "challenges": [], "answered": {}, "action": "discover", "hash": None, "next": e["next"],
                "authors": {e["actor"]}}
        elif kind in ("session", "check", "checkpoint"):
            if kind == "session":
                require(parse_time(e["deadline"]) > parse_time(e["started"]), "nonpositive session budget")
                self.session = e
            elif kind == "check":
                required_text(e, "id", "method", "status")
                require(e["method"] in ("lean", "finite", "sources"), "unknown verification method")
                require(not any(item.get("kind") == "check" and item["id"] == e["id"] for item in self.records), "check ID already used")
            else:
                required_text(e, "actor", "status", "next")
                require(e["status"] in ("ACTIVE", "INTERRUPTED_NOT_COMPLETED"), "research success uses the acceptance gate")
                require(e.get("candidate") is None or e["candidate"] in self.claims, "unknown checkpoint candidate")
        else:
            required_text(e, "candidate", "actor")
            require(e["candidate"] in self.claims, "unknown candidate")
            c = self.claims[e["candidate"]]
            if kind == "attempt":
                required_text(e, "result", "missing", "next")
                c["attempts"].append(e)
                c["authors"].add(e["actor"])
                if any(r["actor"] == e["actor"] for r in c["reviews"].values()):
                    c["reviews"] = {k: r for k, r in c["reviews"].items() if r["actor"] != e["actor"]}
                c["next"] = e["next"]
            elif kind == "compare":
                required_text(e, "finding", "next")
                parents = e["parents"]
                require(strings(parents) and e["candidate"] in parents and all(k in self.claims for k in parents), "invalid comparison set")
                require(len({self.claims[k]["proposal"]["actor"] for k in parents}) >= 2, "comparison requires distinct originators")
                require(all(self.claims[k]["attempts"] for k in parents), "record the independent derivations first")
                require(all(e["actor"] not in self.claims[k]["authors"] for k in parents), "comparison requires independent synthesis")
                self.comparisons.append(e)
                c["next"] = e["next"]
            elif kind == "rank":
                require(e["actor"] not in c["authors"], "rank requires independent evaluator")
                required_text(e, "reason")
                scores = e["scores"]
                require(set(scores) == set(DIMS) and all(type(v) is int and 0 <= v <= 4 for v in scores.values()), "score every dimension 0 through 4")
                c["scores"][e["actor"]] = scores
            elif kind == "challenge":
                required_text(e, "basis", "scope", "finding")
                require(e["basis"] in SCOPED_FAILURES, "invalid falsification basis")
                validate_evidence(e.get("evidence"))
                require(all(w["evidence"]["sha256"] != e["evidence"]["sha256"] for w in c["challenges"]), "challenge evidence already filed")
                c["challenges"].append(e)
            elif kind == "answer":
                required_text(e, "challenge_hash", "finding")
                validate_evidence(e.get("evidence"))
                require(e["actor"] not in c["authors"], "independent examiner must confirm the resolution")
                require(any(w["evidence"]["sha256"] == e["challenge_hash"] for w in c["challenges"]), "unknown challenge")
                c["answered"][e["challenge_hash"]] = e
            elif kind == "decision":
                required_text(e, "action", "reason", "next")
                action = e["action"]
                require(action in ("deepen", "repair", "park", "tombstone", "reopen"), "unknown decision")
                require(c["attempts"], "record a substantive attempt first")
                if c["action"] == "tombstone":
                    require(action == "reopen" and e.get("new_instrument"), "reentry needs a new instrument")
                if action == "tombstone":
                    witnesses = [w for w in c["challenges"] if w["evidence"]["sha256"] == e.get("challenge_hash")]
                    require(any(w["actor"] != e["actor"] and w["scope"] == e.get("scope") for w in witnesses),
                            "need an independently examined scoped challenge of exactly this scope")
                    required_text(e, "scope")
                c["action"], c["next"] = action, e["next"]
            elif kind == "proof":
                validate_evidence(e.get("evidence"))
                require(e["scope"] in ("unconditional", "conditional", "finite"), "invalid scope")
                require(e["method"] in ("analytic", "lean", "finite"), "invalid proof method")
                require(strings(e["deps"]) and strings(e["unpaid"]), "deps and unpaid must be explicit lists")
                require(all(x in self.seed["obligations"] or x in self.claims for x in e["deps"]), "declare every dependency")
                require(e["result_type"] in ("lemma", "parity", "complete_upper", "outside_upper", "infinitude"), "invalid result type")
                if e["result_type"] in ("complete_upper", "outside_upper"):
                    required_text(e["contract"], "population", "normalization")
                    number(e["contract"]["coefficient"])
                if e["method"] in ("lean", "finite"):
                    matching = [ch for ch in self.records if ch["kind"] == "check" and ch["method"] == e["method"]
                                and ch["id"] == e.get("check_id") and ch["status"] == "passed"]
                    require(matching and matching[0].get("sha256") == e["evidence"]["sha256"], "need a successful matching verification of this artifact")
                    if e["method"] == "lean":
                        require(matching[0].get("declaration"), "need a named Lean replay and axiom check")
                c["authors"].add(e["actor"])
                c["proof"], c["hash"], c["reviews"] = e, digest(encoded(e)), {}
            elif kind == "review":
                require(c["hash"] and e.get("proof_hash") == c["hash"], "review references a missing or stale proof hash")
                require(e["actor"] not in c["authors"], "proof contributors cannot referee their own candidate")
                require(e["role"] in REFEREES and e["verdict"] in ("pass", "block"), "invalid review")
                required_text(e, "finding")
                c["reviews"][e["role"], e["actor"]] = e
            elif kind == "discharge":
                require(c["hash"] and e.get("proof_hash") == c["hash"], "missing or stale discharge hash")
                issues = self.audit(e["candidate"])
                require(not issues, "; ".join(issues))
                require(c["proof"]["scope"] == "unconditional" and c["proof"]["method"] != "finite",
                        "analytic endpoint obligations require unconditional general proofs")
                spec = self.seed["obligations"].get(e["obligation"])
                statement = spec.get("statement") if isinstance(spec, dict) else spec
                require(statement == c["proposal"]["statement"], "prove the exact obligation or supply a proved adapter")
                if e["obligation"] == self.seed["outside_id"]:
                    require(c["proof"]["result_type"] == "outside_upper", "outside must be a complete bound")
                    problems = self.outside_contract(c["proof"])
                    require(not problems, "; ".join(problems))
                    threshold = number(self.seed["ledger"]["lower"]) - number(self.seed["ledger"]["box"])
                    require(number(c["proof"]["contract"]["coefficient"]) < threshold, "outside upper is not strict enough for this obligation")
                self.discharges[e["obligation"]] = (e["candidate"], c["hash"])
            elif kind == "accept":
                require(e.get("proof_hash") == c["hash"] and c["hash"], "missing or stale acceptance hash")
                require(e["goal"] in ("S1", "S2", "S3"), "invalid success goal")
                require(e["actor"] not in c["authors"], "independent terminal acceptance required")
                required_text(e, "finding")
                issues = self.gate(e["candidate"], e["goal"])
                require(not issues, "; ".join(issues))
                self.terminal.append(e)
            else:
                raise ValueError(f"unknown event kind {kind}")
        self.records.append(e)

    def priority(self, candidate):
        c = self.claims[candidate]
        independent = [v for k, v in c["scores"].items() if k not in c["authors"]]
        return median(sum(v.values()) for v in independent) if independent else 0

    def live(self):
        return sorted((k for k, c in self.claims.items() if c["action"] not in ("park", "tombstone")),
                      key=lambda k: (-self.priority(k), k != (self.comparisons[-1]["candidate"] if self.comparisons else None), k))

    def summary(self):
        open_items = {k: v for k, v in self.seed["obligations"].items() if not self.assigned(k)}
        ledger = self.seed["ledger"]
        target = number(ledger["lower"]) - number(ledger["box"])
        successes = sorted({e["goal"] for e in self.terminal if
            self.claims[e["candidate"]]["hash"] == e["proof_hash"] and not self.gate(e["candidate"], e["goal"])})
        checks = [{k: r.get(k) for k in ("id", "method", "status", "declaration")}
                  for r in self.records if r["kind"] == "check"]
        reviewed_outside = []
        for k, c in self.claims.items():
            p = c.get("proof", {})
            if (p.get("result_type") == "outside_upper" and p["scope"] == "unconditional"
                    and p["method"] != "finite" and not self.outside_contract(p) and not self.audit(k)):
                reviewed_outside.append(number(p["contract"]["coefficient"]))
        reserve = None
        if not open_items and self.assigned(self.seed["outside_id"]):
            assigned_id, _ = self.discharges[self.seed["outside_id"]]
            reserve = target - number(self.claims[assigned_id]["proof"]["contract"]["coefficient"])
        return {"commit": self.seed["commit"], "source_commit": self.seed.get("source_commit", self.seed["commit"]), "events": len(self.records),
            "programme": "CLOSED" if "S1" in successes else "ACTIVE", "reviewed_success": successes,
            "conditional_outside_threshold": exact(target),
            "reviewed_full_outside_upper": exact(min(reviewed_outside)) if reviewed_outside else None,
            "verified_FM_reserve_lower": exact(reserve) if reserve is not None else None,
            "open_obligations": open_items, "checks": checks,
            "candidates": {k: {"action": c["action"], "attempts": len(c["attempts"]),
                "proof_hash": c["hash"], "priority": self.priority(k), "next": c["next"]}
                for k, c in self.claims.items()}}

def new_row(previous, seq, timestamp, event):
    body = {"seq": seq, "at": timestamp, "prev": previous, "event": event}
    return {**body, "sha256": digest(encoded(body))}


class Journal:
    def __init__(self, db, create=False):
        path = Path(db)
        require(create or path.is_file(), f"journal {path} absent; run init or restore")
        if create:
            path.parent.mkdir(parents=True, exist_ok=True)
        self.db = sqlite3.connect(path, timeout=30, isolation_level=None)
        self.db.execute("PRAGMA synchronous=FULL")
        self.db.execute("CREATE TABLE IF NOT EXISTS journal (seq INTEGER PRIMARY KEY, row_json TEXT NOT NULL)")
        self.state = State()
        self.rows = []

    def close(self):
        self.db.close()

    def load(self):
        self.state, self.rows = State(), []
        for seq, obj in self.db.execute("SELECT seq, row_json FROM journal ORDER BY seq"):
            row = json.loads(obj)
            require(row["seq"] == seq, "database sequence differs from checkpoint")
            self.consume(row, save=False)

    def consume(self, row, save=True):
        parse_time(row["at"])
        label = row["event"].get("event_id")
        if label is not None:
            required_text(row["event"], "event_id")
            require(not any(r["event"].get("event_id") == label for r in self.rows), "duplicate event_id")
        prev = self.rows[-1]["sha256"] if self.rows else ZERO_HASH
        require(row == new_row(prev, len(self.rows) + 1, row["at"], row["event"]), "journal hash chain or sequence mismatch")
        self.state.apply(row["event"])
        if save:
            self.db.execute("INSERT INTO journal VALUES (?,?)", (row["seq"], encoded(row).decode()))
        self.rows.append(row)

    def append(self, event):
        if "event_id" in event:
            required_text(event, "event_id")
            prior = next((r["event"] for r in self.rows if r["event"].get("event_id") == event["event_id"]), None)
            if prior:
                require(prior == event, "event_id already used for different content")
                return
        prev = self.rows[-1]["sha256"] if self.rows else ZERO_HASH
        self.consume(new_row(prev, len(self.rows) + 1, now(), event))

    @contextlib.contextmanager
    def transaction(self, write=False):
        self.db.execute("BEGIN IMMEDIATE" if write else "BEGIN")
        try:
            self.load()
            yield
            self.db.commit()
        except BaseException:
            self.db.rollback()
            raise


def atomic_json(path, obj):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=path.parent, delete=False) as stream:
        tmp = Path(stream.name)
        try:
            json.dump(obj, stream, indent=2, sort_keys=True, ensure_ascii=False)
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
            stream.close()
            os.replace(tmp, path)
            if sys.platform != "win32":
                dir_fd = os.open(path.parent, os.O_RDONLY)
                try:
                    os.fsync(dir_fd)
                finally:
                    os.close(dir_fd)
        finally:
            tmp.unlink(missing_ok=True)


def checkpoint(rows):
    return {"format": "ETH-events-v1", "events": rows}


def recover(journal, file):
    backup = read_json(file)
    require(backup["format"] == "ETH-events-v1", "unknown portable checkpoint")
    incoming = backup["events"]
    require(isinstance(incoming, list) and incoming, "empty checkpoint")
    common = min(len(incoming), len(journal.rows))
    require(incoming[:common] == journal.rows[:common], "divergent histories; compare evidence and import new events explicitly")
    for row in incoming[common:]:
        journal.consume(row)
    return {"restored": max(0, len(incoming) - common), "events": len(journal.rows), "head": journal.rows[-1]["sha256"]}


def export(journal, path):
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    # Directory lock coordinates exports from separate SQLite work copies on POSIX.
    lock = None
    if os.name == "posix":
        import fcntl
        lock = os.open(target.parent, os.O_RDONLY)
    try:
        if lock is not None:
            fcntl.flock(lock, fcntl.LOCK_EX)
        if target.exists():
            old = read_json(target)
            require(old.get("format") == "ETH-events-v1" and isinstance(old.get("events"), list), "destination is not an ETH checkpoint")
            prior = old["events"]
            require(journal.rows[:len(prior)] == prior, "export would overwrite a divergent or newer checkpoint")
        atomic_json(target, checkpoint(journal.rows))
    finally:
        if lock is not None:
            os.close(lock)
    return {"events": len(journal.rows), "file": str(target), "head": journal.rows[-1]["sha256"]}


def inspect_sources(seed, root):
    results = []
    commit = seed.get("source_commit") or seed["commit"]
    if commit:
        cmd = subprocess.run(["git", "-C", str(root), "rev-parse", "HEAD"], capture_output=True, text=True)
        results.append({"type": "git", "expected": commit, "actual": cmd.stdout.strip() or None,
                        "match": cmd.returncode == 0 and cmd.stdout.strip() == commit})
    for source in seed["sources"]:
        if isinstance(source, dict) and "path" in source and "sha256" in source:
            file = root / source["path"]
            actual = digest(file.read_bytes()) if file.is_file() else None
            results.append({"type": "file", "path": source["path"], "expected": source["sha256"],
                            "actual": actual, "match": actual == source["sha256"]})
    return results


def run_check(args, seed):
    check = {"kind": "check", "id": args.id, "method": args.method, "at": now()}
    root = Path(args.cwd).resolve()
    if args.method == "sources":
        result = inspect_sources(seed, root)
        return {**check, "status": "passed" if result and all(i["match"] for i in result) else "unverified", "files": result}
    require(args.file, "specify the verifier / Lean source file")
    file = Path(args.file).resolve()
    require(file.is_file(), "verification file missing")
    data = file.read_bytes()
    check.update(file=file.name, sha256=digest(data))
    stdin = None
    if args.method == "finite":
        argv = [sys.executable, str(file), *args.arg]
    else:
        require(args.declaration and re.fullmatch(r"[\w'.]+", args.declaration), "supply --declaration Qualified.name")
        check["declaration"] = args.declaration
        pins = {name: digest((root / name).read_bytes()) for name in ("lean-toolchain", "lake-manifest.json") if (root / name).is_file()}
        check["pin_hashes"] = pins
        if "lean-toolchain" not in pins or not shutil.which("lake"):
            return {**check, "status": "unavailable", "details": "pinned toolchain or lake is unavailable"}
        stdin = data + f"\n#check @{args.declaration}\n#print axioms {args.declaration}\n".encode()
        argv = ["lake", "env", "lean", "--stdin"]
    try:
        proc = subprocess.run(argv, cwd=root, input=stdin, capture_output=True, timeout=args.timeout)
    except (subprocess.TimeoutExpired, OSError) as exc:
        return {**check, "status": "failed", "details": str(exc)}
    blob = proc.stdout + b"\n" + proc.stderr
    report = blob.decode("utf-8", errors="replace")
    passed = proc.returncode == 0
    if args.method == "lean":
        name = args.declaration
        match = re.search(r"'" + re.escape(name) + r"' depends on axioms:\s*\[([^\]]*)\]", report)
        zero = re.search(r"'" + re.escape(name) + r"' does not depend on any axioms", report)
        axioms = sorted(x.strip() for x in match.group(1).split(",") if x.strip()) if match else []
        check["axioms"] = axioms
        passed = passed and bool(match or zero) and set(axioms) <= {"propext", "Classical.choice", "Quot.sound"}
    return {**check, "status": "passed" if passed else "failed", "returncode": proc.returncode,
            "output_sha256": digest(blob), "output_tail": report[-16000:]}


def packet(state, role, candidate):
    if role == "synthesis":
        selected = candidate.split(",") if candidate else state.live()[:3]
        require(all(k in state.claims for k in selected), "unknown synthesis parent")
        return {"role": role, "instruction": ROLE_PROMPTS[role], "parents": selected,
                "inputs": [packet(state, "engineer", k) for k in selected], "goal": state.seed["goal_statement"]}
    if role == "frontier" and candidate is None:
        scopes = [{"id": k, "scope": c["challenges"][-1]["scope"]} for k, c in state.claims.items()
                  if c["action"] == "tombstone" and c["challenges"]]
        return {"role": role, "instruction": ROLE_PROMPTS[role], "commit": state.seed["commit"],
                "source_contracts": state.seed["sources"], "frontier": state.seed["next"], "scoped_tombstones": scopes}
    live = state.live()
    candidate = candidate or (live[0] if live else None)
    require(candidate is None or candidate in state.claims, "unknown candidate")
    if candidate is None:
        return {"role": role, "instruction": ROLE_PROMPTS[role], "task": state.seed["next"], "candidate": None}
    c = state.claims[candidate]
    return {"role": role, "instruction": ROLE_PROMPTS[role], "candidate": candidate, "proposal": c["proposal"],
            "latest_attempt": c["attempts"][-1] if c["attempts"] else None, "proof": c.get("proof"),
            "proof_hash": c["hash"], "blockers": state.audit(candidate), "next": c["next"],
            "challenges": c["challenges"], "challenge_answers": c["answered"], "reviews": list(c["reviews"].values())}


def worker_wave(state, wave):
    """All blind proposals in a wave receive the same source-only snapshot."""
    live = state.live()
    if not live:
        return [("frontier", "discover-1", None), ("frontier", "discover-2", None)]
    originals = [key for key in live if not state.claims[key]["proposal"].get("parents")]
    initial = [key for key in originals if not state.claims[key]["attempts"] and not state.claims[key]["hash"]]
    if initial:
        return [("engineer", "derive-" + k, k) for k in initial[:2]]
    crossed = [set(event["parents"]) for event in state.comparisons]
    crossed += [set(c["proposal"].get("parents", [])) for c in state.claims.values()]
    for i, left in enumerate(originals):
        for right in originals[i + 1:]:
            pair = {left, right}
            lhs, rhs = state.claims[left], state.claims[right]
            if (lhs["attempts"] and rhs["attempts"] and lhs["proposal"]["actor"] != rhs["proposal"]["actor"]
                    and not any(pair <= group for group in crossed)):
                return [("synthesis", "coordinator-synthesis", left + "," + right)]
    k = live[0]
    c = state.claims[k]
    if c["hash"]:
        assigned = {review["role"] for review in c["reviews"].values()}
        needed = [role for role in REFEREES if role not in assigned]
        if needed:
            return [(role, "referee-" + role, k) for role in needed]
    jobs = [("engineer", "proof-engineer", k)]
    if wave % 5 == 4:
        jobs.append(("frontier", "alternative-invention", None))
    return jobs


def drive(journal, args):
    worker = Path(args.worker).resolve()
    require(worker.is_file(), "supply an available Python research adapter")
    require(args.minutes > 0, "session budget must be positive")
    started = dt.datetime.now(dt.timezone.utc)
    budget = time.monotonic() + 60 * args.minutes
    with journal.transaction(write=True):
        require(journal.state.seed, "initialize the journal first")
        journal.append({"kind": "session", "actor": "adapter-coordinator", "started": started.isoformat(),
                        "deadline": (started + dt.timedelta(minutes=args.minutes)).isoformat()})
    wave = 0
    total = 0
    while time.monotonic() < budget:
        with journal.transaction():
            if "S1" in journal.state.summary()["reviewed_success"]:
                return {"outcome": "reviewed_S1", "waves": wave, "registered_events": total}
            jobs = worker_wave(journal.state, wave)
            head = journal.rows[-1]["sha256"]
            requests = [{"protocol": "ETH-worker-v1", "actor": actor, "head": head,
                         "packet": packet(journal.state, role, candidate)}
                        for role, actor, candidate in jobs]

        def call_worker(req):
            timeout = max(0.01, budget - time.monotonic())
            try:
                result = subprocess.run([sys.executable, str(worker)], input=encoded(req),
                                        capture_output=True, timeout=timeout)
                require(result.returncode == 0, "adapter exited " + str(result.returncode))
                response = json.loads(result.stdout)
                require(isinstance(response, dict) and response.get("head") == req["head"], "adapter returned wrong journal head")
                events = response.get("events")
                require(isinstance(events, list), "adapter response needs an events list")
                return req, events, response.get("handoff")
            except (ValueError, OSError, subprocess.SubprocessError) as exc:
                return req, [], str(exc)

        interruptions = []
        progress = 0
        with ThreadPoolExecutor(max_workers=len(requests)) as pool:
            for req, events, stop_reason in pool.map(call_worker, requests):
                if events:
                    try:
                        with journal.transaction(write=True):
                            before = len(journal.rows)
                            for raw in events:
                                event = attach(raw, worker.parent)
                                require(event.get("actor") == req["actor"], "adapter event actor differs from assigned worker")
                                require(event.get("kind") not in ("seed", "check", "session", "accept", "discharge"),
                                        "verification and final acceptance require their dedicated authority")
                                if event.get("kind") == "review":
                                    require(event["role"] == req["packet"]["role"], "review role differs from assigned worker")
                                event.setdefault("event_id", "adapter-" + digest(encoded(event)))
                                journal.append(event)
                            progress += len(journal.rows) - before
                    except (KeyError, TypeError, ValueError, OSError, sqlite3.Error) as exc:
                        interruptions.append({"actor": req["actor"], "reason": str(exc)})
                if stop_reason:
                    interruptions.append({"actor": req["actor"], "reason": str(stop_reason)})
        wave += 1
        total += progress
        if interruptions or not progress:
            return {"outcome": "checkpointed_handoff", "waves": wave, "registered_events": total,
                    "details": interruptions or [{"reason": "no new journal evidence returned"}]}
    return {"outcome": "time_budget_reached", "waves": wave, "registered_events": total}


def cli():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--db", default="eth.sqlite", help="local SQLite journal, export JSON for git / transfer")
    sub = parser.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("init")
    p.add_argument("seed", nargs="?")
    p = sub.add_parser("record")
    p.add_argument("event", help="one JSON event or an ordered batch")
    for cmd in ("export", "restore"):
        sub.add_parser(cmd).add_argument("path")
    sub.add_parser("status")
    sub.add_parser("graph")
    sub.add_parser("resume")
    p = sub.add_parser("next")
    p.add_argument("--role", choices=ROLE_PROMPTS, default="engineer")
    p.add_argument("--candidate")
    p = sub.add_parser("packet")
    p.add_argument("role", choices=ROLE_PROMPTS)
    p.add_argument("--candidate")
    sub.add_parser("search").add_argument("query")
    p = sub.add_parser("gate")
    p.add_argument("candidate")
    p.add_argument("goal", choices=("lemma", "S1", "S2", "S3"))
    p = sub.add_parser("drive", help="run an explicitly provided research-worker adapter until budget or handoff")
    p.add_argument("--minutes", type=int, default=60)
    p.add_argument("--worker", required=True, help="Python script accepting ETH-worker-v1 requests over stdin")
    p = sub.add_parser("session")
    p.add_argument("--minutes", default=60, type=int)
    p.add_argument("--actor", default="coordinator")
    p = sub.add_parser("check")
    p.add_argument("method", choices=("finite", "lean", "sources"))
    p.add_argument("file", nargs="?")
    p.add_argument("--id", required=True)
    p.add_argument("--cwd", default=".")
    p.add_argument("--timeout", type=int, default=180)
    p.add_argument("--declaration")
    p.add_argument("--arg", action="append", default=[])
    args = parser.parse_args()
    journal = Journal(args.db, create=args.cmd in ("init", "restore"))
    try:
        if args.cmd == "drive":
            started = time.monotonic()
            result = drive(journal, args)
            result["observed_wall_seconds"] = round(time.monotonic() - started, 2)
            if result["outcome"] != "reviewed_S1":
                with journal.transaction(write=True):
                    live = journal.state.live()
                    k = live[0] if live else None
                    task = journal.state.claims[k]["next"] if k else journal.state.seed["next"]
                    journal.append({"kind": "checkpoint", "actor": "adapter-coordinator", "status": "ACTIVE",
                                    "candidate": k, "next": task, "adapter_result": result})
            print(json.dumps(result, indent=2, ensure_ascii=False))
            return 0
        write = args.cmd in ("init", "restore", "record", "session")
        with journal.transaction(write):
            state = journal.state
            require(state.seed or args.cmd in ("init", "restore"), "empty journal")
            if args.cmd == "init":
                seed = normalize_seed(read_json(args.seed) if args.seed else {})
                if state.seed:
                    require(state.seed == seed, "seed differs; retain existing journal and reconcile explicitly")
                else:
                    journal.append(seed)
                output = state.summary()
            elif args.cmd == "restore":
                output = recover(journal, args.path)
            elif args.cmd == "record":
                data = read_json(args.event)
                for event in data if isinstance(data, list) else [data]:
                    require(event["kind"] not in ("seed", "session", "check"), "use the typed command to generate this event")
                    journal.append(attach(event, Path(args.event).parent))
                output = {"events": len(journal.rows), "head": journal.rows[-1]["sha256"],
                          "proof_hashes": {k: c["hash"] for k, c in state.claims.items() if c["hash"]}}
            elif args.cmd == "status":
                output = state.summary()
            elif args.cmd in ("packet", "next"):
                output = packet(state, args.role, args.candidate)
            elif args.cmd == "gate":
                require(args.candidate in state.claims, "unknown candidate")
                problems = state.gate(args.candidate, args.goal)
                output = {"eligible_for_separate_reviewed_acceptance": not problems, "blocked_by": problems}
            elif args.cmd == "graph":
                output = {"endpoint_obligations": state.seed["obligations"], "discharges": state.discharges,
                          "dependencies": {k: c.get("proof", {}).get("deps", []) for k, c in state.claims.items()},
                          "parents": {k: c["proposal"].get("parents", []) for k, c in state.claims.items()}}
            elif args.cmd == "search":
                q = args.query.casefold()
                output = [{"seq": r["seq"], "kind": r["event"]["kind"],
                           "id": r["event"].get("id", r["event"].get("candidate")), "sha256": r["sha256"]}
                          for r in journal.rows if q in encoded(r["event"]).decode().casefold()]
            elif args.cmd == "session":
                require(args.minutes > 0, "session budget must be positive")
                start = dt.datetime.now(dt.timezone.utc)
                event = {"kind": "session", "actor": args.actor, "started": start.isoformat(),
                         "deadline": (start + dt.timedelta(minutes=args.minutes)).isoformat()}
                journal.append(event)
                output = {**event, "worker": "Work coordinator must dispatch actual research workers"}
            elif args.cmd == "resume":
                last = next((e for e in reversed(state.records) if e["kind"] == "checkpoint"), None)
                remaining = None if not state.session else max(0, round((parse_time(state.session["deadline"]) -
                    dt.datetime.now(dt.timezone.utc)).total_seconds()))
                output = {"active_session": state.session, "budget_seconds_left": remaining,
                          "checkpoint": last, "head": journal.rows[-1]["sha256"],
                          "status": state.summary(), "work_packet": packet(state, "engineer", last.get("candidate") if last else None)}
            elif args.cmd == "export":
                output = export(journal, args.path)
            elif args.cmd == "check":
                require(args.timeout > 0, "use a positive timeout")
                seed = state.seed
        if args.cmd == "check":
            output = run_check(args, seed)
            with journal.transaction(write=True):
                journal.append(output)
        print(json.dumps(output, indent=2, ensure_ascii=False))
        return 1 if args.cmd == "check" and output["status"] != "passed" else 0
    finally:
        journal.close()


if __name__ == "__main__":
    try:
        sys.exit(cli())
    except (ValueError, OSError, sqlite3.Error, KeyError, TypeError, IndexError) as exc:
        print(f"ETH: {exc}", file=sys.stderr)
        sys.exit(2)
