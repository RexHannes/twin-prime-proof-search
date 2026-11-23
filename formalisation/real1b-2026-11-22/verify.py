"""Reproduce the REAL 1B replay from the repository and check every audited theorem."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import ssl
import subprocess
import sys
import urllib.request

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
ENTRY = "RequestProject.REAL1B_20261122"
ENVIRONMENT = "lean-4.28.0"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
SERVICE = "https://axle.axiommath.ai/api/v1/check"


def generate_replay():
    bodies, seen = [], set()

    def visit(module):
        if module in seen or module == "Mathlib":
            return
        seen.add(module)
        path = Path(*module.split(".")).with_suffix(".lean")
        lines = (ROOT / path).read_text().splitlines()
        while lines and lines[0].startswith("import "):
            visit(lines.pop(0).removeprefix("import ").strip())
        bodies.append(f"-- {path.as_posix()}\n" + "\n".join(lines).strip())

    visit(ENTRY)
    return "import Mathlib\n\n" + "\n\n".join(bodies) + "\n"


def check_audits(output, names):
    for name in names:
        match = re.search("'" + re.escape(name) +
                          r"' depends on axioms:\s*\[([^\]]*)\]", output)
        if match:
            axioms = {s.strip() for s in match[1].split(",") if s.strip()}
            if axioms <= ALLOWED:
                continue
            raise ValueError(f"{name} depends on {sorted(axioms - ALLOWED)}")
        if f"'{name}' does not depend on any axioms" not in output:
            raise ValueError(f"Missing compiler audit for {name}")


def online(source, names):
    data = {"content": source, "environment": ENVIRONMENT, "ignore_imports": False,
            "timeout_seconds": 180}
    req = urllib.request.Request(SERVICE, data=json.dumps(data).encode(),
                                 headers={"Content-Type": "application/json"})
    tls = ssl.create_default_context()
    system_roots = Path("/etc/ssl/cert.pem")
    if sys.platform == "darwin" and system_roots.is_file():
        tls.load_verify_locations(cafile=str(system_roots))
    with urllib.request.urlopen(req, timeout=270, context=tls) as response:
        result = json.load(response)
    for key in ("lean_messages", "tool_messages"):
        messages = result[key]
        if messages["errors"] or messages["warnings"]:
            raise ValueError(json.dumps(messages, ensure_ascii=False))
    if not result["okay"] or result["failed_declarations"] or result["content"].strip() != source.strip():
        raise ValueError("Online checker rejected the replay or changed its source")
    check_audits("\n".join(result["lean_messages"]["infos"]), names)
    print("AXLE request", result["info"]["request_id"])


def native(names):
    subprocess.run(["lake", "exe", "cache", "get"], cwd=ROOT, check=True)
    subprocess.run(["lake", "build", ENTRY], cwd=ROOT, check=True)
    commands = f"import {ENTRY}\n" + "\n".join(
        f"#check @{name}\n#print axioms {name}" for name in names)
    result = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=ROOT, input=commands,
                            text=True, capture_output=True)
    output = result.stdout + result.stderr
    if result.returncode or "warning:" in output or "error:" in output:
        raise ValueError(output)
    check_audits(output, names)
    print(output.rstrip())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--online", action="store_true", help="check the single file on AXLE")
    mode.add_argument("--lake", action="store_true", help="build and audit the pinned Lake modules")
    mode.add_argument("--write-replay", action="store_true", help="regenerate Replay.lean from imports")
    args = parser.parse_args()
    source = generate_replay()
    replay = HERE / "Replay.lean"
    if args.write_replay:
        replay.write_text(source)
        return
    record = json.loads((HERE / "Verification.json").read_text())
    digest = hashlib.sha256(source.encode()).hexdigest()
    if replay.read_bytes() != source.encode() or record["sha256"] != digest:
        raise ValueError("Repository modules, standalone replay or recorded SHA-256 differ")
    names = re.findall(r"^#print axioms ([\w.]+)$", source, re.MULTILINE)
    if not names or len(names) != len(set(names)) or set(names) != set(record["audited_declarations"]):
        raise ValueError("Audited theorem list differs from the verification record")
    paper_source = HERE / "REAL1B_Gold4_59_FM_Joint_Signed_Verify_20261123.py"
    if hashlib.sha256(paper_source.read_bytes()).hexdigest() != record["joint_verifier"]["source_sha256"]:
        raise ValueError("Gold 4.59 verifier differs from its recorded source")
    paper = subprocess.check_output([sys.executable, str(paper_source)])
    canonical = json.dumps(json.loads(paper), sort_keys=True, separators=(",", ":")).encode()
    if hashlib.sha256(canonical).hexdigest() != record["joint_verifier"]["result_sha256"]:
        raise ValueError("Gold 4.59 finite checks differ from the source registry")
    print("Gold 4.59 finite checks match the original registry.", flush=True)
    subprocess.run([sys.executable, str(HERE / "boxwise.py")], check=True)
    subprocess.run([sys.executable, str(HERE / "full_box.py")], check=True)
    if args.online:
        online(source, names)
    else:
        native(names)
    print(f"Verified {len(names)} declarations. SHA-256 {digest}")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.CalledProcessError) as err:
        sys.exit(str(err))
