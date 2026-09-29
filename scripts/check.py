#!/usr/bin/env python3
"""Local source, scope and axiom checks; not a Palomar mechanical report."""
from pathlib import Path
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Quot.sound", "Classical.choice"}
THEOREM = "CountablyInfiniteCrystallineMeasures.exhaustiveCardinalClaim"


def require(condition, message):
    if not condition:
        raise SystemExit("FAIL: " + message)


def uncomment(source):
    """Remove nested Lean comments and strings, preserving newline positions."""
    output = []
    depth = 0
    quoted = False
    i = 0
    while i < len(source):
        pair = source[i:i + 2]
        char = source[i]
        if quoted:
            if char == "\\":
                i += 2
                continue
            if char == '"':
                quoted = False
            output.append("\n" if char == "\n" else " ")
            i += 1
        elif not depth and char == '"':
            quoted = True
            output.append(" ")
            i += 1
        elif pair == "/-":
            depth += 1
            output.append("  ")
            i += 2
        elif depth and pair == "-/":
            depth -= 1
            output.append("  ")
            i += 2
        elif depth:
            output.append("\n" if char == "\n" else " ")
            i += 1
        elif pair == "--":
            end = source.find("\n", i)
            end = len(source) if end == -1 else end
            output.append(" " * (end - i))
            i = end
        else:
            output.append(char)
            i += 1
    require(depth == 0 and not quoted, "unterminated Lean comment or string")
    return "".join(output)


def imports(source):
    return re.findall(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)",
                      uncomment(source), re.M)


def json_file(path):
    # formalization.yaml uses JSON, a YAML 1.2 subset, with an opening comment.
    source = "\n".join(line for line in path.read_text().splitlines()
                       if not line.startswith("#"))
    def unique(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, f"duplicate key {key} in {path.name}")
            result[key] = value
        return result
    return json.loads(source, object_pairs_hook=unique)


def main():
    require(sys.argv[1:] in ([], ["--source-only"]), "usage: check.py [--source-only]")
    files = [p for p in ROOT.rglob("*")
             if not {".git", ".lake", "__pycache__"}.intersection(p.relative_to(ROOT).parts)
             and (p.is_file() or p.is_symlink())]
    require(sum(p.stat().st_size for p in files) < 500 * 2**20, "source snapshot exceeds 500 MiB")
    require(not (ROOT / "lakefile.lean").exists(), "more than one Lakefile")
    require((ROOT / "lakefile.toml").is_file(), "missing root TOML Lakefile")
    require(not (ROOT / ".gitmodules").exists(), "submodules are not allowed")
    compiled = {".olean", ".ilean", ".a", ".bc", ".dll", ".dylib", ".o", ".obj", ".so", ".trace"}
    for path in files:
        require(path.suffix not in compiled, f"compiled output outside .lake: {path}")
        require(not path.read_bytes().startswith(b"version https://git-lfs.github.com/spec/v1"),
                f"LFS pointer: {path}")

    lean = {str(p.relative_to(ROOT).with_suffix("")).replace("/", "."): p
            for p in files if p.suffix == ".lean"}
    for name, path in lean.items():
        require(not path.is_symlink(), f"Lean source symlink: {path}")
        source = path.read_text()
        code = uncomment(source)
        require(re.match(r"\s*module\b", code) is not None, f"missing module header: {name}")
        require(len(source.splitlines()) <= 10000, f"oversized Lean file: {name}")
        forbidden = re.findall(r"\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|sorryAx|ofReduceBool)\b", code)
        require(forbidden == (["sorry"] if name == "Challenge" else []),
                f"unexpected proof hole or unsafe construct in {name}: {forbidden}")
    challenge = lean["Challenge"].read_text()
    require(len(challenge.encode()) <= 100 * 1024 and len(challenge.splitlines()) <= 1000,
            "Challenge exceeds Palomar limits")
    require(all(m.startswith("Mathlib.") for m in imports(challenge)),
            "Challenge must use only canonical Mathlib imports")
    reachable = set()
    pending = ["Solution"]
    while pending:
        module = pending.pop()
        if module in reachable or module not in lean:
            continue
        reachable.add(module)
        pending.extend(imports(lean[module].read_text()))
    require("Challenge" not in reachable, "Solution imports the statement's placeholder")
    require(set(lean) == reachable | {"Challenge"},
            f"source outside proof closure: {sorted(set(lean) - reachable - {'Challenge'})}")
    provenance = json_file(ROOT / "docs/extraction.json")
    require({entry["path"] for entry in provenance["files"]} ==
            {str(p.relative_to(ROOT)) for n, p in lean.items() if n.startswith("MeyerGeneralProblem.")},
            "extraction manifest and proof source set differ")

    config = json_file(ROOT / "comparator.json")
    require(config == {"challenge_module": "Challenge", "solution_module": "Solution",
                       "theorem_names": [THEOREM],
                       "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]},
            "unexpected Comparator scope or axioms")
    lock = json_file(ROOT / "lake-manifest.json")
    for package in lock["packages"]:
        require(package["type"] == "git", "only pinned public Git dependencies are supported")
        require(re.fullmatch(r"[0-9a-f]{40}", package["rev"]), "dependency lacks a full SHA")
        require(re.fullmatch(r"https://github\.com/[\w.-]+/[\w.-]+(?:\.git)?", package["url"]),
                "dependency URL is not credential-free public GitHub HTTPS")
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    require(re.fullmatch(r"leanprover/lean4:v\d+\.\d+\.\d+(?:-rc\d+)?", toolchain),
            "unrecognized release toolchain")
    require(toolchain == (ROOT / ".lake/packages/mathlib/lean-toolchain").read_text().strip(),
            "project and Mathlib toolchains differ")
    for package in lock["packages"]:
        directory = ROOT / ".lake/packages" / package["name"]
        revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=directory, text=True).strip()
        require(revision == package["rev"], f"dependency checkout differs: {package['name']}")
        dirty = subprocess.check_output(["git", "diff", "HEAD", "--name-only"], cwd=directory, text=True)
        require(not dirty, f"modified dependency source: {package['name']}")

    metadata = json_file(ROOT / "formalization.yaml")
    require(metadata["version"] == "v0.4", "wrong metadata version")
    project = metadata["project"]
    for key in ("name", "description", "authors", "responsible_maintainers"):
        require(bool(project[key]), f"missing project.{key}")
    require(len(project["name"]) <= 300 and len(project["description"]) <= 10000,
            "metadata title or abstract is oversized")
    license_files = [p for p in files if p.parent == ROOT and
                     re.fullmatch(r"(?i)(LICENSE|LICENCE|COPYING|UNLICENSE|OFL)(\.(md|markdown|txt))?", p.name)]
    require(license_files == [ROOT / "LICENSE"], "expected exactly one root license file")
    require(project["license"] == "MIT" and (ROOT / "LICENSE").read_text().startswith("MIT License\n"),
            "license declaration mismatch")
    require(metadata["sources"] and any(s["relationship"] in {"formalizes", "adapts", "independently-proves"}
            for s in metadata["sources"]), "missing substantive source attribution")
    require(all(s.get("type") != "original-proof" for s in metadata["sources"]), "inconsistent source origin")
    require(metadata["automation"]["methods"] and metadata["review"]["status"], "missing production disclosure")
    require(metadata["classification"]["arxiv"], "missing mathematical classification")

    if sys.argv[1:] == ["--source-only"]:
        print(f"PASS: source/metadata preparation checks for {len(lean)} Lean modules.")
        print("Build, axiom and Palomar checks were not run.")
        return

    subprocess.run(["lake", "build", "Challenge", "Solution"], cwd=ROOT, check=True)
    # Identical source text can elaborate differently under different imports.
    # Compare fully explicit types in separate processes, since both modules
    # deliberately declare the same names and cannot be imported together.
    statement_types = []
    for module in ("Challenge", "Solution"):
        probe = ROOT / f".lake/{module}TypeAudit.lean"
        probe.write_text(f"module\nimport {module}\nset_option pp.all true\n#check {THEOREM}\n")
        result = subprocess.run(["lake", "env", "lean", str(probe)], cwd=ROOT,
                                check=True, text=True, capture_output=True)
        statement_types.append(result.stdout)
    require(statement_types[0] == statement_types[1],
            "Challenge and Solution elaborate to different explicit theorem types; run Comparator")
    audit = ROOT / ".lake/AxiomAudit.lean"
    audit.write_text(f"module\nimport Solution\n#print axioms {THEOREM}\n")
    result = subprocess.run(["lake", "env", "lean", str(audit)], cwd=ROOT,
                            check=True, text=True, capture_output=True)
    match = re.search(r"depends on axioms:\s*\[([^\]]*)\]", result.stdout)
    require(match is not None, "missing theorem axiom report")
    axioms = {a.strip() for a in match[1].split(",") if a.strip()}
    require(axioms <= ALLOWED, f"unpermitted theorem axioms: {sorted(axioms - ALLOWED)}")
    print(result.stdout.strip())
    subprocess.run(["git", "diff", "--check"], cwd=ROOT, check=True)
    print(f"PASS: {len(lean)} module sources; exact proof closure; pinned dependencies; "
          "metadata and license shape; matching explicit theorem types; "
          "built theorem; standard axioms only.")
    print("This is a local preparation check, not Palomar's full mechanical verification.")


if __name__ == "__main__":
    main()
