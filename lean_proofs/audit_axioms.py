#!/usr/bin/env python3
"""Validate Lean #print axioms output against an explicit open-theorem allowlist."""
from pathlib import Path
import re
import sys

STANDARD = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_OPEN = set()


def parse(output: str) -> dict[str, set[str]]:
    records: dict[str, set[str]] = {}
    pattern = re.compile(r"'([^']+)' depends on axioms: \[(.*?)\]", re.S)
    for match in pattern.finditer(output):
        name, body = match.groups()
        axioms = {item.strip() for item in body.split(",") if item.strip()}
        if name in records:
            raise ValueError(f"duplicate audit record: {name}")
        records[name] = axioms
    for match in re.finditer(r"'([^']+)' does not depend on any axioms", output):
        name = match.group(1)
        if name in records:
            raise ValueError(f"duplicate audit record: {name}")
        records[name] = set()
    return records


def validate(expected: list[str], records: dict[str, set[str]], expected_open: set[str]) -> int:
    if len(expected) != len(set(expected)):
        raise ValueError("duplicate theorem in Audit.lean")
    missing = set(expected) - set(records)
    extra = set(records) - set(expected)
    if missing or extra:
        raise ValueError(f"audit coverage mismatch: missing={sorted(missing)}, extra={sorted(extra)}")
    failures = []
    for name in expected:
        axioms = records[name]
        unknown = axioms - STANDARD - {"sorryAx"}
        if unknown:
            failures.append(f"{name}: unknown axioms {sorted(unknown)}")
        has_sorry = "sorryAx" in axioms
        if name in expected_open and not has_sorry:
            failures.append(f"{name}: expected open item no longer reports sorryAx; update allowlist deliberately")
        if name not in expected_open and has_sorry:
            failures.append(f"{name}: unexpected sorryAx")
    if failures:
        raise ValueError("\n".join(failures))
    return len(expected) - len(expected_open)


def self_test() -> None:
    sample = """'ok' depends on axioms: [propext, Classical.choice]
'open' depends on axioms: [propext,
 sorryAx,
 Quot.sound]
'pure' does not depend on any axioms
"""
    records = parse(sample)
    assert records == {
        "ok": {"propext", "Classical.choice"},
        "open": {"propext", "sorryAx", "Quot.sound"},
        "pure": set(),
    }
    names = ["ok", "open", "pure"]
    assert validate(names, records, {"open"}) == 2

    def must_reject(call) -> None:
        try:
            call()
        except ValueError:
            return
        raise AssertionError("known-invalid audit was accepted")

    must_reject(lambda: validate(names, records, set()))
    must_reject(lambda: validate(["ok"], {"ok": {"CustomAxiom"}}, set()))
    must_reject(lambda: validate(names, {"ok": set()}, set()))
    must_reject(lambda: parse("'dup' depends on axioms: []\n'dup' depends on axioms: []"))


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: audit_axioms.py Audit.lean axiom-audit.log")
    self_test()
    audit_source = Path(sys.argv[1]).read_text(encoding="utf-8")
    output = Path(sys.argv[2]).read_text(encoding="utf-8")
    expected = re.findall(r"^#print axioms\s+(\S+)", audit_source, re.M)
    records = parse(output)
    try:
        clean = validate(expected, records, EXPECTED_OPEN)
    except ValueError as exc:
        raise SystemExit(str(exc)) from exc
    print(f"SELF_TEST=PASS; COVERAGE={len(expected)}/{len(expected)}; CLEAN={clean}; OPEN={len(EXPECTED_OPEN)}")
    for name in sorted(EXPECTED_OPEN):
        print(f"OPEN_SORRYAX={name}")


if __name__ == "__main__":
    main()
