#!/usr/bin/env python3
"""Run the nine frozen single-fault corpus hostiles.

The driver never invokes the corpus producer.  Author self-tests use a fixed
hand-built projection; execution mode extracts an n<=3 projection from an
already checked supplied corpus.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


FIELDS = [
    "cup_anchor_left", "cup_anchor_right", "cup_straddled",
    "cap_anchor_left", "cap_anchor_right", "cap_straddled",
    "contains_strong_five",
]
EXPECTED = (
    "OMISSION", "DUPLICATION", "ID_COLLISION", "ROOT_INCOMPATIBLE",
    "WRONG_HOLE_TYPE", "STALE_PARENT", "OUTPUT_BIT_FLIP",
    "SPLIT_LEAKAGE", "EXTERNAL_CONTROL_MUTATION",
)
RECEIPT_LIMIT = 2_000_000


def cjson(value: object) -> bytes:
    return json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":")).encode("ascii")


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def rid(preimage: str) -> str:
    return "sha256:" + sha(preimage.encode("ascii"))


def stream(rows) -> str:
    digest = hashlib.sha256()
    for row in rows:
        digest.update(cjson(row) + b"\n")
    return digest.hexdigest()


def reseal(corpus: dict) -> dict:
    split = corpus["split"]
    corpus["counts"] = {
        "subtrees": len(corpus["subtree_records"]),
        "roots": len(corpus["root_records"]),
        "contexts": len(corpus["context_records"]),
        "coordinates": len(corpus["coordinate_records"]),
        "entries": len(corpus["substitution_entries"]),
        "training_roots": len(split["training_root_ids"]),
        "withheld_roots": len(split["withheld_root_ids"]),
        "training_entries": len(split["training_entry_ids"]),
        "withheld_entries": len(split["withheld_entry_ids"]),
        "external_controls": len(corpus["external_controls"]),
    }
    hashes = {
        "subtree_records_sha256": stream(corpus["subtree_records"]),
        "root_records_sha256": stream(corpus["root_records"]),
        "context_records_sha256": stream(corpus["context_records"]),
        "coordinate_records_sha256": stream(corpus["coordinate_records"]),
        "substitution_entries_sha256": stream(corpus["substitution_entries"]),
        "split_sha256": stream([split]),
        "external_controls_sha256": stream(corpus["external_controls"]),
    }
    semantic = "".join(
        f"{label}={hashes[key]}\n" for label, key in (
            ("subtree", "subtree_records_sha256"), ("root", "root_records_sha256"),
            ("context", "context_records_sha256"), ("coordinate", "coordinate_records_sha256"),
            ("entry", "substitution_entries_sha256"), ("split", "split_sha256"),
            ("external_control", "external_controls_sha256"),
        )
    ).encode("ascii")
    hashes["corpus_semantic_sha256"] = sha(semantic)
    corpus["stream_hashes"] = hashes
    return corpus


def profile(n: int, seed: int = 0) -> list[list[int]]:
    rows = []
    for gap in range(n + 1):
        value = (seed + gap) % 3
        rows.append([min(n, 2 + value), value, min(n, 1 + value), min(n, 2), value, min(n, 1), 0])
    return rows


def hand_built_fixture() -> dict:
    def subtree(n: int, coloring: str, seed: int):
        pre = f"S|arity={n:02d}|coloring={coloring}"
        return {"id": rid(pre), "identity_preimage": pre, "arity": n,
                "coloring_hex": coloring, "profiles": profile(n, seed)}

    s1 = subtree(1, "0", 0)
    s2 = subtree(2, "0", 1)
    s3a = subtree(3, "0", 2)
    s3b = subtree(3, "1", 3)
    subtrees = sorted([s1, s2, s3a, s3b], key=lambda row: row["identity_preimage"])

    def root(lower: str, parent: dict):
        pre = f"R|arity=03|lower={lower}|lower_id={s1['id']}|upper_id={s2['id']}"
        return {"id": rid(pre), "identity_preimage": pre, "arity": 3,
                "lower_mask_hex": lower, "parent_subtree_id": parent["id"],
                "lower_subtree_id": s1["id"], "upper_subtree_id": s2["id"]}

    roots = sorted([root("1", s3a), root("2", s3b)], key=lambda row: row["identity_preimage"])
    contexts = []
    root_context = {}
    for root_row in roots:
        lower = int(root_row["lower_mask_hex"], 16)
        sides = (("lower", lower, s2), ("upper", 7 ^ lower, s1))
        root_context[root_row["id"]] = {}
        for side, hole, sibling in sides:
            pre = (
                f"C|arity=03|lower={root_row['lower_mask_hex']}|hole_side={side}"
                f"|sibling_id={sibling['id']}"
            )
            row = {"id": rid(pre), "identity_preimage": pre, "arity": 3,
                   "lower_mask_hex": root_row["lower_mask_hex"], "hole_side": side,
                   "hole_mask_hex": f"{hole:x}", "hole_arity": hole.bit_count(),
                   "sibling_subtree_id": sibling["id"]}
            contexts.append(row)
            root_context[root_row["id"]][side] = row["id"]
    contexts.sort(key=lambda row: row["identity_preimage"])
    entries = []
    partitions = {roots[0]["id"]: "withheld_root", roots[1]["id"]: "training"}
    subtree_by_id = {row["id"]: row for row in subtrees}
    for root_row in roots:
        parent = subtree_by_id[root_row["parent_subtree_id"]]
        for side, child in (("lower", s1), ("upper", s2)):
            context_id = root_context[root_row["id"]][side]
            pre = f"E|context_id={context_id}|child_id={child['id']}"
            entries.append({"id": rid(pre), "identity_preimage": pre,
                            "root_id": root_row["id"], "context_id": context_id,
                            "child_subtree_id": child["id"],
                            "parent_subtree_id": parent["id"],
                            "partition": partitions[root_row["id"]],
                            "output_profiles": parent["profiles"]})
    entries.sort(key=lambda row: row["identity_preimage"])
    qpre = "Q|arity=03|gap=00|field=0"
    coordinates = [{"id": rid(qpre), "identity_preimage": qpre, "arity": 3,
                    "gap": 0, "field_index": 0, "field": FIELDS[0]}]
    zero_profile = [[0, 0, 0, 0, 0, 0, 0] for _ in range(10)]
    left_difference = [2, 3, 4, 3, 4, 5, 0]
    right_difference = [2, 3, 4, 3, 5, 5, 0]
    external = [{
        "control_id": "K6N9-SINGLETON-COLLISION-V1",
        "role": "external_control_not_in_k5_train_or_holdout",
        "source_path": "data/derived/e3-context-k6-n9-singleton-collision.json",
        "source_sha256": "2a7a7930d4e68b0c9836076c0ec9f5573ba3af56cca577e6f17162d892f2a142",
        "n": 9, "k": 6, "lower_mask_hex": "2", "upper_mask_hex": "1fd",
        "crossing_bits_hex": "00000000000000000007f",
        "profile_fields": [
            "cup_anchor_left", "cup_anchor_right", "cup_straddled",
            "cap_anchor_left", "cap_anchor_right", "cap_straddled",
            "contains_strong_six",
        ],
        "equal_upper_all_gap_profile": zero_profile,
        "first_difference": {"gap": 6, "fields": ["cap_anchor_right"],
                             "left": left_difference, "right": right_difference},
        "left": {"upper_coloring_hex": "0", "parent_coloring_hex": "0",
                 "upper_tree": 0, "parent_profile": zero_profile},
        "right": {"upper_coloring_hex": "1", "parent_coloring_hex": "1",
                  "upper_tree": 1, "parent_profile": zero_profile},
    }]
    split = {
        "rule_id": "PARENT-ID-MOD5-V1",
        "grouping_key": "arity plus parent_subtree_id; every root and both side entries for one parent stay together",
        "parent_order": "strict ASCII order of parent subtree identity_preimage within each arity",
        "eligible_layer_rule": "if an arity has at least two distinct rooted parents, zero-based parent indices congruent to 0 modulo 5 are withheld; a layer with fewer than two rooted parents is all training",
        "modulus": 5, "withheld_residue": 0,
        "training_root_ids": sorted([roots[1]["id"]]),
        "withheld_root_ids": sorted([roots[0]["id"]]),
        "training_entry_ids": sorted(row["id"] for row in entries if row["partition"] == "training"),
        "withheld_entry_ids": sorted(row["id"] for row in entries if row["partition"] == "withheld_root"),
    }
    corpus = {
        "schema_version": 1, "corpus_id": "SYNTHETIC-HANKEL-CONTEXT-PROJECTION-V1",
        "scope": {"model": "recursively_decomposable_triple_colorings", "k": 5,
                  "profile_clip": 5, "minimum_n": 1, "maximum_n": 3, "exact": True,
                  "root_scope": "every distinct coloring and every compatible ordered lower/upper root",
                  "context_scope": "both one-step typed hole sides of every compatible root; arbitrary outer contexts are finite compositions of these frames"},
        "provenance": {"generation_base_revision": "0" * 40, "schema_path": "synthetic",
                       "schema_sha256": "0" * 64, "producer_path": "synthetic",
                       "producer_sha256": "0" * 64, "checker_path": "synthetic",
                       "checker_sha256": "0" * 64,
                       "external_control_path": "data/derived/e3-context-k6-n9-singleton-collision.json",
                       "external_control_sha256": "2a7a7930d4e68b0c9836076c0ec9f5573ba3af56cca577e6f17162d892f2a142"},
        "canonicalization": {"version": "HANKEL-CONTEXT-ASCII-V1",
                             "id_algorithm": "sha256:<lowercase hex SHA-256 of the UTF-8 identity_preimage bytes>",
                             "record_order": "strict ascending ASCII identity_preimage; duplicate IDs or preimages forbidden",
                             "stream_encoding": "UTF-8 compact canonical JSON record plus LF: recursively ASCII-sort object keys, preserve array order, emit no whitespace, decimal integers, lowercase true/false, and shortest JSON string escapes"},
        "profile_spec": {"fields": FIELDS, "gap_order": "gap 0 through gap arity, inclusive",
                         "field_semantics": "first six fields are exact maximum monochromatic chain lengths clipped at 5 in left/right/straddled anchor relation; final field is the exact 0/1 existence bit for a strong five-set"},
        "subtree_records": subtrees, "root_records": roots, "context_records": contexts,
        "coordinate_records": coordinates, "substitution_entries": entries,
        "split": split, "external_controls": external,
    }
    return reseal(corpus)


def projection(full: dict) -> dict:
    result = copy.deepcopy(full)
    root_ids = {row["id"] for row in result["root_records"] if row["arity"] <= 3}
    result["scope"]["maximum_n"] = 3
    result["subtree_records"] = [row for row in result["subtree_records"] if row["arity"] <= 3]
    result["root_records"] = [row for row in result["root_records"] if row["id"] in root_ids]
    result["context_records"] = [row for row in result["context_records"] if row["arity"] <= 3]
    result["coordinate_records"] = [row for row in result["coordinate_records"] if row["arity"] <= 3]
    result["substitution_entries"] = [row for row in result["substitution_entries"] if row["root_id"] in root_ids]
    entry_ids = {row["id"] for row in result["substitution_entries"]}
    for key in ("training_root_ids", "withheld_root_ids"):
        result["split"][key] = [value for value in result["split"][key] if value in root_ids]
    for key in ("training_entry_ids", "withheld_entry_ids"):
        result["split"][key] = [value for value in result["split"][key] if value in entry_ids]
    return reseal(result)


def mutations(baseline: dict):
    def omission(value):
        value["substitution_entries"].pop(0)

    def duplication(value):
        value["root_records"].append(copy.deepcopy(value["root_records"][0]))

    def collision(value):
        value["context_records"][0]["id"] = value["context_records"][1]["id"]

    def root_bad(value):
        row = value["root_records"][0]
        mask = int(row["lower_mask_hex"], 16)
        replacement = 2 if mask != 2 else 1
        row["lower_mask_hex"] = f"{replacement:x}"

    def hole_bad(value):
        row = value["context_records"][0]
        row["hole_side"] = "upper" if row["hole_side"] == "lower" else "lower"

    def stale(value):
        row = value["substitution_entries"][0]
        alternatives = [item["id"] for item in value["subtree_records"] if item["id"] != row["parent_subtree_id"]]
        row["parent_subtree_id"] = alternatives[0]

    def bit_flip(value):
        cell = value["substitution_entries"][0]["output_profiles"][0]
        cell[0] = (cell[0] + 1) % 6

    def leakage(value):
        root_id = value["split"]["withheld_root_ids"][0]
        entry_id = value["split"]["withheld_entry_ids"][0]
        value["split"]["training_root_ids"].append(root_id)
        value["split"]["training_entry_ids"].append(entry_id)

    def external(value):
        cell = value["external_controls"][0]["first_difference"]["right"]
        cell[4] = (cell[4] + 1) % 7

    return (
        ("OMISSION", "/substitution_entries/0", omission),
        ("DUPLICATION", "/root_records/-", duplication),
        ("ID_COLLISION", "/context_records/0/id", collision),
        ("ROOT_INCOMPATIBLE", "/root_records/0/lower_mask_hex", root_bad),
        ("WRONG_HOLE_TYPE", "/context_records/0/hole_side", hole_bad),
        ("STALE_PARENT", "/substitution_entries/0/parent_subtree_id", stale),
        ("OUTPUT_BIT_FLIP", "/substitution_entries/0/output_profiles/0/0", bit_flip),
        ("SPLIT_LEAKAGE", "/split/training_*_ids/-", leakage),
        ("EXTERNAL_CONTROL_MUTATION", "/external_controls/0/first_difference/right/4", external),
    )


def run_checker(checker: Path, schema: Path, corpus: Path, baseline: Path | None = None):
    command = [sys.executable, "-B", str(checker), "--schema", str(schema),
               "--corpus", str(corpus), "--projection-only"]
    if baseline is not None:
        command.extend(["--projection-baseline", str(baseline)])
    completed = subprocess.run(command, text=True, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, timeout=30, check=False)
    try:
        outcome = json.loads(completed.stdout.strip().splitlines()[-1])
    except (IndexError, json.JSONDecodeError):
        raise RuntimeError("checker produced no JSON diagnostic") from None
    return completed.returncode, outcome


def exercise(baseline: dict, checker: Path, schema: Path) -> dict:
    results = []
    with tempfile.TemporaryDirectory(prefix="hankel-hostiles-") as directory:
        directory_path = Path(directory)
        baseline_path = directory_path / "baseline.json"
        baseline_path.write_bytes(cjson(baseline) + b"\n")
        status, accepted = run_checker(checker, schema, baseline_path)
        if status != 0 or not accepted.get("ok"):
            raise RuntimeError("hand-built projection was not accepted")
        for diagnostic, pointer, mutate in mutations(baseline):
            changed = copy.deepcopy(baseline)
            mutate(changed)
            mutation_path = directory_path / "mutation.json"
            mutation_path.write_bytes(cjson(changed) + b"\n")
            try:
                status, outcome = run_checker(checker, schema, mutation_path, baseline_path)
            finally:
                mutation_path.unlink(missing_ok=True)
            observed = outcome.get("diagnostic")
            if status == 0 or observed != diagnostic:
                raise RuntimeError(f"{diagnostic} expected, observed status={status} diagnostic={observed}")
            results.append({"mutation_id": diagnostic, "json_pointer": pointer,
                            "checker_exit_status": status, "diagnostic": observed})
        if (directory_path / "mutation.json").exists():
            raise RuntimeError("temporary mutation retained")
    return {"baseline_sha256": sha(cjson(baseline) + b"\n"),
            "accepted_baseline": True, "hostiles": results,
            "diagnostics": [row["diagnostic"] for row in results],
            "ok": tuple(row["diagnostic"] for row in results) == EXPECTED}


def atomic_new(path: Path, value: dict) -> None:
    if path.exists() or path.is_symlink():
        raise RuntimeError("receipt exists")
    temporary = path.with_name("." + path.name + ".tmp")
    if temporary.exists() or temporary.is_symlink():
        raise RuntimeError("receipt temporary exists")
    payload = cjson(value) + b"\n"
    if len(payload) > RECEIPT_LIMIT:
        raise RuntimeError("receipt exceeds 2000000 bytes")
    with temporary.open("xb") as handle:
        handle.write(payload)
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(temporary, path)


def main() -> None:
    parser = argparse.ArgumentParser(description="Run nine one-at-a-time FD014 hostile mutations.")
    parser.add_argument("--schema", type=Path, required=True)
    parser.add_argument("--corpus", type=Path)
    parser.add_argument("--checker", type=Path, required=True)
    parser.add_argument("--receipt", type=Path)
    parser.add_argument("--self-test", action="store_true", help="use only the hand-built outcome-blind projection")
    args = parser.parse_args()
    if args.checker.is_symlink() or not args.checker.is_file():
        parser.error("checker must be a regular non-symlink file")
    if args.self_test:
        if args.corpus is not None or args.receipt is not None:
            parser.error("self-test accepts neither corpus nor receipt")
        result = exercise(hand_built_fixture(), args.checker, args.schema)
        print(json.dumps(result, sort_keys=True))
        if not result["ok"]:
            raise SystemExit(1)
        return
    if args.corpus is None or args.receipt is None:
        parser.error("execution mode requires --corpus and --receipt")
    if args.corpus.is_symlink() or not args.corpus.is_file():
        parser.error("corpus must be a regular non-symlink file")
    full = json.loads(args.corpus.read_text(encoding="utf-8"))
    result = exercise(projection(full), args.checker, args.schema)
    result.update({"corpus": str(args.corpus),
                   "corpus_sha256": sha(args.corpus.read_bytes()),
                   "checker": str(args.checker),
                   "checker_sha256": sha(args.checker.read_bytes())})
    if not result["ok"]:
        raise SystemExit(1)
    atomic_new(args.receipt, result)
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
