#!/usr/bin/env python3
"""Produce the frozen FD014 record-level context-corpus pilot.

This file intentionally shares no semantic module with the independent
checker.  The only executable acquisition boundary is ``--maximum-n 6``.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
import os
from pathlib import Path


VERSION = "HANKEL-CONTEXT-ASCII-V1"
SCHEMA_SHA256 = "b5bcb2f301c2d84560ef131c47166aa4eedc5079cca6bf8f2efc1bd5d1369df0"
CONTROL_SHA256 = "2a7a7930d4e68b0c9836076c0ec9f5573ba3af56cca577e6f17162d892f2a142"
BASE_REVISION = "e1751075e5632c93a7b406136ed5d93b6fbe919e"
PROFILE_FIELDS = [
    "cup_anchor_left", "cup_anchor_right", "cup_straddled",
    "cap_anchor_left", "cap_anchor_right", "cap_straddled",
    "contains_strong_five",
]
COUNT_LIMITS = {
    "compositions": 42396,
    "subtrees": 32055,
    "roots": 32054,
    "contexts": 25952,
    "coordinates": 175,
    "entries": 64108,
}
RECORD_LIMITS = {
    "subtree_records": 1024,
    "root_records": 1024,
    "context_records": 1024,
    "coordinate_records": 512,
    "substitution_entries": 1536,
    "external_controls": 65536,
}
TOP_LEVEL_LIMIT = 2_000_000
FILE_LIMIT = 192_847_488


def canonical(value: object) -> bytes:
    return json.dumps(
        value, ensure_ascii=True, separators=(",", ":"), sort_keys=True,
    ).encode("ascii")


def sha_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def record_id(preimage: str) -> str:
    return "sha256:" + sha_bytes(preimage.encode("ascii"))


def width_hex(value: int, bit_count: int) -> str:
    return f"{value:0{max(1, (bit_count + 3) // 4)}x}"


def triple_list(n: int) -> tuple[tuple[int, int, int], ...]:
    return tuple(itertools.combinations(range(n), 3))


def proper_masks(n: int):
    full = (1 << n) - 1
    for mask in range(1, full):
        yield mask


def crossing_word(n: int, lower_mask: int) -> int:
    answer = 0
    for position, (a, b, c) in enumerate(triple_list(n)):
        selected = (1 << a) | (1 << b) | (1 << c)
        count = (selected & lower_mask).bit_count()
        if 0 < count < 3 and lower_mask & (1 << b):
            answer |= 1 << position
    return answer


def embed_word(child_bits: int, child_vertices: tuple[int, ...], n: int) -> int:
    parent_positions = {triple: i for i, triple in enumerate(triple_list(n))}
    answer = 0
    for local_position, local_triple in enumerate(triple_list(len(child_vertices))):
        if child_bits & (1 << local_position):
            actual = tuple(child_vertices[i] for i in local_triple)
            answer |= 1 << parent_positions[actual]
    return answer


def restrict_word(parent_bits: int, vertices: tuple[int, ...], n: int) -> int:
    parent_positions = {triple: i for i, triple in enumerate(triple_list(n))}
    answer = 0
    for local_position, local_triple in enumerate(triple_list(len(vertices))):
        actual = tuple(vertices[i] for i in local_triple)
        if parent_bits & (1 << parent_positions[actual]):
            answer |= 1 << local_position
    return answer


def compose_word(n: int, lower_mask: int, lower_bits: int, upper_bits: int) -> int:
    lower = tuple(i for i in range(n) if lower_mask & (1 << i))
    upper = tuple(i for i in range(n) if not lower_mask & (1 << i))
    return (
        embed_word(lower_bits, lower, n)
        | embed_word(upper_bits, upper, n)
        | crossing_word(n, lower_mask)
    )


def strong_five(bits: int, n: int, vertices: tuple[int, ...]) -> bool:
    positions = {triple: i for i, triple in enumerate(triple_list(n))}
    for a, b, c, d in itertools.combinations(vertices, 4):
        abc = bool(bits & (1 << positions[(a, b, c)]))
        abd = bool(bits & (1 << positions[(a, b, d)]))
        acd = bool(bits & (1 << positions[(a, c, d)]))
        bcd = bool(bits & (1 << positions[(b, c, d)]))
        if abc != abd or acd != bcd:
            return False
    return True


def profile_table(bits: int, n: int, clip: int = 5) -> list[list[int]]:
    triples = triple_list(n)
    positions = {triple: i for i, triple in enumerate(triples)}
    rows = [[0] * 6 for _ in range(n + 1)]
    has_strong = False
    for size in range(1, min(clip, n) + 1):
        for chain in itertools.combinations(range(n), size):
            required = 0
            for triple in itertools.combinations(chain, 3):
                required |= 1 << positions[triple]
            cup = bits & required == required
            cap = bits & required == 0
            if size == 5:
                has_strong |= strong_five(bits, n, chain)
            if not cup and not cap:
                continue
            for gap in range(n + 1):
                relation = 0 if gap <= chain[0] else 1 if gap > chain[-1] else 2
                if cup:
                    rows[gap][relation] = max(rows[gap][relation], size)
                if cap:
                    rows[gap][3 + relation] = max(rows[gap][3 + relation], size)
    return [row + [int(has_strong)] for row in rows]


def enumerate_colorings(maximum_n: int):
    states: dict[int, tuple[int, ...]] = {1: (0,)}
    roots: list[tuple[int, int, int, int, int]] = []
    compositions = 0
    for n in range(2, maximum_n + 1):
        values: set[int] = set()
        layer_roots: set[tuple[int, int, int, int, int]] = set()
        for lower_mask in proper_masks(n):
            lower_n = lower_mask.bit_count()
            upper_n = n - lower_n
            for lower_bits in states[lower_n]:
                for upper_bits in states[upper_n]:
                    compositions += 1
                    if compositions > COUNT_LIMITS["compositions"]:
                        raise RuntimeError("COUNT_CEILING:compositions")
                    parent = compose_word(n, lower_mask, lower_bits, upper_bits)
                    values.add(parent)
                    layer_roots.add((n, lower_mask, parent, lower_bits, upper_bits))
        states[n] = tuple(sorted(values))
        roots.extend(sorted(layer_roots))
    return states, roots, compositions


def make_subtrees(states: dict[int, tuple[int, ...]]):
    records = []
    lookup = {}
    for n in sorted(states):
        bits_width = math.comb(n, 3)
        for bits in states[n]:
            coloring = width_hex(bits, bits_width)
            preimage = f"S|arity={n:02d}|coloring={coloring}"
            record = {
                "id": record_id(preimage),
                "identity_preimage": preimage,
                "arity": n,
                "coloring_hex": coloring,
                "profiles": profile_table(bits, n),
            }
            records.append(record)
            lookup[(n, bits)] = record
    records.sort(key=lambda row: row["identity_preimage"])
    return records, lookup


def make_roots(raw_roots, subtree_lookup):
    records = []
    payload = {}
    for n, lower_mask, parent_bits, lower_bits, upper_bits in raw_roots:
        lower = subtree_lookup[(lower_mask.bit_count(), lower_bits)]
        upper = subtree_lookup[(n - lower_mask.bit_count(), upper_bits)]
        parent = subtree_lookup[(n, parent_bits)]
        lower_hex = width_hex(lower_mask, n)
        preimage = (
            f"R|arity={n:02d}|lower={lower_hex}|lower_id={lower['id']}"
            f"|upper_id={upper['id']}"
        )
        record = {
            "id": record_id(preimage),
            "identity_preimage": preimage,
            "arity": n,
            "lower_mask_hex": lower_hex,
            "parent_subtree_id": parent["id"],
            "lower_subtree_id": lower["id"],
            "upper_subtree_id": upper["id"],
        }
        records.append(record)
        payload[record["id"]] = (lower_mask, lower, upper, parent)
    records.sort(key=lambda row: row["identity_preimage"])
    return records, payload


def make_contexts(root_records, root_payload):
    by_preimage = {}
    root_contexts = {}
    for root in root_records:
        lower_mask, lower, upper, _ = root_payload[root["id"]]
        n = root["arity"]
        lower_hex = width_hex(lower_mask, n)
        pairs = (
            ("lower", lower_mask, lower_mask.bit_count(), upper),
            ("upper", ((1 << n) - 1) ^ lower_mask, n - lower_mask.bit_count(), lower),
        )
        ids = {}
        for side, hole_mask, hole_n, sibling in pairs:
            preimage = (
                f"C|arity={n:02d}|lower={lower_hex}|hole_side={side}"
                f"|sibling_id={sibling['id']}"
            )
            record = {
                "id": record_id(preimage),
                "identity_preimage": preimage,
                "arity": n,
                "lower_mask_hex": lower_hex,
                "hole_side": side,
                "hole_mask_hex": width_hex(hole_mask, n),
                "hole_arity": hole_n,
                "sibling_subtree_id": sibling["id"],
            }
            previous = by_preimage.setdefault(preimage, record)
            if previous != record:
                raise RuntimeError("ID_COLLISION:context")
            ids[side] = record["id"]
        root_contexts[root["id"]] = ids
    records = sorted(by_preimage.values(), key=lambda row: row["identity_preimage"])
    return records, root_contexts


def make_coordinates(maximum_n: int):
    records = []
    for n in range(2, maximum_n + 1):
        for gap in range(n + 1):
            for field_index, field in enumerate(PROFILE_FIELDS):
                preimage = f"Q|arity={n:02d}|gap={gap:02d}|field={field_index}"
                records.append({
                    "id": record_id(preimage),
                    "identity_preimage": preimage,
                    "arity": n,
                    "gap": gap,
                    "field_index": field_index,
                    "field": field,
                })
    records.sort(key=lambda row: row["identity_preimage"])
    return records


def partition_roots(root_records, subtree_records):
    subtree_by_id = {row["id"]: row for row in subtree_records}
    withheld_parents = set()
    for n in sorted({row["arity"] for row in root_records}):
        parents = {
            row["parent_subtree_id"] for row in root_records if row["arity"] == n
        }
        ordered = sorted(parents, key=lambda item: subtree_by_id[item]["identity_preimage"])
        if len(ordered) >= 2:
            withheld_parents.update(ordered[::5])
    return {
        row["id"]: (
            "withheld_root" if row["parent_subtree_id"] in withheld_parents else "training"
        )
        for row in root_records
    }


def make_entries(root_records, root_payload, root_contexts, partitions):
    records = []
    for root in root_records:
        _, lower, upper, parent = root_payload[root["id"]]
        for side, child in (("lower", lower), ("upper", upper)):
            context_id = root_contexts[root["id"]][side]
            preimage = f"E|context_id={context_id}|child_id={child['id']}"
            records.append({
                "id": record_id(preimage),
                "identity_preimage": preimage,
                "root_id": root["id"],
                "context_id": context_id,
                "child_subtree_id": child["id"],
                "parent_subtree_id": parent["id"],
                "partition": partitions[root["id"]],
                "output_profiles": parent["profiles"],
            })
    records.sort(key=lambda row: row["identity_preimage"])
    if len({row["id"] for row in records}) != len(records):
        raise RuntimeError("ID_COLLISION:entry")
    return records


def make_split(root_records, entries, partitions):
    training_roots = sorted(row["id"] for row in root_records if partitions[row["id"]] == "training")
    withheld_roots = sorted(row["id"] for row in root_records if partitions[row["id"]] == "withheld_root")
    training_entries = sorted(row["id"] for row in entries if row["partition"] == "training")
    withheld_entries = sorted(row["id"] for row in entries if row["partition"] == "withheld_root")
    return {
        "rule_id": "PARENT-ID-MOD5-V1",
        "grouping_key": "arity plus parent_subtree_id; every root and both side entries for one parent stay together",
        "parent_order": "strict ASCII order of parent subtree identity_preimage within each arity",
        "eligible_layer_rule": "if an arity has at least two distinct rooted parents, zero-based parent indices congruent to 0 modulo 5 are withheld; a layer with fewer than two rooted parents is all training",
        "modulus": 5,
        "withheld_residue": 0,
        "training_root_ids": training_roots,
        "withheld_root_ids": withheld_roots,
        "training_entry_ids": training_entries,
        "withheld_entry_ids": withheld_entries,
    }


def make_external(source: dict, source_path: str):
    required = (
        "n", "k", "lower_mask_hex", "upper_mask_hex", "crossing_bits_hex",
        "profile_fields", "equal_upper_all_gap_profile", "first_difference", "left", "right",
    )
    if any(key not in source for key in required):
        raise RuntimeError("EXTERNAL_CONTROL:missing_field")
    answer = {
        "control_id": "K6N9-SINGLETON-COLLISION-V1",
        "role": "external_control_not_in_k5_train_or_holdout",
        "source_path": source_path,
        "source_sha256": CONTROL_SHA256,
    }
    answer.update({key: source[key] for key in required})
    return answer


def stream_hash(records) -> str:
    digest = hashlib.sha256()
    for record in records:
        digest.update(canonical(record) + b"\n")
    return digest.hexdigest()


def validate_limits(corpus, compositions: int) -> None:
    counts = corpus["counts"]
    actual = {
        "compositions": compositions,
        "subtrees": counts["subtrees"],
        "roots": counts["roots"],
        "contexts": counts["contexts"],
        "coordinates": counts["coordinates"],
        "entries": counts["entries"],
    }
    for name, value in actual.items():
        if value > COUNT_LIMITS[name]:
            raise RuntimeError(f"COUNT_CEILING:{name}")
    for stream, limit in RECORD_LIMITS.items():
        for record in corpus[stream]:
            if len(canonical(record) + b"\n") > limit:
                raise RuntimeError(f"RECORD_SIZE:{stream}")
    shell = dict(corpus)
    for key in (
        "subtree_records", "root_records", "context_records",
        "coordinate_records", "substitution_entries", "external_controls",
    ):
        shell[key] = []
    if len(canonical(shell) + b"\n") > TOP_LEVEL_LIMIT:
        raise RuntimeError("TOP_LEVEL_SIZE")
    if len(canonical(corpus) + b"\n") > FILE_LIMIT:
        raise RuntimeError("TOTAL_FILE_SIZE")


def build(maximum_n: int, schema_path: Path, control_path: Path) -> dict:
    if maximum_n != 6:
        raise ValueError("maximum-n must be exactly 6")
    if file_sha256(schema_path) != SCHEMA_SHA256:
        raise RuntimeError("INPUT_STOP:schema_hash")
    if file_sha256(control_path) != CONTROL_SHA256:
        raise RuntimeError("INPUT_STOP:external_control_hash")
    schema = json.loads(schema_path.read_text(encoding="utf-8"))
    if schema.get("title") != "FD014 record-level decomposable context corpus":
        raise RuntimeError("INPUT_STOP:schema_identity")
    external_source = json.loads(control_path.read_text(encoding="utf-8"))
    states, raw_roots, compositions = enumerate_colorings(maximum_n)
    subtrees, subtree_lookup = make_subtrees(states)
    roots, root_payload = make_roots(raw_roots, subtree_lookup)
    contexts, root_contexts = make_contexts(roots, root_payload)
    coordinates = make_coordinates(maximum_n)
    partitions = partition_roots(roots, subtrees)
    entries = make_entries(roots, root_payload, root_contexts, partitions)
    split = make_split(roots, entries, partitions)
    external = [make_external(external_source, str(control_path))]
    repo = Path(__file__).resolve().parent.parent
    checker_path = repo / "scripts/check_hankel_context_corpus.py"
    hashes = {
        "subtree_records_sha256": stream_hash(subtrees),
        "root_records_sha256": stream_hash(roots),
        "context_records_sha256": stream_hash(contexts),
        "coordinate_records_sha256": stream_hash(coordinates),
        "substitution_entries_sha256": stream_hash(entries),
        "split_sha256": stream_hash([split]),
        "external_controls_sha256": stream_hash(external),
    }
    semantic_text = "".join(
        f"{name}={hashes[key]}\n"
        for name, key in (
            ("subtree", "subtree_records_sha256"),
            ("root", "root_records_sha256"),
            ("context", "context_records_sha256"),
            ("coordinate", "coordinate_records_sha256"),
            ("entry", "substitution_entries_sha256"),
            ("split", "split_sha256"),
            ("external_control", "external_controls_sha256"),
        )
    ).encode("ascii")
    hashes["corpus_semantic_sha256"] = sha_bytes(semantic_text)
    counts = {
        "subtrees": len(subtrees), "roots": len(roots), "contexts": len(contexts),
        "coordinates": len(coordinates), "entries": len(entries),
        "training_roots": len(split["training_root_ids"]),
        "withheld_roots": len(split["withheld_root_ids"]),
        "training_entries": len(split["training_entry_ids"]),
        "withheld_entries": len(split["withheld_entry_ids"]),
        "external_controls": 1,
    }
    corpus = {
        "schema_version": 1,
        "corpus_id": "FD014-HANKEL-CONTEXT-CORPUS-PILOT-V1",
        "scope": {
            "model": "recursively_decomposable_triple_colorings", "k": 5,
            "profile_clip": 5, "minimum_n": 1, "maximum_n": maximum_n,
            "exact": True,
            "root_scope": "every distinct coloring and every compatible ordered lower/upper root",
            "context_scope": "both one-step typed hole sides of every compatible root; arbitrary outer contexts are finite compositions of these frames",
        },
        "provenance": {
            "generation_base_revision": BASE_REVISION,
            "schema_path": str(schema_path), "schema_sha256": SCHEMA_SHA256,
            "producer_path": "scripts/produce_hankel_context_corpus.py",
            "producer_sha256": file_sha256(Path(__file__).resolve()),
            "checker_path": "scripts/check_hankel_context_corpus.py",
            "checker_sha256": file_sha256(checker_path),
            "external_control_path": str(control_path),
            "external_control_sha256": CONTROL_SHA256,
        },
        "canonicalization": {
            "version": VERSION,
            "id_algorithm": "sha256:<lowercase hex SHA-256 of the UTF-8 identity_preimage bytes>",
            "record_order": "strict ascending ASCII identity_preimage; duplicate IDs or preimages forbidden",
            "stream_encoding": "UTF-8 compact canonical JSON record plus LF: recursively ASCII-sort object keys, preserve array order, emit no whitespace, decimal integers, lowercase true/false, and shortest JSON string escapes",
        },
        "profile_spec": {
            "fields": PROFILE_FIELDS,
            "gap_order": "gap 0 through gap arity, inclusive",
            "field_semantics": "first six fields are exact maximum monochromatic chain lengths clipped at 5 in left/right/straddled anchor relation; final field is the exact 0/1 existence bit for a strong five-set",
        },
        "subtree_records": subtrees, "root_records": roots,
        "context_records": contexts, "coordinate_records": coordinates,
        "substitution_entries": entries, "split": split,
        "external_controls": external, "counts": counts, "stream_hashes": hashes,
    }
    validate_limits(corpus, compositions)
    return corpus


def atomic_write_new(path: Path, payload: bytes) -> None:
    if path.is_symlink() or path.exists() or path.parent.is_symlink() or path.parent.exists():
        raise RuntimeError("INPUT_STOP:output_or_namespace_exists")
    path.parent.mkdir(mode=0o700, parents=True, exist_ok=False)
    temporary = path.parent / ("." + path.name + ".tmp")
    try:
        with temporary.open("xb") as handle:
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())
        if len(payload) > FILE_LIMIT:
            raise RuntimeError("TOTAL_FILE_SIZE")
        os.replace(temporary, path)
        directory_fd = os.open(path.parent, os.O_RDONLY)
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)
    except BaseException:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass
        raise


def main() -> None:
    parser = argparse.ArgumentParser(description="Produce the exact n<=6 FD014 context corpus.")
    parser.add_argument("--maximum-n", type=int, required=True)
    parser.add_argument("--schema", type=Path, required=True)
    parser.add_argument("--external-control", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.maximum_n != 6:
        parser.error("maximum-n must be exactly 6; no other boundary is reachable")
    corpus = build(args.maximum_n, args.schema, args.external_control)
    payload = canonical(corpus) + b"\n"
    atomic_write_new(args.output, payload)
    print(json.dumps({"output": str(args.output), "bytes": len(payload)}, sort_keys=True))


if __name__ == "__main__":
    main()
