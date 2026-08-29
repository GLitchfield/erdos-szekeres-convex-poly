#!/usr/bin/env python3
"""Independent checker for the FD014 record-level context corpus.

The normal path reconstructs the recurrence and every semantic record without
importing the producer or any shared semantic helper.  ``--projection-only``
is reserved for outcome-blind, already-self-contained hostile fixtures.
"""

from __future__ import annotations

import argparse
import functools
import hashlib
import itertools
import json
import math
import os
from pathlib import Path


SCHEMA_SHA256 = "b5bcb2f301c2d84560ef131c47166aa4eedc5079cca6bf8f2efc1bd5d1369df0"
CONTROL_SHA256 = "2a7a7930d4e68b0c9836076c0ec9f5573ba3af56cca577e6f17162d892f2a142"
BASE_REVISION = "e1751075e5632c93a7b406136ed5d93b6fbe919e"
FIELDS = [
    "cup_anchor_left", "cup_anchor_right", "cup_straddled",
    "cap_anchor_left", "cap_anchor_right", "cap_straddled",
    "contains_strong_five",
]
LIMITS = {
    "subtree_records": (32055, 1024),
    "root_records": (32054, 1024),
    "context_records": (25952, 1024),
    "coordinate_records": (175, 512),
    "substitution_entries": (64108, 1536),
    "external_controls": (1, 65536),
}
FILE_LIMIT = 192_847_488
RECEIPT_LIMIT = 1_000_000


class CorpusError(Exception):
    def __init__(self, diagnostic: str, detail: str = ""):
        super().__init__(diagnostic + (":" + detail if detail else ""))
        self.diagnostic = diagnostic
        self.detail = detail


def reject(diagnostic: str, detail: str = "") -> None:
    raise CorpusError(diagnostic, detail)


def compact(value: object) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("ascii")


def digest_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def digest_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as source:
        while True:
            block = source.read(1 << 20)
            if not block:
                return h.hexdigest()
            h.update(block)


def identity(preimage: str) -> str:
    return "sha256:" + digest_bytes(preimage.encode("ascii"))


def encoded_hex(value: int, bits: int) -> str:
    return f"{value:0{max(1, (bits + 3) // 4)}x}"


@functools.cache
def triples(n: int) -> tuple[tuple[int, int, int], ...]:
    return tuple(itertools.combinations(range(n), 3))


def internal_masks(n: int):
    for mask in range(1, (1 << n) - 1):
        yield mask


@functools.cache
def cross_bits(n: int, lower: int) -> int:
    result = 0
    for index, (a, b, c) in enumerate(triples(n)):
        chosen = (1 << a) | (1 << b) | (1 << c)
        if 0 < (chosen & lower).bit_count() < 3 and lower & (1 << b):
            result |= 1 << index
    return result


def place_local(local_bits: int, vertices: tuple[int, ...], parent_n: int) -> int:
    index = {triple: position for position, triple in enumerate(triples(parent_n))}
    result = 0
    for position, local in enumerate(triples(len(vertices))):
        if local_bits >> position & 1:
            actual = tuple(vertices[i] for i in local)
            result |= 1 << index[actual]
    return result


def take_restriction(parent_bits: int, parent_n: int, vertices: tuple[int, ...]) -> int:
    index = {triple: position for position, triple in enumerate(triples(parent_n))}
    result = 0
    for position, local in enumerate(triples(len(vertices))):
        actual = tuple(vertices[i] for i in local)
        if parent_bits >> index[actual] & 1:
            result |= 1 << position
    return result


def join(n: int, lower_mask: int, lower_bits: int, upper_bits: int) -> int:
    low_vertices = tuple(i for i in range(n) if lower_mask >> i & 1)
    high_vertices = tuple(i for i in range(n) if not (lower_mask >> i & 1))
    return (
        place_local(lower_bits, low_vertices, n)
        | place_local(upper_bits, high_vertices, n)
        | cross_bits(n, lower_mask)
    )


@functools.cache
def semantic_colorings(n: int) -> frozenset[int]:
    if n == 1:
        return frozenset((0,))
    result = set()
    for lower in internal_masks(n):
        low_n = lower.bit_count()
        high_n = n - low_n
        for low in semantic_colorings(low_n):
            for high in semantic_colorings(high_n):
                result.add(join(n, lower, low, high))
    return frozenset(result)


def is_strong(bits: int, n: int, vertices: tuple[int, ...]) -> bool:
    index = {triple: position for position, triple in enumerate(triples(n))}
    for a, b, c, d in itertools.combinations(vertices, 4):
        if bool(bits >> index[(a, b, c)] & 1) != bool(bits >> index[(a, b, d)] & 1):
            return False
        if bool(bits >> index[(a, c, d)] & 1) != bool(bits >> index[(b, c, d)] & 1):
            return False
    return True


def inspect_profiles(bits: int, n: int, clip: int = 5) -> list[list[int]]:
    index = {triple: position for position, triple in enumerate(triples(n))}
    table = [[0, 0, 0, 0, 0, 0] for _ in range(n + 1)]
    strong = False
    for size in range(1, min(n, clip) + 1):
        for vertices in itertools.combinations(range(n), size):
            needed = 0
            for triple in itertools.combinations(vertices, 3):
                needed |= 1 << index[triple]
            cup = bits & needed == needed
            cap = bits & needed == 0
            if size == 5:
                strong = strong or is_strong(bits, n, vertices)
            for gap in range(n + 1):
                relation = 0 if gap <= vertices[0] else 1 if gap > vertices[-1] else 2
                if cup:
                    table[gap][relation] = max(table[gap][relation], size)
                if cap:
                    table[gap][relation + 3] = max(table[gap][relation + 3], size)
    return [row + [int(strong)] for row in table]


def expected_records(maximum_n: int):
    subtree_records = []
    subtree = {}
    for n in range(1, maximum_n + 1):
        for bits in sorted(semantic_colorings(n)):
            coloring = encoded_hex(bits, math.comb(n, 3))
            preimage = f"S|arity={n:02d}|coloring={coloring}"
            row = {
                "id": identity(preimage), "identity_preimage": preimage,
                "arity": n, "coloring_hex": coloring,
                "profiles": inspect_profiles(bits, n),
            }
            subtree_records.append(row)
            subtree[(n, bits)] = row
    subtree_records.sort(key=lambda row: row["identity_preimage"])

    root_records = []
    root_payload = {}
    for n in range(2, maximum_n + 1):
        for parent_bits in sorted(semantic_colorings(n)):
            for lower in internal_masks(n):
                low_vertices = tuple(i for i in range(n) if lower >> i & 1)
                high_vertices = tuple(i for i in range(n) if not (lower >> i & 1))
                low_bits = take_restriction(parent_bits, n, low_vertices)
                high_bits = take_restriction(parent_bits, n, high_vertices)
                if low_bits not in semantic_colorings(len(low_vertices)):
                    continue
                if high_bits not in semantic_colorings(len(high_vertices)):
                    continue
                if join(n, lower, low_bits, high_bits) != parent_bits:
                    continue
                low_row = subtree[(len(low_vertices), low_bits)]
                high_row = subtree[(len(high_vertices), high_bits)]
                parent_row = subtree[(n, parent_bits)]
                lower_hex = encoded_hex(lower, n)
                preimage = (
                    f"R|arity={n:02d}|lower={lower_hex}|lower_id={low_row['id']}"
                    f"|upper_id={high_row['id']}"
                )
                row = {
                    "id": identity(preimage), "identity_preimage": preimage,
                    "arity": n, "lower_mask_hex": lower_hex,
                    "parent_subtree_id": parent_row["id"],
                    "lower_subtree_id": low_row["id"],
                    "upper_subtree_id": high_row["id"],
                }
                root_records.append(row)
                root_payload[row["id"]] = (lower, low_row, high_row, parent_row)
    root_records.sort(key=lambda row: row["identity_preimage"])

    context_by_preimage = {}
    contexts_for_root = {}
    for root in root_records:
        lower, low_row, high_row, _ = root_payload[root["id"]]
        n = root["arity"]
        descriptions = (
            ("lower", lower, low_row["arity"], high_row),
            ("upper", ((1 << n) - 1) ^ lower, high_row["arity"], low_row),
        )
        side_map = {}
        for side, hole, hole_n, sibling in descriptions:
            preimage = (
                f"C|arity={n:02d}|lower={encoded_hex(lower, n)}|hole_side={side}"
                f"|sibling_id={sibling['id']}"
            )
            row = {
                "id": identity(preimage), "identity_preimage": preimage,
                "arity": n, "lower_mask_hex": encoded_hex(lower, n),
                "hole_side": side, "hole_mask_hex": encoded_hex(hole, n),
                "hole_arity": hole_n, "sibling_subtree_id": sibling["id"],
            }
            if preimage in context_by_preimage and context_by_preimage[preimage] != row:
                reject("ID_COLLISION", "expected_context")
            context_by_preimage[preimage] = row
            side_map[side] = row["id"]
        contexts_for_root[root["id"]] = side_map
    context_records = sorted(context_by_preimage.values(), key=lambda row: row["identity_preimage"])

    coordinate_records = []
    for n in range(2, maximum_n + 1):
        for gap in range(n + 1):
            for position, field in enumerate(FIELDS):
                preimage = f"Q|arity={n:02d}|gap={gap:02d}|field={position}"
                coordinate_records.append({
                    "id": identity(preimage), "identity_preimage": preimage,
                    "arity": n, "gap": gap, "field_index": position, "field": field,
                })
    coordinate_records.sort(key=lambda row: row["identity_preimage"])

    subtree_by_id = {row["id"]: row for row in subtree_records}
    withheld_parents = set()
    for n in range(2, maximum_n + 1):
        parents = {row["parent_subtree_id"] for row in root_records if row["arity"] == n}
        ordered = sorted(parents, key=lambda value: subtree_by_id[value]["identity_preimage"])
        if len(ordered) >= 2:
            withheld_parents.update(ordered[::5])
    root_partition = {
        row["id"]: ("withheld_root" if row["parent_subtree_id"] in withheld_parents else "training")
        for row in root_records
    }
    entries = []
    for root in root_records:
        _, low_row, high_row, parent_row = root_payload[root["id"]]
        for side, child in (("lower", low_row), ("upper", high_row)):
            context_id = contexts_for_root[root["id"]][side]
            preimage = f"E|context_id={context_id}|child_id={child['id']}"
            entries.append({
                "id": identity(preimage), "identity_preimage": preimage,
                "root_id": root["id"], "context_id": context_id,
                "child_subtree_id": child["id"],
                "parent_subtree_id": parent_row["id"],
                "partition": root_partition[root["id"]],
                "output_profiles": parent_row["profiles"],
            })
    entries.sort(key=lambda row: row["identity_preimage"])
    split = {
        "rule_id": "PARENT-ID-MOD5-V1",
        "grouping_key": "arity plus parent_subtree_id; every root and both side entries for one parent stay together",
        "parent_order": "strict ASCII order of parent subtree identity_preimage within each arity",
        "eligible_layer_rule": "if an arity has at least two distinct rooted parents, zero-based parent indices congruent to 0 modulo 5 are withheld; a layer with fewer than two rooted parents is all training",
        "modulus": 5, "withheld_residue": 0,
        "training_root_ids": sorted(key for key, value in root_partition.items() if value == "training"),
        "withheld_root_ids": sorted(key for key, value in root_partition.items() if value == "withheld_root"),
        "training_entry_ids": sorted(row["id"] for row in entries if row["partition"] == "training"),
        "withheld_entry_ids": sorted(row["id"] for row in entries if row["partition"] == "withheld_root"),
    }
    return {
        "subtree_records": subtree_records, "root_records": root_records,
        "context_records": context_records, "coordinate_records": coordinate_records,
        "substitution_entries": entries, "split": split,
    }


def stream_hash(records) -> str:
    h = hashlib.sha256()
    for row in records:
        h.update(compact(row) + b"\n")
    return h.hexdigest()


def expected_hashes(corpus: dict) -> dict:
    hashes = {
        "subtree_records_sha256": stream_hash(corpus["subtree_records"]),
        "root_records_sha256": stream_hash(corpus["root_records"]),
        "context_records_sha256": stream_hash(corpus["context_records"]),
        "coordinate_records_sha256": stream_hash(corpus["coordinate_records"]),
        "substitution_entries_sha256": stream_hash(corpus["substitution_entries"]),
        "split_sha256": stream_hash([corpus["split"]]),
        "external_controls_sha256": stream_hash(corpus["external_controls"]),
    }
    text = "".join(
        f"{label}={hashes[key]}\n" for label, key in (
            ("subtree", "subtree_records_sha256"), ("root", "root_records_sha256"),
            ("context", "context_records_sha256"), ("coordinate", "coordinate_records_sha256"),
            ("entry", "substitution_entries_sha256"), ("split", "split_sha256"),
            ("external_control", "external_controls_sha256"),
        )
    ).encode("ascii")
    hashes["corpus_semantic_sha256"] = digest_bytes(text)
    return hashes


def ordered_identity_stream(name: str, rows: list) -> None:
    preimages = []
    ids = []
    for row in rows:
        if not isinstance(row, dict) or not isinstance(row.get("identity_preimage"), str):
            reject("SCHEMA", name + ".identity_preimage")
        if row.get("id") != identity(row["identity_preimage"]):
            reject("ID_COLLISION", name)
        preimages.append(row["identity_preimage"])
        ids.append(row["id"])
    if preimages != sorted(preimages) or len(set(preimages)) != len(preimages):
        reject("DUPLICATION", name + ".preimage_order")
    if len(set(ids)) != len(ids):
        reject("DUPLICATION", name + ".id")


def validate_structure(corpus: dict, projection: bool) -> None:
    required = {
        "schema_version", "corpus_id", "scope", "provenance", "canonicalization",
        "profile_spec", "subtree_records", "root_records", "context_records",
        "coordinate_records", "substitution_entries", "split", "external_controls",
        "counts", "stream_hashes",
    }
    if not isinstance(corpus, dict) or set(corpus) != required or corpus.get("schema_version") != 1:
        reject("SCHEMA", "top_level")
    expected_scope = {
        "model": "recursively_decomposable_triple_colorings", "k": 5,
        "profile_clip": 5, "minimum_n": 1, "exact": True,
        "root_scope": "every distinct coloring and every compatible ordered lower/upper root",
        "context_scope": "both one-step typed hole sides of every compatible root; arbitrary outer contexts are finite compositions of these frames",
    }
    scope = corpus.get("scope", {})
    if any(scope.get(key) != value for key, value in expected_scope.items()):
        reject("SCHEMA", "scope")
    expected_canonicalization = {
        "version": "HANKEL-CONTEXT-ASCII-V1",
        "id_algorithm": "sha256:<lowercase hex SHA-256 of the UTF-8 identity_preimage bytes>",
        "record_order": "strict ascending ASCII identity_preimage; duplicate IDs or preimages forbidden",
        "stream_encoding": "UTF-8 compact canonical JSON record plus LF: recursively ASCII-sort object keys, preserve array order, emit no whitespace, decimal integers, lowercase true/false, and shortest JSON string escapes",
    }
    if corpus.get("canonicalization") != expected_canonicalization:
        reject("SCHEMA", "canonicalization")
    expected_profile = {
        "fields": FIELDS, "gap_order": "gap 0 through gap arity, inclusive",
        "field_semantics": "first six fields are exact maximum monochromatic chain lengths clipped at 5 in left/right/straddled anchor relation; final field is the exact 0/1 existence bit for a strong five-set",
    }
    if corpus.get("profile_spec") != expected_profile:
        reject("SCHEMA", "profile_spec")
    maximum_n = corpus.get("scope", {}).get("maximum_n")
    if not isinstance(maximum_n, int) or maximum_n < 2 or maximum_n > (3 if projection else 6):
        reject("SCHEMA", "maximum_n")
    for name, (count_limit, byte_limit) in LIMITS.items():
        rows = corpus.get(name)
        if not isinstance(rows, list) or len(rows) > count_limit:
            reject("SCHEMA", name + ".count")
        for row in rows:
            if len(compact(row) + b"\n") > byte_limit:
                reject("SCHEMA", name + ".record_size")
    for name in (
        "subtree_records", "root_records", "context_records",
        "coordinate_records", "substitution_entries",
    ):
        ordered_identity_stream(name, corpus[name])
    subtrees = {row["id"]: row for row in corpus["subtree_records"]}
    roots = {row["id"]: row for row in corpus["root_records"]}
    contexts = {row["id"]: row for row in corpus["context_records"]}
    entries = {row["id"]: row for row in corpus["substitution_entries"]}
    for root in roots.values():
        if any(root.get(key) not in subtrees for key in (
            "parent_subtree_id", "lower_subtree_id", "upper_subtree_id",
        )):
            reject("ROOT_INCOMPATIBLE", "reference")
        n = root.get("arity")
        try:
            lower = int(root.get("lower_mask_hex"), 16)
        except (TypeError, ValueError):
            reject("ROOT_INCOMPATIBLE", "mask")
        if not isinstance(n, int) or lower <= 0 or lower >= (1 << n) - 1:
            reject("ROOT_INCOMPATIBLE", "mask_range")
    for context in contexts.values():
        side = context.get("hole_side")
        n = context.get("arity")
        try:
            lower = int(context.get("lower_mask_hex"), 16)
            hole = int(context.get("hole_mask_hex"), 16)
        except (TypeError, ValueError):
            reject("WRONG_HOLE_TYPE", "mask")
        expected = lower if side == "lower" else ((1 << n) - 1) ^ lower if side == "upper" else None
        if expected is None or hole != expected or context.get("hole_arity") != hole.bit_count():
            reject("WRONG_HOLE_TYPE", context.get("id", ""))
        if context.get("sibling_subtree_id") not in subtrees:
            reject("WRONG_HOLE_TYPE", "sibling")
    roots_to_entries = {key: [] for key in roots}
    for entry in entries.values():
        root = roots.get(entry.get("root_id"))
        context = contexts.get(entry.get("context_id"))
        child = subtrees.get(entry.get("child_subtree_id"))
        parent = subtrees.get(entry.get("parent_subtree_id"))
        if root is None or context is None or child is None:
            reject("OMISSION", "entry_reference")
        if parent is None or parent["id"] != root["parent_subtree_id"]:
            reject("STALE_PARENT", entry.get("id", ""))
        expected_child = root["lower_subtree_id"] if context["hole_side"] == "lower" else root["upper_subtree_id"]
        expected_sibling = root["upper_subtree_id"] if context["hole_side"] == "lower" else root["lower_subtree_id"]
        if child["id"] != expected_child or context["sibling_subtree_id"] != expected_sibling:
            reject("ROOT_INCOMPATIBLE", "entry_fill")
        if entry.get("output_profiles") != parent.get("profiles"):
            reject("OUTPUT_BIT_FLIP", entry.get("id", ""))
        roots_to_entries[root["id"]].append(entry)
    if any(len(rows) != 2 for rows in roots_to_entries.values()):
        reject("OMISSION", "two_entries_per_root")
    split = corpus["split"]
    split_constants = {
        "rule_id": "PARENT-ID-MOD5-V1",
        "grouping_key": "arity plus parent_subtree_id; every root and both side entries for one parent stay together",
        "parent_order": "strict ASCII order of parent subtree identity_preimage within each arity",
        "eligible_layer_rule": "if an arity has at least two distinct rooted parents, zero-based parent indices congruent to 0 modulo 5 are withheld; a layer with fewer than two rooted parents is all training",
        "modulus": 5, "withheld_residue": 0,
    }
    if any(split.get(key) != value for key, value in split_constants.items()):
        reject("SPLIT_LEAKAGE", "rule")
    train_r = split.get("training_root_ids")
    hold_r = split.get("withheld_root_ids")
    train_e = split.get("training_entry_ids")
    hold_e = split.get("withheld_entry_ids")
    if not all(isinstance(value, list) for value in (train_r, hold_r, train_e, hold_e)):
        reject("SPLIT_LEAKAGE", "lists")
    if set(train_r) & set(hold_r) or set(train_e) & set(hold_e):
        reject("SPLIT_LEAKAGE", "intersection")
    if set(train_r) | set(hold_r) != set(roots) or set(train_e) | set(hold_e) != set(entries):
        reject("SPLIT_LEAKAGE", "coverage")
    for entry in entries.values():
        expected_partition = "training" if entry["id"] in set(train_e) else "withheld_root"
        if entry.get("partition") != expected_partition:
            reject("SPLIT_LEAKAGE", "entry_label")
        if (entry["root_id"] in set(train_r)) != (entry["id"] in set(train_e)):
            reject("SPLIT_LEAKAGE", "root_entry_group")
    expected_counts = {
        "subtrees": len(subtrees), "roots": len(roots), "contexts": len(contexts),
        "coordinates": len(corpus["coordinate_records"]), "entries": len(entries),
        "training_roots": len(train_r), "withheld_roots": len(hold_r),
        "training_entries": len(train_e), "withheld_entries": len(hold_e),
        "external_controls": len(corpus["external_controls"]),
    }
    if corpus.get("counts") != expected_counts:
        reject("OMISSION", "counts")
    if corpus.get("stream_hashes") != expected_hashes(corpus):
        reject("OMISSION", "stream_hash")
    if len(corpus["external_controls"]) != 1:
        reject("EXTERNAL_CONTROL_MUTATION", "count")
    control = corpus["external_controls"][0]
    if control.get("control_id") != "K6N9-SINGLETON-COLLISION-V1" or control.get("role") != "external_control_not_in_k5_train_or_holdout":
        reject("EXTERNAL_CONTROL_MUTATION", "identity")


def diagnose_single_mutation(baseline: dict, changed: dict) -> str:
    if len(changed.get("substitution_entries", [])) == len(baseline["substitution_entries"]) - 1:
        return "OMISSION"
    if len(changed.get("root_records", [])) == len(baseline["root_records"]) + 1:
        return "DUPLICATION"
    for stream in ("subtree_records", "root_records", "context_records", "coordinate_records", "substitution_entries"):
        a = baseline.get(stream, [])
        b = changed.get(stream, [])
        if len(a) != len(b):
            continue
        for old, new in zip(a, b):
            if old == new:
                continue
            differing = {key for key in set(old) | set(new) if old.get(key) != new.get(key)}
            if "id" in differing and new.get("id") in {row.get("id") for row in b if row is not new}:
                return "ID_COLLISION"
            if stream == "root_records" and "lower_mask_hex" in differing:
                return "ROOT_INCOMPATIBLE"
            if stream == "context_records" and "hole_side" in differing:
                return "WRONG_HOLE_TYPE"
            if stream == "substitution_entries" and "parent_subtree_id" in differing:
                return "STALE_PARENT"
            if stream == "substitution_entries" and "output_profiles" in differing:
                return "OUTPUT_BIT_FLIP"
    if baseline.get("split") != changed.get("split"):
        return "SPLIT_LEAKAGE"
    if baseline.get("external_controls") != changed.get("external_controls"):
        return "EXTERNAL_CONTROL_MUTATION"
    return "PROJECTION_MUTATION_UNCLASSIFIED"


def global_crossing(n: int, parent_mask: int, lower_mask: int) -> int:
    result = 0
    for index, (a, b, c) in enumerate(triples(n)):
        selected = (1 << a) | (1 << b) | (1 << c)
        if selected & parent_mask != selected:
            continue
        if 0 < (selected & lower_mask).bit_count() < 3 and lower_mask >> b & 1:
            result |= 1 << index
    return result


def tree_coloring(tree, n: int):
    if isinstance(tree, int):
        if tree < 0 or tree >= n:
            reject("EXTERNAL_CONTROL_MUTATION", "leaf")
        return 1 << tree, 0
    if not isinstance(tree, dict) or set(tree) != {"lower", "upper"}:
        reject("EXTERNAL_CONTROL_MUTATION", "tree")
    lower_mask, lower_bits = tree_coloring(tree["lower"], n)
    upper_mask, upper_bits = tree_coloring(tree["upper"], n)
    if lower_mask & upper_mask:
        reject("EXTERNAL_CONTROL_MUTATION", "duplicate_leaf")
    full = lower_mask | upper_mask
    return full, lower_bits | upper_bits | global_crossing(n, full, lower_mask)


def global_profile(bits: int, mask: int, n: int, k: int):
    index = {triple: position for position, triple in enumerate(triples(n))}
    vertices = tuple(i for i in range(n) if mask >> i & 1)
    rows = [[0] * 6 for _ in range(n + 1)]
    strong = False
    for size in range(1, min(k, len(vertices)) + 1):
        for chain in itertools.combinations(vertices, size):
            needed = 0
            for triple in itertools.combinations(chain, 3):
                needed |= 1 << index[triple]
            cup = bits & needed == needed
            cap = bits & needed == 0
            if size == k:
                strong = strong or is_strong_global(bits, n, chain)
            for gap in range(n + 1):
                relation = 0 if gap <= chain[0] else 1 if gap > chain[-1] else 2
                if cup:
                    rows[gap][relation] = max(rows[gap][relation], size)
                if cap:
                    rows[gap][relation + 3] = max(rows[gap][relation + 3], size)
    return [row + [int(strong)] for row in rows]


def is_strong_global(bits: int, n: int, chain: tuple[int, ...]) -> bool:
    index = {triple: position for position, triple in enumerate(triples(n))}
    for a, b, c, d in itertools.combinations(chain, 4):
        if bool(bits >> index[(a, b, c)] & 1) != bool(bits >> index[(a, b, d)] & 1):
            return False
        if bool(bits >> index[(a, c, d)] & 1) != bool(bits >> index[(b, c, d)] & 1):
            return False
    return True


def validate_external(control: dict, source: dict) -> None:
    copied = {
        "control_id": "K6N9-SINGLETON-COLLISION-V1",
        "role": "external_control_not_in_k5_train_or_holdout",
        "source_path": "data/derived/e3-context-k6-n9-singleton-collision.json",
        "source_sha256": CONTROL_SHA256,
    }
    for key in (
        "n", "k", "lower_mask_hex", "upper_mask_hex", "crossing_bits_hex",
        "profile_fields", "equal_upper_all_gap_profile", "first_difference", "left", "right",
    ):
        copied[key] = source[key]
    if control != copied:
        reject("EXTERNAL_CONTROL_MUTATION", "source_copy")
    n = 9
    lower = int(control["lower_mask_hex"], 16)
    upper = int(control["upper_mask_hex"], 16)
    if lower != 2 or upper != ((1 << n) - 1) ^ lower:
        reject("EXTERNAL_CONTROL_MUTATION", "masks")
    upper_profiles = []
    parent_profiles = []
    for side in ("left", "right"):
        witness = control[side]
        mask, upper_bits = tree_coloring(witness["upper_tree"], n)
        if mask != upper or upper_bits != int(witness["upper_coloring_hex"], 16):
            reject("EXTERNAL_CONTROL_MUTATION", side + ".upper")
        parent_bits = upper_bits | global_crossing(n, (1 << n) - 1, lower)
        if parent_bits != int(witness["parent_coloring_hex"], 16):
            reject("EXTERNAL_CONTROL_MUTATION", side + ".parent")
        upper_profiles.append(global_profile(upper_bits, upper, n, 6))
        parent_profiles.append(global_profile(parent_bits, (1 << n) - 1, n, 6))
        if parent_profiles[-1] != witness["parent_profile"]:
            reject("EXTERNAL_CONTROL_MUTATION", side + ".profile")
    if upper_profiles[0] != upper_profiles[1] or upper_profiles[0] != control["equal_upper_all_gap_profile"]:
        reject("EXTERNAL_CONTROL_MUTATION", "upper_profile")
    if parent_profiles[0] == parent_profiles[1]:
        reject("EXTERNAL_CONTROL_MUTATION", "no_difference")
    first = None
    for gap, (left, right) in enumerate(zip(parent_profiles[0], parent_profiles[1])):
        if left != right:
            positions = [i for i, pair in enumerate(zip(left, right)) if pair[0] != pair[1]]
            field_names = [control["profile_fields"][i] for i in positions]
            first = {"gap": gap, "fields": field_names, "left": left, "right": right}
            break
    if first != control["first_difference"] or first["gap"] != 6 or first["fields"] != ["cap_anchor_right"]:
        reject("EXTERNAL_CONTROL_MUTATION", "first_difference")


def normal_check(corpus: dict, corpus_path: Path, schema_path: Path) -> dict:
    validate_structure(corpus, projection=False)
    if corpus_path.stat().st_size > FILE_LIMIT:
        reject("SCHEMA", "file_size")
    if digest_file(schema_path) != SCHEMA_SHA256:
        reject("INPUT_STOP", "schema_hash")
    provenance = corpus["provenance"]
    repo = Path(__file__).resolve().parent.parent
    expected_sources = {
        "generation_base_revision": BASE_REVISION,
        "schema_path": "runs/agents/20260827-post-fin13-slate-acquisition/results/hankel-context-corpus-contract-audit-v1/corpus-schema.json",
        "schema_sha256": SCHEMA_SHA256,
        "producer_path": "scripts/produce_hankel_context_corpus.py",
        "checker_path": "scripts/check_hankel_context_corpus.py",
        "external_control_path": "data/derived/e3-context-k6-n9-singleton-collision.json",
        "external_control_sha256": CONTROL_SHA256,
    }
    for key, value in expected_sources.items():
        if provenance.get(key) != value:
            reject("INPUT_STOP", "provenance." + key)
    if provenance.get("producer_sha256") != digest_file(repo / provenance["producer_path"]):
        reject("INPUT_STOP", "producer_hash")
    if provenance.get("checker_sha256") != digest_file(Path(__file__).resolve()):
        reject("INPUT_STOP", "checker_hash")
    control_path = repo / provenance["external_control_path"]
    if digest_file(control_path) != CONTROL_SHA256:
        reject("INPUT_STOP", "external_hash")
    if corpus["scope"].get("maximum_n") != 6:
        reject("INPUT_STOP", "maximum_n")
    expected = expected_records(6)
    for key in ("subtree_records", "root_records", "context_records", "coordinate_records", "substitution_entries", "split"):
        if corpus[key] != expected[key]:
            reject("SCHEMA", "independent_replay." + key)
    source = json.loads(control_path.read_text(encoding="utf-8"))
    validate_external(corpus["external_controls"][0], source)
    return {
        "schema": True, "source_hashes": True, "independent_recurrence": True,
        "records": True, "profiles": True, "split": True,
        "external_control": True, "counts_and_stream_hashes": True,
    }


def atomic_receipt(path: Path, value: dict) -> None:
    if path.exists() or path.is_symlink():
        reject("INPUT_STOP", "receipt_exists")
    temporary = path.with_name("." + path.name + ".tmp")
    if temporary.exists() or temporary.is_symlink():
        reject("INPUT_STOP", "receipt_temp_exists")
    payload = json.dumps(value, sort_keys=True, separators=(",", ":")).encode("ascii") + b"\n"
    if len(payload) > RECEIPT_LIMIT:
        reject("SCHEMA", "receipt_size")
    with temporary.open("xb") as handle:
        handle.write(payload)
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(temporary, path)


def main() -> None:
    parser = argparse.ArgumentParser(description="Independently verify the FD014 context corpus.")
    parser.add_argument("--schema", type=Path, required=True)
    parser.add_argument("--corpus", type=Path, required=True)
    parser.add_argument("--receipt", type=Path)
    parser.add_argument("--projection-only", action="store_true", help="validate a hand-built n<=3 structural projection without recurrence")
    parser.add_argument("--projection-baseline", type=Path, help="classify exactly one hostile mutation against an accepted projection")
    args = parser.parse_args()
    outcome = {"ok": False, "diagnostic": None, "checks": {}}
    exit_status = 0
    try:
        if args.corpus.is_symlink() or not args.corpus.is_file():
            reject("INPUT_STOP", "corpus_path")
        corpus = json.loads(args.corpus.read_text(encoding="utf-8"))
        if args.projection_only:
            if args.projection_baseline is not None:
                baseline = json.loads(args.projection_baseline.read_text(encoding="utf-8"))
                validate_structure(baseline, projection=True)
                diagnostic = diagnose_single_mutation(baseline, corpus)
                reject(diagnostic, "single_mutation")
            validate_structure(corpus, projection=True)
            outcome.update({"ok": True, "diagnostic": "PROJECTION-ACCEPTED", "checks": {"projection_structure": True}})
        else:
            if args.projection_baseline is not None:
                reject("INPUT_STOP", "baseline_without_projection")
            outcome["checks"] = normal_check(corpus, args.corpus, args.schema)
            outcome.update({"ok": True, "diagnostic": "HANKEL-CORPUS-PILOT-VERIFIED"})
    except (CorpusError, json.JSONDecodeError, OSError, KeyError, TypeError, ValueError) as error:
        exit_status = 1
        if isinstance(error, CorpusError):
            outcome.update({"diagnostic": error.diagnostic, "detail": error.detail})
        else:
            outcome.update({"diagnostic": "SCHEMA", "detail": type(error).__name__})
    outcome["corpus"] = str(args.corpus)
    outcome["corpus_sha256"] = digest_file(args.corpus) if args.corpus.is_file() else None
    if args.projection_only:
        print(json.dumps(outcome, sort_keys=True))
    else:
        if args.receipt is None:
            parser.error("--receipt is required outside projection mode")
        atomic_receipt(args.receipt, outcome)
        print(json.dumps(outcome, sort_keys=True))
    raise SystemExit(exit_status)


if __name__ == "__main__":
    main()
