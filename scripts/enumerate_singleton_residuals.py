#!/usr/bin/env python3
"""Enumerate the exact k=6 singleton-context residual oracle at eight leaves.

For each recursively decomposable coloring on ``child_size`` ordered vertices,
the producer records its property-relative all-gap observation and the
observation after every one-vertex deep-below merge.  Closed observations,
which already contain a strong ``k``-set, are collapsed to one terminal value.

The default ``child_size=8`` experiment therefore covers all 18 singleton
contexts at the first nonvacuous nine-vertex transition.  Large per-context
tables are machine-local under ``runs/``; only a compact summary is committed.
The independent checker does not import this module.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import itertools
import json
import os
import struct
import subprocess
from collections import Counter
from dataclasses import dataclass
from pathlib import Path


ROLE_UPPER = "upper"
ROLE_LOWER = "lower"


def triples(n: int) -> tuple[tuple[int, int, int], ...]:
    return tuple(itertools.combinations(range(n), 3))


def nonempty_proper_submasks(mask: int):
    child = (mask - 1) & mask
    while child:
        yield child
        child = (child - 1) & mask


class DecomposableColorings:
    """Bottom-up enumeration in the child's own triple coordinates."""

    def __init__(self, n: int):
        self.n = n
        self.triples = triples(n)
        self.positions = {triple: index for index, triple in enumerate(self.triples)}
        self.support: dict[int, int] = {}
        self.states: dict[int, frozenset[int]] = {}
        for mask in range(1, 1 << n):
            value = 0
            for index, triple in enumerate(self.triples):
                selected = sum(1 << vertex for vertex in triple)
                if selected & mask == selected:
                    value |= 1 << index
            self.support[mask] = value

    def crossing_bits(self, mask: int, lower: int) -> int:
        answer = 0
        for index, (i, j, k) in enumerate(self.triples):
            selected = (1 << i) | (1 << j) | (1 << k)
            if selected & mask != selected:
                continue
            count = (selected & lower).bit_count()
            if 0 < count < 3 and lower & (1 << j):
                answer |= 1 << index
        return answer

    def enumerate(self) -> tuple[int, ...]:
        full = (1 << self.n) - 1
        for size in range(1, self.n + 1):
            for mask in range(1, full + 1):
                if mask.bit_count() != size:
                    continue
                if size == 1:
                    self.states[mask] = frozenset((0,))
                    continue
                answers: set[int] = set()
                for lower in nonempty_proper_submasks(mask):
                    upper = mask ^ lower
                    fixed = self.crossing_bits(mask, lower)
                    for lower_bits in self.states[lower]:
                        for upper_bits in self.states[upper]:
                            answers.add(lower_bits | upper_bits | fixed)
                self.states[mask] = frozenset(answers)
        return tuple(sorted(self.states[full]))


@dataclass(frozen=True)
class SubsetData:
    size: int
    minimum: int
    maximum: int
    required: int
    strong_equalities: tuple[int, ...]


class Observation:
    """Property-relative anchored cup/cap observation for a fixed ambient n."""

    def __init__(self, n: int, k: int):
        self.n = n
        self.k = k
        self.triples = triples(n)
        positions = {triple: index for index, triple in enumerate(self.triples)}
        self.subsets: list[SubsetData] = []
        self.strong_subsets: list[SubsetData] = []
        for size in range(1, min(n, k) + 1):
            for vertices in itertools.combinations(range(n), size):
                required = 0
                for triple in itertools.combinations(vertices, 3):
                    required |= 1 << positions[triple]
                equalities: list[int] = []
                if size == k:
                    for a, b, c, d in itertools.combinations(vertices, 4):
                        equalities.append(
                            (1 << positions[(a, b, c)]) | (1 << positions[(a, b, d)])
                        )
                        equalities.append(
                            (1 << positions[(a, c, d)]) | (1 << positions[(b, c, d)])
                        )
                data = SubsetData(
                    size=size,
                    minimum=vertices[0],
                    maximum=vertices[-1],
                    required=required,
                    strong_equalities=tuple(equalities),
                )
                self.subsets.append(data)
                if equalities:
                    self.strong_subsets.append(data)
        self.record_size = 1 + 4 * (n + 1)
        self.closed_record = bytes((1,)) + bytes(4 * (n + 1))

    @staticmethod
    def equality_holds(bits: int, pair: int) -> bool:
        value = bits & pair
        return value == 0 or value == pair

    def is_closed(self, bits: int) -> bool:
        return any(
            all(self.equality_holds(bits, pair) for pair in subset.strong_equalities)
            for subset in self.strong_subsets
        )

    def encode(self, bits: int) -> bytes:
        if self.is_closed(bits):
            return self.closed_record
        values = [[0] * 6 for _ in range(self.n + 1)]
        for subset in self.subsets:
            cup = bits & subset.required == subset.required
            cap = bits & subset.required == 0
            if not cup and not cap:
                continue
            for gap in range(self.n + 1):
                relation = (
                    0 if gap <= subset.minimum else 1 if gap > subset.maximum else 2
                )
                if cup and subset.size > values[gap][relation]:
                    values[gap][relation] = subset.size
                if cap and subset.size > values[gap][3 + relation]:
                    values[gap][3 + relation] = subset.size
        packed = bytearray((0,))
        for row in values:
            code = 0
            for index, value in enumerate(row):
                code |= value << (3 * index)
            packed.extend(struct.pack("<I", code))
        return bytes(packed)


def embedding_tables(child_n: int, root: int) -> tuple[tuple[int, ...], ...]:
    child_triples = triples(child_n)
    parent_positions = {triple: index for index, triple in enumerate(triples(child_n + 1))}
    mapped_positions = []
    for triple in child_triples:
        mapped = tuple(vertex if vertex < root else vertex + 1 for vertex in triple)
        mapped_positions.append(parent_positions[mapped])
    tables = []
    for byte_index in range((len(child_triples) + 7) // 8):
        table = []
        for byte in range(256):
            value = 0
            for offset in range(8):
                source = 8 * byte_index + offset
                if source < len(mapped_positions) and byte & (1 << offset):
                    value |= 1 << mapped_positions[source]
            table.append(value)
        tables.append(tuple(table))
    return tuple(tables)


def embed(bits: int, tables: tuple[tuple[int, ...], ...]) -> int:
    answer = 0
    for byte_index, table in enumerate(tables):
        answer |= table[(bits >> (8 * byte_index)) & 255]
    return answer


def crossing_bits(n: int, lower: int) -> int:
    answer = 0
    for index, (i, j, k) in enumerate(triples(n)):
        selected = (1 << i) | (1 << j) | (1 << k)
        count = (selected & lower).bit_count()
        if 0 < count < 3 and lower & (1 << j):
            answer |= 1 << index
    return answer


_WORK_COLORINGS: tuple[int, ...] = ()
_WORK_CHILD_N = 0
_WORK_K = 0
_WORK_DIRECTORY = Path()


def initialize_worker(
    colorings: tuple[int, ...], child_n: int, k: int, directory: str
) -> None:
    global _WORK_COLORINGS, _WORK_CHILD_N, _WORK_K, _WORK_DIRECTORY
    _WORK_COLORINGS = colorings
    _WORK_CHILD_N = child_n
    _WORK_K = k
    _WORK_DIRECTORY = Path(directory)


def context_name(root: int, role: str) -> str:
    return f"root-{root:02d}-child-{role}"


def produce_context(context: tuple[int, str]) -> dict[str, object]:
    root, role = context
    parent_n = _WORK_CHILD_N + 1
    full = (1 << parent_n) - 1
    root_mask = 1 << root
    lower = root_mask if role == ROLE_UPPER else full ^ root_mask
    fixed = crossing_bits(parent_n, lower)
    tables = embedding_tables(_WORK_CHILD_N, root)
    observation = Observation(parent_n, _WORK_K)
    name = context_name(root, role)
    path = _WORK_DIRECTORY / f"{name}.bin"
    temporary = path.with_suffix(".bin.tmp")
    digest = hashlib.sha256()
    closed = 0
    with temporary.open("wb") as stream:
        for child_bits in _WORK_COLORINGS:
            parent_bits = embed(child_bits, tables) | fixed
            record = observation.encode(parent_bits)
            closed += record[0]
            digest.update(record)
            stream.write(record)
    os.replace(temporary, path)
    return {
        "root": root,
        "child_role": role,
        "lower_mask_hex": f"{lower:x}",
        "record_count": len(_WORK_COLORINGS),
        "record_size": observation.record_size,
        "closed_count": closed,
        "open_count": len(_WORK_COLORINGS) - closed,
        "records_sha256": digest.hexdigest(),
        "machine_file": str(path),
    }


def source_digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_revision(repo: Path) -> str:
    completed = subprocess.run(
        ["git", "--git-dir=.git-data", "--work-tree=.", "rev-parse", "HEAD"],
        cwd=repo,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    )
    return completed.stdout.strip()


def normalize_ambient_child(hex_bits: str, root: int, child_n: int) -> int:
    ambient = int(hex_bits, 16)
    ambient_positions = {triple: index for index, triple in enumerate(triples(child_n + 1))}
    answer = 0
    for index, triple in enumerate(triples(child_n)):
        mapped = tuple(vertex if vertex < root else vertex + 1 for vertex in triple)
        if ambient & (1 << ambient_positions[mapped]):
            answer |= 1 << index
    return answer


def load_regressions(repo: Path, child_n: int) -> dict[str, tuple[int, int]]:
    if child_n != 8:
        return {}
    context = json.loads(
        (repo / "data/derived/e3-context-k6-n9-singleton-collision.json").read_text()
    )
    rank = json.loads(
        (repo / "data/derived/e3-rank-k6-n9-singleton.json").read_text()
    )
    return {
        "all_gap_collision": (
            normalize_ambient_child(context["left"]["upper_coloring_hex"], 1, child_n),
            normalize_ambient_child(context["right"]["upper_coloring_hex"], 1, child_n),
        ),
        "pair_rank_collision": (
            normalize_ambient_child(
                rank["pair_rank_collision"]["left"]["upper_coloring_hex"], 1, child_n
            ),
            normalize_ambient_child(
                rank["pair_rank_collision"]["right"]["upper_coloring_hex"], 1, child_n
            ),
        ),
    }


def first_context_difference(
    left_index: int,
    right_index: int,
    own_records: list[bytes],
    context_records: list[list[bytes]],
    contexts: list[dict[str, object]],
) -> dict[str, object] | None:
    if own_records[left_index] != own_records[right_index]:
        return {
            "kind": "child_observation",
            **record_difference(own_records[left_index], own_records[right_index]),
        }
    for metadata, records in zip(contexts, context_records):
        if records[left_index] != records[right_index]:
            return {
                "kind": "singleton_context",
                "root": metadata["root"],
                "child_role": metadata["child_role"],
                **record_difference(records[left_index], records[right_index]),
            }
    return None


def unpack_profile(code: int) -> list[int]:
    return [(code >> (3 * index)) & 7 for index in range(6)]


def record_difference(left: bytes, right: bytes) -> dict[str, object]:
    answer: dict[str, object] = {
        "left_closed": bool(left[0]),
        "right_closed": bool(right[0]),
    }
    if left[0] != right[0] or left[0]:
        return answer
    fields = (
        "cup_anchor_left",
        "cup_anchor_right",
        "cup_straddled",
        "cap_anchor_left",
        "cap_anchor_right",
        "cap_straddled",
    )
    for gap in range((len(left) - 1) // 4):
        start = 1 + 4 * gap
        a = struct.unpack("<I", left[start:start + 4])[0]
        b = struct.unpack("<I", right[start:start + 4])[0]
        if a != b:
            av = unpack_profile(a)
            bv = unpack_profile(b)
            answer.update({
                "gap": gap,
                "fields": [
                    field for field, x, y in zip(fields, av, bv) if x != y
                ],
                "left_profile": av,
                "right_profile": bv,
            })
            return answer
    raise AssertionError("unequal open records had no unequal gap")


def context_refinement_summary(
    own_records: list[bytes],
    context_records: list[list[bytes]],
    contexts: list[dict[str, object]],
) -> dict[str, object]:
    individual = []
    for metadata, records in zip(contexts, context_records):
        individual.append({
            "root": metadata["root"],
            "child_role": metadata["child_role"],
            "class_count": len(set(zip(own_records, records))),
        })
    signatures = own_records
    remaining = list(range(len(context_records)))
    greedy = []
    previous_count = len(set(signatures))
    while remaining:
        candidates = [
            (len(set(zip(signatures, context_records[index]))), -index, index)
            for index in remaining
        ]
        count, _, selected = max(candidates)
        if count == previous_count:
            break
        metadata = contexts[selected]
        greedy.append({
            "root": metadata["root"],
            "child_role": metadata["child_role"],
            "class_count": count,
        })
        signatures = [
            signature + record
            for signature, record in zip(signatures, context_records[selected])
        ]
        remaining.remove(selected)
        previous_count = count
    return {
        "individual_contexts": individual,
        "greedy_context_sequence": greedy,
        "redundant_context_count_after_greedy": len(remaining),
    }


def read_records(path: Path, record_size: int, count: int) -> list[bytes]:
    data = path.read_bytes()
    if len(data) != record_size * count:
        raise ValueError(f"unexpected record table size: {path}")
    return [data[start:start + record_size] for start in range(0, len(data), record_size)]


def aggregate(
    repo: Path,
    colorings: tuple[int, ...],
    child_n: int,
    k: int,
    directory: Path,
    contexts: list[dict[str, object]],
) -> dict[str, object]:
    child_observation = Observation(child_n, k)
    own_records = [child_observation.encode(bits) for bits in colorings]
    context_records = [
        read_records(Path(str(item["machine_file"])), int(item["record_size"]), len(colorings))
        for item in contexts
    ]
    classes: dict[bytes, int] = {}
    class_sizes: Counter[int] = Counter()
    class_first: dict[int, int] = {}
    class_second: dict[int, int] = {}
    class_ids: list[int] = []
    coloring_digest = hashlib.sha256()
    state_digest = hashlib.sha256()
    own_alphabet: set[bytes] = set()
    first_refinement = None
    own_first: dict[bytes, tuple[int, int]] = {}
    for index, bits in enumerate(colorings):
        own = own_records[index]
        own_alphabet.add(own)
        signature = own + b"".join(records[index] for records in context_records)
        class_id = classes.get(signature)
        if class_id is None:
            class_id = len(classes)
            classes[signature] = class_id
            class_first[class_id] = bits
        elif class_id not in class_second:
            class_second[class_id] = bits
        class_ids.append(class_id)
        class_sizes[class_id] += 1
        coloring_digest.update(f"{bits:x}\n".encode())
        state_digest.update(f"{bits:x}|{class_id}|".encode())
        state_digest.update(hashlib.sha256(signature).digest())
        previous = own_first.get(own)
        if previous is None:
            own_first[own] = index, class_id
        elif previous[1] != class_id and first_refinement is None:
            old_index = previous[0]
            first_refinement = {
                "left_coloring_hex": f"{colorings[old_index]:x}",
                "right_coloring_hex": f"{bits:x}",
                "first_difference": first_context_difference(
                    old_index, index, own_records, context_records, contexts
                ),
            }

    regressions = {}
    index_by_bits = {bits: index for index, bits in enumerate(colorings)}
    for label, (left, right) in load_regressions(repo, child_n).items():
        left_index = index_by_bits[left]
        right_index = index_by_bits[right]
        regressions[label] = {
            "left_coloring_hex": f"{left:x}",
            "right_coloring_hex": f"{right:x}",
            "equal_child_observation": own_records[left_index] == own_records[right_index],
            "equal_residual_state": class_ids[left_index] == class_ids[right_index],
            "first_difference": first_context_difference(
                left_index, right_index, own_records, context_records, contexts
            ),
        }

    positive = None
    for class_id in sorted(class_second):
        positive = {
            "class_id": class_id,
            "left_coloring_hex": f"{class_first[class_id]:x}",
            "right_coloring_hex": f"{class_second[class_id]:x}",
        }
        break
    size_histogram = Counter(class_sizes.values())
    return {
        "coloring_count": len(colorings),
        "colorings_sha256": coloring_digest.hexdigest(),
        "child_observation_count": len(own_alphabet),
        "residual_class_count": len(classes),
        "nontrivial_residual_class_count": sum(size > 1 for size in class_sizes.values()),
        "largest_residual_class_size": max(class_sizes.values(), default=0),
        "residual_class_size_histogram": {
            str(size): count for size, count in sorted(size_histogram.items())
        },
        "state_records_sha256": state_digest.hexdigest(),
        "context_refinement": context_refinement_summary(
            own_records, context_records, contexts
        ),
        "first_context_refinement": first_refinement,
        "first_nontrivial_residual_class": positive,
        "regressions": regressions,
    }


def produce(child_n: int, k: int, workers: int, directory: Path) -> dict[str, object]:
    if k > child_n + 1:
        raise ValueError("k must not exceed the parent size")
    repo = Path(__file__).resolve().parent.parent
    directory.mkdir(parents=True, exist_ok=True)
    colorings = DecomposableColorings(child_n).enumerate()
    contexts = [
        (root, role)
        for root in range(child_n + 1)
        for role in (ROLE_UPPER, ROLE_LOWER)
    ]
    initialize_worker(colorings, child_n, k, str(directory))
    if workers == 1:
        metadata = [produce_context(context) for context in contexts]
    else:
        with concurrent.futures.ProcessPoolExecutor(
            max_workers=workers,
            initializer=initialize_worker,
            initargs=(colorings, child_n, k, str(directory)),
        ) as pool:
            metadata = list(pool.map(produce_context, contexts))
    metadata.sort(key=lambda item: (int(item["root"]), str(item["child_role"])))
    summary = aggregate(repo, colorings, child_n, k, directory, metadata)
    producer = Path(__file__).resolve()
    checker = repo / "scripts/check_singleton_residuals.py"
    public_metadata = [
        {key: value for key, value in item.items() if key != "machine_file"}
        for item in metadata
    ]
    return {
        "schema_version": 1,
        "experiment": "singleton-context-residual-oracle",
        "generation_base_revision": git_revision(repo),
        "parameters": {
            "child_size": child_n,
            "parent_size": child_n + 1,
            "strong_size": k,
            "context_count": len(contexts),
            "closed_observation": "one terminal symbol",
            "open_observation": (
                "all-gap clipped cup/cap maxima in anchor-left, anchor-right, "
                "and straddling classes"
            ),
        },
        "sources": {
            "producer": {
                "path": str(producer.relative_to(repo)),
                "sha256": source_digest(producer),
            },
            "checker": {
                "path": str(checker.relative_to(repo)),
                "sha256": source_digest(checker),
            },
        },
        "contexts": public_metadata,
        "summary": summary,
        "scope": (
            f"Exact for every recursively deep-below coloring on {child_n} ordered "
            f"vertices and all {2 * (child_n + 1)} one-vertex root contexts."
        ),
    }


def write_atomic(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    os.replace(temporary, path)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--child-size", type=int, default=8)
    parser.add_argument("--strong-size", type=int, default=6)
    parser.add_argument("--workers", type=int, default=min(8, os.cpu_count() or 1))
    parser.add_argument("--run-directory", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if not 3 <= args.child_size <= 8:
        parser.error("child-size must lie between 3 and 8")
    if not 4 <= args.strong_size <= args.child_size + 1:
        parser.error("strong-size must lie between 4 and child-size + 1")
    if not 1 <= args.workers <= 8:
        parser.error("workers must lie between 1 and 8")
    result = produce(
        args.child_size, args.strong_size, args.workers, args.run_directory.resolve()
    )
    write_atomic(args.output, result)
    print(args.output)


if __name__ == "__main__":
    main()
