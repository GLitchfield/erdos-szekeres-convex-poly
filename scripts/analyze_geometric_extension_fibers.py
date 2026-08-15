#!/usr/bin/env python3
"""Build the frozen n=4,5,6 abstract/fixed geometric extension atlas.

This is a bounded exact-rational experiment.  Here ``n`` is the child size,
so no seven-point coloring or extension is constructed.
"""

from __future__ import annotations

import argparse
from collections import defaultdict, deque
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path
from typing import Iterable


EXPECTED_LEVELS = ((4, 3), (5, 4), (6, 5))
ALLOWED_WORDS = {
    (0, 0, 0, 0),
    (0, 0, 0, 1),
    (0, 0, 1, 1),
    (0, 1, 1, 1),
    (1, 0, 0, 0),
    (1, 1, 0, 0),
    (1, 1, 1, 0),
    (1, 1, 1, 1),
}


class AtlasError(Exception):
    """A frozen-input, model, or reconstruction mismatch."""


def combinations(n: int, size: int) -> tuple[tuple[int, ...], ...]:
    return tuple(itertools.combinations(range(n), size))


def pairs(n: int) -> tuple[tuple[int, int], ...]:
    return combinations(n, 2)  # type: ignore[return-value]


def triples(n: int) -> tuple[tuple[int, int, int], ...]:
    return combinations(n, 3)  # type: ignore[return-value]


def width(bit_count: int) -> int:
    return max(1, (bit_count + 3) // 4)


def mask_text(mask: int, bit_count: int) -> str:
    return format(mask, f"0{width(bit_count)}x")


def fraction_text(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def parse_fraction(value: object) -> Fraction:
    if isinstance(value, int):
        return Fraction(value)
    if isinstance(value, str):
        try:
            return Fraction(value)
        except (ValueError, ZeroDivisionError) as error:
            raise AtlasError(f"malformed rational {value!r}") from error
    raise AtlasError(f"non-rational coordinate {value!r}")


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        while chunk := source.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def canonical_sha256(value: object) -> str:
    payload = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(payload).hexdigest()


def read_json(path: Path) -> dict[str, object]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise AtlasError(f"expected JSON object in {path}")
    return value


def validate_frozen_inputs(repo_root: Path, spec_path: Path) -> tuple[
        dict[str, object], dict[str, str]]:
    spec = read_json(spec_path)
    levels = tuple((row["child_n"], row["parent_n"])
                   for row in spec.get("atlas_levels", []))  # type: ignore[index]
    if levels != EXPECTED_LEVELS:
        raise AtlasError(f"unexpected frozen levels: {levels}")
    if spec.get("scope_interpretation") != (
            "n denotes child size, so the atlas extends parent sizes 3, 4, and 5 only"):
        raise AtlasError("frozen n semantics changed")
    hashes = spec.get("frozen_input_sha256")
    if not isinstance(hashes, dict) or len(hashes) != 10:
        raise AtlasError("frozen input ledger must contain exactly ten files")
    checked: dict[str, str] = {}
    for relative, expected in sorted(hashes.items()):
        if not isinstance(relative, str) or not isinstance(expected, str):
            raise AtlasError("malformed frozen input ledger")
        actual = sha256_file(repo_root / relative)
        if actual != expected:
            raise AtlasError(f"frozen input hash mismatch: {relative}")
        checked[relative] = actual
    return spec, checked


def orientation(points: tuple[tuple[Fraction, Fraction], ...],
                i: int, j: int, k: int) -> Fraction:
    xi, yi = points[i]
    xj, yj = points[j]
    xk, yk = points[k]
    return (xj - xi) * (yk - yi) - (yj - yi) * (xk - xi)


def coloring_mask(points: tuple[tuple[Fraction, Fraction], ...]) -> int:
    signs = [orientation(points, *triple) for triple in triples(len(points))]
    if any(sign == 0 for sign in signs):
        raise AtlasError("degenerate frozen parent realization")
    return sum(int(sign > 0) << bit for bit, sign in enumerate(signs))


def validate_points(points: tuple[tuple[Fraction, Fraction], ...]) -> None:
    if any(left[0] >= right[0] for left, right in zip(points, points[1:])):
        raise AtlasError("parent coordinates are not in strict sweep order")
    coloring_mask(points)


def compatible_links(parent_n: int, parent_mask: int) -> tuple[int, ...]:
    pair_positions = {pair: bit for bit, pair in enumerate(pairs(parent_n))}
    triple_positions = {triple: bit for bit, triple in enumerate(triples(parent_n))}
    accepted = []
    for link_mask in range(1 << len(pair_positions)):
        good = True
        for i, j, k in triples(parent_n):
            word = (
                (parent_mask >> triple_positions[(i, j, k)]) & 1,
                (link_mask >> pair_positions[(i, j)]) & 1,
                (link_mask >> pair_positions[(i, k)]) & 1,
                (link_mask >> pair_positions[(j, k)]) & 1,
            )
            if word not in ALLOWED_WORDS:
                good = False
                break
        if good:
            accepted.append(link_mask)
    return tuple(accepted)


def permutation_inversion_masks(n: int) -> set[int]:
    pair_order = pairs(n)
    return {
        sum(int(permutation[i] > permutation[j]) << bit
            for bit, (i, j) in enumerate(pair_order))
        for permutation in itertools.permutations(range(n))
    }


def compose_child_mask(parent_n: int, parent_mask: int, link_mask: int) -> int:
    old_positions = {triple: bit for bit, triple in enumerate(triples(parent_n))}
    link_positions = {pair: bit for bit, pair in enumerate(pairs(parent_n))}
    result = 0
    for bit, (i, j, k) in enumerate(triples(parent_n + 1)):
        if k < parent_n:
            value = (parent_mask >> old_positions[(i, j, k)]) & 1
        else:
            value = (link_mask >> link_positions[(i, j)]) & 1
        result |= value << bit
    return result


def parent_masks(catalog: dict[str, object], parent_n: int) -> tuple[int, ...]:
    if parent_n == 3:
        return (0, 1)
    level = catalog["levels"][str(parent_n)]  # type: ignore[index]
    return tuple(int(value, 16) for value in level["states_hex"])  # type: ignore[index]


def build_abstract_level(catalog: dict[str, object], child_n: int,
                         parent_n: int) -> dict[str, object]:
    pbits = len(triples(parent_n))
    lbits = len(pairs(parent_n))
    cbits = len(triples(child_n))
    rows = []
    independent_edges: dict[tuple[int, int], int] = {}
    inversion_masks = permutation_inversion_masks(parent_n)
    for parent_mask in parent_masks(catalog, parent_n):
        links = compatible_links(parent_n, parent_mask)
        if not set(links) <= inversion_masks:
            raise AtlasError(
                f"compatible link is not a permutation inversion set at parent n={parent_n}")
        for link_mask in links:
            independent_edges[(parent_mask, link_mask)] = compose_child_mask(
                parent_n, parent_mask, link_mask)
        rows.append({
            "compatible_count": len(links),
            "compatible_link_masks_hex": [mask_text(mask, lbits) for mask in links],
            "parent_mask_hex": mask_text(parent_mask, pbits),
        })

    key = f"{parent_n}_to_{child_n}"
    frozen = catalog["rightmost_extensions"][key]  # type: ignore[index]
    catalog_edges: dict[tuple[int, int], int] = {}
    for edge in frozen["edges"]:  # type: ignore[index]
        identity = (int(edge["parent"], 16), int(edge["new_pair_bits"], 16))
        if identity in catalog_edges:
            raise AtlasError(f"duplicate frozen abstract edge at {key}: {identity}")
        catalog_edges[identity] = int(edge["child"], 16)
    if independent_edges != catalog_edges:
        missing = sorted(set(independent_edges) - set(catalog_edges))[:5]
        extra = sorted(set(catalog_edges) - set(independent_edges))[:5]
        wrong = sorted(identity for identity in set(independent_edges) & set(catalog_edges)
                       if independent_edges[identity] != catalog_edges[identity])[:5]
        raise AtlasError(
            f"abstract LastExtensionCompatible mismatch at {key}: "
            f"missing={missing}, extra={extra}, wrong_child={wrong}")
    if any(child >= (1 << cbits) for child in independent_edges.values()):
        raise AtlasError("composed child mask exceeds frozen bit width")
    return {
        "catalog_edge_set_match": True,
        "edge_count": len(independent_edges),
        "link_bit_count": lbits,
        "parent_bit_count": pbits,
        "parent_count": len(rows),
        "rows": rows,
        "transitive_tournament_sanity": {
            "all_compatible_links_are_permutation_inversion_sets": True,
            "evidence_role": "abstract OneChange sanity check; not new geometry",
            "possible_permutation_inversion_mask_count": len(inversion_masks),
        },
    }


def line_data(points: tuple[tuple[Fraction, Fraction], ...]) -> tuple[
        tuple[str, Fraction, Fraction], ...]:
    result = []
    for i, j in pairs(len(points)):
        xi, yi = points[i]
        xj, yj = points[j]
        if xi == xj:
            raise AtlasError("vertical old pair-line violates strict sweep order")
        slope = (yj - yi) / (xj - xi)
        intercept = yi - slope * xi
        result.append((f"{i}-{j}", slope, intercept))
    return tuple(result)


def wiring_from_points(points: tuple[tuple[Fraction, Fraction], ...]) -> dict[str, object]:
    lines = line_data(points)
    x_boundary = max(x for x, _ in points)
    boundary = sorted(lines, key=lambda line: (
        line[1] * x_boundary + line[2], line[1], line[0]))
    current = [line[0] for line in boundary]
    crossing_points: dict[Fraction, dict[Fraction, set[str]]] = defaultdict(
        lambda: defaultdict(set))
    for left, right in itertools.combinations(lines, 2):
        if left[1] == right[1]:
            continue
        cross_x = (right[2] - left[2]) / (left[1] - right[1])
        if cross_x <= x_boundary:
            continue
        cross_y = left[1] * cross_x + left[2]
        crossing_points[cross_x][cross_y].update((left[0], right[0]))

    slices = []
    for cross_x in sorted(crossing_points):
        blocks: list[list[str]] = []
        occupied: set[str] = set()
        for cross_y in sorted(crossing_points[cross_x]):
            labels = crossing_points[cross_x][cross_y]
            if occupied & labels:
                raise AtlasError("one line occurs in two crossing blocks at one x")
            positions = sorted(current.index(label) for label in labels)
            if positions != list(range(positions[0], positions[-1] + 1)):
                raise AtlasError("concurrent lines are not contiguous before crossing")
            block = current[positions[0]:positions[-1] + 1]
            if set(block) != labels:
                raise AtlasError("crossing block label mismatch")
            blocks.append(block)
            occupied.update(labels)
        updated = list(current)
        for block in blocks:
            start = current.index(block[0])
            updated[start:start + len(block)] = reversed(block)
        exact_after = [line[0] for line in sorted(lines, key=lambda line: (
            line[1] * cross_x + line[2], line[1], line[0]))]
        if updated != exact_after:
            raise AtlasError("crossing-block replay disagrees with exact line order")
        current = updated
        slices.append({"blocks": blocks})
    return {
        "boundary_order": [line[0] for line in boundary],
        "slices": slices,
    }


def replay_wiring(parent_n: int, wiring: dict[str, object]) -> set[int]:
    expected_labels = [f"{i}-{j}" for i, j in pairs(parent_n)]
    positions = {label: bit for bit, label in enumerate(expected_labels)}
    order = wiring.get("boundary_order")
    if not isinstance(order, list) or sorted(order) != sorted(expected_labels):
        raise AtlasError("wiring boundary is not a canonical label permutation")
    current = list(order)
    cells: set[int] = set()

    def collect() -> None:
        mask = 0
        cells.add(mask)
        for label in current:
            mask |= 1 << positions[label]
            cells.add(mask)

    collect()
    slices = wiring.get("slices")
    if not isinstance(slices, list):
        raise AtlasError("wiring slices missing")
    for event in slices:
        if not isinstance(event, dict) or not isinstance(event.get("blocks"), list):
            raise AtlasError("malformed wiring slice")
        blocks = event["blocks"]
        used: set[str] = set()
        replacements: list[tuple[int, int, list[str]]] = []
        for block in blocks:
            if (not isinstance(block, list) or len(block) < 2 or
                    any(not isinstance(label, str) for label in block)):
                raise AtlasError("malformed wiring block")
            if used & set(block) or len(set(block)) != len(block):
                raise AtlasError("wiring blocks overlap or repeat a label")
            try:
                start = current.index(block[0])
            except ValueError as error:
                raise AtlasError("unknown wiring label") from error
            if current[start:start + len(block)] != block:
                raise AtlasError("wiring block is not current and contiguous")
            replacements.append((start, len(block), block))
            used.update(block)
        for start, length, block in replacements:
            current[start:start + length] = reversed(block)
        collect()
    return cells


def strict_x_solution(rows: Iterable[tuple[Fraction, Fraction]]) -> Fraction | None:
    lower: Fraction | None = None
    upper: Fraction | None = None
    for coefficient, constant in rows:
        if coefficient > 0:
            bound = -constant / coefficient
            lower = bound if lower is None or lower < bound else lower
        elif coefficient < 0:
            bound = -constant / coefficient
            upper = bound if upper is None or bound < upper else upper
        elif constant <= 0:
            return None
    if lower is not None and upper is not None:
        return (lower + upper) / 2 if lower < upper else None
    if lower is not None:
        return lower + 1
    if upper is not None:
        return upper - 1
    return Fraction(0)


def exact_cell_witness(points: tuple[tuple[Fraction, Fraction], ...],
                       pair_mask: int) -> tuple[Fraction, Fraction] | None:
    lines = line_data(points)
    lower_lines = [(slope, intercept) for bit, (_, slope, intercept) in enumerate(lines)
                   if pair_mask & (1 << bit)]
    upper_lines = [(slope, intercept) for bit, (_, slope, intercept) in enumerate(lines)
                   if not pair_mask & (1 << bit)]
    x_rows = [(Fraction(1), -max(x for x, _ in points))]
    for lower_slope, lower_intercept in lower_lines:
        for upper_slope, upper_intercept in upper_lines:
            x_rows.append((upper_slope - lower_slope,
                           upper_intercept - lower_intercept))
    x = strict_x_solution(x_rows)
    if x is None:
        return None
    lows = [slope * x + intercept for slope, intercept in lower_lines]
    highs = [slope * x + intercept for slope, intercept in upper_lines]
    low = max(lows) if lows else None
    high = min(highs) if highs else None
    if low is not None and high is not None:
        if low >= high:
            raise AtlasError("elimination produced a non-strict y interval")
        y = (low + high) / 2
    elif low is not None:
        y = low + 1
    elif high is not None:
        y = high - 1
    else:
        y = Fraction(0)
    return x, y


def witness_mask(points: tuple[tuple[Fraction, Fraction], ...],
                 witness: tuple[Fraction, Fraction]) -> int:
    result = 0
    for bit, (i, j) in enumerate(pairs(len(points))):
        extended = points + (witness,)
        sign = orientation(extended, i, j, len(points))
        if sign == 0:
            raise AtlasError("cell witness lies on an old pair-line")
        result |= int(sign > 0) << bit
    if witness[0] <= max(x for x, _ in points):
        raise AtlasError("cell witness is not in the strict right half-plane")
    return result


def direct_cells(points: tuple[tuple[Fraction, Fraction], ...]) -> dict[
        int, tuple[Fraction, Fraction]]:
    result = {}
    for mask in range(1 << len(pairs(len(points)))):
        witness = exact_cell_witness(points, mask)
        if witness is None:
            continue
        if witness_mask(points, witness) != mask:
            raise AtlasError("constructed witness has the wrong sign mask")
        result[mask] = witness
    return result


def adjacency(cells: set[int], bit_count: int) -> dict[int, list[int]]:
    graph = {mask: [] for mask in cells}
    for mask in sorted(cells):
        for bit in range(bit_count):
            neighbor = mask ^ (1 << bit)
            if neighbor in cells:
                graph[mask].append(neighbor)
        graph[mask].sort()
    return graph


def topology(graph: dict[int, list[int]]) -> dict[str, object]:
    unseen = set(graph)
    components: list[list[int]] = []
    while unseen:
        start = min(unseen)
        queue = deque([start])
        unseen.remove(start)
        component = []
        while queue:
            vertex = queue.popleft()
            component.append(vertex)
            for neighbor in graph[vertex]:
                if neighbor in unseen:
                    unseen.remove(neighbor)
                    queue.append(neighbor)
        components.append(sorted(component))

    diameter = 0
    for component in components:
        for start in component:
            distances = {start: 0}
            queue = deque([start])
            while queue:
                vertex = queue.popleft()
                for neighbor in graph[vertex]:
                    if neighbor not in distances:
                        distances[neighbor] = distances[vertex] + 1
                        queue.append(neighbor)
            diameter = max(diameter, max(distances.values()))
    edge_count = sum(len(neighbors) for neighbors in graph.values()) // 2
    degree_histogram: dict[str, int] = defaultdict(int)
    for neighbors in graph.values():
        degree_histogram[str(len(neighbors))] += 1
    return {
        "component_count": len(components),
        "component_sizes": [len(component) for component in components],
        "cycle_rank": edge_count - len(graph) + len(components),
        "diameter": diameter,
        "edge_count": edge_count,
        "degree_histogram": dict(sorted(degree_histogram.items(), key=lambda item: int(item[0]))),
    }


def points_from_json(raw: object) -> tuple[tuple[Fraction, Fraction], ...]:
    if not isinstance(raw, list):
        raise AtlasError("coordinate list missing")
    points = []
    for point in raw:
        if not isinstance(point, list) or len(point) != 2:
            raise AtlasError("malformed coordinate pair")
        points.append((parse_fraction(point[0]), parse_fraction(point[1])))
    result = tuple(points)
    validate_points(result)
    return result


def points_json(points: tuple[tuple[Fraction, Fraction], ...]) -> list[list[str]]:
    return [[fraction_text(x), fraction_text(y)] for x, y in points]


def admitted_sources(fixed: dict[str, object]) -> list[dict[str, object]]:
    rows = fixed.get("parents")
    if not isinstance(rows, list) or len(rows) != 62:
        raise AtlasError("admitted fixed certificate must have 62 parents")
    result = []
    for row in rows:
        if not isinstance(row, dict) or not isinstance(row.get("mask_hex"), str):
            raise AtlasError("malformed admitted parent row")
        for variant in ("equal_x", "varied_x"):
            realization = row.get(variant)
            if not isinstance(realization, dict):
                raise AtlasError("admitted realization missing")
            result.append({
                "extensions": realization.get("extensions"),
                "id": f"n6-{row['mask_hex']}-{variant}",
                "parent_mask": int(row["mask_hex"], 16),
                "points": points_from_json(realization.get("points")),
                "source_kind": variant,
            })
    return result


def preflight_admitted_wiring(fixed: dict[str, object]) -> dict[str, object]:
    total = 0
    for source in admitted_sources(fixed):
        points = source["points"]
        assert isinstance(points, tuple)
        if coloring_mask(points) != source["parent_mask"]:
            raise AtlasError(f"admitted parent mask mismatch: {source['id']}")
        extensions = source["extensions"]
        if not isinstance(extensions, list):
            raise AtlasError("admitted extension rows missing")
        claimed: set[int] = set()
        for extension in extensions:
            if not isinstance(extension, dict):
                raise AtlasError("malformed admitted extension")
            mask = int(extension["pair_mask_hex"], 16)
            witness_raw = extension.get("witness")
            if not isinstance(witness_raw, list) or len(witness_raw) != 2:
                raise AtlasError("admitted witness missing")
            witness = (parse_fraction(witness_raw[0]), parse_fraction(witness_raw[1]))
            if witness_mask(points, witness) != mask:
                raise AtlasError("admitted witness/sign mismatch")
            claimed.add(mask)
        if len(claimed) != len(extensions):
            raise AtlasError("duplicate admitted cell mask")
        replayed = replay_wiring(len(points), wiring_from_points(points))
        if replayed != claimed:
            raise AtlasError(
                f"frozen wiring fails admitted cell set for {source['id']}: "
                f"missing={sorted(claimed - replayed)}, extra={sorted(replayed - claimed)}")
        total += len(claimed)
    if total != 1550:
        raise AtlasError(f"admitted preflight expected 1550 cells, found {total}")
    return {
        "admitted_cell_count": total,
        "admitted_realization_count": 124,
        "exact_pair_mask_set_match": True,
        "performed_before_new_atlas_outcomes": True,
        "witnesses_rechecked": total,
    }


def coordinate_cohorts(fixed: dict[str, object]) -> dict[int, list[dict[str, object]]]:
    sources = admitted_sources(fixed)
    cohorts: dict[int, list[dict[str, object]]] = {4: [], 5: [], 6: []}
    for source in sources:
        cohorts[6].append({
            "id": source["id"],
            "parent_mask": source["parent_mask"],
            "points": source["points"],
            "provenance": [source["id"]],
            "source_kind": source["source_kind"],
        })
    for child_n, parent_n in ((4, 3), (5, 4)):
        grouped: dict[tuple[tuple[Fraction, Fraction], ...], list[str]] = defaultdict(list)
        for source in sources:
            prefix = source["points"][:parent_n]  # type: ignore[index]
            grouped[prefix].append(source["id"])  # type: ignore[arg-type]
        by_parent: dict[int, list[tuple[tuple[tuple[Fraction, Fraction], ...], list[str]]]] = (
            defaultdict(list))
        for prefix, provenance in grouped.items():
            by_parent[coloring_mask(prefix)].append((prefix, sorted(provenance)))
        for parent_mask in sorted(by_parent):
            ordered = sorted(by_parent[parent_mask], key=lambda row: row[0])
            for index, (prefix, provenance) in enumerate(ordered):
                cohorts[child_n].append({
                    "id": (f"n{child_n}-{mask_text(parent_mask, len(triples(parent_n)))}-"
                           f"prefix-{index:03d}"),
                    "parent_mask": parent_mask,
                    "points": prefix,
                    "provenance": provenance,
                    "source_kind": "distinct_admitted_prefix",
                })
    for child_n in cohorts:
        cohorts[child_n].sort(key=lambda row: (
            row["parent_mask"], row["points"], row["id"]))  # type: ignore[return-value]
    return cohorts


def build_fixed_realization(child_n: int, source: dict[str, object],
                            abstract_links: set[int]) -> tuple[dict[str, object], set[int]]:
    parent_n = child_n - 1
    points = source["points"]
    assert isinstance(points, tuple)
    validate_points(points)
    if len(points) != parent_n or coloring_mask(points) != source["parent_mask"]:
        raise AtlasError(f"cohort parent mismatch: {source['id']}")
    wiring = wiring_from_points(points)
    wiring_cells = replay_wiring(parent_n, wiring)
    cells = direct_cells(points)
    direct_set = set(cells)
    if wiring_cells != direct_set:
        raise AtlasError(
            f"right-wiring refuted at {source['id']}: "
            f"direct_only={sorted(direct_set - wiring_cells)}, "
            f"wiring_only={sorted(wiring_cells - direct_set)}")
    if not direct_set <= abstract_links:
        raise AtlasError(
            f"geometric cell violates LastExtensionCompatible at {source['id']}: "
            f"{sorted(direct_set - abstract_links)}")
    bit_count = len(pairs(parent_n))
    graph = adjacency(direct_set, bit_count)
    topo = topology(graph)
    if topo["component_count"] != 1:
        raise AtlasError(f"cell adjacency graph disconnected at {source['id']}")
    rows = []
    for mask in sorted(cells):
        rows.append({
            "adjacent_masks_hex": [mask_text(value, bit_count) for value in graph[mask]],
            "mask_hex": mask_text(mask, bit_count),
            "witness": [fraction_text(value) for value in cells[mask]],
        })
    fiber_vector = [mask_text(mask, bit_count) for mask in sorted(direct_set)]
    wiring_stats = {
        "crossing_block_count": sum(len(event["blocks"]) for event in wiring["slices"]),  # type: ignore[index]
        "crossing_slice_count": len(wiring["slices"]),  # type: ignore[arg-type]
        "maximum_concurrency": max(
            (len(block) for event in wiring["slices"] for block in event["blocks"]),  # type: ignore[index]
            default=1),
    }
    row = {
        "abstract_minus_fixed_count": len(abstract_links - direct_set),
        "cell_set_sha256": canonical_sha256(fiber_vector),
        "cells": rows,
        "fixed_cell_count": len(rows),
        "id": source["id"],
        "pair_labels": [f"{i}-{j}" for i, j in pairs(parent_n)],
        "parent_mask_hex": mask_text(int(source["parent_mask"]), len(triples(parent_n))),
        "points": points_json(points),
        "provenance": source["provenance"],
        "source_kind": source["source_kind"],
        "topology": topo,
        "wiring": wiring,
        "wiring_sha256": canonical_sha256(wiring),
        "wiring_stats": wiring_stats,
    }
    return row, direct_set


def collision_classes(rows: list[dict[str, object]], key: str,
                      hash_key: str) -> list[dict[str, object]]:
    grouped: dict[str, list[dict[str, object]]] = defaultdict(list)
    for row in rows:
        grouped[str(row[key])].append(row)
    result = []
    for signature, members in sorted(grouped.items()):
        if len(members) < 2:
            continue
        result.append({
            hash_key: signature,
            "parent_masks_hex": sorted({str(row["parent_mask_hex"]) for row in members}),
            "realization_ids": sorted(str(row["id"]) for row in members),
        })
    return result


def build_level(catalog: dict[str, object], cohorts: dict[int, list[dict[str, object]]],
                child_n: int, parent_n: int) -> dict[str, object]:
    abstract = build_abstract_level(catalog, child_n, parent_n)
    abstract_by_parent = {
        int(row["parent_mask_hex"], 16):
            {int(value, 16) for value in row["compatible_link_masks_hex"]}
        for row in abstract["rows"]  # type: ignore[index]
    }
    fixed_rows = []
    fixed_sets: dict[str, set[int]] = {}
    for source in cohorts[child_n]:
        row, cell_set = build_fixed_realization(
            child_n, source, abstract_by_parent[int(source["parent_mask"])])
        fixed_rows.append(row)
        fixed_sets[str(row["id"])] = cell_set

    comparisons = []
    sensitive = 0
    for parent_mask in parent_masks(catalog, parent_n):
        members = [row for row in fixed_rows
                   if int(row["parent_mask_hex"], 16) == parent_mask]
        if not members:
            raise AtlasError(f"no frozen realization for parent {parent_n}:{parent_mask}")
        union: set[int] = set()
        fiber_groups: dict[str, list[str]] = defaultdict(list)
        wiring_groups: dict[str, list[str]] = defaultdict(list)
        for row in members:
            identifier = str(row["id"])
            union.update(fixed_sets[identifier])
            fiber_groups[str(row["cell_set_sha256"])].append(identifier)
            wiring_groups[str(row["wiring_sha256"])].append(identifier)
        is_sensitive = len(fiber_groups) > 1
        sensitive += int(is_sensitive)
        comparisons.append({
            "abstract_count": len(abstract_by_parent[parent_mask]),
            "abstract_minus_sampled_union_count": len(abstract_by_parent[parent_mask] - union),
            "abstract_minus_sampled_union_masks_hex": [
                mask_text(mask, len(pairs(parent_n)))
                for mask in sorted(abstract_by_parent[parent_mask] - union)],
            "distinct_fixed_fiber_count": len(fiber_groups),
            "distinct_wiring_count": len(wiring_groups),
            "fixed_fiber_classes": [
                {"cell_set_sha256": signature, "realization_ids": sorted(ids)}
                for signature, ids in sorted(fiber_groups.items())],
            "parent_mask_hex": mask_text(parent_mask, len(triples(parent_n))),
            "realization_count": len(members),
            "realization_sensitive": is_sensitive,
            "sampled_union_fixed_count": len(union),
            "sampled_union_fixed_masks_hex": [
                mask_text(mask, len(pairs(parent_n))) for mask in sorted(union)],
            "sampled_union_is_full_geomext_claimed": False,
            "wiring_classes": [
                {"realization_ids": sorted(ids), "wiring_sha256": signature}
                for signature, ids in sorted(wiring_groups.items())],
        })

    abstract_collisions: dict[str, list[str]] = defaultdict(list)
    for row in abstract["rows"]:  # type: ignore[index]
        signature = canonical_sha256(row["compatible_link_masks_hex"])
        abstract_collisions[signature].append(str(row["parent_mask_hex"]))
    abstract_collision_rows = [
        {"compatible_set_sha256": signature, "parent_masks_hex": sorted(masks)}
        for signature, masks in sorted(abstract_collisions.items()) if len(masks) > 1]

    all_wiring_groups: dict[str, list[dict[str, object]]] = defaultdict(list)
    for row in fixed_rows:
        all_wiring_groups[str(row["wiring_sha256"])].append(row)
    for signature, members in all_wiring_groups.items():
        if len({str(row["cell_set_sha256"]) for row in members}) != 1:
            raise AtlasError(
                f"same frozen wiring has different fixed fibers at child n={child_n}: "
                f"{signature}")
    return {
        "abstract": abstract,
        "child_n": child_n,
        "comparison_by_parent": comparisons,
        "fixed": {
            "abstract_fiber_collision_classes": abstract_collision_rows,
            "all_adjacency_graphs_connected": all(
                row["topology"]["component_count"] == 1 for row in fixed_rows),  # type: ignore[index]
            "fixed_fiber_collision_classes": collision_classes(
                fixed_rows, "cell_set_sha256", "cell_set_sha256"),
            "realization_count": len(fixed_rows),
            "realizations": fixed_rows,
            "sensitive_parent_count": sensitive,
            "wiring_collision_classes": collision_classes(
                fixed_rows, "wiring_sha256", "wiring_sha256"),
        },
        "parent_n": parent_n,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", type=Path, default=Path("."))
    parser.add_argument("--frozen-spec", type=Path, required=True)
    parser.add_argument("--catalog", type=Path, required=True)
    parser.add_argument("--fixed-certificate", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    repo_root = args.repo_root.resolve()
    spec, checked_hashes = validate_frozen_inputs(repo_root, args.frozen_spec)
    expected_hashes = spec["frozen_input_sha256"]
    catalog_relative = "runs/agents/20260814-local-constraint-hierarchy/census/census-56/catalog.json"
    fixed_relative = "runs/agents/20260814-local-realizability-456/fixed-extension/certificate.json"
    if sha256_file(args.catalog) != expected_hashes[catalog_relative]:  # type: ignore[index]
        raise AtlasError("explicit catalog is not the frozen catalog")
    if sha256_file(args.fixed_certificate) != expected_hashes[fixed_relative]:  # type: ignore[index]
        raise AtlasError("explicit fixed certificate is not the frozen certificate")
    catalog = read_json(args.catalog)
    fixed = read_json(args.fixed_certificate)
    if catalog.get("bounds") != {"max_n": 6, "min_n": 4}:
        raise AtlasError("catalog scope is not exactly n=4,5,6")

    # This gate intentionally precedes abstract enumeration and cohort analysis.
    preflight = preflight_admitted_wiring(fixed)
    print("preflight: frozen right-wiring exactly reconstructs 1,550 admitted cells")

    cohorts = coordinate_cohorts(fixed)
    levels = {}
    for child_n, parent_n in EXPECTED_LEVELS:
        levels[str(child_n)] = build_level(
            catalog, cohorts, child_n, parent_n)

    tested_realizations = sum(
        levels[str(child_n)]["fixed"]["realization_count"]  # type: ignore[index]
        for child_n, _ in EXPECTED_LEVELS)
    tested_cells = sum(
        row["fixed_cell_count"]
        for child_n, _ in EXPECTED_LEVELS
        for row in levels[str(child_n)]["fixed"]["realizations"]  # type: ignore[index]
    )
    document = {
        "claims": {
            "allowed": "computational_evidence",
            "sampled_realizations_exhaust_geomext": False,
            "uniform_erdos_szekeres_formula_proved": False,
        },
        "frozen_input_sha256": checked_hashes,
        "frozen_spec_sha256": sha256_file(args.frozen_spec),
        "levels": levels,
        "model": {
            "abstract": "all LastExtensionCompatible pair-link masks over labeled OneChangeOn parents",
            "fixed": "all full-dimensional strict sign cells of old pair-lines in x greater than max parent x for the frozen rational coordinate cohorts",
            "object_tiers_kept_distinct": True,
            "scope": "child n=4,5,6 only; parent n=3,4,5",
        },
        "outcome": "ATLAS-56-LAND",
        "preflight": preflight,
        "schema_version": 1,
        "summary": {
            "abstract_edge_count_by_child_n": {
                str(child_n): levels[str(child_n)]["abstract"]["edge_count"]  # type: ignore[index]
                for child_n, _ in EXPECTED_LEVELS},
            "all_adjacency_graphs_connected": all(
                levels[str(child_n)]["fixed"]["all_adjacency_graphs_connected"]  # type: ignore[index]
                for child_n, _ in EXPECTED_LEVELS),
            "all_wiring_replays_exact": True,
            "child_levels": [4, 5, 6],
            "fixed_cell_count": tested_cells,
            "fixed_realization_count": tested_realizations,
            "n7_embargo_observed": True,
            "sensitive_parent_count_by_child_n": {
                str(child_n): levels[str(child_n)]["fixed"]["sensitive_parent_count"]  # type: ignore[index]
                for child_n, _ in EXPECTED_LEVELS},
        },
        "wiring_sufficiency": {
            "convention": {
                "boundary_order": "labeled pair-lines bottom-to-top immediately right of max parent x",
                "labels": "canonical i-j labels in lexicographic pair-bit order",
                "sign_bit_one": "positive orientation, equivalently above the labeled pair-line",
                "slices": "strict crossing-x order; every equal-x collection is one atomic slice of disjoint bottom-to-top concurrent blocks",
                "simultaneous_replay": "reverse every block from the common pre-slice order before collecting any new prefix; no partial-slice cells",
            },
            "counterexample": None,
            "representation_contains_fiber_data": False,
            "same_wiring_distinct_fiber_collision": None,
            "tested_fixed_realizations": tested_realizations,
            "verdict": "sufficient_for_every_frozen_fixed_realization",
        },
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(document, indent=2, sort_keys=True) + "\n")
    print(f"atlas: {tested_realizations} fixed realizations, {tested_cells} cells")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
