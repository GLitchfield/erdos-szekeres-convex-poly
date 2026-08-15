#!/usr/bin/env python3
"""Independent checker for the frozen geometric extension-fiber atlas."""

from __future__ import annotations

import argparse
from collections import defaultdict, deque
from copy import deepcopy
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path


LEVELS = ((4, 3), (5, 4), (6, 5))


class CheckError(Exception):
    """The certificate or one of its frozen dependencies is invalid."""


def choose(n: int, k: int) -> tuple[tuple[int, ...], ...]:
    return tuple(itertools.combinations(range(n), k))


def all_pairs(n: int) -> tuple[tuple[int, int], ...]:
    return choose(n, 2)  # type: ignore[return-value]


def all_triples(n: int) -> tuple[tuple[int, int, int], ...]:
    return choose(n, 3)  # type: ignore[return-value]


def hex_width(bits: int) -> int:
    return max(1, (bits + 3) // 4)


def hex_mask(value: int, bits: int) -> str:
    return format(value, f"0{hex_width(bits)}x")


def digest_file(path: Path) -> str:
    state = hashlib.sha256()
    with path.open("rb") as stream:
        for data in iter(lambda: stream.read(1024 * 1024), b""):
            state.update(data)
    return state.hexdigest()


def digest_object(value: object) -> str:
    encoded = json.dumps(value, separators=(",", ":"), sort_keys=True).encode()
    return hashlib.sha256(encoded).hexdigest()


def json_object(path: Path) -> dict[str, object]:
    data = json.loads(path.read_text())
    if not isinstance(data, dict):
        raise CheckError(f"not a JSON object: {path}")
    return data


def rational(value: object) -> Fraction:
    if isinstance(value, int):
        return Fraction(value)
    if not isinstance(value, str):
        raise CheckError("coordinate is not an exact rational string/integer")
    try:
        return Fraction(value)
    except (ValueError, ZeroDivisionError) as error:
        raise CheckError("invalid rational") from error


def parse_points(value: object) -> tuple[tuple[Fraction, Fraction], ...]:
    if not isinstance(value, list):
        raise CheckError("points missing")
    output = []
    for point in value:
        if not isinstance(point, list) or len(point) != 2:
            raise CheckError("malformed point")
        output.append((rational(point[0]), rational(point[1])))
    return tuple(output)


def canonical_points(points: tuple[tuple[Fraction, Fraction], ...]) -> list[list[str]]:
    return [[f"{x.numerator}/{x.denominator}", f"{y.numerator}/{y.denominator}"]
            for x, y in points]


def det(points: tuple[tuple[Fraction, Fraction], ...],
        i: int, j: int, k: int) -> Fraction:
    a, b = points[i]
    c, d = points[j]
    e, f = points[k]
    return (c - a) * (f - b) - (d - b) * (e - a)


def parent_code(points: tuple[tuple[Fraction, Fraction], ...]) -> int:
    if any(points[index][0] >= points[index + 1][0]
           for index in range(len(points) - 1)):
        raise CheckError("coordinates violate strict x order")
    value = 0
    for bit, triple in enumerate(all_triples(len(points))):
        area = det(points, *triple)
        if area == 0:
            raise CheckError("coordinates are not in general position")
        value |= int(area > 0) << bit
    return value


def verify_sources(repo_root: Path, spec_path: Path) -> tuple[
        dict[str, object], dict[str, str]]:
    spec = json_object(spec_path)
    level_rows = spec.get("atlas_levels")
    if not isinstance(level_rows, list):
        raise CheckError("frozen atlas levels missing")
    observed = tuple((entry.get("child_n"), entry.get("parent_n"))
                     for entry in level_rows if isinstance(entry, dict))
    if observed != LEVELS:
        raise CheckError("frozen scope is not exactly child n=4,5,6")
    ledger = spec.get("frozen_input_sha256")
    if not isinstance(ledger, dict) or len(ledger) != 10:
        raise CheckError("frozen ledger does not contain ten inputs")
    actuals = {}
    for name, expected in sorted(ledger.items()):
        if not isinstance(name, str) or not isinstance(expected, str):
            raise CheckError("malformed frozen ledger")
        found = digest_file(repo_root / name)
        if found != expected:
            raise CheckError(f"frozen dependency changed: {name}")
        actuals[name] = found
    return spec, actuals


def old_states(catalog: dict[str, object], n: int) -> tuple[int, ...]:
    if n == 3:
        return (0, 1)
    states = catalog["levels"][str(n)]["states_hex"]  # type: ignore[index]
    return tuple(int(item, 16) for item in states)


def one_change_word(bits: tuple[int, int, int, int]) -> bool:
    return sum(int(left != right) for left, right in zip(bits, bits[1:])) <= 1


def independently_allowed_links(n: int, old_mask: int) -> tuple[int, ...]:
    pair_index = {pair: index for index, pair in enumerate(all_pairs(n))}
    triple_index = {triple: index for index, triple in enumerate(all_triples(n))}
    output = []
    for link in range(1 << len(pair_index)):
        if all(one_change_word((
                (old_mask >> triple_index[(i, j, k)]) & 1,
                (link >> pair_index[(i, j)]) & 1,
                (link >> pair_index[(i, k)]) & 1,
                (link >> pair_index[(j, k)]) & 1,
        )) for i, j, k in all_triples(n)):
            output.append(link)
    return tuple(output)


def child_code(n: int, old_mask: int, link: int) -> int:
    old_index = {triple: index for index, triple in enumerate(all_triples(n))}
    pair_index = {pair: index for index, pair in enumerate(all_pairs(n))}
    result = 0
    for position, (i, j, k) in enumerate(all_triples(n + 1)):
        source = ((old_mask >> old_index[(i, j, k)]) & 1 if k < n else
                  (link >> pair_index[(i, j)]) & 1)
        result |= source << position
    return result


def inversion_codes(n: int) -> set[int]:
    order = all_pairs(n)
    codes = set()
    for permutation in itertools.permutations(range(n)):
        code = 0
        for bit, (i, j) in enumerate(order):
            code |= int(permutation[i] > permutation[j]) << bit
        codes.add(code)
    return codes


def expected_abstract(catalog: dict[str, object], child_n: int,
                      parent_n: int) -> tuple[dict[int, set[int]], int]:
    expected: dict[int, set[int]] = {}
    inversion = inversion_codes(parent_n)
    computed_edges = {}
    for old in old_states(catalog, parent_n):
        links = set(independently_allowed_links(parent_n, old))
        if not links <= inversion:
            raise CheckError("abstract link failed inversion-set sanity")
        expected[old] = links
        for link in links:
            computed_edges[(old, link)] = child_code(parent_n, old, link)
    section = catalog["rightmost_extensions"][f"{parent_n}_to_{child_n}"]  # type: ignore[index]
    recorded_edges = {}
    for row in section["edges"]:  # type: ignore[index]
        key = (int(row["parent"], 16), int(row["new_pair_bits"], 16))
        if key in recorded_edges:
            raise CheckError("duplicate catalog edge")
        recorded_edges[key] = int(row["child"], 16)
    if recorded_edges != computed_edges:
        raise CheckError("catalog and independent LastExtensionCompatible enumeration differ")
    return expected, len(computed_edges)


def admitted_realizations(fixed: dict[str, object]) -> list[dict[str, object]]:
    parents = fixed.get("parents")
    if not isinstance(parents, list) or len(parents) != 62:
        raise CheckError("fixed certificate does not contain 62 parents")
    output = []
    for parent in parents:
        if not isinstance(parent, dict):
            raise CheckError("malformed admitted parent")
        parent_hex = parent.get("mask_hex")
        if not isinstance(parent_hex, str):
            raise CheckError("admitted parent mask missing")
        for kind in ("equal_x", "varied_x"):
            sample = parent.get(kind)
            if not isinstance(sample, dict):
                raise CheckError("admitted sample missing")
            points = parse_points(sample.get("points"))
            output.append({
                "extensions": sample.get("extensions"),
                "id": f"n6-{parent_hex}-{kind}",
                "parent": int(parent_hex, 16),
                "points": points,
                "provenance": [f"n6-{parent_hex}-{kind}"],
                "source_kind": kind,
            })
    return output


def expected_cohorts(fixed: dict[str, object]) -> dict[int, list[dict[str, object]]]:
    admitted = admitted_realizations(fixed)
    result: dict[int, list[dict[str, object]]] = {4: [], 5: [], 6: []}
    for row in admitted:
        result[6].append({key: row[key] for key in
                          ("id", "parent", "points", "provenance", "source_kind")})
    for child_n, parent_n in ((4, 3), (5, 4)):
        origins: dict[tuple[tuple[Fraction, Fraction], ...], list[str]] = defaultdict(list)
        for row in admitted:
            prefix = row["points"][:parent_n]  # type: ignore[index]
            origins[prefix].append(str(row["id"]))  # type: ignore[arg-type]
        partition: dict[int, list[tuple[tuple[tuple[Fraction, Fraction], ...], list[str]]]] = (
            defaultdict(list))
        for points, identifiers in origins.items():
            partition[parent_code(points)].append((points, sorted(identifiers)))
        for parent in sorted(partition):
            entries = sorted(partition[parent], key=lambda item: item[0])
            for ordinal, (points, identifiers) in enumerate(entries):
                result[child_n].append({
                    "id": (f"n{child_n}-{hex_mask(parent, len(all_triples(parent_n)))}-"
                           f"prefix-{ordinal:03d}"),
                    "parent": parent,
                    "points": points,
                    "provenance": identifiers,
                    "source_kind": "distinct_admitted_prefix",
                })
    for child_n in result:
        result[child_n].sort(key=lambda item: (
            item["parent"], item["points"], item["id"]))  # type: ignore[return-value]
    return result


def affine_lines(points: tuple[tuple[Fraction, Fraction], ...]) -> tuple[
        tuple[str, Fraction, Fraction], ...]:
    output = []
    for i, j in all_pairs(len(points)):
        xi, yi = points[i]
        xj, yj = points[j]
        if xj == xi:
            raise CheckError("vertical pair-line")
        gradient = (yj - yi) / (xj - xi)
        offset = yi - gradient * xi
        output.append((f"{i}-{j}", gradient, offset))
    return tuple(output)


def right_crossings(points: tuple[tuple[Fraction, Fraction], ...]) -> dict[
        Fraction, dict[Fraction, set[str]]]:
    boundary = points[-1][0]
    events: dict[Fraction, dict[Fraction, set[str]]] = defaultdict(
        lambda: defaultdict(set))
    for first, second in itertools.combinations(affine_lines(points), 2):
        if first[1] == second[1]:
            continue
        x = (second[2] - first[2]) / (first[1] - second[1])
        if x > boundary:
            y = first[1] * x + first[2]
            events[x][y].update((first[0], second[0]))
    return events


def exact_wiring(points: tuple[tuple[Fraction, Fraction], ...]) -> dict[str, object]:
    lines = affine_lines(points)
    boundary_x = points[-1][0]
    initial = [line[0] for line in sorted(
        lines, key=lambda item: (item[1] * boundary_x + item[2], item[1], item[0]))]
    by_label = {line[0]: line for line in lines}
    slices = []
    for x, y_groups in sorted(right_crossings(points).items()):
        blocks = []
        used: set[str] = set()
        for _, labels in sorted(y_groups.items()):
            if used & labels:
                raise CheckError("line repeated within an equal-x crossing slice")
            # At x-epsilon, larger slope is lower within a concurrent block.
            block = sorted(labels, key=lambda label: (-by_label[label][1], label))
            blocks.append(block)
            used.update(labels)
        slices.append({"blocks": blocks})
    return {"boundary_order": initial, "slices": slices}


def masks_from_wiring(n: int, wiring: dict[str, object]) -> set[int]:
    labels = [f"{i}-{j}" for i, j in all_pairs(n)]
    bit_of = {label: bit for bit, label in enumerate(labels)}
    boundary = wiring.get("boundary_order")
    if not isinstance(boundary, list) or sorted(boundary) != sorted(labels):
        raise CheckError("wiring boundary labels are not a permutation")
    order = list(boundary)
    masks: set[int] = set()

    def add_prefixes() -> None:
        value = 0
        masks.add(value)
        for label in order:
            value |= 1 << bit_of[label]
            masks.add(value)

    add_prefixes()
    slices = wiring.get("slices")
    if not isinstance(slices, list):
        raise CheckError("wiring slices missing")
    for event in slices:
        if not isinstance(event, dict) or not isinstance(event.get("blocks"), list):
            raise CheckError("malformed crossing slice")
        before = list(order)
        updates: list[tuple[int, list[str]]] = []
        occupied: set[str] = set()
        for block in event["blocks"]:
            if not isinstance(block, list) or len(block) < 2:
                raise CheckError("malformed crossing block")
            if len(set(block)) != len(block) or occupied & set(block):
                raise CheckError("crossing blocks overlap")
            try:
                start = before.index(block[0])
            except ValueError as error:
                raise CheckError("unknown crossing label") from error
            if before[start:start + len(block)] != block:
                raise CheckError("block is not contiguous in the common pre-slice order")
            updates.append((start, block))
            occupied.update(block)
        # Every update is based on `before`; no partial equal-x state is sampled.
        after = list(before)
        for start, block in updates:
            after[start:start + len(block)] = list(reversed(block))
        order = after
        add_prefixes()
    return masks


def sign_code(points: tuple[tuple[Fraction, Fraction], ...],
              q: tuple[Fraction, Fraction]) -> int:
    if q[0] <= points[-1][0]:
        raise CheckError("purported cell witness is not strictly rightmost")
    augmented = points + (q,)
    code = 0
    for bit, (i, j) in enumerate(all_pairs(len(points))):
        value = det(augmented, i, j, len(points))
        if value == 0:
            raise CheckError("purported cell witness lies on a pair-line")
        code |= int(value > 0) << bit
    return code


def direct_vertical_probes(points: tuple[tuple[Fraction, Fraction], ...]) -> dict[
        int, tuple[Fraction, Fraction]]:
    """Enumerate cells by exact probes in every open vertical event slab."""
    lines = affine_lines(points)
    boundary = points[-1][0]
    event_xs = sorted(right_crossings(points))
    probes = []
    if event_xs:
        probes.append((boundary + event_xs[0]) / 2)
        probes.extend((left + right) / 2 for left, right in zip(event_xs, event_xs[1:]))
        probes.append(event_xs[-1] + 1)
    else:
        probes.append(boundary + 1)
    cells: dict[int, tuple[Fraction, Fraction]] = {}
    for x in probes:
        ordered = sorted((slope * x + offset, label)
                         for label, slope, offset in lines)
        if any(ordered[index][0] == ordered[index + 1][0]
               for index in range(len(ordered) - 1)):
            raise CheckError("probe x unexpectedly coincides with an event")
        heights = [item[0] for item in ordered]
        ys = [heights[0] - 1]
        ys.extend((low + high) / 2 for low, high in zip(heights, heights[1:]))
        ys.append(heights[-1] + 1)
        for y in ys:
            q = (x, y)
            cells.setdefault(sign_code(points, q), q)
    return cells


def graph_for(cells: set[int], dimensions: int) -> dict[int, list[int]]:
    return {
        cell: sorted(cell ^ (1 << bit) for bit in range(dimensions)
                     if cell ^ (1 << bit) in cells)
        for cell in cells
    }


def graph_invariants(graph: dict[int, list[int]]) -> dict[str, object]:
    remaining = set(graph)
    sizes = []
    diameter = 0
    while remaining:
        seed = min(remaining)
        component = {seed}
        queue = deque([seed])
        remaining.remove(seed)
        while queue:
            here = queue.popleft()
            for there in graph[here]:
                if there not in component:
                    component.add(there)
                    remaining.discard(there)
                    queue.append(there)
        sizes.append(len(component))
        for start in component:
            distance = {start: 0}
            queue = deque([start])
            while queue:
                here = queue.popleft()
                for there in graph[here]:
                    if there not in distance:
                        distance[there] = distance[here] + 1
                        queue.append(there)
            diameter = max(diameter, max(distance.values()))
    degrees: dict[str, int] = defaultdict(int)
    for neighbors in graph.values():
        degrees[str(len(neighbors))] += 1
    edges = sum(map(len, graph.values())) // 2
    return {
        "component_count": len(sizes),
        "component_sizes": sizes,
        "cycle_rank": edges - len(graph) + len(sizes),
        "diameter": diameter,
        "edge_count": edges,
        "degree_histogram": dict(sorted(degrees.items(), key=lambda pair: int(pair[0]))),
    }


def check_admitted_preflight(fixed: dict[str, object]) -> dict[str, object]:
    count = 0
    for row in admitted_realizations(fixed):
        points = row["points"]
        assert isinstance(points, tuple)
        if parent_code(points) != row["parent"]:
            raise CheckError("admitted parent coordinates have the wrong coloring")
        extension_rows = row["extensions"]
        if not isinstance(extension_rows, list):
            raise CheckError("admitted cells missing")
        claimed = set()
        for extension in extension_rows:
            if not isinstance(extension, dict):
                raise CheckError("malformed admitted cell")
            mask = int(extension["pair_mask_hex"], 16)
            witness = extension.get("witness")
            if not isinstance(witness, list) or len(witness) != 2:
                raise CheckError("admitted witness missing")
            if sign_code(points, (rational(witness[0]), rational(witness[1]))) != mask:
                raise CheckError("admitted witness has wrong sign")
            claimed.add(mask)
        if len(claimed) != len(extension_rows):
            raise CheckError("duplicate admitted cell")
        probes = set(direct_vertical_probes(points))
        wiring = masks_from_wiring(len(points), exact_wiring(points))
        if claimed != probes or claimed != wiring:
            raise CheckError("admitted exact cells, direct probes, and wiring differ")
        count += len(claimed)
    if count != 1550:
        raise CheckError("admitted preflight is not exactly 1,550 cells")
    return {
        "admitted_cell_count": 1550,
        "admitted_realization_count": 124,
        "exact_pair_mask_set_match": True,
        "performed_before_new_atlas_outcomes": True,
        "witnesses_rechecked": 1550,
    }


def require_equal(actual: object, expected: object, message: str) -> None:
    if actual != expected:
        raise CheckError(message)


def verify_abstract_claim(claim: dict[str, object], catalog: dict[str, object],
                          child_n: int, parent_n: int) -> dict[int, set[int]]:
    expected, edge_count = expected_abstract(catalog, child_n, parent_n)
    require_equal(claim.get("catalog_edge_set_match"), True, "catalog edge verdict false")
    require_equal(claim.get("edge_count"), edge_count, "abstract edge count mismatch")
    require_equal(claim.get("link_bit_count"), len(all_pairs(parent_n)),
                  "link bit count mismatch")
    require_equal(claim.get("parent_bit_count"), len(all_triples(parent_n)),
                  "parent bit count mismatch")
    require_equal(claim.get("parent_count"), len(expected), "parent count mismatch")
    rows = claim.get("rows")
    if not isinstance(rows, list) or len(rows) != len(expected):
        raise CheckError("abstract rows missing")
    for row, parent in zip(rows, old_states(catalog, parent_n)):
        if not isinstance(row, dict):
            raise CheckError("malformed abstract row")
        links = sorted(expected[parent])
        require_equal(row.get("parent_mask_hex"),
                      hex_mask(parent, len(all_triples(parent_n))),
                      "abstract parent order mismatch")
        require_equal(row.get("compatible_count"), len(links),
                      "compatible count mismatch")
        require_equal(row.get("compatible_link_masks_hex"),
                      [hex_mask(link, len(all_pairs(parent_n))) for link in links],
                      "compatible link set mismatch")
    sanity = claim.get("transitive_tournament_sanity")
    expected_sanity = {
        "all_compatible_links_are_permutation_inversion_sets": True,
        "evidence_role": "abstract OneChange sanity check; not new geometry",
        "possible_permutation_inversion_mask_count": len(inversion_codes(parent_n)),
    }
    require_equal(sanity, expected_sanity, "inversion-set sanity report mismatch")
    return expected


def expected_wiring_statistics(wiring: dict[str, object]) -> dict[str, int]:
    slices = wiring["slices"]
    return {
        "crossing_block_count": sum(len(event["blocks"]) for event in slices),
        "crossing_slice_count": len(slices),
        "maximum_concurrency": max(
            (len(block) for event in slices for block in event["blocks"]), default=1),
    }


def verify_fixed_row(claim: dict[str, object], source: dict[str, object],
                     child_n: int, abstract: set[int]) -> set[int]:
    parent_n = child_n - 1
    require_equal(claim.get("id"), source["id"], "realization id/order mismatch")
    require_equal(claim.get("source_kind"), source["source_kind"], "source kind mismatch")
    require_equal(claim.get("provenance"), source["provenance"], "provenance mismatch")
    points = parse_points(claim.get("points"))
    require_equal(points, source["points"], "frozen coordinate mismatch")
    require_equal(claim.get("points"), canonical_points(points), "coordinates not canonical")
    parent = parent_code(points)
    require_equal(parent, source["parent"], "parent coloring mismatch")
    require_equal(claim.get("parent_mask_hex"),
                  hex_mask(parent, len(all_triples(parent_n))), "parent mask text mismatch")
    labels = [f"{i}-{j}" for i, j in all_pairs(parent_n)]
    require_equal(claim.get("pair_labels"), labels, "line label corruption")

    wiring = exact_wiring(points)
    require_equal(claim.get("wiring"), wiring, "false wiring")
    require_equal(claim.get("wiring_sha256"), digest_object(wiring), "wiring hash mismatch")
    require_equal(claim.get("wiring_stats"), expected_wiring_statistics(wiring),
                  "wiring statistics mismatch")
    direct = direct_vertical_probes(points)
    cells = set(direct)
    require_equal(masks_from_wiring(parent_n, wiring), cells,
                  "wiring replay and direct probes differ")
    if not cells <= abstract:
        raise CheckError("fixed geometric fiber is not abstract-compatible")
    dimensions = len(all_pairs(parent_n))
    graph = graph_for(cells, dimensions)
    cell_rows = claim.get("cells")
    if not isinstance(cell_rows, list) or len(cell_rows) != len(cells):
        raise CheckError("omitted or duplicate cell")
    observed = []
    for cell_row, expected_mask in zip(cell_rows, sorted(cells)):
        if not isinstance(cell_row, dict):
            raise CheckError("malformed cell row")
        require_equal(cell_row.get("mask_hex"), hex_mask(expected_mask, dimensions),
                      "sign mask corruption")
        witness = cell_row.get("witness")
        if not isinstance(witness, list) or len(witness) != 2:
            raise CheckError("cell witness missing")
        if sign_code(points, (rational(witness[0]), rational(witness[1]))) != expected_mask:
            raise CheckError("cell witness does not realize its mask")
        require_equal(cell_row.get("adjacent_masks_hex"),
                      [hex_mask(neighbor, dimensions) for neighbor in graph[expected_mask]],
                      "false adjacency")
        observed.append(cell_row["mask_hex"])
    require_equal(claim.get("fixed_cell_count"), len(cells), "fixed cell count mismatch")
    require_equal(claim.get("cell_set_sha256"), digest_object(observed),
                  "cell set digest mismatch")
    require_equal(claim.get("abstract_minus_fixed_count"), len(abstract - cells),
                  "abstract/fixed gap mismatch")
    require_equal(claim.get("topology"), graph_invariants(graph), "topology mismatch")
    if claim["topology"]["component_count"] != 1:  # type: ignore[index]
        raise CheckError("fixed cell adjacency graph is disconnected")
    return cells


def classes_by(rows: list[dict[str, object]], field: str,
               output_field: str) -> list[dict[str, object]]:
    groups: dict[str, list[dict[str, object]]] = defaultdict(list)
    for row in rows:
        groups[str(row[field])].append(row)
    return [{
        output_field: signature,
        "parent_masks_hex": sorted({str(row["parent_mask_hex"]) for row in members}),
        "realization_ids": sorted(str(row["id"]) for row in members),
    } for signature, members in sorted(groups.items()) if len(members) > 1]


def verify_level(level: dict[str, object], catalog: dict[str, object],
                 cohort: list[dict[str, object]], child_n: int,
                 parent_n: int) -> dict[str, object]:
    require_equal(level.get("child_n"), child_n, "child level mismatch")
    require_equal(level.get("parent_n"), parent_n, "parent level mismatch")
    abstract_claim = level.get("abstract")
    if not isinstance(abstract_claim, dict):
        raise CheckError("abstract section missing")
    abstract = verify_abstract_claim(abstract_claim, catalog, child_n, parent_n)
    fixed_claim = level.get("fixed")
    if not isinstance(fixed_claim, dict):
        raise CheckError("fixed section missing")
    rows = fixed_claim.get("realizations")
    if not isinstance(rows, list) or len(rows) != len(cohort):
        raise CheckError("fixed realization cohort incomplete")
    cell_sets = {}
    for row, source in zip(rows, cohort):
        if not isinstance(row, dict):
            raise CheckError("malformed fixed realization row")
        cell_sets[str(source["id"])] = verify_fixed_row(
            row, source, child_n, abstract[int(source["parent"])])
    require_equal(fixed_claim.get("realization_count"), len(rows),
                  "fixed realization count mismatch")
    require_equal(fixed_claim.get("all_adjacency_graphs_connected"), True,
                  "connectivity summary mismatch")

    sensitive = 0
    expected_comparisons = []
    for parent in old_states(catalog, parent_n):
        members = [row for row in rows if int(row["parent_mask_hex"], 16) == parent]
        if not members:
            raise CheckError("a parent has no frozen fixed realization")
        union = set().union(*(cell_sets[str(row["id"])] for row in members))
        fiber_groups: dict[str, list[str]] = defaultdict(list)
        wire_groups: dict[str, list[str]] = defaultdict(list)
        for row in members:
            fiber_groups[str(row["cell_set_sha256"])].append(str(row["id"]))
            wire_groups[str(row["wiring_sha256"])].append(str(row["id"]))
        sensitive_here = len(fiber_groups) > 1
        sensitive += int(sensitive_here)
        expected_comparisons.append({
            "abstract_count": len(abstract[parent]),
            "abstract_minus_sampled_union_count": len(abstract[parent] - union),
            "abstract_minus_sampled_union_masks_hex": [
                hex_mask(mask, len(all_pairs(parent_n)))
                for mask in sorted(abstract[parent] - union)],
            "distinct_fixed_fiber_count": len(fiber_groups),
            "distinct_wiring_count": len(wire_groups),
            "fixed_fiber_classes": [
                {"cell_set_sha256": signature, "realization_ids": sorted(ids)}
                for signature, ids in sorted(fiber_groups.items())],
            "parent_mask_hex": hex_mask(parent, len(all_triples(parent_n))),
            "realization_count": len(members),
            "realization_sensitive": sensitive_here,
            "sampled_union_fixed_count": len(union),
            "sampled_union_fixed_masks_hex": [
                hex_mask(mask, len(all_pairs(parent_n))) for mask in sorted(union)],
            "sampled_union_is_full_geomext_claimed": False,
            "wiring_classes": [
                {"realization_ids": sorted(ids), "wiring_sha256": signature}
                for signature, ids in sorted(wire_groups.items())],
        })
    require_equal(level.get("comparison_by_parent"), expected_comparisons,
                  "per-parent comparison/gap/sensitivity mismatch")
    require_equal(fixed_claim.get("sensitive_parent_count"), sensitive,
                  "sensitivity summary mismatch")

    abstract_groups: dict[str, list[str]] = defaultdict(list)
    for parent in old_states(catalog, parent_n):
        vector = [hex_mask(mask, len(all_pairs(parent_n))) for mask in sorted(abstract[parent])]
        abstract_groups[digest_object(vector)].append(
            hex_mask(parent, len(all_triples(parent_n))))
    expected_abstract_collisions = [
        {"compatible_set_sha256": signature, "parent_masks_hex": sorted(parents)}
        for signature, parents in sorted(abstract_groups.items()) if len(parents) > 1]
    require_equal(fixed_claim.get("abstract_fiber_collision_classes"),
                  expected_abstract_collisions, "abstract collision classes mismatch")
    require_equal(fixed_claim.get("fixed_fiber_collision_classes"),
                  classes_by(rows, "cell_set_sha256", "cell_set_sha256"),
                  "fixed fiber collision classes mismatch")
    require_equal(fixed_claim.get("wiring_collision_classes"),
                  classes_by(rows, "wiring_sha256", "wiring_sha256"),
                  "wiring collision classes mismatch")
    for collision in classes_by(rows, "wiring_sha256", "wiring_sha256"):
        member_ids = set(collision["realization_ids"])
        fiber_hashes = {str(row["cell_set_sha256"]) for row in rows
                        if row["id"] in member_ids}
        if len(fiber_hashes) != 1:
            raise CheckError("same labeled wiring has distinct fixed fibers")
    return {
        "abstract_edges": sum(len(links) for links in abstract.values()),
        "cells": sum(len(cell_set) for cell_set in cell_sets.values()),
        "realizations": len(rows),
        "sensitive_parents": sensitive,
    }


def verify(document: dict[str, object], spec_path: Path,
           sources: dict[str, str], catalog: dict[str, object],
           fixed: dict[str, object]) -> dict[str, object]:
    require_equal(document.get("schema_version"), 1, "certificate schema mismatch")
    require_equal(document.get("outcome"), "ATLAS-56-LAND", "outcome mismatch")
    require_equal(document.get("frozen_spec_sha256"), digest_file(spec_path),
                  "frozen spec hash mismatch")
    require_equal(document.get("frozen_input_sha256"), sources,
                  "frozen input ledger mismatch")
    require_equal(document.get("claims"), {
        "allowed": "computational_evidence",
        "sampled_realizations_exhaust_geomext": False,
        "uniform_erdos_szekeres_formula_proved": False,
    }, "claim ceiling mismatch")
    require_equal(document.get("model"), {
        "abstract": "all LastExtensionCompatible pair-link masks over labeled OneChangeOn parents",
        "fixed": "all full-dimensional strict sign cells of old pair-lines in x greater than max parent x for the frozen rational coordinate cohorts",
        "object_tiers_kept_distinct": True,
        "scope": "child n=4,5,6 only; parent n=3,4,5",
    }, "model statement mismatch")
    preflight = check_admitted_preflight(fixed)
    require_equal(document.get("preflight"), preflight, "admitted preflight report mismatch")
    levels = document.get("levels")
    if not isinstance(levels, dict) or set(levels) != {"4", "5", "6"}:
        raise CheckError("certificate levels are not exactly 4,5,6")
    cohorts = expected_cohorts(fixed)
    positive = {}
    for child_n, parent_n in LEVELS:
        level = levels[str(child_n)]
        if not isinstance(level, dict):
            raise CheckError("malformed level")
        positive[str(child_n)] = verify_level(
            level, catalog, cohorts[child_n], child_n, parent_n)

    expected_summary = {
        "abstract_edge_count_by_child_n": {
            key: positive[key]["abstract_edges"] for key in ("4", "5", "6")},
        "all_adjacency_graphs_connected": True,
        "all_wiring_replays_exact": True,
        "child_levels": [4, 5, 6],
        "fixed_cell_count": sum(positive[key]["cells"] for key in positive),
        "fixed_realization_count": sum(positive[key]["realizations"] for key in positive),
        "n7_embargo_observed": True,
        "sensitive_parent_count_by_child_n": {
            key: positive[key]["sensitive_parents"] for key in ("4", "5", "6")},
    }
    require_equal(document.get("summary"), expected_summary, "global summary mismatch")
    convention = {
        "boundary_order": "labeled pair-lines bottom-to-top immediately right of max parent x",
        "labels": "canonical i-j labels in lexicographic pair-bit order",
        "sign_bit_one": "positive orientation, equivalently above the labeled pair-line",
        "slices": "strict crossing-x order; every equal-x collection is one atomic slice of disjoint bottom-to-top concurrent blocks",
        "simultaneous_replay": "reverse every block from the common pre-slice order before collecting any new prefix; no partial-slice cells",
    }
    require_equal(document.get("wiring_sufficiency"), {
        "convention": convention,
        "counterexample": None,
        "representation_contains_fiber_data": False,
        "same_wiring_distinct_fiber_collision": None,
        "tested_fixed_realizations": expected_summary["fixed_realization_count"],
        "verdict": "sufficient_for_every_frozen_fixed_realization",
    }, "wiring sufficiency verdict mismatch")
    return {
        "levels": positive,
        "preflight": preflight,
        "summary": expected_summary,
        "wiring_convention": convention,
    }


def rejected(candidate: dict[str, object], spec_path: Path, sources: dict[str, str],
             catalog: dict[str, object], fixed: dict[str, object]) -> bool:
    try:
        verify(candidate, spec_path, sources, catalog, fixed)
    except (CheckError, AssertionError, KeyError, TypeError, ValueError, IndexError):
        return True
    return False


def corruption_controls(document: dict[str, object], spec_path: Path,
                        sources: dict[str, str], catalog: dict[str, object],
                        fixed: dict[str, object]) -> dict[str, bool]:
    coordinate = deepcopy(document)
    first = coordinate["levels"]["4"]["fixed"]["realizations"][0]  # type: ignore[index]
    first["points"][1][0] = first["points"][0][0]

    line_label = deepcopy(document)
    line_label["levels"]["4"]["fixed"]["realizations"][0]["pair_labels"][0] = "9-9"  # type: ignore[index]

    sign_mask = deepcopy(document)
    sign_mask["levels"]["4"]["fixed"]["realizations"][0]["cells"][0]["mask_hex"] = "fff"  # type: ignore[index]

    omitted = deepcopy(document)
    omitted["levels"]["4"]["fixed"]["realizations"][0]["cells"].pop()  # type: ignore[index]

    false_adjacency = deepcopy(document)
    bad_cell = false_adjacency["levels"]["4"]["fixed"]["realizations"][0]["cells"][0]  # type: ignore[index]
    bad_cell["adjacent_masks_hex"].append(bad_cell["mask_hex"])

    false_wiring = deepcopy(document)
    boundary = false_wiring["levels"]["4"]["fixed"]["realizations"][0]["wiring"]["boundary_order"]  # type: ignore[index]
    boundary[0], boundary[1] = boundary[1], boundary[0]

    return {
        "coordinate_corruption_rejected": rejected(
            coordinate, spec_path, sources, catalog, fixed),
        "false_adjacency_rejected": rejected(
            false_adjacency, spec_path, sources, catalog, fixed),
        "false_wiring_rejected": rejected(
            false_wiring, spec_path, sources, catalog, fixed),
        "line_label_corruption_rejected": rejected(
            line_label, spec_path, sources, catalog, fixed),
        "omitted_cell_rejected": rejected(
            omitted, spec_path, sources, catalog, fixed),
        "sign_mask_corruption_rejected": rejected(
            sign_mask, spec_path, sources, catalog, fixed),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", type=Path, default=Path("."))
    parser.add_argument("--frozen-spec", type=Path, required=True)
    parser.add_argument("--catalog", type=Path, required=True)
    parser.add_argument("--fixed-certificate", type=Path, required=True)
    parser.add_argument("--certificate", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()

    spec, sources = verify_sources(args.repo_root.resolve(), args.frozen_spec)
    ledger = spec["frozen_input_sha256"]
    if digest_file(args.catalog) != ledger[
            "runs/agents/20260814-local-constraint-hierarchy/census/census-56/catalog.json"]:  # type: ignore[index]
        raise CheckError("explicit catalog is not frozen")
    if digest_file(args.fixed_certificate) != ledger[
            "runs/agents/20260814-local-realizability-456/fixed-extension/certificate.json"]:  # type: ignore[index]
        raise CheckError("explicit fixed certificate is not frozen")
    catalog = json_object(args.catalog)
    fixed = json_object(args.fixed_certificate)
    certificate = json_object(args.certificate)
    positive = verify(certificate, args.frozen_spec, sources, catalog, fixed)
    controls = corruption_controls(
        certificate, args.frozen_spec, sources, catalog, fixed)
    if not all(controls.values()):
        raise CheckError(f"corruption control escaped: {controls}")
    report = {
        "certificate_sha256": digest_file(args.certificate),
        "checker_method": (
            "independent exact vertical-slab probes plus separately reconstructed "
            "labeled atomic crossing-block wiring"
        ),
        "controls": controls,
        "frozen_spec_sha256": digest_file(args.frozen_spec),
        "n7_embargo_observed": True,
        "ok": True,
        "positive": positive,
        "schema_version": 1,
    }
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print("geometric extension-fiber atlas verified independently")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
