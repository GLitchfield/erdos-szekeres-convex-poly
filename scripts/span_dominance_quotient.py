#!/usr/bin/env python3
"""Canonical finite encoding of the span-dominance incidence candidate.

For an open exact endpoint-span record, the candidate retains:

* the histogram of exact cup/cap rank labels, with every count clipped at k;
* the sidewise Pareto-frontier tags licensed by ``SpanDominance.lean``; and
* the multiset of endpoint-local incidence types, again with multiplicities
  clipped at k.

An endpoint incidence remembers only whether an incident pair has cup rank at
least three and/or cap rank at least three, together with all dominance tags
carried by that pair.  It deliberately forgets ambient endpoint identities
and the exact rank attached to each individual pair.  Exact ranks survive only
through the clipped global histogram.

The byte encoding is canonical and depends on k but has no n-indexed output
field.  This module is the producer implementation.  The independent checker
duplicates the definition and imports neither this file nor its producer.
"""

from __future__ import annotations

from collections import Counter
import itertools


def _frontier_bit(direction: int, color: int, rank: int, k: int) -> int:
    width = max(0, k - 3)
    return 1 << (direction * 2 * width + color * width + rank - 3)


def encode_span_dominance_quotient(record: bytes, n: int, k: int) -> bytes:
    """Encode one raw span-rank footprint into the finite quotient candidate."""
    if not 0 <= n <= 65535:
        raise ValueError("n must lie between 0 and 65535")
    if not 4 <= k <= 255:
        raise ValueError("k must lie between 4 and 255")
    pairs = tuple(itertools.combinations(range(n), 2))
    if len(record) != 1 + len(pairs):
        raise ValueError("record length does not match n")
    if record[0]:
        return bytes((1,))

    pair_index = {pair: index for index, pair in enumerate(pairs)}
    frontier_masks = [0] * len(pairs)
    for color in (0, 1):
        ranks = tuple(
            ((value & 15) if color == 0 else (value >> 4))
            for value in record[1:]
        )
        for rank in range(3, k):
            for right in range(n):
                for left in range(right - 1, -1, -1):
                    position = pair_index[(left, right)]
                    if ranks[position] >= rank:
                        frontier_masks[position] |= _frontier_bit(0, color, rank, k)
                        break
            for left in range(n):
                for right in range(left + 1, n):
                    position = pair_index[(left, right)]
                    if ranks[position] >= rank:
                        frontier_masks[position] |= _frontier_bit(1, color, rank, k)
                        break

    endpoint_incidence = [set() for _ in range(n)]
    for position, (left, right) in enumerate(pairs):
        raw_label = record[1 + position]
        cup_active = int((raw_label & 15) >= 3)
        cap_active = int((raw_label >> 4) >= 3)
        coarse_label = cup_active | (cap_active << 1)
        if coarse_label == 0:
            continue
        mask = frontier_masks[position]
        endpoint_incidence[left].add((0, coarse_label, mask))
        endpoint_incidence[right].add((1, coarse_label, mask))

    endpoint_types = Counter(tuple(sorted(incidence)) for incidence in endpoint_incidence)
    mask_width = (4 * (k - 3) + 7) // 8
    output = bytearray((0,))
    raw_histogram = Counter(record[1:])
    output.extend(min(k, raw_histogram.get(label, 0)) for label in range(256))
    output.extend(len(endpoint_types).to_bytes(2, "little"))
    for signature, multiplicity in sorted(endpoint_types.items()):
        output.append(min(k, multiplicity))
        output.extend(len(signature).to_bytes(2, "little"))
        for role, coarse_label, frontier_mask in signature:
            output.append(role | (coarse_label << 1))
            output.extend(frontier_mask.to_bytes(mask_width, "little"))
    return bytes(output)
