#!/usr/bin/env python3
"""Exact rational controls for the Suk adjacent-region finite kernel."""

from fractions import Fraction
from itertools import combinations, permutations


Point = tuple[Fraction, Fraction]


def orientation(a: Point, b: Point, c: Point) -> Fraction:
    return (b[0] - a[0]) * (c[1] - a[1]) - (
        b[1] - a[1]
    ) * (c[0] - a[0])


def in_support(
    previous: Point, left: Point, right: Point, next_point: Point, p: Point
) -> bool:
    return (
        orientation(left, right, p) > 0
        and orientation(previous, left, p) < 0
        and orientation(right, next_point, p) < 0
    )


def in_triangle(a: Point, b: Point, c: Point, p: Point) -> bool:
    triangle_sign = orientation(a, b, c)
    signs = (
        orientation(a, b, p),
        orientation(b, c, p),
        orientation(c, a, p),
    )
    if triangle_sign > 0:
        return all(value >= 0 for value in signs)
    return all(value <= 0 for value in signs)


def is_chain(base_left: Point, base_right: Point, points: tuple[Point, ...]) -> bool:
    return all(
        in_triangle(base_left, base_right, p, q)
        or in_triangle(base_left, base_right, q, p)
        for p, q in combinations(points, 2)
    )


def in_general_position(points: tuple[Point, ...]) -> bool:
    return all(orientation(*triple) != 0 for triple in combinations(points, 3))


def convex_hull(points: tuple[Point, ...]) -> tuple[Point, ...]:
    ordered = sorted(set(points))

    def half(sequence: list[Point]) -> list[Point]:
        result: list[Point] = []
        for point in sequence:
            while (
                len(result) >= 2
                and orientation(result[-2], result[-1], point) <= 0
            ):
                result.pop()
            result.append(point)
        return result

    return tuple(half(ordered)[:-1] + half(list(reversed(ordered)))[:-1])


def in_convex_position(points: tuple[Point, ...]) -> bool:
    return in_general_position(points) and len(convex_hull(points)) == len(set(points))


def same_arrangement_cell(
    anchor: Point, replacement: Point, triple: tuple[Point, Point, Point]
) -> bool:
    def replace(point: Point) -> Point:
        return replacement if point == anchor else point

    source = (anchor,) + triple
    return all(
        (orientation(replace(a), replace(b), replace(c)) > 0)
        == (orientation(a, b, c) > 0)
        and (orientation(replace(a), replace(b), replace(c)) < 0)
        == (orientation(a, b, c) < 0)
        for a, b, c in permutations(source, 3)
    )


def same_strict_side(a: Point, b: Point, c: Point, d: Point) -> bool:
    return orientation(a, b, c) * orientation(a, b, d) > 0


def check_certificate(left: tuple[Point, ...], right: tuple[Point, ...]) -> bool:
    cap = tuple((Fraction(i), Fraction(-(i * i))) for i in range(5))
    anchor = cap[2]
    return (
        all(in_support(*cap[0:4], p) for p in left)
        and all(in_support(*cap[1:5], p) for p in right)
        and is_chain(cap[0], cap[3], left)
        and is_chain(cap[1], cap[4], right)
        and in_general_position((anchor,) + left + right)
        and in_convex_position((anchor,) + left)
        and in_convex_position((anchor,) + right)
        and all(
            same_arrangement_cell(anchor, q, triple)
            for triple in combinations(left, 3)
            for q in right
        )
        and all(
            same_arrangement_cell(anchor, q, triple)
            for triple in combinations(right, 3)
            for q in left
        )
        and all(
            same_strict_side(a, b, c, d) and same_strict_side(c, d, a, b)
            for a, b in combinations(left, 2)
            for c, d in combinations(right, 2)
        )
        and in_convex_position(left + right)
    )


def main() -> None:
    left = (
        (Fraction(5, 4), Fraction(-13, 8)),
        (Fraction(5, 4), Fraction(-3, 2)),
        (Fraction(11, 8), Fraction(-13, 8)),
    )
    right = (
        (Fraction(9, 4), Fraction(-41, 8)),
        (Fraction(19, 8), Fraction(-11, 2)),
        (Fraction(19, 8), Fraction(-43, 8)),
    )
    assert check_certificate(left, right)

    corruptions = []
    changed = list(left)
    changed[0] = (changed[0][0] + Fraction(1, 8), changed[0][1])
    corruptions.append((tuple(changed), right))
    changed = list(left)
    changed[2] = (changed[2][0], changed[2][1] + Fraction(1, 8))
    corruptions.append((tuple(changed), right))
    changed = list(right)
    changed[0] = (changed[0][0], changed[0][1] + Fraction(1, 8))
    corruptions.append((left, tuple(changed)))
    assert all(not check_certificate(*corruption) for corruption in corruptions)

    print(
        "suk adjacent-region rational controls passed: "
        "support_points=6 chain_pairs=6 general_position_triples=35 "
        "arrangement_replacements=6 pair_supports=9 corruptions_rejected=3"
    )


if __name__ == "__main__":
    main()
