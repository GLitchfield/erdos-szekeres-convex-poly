#!/usr/bin/env python3
"""Deterministic rational controls for the explicit Tóth--Valtr chart."""

from fractions import Fraction
from itertools import combinations


Point = tuple[Fraction, Fraction]


def det(a: Point, b: Point, c: Point) -> Fraction:
    return (b[0] - a[0]) * (c[1] - a[1]) - (
        b[1] - a[1]
    ) * (c[0] - a[0])


def quarter(anchor: Point, p: Point) -> Point:
    return (-(p[1] - anchor[1]), p[0] - anchor[0])


def project(delta: Fraction, p: Point) -> Point:
    denominator = p[1] + delta
    return (p[0] / denominator, p[1] / denominator)


def is_general(points: tuple[Point, ...]) -> bool:
    return all(det(*triple) != 0 for triple in combinations(points, 3))


def inside_triangle(p: Point, a: Point, b: Point, c: Point) -> bool:
    triangle_sign = det(a, b, c)
    signs = (det(a, b, p), det(b, c, p), det(c, a, p))
    if triangle_sign > 0:
        return all(value > 0 for value in signs)
    return all(value < 0 for value in signs)


def is_convex(points: tuple[Point, ...]) -> bool:
    for index, point in enumerate(points):
        others = points[:index] + points[index + 1 :]
        if any(inside_triangle(point, *triangle) for triangle in combinations(others, 3)):
            return False
    return True


def is_cap(points: tuple[Point, ...]) -> bool:
    ordered = tuple(sorted(points))
    return all(det(*triple) < 0 for triple in combinations(ordered, 3))


def choose_delta(centered: tuple[Point, ...]) -> Fraction:
    radial = sorted(centered, key=lambda p: p[0] / p[1])
    delta = Fraction(1)
    for _ in range(80):
        projected = tuple(project(delta, p) for p in radial)
        if all(projected[i][0] < projected[i + 1][0] for i in range(len(projected) - 1)):
            return delta
        delta /= 2
    raise AssertionError("failed to stabilize the finite radial order")


def check_configuration(points: tuple[Point, ...]) -> tuple[int, int]:
    assert is_general(points)
    assert all(points[i][0] < points[i + 1][0] for i in range(len(points) - 1))
    anchor = points[0]
    centered_all = tuple(quarter(anchor, p) for p in points)
    centered = centered_all[1:]
    assert all(p[1] > 0 for p in centered)
    assert len({p[0] / p[1] for p in centered}) == len(centered)
    delta = choose_delta(centered)
    transformed_all = tuple(project(delta, p) for p in centered_all)
    transformed = transformed_all[1:]

    for i, j, k in combinations(range(len(points)), 3):
        lhs = det(transformed_all[i], transformed_all[j], transformed_all[k])
        a, b, c = centered_all[i], centered_all[j], centered_all[k]
        denominator = (a[1] + delta) * (b[1] + delta) * (c[1] + delta)
        rhs = delta * det(a, b, c) / denominator
        assert lhs == rhs
        assert (lhs > 0) == (det(points[i], points[j], points[k]) > 0)

    convexity_checks = 0
    for size in range(3, len(points) + 1):
        for indices in combinations(range(len(points)), size):
            source = tuple(points[i] for i in indices)
            image = tuple(transformed_all[i] for i in indices)
            assert is_convex(source) == is_convex(image)
            convexity_checks += 1

    cap_checks = 0
    for size in range(3, len(transformed) + 1):
        for cap in combinations(transformed, size):
            if is_cap(cap):
                assert is_convex(((Fraction(0), Fraction(0)),) + cap)
                cap_checks += 1
    assert cap_checks > 0

    corrupted = list(transformed_all)
    corrupted[-1] = (corrupted[-1][0] + Fraction(1, 97), corrupted[-1][1])
    assert any(
        det(corrupted[i], corrupted[j], corrupted[k])
        != delta
        * det(centered_all[i], centered_all[j], centered_all[k])
        / (
            (centered_all[i][1] + delta)
            * (centered_all[j][1] + delta)
            * (centered_all[k][1] + delta)
        )
        for i, j, k in combinations(range(len(points)), 3)
    )
    return convexity_checks, cap_checks


def main() -> None:
    height_sets = (
        (0, 1, 4, 9, 16, 25, 36),
        (0, -1, -4, -9, -16, -25, -36),
        (0, 2, 9, 1, 15, 6, 25),
    )
    totals = [0, 0]
    for heights in height_sets:
        points = tuple((Fraction(i), Fraction(y)) for i, y in enumerate(heights))
        convexity, caps = check_configuration(points)
        totals[0] += convexity
        totals[1] += caps
    print(
        "toth-valtr rational controls passed: "
        f"configurations={len(height_sets)} "
        f"convexity_subsets={totals[0]} cap_extensions={totals[1]} "
        "corruptions_rejected=3"
    )


if __name__ == "__main__":
    main()
