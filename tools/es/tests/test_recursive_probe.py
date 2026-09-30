from __future__ import annotations

from copy import deepcopy
import importlib
import json
import math
import os
from pathlib import Path
import random
import shutil
import time

import pytest


ROOT = Path(__file__).resolve().parents[3]
EXAMPLES = ROOT / "harness" / "research" / "examples"


def load_fixture():
    spec = json.loads((EXAMPLES / "recursive-cut-small.json").read_text())
    expected = json.loads((EXAMPLES / "recursive-cut-small.expected.json").read_text())
    return spec, expected


def jsonable(value):
    if isinstance(value, tuple):
        return [jsonable(item) for item in value]
    if isinstance(value, list):
        return [jsonable(item) for item in value]
    if isinstance(value, dict):
        return {key: jsonable(item) for key, item in value.items()}
    return value


def word(value):
    return tuple("S" if token == "S" else tuple(token) for token in value)


def test_shared_primitives_match_checked_in_golden_arithmetic():
    from harness.research import primitives

    fixture = json.loads((EXAMPLES / "primitives-golden-v1.json").read_text())
    assert fixture["semantics"] == "rank-primitives-v1"
    assert "not a Lean equivalence" in fixture["semantic_caveat"]
    assert set(fixture["provenance"]) == {
        "extension", "clip", "P", "part", "ordered_cover", "sole_opposite_normalize"}

    ext = fixture["extension"]
    args = ext["input"]
    assert primitives.extension(word(args["word"]), args["depth"], args["side"],
                                args["p"], args["left"]) == ext["expected"]
    cp = fixture["clip_and_potential"]
    rows, keep = cp["input"]["rows"], set(cp["input"]["keep"])
    assert primitives.clip(rows, keep, 0) == cp["expected"]["clip_axis_0"]
    assert primitives.clip(rows, keep, 1) == cp["expected"]["clip_axis_1"]
    assert primitives.P(rows) == cp["expected"]["P"]
    for case in fixture["parts"]:
        source = case["source"] | {"word": word(case["source"]["word"]),
                                   "maxima": tuple(case["source"]["maxima"])}
        actual = primitives.part(source, tuple(case["keep"]), case["side"], case["maximum"])
        assert jsonable(actual) == case["expected"]
    cover = fixture["ordered_cover"]
    assert primitives.ordered_cover(cover["input"]) == cover["expected"]
    normalize = fixture["sole_opposite_normalize"]
    source = normalize["input"] | {"word": word(normalize["input"]["word"]),
                                    "maxima": tuple(normalize["input"]["maxima"])}
    assert jsonable(primitives.sole_opposite_normalize(source)) == normalize["expected"]


def test_small_fixture_matches_retained_extreme_next_cases():
    from harness.research.recursive_cut import evaluate

    spec, expected = load_fixture()
    assert expected["provenance"]["generator_and_candidate"].endswith("extreme_next_probe.py")
    assert "not a Lean equivalence" in expected["semantic_caveat"]
    result = evaluate(spec)
    assert result["outcome"] == expected["outcome"]
    assert result["stop_reason"] == expected["stop_reason"]
    assert result["coverage"] == expected["coverage"]
    selected = []
    for row in result["sample_rows"]:
        selected.append({
            "case_index": row["case_index"], "word": row["source"]["word"],
            "maxima": row["source"]["maxima"], "keep": row["layout"]["keep"],
            "removed": row["layout"]["removed"],
            "control_bounds": [row["control"]["A_bound"], row["control"]["B_bound"]],
            "target_bounds": [row["target"]["A_bound"], row["target"]["B_bound"]],
        })
    assert selected == expected["rows"]
    assert result["limits"]["memory"] == "1G"
    assert result["lean_equivalence"] is False
    assert result["lean_refutation"] is False
    assert result["finite_negative_has_proof_credit"] is False


def test_semantics_are_explicit_and_preserve_zero_child_behavior():
    from harness.research.primitives import part
    from harness.research.recursive import evaluator

    _, expected = load_fixture()
    case = expected["zero_child_regression"]
    source = case["source"] | {"chosen": "lower"}
    word = tuple("S" if token == "S" else tuple(token) for token in source["word"])
    maxima = tuple(source["maxima"])
    for semantics in ("context-bound-zero-children-v1", "historical-f2-v1"):
        rec = evaluator(source["a"], source["u"], source["k"], semantics=semantics, cache_size=64)
        assert int(rec(word, maxima)) == case[semantics]
    literal = evaluator(3, 3, 3, semantics="context-bound-zero-children-v1", cache_size=64)
    lower = part(source, (0,), "lower", 1)
    upper = part(source, (2,), "upper", 1)
    assert int(literal(lower["word"], lower["maxima"])) == case["lower_part"]
    assert int(literal(upper["word"], upper["maxima"])) == case["upper_part"]
    with pytest.raises(ValueError, match="explicit registered"):
        evaluator(3, 3, 3, semantics="implicit")


def test_evaluator_factory_restores_legacy_cache_default():
    from harness.research.recursive import evaluator

    evaluator(3, 3, 3, semantics="historical-f2-v1", cache_size=17)
    legacy = importlib.import_module("decomposable_recursive_formula")
    sentinel = legacy.CACHE_SIZE
    rec = evaluator(3, 3, 3, semantics="historical-f2-v1", cache_size=19)
    assert legacy.CACHE_SIZE is sentinel
    assert rec.cache_info().maxsize == 19


@pytest.mark.skipif(shutil.which("cc") is None, reason="C compiler unavailable")
def test_compiled_context_bound_matches_python_random_fixture():
    from harness.research.recursive import evaluator

    fixture = json.loads((EXAMPLES / "context-bound-c-v1.json").read_text())
    rng = random.Random(fixture["seed"])
    limits = fixture["generator"]
    for a, u, k in fixture["cases"]:
        python_bound = evaluator(a, u, k, semantics=fixture["python_semantics"], cache_size=100000)
        compiled_bound = evaluator(a, u, k, semantics=fixture["compiled_semantics"], cache_size=16000)
        for _ in range(fixture["samples_per_case"]):
            s_count = rng.randint(limits["s_min"], limits["s_max"])
            external_count = rng.randint(0, limits["external_max"])
            depth = rng.randint(1 if external_count else 0, limits["depth_max"])
            sides = {level: rng.choice(("lower", "upper")) for level in range(1, depth + 1)}
            word = ["S"] * s_count
            word += [(level := rng.randint(1, depth), sides[level]) for _ in range(external_count)]
            rng.shuffle(word)
            maxima = tuple(rng.randint(1, k - 2) for _ in range(depth))
            word = tuple(word)
            assert compiled_bound(word, maxima) == int(python_bound(word, maxima)), (a, u, k, word, maxima)
    counterexample = fixture["end_cut_counterexample"]
    word = tuple("S" if token == "S" else tuple(token) for token in counterexample["word"])
    maxima = tuple(counterexample["maxima"])
    a, u, k = counterexample["case"]
    expected = counterexample["expected_bound"]
    assert evaluator(a, u, k, semantics=fixture["python_semantics"])(word, maxima) == expected
    assert evaluator(a, u, k, semantics=fixture["compiled_semantics"])(word, maxima) == expected
    assert evaluator(a, u, k, semantics=fixture["compiled_semantics"], cache_size=1)(word, maxima) == expected
    zero_word = ("S", (1, "lower"), "S", (2, "upper"), "S")
    zero_maxima = (0, 0)
    for a, u, k in fixture["cases"]:
        expected = evaluator(a, u, k, semantics=fixture["python_semantics"])(zero_word, zero_maxima)
        assert evaluator(a, u, k, semantics=fixture["compiled_semantics"])(zero_word, zero_maxima) == expected


@pytest.mark.skipif(shutil.which("cc") is None, reason="C compiler unavailable")
def test_compiled_evaluator_runs_through_registered_probe_interface():
    from harness.research.recursive_cut import evaluate, replay

    spec, _ = load_fixture()
    python_result = evaluate(spec)
    spec["semantics"] = "context-bound-zero-children-c-v1"
    compiled_result = evaluate(spec)
    assert compiled_result["outcome"] == python_result["outcome"]
    assert compiled_result["stop_reason"] == python_result["stop_reason"]
    assert compiled_result["coverage"] == python_result["coverage"]
    assert compiled_result["sample_rows"] == python_result["sample_rows"]
    assert compiled_result["cache"]["hits"] == 0
    assert compiled_result["cache"]["misses"] > 0
    assert compiled_result["cache"]["maxsize"] == spec["evaluator"]["cache_size"]
    assert compiled_result["cache"]["currsize"] == 0
    witness_spec = deepcopy(spec)
    witness_spec["candidate"]["target"]["budget"] = 0
    witness = evaluate(witness_spec)["witness"]
    checked = replay(witness)
    assert checked["replayed"] is True
    assert checked["computed"]["target"]["sum"] == 7
    assert checked["computed"]["control"]["sum"] == 7


@pytest.mark.skipif(shutil.which("cc") is None, reason="C compiler unavailable")
def test_compiled_context_bound_rejects_overflow_and_out_of_range_inputs():
    import ctypes

    from harness.research import context_bound
    from harness.research.recursive import evaluator

    with pytest.raises(ValueError, match="positive C integers"):
        evaluator(1 << 40, 4, 5, semantics="context-bound-zero-children-c-v1")
    # The public C API accepts a null maxima pointer exactly when its depth is zero.
    word = (ctypes.c_int * 2)(0, 0)
    out = ctypes.c_int64()
    assert context_bound._load_library().es_context_bound(
        3, 4, 5, word, 2, None, 0, 1, ctypes.byref(out)) == 0
    exact = evaluator(35, 35, 67, semantics="context-bound-zero-children-c-v1")
    assert exact(("S",), ()) == math.comb(66, 33)
    bound = evaluator(36, 36, 69, semantics="context-bound-zero-children-c-v1")
    with pytest.raises(OverflowError, match="signed 64-bit"):
        bound(("S",), ())


def test_compiled_context_bound_rejects_insecure_cache_directory(tmp_path, monkeypatch):
    from harness.research import context_bound

    directory = tmp_path / f"es-context-bound-{os.getuid()}"
    directory.mkdir(mode=0o777)
    directory.chmod(0o777)
    monkeypatch.setattr(context_bound.tempfile, "gettempdir", lambda: str(tmp_path))
    monkeypatch.setattr(context_bound, "_LIBRARY", None)
    with pytest.raises(RuntimeError, match="unsafe.*cache directory"):
        context_bound._load_library()


def test_witness_replay_recomputes_both_couplings_and_rejects_tampering():
    from harness.research.recursive_cut import evaluate, replay

    spec, _ = load_fixture()
    spec["candidate"]["target"]["budget"] = 0
    result = evaluate(spec)
    assert result["outcome"] == "witness_found"
    assert result["coverage"]["completed"] == 1
    checked = replay(result["witness"])
    assert checked["replayed"] is True
    assert checked["computed"]["target"]["sum"] == 7
    assert checked["computed"]["control"]["sum"] == 7
    assert checked["lean_refutation"] is False
    tampered = deepcopy(result["witness"])
    tampered["layout"]["removed"] = tampered["layout"]["keep"]
    with pytest.raises(ValueError, match="partition"):
        replay(tampered)


def test_parameter_validation_rejects_unregistered_or_unbounded_inputs():
    from harness.research.recursive_cut import evaluate

    spec, _ = load_fixture()
    changes = [
        (("semantics",), "implicit"),
        (("domain",), "all_contexts"),
        (("generator", "child_counts"), [1]),
        (("candidate", "target", "n"), 2),
        (("budget", "memory"), "unlimited"),
        (("budget", "seconds"), float("nan")),
        (("evaluator", "per_case_seconds"), 61),
    ]
    for path, value in changes:
        invalid = deepcopy(spec)
        target = invalid
        for key in path[:-1]:
            target = target[key]
        target[path[-1]] = value
        with pytest.raises(ValueError):
            evaluate(invalid)


def test_per_case_timeout_is_recorded_and_handler_is_restored(monkeypatch):
    from harness.research import recursive_cut

    spec, _ = load_fixture()
    spec["budget"] = {"cases": 1, "seconds": 0.2, "memory": "1G"}
    spec["evaluator"]["per_case_seconds"] = 0.01

    class SlowEvaluator:
        def __call__(self, *_):
            time.sleep(0.1)
            return 0

        def cache_clear(self):
            pass

        def cache_info(self):
            return type("CacheInfo", (), {"hits": 0, "misses": 0, "maxsize": 1, "currsize": 0})()

    monkeypatch.setattr(recursive_cut, "evaluator", lambda *args, **kwargs: SlowEvaluator())
    result = recursive_cut.evaluate(spec)
    assert result["outcome"] == "timeout"
    assert result["coverage"]["admitted"] == 1
    assert result["coverage"]["completed"] == 0
    assert result["coverage"]["timeouts"] == 1
