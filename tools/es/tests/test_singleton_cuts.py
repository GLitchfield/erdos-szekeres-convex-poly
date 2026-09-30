from __future__ import annotations

import json
from pathlib import Path

import pytest

from harness.research.context_bound import compiled_evaluator
from harness.research.singleton_cuts import singleton_cut_values


ROOT = Path(__file__).resolve().parents[3]
FIXTURE = ROOT / "harness/research/examples/singleton-cuts-v1.json"


def test_preserves_frozen_cut_values_couplings_and_zero_parts():
    fixture = json.loads(FIXTURE.read_text())
    assert fixture["semantics"] == "context-bound-zero-children-c-v1"
    for case in fixture["cases"]:
        row = {key: value for key, value in case.items() if key != "choices"}
        evaluate = compiled_evaluator(row["a"], row["u"], row["k"], persistent=True)
        try:
            values = singleton_cut_values(evaluate, row)
        finally:
            evaluate.close()
        assert [list(value) for value in values] == case["choices"]
        children = row["word"].count("S")
        assert len(values) == children * 2 * (row["k"] - 2)


def test_rejects_empty_complement_and_invalid_coupling_domain_before_evaluation():
    def must_not_evaluate(*_args):
        raise AssertionError("invalid cut was evaluated")

    row = {"word": ("S",), "maxima": (), "a": 4, "u": 4, "k": 5, "chosen": "lower"}
    with pytest.raises(ValueError, match="at least two S"):
        singleton_cut_values(must_not_evaluate, row)
    for invalid_k in (2, True, 3.0):
        with pytest.raises(ValueError, match="integer k >= 3"):
            singleton_cut_values(must_not_evaluate, {**row, "word": ("S", "S"), "k": invalid_k})


def test_rejects_mismatched_compiled_globals():
    row = {"word": ("S", (1, "lower"), "S"), "maxima": (1,),
           "a": 4, "u": 4, "k": 5, "chosen": "lower"}
    evaluate = compiled_evaluator(4, 4, 6, persistent=True)
    try:
        with pytest.raises(ValueError, match="evaluator k"):
            singleton_cut_values(evaluate, row)
    finally:
        evaluate.close()


def test_does_not_truncate_evaluator_overflow():
    def overflow(*_args):
        raise OverflowError("fixture overflow")

    row = {"word": ("S", "S"), "maxima": (), "a": 4, "u": 4, "k": 5, "chosen": "lower"}
    with pytest.raises(OverflowError, match="fixture overflow"):
        singleton_cut_values(overflow, row)
