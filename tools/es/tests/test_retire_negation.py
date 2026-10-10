"""The refutation rewrite negates the conclusion after the TOP-LEVEL colon, not after the last colon
(which may belong to an ∃/∀ binder inside the conclusion)."""
from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from es.commands.node import top_level_colon  # noqa: E402


def test_top_level_colon_skips_binders_and_exists():
    sig = " {n : ℕ} (χ : TripleColoring n) (h : ¬P χ) : ∃ A : Finset (Fin n), Q A ∧ R (f : Fin n) "
    i = top_level_colon(sig)
    assert sig[i + 1:].strip().startswith("∃ A : Finset")


def test_top_level_colon_ignores_assign_and_angle_brackets():
    sig = " (t : ⟨a, b : Fin n⟩) : S t "
    assert sig[top_level_colon(sig) + 1:].strip() == "S t"
    assert top_level_colon(" (x : Nat) ") == -1
