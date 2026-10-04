#!/usr/bin/env python3
"""Guarded example of classical labels and solver-free complete-triple metrics."""
import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
from harness.research.binary_labels import classical_pascal_labels, binary_label_coloring
from harness.research.triple_metrics import FiniteTripleColoring


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--out', type=Path)
    args = parser.parse_args()
    labels = classical_pascal_labels(3, 3)
    value = FiniteTripleColoring(binary_label_coloring(labels), len(labels))
    report = {'diagnostic': True, 'terminal': True, 'labels': labels,
              'cup_cap': value.metrics(), 'strong': value.strong_number()}
    text = json.dumps(report, sort_keys=True) + '\n'
    if args.out is not None:
        args.out.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
