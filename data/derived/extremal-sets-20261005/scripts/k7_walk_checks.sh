#!/bin/bash
PY=/home/gavin/git/erdos-szekeres-convex-poly/runs/etv-cc-20260930/.venv/bin/python
D=/home/gavin/git/erdos-szekeres-convex-poly/runs/claude-extremal-20261005
$PY $D/halving.py $D/fw7.jsonl 152 1
$PY $D/cube_label.py $D/fw7.jsonl 152 gon
python3 $D/layers.py $D/fw7.jsonl 152
