"""Run the pure finite-context endpoint operations on a frozen profile."""
import json
from pathlib import Path

from harness.research.endpoint_profiles import (
    child_slot_barriers, expand_run_profile, refine_slot_profile,
)


def main():
    fixture = json.loads(Path(__file__).with_name('endpoint-profiles-v1.json').read_text())
    row = fixture['rows'][0]
    caps, cups, barriers = expand_run_profile(
        row['word'], row['parent']['run_caps'], row['parent']['run_cups'])
    chosen = row['children'][0]
    refined = refine_slot_profile(caps, cups, chosen['keep'], chosen['side'],
                                  chosen['opposite_max'], row['case'][2] - 1)
    result = {'caps': refined[0], 'cups': refined[1],
              'barriers': child_slot_barriers(barriers, chosen['keep'])}
    assert result == {k: tuple(tuple(v) for v in chosen['expected'][k])
                      if k != 'barriers' else tuple(chosen['expected'][k])
                      for k in ('caps', 'cups', 'barriers')}
    print(json.dumps(result))


if __name__ == '__main__':
    main()
