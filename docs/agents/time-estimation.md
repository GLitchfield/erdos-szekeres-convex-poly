# Work-time estimation and calibration

Time estimates in this project are empirical forecasts, not task-list theater.
Every substantial forecast must be recorded before execution and closed with
the observed wall time. The canonical ledger is `time-estimates.csv`.

## Required record

For every item forecast at fifteen minutes or more, record:

- a stable ID, category, and concrete deliverable;
- the forecast low and high wall-clock minutes;
- start and finish timestamps;
- actual wall-clock minutes, including model reasoning and tool execution;
- paused minutes caused by user input, host outage, quota, or an obsolete run;
- outcome (`proved`, `refuted`, `partial`, `blocked`, or `maintenance`); and
- a short explanation for material forecast error.

Do not silently discard a row when a theorem is false or a route changes. A
certified counterexample is still completed work and must receive an actual.

## Wall time versus work volume

Plans shown to the user forecast elapsed wall time. Do not obtain that number
by blindly summing task estimates:

- sequential items contribute their sum;
- parallel items contribute the longest overlapping critical path;
- review latency counts only when it actually blocks the next step;
- project builds use measured recent build time, not a generic allowance; and
- speculative proof search receives a stop budget, not a claim that it will
  consume the whole budget.

An `N`-hour queue may contain overflow work, but it must be labeled as backlog
scope unless calibrated elapsed-time data supports the `N`-hour forecast. Do
not idle or prolong a search to make an estimate look accurate.

## Calibration

For a completed row, let

```text
forecast midpoint = (forecast low + forecast high) / 2
error ratio = actual active wall minutes / forecast midpoint
```

`error ratio < 1` means the forecast was too long; `> 1` means it was too
short. After three completed rows in a category, future midpoints must use the
median category error ratio as a multiplier. Until three rows exist, state
that the estimate is uncalibrated and use a wide range rather than presenting
a precise duration.

After every five completed rows, summarize:

- median error ratio overall and by category;
- the fraction whose actual time fell inside the forecast range;
- the largest miss and its cause; and
- one concrete adjustment to future planning.

The useful categories are `lean-routine`, `lean-new-lemma`,
`mathematical-discovery`, `bounded-computation`, `review`, `integration`, and
`mixed-research`. Add a category only when existing ones are genuinely
misleading.

## Session protocol

1. Append the forecast before substantive work starts.
2. Record the start timestamp when execution begins.
3. Close the row as soon as its evidence gate passes or its stop condition is
   reached.
4. Before quoting a multi-hour plan, inspect completed comparable rows and
   report whether the estimate is calibrated.
5. Preserve the ledger across context compaction, route changes, commits, and
   machine restarts.

The ledger measures forecasting quality, not mathematical value. It must never
be used to prefer easy lemmas over consequential ones.
