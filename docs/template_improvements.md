# Open-math-research-template improvement backlog

This project is the proving ground for reusable research-process improvements.
Items here are candidates for a later, separately reviewed change to
`open-math-research-template`; this file does not authorize edits to the
neighboring template repository.

| Candidate | Provenance in this project | Promotion gate |
| --- | --- | --- |
| Multi-agent persona and orchestration protocol | `docs/agents/`, including immutable task packets, evidence levels, serialized integration, formal review, contrarian review, and the innovation sidecar | Extract project-neutral names and examples; validate packet/result schemas in a fresh template instance |
| Automatic innovation-sidecar decision | `docs/agents/README.md`: evaluate innovation help at every approved mathematical batch, with dispatch/reuse/skip recorded | Forward-test on routine, discovery, and route-change tasks without over-dispatching |
| Free mathematical-software catalog and optional per-tool skills | User-requested backlog: record free tools, problem classes, trust boundaries, installation notes, licenses, and skill entry points | Design the catalog schema; seed it only with tools reproduced in at least one project |
| Calibrated timekeeping and planning skill | `docs/agents/time-estimation.md` and `time-estimates.csv`: separate forecast, stop budget, backlog scope, paused time, and overlapping critical paths; compare forecast midpoint with actual active wall time | Add a deterministic ledger summary/check script, concise `SKILL.md`, unit tests, and forward-tests on short and multi-hour plans |

For the timekeeping skill, the reusable behavior should be:

1. inspect comparable completed rows before quoting a duration;
2. label forecasts uncalibrated until enough comparable observations exist;
3. distinguish elapsed-time prediction from speculative stop budget and
   overflow backlog;
4. append the forecast before work and close it as soon as its evidence gate
   passes;
5. report forecast-versus-actual error without prolonging work to fit the
   estimate; and
6. revise future estimates from measured category medians.
