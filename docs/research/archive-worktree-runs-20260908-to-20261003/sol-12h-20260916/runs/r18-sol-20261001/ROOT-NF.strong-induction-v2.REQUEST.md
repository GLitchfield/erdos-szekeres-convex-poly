Proof-body diagnostic for the registered ROOT-NF node, locked typee0cedb9ee88cc591.
Requires imports of closed CtxBoundZeroOfUnitGlobalAxis and
CtxBoundLeIffAllIntervalCutsLe in addition to the existing core import.
It changes no statement and assumes no cut inequality.

P(n) is full ROOT-NF for all legal one-level roots with n children. Proper
interval block/complement counts are strictly smaller, but their two-level
history prevents directly instantiating P with those parts. Trace goals preserve
the exact paired upper obligation, single-run base and lower inequality.
Four explicit holes remain; this is a diagnostic partial proof, not theorem credit.
Use es check --async --targeted after insertion only after the registration
commit has finished. es proof check rejects candidates containing sorry before
compilation, so it cannot provide this requested partial-body compiler evidence.
