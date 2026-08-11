# Experiment 0099: middle-word frontier selector

Date: 2026-08-11

Status: Frozen selector refuted at the first checked `k = 5` gate

## Question

Can failure of strong middle-determined chains be encoded by a short binary
word at each vertex, with the selected words globally prefix-free?  Such a
selector would turn the Kraft inequality into the desired power-of-two
capacity bound.

## Frozen noncircular definition

For a word `w`, `RealizesMiddleWordThrough χ support v w` means that some
strong middle-determined chain in `support`, containing `v`, has middle-color
word `w`.  The frontier at `v` consists of the prefix-minimal unrealized words.
A selector chooses one frontier word for every vertex and separately requires
the chosen words to be globally prefix-free.  Neither the definition nor the
selector contains a cardinality bound or the desired conclusion.

## Decisive bounded counterexample

The first checked failure is the abstract rank-three signotope

```text
k = 5, d = 3, n = 6, coloring = 0x1fffe.
```

It has no strong five-set, but every one of its six vertices has exactly the
same frontier

```text
{00, 01, 10, 110, 111}.
```

Prefix-freeness implies that the six selected words must be distinct, while
only five words are available.  Therefore no selector exists.

An independent checker reconstructs the signotope law and strong-chain
semantics directly, reproduces every frontier and the selector failure, checks
the bounded first-occurrence census, validates rational pair-rank controls,
and rejects two corrupted outputs.  The producer used 1.40 seconds and 21 MiB;
the checker used 0.18 seconds and 19 MiB.

## Evidence boundary and disposition

`STOP_AS_STATED`.  The witness is an abstract signotope; it is not proved
planar or sweep-realizable.  Thus this refutes the proposed universal abstract
selector, not the happy-ending formula and not every possible geometric
frontier refinement.  No Lean theorem was attempted after the frozen stop
condition fired.

Artifacts and hashes:

- frozen definition: `7f665f197129616f4a4e6ddc09d483544bf503f158446d28983482b789702bb5`;
- result: `514eccbd06e267519bd437f5bdaaac780bc47eb204868f011b437a4e952a5f54`;
- independent checker: `e4e9124d559c239c2d77cd4044f3c30834c4de1624f43644a1318304cb9b4c2f`;
- structured report: `7cd95e5de08ba875742620afc239fc2783f7dfc0ead997d6ad13f27d3ac40427`.

The ignored artifacts are under
`runs/agents/20260811-wave3/middle-frontier/`.
