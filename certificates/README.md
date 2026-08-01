# ES(5) finite certificate

`es5-signotope.cnf` has one Boolean variable for each of the 84 increasing
triples on nine ordered vertices. Its 2,016 clauses consist of:

- 1,008 clauses excluding the eight non-one-change patterns on each of the
  126 four-subsets; and
- 1,008 clauses excluding the eight strong-polygon patterns on each of the
  126 five-subsets.

Regenerate the CNF and the semantic Lean modules with:

```console
python3 scripts/generate_es5_sat.py certificates/es5-signotope.cnf \
  --lean ErdosSzekeres/ES5CNFGenerated.lean
```

The committed LRAT trace was produced with CaDiCaL 1.7.3:

```console
cadical --lrat --no-binary \
  certificates/es5-signotope.cnf certificates/es5-signotope.lrat
```

Checksums:

```text
322c753bd3189b97fd381d7363c8b4aaa7e7c4a59d9d993b0da6ce75fe1ca09e  es5-signotope.cnf
741e74e9c5df5adfad2b0b99534ad5fe184ddc1658de6d0545135f2a470c2a50  es5-signotope.lrat
```

The solver is not trusted. `ErdosSzekeres/ES5Unsat.lean` checks the LRAT trace
inside Lean, while the generated chunk modules prove that every encoded clause
follows from `TurnSequenceAllowed` or the assumption that a five-subset is not
strong.
