"""Count cube labellings (with prefix-gon condition) of k=5 extremal sets, up to CAP, by blocking each found phi.
Labellings related by the word symmetry? none assumed. Diagnostic. usage: cube_count.py MAX CAP"""
import sys, json, itertools, runpy
from collections import Counter
sys.argv = [sys.argv[0], '/home/gavin/git/erdos-szekeres-convex-poly/runs/claude-extremal-20261005/k5.json', sys.argv[1], 'gon', sys.argv[2]]
src = open('/home/gavin/git/erdos-szekeres-convex-poly/runs/claude-extremal-20261005/cube_label.py').read()
src = src.replace("sol = Cadical195(bootstrap_with=cl); ok = sol.solve(); sol.delete()",
 "sol = Cadical195(bootstrap_with=cl); cnt = 0\n    CAP = int(sys.argv[4])\n    while cnt < CAP and sol.solve():\n        mm = set(z for z in sol.get_model() if z > 0); cnt += 1\n        sol.add_clause([-x[(v, w)] for v in range(n) for w in words if x[(v, w)] in mm])\n    sol.delete(); ok = cnt\n    st[('count', cnt if cnt < CAP else 'cap')] += 1")
exec(compile(src, 'cube_count', 'exec'))
