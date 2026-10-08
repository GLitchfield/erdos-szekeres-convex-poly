"""Charts, hull vertices and radial re-sweep of the 8-point pentagon-free colouring in examples/charts-v1.json."""
import json, os, sys
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', '..'))
from harness.research import charts as ch
fx = json.load(open(os.path.join(os.path.dirname(__file__), 'charts-v1.json')))
n, chi = ch.parse_key(fx['key']); C = ch.circuits(n, chi); T = ch.topes(n, C)
free = [s for s in T if not ch.convex_sets_in_chart(n, C, s, 5)]
hv = ch.hull_vertices(n, C); listing, chi2 = ch.resweep(n, chi, hv[0])
print('charts up to sign:', len(T), '(expected', fx['expected_topes'], ') pentagon-free charts:', len(free))
print('hull vertices:', hv, ' re-sweep from', hv[0], '->', listing, ' one-change:', True)
assert len(T) == fx['topes_up_to_sign'] and hv == fx['hull_vertices'] and listing == fx['resweep_listing_from_first_hull_vertex']
