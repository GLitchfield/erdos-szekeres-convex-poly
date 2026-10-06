# A singleton insertion certificate for a one-point loss

2026-10-03. General hand lemma; no compiled theorem.

Suppose a source profile P, with strong limit s, is relabeled into a target
profile Q by a nondecreasing zone map f. Insert a new point at a cut c
between source zones, assign it target zone z compatible with that order,
and attach it as a singleton root upper child. Retain the source as the
root lower child. The following sufficient conditions certify the union:

- Inherited endpoint bounds of P are at most Q's mapped bounds.
- Q's lower counts are supplied by P's aggregated lower counts plus the
  single new point in z.
- Every source cup has length at most s−1.
- A source cup with both endpoints before c may gain the new last point;
  its P limit plus1 is at most Q's bound from its mapped first zone to z.
  For a cup after c use Q's bound from z to its mapped last zone.
- New mixed caps have length2 on one side of the cut and at most3 when
  source points lie on both sides. Q has the corresponding endpoint
  bounds at least2/3. The new singleton itself is allowed by Q.

Proof: root decomposability is preserved by attachment. DS enumerates the
mixed chains exactly as stated; a cup crossing the cut cannot acquire an
outside singleton. The root strong coupling is cup(source)+1≤s.
Inherited chains and the original strong maximum were already bounded.
Counts and sweep order follow from the map and the point's position.
For a lower singleton, interchange cup and cap throughout.

Every source model therefore gives a target model with one more point.
If an independent argument gives N_s(Q)≤U, then N_s(P)≤U−1.
This is a sufficient augmentation test, not a characterization of every
one-point endpoint loss. It remains valid when the target bound is only
an upper bound rather than an exact maximum.

For example, cap4/cup4 source profiles in which every4-cup crosses a cut
permit an upper singleton there: caps containing it have at most3 points,
and no cup becomes5. The classical cap4/cup4 upper20 then gives19 for
the source. A cap3/cup5 profile in which every3-cap crosses a cut uses
a lower singleton and the classical upper15, giving14. These explain
several tight25-to24 DS root deficits without another SAT boundary.

`marker_maps.py` checks the sufficient finite inequalities and searches
the cuts, target zones, sides and order-preserving maps. It does not run
a solver, manage jobs or grant Lean proof credit.
