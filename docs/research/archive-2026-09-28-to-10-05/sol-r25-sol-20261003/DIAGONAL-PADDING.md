# Uniform Pascal-tail padding into the diagonal

Paper construction using the accepted DS law. **Neither the diagonal
upper bound nor BDL is proved here.** This shows how the active cardinality
windows arise by removing explicit padding capacities from the diagonal.
There is no new Lean statement or receipt.

Write c,d,sigma for actual cup, cap and strong maxima. A finite ordered
decomposable coloring is given; the construction preserves its restriction
exactly. Classical cup--cap blocks K(a,b) have cup<=a, cap<=b and
size choose(a+b-2,a-1). Their retained generator is univ.es_labels.
For a,b>=2 the maxima attaina,b; a=1 or b=1 is a singleton. Their
strong number is at mostmax(1,a+b-2), by their spatial Pascal recursion.

## The tail block E_s(t)

Fix s>=2 and0<=t<=s. Set E_s(0) empty and E_s(1) a singleton. For
j=1,...,t-1 append the classical block K(j+1,s-j) on the RIGHT and
ABOVE the previous carrier:

  E_s(j+1) = E_s(j) << K(j+1,s-j), spatially left/right.

Its size is

  L_s(t) = sum(j=0,...,t-1)choose(s-1,j).

For2<=t<=s its actual profile is c=t,d=s,sigma=s. To prove this,
the first appended block K(2,s-1), together with the initial lower
singleton, forms an s-cap. At each later step the old cup numberj
plus an upper endpoint gives a(j+1)-cup, and the new block's cup is
at mostj+1. Only one upper endpoint can extend an old cup because
the blocks are spatially separated. Dually mixed caps have at most
(s-j)+1<=s points, and the already attained s-cap persists. The
strong root join is exactlyj+(s-j)=s. Old/new block strong numbers
are at mosts, so DS gives sigma=s. This includes the final singleton
block when j=s-1. For s2,t2 the two singleton blocks form the required
pair. The singleton E_s(1) has c=d=sigma=1 instead.

Color complementation gives a dual tail with cap=t,cup=s,sigma=s
for t>=2, with the same size. This is a uniform symbolic construction,
not a fit to a list of finite examples.

## Padding any active profile

Let B be nonempty with sigma(B)<=s,c(B)=alpha,d(B)=beta and
alpha+beta>=s+1. Cups and caps are strong, so alpha,beta<=s. Put

  p=s-beta, q=s-alpha, F=sum(j=p,...,alpha-1)choose(s-1,j).

Then0<=p,q<=s-1 and p+1<=alpha. Append a LOWER E_s(p) on the RIGHT
of B. If p=0 omit it; otherwise form Y=E_s(p)<<B in this spatial order.
The lower part's cup number is p, and every mixed cup uses at most one
B endpoint, so cup(Y)=alpha. Mixed caps have at mostbeta+1<=s points.
For p>=2 the padding itself has cap s; for p=1,beta=s-1 and a maximum
B cap gains the padding singleton as an endpoint. Thus cap(Y)=s.
If p=0, cap(B) was alreadys. The strong root join is p+beta=s,
so sigma(Y)<=s. No triple on B changes.

Now append an UPPER dual E_s(q) on the RIGHT of Y; omit it when q=0.
For q>0 set Z=Y<<dualE_s(q). Since alpha+q=s, the strong join fits.
Mixed cups have at mostalpha+1<=s points, and mixed caps at mostq+1<=s.
For q>=2 the padding attains cup s; for q=1 the old alpha=s-1 cup
gains the final upper endpoint. For q=0 it was alreadys. The old s-cap
persists. Hence in all cases

  c(Z)=d(Z)=sigma(Z)=s,
  |Z|=|B|+L_s(p)+L_s(q),
  Z restricted to its first |B| points is exactly B.

Both added roots and every block are decomposable. The s1 case needs no
padding: its only nonempty coloring with sigma<=1 is the singleton.
For planar realizations the spatial blocks can be affinely shrunk and
translated far below/above the finitely many relevant lines, so the same
construction gives the required strict mixed turns and preserves general
position. The abstract DS construction alone suffices for this project.

## Consequence and its exact limit

The two missing tails are disjoint, because p<=alpha-1. Binomial symmetry
gives

  L_s(p)+L_s(q)
    = sum(j<p)choose(s-1,j)+sum(j>=alpha)choose(s-1,j)
    = 2^(s-1)-F.

Therefore a DIAGONAL cardinality theorem |Z|<=2^(s-1) immediately gives
|B|<=F for every active profile. The one- and two-band boundaries agree
with the classical coefficients by Pascal's identity. Inactive profiles
alpha+beta<=s use the accepted classical cup--cap bound. Conversely the
full cardinality theorem includes its diagonal. Thus the two cardinality
targets are conditionally equivalent under the stated classical/DS inputs.

This does not prove a diagonal upper bound. Padding preserves numerical
excess exactly:

  |Z|-2^(s-1) = |B|-F.

It need not decrease cardinality, tree size or strong budget when applied
to a child of an attempted diagonal induction. Descending through a child
and padding back to the diagonal can therefore be circular. Marking the
original child separately from its dummy tails would require an additional
induction invariant, essentially the unresolved state accounting.

It also does not transfer BDL partitions: restricting a diagonal map
leaves B on indices0,...,s-1, while BDL requires[p,alpha-1]. No lemma
removing the outside-band assignments has been proved. Dummy capacity
alone does not supply compatible recoloring or solve mixed-maximum ROOT.

There is an explicit canonical map on each padding tail: put its
K(j+1,s-j) block in bandj. The lower tail uses0,...,p-1 and the upper
dual tail usesalpha,...,s-1. A valid BDL map on B would therefore glue
with these tails using disjoint bands. This verifies the forward map
construction, but provides no converse normalization of an arbitrary
diagonal map to those fixed tail assignments.

Capacity saturation does not force these assignments. In the padded
ROOT14 s5/n16 case, a valid saturated diagonal map has cells
{6}/{0,7,13,14}/{2,3,4,5,11,12}/{1,8,9,10}/{15}. Their sizes are
1/4/6/4/1, all exactly choose(4,j), with valid cup/cap maxima
(1,1),(2,4),(3,3),(4,2),(1,1). Old point6 is outside its natural1..3
range; lower dummy14 is in band1. Direct certificate211955-bd7fb4 passed
0.003640664s/10MiB. This refutes automatic canonical allocation/restriction,
not a different globally recolored map. Paper79 gives the full scope.

Dedup search "decomposable off diagonal padding binomial tail diagonal
extension" returned no theorem hits. Guarded pilot211235-f49a25 passed
0.000383694s/12MiB. Fixed audit211338-422631 passed2.672292322s/13MiB:
cup4_s5, cap4_s5 and retained ROOT14 all pad to n16/profile(5,5,5);
cap4_then_cup5_s6 pads from n9 to n16/profile(6,6,6). Every original
triple, predicted tail count, stage profile and mixed root is checked
against complete-triple/quad metrics. Evidence diagonal-padding-pilot.json
and diagonal-padding-fixed.json. This is diagnostic construction support,
not an upper bound or compiling Lean theorem; no larger search follows.
