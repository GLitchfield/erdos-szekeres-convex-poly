"""Pure retained rank/clip/cover primitives, semantics version rank-primitives-v1.

Extracted without changing arithmetic or domain conventions from the September 10
probes. These are exploratory computations and establish no Lean theorem.
"""
import math

# Retained source: runs/2026-09-10-active-lean-research/rank_saturation_diagnostic_common.py
def extension(word, depth, side, p, left):
    states = {p: 0}
    for j in range(1, depth + 1):
        positions = [i for i, x in enumerate(word) if x != 'S' and x[0] == j]
        if not positions or word[positions[0]][1] != side:
            continue
        nxt = dict(states)
        for q, count in states.items():
            for z in positions:
                if (z < q) if left else (q < z):
                    nxt[z] = max(nxt.get(z, 0), count + 1)
        states = nxt
    return max(states.values())

# Retained source: runs/2026-09-10-active-lean-research/abstract_rank_strip_probe.py
def clip(rows,keep,axis):
 out=[]
 for i,z in enumerate(rows):
  if i not in keep:continue
  z=list(z);left=[rows[j][2*axis] for j in range(i) if j not in keep];right=[rows[j][2*axis+1] for j in range(i+1,len(rows)) if j not in keep]
  if left:z[2*axis]=max(z[2*axis],max(left)+1)
  if right:z[2*axis+1]=min(z[2*axis+1],min(right)-1)
  out.append(z)
 return out

# Retained source: runs/2026-09-10-active-lean-research/abstract_rank_strip_probe.py
def P(rows):
 sx=set();sy=set();edges={};units=set()
 for a,b,c,d in rows:
  if a>b or c>d:continue
  sx.update(range(a,b+1));sy.update(range(c,d+1))
  if a==b:units.add(a)
  else:edges.setdefault(a,set()).update(range(c,d+1))
 raw=sum(map(len,edges.values()))+len(units)
 rect=0 if not sx or not sy else(len(sx)-1)*(len(sy)-1)+1
 return min(raw,rect)

# Retained source: runs/2026-09-10-active-lean-research/maximum_thin_clear_history_transfer_probe.py
def sideat(row,j):
 return next((x[1] for x in row['word'] if x!='S' and x[0]==j),'lower')

# Retained source: runs/2026-09-10-active-lean-research/maximum_thin_clear_history_transfer_probe.py
def actual(row,j):return any(x!='S' and x[0]==j for x in row['word'])

# Retained source: runs/2026-09-10-active-lean-research/maximum_thin_clear_history_transfer_probe.py
def part(row,keep,side,m):
 word=tuple(x if x=='S' else tuple(x) for x in row['word'])
 return {'word':tuple(('S' if i in keep else (1,side)) if x=='S' else (x[0]+1,x[1]) for i,x in enumerate(word)),
  'maxima':(m,)+tuple(row['maxima']),**{k:row[k] for k in ['a','u','k','chosen']}}

# Retained source: runs/2026-09-10-active-lean-research/maximum_thin_clear_history_transfer_probe.py
def ordered_cover(rec):
 rectangles=rec['rectangles'];dp=[0]+[10**20]*len(rectangles)
 for i in range(len(rectangles)):
  X=set();Y=set()
  for j in range(i,len(rectangles)):
   _,L,R,lo,hi=rectangles[j];X.update(range(L,R+1));Y.update(range(lo,hi+1))
   D=(len(X)-1)*(len(Y)-1)+1
   dp[j+1]=min(dp[j+1],dp[i]+D)
 return dp[-1]

# Retained source: runs/2026-09-10-active-lean-research/maximum_thin_clear_history_transfer_probe.py
def maximum_bounds(row):
 bounds=[];k=row['k']
 for j,m in enumerate(row['maxima'],1):
  side=sideat(row,j);otherG=row['a'] if side=='lower' else row['u']
  if m>=k-2:bounds.append({'bound':1,'reason':'indexed maximum at least k-2','level':j})
  elif m>=k-3:bounds.append({'bound':max(0,otherG-1),'reason':'normalize to global at most three','level':j})
  elif m>=k-4:bounds.append({'bound':math.comb(otherG,2),'reason':'normalize to global at most four','level':j})
  if m>=k-4 and otherG<=k and any(actual(row,i) and sideat(row,i)==side for i in range(1,j)):
   bounds.append({'bound':min(2*k-4,max(0,2*max(0,otherG-1)-1)),'reason':'normalize to global four retaining younger actual marker; minimum of drafted saturated and checked ordinary refined linear bounds','level':j})
 return bounds

# Retained source: runs/2026-09-10-active-lean-research/maximum_thin_clear_history_transfer_probe.py
def sole_opposite_normalize(row):
 other='upper' if row['chosen']=='lower' else 'lower'
 assert sideat(row,1)==other
 assert all(sideat(row,j)!=other for j in range(2,len(row['maxima'])+1))
 D=len(row['maxima']);n=row['maxima'][0]
 result={**row,'word':tuple(x if x=='S' else ((D if x[0]==1 else x[0]-1),x[1]) for x in row['word']), 'maxima':tuple(row['maxima'][1:])}
 field='u' if other=='lower' else 'a';result[field]=min(row[field],max(0,row['k']-n));return result

ext = extension
