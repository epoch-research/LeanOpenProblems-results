# Hereditary ratio extremality and energy: exact conclusions and gaps

These results do NOT settle the actual planar comparison E>=c nI on hereditary
ratio-extremal sets, nor the sharp distinct-distances conjecture. There is no
certified planar counterexample under that restriction. The elementary
identities and abstract constructions below were checked by the parent.

Let K=n/D, E=Σ_s r_s², I=Σ_{p,s}k_ps(k_ps-1). EXT means K(Q)<=K(P) for all
nontrivial induced subsets. An exact maximizing subset exists inside any
finite set. It preserves a violation K(P0)²>B log|P0|, because K increases and
cardinality decreases. This reduction does not preserve normalized energy.

## What EXT really controls

For R⊂P leaving at least two points, let lambda(R) be the number of colors
extinguished by deleting R. Then EXT is equivalent to lambda(R)<=|R|/K.
In particular K>=2. For every proper color family C, the union of its edge
graphs has vertex-cover number >=K|C|. A cover leaving two points follows
from the extinction identity; otherwise its size>=n-1>=K(D-1). For a single
color, when D>=2, its matching number is at least K/2.

The incidence bipartite graph (vertices, colors present at a vertex) satisfies
fractional Hall: there are a_ps>=0 supported on present incidences such that
Σ_s a_ps=1 and Σ_p a_ps=K. Scale capacities by D to use integer max-flow.
This is a SUPPORT allocation, not a bound on the large degree-squared terms.

Exactly, with Delta=Σ_{p,s}(k_ps-r_s/n)²,

  I = E/n - n(n-1) + Delta.

Thus comparison would follow from degree delocalization Delta=O(E/n), but
EXT does not prove it. For A>0, the color-specific sets
H_s={p:k_ps>A r_s/n} satisfy |H_s|<n/A and
Σ_{s,p notin H_s}k_ps²<=A E/n. Deleting such heavy sets need not EXTINGUISH
colors, so the support/cover inequalities do not give a density increment.

An exact weighted conversion is

 J=Σ_{p,s:k>0} [r_s/(n k_ps)] k_ps(k_ps-1)
  =(1/n)Σ_s r_s(r_s-h_s),  h_s=|{p:k_ps>0}|,
 E/n-n(n-1)<=J<=E/n.

Proving J>=c n²K² would essentially be the desired energy amplification;
defining these weights does not establish that bound.

The separated scaled-grid planar counterexample saved in
pinned_degree_comparison_counterexample.md is genuinely nonextremal. Its
unique diameter edge joins extreme corners in the two extreme blocks (their
scales differ, so the vertical maximizing choice is unique). Removing one
endpoint deletes a color, which increases K whenever D<n. Selecting a grid
block changes E/(nI) from order1/m to order1; a maximizing selection cannot
simply be assumed to preserve the counterexample.

## Explicit full-EXT abstract obstruction to comparison (NOT PLANAR)

Partition n=km vertices into m groups of even size k, each half labeled with
each parity. Internal edges of group i have color i. For i<j color a cross
edge i if endpoint parities agree and j otherwise. Every vertex has own-color
degree a=(n+k-2)/2 and each other color degree b=k/2. Thus

 D=m, K=k, r_i=k(n-1), E=nk(n-1)²,
 I=n[a(a-1)+(m-1)b(b-1)].

For any selected Q, at most one occupied group can have its color absent:
an edge between two absent groups would have one of those colors. An absent
group contributes one vertex, and then every other occupied group contributes
at most k/2 vertices, to avoid creating the absent color. Hence either
|Q|<=kD(Q), or |Q|<=1+(k/2)D(Q)<=kD(Q). This proves FULL EXT.
Taking k=2t,m=2^(2t) gives D/n->0, E/(nI)~4/m->0, and ED²/n⁵~1/k->0,
even with E=O(n³log n). The monochromatic k-cliques exclude any planar
realization for k>=4. This is only an obstruction to using support axioms.

## Full-EXT upgrade of the balanced motion-table relaxation (NOT PLANAR)

The existing rich_motion_joint_table.md proves a balanced random coloring
with t=2^s>=64, n=2^t, D=n/t, r_s=t(n-1), simultaneously satisfying

 D(Q)>=min(|Q|/16,3D/4) for 2<=|Q|<=n/2,
 r_s(Q)<16|Q| for |Q|<=sqrt n, and deg_s(v)<8t,

with total failure probability <3/10. Also a fixed half-size Q misses a
fixed color with probability <=exp(-binom(n/2,2)/D). The union bound over
all colors and half-size subsets is

 D exp(n log2 - t(n-2)/8)<1/10.

Thus one may simultaneously require every subset of size>=n/2 to see every
color. For smaller q, q/t<=min(q/16,3D/4). FULL EXT follows at every size.
But exactly E=t n(n-1)², and Cauchy plus the degree bound give

 t(n-1)²-n(n-1)<=I<(8t-1)n(n-1).

So E>=(1/16)nI, while (I+n²)D²/n⁴<=9/t and ED²/n⁵=(1-1/n)²/t tend to zero.
Comparison alone does not imply the missing amplification. This model keeps
the previously established numerical unit-distance, rich-tail, row/domain,
and balanced table identities. It still lacks endpoint-consistent point maps:
shared source endpoints in a motion row need not share their target endpoint.
Nothing makes it an actual Euclidean configuration.

## Exact unresolved geometric step

The desired comparison on EXT sets is equivalent (with matching constants
and lowD threshold) to the actual density increment

 E(P)<c|P|I(P)  =>  some proper actual Q has K(Q)>K(P).

Similarly ED²<c n⁵ => an actual ratio improvement would imply amplification
on EXT sets and, with Guth--Katz, the sharp conjecture. Neither implication
has been proved. Color-specific heavy pins, fractional Hall, and abstract
support/table information do not supply it. No Lean file was modified.

## Further obstruction: the balanced abstract model is already a positive record

The stronger logarithmic-record condition does not, by itself, exclude the
existing balanced ABSTRACT coloring. This is not a planar counterexample.
No transfer of motion tables to a selected subset is needed for this fact:
the entire model itself is a record.

Fix A>0. In the full-EXT balanced model above, take t sufficiently large,
n=2^t, D=n/t, K=t. For every subset Q with 2<=q<=n/2, property (9) gives

```
K(Q) <= max(16, 4q/(3D)) <= 2t/3.
```

Since log(n/q)<=log n=t log2, the inequality

```
t >= (9/5) A log2
```

implies `K(Q)^2 <= t^2-A log(n/q)` for all these subsets. For n/2<=q<=n,
every color is present. Put x=q/n in [1/2,1]; then K(Q)=tx and

```
log(1/x) <= 1/x-1 <= 2(1-x) <= 2(1-x^2).
```

Consequently `t^2>=2A` gives the same record inequality in this range.
Thus, for every fixed A>0, all sufficiently large members of the abstract
family satisfy, for EVERY nontrivial actual vertex subset,

```
K(Q)^2 <= K(P)^2 - A log(n/q),
K(P)^2-A log n > 0.
```

The full model still has exactly

```
E=t n(n-1)^2,
E D^2/n^5 = (1-1/n)^2/t -> 0,
K(P)^2/log n = t/log2 -> infinity.
```

Even the numerical energy upper bound is hereditary. For q<=sqrt n,
`max_s r_s(Q)<16q` gives `E(Q)<=16q^3`. For q>sqrt n, the degree bound gives
`max_s r_s(Q)<=8tq`, so `E(Q)<=8tq^3<= (16/log2)q^3 log q`. These are estimates
for the same abstract coloring, not for Euclidean point sets.

Therefore logarithmic records, all previously verified support conditions,
and even a hereditary Guth--Katz-shaped numerical energy bound do not alone
supply the missing amplification. A proof must use additional actual
Euclidean structure, such as the coherent endpoint images absent from this
model. This observation does not refute the record reduction, which is valid,
or any conjecture restricted to genuine planar configurations. Spec is unchanged.
