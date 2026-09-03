# Complete parallel-parabola partitions

## Original task status

The original conjecture is still neither proved nor disproved. Spec.lean
has not been changed and retains its original sorry. No proof submission
has been made.

Four new production files compile, with current oleans:

1. FiberColorEnergyExplore.lean
2. ParallelParabolaPartitionExplore.lean
3. CompletePartitionColorTransferExplore.lean
4. CompletePartitionRowExplore.lean

CompletePartitionTransferAudit.lean checks 18 declarations, and
CompletePartitionRowAudit.lean checks three. All depend only on propext,
Classical.choice, and Quot.sound. No production placeholders were added.

## 1. General label fibers

FiberColorEnergyExplore generalizes the matching calculation from integer
label sums to a symmetric cancellative map sigma:(Fin n)^2 -> kappa, where
kappa is finite and i -> sigma(i,i) is injective. The unordered pairs in a
fiber form a matching. The full ordered fiber is twice the unordered sum
plus its diagonal; the diagonal squared energy is exactly sum_i V(i,i)^2.

For symmetric coarse K on a finite nonempty color type, put

  mu=mean(K),
  var=mean_(x,y) (K(x,y)-mu)^2,
  diag=mean_x (K(x,x)-mu)^2.

Independent uniform colors satisfy

  mean_omega [sum_q (sum_(sigma(i,j)=q) (K(omega_i,omega_j)-mu))^2]
    <=8n^2 var+2n diag.

In particular there is no residual old sign-pattern energy here.

## 2. The complete partition

For an odd finite field F of cardinality n and an equivalence rho:Fin n~F,
let

  P_i = {(x,x^2+rho(i)) : x in F}.

These sets are pairwise disjoint, each has cardinality n, and their union
is all of F^2. Their mixed count at (t,s) is

  N(rho(i)+rho(j);t,s),
  N(u;t,s)=#{x : x^2+(t-x)^2=s-u}
          =1+chi(2(s-u)-t^2).

Thus N<=2, and the sum of all mixed counts is exactly n^2 at EVERY target.
The grouping map sigma(i,j)=rho(i)+rho(j) satisfies the general matching
hypotheses, including diagonal injectivity in odd characteristic.

For an arbitrary real pair matrix V, the parameter-weighted count obeys

  R(V;t,s)^2 <=4n energy_sigma(V),

uniformly in (t,s). This follows from the coefficient bound and
Cauchy--Schwarz over the n label-sum fibers. It is not a bound obtained by
summing over the n^2 fine targets.

## 3. Kernel selection and actual-set transfer

For a finite symmetric kernel family K_k with nonnegative weights w_k,
define

  Budget=sum_k w_k [8n^2 var(K_k)+2n diag(K_k)].

One coloring omega:Fin n->alpha has, for every k in the requested family
and EVERY fine target,

  w_k [R(K_k,omega;t,s)-n^2 mean(K_k)]^2 <=4n Budget.

The same statement holds exactly for the actual set

  A_omega=union_i P_i x B_(omega_i),

when K_q(x,y)=r_(B_x,B_y)(q), for arbitrary overlapping coarse finite sets
B_x. There is NO origin repair or maximum-coarse-kernel error term.

For a single kernel the squared error is at most

  32n^3 var(K)+8n^2 diag(K).

Constant kernels are exactly flat: both centered costs vanish. These
statements are checked in CompletePartitionColorTransferExplore.lean.

The actual set has the precise membership formula

  ((x,y),q) in A_omega
    iff q in B_(omega(rho^-1(y-x^2))).

It also has cardinality n sum_i |B_(omega_i)|. If every coarse color is
nonempty, its projection onto the fine plane is the whole fine plane.
Consequently there is no fixed, independently excluded sparse fine support
as in the previous repaired-curve palette. Full projection is NOT being
confused with asymptotic residue equidistribution.

## 4. Quantitative limitation

Here n is the FULL FIELD SIZE, not a small interval of h labels in a much
larger field. The absence of an old-pattern term does not make the bound
uniformly stronger in the logarithmic-density regime.

For a single kernel with mu>0, normalizing by (n^2 mu)^2 gives the bound

  32 var/(n mu^2)+8 diag/(n^2 mu^2).

If var is of order mu and the target mean is M=n^2 mu, the first term is
of order n/M. Thus a very large fine field with only logarithmic target
mean is NOT covered by a vanishing relative-error deduction from this
bound. This is a limitation of the available upper estimate, not an
impossibility theorem for all complete-partition constructions.

The finite-family budget likewise still depends on the requested coarse
targets. No cutoff-independent infinite coarse profile was constructed.

## 5. Checked literal-row limitation

For every coarse color assignment, every fixed y and coarse q, the row

  X={x : ((x,y),q) in A_omega}

is invariant under x -> -x. Choosing coarse colors does not break this
reflection, since membership depends on y-x^2.

CompletePartitionRowExplore combines this fact with the earlier integer
row theorem. If a natural-number set contains the whole row encoded in
[a,a+p), it has a target 2a<=m<2(a+p) with |X|<=2 r_A(m). Under a global
logarithmic upper envelope, the row therefore has O(log(a+p)) points.

This restriction concerns literal whole-row encodings only. It does not
exclude arbitrary clipping, point-dependent phases, other graph functions,
or general natural-number sets. It is NOT a disproof of Erdős 66.

## Remaining infinite issue

Complete partitions remove the fixed sparse-support obstruction, but
neither exact group uniformity nor the new variance estimate supplies
control of the short integer prefixes where successive stages must meet.
The reviewed recursive ideas still require one of:

- spatial estimates useful relative to a short interval's own local mean;
- a compatible change-of-period construction with controlled mixed counts;
- an infinite correction mechanism meeting all shrinking tolerances; or
- a genuinely universal obstruction.

No such result was obtained here. In particular no infinite construction
follows from separately choosing a good coloring at each finite stage.

## A possible further finite variant (NOT formalized)

The complete partition can use translates of a more general graph
P_i={(x,f(x)+rho(i))}. If every sum fiber
#{x:f(x)+f(t-x)=s-u} is bounded by D, the same energy argument should work
with 4n replaced by D^2 n. For example f(x)=x^4+x has a degree-four sum
polynomial with leading coefficient 2 in odd characteristic, suggesting
D=4. Unlike the quadratic graph, it has no single horizontal reflection
preserving the graph in characteristic other than 2 or 3 (compare the
values at t/2 +/-1 and t/2 +/-2).

Neither this generic graph transfer nor the quartic facts have been
formalized yet, and they would still be finite statements. They might
avoid the forced row symmetry, but by themselves do not solve the small-
local-mean or infinite-prefix problem. Do not claim an infinite consequence
from them.

## Subsequent update

The finite coarse-target-list restriction has now been removed; see
UniversalCompleteProgress.md. The universal bound incurs the explicit
centered-matrix/color-dimension cost described there. No infinite-scale
natural-number construction follows without an additional compatibility
and coarse-profile argument.
