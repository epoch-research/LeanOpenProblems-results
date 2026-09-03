# Split/merge extension of the moment obstruction

This is an auxiliary mathematical investigation, NOT a disproof of Erdős 371.
`MergeKernelObstruction.lean` checks the finite algebra below. The PD(1)
Palm formula and the probability-space construction in this note are not
formalized in Lean.

## 1. A pointwise signed insertion identity

For positive x,y,z with s=x+y+z<1 and a residual partition R of mass 1-s,
consider the signed combination of five partitions

  Omega = delta_(x,y,z,R) - delta_(x,y+z,R) - delta_(y,x+z,R)
          - delta_(z,x+y,R) + 2 delta_(s,R).

Let c be smaller than every pair sum x+y,x+z,y+z. An ordered factorial
observation supported on configurations of total selected mass <c cannot
select a merged atom or two of x,y,z. On the unmerged state it is therefore
the sum of its residual-only contribution and its three single-block-atom
contributions. On each two-block state only its surviving single atom and
the residual can contribute. On the one-block state only the residual can
contribute. The residual-only coefficient is 1-3+2=0, and each single-atom
coefficient is 1-1=0. Thus the signed factorial observation is identically
zero, for each fixed x,y,z,R. This includes the empty observation.

For bounded tests supported away from zero all sums are finite. General
integrable tests follow by truncation; a finite factorial moment is not
assumed for arbitrary tests accumulating at zero.

## 2. Absolute continuity under the PD(1) factorial Palm formula

Take a bounded probability density w(x,y,z) supported in a compact box
inside the positive simplex x+y+z<1, bounded away from coordinate zero.
For each x,y,z, draw R as (1-s) times an independent PD(1) partition.
Integrate Omega against w(x,y,z) dx dy dz and this residual law, obtaining
a finite signed measure nu on mass partitions.

The ordered PD(1) factorial Palm formula states

  E_PD sum_(ordered distinct atoms u_1,...,u_k) F(u_1,...,u_k,residual)
   = integral_(sum u_i<1) E[F(u_1,...,u_k,(1-sum u_i) PD)]
                         du_1...du_k/(u_1...u_k).

It gives nu=f dPD with bounded density f. More explicitly, the unmerged
positive component has density

  sum_(ordered distinct atoms x,y,z) xyz w(x,y,z).

The x-surviving merged component has density

  sum_(ordered distinct atoms u,v) uv integral_0^v w(u,t,v-t) dt.

The y- and z-surviving components use w(t,u,v-t) and w(t,v-t,u),
respectively, inside the same formula. The full-merge component has density

  sum_(atoms u) u integral_(x>0,y>0,x+y<u) w(x,y,u-x-y) dx dy.

These formulas have exactly the coefficients +1,-1,-1,-1,+2 specified
above. They use ORDERED factorial sums: no factorial normalization is
missing. The convolution fibers follow from linear changes of variables
with determinant one.

Boundedness follows because w and its fiber integrals are bounded and
all selected atom sizes are bounded below on their supports. A partition
of unit mass contains only finitely many such atoms, with a uniform bound.
Each positive component has total mass integral w=1, so E_PD f=0.
Section 1 shows that every f-weighted factorial test with selected mass
below c integrates to zero. Unlike the earlier two-atom differential
kernel construction, f need not vanish on partitions with largest atom
above one half.

## 3. Two interlaced choices, including upper-half bias

Use two small boxes centered at

  (x_1,y_1,z_1)=(.24,.30,.36),
  (x_2,y_2,z_2)=(.25,.31,.37).

For example coordinate deviations less than .001 are enough for all the
strict inequalities below. Choose any bounded probability densities w_1,
w_2 supported in those boxes. All pair sums exceed c=.52, and residual
mass is smaller than each selected block atom.

The largest-atom signed measures of the five components have coefficients

  a=(1,-1,-1,-1,2)

in the increasing order of their five narrow support intervals. The interval
centers are

  A=(.36,.54,.60,.66,.90),
  B=(.37,.56,.62,.68,.93).

They strictly interlace A_0<B_0<A_1<B_1<...<A_4<B_4, even after the stated
coordinate deviations. Thus every cross-component comparison has a fixed
sign throughout its support. Elementary finite summation yields

  sum_(i,j) a_i a_j [1_(A_i<B_j)-1_(B_j<A_i)] = sum_i a_i^2 = 8.

If both largest atoms must exceed 1/2, remove i=0 and j=0; the same
calculation gives 7. These are exact signed probability pairings, because
each component measure has mass one and its largest-atom support stays
inside the indicated interval. No numerical approximation is being used.

For independent PD(1) partitions P,Q, let f_1,f_2 be the bounded densities
from Section 2 and perturb the product density by

  1 + epsilon*(f_1(P)f_2(Q)-f_2(P)f_1(Q)).

For sufficiently small positive epsilon this is strictly positive. Both
marginals remain exactly PD(1). Mixed factorial data of combined selected
mass <=1 remain those of independence, because one side has mass <=.5<c
and both weighted factorial observations on that side vanish. Fubini
factorizes the signed product term; boundedness ensures the required
integrability whenever the original factorial test is integrable.

The unrestricted largest-atom rising probability changes by 8 epsilon.
The rising probability restricted to both largest atoms exceeding 1/2
changes by 7 epsilon, and its falling probability changes by -7 epsilon.
The total probability of the symmetric upper-half region is unchanged.
PD has a continuous largest-atom distribution, so ties have probability
zero under independence and under this absolutely continuous perturbation.

Consequently exact PD marginals plus all low-total-mass factorial data
alone do NOT force either full order symmetry or upper-half order symmetry.
This conclusion uses the stated standard factorial Palm law. Its Lean
formalization remains separate from the checked finite calculation.

## 4. Checked finite certificate

`MergeKernelObstruction.lean` has ten states, in two families. Every state
has total mass 100. The first family uses the triple (24,30,36) with a
common residual atom 10; the second uses (25,31,37) with residual atom 7.
In each family perform the same three pair-merges and the full merge.

The two signed vectors a,b have coefficients (1,-1,-1,-1,2) on their own
family and zero on the other. Let K(i,j)=a(i)b(j)-b(i)a(j). Lean proves:
- all row and column sums of K are zero;
- |K(i,j)|<=4;
- every mixed inclusion moment of combined mass <110 is zero;
- the rising signed mass is 8, and its upper-half restriction is 7;
- W(i,j)=1/100+K(i,j)/1000 is strictly positive, with row and column
  marginals 1/10;
- all combined-mass-at-most-100 moments equal those of the independent
  coupling with the same marginals;
- rising mass for W is 229/500 instead of the independent value 9/20;
- upper-half rising mass is 287/1000 instead of the independent value 7/25.

All printed axiom checks use only propext, Classical.choice, Quot.sound.
No claim here constructs an actual joint limit of integer factorizations,
preserves all arithmetic constraints, or settles the original conjecture.
