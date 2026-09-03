# Universal Bernstein color transfer and ordinary carries

## Original task status

The conjecture in Submission/Spec.lean remains unresolved. Its original
import, statement, and sorry are unchanged. No proof or disproof has been
submitted. The results here are not a solution of that existential statement.

## New production files

* CompleteBernsteinEnergyExplore.lean
* UniversalBernsteinGraphExplore.lean
* UniversalBernsteinActualExplore.lean

All three compile, with current oleans and no warnings in the final build.
UniversalBernsteinColorAudit.lean audits eighteen declarations. The saved
log contains only propext, Classical.choice, and Quot.sound. No production
source contains sorry, admit, or a new axiom.

The preceding finite-list Bernstein refinement was also audited: see
BernsteinColorBudgetProgress.md and BernsteinColorBudgetAudit.log.

## 1. Complete-field matching selection

For labels rho:Fin n~F, the pairs i<j with rho(i)+rho(j)=u form a matching
of size at most n. The variance-sensitive MGF and variable-threshold selector
therefore apply directly to cyclic field-label fibers. In odd characteristic
the diagonal map is injective, so its contribution remains at most 2n M^2.

For m symmetric kernels with centered variance at most V and centered entries
bounded by M, one coloring gives each complete label energy at most

    E(n,m,V,M)=64n^2 V ell+64n M^2 ell^2+2n M^2,
    ell=log(4mn+2).

Each kernel may use its own V and M. The selection still has a finite list
at this stage. No ell<=n hypothesis is needed.

## 2. A finite mask list controls all later kernels

Let q be the alphabet cardinality. Use the q^2 ordered indicator masks
M_ab(x,y)=1_((x,y)=(a,b)). Symmetrization preserves their label energy and
mean. Each symmetrized mask is between zero and one, has mean 1/q^2,
and centered variance at most 1/q^2.

One coloring therefore controls every ordered mask with energy at most
E(n,q^2,1/q^2,1). Nonnegative linear combinations of masks represent EVERY
later nonnegative real kernel. Triangle inequality transfers the same
relative error to all those kernels, with no dependence on the number of
later coarse targets.

Define

    ell=log(4nq^2+2),
    paletteCost(n,q)=64q^2 n ell+64q^4 ell^2+2q^4.

The principal result

    Erdos66UniversalBernsteinGraph.exists_universal_bernstein_graph_accuracy

selects ONE coloring before all later graphs f, root caps D, tolerances
epsilon, nonnegative kernels K, and fine targets. Whenever

    D^2 paletteCost(n,q) <= epsilon^2 n^2,

it gives

    |graphSum(K;t,s)-n^2 mean(K)| <= epsilon n^2 mean(K).

Nonsymmetric kernels and zero means are included. The old fourth-power-only
sufficient condition 10D^2 q^4<=epsilon^2 n is replaced by the displayed
variance/range condition. For suitable parameters its leading alphabet
cost is quadratic times a logarithm. The fourth-power range term is still
present; no uniform domination for every parameter choice is asserted.

## 3. Actual sets and all coarse targets

UniversalBernsteinActualExplore has both finite and genuinely infinite
mixed-set versions. One coloring precedes arbitrary later coarse families
B,C, whose members may overlap, and every coarse target. The fine graph
slices form a complete disjoint partition. No finite-support convention or
cutoff is used for the infinite endpoint.

The plane color classes also have all mixed counts within relative epsilon
of n^2/q^2 under the same numerical condition.

## 4. Ordinary natural-number carry endpoint

For odd prime p, retain the existing complete-color natural operator. Its
fine field condition is now

    D^2 paletteCost(p,q)<=epsilon^2 p^2.

The coloring precedes every later thickening K, outer repetition count L,
graph, infinite coarse family, and natural target satisfying this condition.
With

    beta=K^2 p^2/q^2,
    eta=epsilon+2(1+epsilon)/K,
    M=(pK)^2, H=ML,
    w(k)=#{a:k in B_a}, F=w*w,

for n>0 and target nH+z.val+Mr the checked bound remains

    |r_A-beta[r F(n)+(L-r)F(n-1)]|
      <= beta[L eta+1+eta][F(n)+F(n-1)].

Both carry levels are included. The principal endpoint is

    Erdos66UniversalBernsteinActual.exists_universal_bernstein_natural.

The exact membership, complete coverage, and fixed-operator prefix-causality
lemmas from UniversalCompleteNaturalExplore apply without modification.

## 5. Scope and the unresolved sufficient step

This removes the finite coarse-target budget in the Bernstein setting by
paying for the finite-dimensional color basis. It does not manufacture the
coarse main profile. F is still the convolution of integer color
multiplicities, not the exact real fractional harmonic profile.

The operator and field are fixed. Selecting larger fields at higher
precision does not preserve earlier natural membership bits by any theorem
proved here. The carry and accuracy constants at fixed parameters are not
shown to tend to zero. Full fine coverage is not a theorem of asymptotic
residue equidistribution for a changing-scale construction.

A review of applying the finite-list estimate to a randomly colored coarse
host did not close this gap either. In the illustrative regime V comparable
to mu, target mean h^2 mu comparable to c log m, the normalized variance
term scales as h/c, while the retained sign-pattern term scales as 1/h.
That particular upper-bound calculation cannot yield arbitrarily small
error at fixed c merely by tuning h. This is a limitation of that calculation,
not a lower bound on actual errors or an impossibility theorem for all
coarse sources. A better low-variance colored invariant has not been
constructed.

No compatible changing-palette chain, cutoff-independent finite-prefix
feasibility, sharp repair construction, pointwise sublogarithmic quadratic
Boolean rounding, or universal contradiction was established.
