# Logarithmic finite coarse-target budgets

## Original task status

The conjecture in Submission/Spec.lean remains neither proved nor disproved.
Its original import, statement, and sorry are unchanged. No proof submission
has been made. These new finite selection results do not settle the original
existential natural-number statement.

## New checked result

The old fixed-sign-pattern color selection paid linearly for a finite list
of coarse kernels using a summed second moment. The new selection pays a
LOGARITHM of the list size, under a pointwise centered-entry bound. This is
not being described as a variance-only estimate or an infinite-list theorem.

For h labels, m requested symmetric kernels K_k, and

    ell = log(8mh+2) <= h,
    |K_k(a,b)-mean(K_k)| <= M_k,   M_k>0,

one coloring omega controls BOTH signed and unsigned centered energies:

    jointEnergy_k <= 2 M_k^2 (64 h^2 ell + 2h).

The sign pattern is fixed before the list. The bound has no factor depending
on the cardinality of the color alphabet, and each kernel retains its own
M_k rather than a common maximum.

## Matching exponential calculation

MatchingColorExponentialExplore proves exact factorization of finite uniform
MGFs for kernels on disjoint coordinate pairs. If a kernel has mean zero,
absolute value at most one, and the fixed edge weights have absolute value
at most one, then for |t|<=1,

    mean exp(t sum_matching v_e K(omega_i,omega_j))
       <= exp(|matching| t^2).

No symmetry is needed for this MGF lemma. It uses Mathlib's checked
quadratic bound for exp on [-1,1] and finite-average factorization.

At a fixed integer label sum the unordered edges form a matching with at
most h edges. Summing two-sided exponential potentials over m kernels and
2h fibers gives the sufficient budget

    4mh exp(h t^2-t R)<1.

For ell0=log(4mh+2)<=h, choose t=sqrt(ell0/h), R=2h t. This gives one
coloring with every unordered fiber smaller than R in absolute value.
The diagonal and both ordered orientations are retained, giving

    orderedEnergy_k <= 64h^2 ell0+2h

for normalized kernels. Scaling handles each positive M_k. Doubling the
request list handles the signed and unsigned energies with the SAME coloring,
which gives the ell=log(8mh+2) formula above.

## All fine targets and actual sets

LogarithmicRootBudgetExplore selects an admissible field translate a with
old sign energy at most 8h^2, before the later coarse data. For an odd prime
p with 4h<p, the later coloring obeys, for every requested k and ALL t,s in
ZMod p,

    [rootCount_k(t,s)-h^2 mu_k]^2
      <= 6h [8 mu_k^2 h^2 + 2 M_k^2 (64h^2 ell+2h)].

There is no union bound over the fine field targets. Here mu_k=mean(K_k).
For positive mu_k, the displayed relative squared bound is exactly

    48/h + 768 (M_k/mu_k)^2 ell/h + 24 (M_k/mu_k)^2/h^2.

LogarithmicActualBudgetExplore then uses the existing disjoint origin repair.
For h^2+4h+2<p, the translate and actual disjoint curve palette P_i are chosen
before arbitrary later coarse finite sets B_a, finite target list S, and
positive bounds M_q on their mixed pair counts. Members B_a may overlap.
The actual set is

    A_omega = union_i P_i x B_(omega_i).

With K_q(a,b)=r_(B_a,B_b)(q), nonnegativity and K_q<=M_q give the required
centered-entry bound. The ACTUAL self-count satisfies, for every q in S and
every fine target,

    [r_A((t,s),q)-h^2 mu_q]^2
      <= 2 [M_q(10h+8)]^2
         +12h [8 mu_q^2 h^2+2 M_q^2(64h^2 ell+2h)].

The origin-repair term is displayed separately. This is a finite product-group
set theorem, not an asserted integer embedding or natural-prefix extension.

## Production files and audit

All five files compile and have current oleans:

* MatchingColorExponentialExplore.lean
* ExponentialColorSelectionExplore.lean
* LogarithmicColorBudgetExplore.lean
* LogarithmicRootBudgetExplore.lean
* LogarithmicActualBudgetExplore.lean

LogarithmicColorBudgetAudit.lean audits seventeen principal declarations.
The saved log contains only propext, Classical.choice, and Quot.sound.
No production file contains a sorry or a new axiom. One tactic-style
suggestion remains harmless.

## Remaining gap and scope

The direct source review reconfirmed that the available infinite existence
theorems do not meet the completion criterion: their fixed coefficient has
only a wider all-target envelope, and their fixed-tolerance exceptional
power saving need not cross the square-root threshold. The approximation
theorem with arbitrarily small fixed relative tolerance changes its
coefficient with that tolerance.

The new logarithmic list cost is stronger than the earlier second-moment
list budget when centered entry bounds are useful. It does not automatically
dominate the variance-sensitive theorem when M_k is much larger than the
root-mean-square centered kernel. It also does not replace the all-later-kernel
complete-partition theorem, whose quantifiers and color-dimension cost are
different.

In particular, log(8mh+2)<=h still restricts the finite list for fixed h.
Choosing a new h and coloring at each larger horizon does not prove
cutoff-independent finite feasibility or compatible natural prefixes.
No accurate infinite coarse source, density-correct changing-scale chain,
pointwise quadratic Boolean rounding, or universal contradiction was obtained.

The variance-preserving Bernstein refinement has now been proved and audited
in six subsequent production files; see BernsteinColorBudgetProgress.md. It
retains the finite-list logarithm and an explicit range term. It still needs
a genuinely infinite construction argument before it could settle Spec.lean.
