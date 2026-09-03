# Arbitrary pair weights, uniform spans, and the adaptive-weight limitation

## Original task status

The original conjecture is still unresolved. Spec.lean is unchanged, with
its original statement, import, and sorry. No proof or disproof has been
submitted.

Four new production files compile, with current oleans:

1. PairWeightedCharacterEnergyExplore.lean
2. PairWeightedRootTransferExplore.lean
3. UniformMatrixSpanExplore.lean
4. AdaptiveMatrixEnergyExplore.lean

PairWeightedTransferAudit.lean checks 13 principal declarations. They use only
propext, Classical.choice, and Quot.sound. No production placeholders or new
axioms were introduced.

## 1. Arbitrary pair-weight matrices

For h<=p, p an odd prime, W an arbitrary real h-by-h pair-weight matrix,
and a in ZMod p, define

    F_a(q) = sum_(i,j<h, i+j=q) W_ij chi(a+i) chi(a+j),
    E_a(W) = sum_(q<2h) F_a(q)^2,
    mass(W) = sum_(i,j<h) W_ij^2.

The new matrix weights need NOT be separable as W_ij=v_i*v_j, need not be
symmetric, and need not be nonnegative.

`average_matrix_fiber_energy` proves

    sum_a F_a(q)^2 <= 4p sum_(i+j=q) W_ij^2.

`average_matrix_energy` consequently proves

    sum_a E_a(W) <= 4p mass(W).

The proof uses the existing quadratic-character correlation identity and
the two-to-one square fibers. It does not invoke a quartic Weil estimate.

For a finite list W_k with nonnegative weights w_k and p>4h,
`exists_admissible_matrix_budget` selects ONE a with nonzero/nonopposite
parameters and

    sum_k w_k E_a(W_k) <= 8 sum_k w_k mass(W_k).

The matrix data and weights precede the choice of a.

## 2. Transfer to every fine root-count target

Let

    R_a(W;t,s) = sum_(i,j<h) W_ij
       #{x : ZMod p : x^2/(a+i)+(t-x)^2/(a+j)=s}.

`matrixRootCount_identity` proves

    R_a(W;t,s) = sum_ij W_ij
       + sum_(q<2h) F_a(q) chi((2a+q)s-t^2).

The resulting uniform error estimate is

    (R_a(W;t,s)-sum_ij W_ij)^2 <= 2h E_a(W).

There is no factor counting the fine field-plane targets. In particular,
`exists_matrix_root_transfer` selects one admissible a with, for ALL t,s,

    (R_a(W;t,s)-sum_ij W_ij)^2 <= 16h mass(W).

`exists_matrix_root_budget` gives the weighted simultaneous version.

These are PARAMETER-WEIGHTED ROOT COUNTS. The file does not identify them
with the self-representation counts of an actual infinite set. If W comes
from arbitrary overlapping coarse color sets, origin multiplicity and the
integer carries still require an actual-set conversion.

## 3. Uniformity for all later coefficients in a fixed span

`exists_uniform_matrix_span` selects a for a fixed finite family W_k BEFORE
an arbitrary coefficient vector c is chosen. For

    W(c) = sum_k c_k W_k,

it gives, for every later c and every t,s,

    (R_a(W(c);t,s)-sum_ij W(c)_ij)^2
      <= 16h (sum_k mass(W_k)) (sum_k c_k^2).

If every basis matrix has squared mass at most one, the first sum is at
most the family size (`exists_normalized_matrix_span`). Orthonormality or
linear independence is not assumed. Consequently this is a coefficient-
budget estimate, not an automatic bound by mass(W(c)) for arbitrary bases.

This removes dependence on the number of requested coefficient vectors,
but not dependence on the chosen span and its budget. No infinite coarse
profile with the required small span/coefficient budget has been constructed.

## 4. Why arbitrary adaptive weights cannot be allowed

For any fixed admissible a, set f_i=chi(a+i) in {-1,1} and

    W_ij=(1+f_i f_j)/2.

`alignedMatrix_zero_one` proves W is zero-one on the label square. Its
signed fiber equals its ordinary nonnegative fiber, and

    sum_ij W_ij = (h^2+(sum_i f_i)^2)/2 >= h^2/2.

Cauchy--Schwarz gives

    E_a(W) >= h^3/8,       mass(W) <= h^2.

These are `alignedMatrix_energy_lower` and `alignedMatrix_mass_le`.

Thus if a fixed a were to satisfy E_a(W)<=C mass(W) for EVERY later
nonnegative bounded W, then h<=8C (for h>0, C>=0). This is checked by
`universal_matrix_budget_requires_large_constant`.

This is a limitation of the proposed universal energy engine, not a
negation of the original existential conjecture. It does not prevent
selecting particular good adaptive profiles or using a controlled span.

## Remaining infinite issue

The investigation of scale averaging did not produce an infinite witness.
The existing moving-window theorem alone is already known insufficient.
The new matrix estimates permit aggregate coarse interactions more general
than separable scalar profiles and permit later choices within a fixed span.
They do not supply the needed coarse patterns, an actual-set origin repair
for arbitrary pair data, or compatible changes of period with vanishing
relative error and a fixed logarithmic coefficient.

A possible further question is whether a previously selected low-energy
character pattern admits suitably chosen coarse color assignments, rather
than arbitrary assignments. For off-diagonal additive label pairs, two
nonidentical, nonswapped pairs with the same sum have four distinct indices;
this could simplify a random-assignment energy calculation. No such
fixed-translate selection or infinite consequence has been proved here.

## Subsequent logarithmic finite-list selection

LogarithmicColorBudgetProgress.md records an exponential matching-fiber
selection theorem reducing the finite coarse-target cost to a logarithm,
under explicit centered-entry bounds. It includes an actual disjoint-palette
set endpoint. It is not an infinite-prefix construction or a variance-only
replacement for all of the earlier budgets.
