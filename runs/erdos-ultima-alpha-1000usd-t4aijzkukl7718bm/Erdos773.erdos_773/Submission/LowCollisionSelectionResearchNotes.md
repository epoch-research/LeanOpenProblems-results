# Four-support selection and the remaining collision-count target

This is NOT a settlement of Erdos 773. The main file is unchanged and still
contains its sole admission for 0 < epsilon <= 1/3. No new actual Sidon
exponent has been proved.

## Clean finite theorems

`Submission/LowCollisionSelection.lean`, namespace
`Erdos773.LowCollisionSelection`, imports only the already clean
`WeakSidonExtraction` module (which imports `Hypergraph`). It does not import
the admitted `Spec` theorem.

For a finite set A of natural-number VALUES, `fourSupports A` consists of
its nontrivial equal-pair-sum supports having exactly four vertices. Supports
are counted once, not once per ordered presentation. The vertices are on the
subtype A; this keeps the alteration argument finite and avoids ambient
infinite edge sets. For square roots R, apply the definition to
`R.image (fun n => n^2)`.

`finite_selection` proves, for 0 <= p <= 1, an actual Sidon subset C of A with

    |C| >= (p |A| - p^4 E)/4,    E = |fourSupports A|.

`finite_max_bound` gives the same lower bound for the Sidon maximum of any
ambient finite set containing A.

Importantly, A need not be progression-free. The alteration first removes
only four-entry supports, producing a weak Sidon set. The previously
verified constant-fraction extraction then removes all nontrivial three-
entry progressions. Thus this route does NOT need the subpower Behrend loss
suggested in the earlier gap notes.

`power_count_bound` makes the exponents explicit. For X>=1 and alpha<=beta,
if |A|>=X^alpha and E<=X^beta, then

    M >= (7/64) X^((4 alpha-beta)/3).

Take p=(1/2) X^((alpha-beta)/3). The leading term is at least R/2 and the
cost at most R/16, with R=X^((4 alpha-beta)/3); divide the difference by four.
The global collision exponent beta=2+o(1) and alpha=1-o(1) still give only
the already established exponent 2/3-o(1).

`supersaturation` is a converse finite estimate. If M is the positive
maximum Sidon cardinality of an ambient set containing A, and |A|>=8M, then

    |A|^4 <= 1024 M^3 E.

The proof uses p=8M/|A| in the same finite inequality. This is a count of
four-entry supports rather than merely an existence assertion. It is not
an upper bound on M and does not disprove the conjecture.

## Exact equivalence

`LowCollision` asserts that for every delta>0, eventually there is a subset
A of the first N positive squares such that

    |A| >= N^(1-delta),    E <= N^(1+delta).

The theorem `lowCollision_iff_near_linear` proves this assertion equivalent
to the UNCHANGED proposition of the original conjecture. The forward
implication uses delta=epsilon/4 and p=N^(-delta). The leading term is
N^(1-2delta), the cost is at most N^(1-3delta), and the constant factor four
is absorbed by the remaining exponent slack. The reverse implication takes
a maximum Sidon subset, which has E=0.

This makes a sufficient target rigorous but does not establish it. In
particular, the existing bounded-multiplicity and prime/moment theorems do
not prove `LowCollision`. No such hypothesis has been added to the original
conjecture, and the equivalence is not being substituted for its proof.

## Checks

The final build log is `/tmp/low-collision-selection-final.log`. All seven
printed axiom audits use exactly propext, Classical.choice, Quot.sound. The
module has no admissions or warnings. Its build is
`.lake/build/lib/lean/Submission/LowCollisionSelection.olean`.

The latest main-file check is `/tmp/spec-low-collision-check.log`. It retains
the expected admission warning. No proof submission has been made.
