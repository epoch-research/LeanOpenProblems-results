# Universal fixed-color kernel transfer

## Original task status

The original conjecture is unresolved. `Submission/Spec.lean` is unchanged
with its original `sorry`. No valid proof or disproof has been submitted.

## Completed files

* `UniversalColorKernelSpanExplore.lean`
* `UniversalActualKernelExplore.lean`
* `UniversalKernelAccuracyExplore.lean`

All three compile and have current oleans. `UniversalColorKernelAudit.lean`
audits their 17 declarations; the output is saved in
`UniversalColorKernelAudit.log` and uses only the permitted axioms.

## Removing the finite coarse-target budget for a fixed alphabet

For a fixed finite color alphabet alpha and a FIXED label coloring omega,
all later pair kernels lie in the span of the alpha-by-alpha indicator
masks. At every label pair, exactly one mask is one, so the sum of their
Frobenius masses is h^2.

Applying the previously checked uniform matrix-span selection to this basis
chooses a single admissible field translate a with

    [rootCount(K)-sum_(i,j) K(omega(i),omega(j))]^2
      <= 16 h^3 sum_(x,y in alpha) K(x,y)^2

for EVERY later real pair kernel K and EVERY fine target. K need not be
symmetric or nonnegative. There is no finite list of coarse targets and no
sum over such a list in this statement.

If e:Fin h equiv alpha x Fin m and omega(i)=(e i).1, each color has exactly
m labels. The unsigned mean is then exact for every kernel:

    sum_(i,j) K(omega(i),omega(j)) = h^2 kernelMean(K).

The coloring is fixed before the field translation, and the field translation
is fixed before all later kernels. This differs from the earlier pipeline
that fixed a low-energy sign pattern first and then selected colors after a
finite family of kernels.

## Actual sets, arbitrary later coarse data

The existing oriented-edge repair converts the selected parameter curves
to a pairwise disjoint fine palette P_i. Its total mixed-count matrix L1
error is at most 10h+8, including the fine origin.

One palette now works for every later family of finite coarse sets B_x,
which may overlap, and every coarse target q. If

    K_q(x,y)=pairCount(B_x,B_y;q),  K_q(x,y)<=M,

then the ACTUAL assembled set obeys

    error(q;t,s)^2
      <= 2[M(10h+8)]^2 + 32h^3 sum_(x,y) K_q(x,y)^2,

where the main term is h^2 kernelMean(K_q).

No finite target set S, target weights, or later choice of coloring occurs.
The coarse ambient group may be infinite; the coarse members B_x in this
statement are finite sets.

## Unconditional relative accuracy and dimension cost

For every nonnegative kernel on a nonempty finite alphabet,

    max K <= |alpha|^2 kernelMean(K),
    sum K^2 <= |alpha|^4 kernelMean(K)^2.

Thus the same palette has

    error^2 <= |alpha|^4 [2(10h+8)^2+32h^3] kernelMean(K)^2.

For h>=1 the bracket is at most 680h^3. Consequently the checked theorem
`exists_universal_actual_accuracy` gives

    |error| <= epsilon h^2 kernelMean(K)

whenever epsilon>=0 and

    680 |alpha|^4 <= epsilon^2 h.

This includes zero-mean kernels. The field still has to be odd and satisfy
p>h^2+4h+2, and the label coloring has equal color multiplicities.
`exists_color_accuracy_threshold` chooses the natural lower threshold on h
before later field sizes or coarse data.

## What this does and does not resolve

For a FIXED finite color alphabet this removes the previous need to sum a
budget over coarse targets in the sparse-curve transfer. It is therefore
stronger than merely applying the finite-family theorem to successively
larger target lists. The fourth-power alphabet loss must be retained if the
alphabet itself grows.

It is not a Boolean rounding of the infinite harmonic profile and does not
prove its quadratic self-error is o(log n). The coarse main term still comes
from the later coarse data; the transfer does not create an accurate infinite
coarse profile. The theorem also does not identify field-plane addition with
integer addition without the separately proved carry mechanisms.

Most importantly, the sparse fine support cannot be retained as a permanent
residue restriction in an exact nonzero logarithmic-limit witness. Varying
fields/palettes and controlling mixed representations through all intermediate
integer scales remain unproved. Neither these new universal kernel estimates
nor the previous complete-partition graph estimates supply the required
cutoff-independent finite-prefix feasibility theorem.
