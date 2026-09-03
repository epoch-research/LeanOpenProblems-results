# Power–log endpoint obstruction

## Original task status

Erdos66.erdos_66 is still unproved and undisproved. Spec.lean has not been
changed and retains its original sorry. The results here concern a different
weighted convolution and must not be submitted as its negation.

## New specialization

PowerLogEndpointExplore.lean specializes the previously checked general
endpoint obstruction to

    w(n) = (n+2)^(-alpha) log(n+2)^(-beta),
    g(n) = (n+2)^(2 alpha) log(n+2)^(2 beta-1),

for alpha>0 and beta>=0. It proves positivity, antitonicity of w, the exact
identity

    w(n) g(n) = (n+2)^alpha log(n+2)^(beta-1),

and divergence of this product. Consequently, for EVERY infinite natural
set A, w-weighted self-convolution times g has arbitrarily late, arbitrarily
large peaks, and cannot have any finite limit.

The critical specialization alpha=1/4, beta=3/4 gives exactly the proposed
log-log energy weight and normalization

    sqrt(n+2) sqrt(log(n+2)).

Thus a pointwise finite-limit transfer to this weighted expression is
impossible for every infinite set; it is not merely an outstanding estimate
that might follow from the original conjecture.

## Mechanism and limitation

Fix a in A and let b run through arbitrarily large elements of A. At n=a+b,
nonnegativity gives

    weightedRep(A,w,n) >= w(a) w(b) >= w(a) w(n).

After multiplication by g(n), the displayed divergent product forces the
peaks. No unweighted representation asymptotic is used.

A single ordered pair contributes only 1/log(n) to the original normalized
count, which tends to zero. Amplifying that same pair with endpoint-sensitive
weights therefore does not establish logarithmic fluctuations of sumRep.
The result excludes this proposed pointwise transfer argument, not a witness
to Erdős 66 or every possible weighted-energy method.

## Verification

The production file compiles without warnings and has a current olean.
PowerLogEndpointAudit.lean and its saved log audit all nine lemma/theorem
declarations; only propext, Classical.choice, and Quot.sound occur.
