# Exact boundary resets (verified; not a settlement)

`Submission/CongruentTailResets.lean` compiles without warnings. Its printed
axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
The conjecture in `Submission/Spec.lean` is unchanged and still unproved.

## Arithmetic classification

Suppose an integer sequence t satisfies, for every n >= N,

    1 <= t_n <= n-1,
    n divides t_(n+1)-t_n+1.

For n >= max(N,2), the verified lemma `step` gives exactly

    t_(n+1) = n       if t_n=1,
    t_(n+1) = t_n-1   otherwise.

Thus the upper endpoint, omitted from the previous strict positive-tail
criterion, permits resets rather than an endless descent.

`exists_reset` shows that, from any M >= max(N,2), there is a reset index
M <= a < 2M with t_a=1. If t_a=1, then `reset_block` gives

    t_(a+1+i) = a-i,    0 <= i < a.

Consequently the next reset is at exactly 2a. There is no reset between a
and 2a. `eventual_reset_blocks` packages the classification: for some a,
all successive reset indices are a, 2a, 4a, ..., and every open interval
between two consecutive such indices has no reset.

The same arithmetic applies to the nonnegative convention after replacing
u_n by t_n=u_n+1: a zero of u is a reset, and the allowed bound is
0 <= u_n < n-1.

## Missing connection to the target

This is a classification of sequences satisfying the displayed hypotheses,
not a proof that any particular normalization of the original series avoids
the reset pattern. The original Lambert coefficients have the required
congruence but tails much larger than this bound. The verified rowwise
small-tail representation does not preserve the congruence.

No argument excluding eventual constant factorial-grid approximants, or
otherwise proving irrationality of the target, was obtained. No proof or
disproof has been submitted.
