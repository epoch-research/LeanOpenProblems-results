# A factorial factor after primitive Padé specialization

Verified auxiliary arithmetic, NOT a proof or disproof of Erdős 68.
Submission/Spec.lean remains unchanged with its original sorry. No settlement
has been obtained or submitted.

DirectPadePrimitiveDenominator.lean compiles without warnings and has a built
olean. Its four printed principal axiom audits contain only propext,
Classical.choice, and Quot.sound. There are no proof holes or numerical premises.

## General reduction-aware arithmetic

Let M>0 be natural and D,a,b,c integers, a nonzero. Suppose

    M divides a,
    M divides D*(b-c).

For r=b/a in lowest terms, the file proves

    M divides |D*c|*den(r),
    M/gcd(M,|D*c|) divides den(r).

To see the first assertion, a*num(r)=b*den(r), so M divides b*den(r).
Multiplying by D and subtracting the supplied congruence times den(r) gives
M | D*c*den(r). Taking natural absolute values and extracting the gcd gives
the second assertion. Thus cancellation in the final coefficient pair is
fully included, not ignored.

The main general declarations are

* congruence_dvd_derivative_times_reduced_denominator
* reduced_denominator_retains_congruence.

## Direct-series Padé consequence

Use the hypotheses of DirectPadeDerivativeCongruenceNotes.md:

    Q in Z[z], P in Q[z],
    deg P<N, deg Q+L<=N, L>=2,
    coeff_k(QF-P)=0 for every k<=N,
    P(1)=b in Z, Q(1) nonzero.

Let S_L=sum_(k<L) 1/(k!-1), with the two initial zero summands, and
D_L=den(S_L). The previous verified congruences are

    L! | Q(1),
    L! | D_L*(b-Q'(1)).

For the REDUCED rational r=b/Q(1), primitive_pade_denominator_divisible proves

    L!/gcd(L!, |D_L*Q'(1)|) divides den(r).

If Q'(1) is nonzero, the numerical consequence is

    L! <= D_L*|Q'(1)|*den(r).

The file also records the conditional consequence that all of L! survives
when gcd(L!,|D_L*Q'(1)|)=1. No claim is made that this coprimality condition
holds, or is achievable at large L, for a useful approximation family.

## Remaining gap

The retained divisor can equal one, including when Q'(1)=0. No bound on
D_L*Q'(1) or on its gcd with L! has been obtained for an infinite useful family.
Large reduced denominators by themselves do not imply an irrational limit.
There is still no small nonzero integer-form family for the target, and no
conclusion about real versus p-adic limits.

This makes the arithmetic statement explicitly reduction-aware. It does not
supply the missing analytic/arithmetic construction and does not settle the
original conjecture.

No numerical search was run. The compilation log is
/tmp/direct_pade_primitive_denominator.log. The exploratory API check is
/tmp/PrimitivePadeAPI.lean and is not part of the submission. All checks have
completed; no process is pending.
