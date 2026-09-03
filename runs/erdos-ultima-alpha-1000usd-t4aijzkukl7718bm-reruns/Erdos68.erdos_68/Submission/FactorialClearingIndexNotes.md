# A superlinear factorial-clearing index (not a solution)

`Submission/FactorialClearingIndex.lean` proves:

* `not_dvd_double_factorial`: for every k>=9, k!-1 does not divide (2k)!;
* `eventual_clearing_index_gt_linear`: for every fixed natural C, eventually
  every N such that k!-1 divides N! satisfies C*k<N.

The second statement says that the least factorial index clearing the
individual denominator k!-1 grows faster than every fixed linear multiple
of k. No least-index function is needed in the formal statement.

## Proof

The denominator k!-1 is coprime to k!. Define integers B(C,k) recursively by

    B(0,k)=1,
    B(C+1,k)=B(C,k)*choose((C+1)*k,k).

Binomial factorial identities give

    B(C,k)*(k!)^C = (C*k)!.

The crude binomial bound choose(n,k)<=2^n gives

    0<B(C,k)<=2^(C^2*k).

If k!-1 divides (C*k)!, coprimality therefore implies

    k!-1 divides B(C,k),
    k!-1 <= 2^(C^2*k).

For fixed C this fails eventually, because factorial growth dominates every
fixed exponential. Factorial divisibility is monotone in its index, giving
the claimed bound on every clearing index N.

For C=2, use the sharper central-binomial bound choose(2k,k)<=4^k and the
inductive inequality 4^k<k!-1 for all k>=9.

## Limitations

This theorem does not assert that k!-1 has a prime factor larger than C*k.
A prime-power multiplicity can also prevent divisibility by (C*k)!.
It does not control cancellation when rational summands are combined, or the
reduced denominators of rounded approximations. It is an obstruction to a
simple clearing strategy, not an irrationality proof.

The file compiles and its two printed axiom checks list only propext,
Classical.choice, and Quot.sound. Spec.lean remains unchanged and unproved.
