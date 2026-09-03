# Uniform clearing obstruction for finite blocks

This is verified auxiliary progress, NOT a settlement of Erdős 68.
`Submission/Spec.lean` is unchanged and still contains its original sorry.
No proof or disproof of the conjecture has been submitted.

`Submission/UniformBlockClearing.lean` compiles, has a built olean, and its
principal axiom audits list only propext, Classical.choice, and Quot.sound.

## Uniform block theorem

For k>=2 and J>=0 put

    B(k,J)=sum_(i=0)^J 1/((k+i)!-1)=P/Q

in lowest terms, Q>0. The file proves:

* `block_den_coprime`: gcd(k!,Q)=1.
* `block_bounds`: 0<B(k,J)<2/(k!-1), independently of J.
* `block_den_lower_bound`: k!-1<2Q.

The coprimality follows termwise and survives reduction of a finite sum.
The analytic bound compares the block with the already verified entire
positive tail, bounded above by (3/2)/(k!-1). Since P is a positive integer,
P>=1 yields the reduced-denominator bound.

Write (Ck)!=b(C,k)*(k!)^C, where

    0<b(C,k)<=2^(C^2*k).

If Q divides (Ck)!, coprimality forces Q to divide b(C,k). Consequently

    k!-1<2*2^(C^2*k).

For fixed C this fails for all sufficiently large k, by factorial growth.
Unlike the older proof in FiniteBlockClearing.lean, this bound is UNIFORM
in J, not just eventual for each fixed J.

The theorem `eventual_reduced_clearing_index_gt_linear` states exactly:

    for every C, eventually in k, for all J,N,
      den(B(k,J)) divides N!  ==>  C*k<N.

Cancellation within the block is fully allowed.

## Moving cutoffs: neither monotonicity nor bounded jumps is needed

Let

    S(k)=sum_(i=0)^(k-1) 1/(i!-1).

(The i=0,1 terms are zero in Lean.)

`no_proportional_cutoff` proves there is no K:N->N satisfying all of:

    K(n) tends to infinity,
    n<=C*K(n) eventually, for a fixed C,
    den(S(K(n))) divides n! eventually.

There is NO monotonicity or jump-size hypothesis.

Indeed both S(K(n)) and S(K(n+1)) have denominators dividing (n+1)!.
If the cutoffs are unequal, their difference is a positive block beginning
at k=min(K(n),K(n+1)). Its reduced denominator also divides (n+1)!, since
it divides the lcm of the two prefix denominators. Both k and the other
cutoff eventually lie past the uniform block threshold for C+1.

If k=K(n), proportionality and k>=1 give n+1<=(C+1)*k.
If k=K(n+1), proportionality gives n+1<=C*k<=(C+1)*k.
Either case contradicts the block theorem. Thus K is eventually constant,
contradicting its divergence.

The helper `block_den_dvd_of_prefix_den_dvd` uses reduced denominators and
an lcm; it assumes no termwise clearing of reciprocal denominators.

## Scope and missing connection

This closes the unbounded-jump and nonmonotone-cutoff loopholes in the earlier
moving-prefix obstruction. It remains an obstruction to a proposed proof
method, not an irrationality proof.

Rationality of the infinite sum does NOT imply the finite-prefix clearing
hypothesis used here. Nor may finite-sum coprimality be passed to the real
limit: it is not a topologically closed condition. The rational comparison
series in NearFactorialRational.lean already warns against this inference.

No proof of infinitely many original carry changes, non-stabilization of
the GCD-corrected approximants, or nonzero integral forms tending to zero
has been obtained. There is no complete informal settlement awaiting Lean
formalization.
