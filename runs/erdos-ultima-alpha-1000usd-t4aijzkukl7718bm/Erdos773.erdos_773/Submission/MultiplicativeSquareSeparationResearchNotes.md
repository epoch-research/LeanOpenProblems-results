# Prime-scaled square fibers: separation, union, and cardinality cost

The original Erdos 773 conjecture remains UNSETTLED. Spec.lean was not edited.
Its sole admission remains at line 17287 for 0 < epsilon < 1/3. The completed
actual lower bound remains eventually M(N) >= N^(2/3).

## New verified module

Submission/MultiplicativeSquareSeparation.lean imports the clean
PrivateModulusPacking module, not Spec.lean. It compiles without warnings or
admissions. Its ten printed audits use only propext, Classical.choice, and
Quot.sound. A built olean is available.

Log: /tmp/multiplicative-separation.log
Namespace: Erdos773.MultiplicativeSquareSeparation

## Prime-power separation

For an odd prime p, p not dividing x, and x<=y,

    p^k divides y^2-x^2
      ==> p^k divides y-x OR p^k divides y+x.

This is proved by factoring the difference and canceling the factor coprime
to p; no integral-domain assumption is made about ZMod(p^k).

Consequently x |-> x^2 mod p^k is injective on roots x<=H coprime to p
whenever 2H<p^k. Multiplying the roots by a unit modulo p preserves this
injectivity.

Define scaledValues(t,A)={(t*a)^2 : a in A}. If p^k divides s, p does not
divide t or any member of B, every b in B is at most H, and 2H<p^(2k), then

    positiveDiffs(scaledValues(s,A))
      and positiveDiffs(scaledValues(t,B)) are disjoint.

The first seed A need not be Sidon for this separation statement.

## A genuine finite union construction

prime_scaled_union proves Sidonness of the union of p-scaled copies of one
seed A under all of the following explicit hypotheses:

* A subset [1,H], and A's square values are Sidon;
* every a in A is 1 modulo q;
* the scale labels R have PairMatching q R;
* all p in R are odd primes with p^2>2H;
* every seed root is coprime to every scale prime.

The proof uses modular matching for the labels, individual scaled Sidonness,
and the actual positive-difference separation just proved. It does not infer
Sidonness from the last two properties alone.

prime_union_card proves exact union cardinality |R|*|A| under prime-scale and
unit-root hypotheses. union_subset_squares proves actual containment in the
first P*H squares when R subset [1,P] and A subset [1,H].

## Mixed labels are an essential gap

unmatched_prime_example verifies the seed {1,2} and scales {3,7,13}. All the
prime, unit, and shortness conditions hold at H=2. Nevertheless

    3^2+14^2 = 6^2+13^2 = 205.

Thus dropping label matching is invalid, even for these prime-scaled fibers.
The certificate is checked in the kernel. This is not a counterexample to
the original conjecture.

## Two-thirds ceiling on this common-residue scheme

For q>0 and |A|>=2, the common-residue cardinality cost and PairMatching imply

    |R|*|A| <= 2H.

This uses |R|^2<=2q, (|A|-1)q<=H, and |A|<=H. Therefore, if 2H<=P^2,
construction_cube_bound proves

    |union_p scaledValues(p,A)|^3 <= 4(PH)^2.

The cardinality theorem itself does not assume scale containment in [1,P];
that containment is separately supplied by union_subset_squares when PH is
used as a root-height bound. For a nonempty scale family with every p<=P and
p^2>2H, its hypothesis 2H<=P^2 follows immediately. Empty families have no
amplification. The |A|>=2 hypothesis is essential to the stated cost argument;
a singleton seed merely rescales the scale set and is not controlled by it.

This is a ceiling on this PARTICULAR common-residue, matched-label scheme,
not an upper bound for arbitrary square-Sidon sets or all multiplicative
constructions. No improved actual Sidon exponent, near-linear selector, or
fixed-power original-conjecture upper bound was obtained. No incomplete proof
was submitted.
