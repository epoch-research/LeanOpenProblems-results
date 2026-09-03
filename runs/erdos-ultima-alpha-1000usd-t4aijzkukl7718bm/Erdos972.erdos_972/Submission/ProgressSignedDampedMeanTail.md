# Signed scalar damped tail — verified, not a settlement

Spec.lean is unchanged and the original conjecture remains unresolved.
No sufficient prime-pair lower bound or irrational counterexample was found.

New file: SignedDampedMeanTail.lean.
Namespace: Erdos972SignedDampedMeanTail.
The file compiles; its principal axiom audits contain only propext,
Classical.choice and Quot.sound.

## Signed finite Abel bound

For any nonnegative antitone weights w(n), if every partial sum of z through
K has absolute value at most E, then

    |sum_{n<K} w(n)z(n)| <= w(0) E.

The proof retains the endpoint and telescopes the total variation exactly.

## Actual Möbius scalar tail

Let m(X)=sum_{d<=X} mu(d)/d. If |m(X)|<=eta for EVERY X>=D, then for every
t>=0 and M>=D,

    |divisorMean(M,dampedCoefficient(t))
       -divisorMean(D,dampedCoefficient(t))| <= 2 eta D^(-t).

For t>0, taking M to infinity gives the same bound for the full scalar tail.
There is no inverse-t loss here. This improves the previously verified
absolute estimate D^(-t)/t.

The already proved signed limit m(X)->0 supplies the uniform conclusion:
for every epsilon>0, eventually in D, for EVERY t>0,

    |divisorMean(D,dampedCoefficient(t))-dampedMean(t)|
       <= epsilon D^(-t).

The cutoff threshold is independent of t.

## Precise limitations

1. The normalized smooth Mangoldt scalar divides this error by t. The
   qualitative m(X)->0 threshold gives no claimed log-rate and cannot be
   used as though epsilon were freely epsilon_D=t_D*o(1) at D=N^delta.
2. These sums have scalar weights mu(d)/d. The arithmetic prime-input tail
   has mu(d) times the ACTUAL divisor row. No signed partial-sum estimate
   for that latter sequence has been proved here. Applying this scalar
   result to it would be invalid.
3. Consequently this improvement does not justify a bounded-t*log N mean,
   a positive prime-detecting minorant, or the original infinitude claim.

No unproved assertion has been inserted into Spec.lean and no incomplete
proof has been submitted.
