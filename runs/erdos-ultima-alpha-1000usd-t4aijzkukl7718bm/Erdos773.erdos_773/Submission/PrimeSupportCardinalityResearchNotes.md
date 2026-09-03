# Fixed prime-support carrier bound

This does NOT settle Erdős 773. `Spec.lean` is unchanged and retains its
one admission for 0 < epsilon < 1/3. No proof submission was made.

## Verified finite theorem

`PrimeSupportCardinality.lean` imports only FormalConjecturesUtil. For a
finite set P of primes and a finite set A of positive integers, it proves:

    A subset [1,H^k], k>0, primeFactors(n) subset P for every n in A
      ==> |A| <= k^|P| H.

For each prime exponent e, write e=k*(e/k)+(e%k). Every n has a unique
encoding by a positive quotient part m<=H and a function P -> Fin k.
Reconstructing n from this encoding proves injectivity and the count.

Public APIs:

* decomposition: n = quotientPart^k * remainderPart;
* encoding_injective;
* card_le: the stated bound;
* card_le_sq: if k^|P|<=H, then |A|<=H^2;
* log_card_bound: log |A| <= |P| log k + log H, with explicit positivity.

All five printed audits use only propext, Classical.choice, Quot.sound.
The file builds without warnings or admissions. Log:

    /tmp/prime-support-cardinality.log

## Meaning and limits

This bounds the WHOLE fixed-prime-support carrier, independently of any
Sidon requirement. It explains a problem with the proposed use of
exponential-in-rank S-unit estimates: making that rank cost subpower forces
the prime-support rank into a range where the carrier itself is too small.
No S-unit theorem or asymptotic smooth-number estimate has been assumed or
formalized in this module. The finite bound and logarithmic inequality are
the exact verified claims.

The result does not bound arbitrary square-Sidon sets, whose roots need
not lie in a fixed small prime support. It gives no original-conjecture
upper exponent, no new lower exponent, and no negation of erdos_773.

The accompanying review of finite checksum seeds and concatenation yielded
no preservation or amplification theorem. The earlier verified two-block
failure of the 27-root base-81 seed remains relevant; it is not a disproof
of every possible lifting construction.
