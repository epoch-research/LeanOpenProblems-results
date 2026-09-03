# Separate carry profiles and varying-color transfer

The original conjecture is still neither proved nor disproved. `Spec.lean`
remains unchanged, with its original `sorry`.

## Completed results

`OuterCarryProfileExplore.lean` repeats a cyclic template C modulo M into
all K outer blocks, producing outerLift(C) modulo M*K. For any two templates
C,D, target t modulo M and outer digit 0<=r<K, it proves

  cyclicCount(outerLift(C),outerLift(D)) = K*cyclicCount(C,D),
  lower(outerLift(C),outerLift(D);t+M*r)
      = r*cyclicCount(C,D;t)+lower(C,D;t),
  upper(outerLift(C),outerLift(D);t+M*r)
      = (K-r-1)*cyclicCount(C,D;t)+upper(C,D;t).

If the small cyclic count is within E of mu, each large carry fiber is
within K*E+mu+E of its respective main term r*mu or (K-r)*mu.
This controls the separate fibers even for DIFFERENT C and D.

`ColoredBlockTransferExplore.lean` applies that fact to a varying family
C_i with nonnegative weights w_i and mixed cyclic means beta*w_i*w_j.
Assume every small mixed cyclic count has relative error at most eta.
Write S(q)=sum_{i=0}^q w_i*w_{q-i}. For the actual integer block set made from
the outer lifts, the representation count at q*(M*K)+(t+M*r) differs from

  beta * [r*S(q)+(K-r)*S(q-1)]

by at most

  beta*(K*eta+1+eta)*[S(q)+S(q-1)].

If the two high convolutions are within epsilon*mu of mu, the representation
count differs from K*beta*mu by at most

  beta*mu * [K*epsilon+2*(K*eta+1+eta)*(1+epsilon)].

All the files compile, and `OuterCarryAxiomCheck.lean` checks that the principal
results use only propext, Classical.choice, and Quot.sound.

## What this fixes, and what it does not

This supplies one sufficient extra averaging identity for the carry issue
identified in `EveryPrimeFlatProgress.md`. Neighboring low templates need not
be equal, provided they are first repeated across the outer blocks.

It does NOT supply the scalar high profile for arbitrarily large indices at
a fixed logarithmic coefficient, and it does not compare patterns from
different prime fields. It also retains the difference spikes caused by
repeated copies; no nonzero difference-flat cyclic result is claimed.
There is still no compatible infinite natural-number construction.
