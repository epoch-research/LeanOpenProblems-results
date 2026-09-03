# Prescribed means at every finite cyclic modulus

## Task status

The original infinite-set conjecture is still unresolved. `Spec.lean` is
unchanged and still contains its original `sorry`. No proof has been
submitted. The results below do not assert compatible integer prefixes.

## Checked new finite results

`EveryPrimeCyclicFamilyExplore.lean` converts the every-prime plane family
into cyclic templates at modulus (p*H)^2. Level i<=2H has mean

    nu = (2*H*D*i)^2

and relative error <=5/H. D is fixed before p.

`CyclicDensityTransferExplore.lean` combines cyclic padding with a density
comparison. If source modulus M and target modulus N satisfy

    N*nu <= M*mu <= (1+sigma)*N*nu,
    nu <= rho*mu,

and the source's relative error is delta, the padded set has error at most

    (2*delta + sigma + (4+2*delta)*rho)*mu.

`CyclicMeanTuningExplore.lean` proves:

    For every epsilon>0 there exist a,b>0 such that for every positive
    modulus N and every real mean mu with a<=mu and b*mu<=N, there is
    B subset ZMod N with all cyclic self-counts within epsilon*mu of mu.

The quantitative form gives error (39/H)*mu. The parameters a,b depend
only on H. This is valid at EVERY modulus, not only selected primes or
prime squares.

Parameter selection uses x=sqrt(N/mu), t=ceil(x), and Bertrand to obtain
2DHt<p<=4DHt. Then i=floor(p/(2Dt)) lies between H and 2H. The floor and
ceiling errors give

    (2Dix)^2 <= p^2 <= (1+15/H)*(2Dix)^2.

Density transfer finishes once mu is larger than a fixed multiple of the
largest source mean.

`CyclicAsymptoticExplore.lean` proves that ANY divergent sublinear target
f(N) is uniformly realizable by independently chosen finite cyclic sets:

    f(N) -> infinity and f(N)/N -> 0
    imply existence of B_N subset ZMod N with
    sup_z |r_{B_N,cyclic}(z)/f(N)-1| -> 0.

An actual sequence B_N is selected by finite minimax at each modulus.
In particular, for every c>0, the logarithmic cyclic analogue holds at
every modulus, uniformly over target residues. It is not necessary to
restrict N to a subsequence or to prime moduli.

All principal declarations were axiom-audited in:
- CyclicMeanTuningAxiomCheck.lean
- CyclicAsymptoticAxiomCheck.lean
Only propext, Classical.choice, and Quot.sound occur.

## Limitation

The choice B_N is independent for each N. Neither the minimax selection nor
padding proves that these sets are restrictions of a single infinite A.
Moreover cyclic flatness is not the correct full integer-prefix profile.
No control of the transition mixed counts has been established.
