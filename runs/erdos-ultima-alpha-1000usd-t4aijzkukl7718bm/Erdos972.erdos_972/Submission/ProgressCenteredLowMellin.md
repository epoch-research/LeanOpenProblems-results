# Centered low-frequency four-factor integral — verified, still unsolved

Spec.lean is unchanged and retains its original sorry. The original
conjecture is STILL UNSOLVED. No irrational counterexample or sufficient
high-frequency bound has been obtained. No completed proof was submitted.

New files:

* CenteredLowMellinBlock.lean
* DivisorMeanRecenter.lean

Both compile. Principal declarations audit with only propext,
Classical.choice, and Quot.sound.

## Explicit finite low-frequency integral

Define

    A(U,M,t) = sum_{M<n<=2M} [a_U(n)+m(U)] n^(it),
    B(V,M,t) = sum_{M<n<=2M} Lambda_{>V}(n) n^(it),

where a_U=mu_{>U}*zeta is the actual Vaughan divisor coefficient and
m(U)=sum_{d<=U} mu(d)/d. The Mangoldt cutoffs V,T are retained.

For U,S>0, U^2,S^2<=M, 0<=H<=min(M/U^2,M/S^2), and any complex kernel
K satisfying |K(t)|<=1/M^2 on [-H,H], the file proves

    ||integral_{-H..H} K(t) A(U,M,t) B(V,M,t)
                    conjugate(A(S,M,t) B(T,M,t)) dt||
      <= 2240*M^2*(1+log(2M))^2/(U*S).

The proof uses the centered coefficient suprema 4M/U and 4M/S, the actual
Mangoldt energy bound

    integral_{-H..H} |B(V,M,t)|^2 dt <= 140*M^2*(1+log(2M))^2,

and Young's inequality on the remaining two factors. It does not replace
Mangoldt factors by unweighted lattice counts.

At U=S=growingCutoff(u), M=u^3, all H<=balancedMellinRange(u), this gives

    norm(integral) <= Budget(u)*u^6,
    Budget(u) = 35840*((1+log u)/growingCutoff(u))^2 -> 0.

This holds at EVERY sufficiently large u, simultaneously for V,T,H,K
under the stated conditions. There is no choice of independent good scales.
No logarithmic Mertens rate is used in this bound for CENTERED coefficients.

## Exact arithmetic centering correction

DivisorMeanRecenter.lean defines arithmetic functions

    centeredCoeff_U = a_U + m(U)*zeta,
    logTail_V = zeta*Lambda_{>V},
    centeredR_UV = centeredCoeff_U*Lambda_{>V}.

It proves exactly

    logTail_V = log-zeta*Lambda_{<=V}
              = typeIPart(1,V)-Lambda_{<=V},
    centeredR_UV = R_UV + m(U)*logTail_V.

Subtracting the same term from the Type-I part gives another exact Vaughan
identity. The centeredBlock used in the integral is proved to be precisely
the Mellin sum of centeredCoeff_U on its positive dyadic interval.

The full covariance correction is also retained exactly:

    Cov(centeredR_UV, centeredR_ST_output) - Cov(R_UV,R_ST_output)
      = m(U)*Cov(logTail_V,R_ST_output)
        +m(S)*Cov(R_UV,logTail_T_output)
        +m(U)*m(S)*Cov(logTail_V,logTail_T_output).

NO SMALLNESS of this correction is asserted by the identity. In particular,
small m(U) cannot simply be multiplied by an unproved uniform covariance
bound or an uncontrolled logarithmic factor.

## Update

The finite and common-scale recentering estimates proposed below have now
been proved in RecenterCovarianceBounds.lean and RecenterCovarianceScales.lean.
See ProgressRecenterCovariance.md. The lower-gap/high-frequency problem
remains unresolved.

## Remaining limitations (at the time of this note)

1. The new integral is explicitly defined and bounded. A full Mellin
   representation/minorant of the sharp floor strip, including dyadic
   restrictions and endpoint errors, has NOT been deduced from it.
2. The frequency range is still o(u^3), hence far below the order-u^6
   bandwidth required by the floor strip at N=u^6.
3. The complete arithmetic recentering correction above has not yet been
   proved o(N) at the actual common good scales in this continuation.
4. No bound on the signed HIGH-frequency contribution follows from the
   low-frequency estimate. The former supremum/energy power-loss problem
   is not solved by this file.

Thus this is a genuine finite low-frequency estimate and an exact change
of decomposition, not a proof or disproof of Erdos 972.

## Possible next finite step (NOT a proved theorem)

For W=growingCutoff(u), write m=m(W), A=typeIPart(W,W),
B=typeIPart(1,W), s=Lambda_{<=W}. Then R=Lambda-A and
centeredR=R+m*(B-s). Existing Type-I row bounds apply to both A and B
because W^2<=root64(u), and logTail=B-s.

A prospective common-scale correction bound can use:

* original/dual Type-I errors for Cov(B,Lambda_output) and Cov(Lambda,B_output);
* the joint Type-I estimate for (B,A), (A,B), and (B,B), retaining its
  main 32*N*|m(U)*m(S)| term;
* |m|<=1 eventually;
* |R|<=4*v*L^2, |B|<=3*v*L^2, |s|<=v*L^2;
* total |s| and total |s_output| <=7*v.

L1 covariance perturbation would make removing the two m*s terms cost at
most 210*v^2*L^2. The other three correction terms would cost at most
E_left+E_right+96*N*m^2+3*E_joint. Since
E_joint=100*(rowError+1)*v^2*L^5 and L>=1, the entire correction can be
absorbed by E_left+E_right+6*(32*N*m^2+E_joint).

This calculation is a PLAN, not a formal declaration. The eventual budget
thresholds must be chosen before one invocation of
exists_two_sided_prime_divisor_scale. It is invalid to intersect the
independently obtained existential good-scale sets.
