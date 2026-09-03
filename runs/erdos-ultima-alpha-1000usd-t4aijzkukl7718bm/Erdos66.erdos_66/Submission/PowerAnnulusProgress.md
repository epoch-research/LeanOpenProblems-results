# Finite power-length annuli

The original conjecture in `Spec.lean` is still unproved and undisproved.
Its statement and `sorry` are unchanged.

## New checked theorem

`Erdos66PowerAnnulus.exists_power_annulus` in `PowerAnnulusExplore.lean`:
for every c>0 and epsilon>0 there exists delta>0 such that, for every N0,
there are N>=N0 and a finite set A supported above N0 with

* r_A(n)/log(n) < c+epsilon for every natural n;
* |r_A(n)/log(n)-c| < epsilon whenever N<=n<=N^(1+delta).

Delta is fixed BEFORE N0. The axiom check in `PowerAnnulusAxiomCheck.lean`
uses only propext, Classical.choice, and Quot.sound.

## Pipeline

1. `RelativeCyclicFamilyExplore`: nested flat cyclic families with a fixed
   coefficient beta>0 before the arbitrarily large period M.
2. `BinaryBlockTransferExplore`: exact carry interpolation
   r_A(qM+t)=lower_B(t)*r_D(q)+upper_B(t)*r_D(q-1), with relative errors
   combining multiplicatively and no accumulated error in q.
3. `FiniteBernoulliExplore`: exact finite product expectations and MGF
   factorization for disjoint binary monomials.
4. `BernoulliConcentrationExplore`: centered MGF bound exp(2*t^2*mean),
   and simultaneous realization if 2*number_targets*exp(-eps^2*V/8)<1.
5. `FiniteRepBernoulliExplore`: each unordered off-diagonal pair gives a
   two-coordinate monomial of weight 2; a diagonal gives a singleton of
   weight 1. Coordinate sets at one target are disjoint. The exact mean is
   the product-probability convolution plus a diagonal correction in [0,1].
6. `RandomConstantProfileExplore`: probabilities sqrt(mu)*b(i+s), s=ceil(mu),
   give finite D with r_D<=mu*(1+eps) everywhere and relative error <eps on
   [q0,L], provided 64*s^2<=eps^2*(q0+1) and
   2*(2L+1)*exp(-eps^2*(mu+1)/128)<1.
7. `ExponentialProfileParametersExplore`: q0=ceil(64*ceil(mu)^2/eps^2),
   L=floor(exp(k*mu)), for 256*k<=eps^2. Eventually q0+3<=exp(k*mu/4)
   and L>=exp(k*mu/2), and the concentration criterion holds.
8. `PowerAnnulusGeometryExplore`: elementary logarithmic normalization.
9. `PowerAnnulusExplore`: take d=min(eps/(16*(c+1)),1/16), then beta from
   the cyclic family, k=min(d^2/256,d*beta/c), a=k*c/beta, delta=a/8,
   mu=c*log(M)/beta and N=M*(q0+3). Translate the binary blocks by M.

`BernoulliAxiomCheck.lean` and `RandomProfileAxiomCheck.lean` check the
probability and representation-count components separately.

## Still missing

There is no globally compatible family of these sets. The periods may be
unrelated; mixed representation counts during transitions are uncontrolled.
Neither these power annuli nor the earlier global upper envelope supplies
an eventual global lower bound. No disproof for all possible sets exists.
