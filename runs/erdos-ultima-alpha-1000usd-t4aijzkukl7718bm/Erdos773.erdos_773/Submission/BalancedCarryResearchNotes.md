# Balanced carry obstruction

This does NOT settle Erdos 773. The original conjecture in `Spec.lean` is
unchanged and still has one admission at line 2031 for 0 < epsilon <= 1/3.

## Verified family

`BalancedCarryObstacle.lean` proves the following. Set u=t+39, B=3*u^2,
and H=33*u. The four words, constant coefficient first, are

    [21,0,219,0,15u,0,219,0,309,0,33u,15u,0,33u,0,0,1]
    [309,0,219,0,33u,0,219,0,21,0,15u,33u,0,15u,0,0,1]
    [219,0,21,0,15u,0,309,0,219,0,33u,33u,0,15u,0,0,1]
    [219,0,309,0,33u,0,21,0,219,0,15u,15u,0,33u,0,0,1].

They have:

* identical complete digit histograms;
* leading digit 1, lower digits divisible by 3, and constants 3 modulo 9;
* common digit sum 769+96u < B;
* common squared-digit sum 191845+2628u^2;
* every digit <= H, with H^2=363B and 2H<B;
* a nontrivial equal-square-sum relation after evaluation at B.

At t=0, B=4563 and the root gcd is 3 (kernel-verified). The gcd is not
uniformly 3 for all t: for example t=10 has gcd 507. No primitive-family
claim is being made.

A stronger exact polynomial certificate is proved in Lean:

  P0(X)^2+P1(X)^2-P2(X)^2-P3(X)^2
    =216 X^15 (B-X) (X^2-1) (X^6-1).

Thus this is not a formal zero norm identity. The evaluation at B is essential.

The file also verifies that, for every real delta>0, eventually

  H <= B^(1/2+delta),

and that for every natural C there exists a member with C*H<B. Consequently
one cannot replace the quadratic-order carry bound by a fixed subquadratic
power bound merely by adding the stated histogram and Eisenstein coefficient
conditions. This is not an upper bound for arbitrary Sidon subsets.

## Algebraic origin

Use the earlier rational Gaussian factorization with a variable denominator:

  Q(X)=X^2+(24-9i)X/K+(24+9i)/K,
  R(X)=X^6+(8-3i)K X^3+(8+3i)K.

Take the components of (1+i)QR and (1+i)conj(Q)R, substitute X^2, and
move the small fractional leading-block coefficients to the preceding empty
positions at the evaluation base. Unlike the earlier construction with fixed
K=96, choose K=3u and B=K^2/3=3u^2. Then 15B/K=5K=15u and
33B/K=11K=33u. This balances the two kinds of large digits at sqrt(B).

## Verification

Command:

  lake env lean -s 65536 Submission/BalancedCarryObstacle.lean

All nine printed audits use only propext, Classical.choice, and Quot.sound.
Log: `/tmp/balanced-carry.log`. No admissions or new axioms were used in this
file. `Spec.lean` SHA-256 remains

  917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.

## Further ideas examined (not established positive results)

Rational rotations still give a useful sufficient condition in a genuine
vector model: if x,y,z,w have the same Euclidean norm, z=a*x+b*y,
w=-b*x+a*y, a^2+b^2=1, and a*b is nonzero, then <x,y>=0. Positive
vectors cannot satisfy this. The missing step is lifting integer root
relations to such vector relations without uncontrolled carries. No such
lifting argument was obtained.

Requiring all digits to be distinct or choosing a prime base was considered,
but neither has yielded a valid positive theorem. In particular, prime bases
do not by themselves rescue the weaker Eisenstein-only criterion; see the
exact mathematical observation below. It does not address the full histogram
condition at prime bases.

## Prime-base observation (mathematics only, not yet formalized)

Let v>=25 and let B satisfy 6v^2 <= B < 6(v+1)^2 and 3 not dividing B.
Put r=3B-18v^2. Then the three degree-two words

  A=[r+36, 9, 1],
  D=[72v+36-r, 12v+15, 1],
  C=[36v+36-r, 6v+15, 1]

have positive digits bounded by 72v+36 and less than B/2. Each lower digit
is divisible by 3 and each constant digit is not divisible by 9. Their
values satisfy A(B)^2+D(B)^2=2*C(B)^2 nontrivially. To check this, put
x=B+3v+6 and y=3v. The values are respectively x^2-y^2-2xy,
x^2-y^2+2xy, and x^2+y^2.

Every sufficiently large integer B lies in such a window for some v. Thus
this includes all sufficiently large prime bases. These three words do NOT
have a common histogram or common digit norm, and their constants need not
all be 3 modulo 9 (some are 6 modulo 9). Do not treat this observation as a
counterexample to the stronger combined prime-base/histogram candidate.

A convenient explicit specialization is B=6v^2+v+1. The digits become

  [3v+39,9,1], [69v+33,12v+15,1], [33v+33,6v+15,1].

For example v=30 gives the prime base 5431. These observations were checked
algebraically but have not been promoted to Lean theorems in this continuation.


## Subsequent stronger result in this continuation

`UniversalCarryObstacle.lean` now gives a fully verified degree-35 obstruction
for every B >= 900000000 with B % 3 = 2, including prime bases. Unlike the
three-word prime-base observation above, the new four words DO share a full
histogram and a common constant digit congruent to 3 modulo 9. They also have
small total digit sum and height O(sqrt(B)). See `UniversalCarryResearchNotes.md`.
This remains a method obstruction, not a disproof of Erdos 773.
