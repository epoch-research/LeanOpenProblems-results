# A histogram collision for every sufficiently large base B = 2 mod 3

This does NOT disprove Erdos 773. The main conjecture in `Spec.lean` is unchanged,
with one admission at line 2031. The result here is an obstruction to a proposed
sufficient digit criterion, not an upper bound on arbitrary Sidon subsets.

## Verified theorem

`UniversalCarryObstacle.lean`, theorem `counterexample_for_large_base`, proves:
for EVERY natural B >= 900000000 with B % 3 = 2, there exist four degree-35
digit words with

* leading digit 1;
* the SAME constant digit 192*T, which is 3 modulo 9;
* every lower digit divisible by 3;
* identical complete digit histograms;
* common digit sum 4801+4800*T+160*u < B;
* every digit at most H=309*(T+1)+33*u, where H^2 <= 8000000*B;
* a nontrivial equal-square-sum collision after evaluation at B.

`digit_bounds_of_sum` also proves every digit is less than B/2 under the
stated digit-sum bound. This works for all sufficiently large PRIME bases
that are 2 modulo 3, not just specially factored composite bases. A prime
hypothesis is not needed for the theorem.

The constant digit is identical across the four words but depends on B.
Do not strengthen this to an arbitrary preassigned constant digit, such as 3.
The words have repeated digits. No theorem about all-distinct-digit classes
or every possible histogram class has been proved. No primitive-gcd assertion
has been proved for this new family.

## Parameter selection

Set s=floor(sqrt(B)), u=3*(floor(s/3)+1), and T=u^2-B. Then

  s < u <= s+3, 3 divides u,
  B+T=u^2, 0<T<=6u, T=1 modulo 3,
  u>=30000.

These imply the displayed sum and height bounds. The parameter selection and
all inequalities are formalized in `large_base_parameters`.

## Pattern and algebraic source

Let sigma=(0,1,0,-1,0), and set

  q(X)=sum_{j=0}^4 (24+9*i*sigma_j) X^j,
  r(X)=sum_{j=0}^4 (8+3*i*sigma_j) X^(6j),
  Q(X)=X^5+u*q(X), R(X)=X^30+u*r(X).

As usual, compare the components of (1+i)QR and (1+i)conj(Q)R.
A product coefficient is k*u^2. Since u^2=B+T, replace that coefficient
at position j by k*T at position j and a carry k at position j+1.
These carries are incorporated into the digit words.

The isolated +1 and -1 signs have sign-symmetric transitions. Flipping either
factor's signs therefore permutes the resulting digits, including the carries.
This is why a full histogram survives, unlike simpler consecutive +/- patterns.

For the first word, the five blocks of length six correspond to
sigma=(0,1,0,-1,0). The three block types are

  tau=0:
    [192T,120T+192,192T+120,264T+192,192T+264,8u+192]
  tau=+1:
    [120T,21T+120,120T+21,219T+120,120T+219,5u+120]
  tau=-1:
    [264T,219T+264,264T+219,309T+264,264T+309,11u+264].

The final six digits are [24u,15u,24u,33u,24u,1]. The other words flip
sigma signs in the first factor, second factor, or both. The Lean file uses
a 22-symbol alphabet and a closed four-by-36 pattern to encode the permutations.

The exact norm-difference certificate, also formalized, is

  P0(X)^2+P1(X)^2-P2(X)^2-P3(X)^2
    =216 X^42 (u^2-T-X) (X^2-1) (X^12-1).

Evaluation at X=B makes this zero. It is not a formal zero polynomial.
The first words differ at digit 1, or digit 6, when T>0. A generic digit
encoding injectivity lemma proves that these are genuinely different roots.

## Verification and performance

Both the entire file and all nine printed axiom audits are clean:

  lake env lean -s 65536 Submission/UniversalCarryObstacle.lean

Log: `/tmp/universal-carry.log`.

Direct simplification of four full 36-entry vectors under integer casts timed
out. The successful version uses an alphabet defined by a Nat pattern match,
a finite pattern-permutation certificate (`decide +kernel`), and NATURAL value
expansions before casting to integers. The final polynomial certificate is
then proved with `ring`.

For the nontriviality proof, `change` to the known digit expressions was more
reliable than unfolding the entire vector with `norm_num`. There are no
admissions, new axioms, native evaluation proofs, or debugging IO in the file.

## Main status

This rules out prime-base and common-constant-digit repairs of the blanket
histogram/Eisenstein/small-total-sum sufficient condition for the indicated
bases. It does not show every large class is bad, and it does not settle the
original conjecture. Nothing has been consolidated into `Spec.lean` from
these obstruction files.
