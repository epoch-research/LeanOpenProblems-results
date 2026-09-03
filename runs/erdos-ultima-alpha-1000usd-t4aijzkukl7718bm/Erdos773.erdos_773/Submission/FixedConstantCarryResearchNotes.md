# Fixed constant digit 3: verified carry obstruction

This does NOT settle Erdős 773. `Spec.lean` is unchanged, with its one admission
at line 2031. No proof submission has been made.

## New verified family

`FixedConstantCarryObstacle.lean` constructs degree-19 words. With constant
coefficient first, they are:

    [3,12,24,18,v+3,9,30,72,60,3v+9,15,66,120,84,5v+15,3u,9u,15u,3u,1]
    [3,18,24,12,v+3,15,84,120,66,5v+15,9,60,72,30,3v+9,3u,15u,9u,3u,1]
    [3,18,24,12,v+3,9,60,72,30,3v+9,15,84,120,66,5v+15,3u,15u,9u,3u,1]
    [3,12,24,18,v+3,15,66,120,84,5v+15,9,30,72,60,3v+9,3u,9u,15u,3u,1]

They have identical histograms, common digit sum 541+30u+9v, and common
squared-digit sum 324u^2+35v^2+210v+37171. Every lower coefficient is divisible
by 3 when 3 divides v. For u>0, every digit is positive. If u>=2 and v>=1,
every interior digit is greater than 3: the constant digit 3 occurs exactly
once, and the leading digit is 1. There are still other repeated digits.

The exact identity is

    P0(X)^2+P1(X)^2-P2(X)^2-P3(X)^2
      =24 X^25 (uv-X-1)(X-1)(X^5-1).

Thus evaluation at B gives a nontrivial collision whenever B+1=uv and the
digit sum is below B. The first and third words differ at digit 1 (12 vs 18);
the first and fourth differ at digit 5 (9 vs 15).

## Two parameter choices

1. Balanced height: u=v=3(t+20), B=u^2-1. All digits are <=15u, twice each
   digit is less than B, and the digit sum is less than B. In particular,
   H^2=225(B+1). These bases are composite. At t=0 (u=v=60, B=3599), the gcd
   of all four evaluated roots is exactly 1, verified in Lean.
   Do not claim uniform primitivity: at u=v=66 the gcd is 49.

2. Every B>=3635 with B%36=35: u=12, v=(B+1)/12, with 3 dividing v.
   Again every digit is positive and less than B/2, and the digit sum is
   below B. This includes every prime in the indicated progression; no
   primality hypothesis or prime-existence theorem is needed. Here the height
   is linear in B, not O(sqrt(B)).

The final theorem `counterexample_in_progression` packages the entire second
construction as an existential statement about twenty-digit words with all
these conditions and non-Sidon evaluated squares.

## Algebraic source

    q=3+(12+3i)X+(12-3i)X^2+3X^3
    r=1+(4+i)X^5+(4-i)X^10
    Q=X^4+u q, R=X^15+v r.

Compare (1+i)QR and (1+i)conj(Q)R. Replace uv by B+1, carrying one copy of
each product coefficient to the next position. Since q's coefficient list is
conjugate-palindromic with equal real endpoints, the adjacent sums formed by
these carries are permuted by conjugation. The two complex coefficients of r
exchange whole blocks. Unlike the earlier universal family, the real constant
terms of q and r are only 3 and 1, giving constant digit exactly 3.

## Verification

    lake env lean -s 65536 Submission/FixedConstantCarryObstacle.lean

All ten printed audits contain only propext, Classical.choice, and Quot.sound.
Log: `/tmp/fixed-constant-carry.log`. The file contains no admissions.

## Limitations

This refutes a blanket sufficient digit criterion, not Erdős 773. It does not
show that every histogram or sphere class is bad, nor exclude a large Sidon
subclass. It does not give all-distinct digits, fixed inversion count, or the
same position moments. The four inversion counts at u=v=60 are 45,58,49,54
(counted from the constant coefficient).

A separate counting caution remains important: fixing a full histogram and
also imposing total digit sum <B cannot by itself yield near-linear root
counts. Such a histogram has only O(sqrt(B)) distinct digits. This does not
apply to merely fixing a digit sum and digit norm while allowing histograms
to vary.
