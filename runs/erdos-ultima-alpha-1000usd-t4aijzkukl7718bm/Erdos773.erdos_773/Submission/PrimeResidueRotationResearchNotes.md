# Prime-residue restriction on rational rotations

This does NOT settle Erdos 773. The new module is auxiliary and is not
included in Spec.lean. No improved Sidon exponent has been obtained.

## Verified result

`PrimeResidueRotation.lean` imports only FormalConjecturesUtil. For an odd
prime l and integers a,b,c all congruent to 1 modulo l, it proves:

* If p*a+r*b=q*c and q^2=p^2+r^2, then l divides p or r.
* Suppose p=+/- (u^2-v^2), r=+/- 2uv, q=u^2+v^2, and
  u, v, u-v, u+v are all nonzero. Then l^2 <= 2q.

The signs of the two numerators are independent. Interchanging a and b
also handles the corresponding interchange of numerator coordinates.

The first claim follows by reducing the linear relation modulo l and
squaring: 2pr is divisible by l. Primality and l>2 cancel the factor two.
Factoring the two numerator forms shows that l divides one of u, v, u-v,
u+v. Nondegeneracy and the elementary divisor bound then give l^2<=2q.
No Gaussian factorization or rational-parameterization theorem is silently
assumed in the statement: the displayed parameter forms are explicit
hypotheses.

The carrier `roots l K` consists of l*k+1 for 0<=k<K. It has cardinality K,
is contained in [1,l*K], and every member is 1 modulo l. The theorem
`roots_no_small_rotation` rules out the displayed parameterized rotations
when 2*(u^2+v^2)<l^2. This is not a claim that the carrier is Sidon.

The module compiles without warnings or admissions and has a built olean.
All five printed principal axiom audits use only propext, Classical.choice,
and Quot.sound. Log:

    /tmp/prime-residue-rotation.log

## Remaining gap

This arithmetic restriction is a simpler way to exclude a range of small
denominators than the earlier digit-sphere lifting argument. It does not
supply a favorable count or a selector for the surviving large-denominator
collisions. No power-saving upper bound for arbitrary Sidon subsets was
obtained either.

Spec.lean remains unchanged, with its exact conjecture and one sorry for
0<epsilon<1/3. Its established endpoint is eventually M(N)>=N^(2/3).
No incomplete result was submitted as a settlement.

## Explicit limit at quadratic height

The module now also proves `quadratic_height_collision`. For every integer
l>=1, the four positive roots

    a = 3*l+1,
    b = 10*l^2+7*l+1,
    c = 8*l^2+5*l+1,
    d = 6*l^2+5*l+1

satisfy a<d<c<b, are all 1 modulo l, and satisfy a^2+b^2=c^2+d^2.
They are below the stated quadratic height 10*l^2+7*l+1. The polynomial
identity and all inequalities are checked in Lean; no primality hypothesis
is needed for this collision.

Consequently `residue_carrier_not_sidon` proves that `roots l K` is not a
square-Sidon carrier whenever K>=10*l+8. This is a limitation of retaining
the WHOLE residue carrier, not an upper bound on its largest Sidon subset,
and not a disproof of Erdos 773. It makes explicit why the preceding
small-denominator exclusion cannot simply be extended to all collisions.

All seven printed principal audits are now clean, using only the permitted
axioms. The module builds without warnings or admissions.
