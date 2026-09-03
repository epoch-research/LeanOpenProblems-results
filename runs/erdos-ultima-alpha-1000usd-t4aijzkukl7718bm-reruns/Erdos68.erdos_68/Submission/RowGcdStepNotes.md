# Exact successive-difference test for GCD-corrected approximants

This is auxiliary work, not a settlement of Erdős 68. Spec.lean is unchanged
and still contains the original sorry. No proof or disproof was submitted.

## Verified integer criterion

`Submission/RowGcdStep.lean` compiles and has a built olean. Its principal
axiom audits list only propext, Classical.choice, and Quot.sound.

Using the existing definitions

    F_n=sum_(k=2)^n floor(n!/(k!-1)),
    g_n=gcd(F_n,n!),
    c_(n+1)=F_(n+1)-(n+1)*F_n,
    Q_n=(F_n+g_n)/n!,

set

    D_n=c_(n+1)+g_(n+1)-(n+1)*g_n.

The file verifies exactly:

    Q_(n+1)-Q_n = D_n/(n+1)!,
    D_n=0 iff Q_(n+1)=Q_n,
    D_n=0 eventually iff Q_n is eventually constant,
    Irrational alpha iff for every N there is n>=N with D_n!=0.

This is a reformulation of the existing GCD non-stabilization criterion.
The infinite nonvanishing assertion is NOT proved.

## Finite exact check

The external script `/tmp/check_gcd_corrections.py` computes F_n and g_n with
GMP integers and tests the integer equality

    c_n+g_n=n*g_(n-1).

For every base 3<=n<=5000 it found inequality. The earlier base n=2 is
also unequal directly. This extends the previous external check through 999.
The log is `/tmp/gcd-corrections-5000.log`. The script completed in about
388 seconds; no check is still running.

This finite check has NOT been formalized in Lean and does not establish
any infinite claim or a bound valid for arbitrary n.

## A prime-factor exclusion attempt fails

One possible sufficient route would be to show that at prime p the reduced
denominator of Q_p always retains the factor p, preventing equality with
Q_(p-1). The proposed uniform prime-factor claim is false.

A separate exact calculation through p<=1000 found p dividing F_p+g_p at
p=2,5,41,53,709. In particular,

    g_53=46,   F_53 mod 53=7,
    g_709=92,  F_709 mod 709=617.

At 53 and 709 the prime divides F_p+g_p but not F_p itself. Since p occurs
exactly once in p!, it genuinely disappears from the corrected denominator.
These are external exact calculations, not newly asserted Lean theorems.
They do not imply equality of successive corrected approximants (the check
above found no equality). They only block this simple prime-denominator
argument. No weaker eventual prime statement has been proved either.

## Remaining gap

Rationality would force g_n to equal the positive sublinear real row tail
exactly, eventually. Neither the GCD identity nor its successive-difference
form gives an integer descent: the possible small integer tails can vary.
No arithmetic theorem has been obtained forcing D_n!=0 at arbitrarily large
indices. There is no complete informal settlement awaiting formalization.
