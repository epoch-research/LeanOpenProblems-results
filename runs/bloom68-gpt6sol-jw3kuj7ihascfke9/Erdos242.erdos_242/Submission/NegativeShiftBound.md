# A uniform obstruction to Type-II factorizations of fixed negative shifts

**Status:** The new bound and its infinite-prime consequence have sorry-free
proofs in `NegativeShiftBound.lean`. Neither file imports or changes
`Submission/Spec.lean`. These results obstruct a **particular family of
Type-II certificates**, not the full Type-II axis or the Erdős–Straus
conjecture.

Write `h=4m−1` and require `m,d>0`, `d∣m²`, `h∣p+4d`. The genuinely
variable-modulus proposal “choose an appropriate factor `h` of `p−r`”
actually has a **uniform bound for every fixed positive shift `r`**:

> If `r≤p` and `h∣p−r` as well, then `4m ≤ r²+2r`.

The proof does not assume `p` is prime and does not need `4d<p`.
Subtracting the two divisible numbers gives `h∣r+4d`. Set
`e=m²/d`. Since `16m²=h(4m+1)+1`, multiplying `r+4d` by `4e`
gives the exact dual condition `h∣4re+1`. Its quotient
`u=(4re+1)/h` is `3 (mod 4)`, so `u≥3` and

    4re+1 ≥ 3(4m−1)  ⇒  re ≥ 3m−1 ≥ 2m.

Multiplying by `d`, using `de=m²`, and canceling positive `m` yields
`2d≤rm`. The original quotient `t=(r+4d)/h` satisfies

    th=r+4d≤r+2rm≤r(4m−1)=rh,

so `1≤t≤r`. As `th=r+4d` and `h=4m−1`, we have `4|(r+t)`.
Set `c=(r+t)/4`, so `2c≤r` and `d+c=tm`. Crucially,

    d∣m²  ⇒  d∣(tm)²=(d+c)²  ⇒  d∣c².

Thus `d≤c²`, `m≤tm=d+c≤c²+c`, and
`4m≤4c²+4c≤r²+2r`. In Lean these assertions are
`negative_shift_parameter_bound` and `negative_shift_typeII_bound`.
The **divisor** conclusion `d∣c²`, not just a quadratic sign, is the
reason this controls every factor `h` of the shift.

**Infinitely many prime failures of every prescribed finite list.** For
arbitrary `R,N` let `B=R²+2R`. The previously proved
`Erdos242.hard_primes_escape_bounded_modular_parameters B (max N R)`
(in `Submission/Partial.lean`) gives a prime `p>max(N,R)`, `p≡1 (mod 840)`, with no square-divisor
modular certificate at **any** `m≤B`. The bound above puts any
certificate whose modulus divides one of `p−1,…,p−R` into that
excluded range. Hence arbitrarily large hard primes **simultaneously**
defeat all these finitely many negative-shift factor strategies, even
if their factors and their `m` values are selected *after seeing `p`*.
This is `hard_primes_escape_finite_negative_shifts` in Lean. Unlike
merely checking a fixed set of `m`, the argument first proves that
**every possible factor of each fixed negative shift** would force a
bounded `m`. It does not apply to unbounded shifts or to factors of
**positive** shifts such as `p+2`.

**The `p+2` positive-shift proposal also is not universal.** The
existing `SmallShiftRigidity.plus_two_shift_exact` proves that a
full Type-II witness with `h∣p+2` exists for hard `p` exactly when
`p+2` has a divisor `7 (mod 8)`. `NegativeShiftBound.lean` checks
without `sorry` that the hard **prime `p=97`** has
`p+2=99=3²·11`, whose six positive divisors have residue `1` or
`3 (mod 8)`. Thus *no* full square-divisor certificate can use a
factor of `p+2` at this prime. It nevertheless **has** the genuine
full Type-II witness `(m,d,h)=(2,2,7)`:
`d∣m²`, `4d=8<97`, and `7∣97+4d=105`, giving the strictly ordered
identity

    4/97 = 1/28 + 1/194 + 1/2716.

This counterexample is **only** to the `p+2` subfamily, not to full
Type II or Erdős–Straus. The similarly audited prime `66529` in
`SmallShiftRigidity.md` defeats more short positive-shift tests but
also has full Type-II solutions.

**Remaining pointwise gap.** `TypeIIOffsetBound.full_square_axis_iff_typeII`
identifies the full `d∣m²`, `4d<p` axis with the Type-II branch on hard
primes, while `good_iff_hard_typeI_or_full_square_axis` retains Type I.
Proving full Type-II coverage for every hard prime would be *stronger*
than the original conjecture. Neither the negative-shift obstruction,
the failed `p+2` subfamily, CRT exclusions of bounded `m`, reciprocity
signs, nor finite data supplies a prime failing **all** Type-II
moduli, much less one failing Type I as well. A universal proof still
must find an **exact** residue `d≡−mp (mod 4m−1)` among divisors
`d∣m²` with `4d<p` for *each* hard prime (or use Type I when it is
available).

Verification: `lake env lean Submission/NegativeShiftBound.lean` and
`lake build Submission.NegativeShiftBound` check the stated theorems;
`#print axioms` for the universal bound and infinite-prime corollary
shows only `propext`, `Classical.choice`, and `Quot.sound`, without
`sorryAx`. The finite prime's fraction identity can be checked using
exact rational arithmetic.
