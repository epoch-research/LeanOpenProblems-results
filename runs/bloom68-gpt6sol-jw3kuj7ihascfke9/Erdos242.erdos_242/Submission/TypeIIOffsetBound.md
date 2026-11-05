# The bounded full square-divisor axis is exactly Type II, not merely sufficient

**Status:** new exact equivalence and a sharp size deduction, **not** a proof
that every prime has a Type-II witness or an Erdős–Straus solution. The
sorry-free Lean proofs are in `TypeIIOffsetBound.lean`, importing
`FullSquareAxis.lean` and `CoveringGap.lean` but never `Spec.lean`.
`Spec.lean` is unchanged.

## The previously unproved necessity of `4d<p`

Let `p` be prime, `p<4x`, `2x<p`, and suppose the **full** Type-II
condition holds at `x`: `0<d<x`, `d∣x²`, `a=4x−p∣x+d`. Then

    4d<p.                                                       (1)

**Proof.** Primality and `0<x<p` give `gcd(a,x)=1`, hence
`gcd(a,d)=1`. Put `b=x²/d`; because `d<x`, we have `b>x`.
The exact identity

    d(x+b)=x(x+d)

and cancellation of `d` modulo `a` imply `a∣x+b`. Subtracting the
original congruence shows `a∣b−d`. Set `r=x−d>0`, `q=b−d>0`.
The factorization `db=x²` gives another exact identity

    d q=r(x+d).                                                 (2)

If `4d≥p`, then `a=4x−p≥4(x−d)=4r`; meanwhile `2x<p≤4d`
gives `x<2d`, hence (2) yields `q<3r`. Since `a∣q` and `q>0`,
`4r≤a≤q<3r`, a contradiction. Thus (1) holds for **every** actual
Type-II divisor, not just for a more convenient replacement divisor.
This is `typeII_offset_lt_quarter` in Lean. Primality matters: e.g.
for the composite `p=65`, `x=30`, `a=55`, `d=25` satisfies the bare
divisor and congruence conditions with `4d=100≥p`; here `gcd(a,x)=5`.

## Exact modular reparameterization

For a prime `p≡1 (mod 24)`, define the *full* square-divisor axis

    FullSquareAxis(p) :⇔ ∃m,d>0,
        m≤(p−1)/6,  d∣m²,  4d<p,  (4m−1)∣p+4d.                  (3)

The sorry-free theorem `full_square_axis_iff_typeII` proves **both**
directions of

    FullSquareAxis(p) ⇔ ∃x, p<4x, 2x<p, TypeII(p,x).          (4)

For necessity, the existing `CoveringGap.typeII_modular_parameter`
takes `m=(x+d)/(4x−p)`, proves `d∣m²` and
`(4m−1)∣p+4d`; (1) supplies the missing `4d<p`, and
`FullSquareAxis.full_square_axis_bound` then supplies
`m≤(p−1)/6`. For sufficiency, put `h=4m−1`,
`a=(p+4d)/h` and `x=(pm+d)/h`. Direct calculations show
`4x=p+a`, `0<a<p`, `x+d=am`, and `d<x`; moreover `d∣m²`
implies `d∣(am)²=d∣(x+d)²`, hence `d∣x²`. This gives
**the actual Type-II certificate**, not merely a `Good` proof from a
possibly unrelated decomposition. All natural-number divisions and
strict inequalities are justified in the Lean proof. The `m` bound is
special to the hard-prime residue class; (4) is not asserted for all
prime residues.

Combining (4) with the already proved ordered classification and prime
reduction gives `all_good_iff_typeI_or_full_square_axis`:

    (∀n>2, Good(n))
      ⇔ (∀ primes p≡1 (mod 24),
           [∃x: p<4x, 2x<p, TypeI(p,x)] ∨ FullSquareAxis(p)).  (5)

This is an **exact all-prime condition**, not a proof of its right-hand
side. To settle `Spec.lean` positively one still needs to prove the
disjunction in (5) for *every* specified hard prime (a universal
Type-II witness from (3) would suffice, but is stronger than necessary).
A genuine disproof instead needs a certified prime with **no** Type-I
certificate at **any** eligible `x` and **no** modular pair (3). A
single failed `m`, a failed restricted `d∣m` axis, or arbitrarily many
checked primes does not meet either requirement. The independent new
`MinusTwoBarrier.lean` proves that a modulus dividing `p−2` can never
serve as `4m−1` in (3); it does not cover other moduli.

Verification: `lake env lean Submission/TypeIIOffsetBound.lean` and
`lake build Submission.TypeIIOffsetBound` succeed. Auditing the main
theorems with `#print axioms` shows only `propext`, `Classical.choice`,
and `Quot.sound`, no `sorryAx` or other added axiom. No use of the two
`sorry` declarations in `Submission/Spec.lean` occurs.
