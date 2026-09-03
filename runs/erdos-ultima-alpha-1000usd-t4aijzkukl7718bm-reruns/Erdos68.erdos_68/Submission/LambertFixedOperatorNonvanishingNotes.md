# Fixed Lambert shift operators cannot vanish eventually

Verified auxiliary work, NOT a settlement of Erdős 68. Spec.lean remains
unchanged and retains its original sorry. No complete proof or disproof has
been obtained, and no new submission check was made.

LambertFixedOperatorNonvanishing.lean compiles without warnings and has a
current olean. Its four principal printed axiom audits contain only propext,
Classical.choice, and Quot.sound.

## Prime-index coefficient test

Let a_n be the original Lambert coefficients and c_n=a_n/n!. For fixed integer
weights w_0,...,w_D, put

    F_w(n)=sum_(i=0)^D w_i*c_(n+i).

If p=n+D is prime and p does not divide w_D, then F_w(n) is nonzero.
Indeed, (p-1)! times the earlier terms is an integer z, while a_p=1.
Vanishing would imply p*z+w_D=0, contradicting the nondivisibility.

For w_D nonzero, choose a prime

    p >= H+D+abs(w_D)+1.

Then n=p-D>=H and the prime test applies. Thus every fixed nonzero integer
shift operator is nonzero at arbitrarily late indices. Clearing the finitely
many rational weights extends this statement to rational operators. The
clearing multiplier in the proof is the product of their reduced denominators;
no small-height assertion about that multiplier is made.

## Tail operators at an arbitrary real endpoint

For any real x define

    T_w(n)=sum_(i=0)^D w_i*(x-S_(n+i)),
    S_m=sum_(j=0)^m c_j.

The file proves the exact identity

    T_w(n)-T_w(n+1)=F_w(n+1).

Consequently T_w is nonzero at arbitrarily late indices for every fixed
nonzero rational operator, even without assuming anything about x. At a
prime-detected nonzero coefficient form, at least one of the corresponding
two adjacent tail forms is nonzero.

This is frequent nonvanishing, NOT eventual nonvanishing at every index.
The conclusion holds even for rational x such as zero. In particular it
cannot, on its own, prove irrationality of the target endpoint value.

Principal declarations:

* coefficientForm_ne_zero_at_prime
* integer_operator_frequently_ne_zero
* rational_operator_frequently_ne_zero
* tailForm_sub_succ
* tail_operator_frequently_ne_zero

## Remaining quantitative gap

In the existing boundary-lattice construction the operator, its degree, and
its coefficient height vary with the approximation parameter. The new theorem
does not provide a nonvanishing index compatible with that construction's
boundary denominator and error estimates. Moving a fixed operator to a later
prime-detected index also changes the rational boundary that must be cleared.
No uniform bound overcoming this cost has been proved.

The accompanying reviews of higher signed-product differences, long-offset
row separation, and factorial coefficient recurrences did not yield a new
integer-form family. No complete informal proof is awaiting formalization.
There is no pending computation or compilation. The original conjecture is
still unproved and undisproved in this workspace.
