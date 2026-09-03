# Fixed-modulus criteria for the actual carried series

This is verified auxiliary progress, NOT a settlement of Erdős 68.
Spec.lean remains unchanged with its original sorry. No proof or disproof
has been submitted in this continuation.

CarriedFixedModulusCriterion.lean compiles without warnings and has a
current olean. Its five principal axiom audits use only propext,
Classical.choice, and Quot.sound. It contains no proof holes.

## Necessary residue pattern under rationality

Let c_n be CongruencePreservingCarry.coeff, the representation preserving
the EXACT original target, and let T_n be its factorial-scaled tail.
If the target equals the rational number q, then the file proves

    n >= 2*(q.den+6),  n even  ==>  c_n == n-1 (mod 4).

This is rational_even_coefficient_mod_four.

To prove it, enclose any sufficiently large index between consecutive
primes p<s<2p. The previously verified rational prime-gap identities give

    T_n = 2p-1-n       at composite indices between them,
    T_s = s*(2p-s)-1  at the final prime.

The new file verifies that odd-index integral tails are even. At even n,
T_n == 1-n modulo four and n*T_(n-1) is divisible by four. The recurrence
c_n=n*T_(n-1)-T_n gives the stated residue.

The enclosing-prime argument uses the existing prime enumeration starting
at five and Bertrand's theorem; no distribution assumption is made.

## Two sufficient infinite-occurrence conditions

1. If arbitrarily late even indices n have c_n even, the target is
   irrational. This is irrational_of_frequent_even_coefficients.

2. If arbitrarily large odd m satisfy

       4 divides c_(4m)-c_(2m),

   the target is irrational. This is irrational_of_frequent_dold_mod_four.
   Under rationality the two residues would instead be 3 and 1 modulo four.

NEITHER infinite-occurrence hypothesis has been proved.

The exact original Lambert coefficients do satisfy the latter congruence
for every m>=2. The theorem original_dold_mod_four specializes the existing
Dold prime-power congruence and removes the (2m)! correction, which is
divisible by four. This assertion is about the original coefficients, not
the carried ones, and supplies no inheritance theorem.

## Finite check and limitations

The Lean theorem coefficient_six verifies exactly c_6=26. This is one
parity violation of the necessary eventual pattern, not infinitely many.
It also prevents simply assuming that all actual carried coefficients are
odd. The proof evaluates the finite Lambert prefixes and rational floors;
no unchecked computation or native_decide is used.

An external exact Fraction/Sage calculation through n=120 checked the
explicit carried recurrence. It found both successes and failures of the
mod-four inheritance condition at odd m. For example the residues of
c_(4m)-c_(2m) modulo four at m=3,5,7,9,11 were respectively 1,2,0,1,0.
These external finite instances, apart from the separately proved c_6
value, have not been formalized and are not premises of any Lean theorem.
The calculation has completed; no process is pending.

The preceding informal review considered preserving predecessor and Dold
congruences together by changing the carry modulus. Such a change enlarges
the available tail intervals. No construction retaining all the needed
congruences AND the required linear composite-tail bounds was obtained.
The fact that the original row denominators are odd does not control the
parity of the real floors used in carrying.

There is still no complete informal proof or disproof awaiting
formalization. The final conjecture file was not modified.
