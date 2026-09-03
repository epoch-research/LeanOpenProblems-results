# Prime, including inert-prime, rational specialization fails

## Original problem remains unresolved

No proof or disproof of Erdős 773 was obtained. Spec.lean is unchanged,
with its only admission at line 2031, for 0 < epsilon <= 1/3. No proof was
submitted in this continuation. The earlier rejected incomplete submission
has not become valid.

No actual asymptotic exponent or coefficient was improved. The strongest
actual lower bound remains eventual M(N) >= N^(2/3)/36. The new result is
an obstruction to a proposed sufficient construction, not an upper bound
on a largest Sidon subclass and not a disproof of the original conjecture.

## New verified module

File: Submission/PrimeRationalSpecialization.lean
Namespace: Erdos773.PrimeRationalSpecialization

The theorem arbitrarily_large_prime_obstruction proves that, for every B,
there is a parameter t whose denominator q exceeds B and is PRIME, with
q = 3 modulo 4. Put p=q+1. The four polynomials are

    E_i(X) = X^43 + 6 P_i(X),
    degree(P_i)<43, P_i(0)=1.

The following all hold simultaneously:

* The formal polynomial squares {E_i(X)^2} are Sidon in Z[X].
* Every encoding coefficient is nonnegative.
* Every nonconstant lower encoding coefficient is less than q/100.
* The sum of ALL encoding coefficients, including leading 1 and constant 6,
  is less than q.
* p and q are coprime.
* The exact cleared evaluations n_i=q^43 E_i(p/q) are positive naturals.
* All four n_i are distinct.
* n_0^2+n_1^2=n_2^2+n_3^2 is a nontrivial square-sum collision.

Thus neither prime denominators nor their inertness in the Gaussian
integers repairs this particular specialization claim. The numerator p
is even and composite; no prime-numerator assertion is made. No histogram,
common energy, or primitive-gcd assertion is made.

## Exact algebraic transformation, not a new numerical search

Use the old degree-42 SmallRationalGaussianSpecialization certificate,
whose rational functions are F_0,G_0,U_0,V_0 and raw roots R_i(z). Set

    p=z+1,
    F=F_0, U=U_0,
    G=p G_0+6 z^39,
    V=p V_0.

The four new roots are the real combinations

    FG-UV-FV-GU,
    FG-UV+FV+GU,
    FG+UV-FV+GU,
    FG+UV+FV-GU.

Their norm identity holds algebraically for every rational z. More
specifically raw_shift proves

    new_R_i(z) = (z+1) R_i(z) + 6 z^39 (F_0(z)+sigma_i U_0(z)),
    sigma=(-1,+1,+1,-1).

Let L be the old common denominator and e=10^(-18), so eL is an integer.
If c_ij and v_j are the old coefficient slopes and integer offsets, the
new slopes have numerator

    c'_i1=c_i1-sigma_i eL,
    c'_i2=c_i2+sigma_i eL,
    c'_ij=c_ij for j=3,...,41,
    c'_i42=0.

The new offset vector is

    [-3, v_1+7, v_2-4, v_3+1, v_4, ..., v_41].

This follows from adding 6*((X-1)^4+X^2) to X times the old unperturbed
encoding. The new rational digit is (c'_ij/L)*(z+1)+b_j. Consequently it
is integral at

    q=L*(t+T)-1, T=524783238475,

rather than only at multiples of L. Natural-number offsets, positivity,
and all coefficient budgets are checked exactly in Lean.

Dirichlet's theorem, Nat.forall_exists_prime_gt_and_modEq, supplies
arbitrarily large primes congruent to L-1 modulo L. This is a coprime
residue class. The proof explicitly converts each such prime to q(t)
with t>=0, rather than assuming that arbitrary progression entries are
prime. Since 4 divides L, every such denominator is 3 modulo 4.

Individual-value injectivity uses the existing rational-root-theorem
lemma RationalDigitInjection.eval_injective and the coefficient at degree
37 to distinguish the four polynomials. It is kept separate from the
(nonpreserved) Sidon property.

## Verification

The complete module builds without errors, warnings, or admissions. Its
10 printed axiom audits all list only propext, Classical.choice, Quot.sound.
It imports only the clean SmallRationalGaussianSpecialization chain, not
Spec.lean. No solver or native evaluation is trusted.

Log: /tmp/prime-rational-2.log
Olean: .lake/build/lib/lean/Submission/PrimeRationalSpecialization.olean

Research/PrimeRationalSpecializationData.py computes the new rational
certificate from the old JSON using exact integer arithmetic. It writes
Research/PrimeRationalSpecializationData.json and a temporary header at
/tmp/prime-rational-header.lean; it does not overwrite the Lean proof.
The Lean source contains all literal certificate data and has no runtime
dependency on either JSON file or on Python.

During development, finite Fin equality conditions needed Fin.ext_iff
for normalization, and vector projections needed ordinary simp rather
than an incomplete hand-written simp-only list. A kernel-depth issue was
avoided by proving the nontriviality inequalities at an abstract rational
z before specializing to the large natural denominator.

## Other review in this continuation

The old norm checksum for X^3-X-1 was tested exactly at irreducible prime
bases. It also fails at 29, which is 2 modulo 3:

    414721^2+585517^2 = 219581^2+683087^2 = 514823665130.

The four residue indices are 108,181,80,195 respectively. This is an
exploratory exact-integer check, not a newly formalized theorem. The
base-5 positive checksum was confirmed to be a separate lookup function,
not the same norm formula. No infinite checksum family was found.

Spec.lean SHA-256 remains
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.
