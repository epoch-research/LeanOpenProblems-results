# Shift checks — original conjecture remains unresolved

The new standalone development file `ShiftedPrimeParity.lean` imports only
FormalConjecturesUtil and compiles. Its namespace is
`Erdos972ShiftedPrimeParity`.

Verified results:

- `floor_slope_nat_shift`: for alpha >= 0,
  floor((alpha+k)*p) = floor(alpha*p) + k*p.
- `not_both_prime_odd_slope_shift`: for alpha >= 1, odd natural k, and
  prime p > 2, the output floors at alpha and alpha+k cannot both be prime.
- `odd_slope_shift_inter_subset`: the two prime-input sets consequently
  have intersection contained in {2}.
- `prime_and_succ_prime`: consecutive primes must be 2 and 3.
- `unit_intercept_inter_subset`: the prime-input sets with intercepts zero
  and one likewise have intersection contained in {2} when alpha >= 1.
- `floor_bounded_intercept`: an intercept in [0,1] changes the floor by
  either zero or one.
- `equal_outputs_of_both_prime`: above input two, if both the original and
  bounded-intercept outputs are prime, those two outputs are equal.

The four principal declarations were audited by `#print axioms`; all use
only propext, Classical.choice, and Quot.sound.

These facts prevent treating a shift as preservation of the prime pairs.
They do NOT disprove the conjecture: infinite sets of successful prime inputs
for two different slopes or intercepts may have finite intersection.
No theorem transferring almost-everywhere results to every irrational slope,
no sufficient prime-pair lower bound, and no irrational counterexample was
found. Spec.lean remains unchanged with its original sorry, and was not
resubmitted.
