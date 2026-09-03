# Rational initial states synchronize in the carry recurrence

This is verified auxiliary progress, NOT a proof or disproof of Erdos 68.
Spec.lean remains unchanged with its original sorry.

CarryOrbitSynchronization.lean compiles without warnings, has a built olean,
and contains no proof holes. Its four principal axiom audits use only
propext, Classical.choice, and Quot.sound.

## General recurrence

Let f_r be arbitrary rational forcing, and start at any x in Q. The index r
corresponds to original index r+3. At the next step put

    v=(r+4)*u_r+f_r.

If r+4 is prime, set u_(r+1)=v. Otherwise reduce v modulo r+3, using the
rational floor formula. This is precisely the existing actual carry orbit
when f_r=1/((r+4)!-1) and x=16/5.

For two rational initial values x,y, the difference at index r is

    4*5*...*(r+3)*(x-y) minus an integer.

Since r! divides the displayed product, this difference is integral when
r >= den(x-y). If p=r+4 is prime, the next difference is p times an integer.
The step at p+1 then reduces modulo p and removes that difference exactly.
Equal states remain equal thereafter.

## Verified conclusions

* synchronize_after_prime: if r+4 is prime and den(x-y)<=r, the two orbits
  agree at every index n>=r+2.
* eventually_equal: for arbitrary rational forcing, all rational initial
  states give the same eventual orbit.
* eventually_actual_orbit: for the actual factorial-minus-one forcing,
  any rational initial value eventually agrees with ExplicitCarryOrbit.orbit.
* irrational_of_frequent_small_fraction: the existing sufficient condition
  of arbitrarily late fractional parts <=1/2 can consequently be checked
  using ANY rational initial value.

## Remaining gap

No infinite occurrence of such small fractional parts has been proved.
Synchronization holds for arbitrary forcing and is not an equidistribution
or escape theorem. In particular it does not exclude the eventual prime-gap
pattern forced by a hypothetical rational value of the original sum.
Varying the rational initial state gives no different eventual trajectories
that could themselves contradict that pattern.

No complete informal proof or disproof of the original conjecture has been
obtained. No new numerical experiment or submission check was run. All
compilation and axiom checks have completed; nothing remains pending.
