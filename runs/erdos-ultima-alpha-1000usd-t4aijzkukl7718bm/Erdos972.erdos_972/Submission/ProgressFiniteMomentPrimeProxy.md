# Smaller weighted moment target — original conjecture still unresolved

Spec.lean is unchanged and retains its original sorry. No pointwise
prime-pair lower bound or irrational counterexample was obtained.

## New verified file

Submission/FiniteMomentPrimeProxy.lean
Namespace: Erdos972FiniteMomentPrimeProxy.

It compiles without errors or warnings. Its four principal printed axiom
audits use only propext, Classical.choice, and Quot.sound.

Define, for n>1,

    T_J(n) = sum_{j<J} exp(-2 log n) E_2(n)^j,

and define it to be zero at n=0,1.

The verified bounds are:

* 0 <= T_J(n) <= P_2(n), for all J,n.
* At a prime q,

      T_J(q) = 1-(1-1/q^2)^J,
      J/(q^2+J) <= T_J(q) <= J/q^2.

* If J<=q^2, then

      J/(2q^2) <= T_J(q) <= J/q^2.

* For logarithmicBudget(q)=q*Nat.log(2,q), the budget is <=q^2 and

      Nat.log(2,q)/(2q) <= T_logarithmicBudget(q)(q)
                         <= Nat.log(2,q)/q

  at every prime q.

* For ANY output-dependent budget J : Nat -> Nat and alpha>=1, the
  prime-input truncated contribution restricted to nonprime outputs is
  summable. It is bounded by the same complete composite proxy as before.

Principal declarations:

    truncatedProxy_prime_lower
    truncatedProxy_prime_comparison
    logarithmicBudget_prime_bounds
    summable_truncatedCompositeError

## Important clarification

The earlier q^2 moment scale is necessary to recover a fixed positive
fraction of the full detector value 1 at a prime q. It is NOT a proved
necessary moment scale for every infinitude argument. A smaller moment
budget may suffice if its accumulated prime-input contribution diverges.
The new logarithmic budget gives one concrete weighted target of that kind.

No divergence of this weighted detector for a prescribed irrational slope
has been proved. The available fixed-parameter/fixed-moment means have not
been extended uniformly to J=q*Nat.log(2,q). Moreover, infinitude alone does
not imply divergence of an arbitrary weighted prime-pair series, so this
weighted target is sufficient, not an established equivalence to finiteness.

This new finite calculation and the earlier uniform composite-error
regularity do not supply the missing arithmetic lower bound. No incomplete
proof was submitted as a settlement.

Compilation:

    lake env lean -o .lake/build/lib/lean/Submission/FiniteMomentPrimeProxy.olean \
      Submission/FiniteMomentPrimeProxy.lean
