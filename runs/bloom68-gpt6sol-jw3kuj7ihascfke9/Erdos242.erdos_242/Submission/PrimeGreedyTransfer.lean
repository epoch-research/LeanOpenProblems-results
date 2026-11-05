import Submission.CoveringGap
import Submission.NormShiftDescent

/-!
# Greedy-denominator prime induction is equivalent to the whole conjecture

For `p=24k+1`, the smaller integer `(p+3)/4=6k+1` is always good
*under the least-counterexample hypothesis*. Therefore a proposed universal
transfer from its `Good` witness to `Good p` is precisely the remaining
unproved input, not a separate consequence of the Euclidean algorithm.
The theorem here proves this equivalence; it does not prove either side.
`Submission.Spec` is not imported or changed.
-/

namespace Erdos242

/-- An all-hard-prime implication `Good ((p+3)/4) → Good p` is equivalent to
ordered Erdős–Straus itself. The reverse direction uses strong induction,
the known easy residue classes, and scaling from a prime divisor. -/
theorem all_good_iff_prime_greedy_transfer :
    (∀ n : ℕ, 2 < n → Good n) ↔
      ∀ k : ℕ, (24 * k + 1).Prime → Good (6 * k + 1) → Good (24 * k + 1) := by
  constructor
  · intro all k hp _
    exact all _ (by have := hp.two_le; omega)
  · intro transfer n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hmod : n % 24 = 1
      · obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
        have hpgt : 2 < p := by
          have hpge := hp.two_le
          by_contra h
          have hp2 : p = 2 := by omega
          rw [hp2] at hpn
          have hn2 : n % 2 = 0 := Nat.mod_eq_zero_of_dvd hpn
          omega
        have hple : p ≤ n := Nat.le_of_dvd (by omega : 0 < n) hpn
        have hgoodp : Good p := by
          by_cases hplt : p < n
          · exact ih p hplt hpgt
          · have heq : p = n := by omega
            have hpmod : p % 24 = 1 := by omega
            have hk : p = 24 * (p / 24) + 1 := by omega
            have hp' : (24 * (p / 24) + 1).Prime := by rwa [← hk]
            have hq_gt : 2 < 6 * (p / 24) + 1 := by omega
            have hq_lt : 6 * (p / 24) + 1 < n := by omega
            have hgoodq : Good (6 * (p / 24) + 1) := ih _ hq_lt hq_gt
            have hgoodp' := transfer (p / 24) hp' hgoodq
            rwa [← hk] at hgoodp'
        rcases hpn with ⟨t, rfl⟩
        have ht : 0 < t := by
          by_contra ht0
          have ht0' : t = 0 := by omega
          subst t
          simp at hn
        exact good_mul hgoodp ht
      · exact good_outside_24 n hn hmod

/-- Every divisor of the square of a power of a prime `1 (mod 3)` is
itself `1 (mod 3)`. This is the precise integrality obstruction at the
greedy first denominator, not a failure of `Good` for the numerator. -/
private theorem prime_power_square_divisors_one_mod_three
    (r t e : ℕ) (hr : r.Prime) (hrmod : r % 3 = 1)
    (he : e ∣ (r ^ t) ^ 2) : e % 3 = 1 := by
  have hd : e ∣ r ^ (t * 2) := by simpa only [pow_mul] using he
  obtain ⟨j, _, rfl⟩ := (Nat.dvd_prime_pow hr).mp hd
  simp [Nat.pow_mod, hrmod]

/-- A power of a prime `1 (mod 3)` cannot support either full Type-I or
Type-II certificate at the first possible denominator `q=(p+3)/4` when
`p=4q-3`. Later first denominators are not excluded. -/
theorem no_greedy_fiber_of_prime_power (r t : ℕ)
    (hr : r.Prime) (hrmod : r % 3 = 1) :
    ¬TypeI (4 * r ^ t - 3) (r ^ t) ∧
    ¬TypeII (4 * r ^ t - 3) (r ^ t) := by
  apply no_types_if_divisors_one_mod_three
  · omega
  · simp [Nat.pow_mod, hrmod]
  · intro e _ hdiv
    exact prime_power_square_divisors_one_mod_three r t e hr hrmod hdiv

/-- All three source numbers `q` are prime powers of split primes, so the
greedy first denominator fails both *full* types, even though both `Good q`
and `Good p` have explicit positive ordered witnesses. -/
theorem greedy_fiber_193_fails : ¬TypeI 193 49 ∧ ¬TypeII 193 49 := by
  simpa using no_greedy_fiber_of_prime_power 7 2 (by norm_num) (by norm_num)

theorem greedy_fiber_2521_fails : ¬TypeI 2521 631 ∧ ¬TypeII 2521 631 := by
  simpa using no_greedy_fiber_of_prime_power 631 1 (by norm_num) (by norm_num)

theorem greedy_fiber_66529_fails : ¬TypeI 66529 16633 ∧ ¬TypeII 66529 16633 := by
  simpa using no_greedy_fiber_of_prime_power 16633 1 (by norm_num) (by norm_num)


/-- `Good ((193+3)/4)` is genuinely true, even though no solution for
`193` starts at that first denominator `49`. -/
theorem greedy_source_193 : Good 49 := by
  refine ⟨14, 147, 294, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num

/-- The same phenomenon applies when the smaller number is itself prime. -/
theorem greedy_source_2521 : Good 631 := by
  refine ⟨158, 124662, 497859, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num

/-- Here even the smaller `16633` is in the hard residue class `1 (mod 24)`;
its explicit witness still does not by itself give a certificate for `66529`. -/
theorem greedy_source_66529 : Good 16633 := by
  refine ⟨4160, 10379200, 207496675,
    by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num

end Erdos242
