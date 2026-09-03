import FormalConjecturesUtil

/-!
# DEVELOPMENT: elementary Erdős–Straus representations and reductions

These are partial results for strictly increasing positive natural denominators.
The reduction to primes congruent to `1 mod 24` is conditional: representations
for those primes are not proved here. This file does not import or alter `Spec`.
-/

namespace Erdos242.Development

/-- The original representation predicate, including strict ordering. -/
def ES (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
    (4 / n : ℚ) = 1 / x + 1 / y + 1 / z

/-- Scale all three denominators by a positive integer. -/
theorem ES.scale {n k : ℕ} (hn : ES n) (hk : 0 < k) : ES (k * n) := by
  obtain ⟨x, y, z, hx, hxy, hyz, h⟩ := hn
  refine ⟨k * x, k * y, k * z, Nat.mul_pos hk hx,
    Nat.mul_lt_mul_of_pos_left hxy hk, Nat.mul_lt_mul_of_pos_left hyz hk, ?_⟩
  simpa only [Nat.cast_mul, add_div, div_div, mul_comm] using
    congrArg (fun q : ℚ => q / (k : ℚ)) h

/-- A represented divisor represents every positive multiple. -/
theorem ES.of_dvd {d n : ℕ} (hd : ES d) (hdn : d ∣ n) (hn : 0 < n) : ES n := by
  obtain ⟨k, rfl⟩ := hdn
  simpa only [Nat.mul_comm] using hd.scale (Nat.pos_of_mul_pos_left hn)

/-- For `n = 2m`, use `(m, m + 1, m(m + 1))`. -/
theorem es_two_mul (m : ℕ) (hm : 2 ≤ m) : ES (2 * m) := by
  refine ⟨m, m + 1, m * (m + 1), by omega, by omega, ?_, ?_⟩
  · nlinarith
  · have hm0 : (m : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp [hm0]; ring

/-- For `n = 3m`, use `(m, 4m, 12m)`. -/
theorem es_three_mul (m : ℕ) (hm : 1 ≤ m) : ES (3 * m) := by
  refine ⟨m, 4 * m, 12 * m, hm, by omega, by omega, ?_⟩
  have hm0 : (m : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp [hm0]; ring

/-- For `n = 3m - 1`, use `(m, 3m - 1, m(3m - 1))`. -/
theorem es_three_mul_sub_one (m : ℕ) (hm : 2 ≤ m) : ES (3 * m - 1) := by
  refine ⟨m, 3 * m - 1, m * (3 * m - 1), by omega, by omega, ?_, ?_⟩
  · nlinarith [Nat.sub_add_cancel (show 1 ≤ 3 * m by omega)]
  · have hm0 : (m : ℚ) ≠ 0 := by positivity
    have hn0 : ((3 * m - 1 : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast (show 3 * m - 1 ≠ 0 by omega)
    push_cast [Nat.cast_sub (show 1 ≤ 3 * m by omega)] at *
    field_simp [hm0, hn0]; ring

/-- For `n = 4m - 1`, use `(m, 4m², 4m²(4m - 1))`. -/
theorem es_four_mul_sub_one (m : ℕ) (hm : 1 ≤ m) : ES (4 * m - 1) := by
  refine ⟨m, 4 * m ^ 2, 4 * m ^ 2 * (4 * m - 1), hm, ?_, ?_, ?_⟩
  · nlinarith [Nat.le_mul_self m]
  · have hn : 1 < 4 * m - 1 := by omega
    simpa only [mul_one] using
      Nat.mul_lt_mul_of_pos_left hn (show 0 < 4 * m ^ 2 by positivity)
  · have hm0 : (m : ℚ) ≠ 0 := by positivity
    have hn0 : ((4 * m - 1 : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast (show 4 * m - 1 ≠ 0 by omega)
    push_cast [Nat.cast_sub (show 1 ≤ 4 * m by omega)] at *
    field_simp [hm0, hn0]; ring

/-- For `n = 8m - 3`, use `(2m, m(8m - 3), 2m(8m - 3))`. -/
theorem es_eight_mul_sub_three (m : ℕ) (hm : 1 ≤ m) : ES (8 * m - 3) := by
  refine ⟨2 * m, m * (8 * m - 3), 2 * m * (8 * m - 3), by omega, ?_, ?_, ?_⟩
  · nlinarith [Nat.sub_add_cancel (show 3 ≤ 8 * m by omega)]
  · have hn : 0 < 8 * m - 3 := by omega
    exact Nat.mul_lt_mul_of_pos_right (by omega) hn
  · have hm0 : (m : ℚ) ≠ 0 := by positivity
    have hn0 : ((8 * m - 3 : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast (show 8 * m - 3 ≠ 0 by omega)
    push_cast [Nat.cast_sub (show 3 ≤ 8 * m by omega)] at *
    field_simp [hm0, hn0]; ring

/-- All even `n > 2`, including every power of two greater than two. -/
theorem es_even {n : ℕ} (hn : 2 < n) (heven : Even n) : ES n := by
  obtain ⟨m, rfl⟩ := even_iff_two_dvd.mp heven
  exact es_two_mul m (by omega)

/-- Every odd prime outside the residue class `1 mod 24` is represented. -/
theorem es_prime_not_one_mod24 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hmod : p % 24 ≠ 1) : ES p := by
  by_cases hp3 : p = 3
  · subst p
    exact es_three_mul 1 (by decide)
  have hp5 := hp.five_le_of_ne_two_of_ne_three hp2 hp3
  by_cases h3 : p % 3 = 2
  · convert es_three_mul_sub_one (p / 3 + 1) (by omega) using 1; omega
  by_cases h4 : p % 4 = 3
  · convert es_four_mul_sub_one (p / 4 + 1) (by omega) using 1; omega
  by_cases h8 : p % 8 = 5
  · convert es_eight_mul_sub_three (p / 8 + 1) (by omega) using 1; omega
  have hodd := hp.mod_two_eq_one_iff_ne_two.mpr hp2
  have hn3 : p % 3 ≠ 0 := by
    intro h0
    have := hp.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h0)
    omega
  omega

/-- CONDITIONAL reduction; the hypothesis for primes `1 mod 24` remains open. -/
theorem es_of_primes_mod24
    (h : ∀ p : ℕ, p.Prime → p % 24 = 1 → ES p)
    (n : ℕ) (hn : 2 < n) : ES n := by
  by_cases h2 : 2 ∣ n
  · exact es_even hn (even_iff_two_dvd.mpr h2)
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact h2 hpn
  have hES : ES p := by
    by_cases hmod : p % 24 = 1
    · exact h p hp hmod
    · exact es_prime_not_one_mod24 hp hp2 hmod
  exact hES.of_dvd hpn (by omega)

/-- An equivalence of the open statement with its remaining prime cases, not a proof of either. -/
theorem all_iff_primes_mod24 :
    (∀ n : ℕ, 2 < n → ES n) ↔ (∀ p : ℕ, p.Prime → p % 24 = 1 → ES p) := by
  refine ⟨?_, fun h n hn => es_of_primes_mod24 h n hn⟩
  intro h p hp hmod
  have := hp.two_le
  exact h p (by omega)

end Erdos242.Development
