import Submission.Reduction

/-!
# Necessary bounds for sorted Erdős–Straus solutions

These lemmas give necessary conditions on an existing positive, strictly sorted
solution.  In particular, for a prime `p ≡ 1 (mod 4)`, its first denominator lies
strictly between `p / 4` and `p / 2`, and at least one of its other denominators
is divisible by `p`.  No existence of a solution is assumed beyond the displayed
rational equation in each lemma.
-/

namespace Erdos242Aux

/-- Clearing the denominators of a positive sorted solution. -/
lemma solution_cross_mul {n x y z : ℕ} (hn : 0 < n)
    (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z)
    (heq : (4 / n : ℚ) = 1 / x + 1 / y + 1 / z) :
    4 * x * y * z = n * (x * y + x * z + y * z) := by
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hx0 : (x : ℚ) ≠ 0 := by exact_mod_cast (by omega : x ≠ 0)
  have hy0 : (y : ℚ) ≠ 0 := by exact_mod_cast (by omega : y ≠ 0)
  have hz0 : (z : ℚ) ≠ 0 := by exact_mod_cast (by omega : z ≠ 0)
  have hq := heq
  field_simp [hn0, hx0, hy0, hz0] at hq
  have hpoly : (4 : ℚ) * x * y * z = n *
      ((x : ℚ) * y + (x : ℚ) * z + (y : ℚ) * z) := by
    nlinarith [hq]
  exact_mod_cast hpoly

/-- Positivity of the two larger reciprocal terms gives the strict lower bound. -/
theorem lt_four_mul_first {n x y z : ℕ} (hn : 0 < n)
    (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z)
    (heq : (4 / n : ℚ) = 1 / x + 1 / y + 1 / z) : n < 4 * x := by
  have hnQ : (0 : ℚ) < n := by exact_mod_cast hn
  have hxQ : (0 : ℚ) < x := by exact_mod_cast (by omega : 0 < x)
  have hyQ : (0 : ℚ) < y := by exact_mod_cast (by omega : 0 < y)
  have hzQ : (0 : ℚ) < z := by exact_mod_cast (by omega : 0 < z)
  have hyrec : (0 : ℚ) < 1 / y := by positivity
  have hzrec : (0 : ℚ) < 1 / z := by positivity
  have hrec : (1 : ℚ) / x < 4 / n := by linarith [heq]
  have hmul := (div_lt_div_iff₀ hxQ hnQ).mp hrec
  simp only [one_mul] at hmul
  exact_mod_cast hmul

/-- Each reciprocal is at most the reciprocal of the first denominator. -/
theorem four_mul_first_le_three_mul {n x y z : ℕ} (hn : 0 < n)
    (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z)
    (heq : (4 / n : ℚ) = 1 / x + 1 / y + 1 / z) : 4 * x ≤ 3 * n := by
  have hnQ : (0 : ℚ) < n := by exact_mod_cast hn
  have hxQ : (0 : ℚ) < x := by exact_mod_cast (by omega : 0 < x)
  have hxyQ : (x : ℚ) ≤ y := by exact_mod_cast hxy.le
  have hxzQ : (x : ℚ) ≤ z := by exact_mod_cast (by omega : x ≤ z)
  have hyrec := one_div_le_one_div_of_le hxQ hxyQ
  have hzrec := one_div_le_one_div_of_le hxQ hxzQ
  have hrec : (4 : ℚ) / n ≤ 3 / x := by
    calc
      (4 : ℚ) / n = 1 / x + 1 / y + 1 / z := heq
      _ ≤ 1 / x + 1 / x + 1 / x := by linarith only [hyrec, hzrec]
      _ = 3 / x := by ring
  have hmul := (div_le_div_iff₀ hnQ hxQ).mp hrec
  exact_mod_cast hmul

/-- The preliminary upper bound already places the first denominator below `n`. -/
theorem first_lt {n x y z : ℕ} (hn : 0 < n)
    (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z)
    (heq : (4 / n : ℚ) = 1 / x + 1 / y + 1 / z) : x < n := by
  have hbound := four_mul_first_le_three_mul hn hx hxy hyz heq
  omega

lemma prime_one_mod_four_ge_five {p : ℕ} (hp : p.Prime) (hmod : p % 4 = 1) :
    5 ≤ p := by
  have := hp.two_le
  omega

/-- The first denominator of a sorted solution is not divisible by its prime numerator. -/
theorem prime_not_dvd_first {p x y z : ℕ} (hp : p.Prime)
    (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z)
    (heq : (4 / p : ℚ) = 1 / x + 1 / y + 1 / z) : ¬ p ∣ x := by
  exact Nat.not_dvd_of_pos_of_lt (by omega) (first_lt hp.pos hx hxy hyz heq)

/-- For primes congruent to one modulo four, the prime divides the product
of the two larger denominators. -/
theorem prime_dvd_last_product {p x y z : ℕ} (hp : p.Prime) (hmod : p % 4 = 1)
    (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z)
    (heq : (4 / p : ℚ) = 1 / x + 1 / y + 1 / z) : p ∣ y * z := by
  have hp5 := prime_one_mod_four_ge_five hp hmod
  have hp4 : ¬ p ∣ 4 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  have hpoly := solution_cross_mul hp.pos hx hxy hyz heq
  have hd : p ∣ 4 * (x * (y * z)) := by
    have hrew : 4 * (x * (y * z)) = p * (x * y + x * z + y * z) := by
      nlinarith only [hpoly]
    rw [hrew]
    exact dvd_mul_right p _
  have hdxyz : p ∣ x * (y * z) := (hp.dvd_mul.mp hd).resolve_left hp4
  exact (hp.dvd_mul.mp hdxyz).resolve_left (prime_not_dvd_first hp hx hxy hyz heq)

/-- At least one of the two larger denominators is divisible by the prime. -/
theorem prime_dvd_larger_denominator {p x y z : ℕ} (hp : p.Prime) (hmod : p % 4 = 1)
    (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z)
    (heq : (4 / p : ℚ) = 1 / x + 1 / y + 1 / z) : p ∣ y ∨ p ∣ z := by
  exact hp.dvd_mul.mp (prime_dvd_last_product hp hmod hx hxy hyz heq)

/-- If both larger denominators are multiples of the numerator, the easy
reciprocal estimate already gives the half-numerator upper bound. -/
private lemma two_mul_first_le_of_two_divisible {n x y z : ℕ} (hn : 0 < n)
    (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z) (hdy : n ∣ y) (hdz : n ∣ z)
    (heq : (4 / n : ℚ) = 1 / x + 1 / y + 1 / z) : 2 * x ≤ n := by
  have hnQ : (0 : ℚ) < n := by exact_mod_cast hn
  have hxQ : (0 : ℚ) < x := by exact_mod_cast (by omega : 0 < x)
  have hny : n ≤ y := Nat.le_of_dvd (by omega) hdy
  have hnz : n ≤ z := Nat.le_of_dvd (by omega) hdz
  have hnyQ : (n : ℚ) ≤ y := by exact_mod_cast hny
  have hnzQ : (n : ℚ) ≤ z := by exact_mod_cast hnz
  have hyrec := one_div_le_one_div_of_le hnQ hnyQ
  have hzrec := one_div_le_one_div_of_le hnQ hnzQ
  have hrec : (2 : ℚ) / n ≤ 1 / x := by
    calc
      (2 : ℚ) / n = 4 / n - (1 / n + 1 / n) := by ring
      _ = 1 / x + 1 / y + 1 / z - (1 / n + 1 / n) := by rw [heq]
      _ ≤ 1 / x := by linarith only [hyrec, hzrec]
  have hmul := (div_le_div_iff₀ hnQ hxQ).mp hrec
  simp only [one_mul] at hmul
  exact_mod_cast hmul

/-- The one-divisible-denominator case.  Clearing the equation forces
`4*w - 1 = p*s`, with `s ≡ 3 (mod 4)`.  The inequality `x ≤ v` then rules out
`2*x ≥ p + 1`. -/
private lemma two_mul_first_lt_of_one_divisible {p x v w : ℕ}
    (hp : p.Prime) (hmod : p % 4 = 1) (hx : 1 ≤ x) (hxv : x ≤ v) (hw : 1 ≤ w)
    (hpx : ¬ p ∣ x) (hpv : ¬ p ∣ v)
    (heq : (4 / p : ℚ) = 1 / x + 1 / v + 1 / (p * w : ℕ)) : 2 * x < p := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hx0 : (x : ℚ) ≠ 0 := by exact_mod_cast (by omega : x ≠ 0)
  have hv0 : (v : ℚ) ≠ 0 := by exact_mod_cast (by omega : v ≠ 0)
  have hw0 : (w : ℚ) ≠ 0 := by exact_mod_cast (by omega : w ≠ 0)
  have hq := heq
  push_cast at hq
  field_simp [hp0, hx0, hv0, hw0] at hq
  have hpolyQ : (4 : ℚ) * w * x * v =
      (p : ℚ) * w * ((x : ℚ) + v) + (x : ℚ) * v := by
    nlinarith only [hq]
  have hpoly : 4 * w * x * v = p * w * (x + v) + x * v := by
    exact_mod_cast hpolyQ
  have hwsub : (4 * w - 1) + 1 = 4 * w := by omega
  have hpolySub : (4 * w - 1) * x * v = p * w * (x + v) := by
    rw [← hwsub] at hpoly
    nlinarith only [hpoly]
  have hpc : p ∣ 4 * w - 1 := by
    have hd : p ∣ (4 * w - 1) * x * v := by
      rw [hpolySub]
      refine ⟨w * (x + v), ?_⟩
      ring
    have hdcx : p ∣ (4 * w - 1) * x := (hp.dvd_mul.mp hd).resolve_right hpv
    exact (hp.dvd_mul.mp hdcx).resolve_right hpx
  obtain ⟨s, hs⟩ := hpc
  have hws : 4 * w = p * s + 1 := by omega
  have hsmod : (s % 4 + 1) % 4 = 0 := by
    have hm := congrArg (fun a : ℕ => a % 4) hws
    simpa [Nat.add_mod, Nat.mul_mod, hmod] using hm.symm
  have hs3 : 3 ≤ s := by omega
  rw [hs] at hpolySub
  have hpolyS : s * x * v = w * (x + v) := by
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    nlinarith only [hpolySub]
  have hboundMul : (s * x) * v ≤ (2 * w) * v := by
    calc
      (s * x) * v = w * (x + v) := hpolyS
      _ ≤ w * (2 * v) := Nat.mul_le_mul_left w (by omega)
      _ = (2 * w) * v := by ring
  have hbound : s * x ≤ 2 * w := Nat.le_of_mul_le_mul_right hboundMul (by omega)
  by_contra hbad
  have hbadN : p + 1 ≤ 2 * x := by omega
  have hbadMul := Nat.mul_le_mul_right s hbadN
  nlinarith only [hbound, hws, hbadMul, hs3]

/-- The sharp upper bound for the smallest denominator when `p ≡ 1 (mod 4)`. -/
theorem two_mul_first_lt_prime {p x y z : ℕ} (hp : p.Prime) (hmod : p % 4 = 1)
    (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z)
    (heq : (4 / p : ℚ) = 1 / x + 1 / y + 1 / z) : 2 * x < p := by
  have hpx := prime_not_dvd_first hp hx hxy hyz heq
  have hd := prime_dvd_larger_denominator hp hmod hx hxy hyz heq
  by_cases hpy : p ∣ y
  · by_cases hpz : p ∣ z
    · have hle := two_mul_first_le_of_two_divisible hp.pos hx hxy hyz hpy hpz heq
      omega
    · obtain ⟨w, hyw⟩ := hpy
      have hw : 1 ≤ w := by
        by_contra h
        have hwzero : w = 0 := by omega
        simp [hwzero] at hyw
        omega
      apply two_mul_first_lt_of_one_divisible hp hmod hx (by omega : x ≤ z) hw hpx hpz
      simpa [hyw, add_comm, add_left_comm, add_assoc] using heq
  · have hpz : p ∣ z := hd.resolve_left hpy
    obtain ⟨w, hzw⟩ := hpz
    have hw : 1 ≤ w := by
      by_contra h
      have hwzero : w = 0 := by omega
      simp [hwzero] at hzw
      omega
    apply two_mul_first_lt_of_one_divisible hp hmod hx hxy.le hw hpx hpy
    simpa [hzw] using heq

/-- The requested strict interval for the first denominator, including its
immediate consequence `x < p`. -/
theorem prime_solution_bounds {p x y z : ℕ} (hp : p.Prime) (hmod : p % 4 = 1)
    (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z)
    (heq : (4 / p : ℚ) = 1 / x + 1 / y + 1 / z) :
    p < 4 * x ∧ 2 * x < p ∧ x < p := by
  have hhalf := two_mul_first_lt_prime hp hmod hx hxy hyz heq
  exact ⟨lt_four_mul_first hp.pos hx hxy hyz heq, hhalf, by omega⟩

/-- The divisibility pattern: the first denominator is not divisible by `p`,
whereas one or both of the larger denominators are. -/
theorem prime_solution_divisibility {p x y z : ℕ} (hp : p.Prime) (hmod : p % 4 = 1)
    (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z)
    (heq : (4 / p : ℚ) = 1 / x + 1 / y + 1 / z) :
    ¬ p ∣ x ∧ p ∣ y * z ∧ (p ∣ y ∨ p ∣ z) := by
  have hd := prime_dvd_last_product hp hmod hx hxy hyz heq
  exact ⟨prime_not_dvd_first hp hx hxy hyz heq, hd, hp.dvd_mul.mp hd⟩

/-- An integer interval for enumerating the possible first denominators. -/
theorem prime_first_search_interval {p x y z : ℕ} (hp : p.Prime) (hmod : p % 4 = 1)
    (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z)
    (heq : (4 / p : ℚ) = 1 / x + 1 / y + 1 / z) :
    p / 4 + 1 ≤ x ∧ x ≤ (p - 1) / 2 := by
  have hb := prime_solution_bounds hp hmod hx hxy hyz heq
  omega

/-- The second denominator also has a finite upper bound once the first is fixed.
The strict inequality uses `y < z`, rather than just positivity. -/
theorem second_mul_gap_lt {n x y z : ℕ} (hn : 0 < n)
    (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z)
    (heq : (4 / n : ℚ) = 1 / x + 1 / y + 1 / z) :
    (4 * x - n) * y < 2 * n * x := by
  have hlower := lt_four_mul_first hn hx hxy hyz heq
  have hsub : (4 * x - n) + n = 4 * x := by omega
  have hpoly := solution_cross_mul hn hx hxy hyz heq
  have hpolyGap : (4 * x - n) * y * z = n * x * (y + z) := by
    rw [← hsub] at hpoly
    nlinarith only [hpoly]
  have hnxpos : 0 < n * x := Nat.mul_pos hn (by omega)
  have hboundMul : ((4 * x - n) * y) * z < (2 * n * x) * z := by
    calc
      ((4 * x - n) * y) * z = n * x * (y + z) := hpolyGap
      _ < (n * x) * (2 * z) := Nat.mul_lt_mul_of_pos_left (by omega) hnxpos
      _ = (2 * n * x) * z := by ring
  exact Nat.lt_of_mul_lt_mul_right hboundMul

/-- The integer form of the finite upper bound for the second denominator.
Together with `x < y` this gives a finite search interval. -/
theorem second_le_search_bound {n x y z : ℕ} (hn : 0 < n)
    (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z)
    (heq : (4 / n : ℚ) = 1 / x + 1 / y + 1 / z) :
    y ≤ (2 * n * x - 1) / (4 * x - n) := by
  have hlower := lt_four_mul_first hn hx hxy hyz heq
  have hgap : 0 < 4 * x - n := by omega
  have hprod := second_mul_gap_lt hn hx hxy hyz heq
  have hprod' : y * (4 * x - n) < 2 * n * x := by
    simpa only [Nat.mul_comm] using hprod
  apply (Nat.le_div_iff_mul_le hgap).mpr
  omega

end Erdos242Aux
