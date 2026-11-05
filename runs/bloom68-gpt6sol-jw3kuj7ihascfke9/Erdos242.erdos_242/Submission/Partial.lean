import Submission.Reduction

/-!
# Further conditional Erdős–Straus constructions

These results strengthen the elementary reduction in `Submission.Reduction`.
No universal Erdős–Straus assertion is made here.
-/

namespace Erdos242

/-- A single divisor `4*m-1` of `n+4` produces three *distinct* denominators.
This is the `d=1` case of `good_of_modular_witness`; the quotient condition
follows automatically from `n ≥ 4` and the divisibility. -/
theorem good_of_shifted_divisor (n m : ℕ) (hn : 4 ≤ n) (hm : 0 < m)
    (hdiv : 4 * m - 1 ∣ n + 4) : Good n := by
  have hh : 0 < 4 * m - 1 := by omega
  have hsum : n * m + 1 + (4 * m - 1) = (n + 4) * m := by
    calc
      n * m + 1 + (4 * m - 1) = n * m + 4 * m := by omega
      _ = (n + 4) * m := by ring
  have hnum : 4 * m - 1 ∣ n * m + 1 := by
    have hadd : 4 * m - 1 ∣ n * m + 1 + (4 * m - 1) := by
      rw [hsum]
      exact dvd_mul_of_dvd_left hdiv m
    exact (Nat.dvd_add_iff_left (dvd_refl (4 * m - 1))).mpr hadd
  have hx : (4 * m - 1) * ((n * m + 1) / (4 * m - 1)) = n * m + 1 :=
    Nat.mul_div_cancel' hnum
  have hbound : 4 * m - 1 < n * m + 1 := by
    have : 4 * m ≤ n * m := Nat.mul_le_mul_right m hn
    omega
  have hxd : 1 < (n * m + 1) / (4 * m - 1) := by
    by_contra hc
    have hle : (n * m + 1) / (4 * m - 1) ≤ 1 := by omega
    have hprod := Nat.mul_le_mul_left (4 * m - 1) hle
    have : n * m + 1 ≤ 4 * m - 1 := by simpa only [hx, mul_one] using hprod
    omega
  exact good_of_modular_witness n m 1 (by omega) hm (by decide)
    (by simp) hh (by simpa using hdiv) hxd

/-- In particular any divisor `q ≡ 3 (mod 4)` of `n+4` gives a solution.
Primality of `q` is not required. -/
theorem good_of_three_mod_four_divisor (n q : ℕ) (hn : 4 ≤ n)
    (hq : q % 4 = 3) (hdiv : q ∣ n + 4) : Good n := by
  have hm : 0 < (q + 1) / 4 := by omega
  have hqeq : 4 * ((q + 1) / 4) - 1 = q := by omega
  exact good_of_shifted_divisor n ((q + 1) / 4) hn hm (by simpa [hqeq] using hdiv)

/-- An elementary obstruction: no choice `d ∣ m²` can satisfy
`4*m-1 ∣ 1+4*d`. In particular, imposing `p ≡ 1 (mod 4*m-1)` rules
out this particular type-II modular witness at that value of `m`. -/
theorem not_one_modular_divisor (m d : ℕ) (hm : 0 < m) (hd : 0 < d)
    (hdsq : d ∣ m ^ 2) : ¬ (4 * m - 1 ∣ 1 + 4 * d) := by
  intro hdiv
  let h := 4 * m - 1
  let a := m ^ 2 / d
  have hfour : h + 1 = 4 * m := by dsimp [h]; omega
  have hda : d * a = m ^ 2 := Nat.mul_div_cancel' hdsq
  have hfirst : h ≤ 1 + 4 * d := Nat.le_of_dvd (by omega) hdiv
  have hdge : m ≤ d := by dsimp [h] at hfirst; omega
  have hprod : (h + 1) * (4 * m + 1) = (4 * m) * (4 * m + 1) :=
    congrArg (fun t : ℕ => t * (4 * m + 1)) hfour
  have hsq : 16 * m ^ 2 = h * (4 * m + 1) + 1 := by nlinarith [hprod]
  have hmul : h ∣ (1 + 4 * d) * (4 * a) := dvd_mul_of_dvd_left hdiv (4 * a)
  have hmul_eq : (1 + 4 * d) * (4 * a) = (4 * a + 1) + h * (4 * m + 1) := by
    calc
      (1 + 4 * d) * (4 * a) = 4 * a + 16 * (d * a) := by ring
      _ = 4 * a + 16 * m ^ 2 := by rw [hda]
      _ = (4 * a + 1) + h * (4 * m + 1) := by omega
  rw [hmul_eq] at hmul
  have hadiv : h ∣ 4 * a + 1 :=
    (Nat.dvd_add_iff_left (dvd_mul_right h (4 * m + 1))).mpr hmul
  have ha_ge : h ≤ 4 * a + 1 := Nat.le_of_dvd (by omega) hadiv
  have hage : m ≤ a := by dsimp [h] at ha_ge; omega
  have hdle : d ≤ m := by
    by_contra hc
    have hm1 : m + 1 ≤ d := by omega
    have hlarge : (m + 1) * m ≤ d * a := by
      calc
        (m + 1) * m ≤ d * m := Nat.mul_le_mul_right m hm1
        _ ≤ d * a := Nat.mul_le_mul_left d hage
    nlinarith [hda, hlarge]
  have hd_eq : d = m := by omega
  have htwo : h ∣ 2 := by
    have heq : 1 + 4 * d = h + 2 := by dsimp [h]; omega
    rw [heq] at hdiv
    exact (Nat.dvd_add_iff_right (dvd_refl h)).mpr hdiv
  have : h ≤ 2 := Nat.le_of_dvd (by decide) htwo
  dsimp [h] at this
  omega

/-- For each fixed `m`, primes `p ≡ 1 (mod 4*m-1)` cannot be handled
by the `d ∣ m²` modular construction with that particular `m`. -/
theorem no_modular_divisor_if_one_remainder (p m d : ℕ)
    (hm : 0 < m) (hd : 0 < d) (hdsq : d ∣ m ^ 2)
    (hrem : p % (4 * m - 1) = 1) : ¬ (4 * m - 1 ∣ p + 4 * d) := by
  intro hdiv
  have hh : 1 < 4 * m - 1 := by omega
  have hmod : (p + 4 * d) % (4 * m - 1) = 0 := Nat.mod_eq_zero_of_dvd hdiv
  have hmod1 : (1 + 4 * d) % (4 * m - 1) = 0 := by
    rw [Nat.add_mod, hrem] at hmod
    rw [Nat.add_mod, Nat.mod_eq_of_lt hh]
    exact hmod
  exact not_one_modular_divisor m d hm hd hdsq (Nat.dvd_of_mod_eq_zero hmod1)

/-- The specific modular-witness criterion `d ∣ m²` cannot be made universal
by putting an upper bound on `m`: for every bound there are arbitrarily large
hard primes for which *all* parameters below that bound fail. This uses
Dirichlet's theorem (in Mathlib) and does **not** assert a counterexample to
Erdős–Straus. -/
theorem hard_primes_escape_bounded_modular_parameters (B N : ℕ) :
    ∃ p : ℕ, N < p ∧ p.Prime ∧ p % 840 = 1 ∧
      ∀ m d : ℕ, 0 < m → m ≤ B → 0 < d → d ∣ m ^ 2 →
        ¬ (4 * m - 1 ∣ p + 4 * d) := by
  let L := 840 * (4 * B).factorial
  have hL : L ≠ 0 := by dsimp [L]; positivity
  obtain ⟨p, hpgt, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq N
    (q := L) (a := 1) hL (by simp)
  have h840 : 840 ∣ L := by dsimp [L]; exact dvd_mul_right 840 _
  have h840rem : p % 840 = 1 := by
    have hc := Nat.ModEq.of_dvd h840 hmod
    simpa [Nat.ModEq] using hc
  refine ⟨p, hpgt, hp, h840rem, ?_⟩
  intro m d hm hmB hd hdsq
  have hfact : 4 * m - 1 ∣ (4 * B).factorial :=
    Nat.dvd_factorial (by omega) (by omega)
  have hdivL : 4 * m - 1 ∣ L := by
    dsimp [L]
    exact dvd_mul_of_dvd_right hfact 840
  have hrem : p % (4 * m - 1) = 1 := by
    have hc := Nat.ModEq.of_dvd hdivL hmod
    change p % (4 * m - 1) = 1 % (4 * m - 1) at hc
    simpa only [Nat.mod_eq_of_lt (by omega : 1 < 4 * m - 1)] using hc
  exact no_modular_divisor_if_one_remainder p m d hm hd hdsq hrem

/-- The `m=2` type-II parameter covers the three nonsquares modulo 7. -/
theorem good_of_mod7 (n : ℕ) (hn : 31 ≤ n)
    (hr : n % 7 = 3 ∨ n % 7 = 5 ∨ n % 7 = 6) : Good n := by
  rcases hr with h | h | h
  · refine good_of_modular_witness n 2 1 (by omega) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ?_ ?_
    · change 7 ∣ n + 4
      exact Nat.dvd_iff_mod_eq_zero.mpr (by omega)
    · change 1 < (n * 2 + 1) / 7
      omega
  · refine good_of_modular_witness n 2 4 (by omega) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ?_ ?_
    · change 7 ∣ n + 16
      exact Nat.dvd_iff_mod_eq_zero.mpr (by omega)
    · change 4 < (n * 2 + 4) / 7
      omega
  · refine good_of_modular_witness n 2 2 (by omega) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ?_ ?_
    · change 7 ∣ n + 8
      exact Nat.dvd_iff_mod_eq_zero.mpr (by omega)
    · change 2 < (n * 2 + 2) / 7
      omega

/-- The `m=3` parameter also covers three nonsquares modulo 11,
including hard primes beyond the six exceptional classes modulo 840. -/
theorem good_of_mod11 (n : ℕ) (hn : 31 ≤ n)
    (hr : n % 11 = 7 ∨ n % 11 = 8 ∨ n % 11 = 10) : Good n := by
  rcases hr with h | h | h
  · refine good_of_modular_witness n 3 1 (by omega) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ?_ ?_
    · change 11 ∣ n + 4
      exact Nat.dvd_iff_mod_eq_zero.mpr (by omega)
    · change 1 < (n * 3 + 1) / 11
      omega
  · refine good_of_modular_witness n 3 9 (by omega) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ?_ ?_
    · change 11 ∣ n + 36
      exact Nat.dvd_iff_mod_eq_zero.mpr (by omega)
    · change 9 < (n * 3 + 9) / 11
      omega
  · refine good_of_modular_witness n 3 3 (by omega) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ?_ ?_
    · change 11 ∣ n + 12
      exact Nat.dvd_iff_mod_eq_zero.mpr (by omega)
    · change 3 < (n * 3 + 3) / 11
      omega

/-- For `n ≡ 1 (mod 3)`, the `m=4` type-II parameter covers both
nonsquares modulo 5. -/
theorem good_of_mod5 (n : ℕ) (hn : 31 ≤ n) (hthree : n % 3 = 1)
    (hr : n % 5 = 2 ∨ n % 5 = 3) : Good n := by
  rcases hr with h | h
  · refine good_of_modular_witness n 4 2 (by omega) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ?_ ?_
    · change 15 ∣ n + 8
      exact Nat.dvd_iff_mod_eq_zero.mpr (by omega)
    · change 2 < (n * 4 + 2) / 15
      omega
  · refine good_of_modular_witness n 4 8 (by omega) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ?_ ?_
    · change 15 ∣ n + 32
      exact Nat.dvd_iff_mod_eq_zero.mpr (by omega)
    · change 8 < (n * 4 + 8) / 15
      omega

private theorem six_square_remainders_840 (r : ℕ) (hr : r < 840)
    (h24 : r % 24 = 1) (h5 : r % 5 = 1 ∨ r % 5 = 4)
    (h7 : r % 7 = 1 ∨ r % 7 = 2 ∨ r % 7 = 4) :
    r = 1 ∨ r = 121 ∨ r = 169 ∨ r = 289 ∨ r = 361 ∨ r = 529 := by
  rcases h5 with h5 | h5 <;> rcases h7 with h7 | h7 | h7 <;> omega

/-- The `m=2,4` constructions solve every prime outside the six square
classes modulo 840. The `m=3` theorem also handles some of these six classes. -/
theorem good_prime_outside_six_840 (p : ℕ) (hp : p.Prime) (hpgt : 2 < p)
    (hnot : p % 840 ≠ 1 ∧ p % 840 ≠ 121 ∧ p % 840 ≠ 169 ∧
      p % 840 ≠ 289 ∧ p % 840 ≠ 361 ∧ p % 840 ≠ 529) : Good p := by
  by_cases h24 : p % 24 = 1
  · have hge : 31 ≤ p := by
      have hp2 := hp.two_le
      by_contra h
      have hp25 : p = 25 := by omega
      subst p
      norm_num at hp
    have h5nz : p % 5 ≠ 0 := by
      intro hz
      have h5dvd : 5 ∣ p := Nat.dvd_of_mod_eq_zero hz
      have heq : 5 = p := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h5dvd
      omega
    have h7nz : p % 7 ≠ 0 := by
      intro hz
      have h7dvd : 7 ∣ p := Nat.dvd_of_mod_eq_zero hz
      have heq : 7 = p := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h7dvd
      omega
    have hcases : p % 5 = 2 ∨ p % 5 = 3 ∨ p % 7 = 3 ∨
        p % 7 = 5 ∨ p % 7 = 6 := by
      by_contra hbad
      push_neg at hbad
      have h5 : p % 5 = 1 ∨ p % 5 = 4 := by omega
      have h7 : p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4 := by omega
      have hr24 : p % 840 % 24 = 1 := by
        rwa [Nat.mod_mod_of_dvd p (by decide : 24 ∣ 840)]
      have hr5 : p % 840 % 5 = 1 ∨ p % 840 % 5 = 4 := by
        rw [Nat.mod_mod_of_dvd p (by decide : 5 ∣ 840)]
        exact h5
      have hr7 : p % 840 % 7 = 1 ∨ p % 840 % 7 = 2 ∨
          p % 840 % 7 = 4 := by
        rw [Nat.mod_mod_of_dvd p (by decide : 7 ∣ 840)]
        exact h7
      have hclass := six_square_remainders_840 (p % 840)
        (Nat.mod_lt _ (by decide)) hr24 hr5 hr7
      rcases hclass with h | h | h | h | h | h <;> omega
    rcases hcases with h | h | h | h | h
    · exact good_of_mod5 p hge (by omega) (Or.inl h)
    · exact good_of_mod5 p hge (by omega) (Or.inr h)
    · exact good_of_mod7 p hge (Or.inl h)
    · exact good_of_mod7 p hge (Or.inr (Or.inl h))
    · exact good_of_mod7 p hge (Or.inr (Or.inr h))
  · exact good_outside_24 p hpgt h24

/-- Consequently, proving just the six specified prime residue classes
suffices to prove the ordered-distinct-denominator conjecture for all `n>2`. -/
theorem good_of_six_prime_classes
    (hard : ∀ p : ℕ, p.Prime →
      (p % 840 = 1 ∨ p % 840 = 121 ∨ p % 840 = 169 ∨
        p % 840 = 289 ∨ p % 840 = 361 ∨ p % 840 = 529) → Good p) :
    ∀ n : ℕ, 2 < n → Good n := by
  apply good_of_hard_primes
  intro p hp h24
  by_cases h : p % 840 = 1 ∨ p % 840 = 121 ∨ p % 840 = 169 ∨
      p % 840 = 289 ∨ p % 840 = 361 ∨ p % 840 = 529
  · exact hard p hp h
  · have hpgt : 2 < p := by
      have hp2 := hp.two_le
      omega
    exact good_prime_outside_six_840 p hp hpgt (by omega)

/-- An exact reduction to primes not covered by the three constructions
above. This is conditional; in particular it does not assert that there
are any insoluble primes. -/
theorem good_of_residual_prime_cases
    (hard : ∀ p : ℕ, p.Prime →
      (p % 840 = 1 ∨ p % 840 = 121 ∨ p % 840 = 169 ∨
        p % 840 = 289 ∨ p % 840 = 361 ∨ p % 840 = 529) →
      ¬ (p % 11 = 7 ∨ p % 11 = 8 ∨ p % 11 = 10) →
      (¬ ∃ q : ℕ, q % 4 = 3 ∧ q ∣ p + 4) → Good p) :
    ∀ n : ℕ, 2 < n → Good n := by
  apply good_of_six_prime_classes
  intro p hp h840
  have hge : 31 ≤ p := by
    have hp2 := hp.two_le
    rcases h840 with h | h | h | h | h | h <;> omega
  by_cases h11 : p % 11 = 7 ∨ p % 11 = 8 ∨ p % 11 = 10
  · exact good_of_mod11 p hge h11
  · by_cases hq : ∃ q : ℕ, q % 4 = 3 ∧ q ∣ p + 4
    · obtain ⟨q, hq4, hqdiv⟩ := hq
      exact good_of_three_mod_four_divisor p q (by omega) hq4 hqdiv
    · exact hard p hp h840 h11 hq

end Erdos242
