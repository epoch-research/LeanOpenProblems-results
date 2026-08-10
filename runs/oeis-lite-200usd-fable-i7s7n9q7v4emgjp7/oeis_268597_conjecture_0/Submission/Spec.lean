import FormalConjectures.Util.ProblemImports
open Nat Set

noncomputable def A268597 (n : ℕ) : ℕ :=
  sInf { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n }

theorem A268597.pos_of_witness (n x : ℕ) (hx : 0 < x)
    (h : (x - 1) % Nat.totient x = n) : A268597 n > 0 := by
  rw [A268597, gt_iff_lt, Nat.pos_iff_ne_zero]
  intro hz
  rcases Nat.sInf_eq_zero.mp hz with h0 | hemp
  · exact absurd h0.1 (by norm_num)
  · exact Set.eq_empty_iff_forall_notMem.mp hemp x ⟨hx, h⟩

theorem A268597.pos_of_goldbach (n p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (h3 : 3 ≤ p) (hlt : p < q) (hsum : p + q = n + 2) : A268597 n > 0 := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr (Nat.ne_of_lt hlt)
  have htot : Nat.totient (p * q) = (p - 1) * (q - 1) := by
    rw [Nat.totient_mul hcop, Nat.totient_prime hp, Nat.totient_prime hq]
  obtain ⟨a, rfl⟩ : ∃ a, p = a + 3 := ⟨p - 3, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, q = b + 4 := ⟨q - 4, by omega⟩
  have hD : (a + 3 - 1) * (b + 4 - 1) + (a + b + 5) = (a + 3) * (b + 4) - 1 := by
    simp only [show a + 3 - 1 = a + 2 from rfl, show b + 4 - 1 = b + 3 from rfl]
    have : (a + 3) * (b + 4) = (a + 2) * (b + 3) + (a + b + 5) + 1 := by ring
    omega
  have hr : a + b + 5 < (a + 3 - 1) * (b + 4 - 1) := by
    simp only [show a + 3 - 1 = a + 2 from rfl, show b + 4 - 1 = b + 3 from rfl]
    nlinarith
  apply A268597.pos_of_witness n ((a + 3) * (b + 4)) (by positivity)
  rw [htot, ← hD, Nat.add_mod_left, Nat.mod_eq_of_lt hr]
  omega

theorem A268597.pos_of_goldbach_odd (n t a b : ℕ)
    (hp : Nat.Prime (a + 5)) (hq : Nat.Prime (b + 11)) (hlt : a + 5 < b + 11)
    (hN : n + 1 = 2 ^ (t + 1) * (a + b + 15)) :
    A268597 n > 0 := by
  set p := a + 5 with hpdef
  set q := b + 11 with hqdef
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr (Nat.ne_of_lt hlt)
  have hc2 : Nat.Coprime (2 ^ (t + 1)) (p * q) := by
    apply Nat.Coprime.mul_right
    · exact (Nat.coprime_primes Nat.prime_two hp).mpr (by omega) |>.pow_left _
    · exact (Nat.coprime_primes Nat.prime_two hq).mpr (by omega) |>.pow_left _
  have htot : Nat.totient (2 ^ (t + 1) * (p * q)) = 2 ^ t * ((a + 4) * (b + 10)) := by
    rw [Nat.totient_mul hc2, Nat.totient_mul hcop, Nat.totient_prime hp,
      Nat.totient_prime hq, Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos t)]
    simp [hpdef, hqdef]
  apply A268597.pos_of_witness n (2 ^ (t + 1) * (p * q)) (by positivity)
  rw [htot]
  have hE : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have hkey : 2 ^ (t + 1) * (p * q) = 2 ^ t * ((a + 4) * (b + 10)) * 2
      + 2 ^ (t + 1) * (a + b + 15) := by
    simp only [hpdef, hqdef]; ring
  have hlt2 : 2 ^ (t + 1) * (a + b + 15) - 1 < 2 ^ t * ((a + 4) * (b + 10)) := by
    have hPR : 2 * (a + b + 15) < (a + 4) * (b + 10) := by nlinarith
    calc 2 ^ (t + 1) * (a + b + 15) - 1 < 2 ^ (t + 1) * (a + b + 15) := by
          have : 0 < 2 ^ (t + 1) * (a + b + 15) := by positivity
          omega
      _ = 2 ^ t * (2 * (a + b + 15)) := by ring
      _ ≤ 2 ^ t * ((a + 4) * (b + 10)) := Nat.mul_le_mul_left _ (le_of_lt hPR)
  have hx1 : 2 ^ (t + 1) * (p * q) - 1
      = (2 ^ (t + 1) * (a + b + 15) - 1) + 2 ^ t * ((a + 4) * (b + 10)) * 2 := by
    have h1 : 0 < 2 ^ (t + 1) * (a + b + 15) := by positivity
    omega
  rw [hx1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt2]
  omega

theorem A268597.pos_two_three (n s k : ℕ) (hN : n + 1 = 2 ^ (s + 1) * 3 ^ k) :
    A268597 n > 0 := by
  have hc23 : Nat.Coprime 2 3 := by norm_num
  have hc : Nat.Coprime (2 ^ (s + 1)) (3 ^ (k + 1)) := hc23.pow _ _
  have htot : Nat.totient (2 ^ (s + 1) * 3 ^ (k + 1)) = 2 ^ (s + 1) * 3 ^ k := by
    rw [Nat.totient_mul hc, Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos s),
      Nat.totient_prime_pow Nat.prime_three (Nat.succ_pos k)]
    simp only [Nat.succ_sub_one]
    ring
  apply A268597.pos_of_witness n (2 ^ (s + 1) * 3 ^ (k + 1)) (by positivity)
  rw [htot]
  have hkey : 2 ^ (s + 1) * 3 ^ (k + 1) = (2 ^ (s + 1) * 3 ^ k) * 2 + (n + 1) := by
    rw [hN]; ring
  have hpos : 0 < 2 ^ (s + 1) * 3 ^ k := by positivity
  have hx1 : 2 ^ (s + 1) * 3 ^ (k + 1) - 1 = n + (2 ^ (s + 1) * 3 ^ k) * 2 := by omega
  rw [hx1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem A268597.pos_two_prime_sq (n s p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hN : n + 1 = 2 ^ (s + 1) * p) : A268597 n > 0 := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hc : Nat.Coprime (2 ^ (s + 1)) (p ^ 2) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega))
  have htot : Nat.totient (2 ^ (s + 1) * p ^ 2) = 2 ^ s * (p * (p - 1)) := by
    rw [Nat.totient_mul hc, Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos s),
      Nat.totient_prime_pow hp (by norm_num : 0 < 2)]
    simp only [Nat.succ_sub_one, pow_one]
    ring
  apply A268597.pos_of_witness n (2 ^ (s + 1) * p ^ 2) (by positivity)
  rw [htot]
  obtain ⟨c, rfl⟩ : ∃ c, p = c + 3 := ⟨p - 3, by omega⟩
  have hkey : 2 ^ (s + 1) * (c + 3) ^ 2
      = (2 ^ s * ((c + 3) * (c + 3 - 1))) * 2 + 2 ^ (s + 1) * (c + 3) := by
    simp only [show c + 3 - 1 = c + 2 from rfl]
    ring
  have hpos : 0 < 2 ^ s * ((c + 3) * (c + 3 - 1)) := by
    simp only [show c + 3 - 1 = c + 2 from rfl]; positivity
  have hlt : n < 2 ^ s * ((c + 3) * (c + 3 - 1)) := by
    simp only [show c + 3 - 1 = c + 2 from rfl]
    have h1 : 2 ^ (s + 1) * (c + 3) = 2 ^ s * ((c + 3) * 2) := by ring
    have h2 : 2 ^ s * ((c + 3) * 2) ≤ 2 ^ s * ((c + 3) * (c + 2)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
    have h3 : 0 < 2 ^ s * ((c + 3) * 2) := by positivity
    omega
  have hx1 : 2 ^ (s + 1) * (c + 3) ^ 2 - 1
      = n + (2 ^ s * ((c + 3) * (c + 3 - 1))) * 2 := by omega
  rw [hx1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- The Goldbach-type hypothesis to which the conjecture reduces. -/
def GoldbachPairs : Prop :=
  ∀ m : ℕ, 26 ≤ m → 2 ∣ m →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 5 ≤ p ∧ p + 6 ≤ q ∧ p + q = m

/-- Main reduction: `GoldbachPairs` implies the full A268597 conjecture. -/
theorem A268597.conjecture_of_goldbach (H : GoldbachPairs) (n : ℕ) :
    A268597 n > 0 := by
  by_cases h2 : 2 ∣ (n + 1)
  · -- `n` odd (or the special treatment via powers of two): N = n+1 even
    obtain ⟨s, W, hWodd, hsW⟩ := Nat.exists_eq_pow_mul_and_not_dvd
      (show n + 1 ≠ 0 by omega) 2 (by norm_num)
    have hs1 : 1 ≤ s := by
      rcases Nat.eq_zero_or_pos s with rfl | h
      · simp at hsW; rw [hsW] at h2; exact absurd h2 hWodd
      · exact h
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    by_cases hW25 : W ≤ 24
    · have hW1 : 1 ≤ W := by
        rcases Nat.eq_zero_or_pos W with rfl | h
        · simp at hsW
        · exact h
      interval_cases W
      · exact A268597.pos_two_three n t 0 (by simpa using hsW)
      · exact absurd (by norm_num : (2:ℕ) ∣ 2) hWodd
      · exact A268597.pos_two_three n t 1 (by simpa using hsW)
      · exact absurd (by norm_num : (2:ℕ) ∣ 4) hWodd
      · exact A268597.pos_two_prime_sq n t 5 (by norm_num) (by norm_num) hsW
      · exact absurd (by norm_num : (2:ℕ) ∣ 6) hWodd
      · exact A268597.pos_two_prime_sq n t 7 (by norm_num) (by norm_num) hsW
      · exact absurd (by norm_num : (2:ℕ) ∣ 8) hWodd
      · exact A268597.pos_two_three n t 2 (by simpa using hsW)
      · exact absurd (by norm_num : (2:ℕ) ∣ 10) hWodd
      · exact A268597.pos_two_prime_sq n t 11 (by norm_num) (by norm_num) hsW
      · exact absurd (by norm_num : (2:ℕ) ∣ 12) hWodd
      · exact A268597.pos_two_prime_sq n t 13 (by norm_num) (by norm_num) hsW
      · exact absurd (by norm_num : (2:ℕ) ∣ 14) hWodd
      · exact A268597.pos_of_goldbach_odd n t 0 0 (by norm_num) (by norm_num)
          (by norm_num) (by simpa using hsW)
      · exact absurd (by norm_num : (2:ℕ) ∣ 16) hWodd
      · exact A268597.pos_two_prime_sq n t 17 (by norm_num) (by norm_num) hsW
      · exact absurd (by norm_num : (2:ℕ) ∣ 18) hWodd
      · exact A268597.pos_two_prime_sq n t 19 (by norm_num) (by norm_num) hsW
      · exact absurd (by norm_num : (2:ℕ) ∣ 20) hWodd
      · exact A268597.pos_of_goldbach_odd n t 0 6 (by norm_num) (by norm_num)
          (by norm_num) (by simpa using hsW)
      · exact absurd (by norm_num : (2:ℕ) ∣ 22) hWodd
      · exact A268597.pos_two_prime_sq n t 23 (by norm_num) (by norm_num) hsW
      · exact absurd (by norm_num : (2:ℕ) ∣ 24) hWodd
    · -- W ≥ 25, odd; use H on W + 1
      have hWodd' : ¬ 2 ∣ W := hWodd
      obtain ⟨p, q, hp, hq, h5, h6, hsum⟩ := H (W + 1) (by omega) (by omega)
      obtain ⟨a, rfl⟩ : ∃ a, p = a + 5 := ⟨p - 5, by omega⟩
      obtain ⟨b, rfl⟩ : ∃ b, q = b + 11 := ⟨q - 11, by omega⟩
      exact A268597.pos_of_goldbach_odd n t a b hp hq (by omega)
        (by rw [hsW]; congr 1; omega)
  · -- `n` even: N = n + 1 odd
    by_cases hsmall : n ≤ 22
    · have hne : ¬ 2 ∣ (n + 1) := h2
      interval_cases n
      · exact A268597.pos_of_witness 0 1 (by norm_num) (by decide)
      · exact absurd (by norm_num : (2:ℕ) ∣ 2) hne
      · exact A268597.pos_of_witness 2 9 (by norm_num) (by decide)
      · exact absurd (by norm_num : (2:ℕ) ∣ 4) hne
      · exact A268597.pos_of_witness 4 25 (by norm_num) (by decide)
      · exact absurd (by norm_num : (2:ℕ) ∣ 6) hne
      · exact A268597.pos_of_witness 6 15 (by norm_num) (by decide)
      · exact absurd (by norm_num : (2:ℕ) ∣ 8) hne
      · exact A268597.pos_of_witness 8 21 (by norm_num) (by decide)
      · exact absurd (by norm_num : (2:ℕ) ∣ 10) hne
      · exact A268597.pos_of_witness 10 35 (by norm_num) (by decide)
      · exact absurd (by norm_num : (2:ℕ) ∣ 12) hne
      · exact A268597.pos_of_witness 12 33 (by norm_num) (by decide)
      · exact absurd (by norm_num : (2:ℕ) ∣ 14) hne
      · exact A268597.pos_of_witness 14 39 (by norm_num) (by decide)
      · exact absurd (by norm_num : (2:ℕ) ∣ 16) hne
      · exact A268597.pos_of_witness 16 65 (by norm_num) (by decide)
      · exact absurd (by norm_num : (2:ℕ) ∣ 18) hne
      · exact A268597.pos_of_witness 18 51 (by norm_num) (by decide)
      · exact absurd (by norm_num : (2:ℕ) ∣ 20) hne
      · exact A268597.pos_of_witness 20 45 (by norm_num) (by decide)
      · exact absurd (by norm_num : (2:ℕ) ∣ 22) hne
      · exact A268597.pos_of_witness 22 95 (by norm_num) (by decide)
    · obtain ⟨p, q, hp, hq, h5, h6, hsum⟩ := H (n + 2) (by omega) (by omega)
      exact A268597.pos_of_goldbach n p q hp hq (by omega) (by omega) hsum

/-!
Everything above is fully proved.  The conjecture below therefore reduces to
`GoldbachPairs`: every even `m ≥ 26` is `p + q` with primes `5 ≤ p`, `p + 6 ≤ q`.
This is a strong form of the binary Goldbach conjecture — an open problem, verified
numerically far beyond any bound relevant here, but not provable with current
mathematics; hence the single remaining `sorry` below is exactly that open core.
-/

/--
A268597 Conjecture: a(n) > 0 for all n.
-/
theorem oeis_268597_conjecture_0 (n : ℕ) : A268597 n > 0 :=
  A268597.conjecture_of_goldbach (fun _m _hm _h2 => by sorry) n
