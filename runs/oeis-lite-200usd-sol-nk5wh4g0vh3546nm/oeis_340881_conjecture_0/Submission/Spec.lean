import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) fun k ↦
    (2 ^ Nat.choose (k + 1) 2) *
    (Finset.prod (Finset.Ico (k + 1) n) fun j ↦ (2 ^ j - 1))

lemma a_succ_cast (p n : ℕ) :
    (a (n+1) : ZMod p) = ((2 : ZMod p)^n - 1) * (a n : ZMod p) +
      (2 : ZMod p) ^ Nat.choose (n+1) 2 := by
  simp only [a, Finset.sum_range_succ]
  push_cast
  have hone : ∀ j : ℕ, 1 ≤ 2^j := by intro j; exact Nat.one_le_pow j 2 (by omega)
  simp_rw [Nat.cast_sub (hone _), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  rw [Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    have hkn : k + 1 ≤ n := by simpa using hk
    rw [Finset.prod_Ico_succ_top hkn]
    ring
  · simp

lemma choose_add_two (x y : ℕ) :
    Nat.choose (x+y) 2 = Nat.choose x 2 + x*y + Nat.choose y 2 := by
  rw [Nat.add_choose_eq]
  simp [Finset.Nat.antidiagonal_succ_succ']
  omega

lemma choose_two_mul (q : ℕ) : Nat.choose (2*q) 2 = q * (2*q-1) := by
  rw [Nat.choose_two_right]
  have h : 2*q*(2*q-1) = (q*(2*q-1))*2 := by ring
  rw [h, Nat.mul_div_cancel _ (by omega)]

lemma choose_two_mul_add_one (q : ℕ) : Nat.choose (2*q+1) 2 = q * (2*q+1) := by
  rw [Nat.choose_two_right]
  have hs : 2*q+1-1 = 2*q := by omega
  rw [hs]
  have h : (2*q+1)*(2*q) = (q*(2*q+1))*2 := by ring
  rw [h, Nat.mul_div_cancel _ (by omega)]

lemma pow_shift_choose {p : ℕ} [Fact p.Prime]
    (h2 : (2 : ZMod p) ≠ 0) (x : ℕ) :
    (2 : ZMod p) ^ Nat.choose (x + 2*(p-1)) 2 =
      (2 : ZMod p) ^ Nat.choose x 2 := by
  have hF : (2 : ZMod p) ^ (p-1) = 1 := ZMod.pow_card_sub_one_eq_one h2
  rw [choose_add_two, pow_add, pow_add, choose_two_mul]
  have hxa : x * (2 * (p - 1)) = (p-1) * (2*x) := by ring
  rw [hxa, pow_mul, hF, one_pow]
  rw [pow_mul, hF, one_pow, mul_one, mul_one]

lemma pow_shift {p : ℕ} [Fact p.Prime]
    (h2 : (2 : ZMod p) ≠ 0) (x : ℕ) :
    (2 : ZMod p) ^ (x + 2*(p-1)) = (2 : ZMod p)^x := by
  have hF : (2 : ZMod p) ^ (p-1) = 1 := ZMod.pow_card_sub_one_eq_one h2
  rw [pow_add]
  have ht : 2*(p-1) = (p-1)*2 := by omega
  rw [ht, pow_mul, hF, one_pow, mul_one]

lemma a_period_cast_odd (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    ∀ n : ℕ, 1 ≤ n → (a (n + 2*(p-1)) : ZMod p) = (a n : ZMod p) := by
  letI : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hp1 | hp2
    · exact hp.ne_one hp1
    · exact hodd hp2
  have hF : (2 : ZMod p) ^ (p-1) = 1 := ZMod.pow_card_sub_one_eq_one h2
  have hbase : (a (1 + 2*(p-1)) : ZMod p) = (a 1 : ZMod p) := by
    rw [show 1 + 2*(p-1) = 2*(p-1)+1 by omega, a_succ_cast]
    have ht := pow_shift h2 0
    simp only [zero_add, pow_zero] at ht
    rw [ht]
    simp only [sub_self, zero_mul, zero_add]
    rw [choose_two_mul_add_one, pow_mul, hF, one_pow]
    simp [a]
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction m with
  | zero => simpa using hbase
  | succ m ih =>
      rw [show 1 + (m+1) + 2*(p-1) = (1+m+2*(p-1))+1 by omega,
        a_succ_cast, show 1+(m+1) = (1+m)+1 by omega, a_succ_cast]
      rw [pow_shift h2 (1+m)]
      rw [show 1+m+2*(p-1)+1 = (1+m+1)+2*(p-1) by omega,
        pow_shift_choose h2 (1+m+1), ih (by omega)]

lemma a_cast_two (n : ℕ) (hn : 1 ≤ n) : (a n : ZMod 2) = 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction m with
  | zero => simp [a]
  | succ m ih =>
      rw [show 1+(m+1) = (1+m)+1 by omega, a_succ_cast, ih (by omega)]
      have he : Nat.choose (1+m+1) 2 ≠ 0 :=
        (Nat.choose_pos (by omega)).ne'
      have hpos : 1+m ≠ 0 := by omega
      have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
      rw [htwo, zero_pow hpos, zero_pow he]
      exact (show (-1 : ZMod 2) = 1 by decide)

 theorem oeis_340881_conjecture_0 (p : ℕ) (hp : Nat.Prime p) :
  ∀ (n : ℕ), n ≥ 1 → a (n + 2 * (p - 1)) % p = a n % p := by
  intro n hn
  change a (n + 2 * (p - 1)) ≡ a n [MOD p]
  rw [← ZMod.natCast_eq_natCast_iff]
  by_cases h : p = 2
  · subst p
    rw [a_cast_two n hn, a_cast_two (n + 2 * (2-1)) (by omega)]
  · exact a_period_cast_odd p hp h n hn
