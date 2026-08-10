import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
Row sums of A340880.
$$a(n) = \sum_{k = 0}^{n-1} 2^{k(k+1)/2} \cdot \left( \prod_{j = k+1}^{n-1} (2^j - 1) \right)$$
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) fun k ↦
    (2 ^ Nat.choose (k + 1) 2) *
    (Finset.prod (Finset.Ico (k + 1) n) fun j ↦ (2 ^ j - 1))

/--
Conjectures: 1) For prime p, the sequence taken modulo p is purely periodic with
minimum period dividing 2*(p - 1).
-/
lemma a_succ (n : ℕ) :
    a (n + 1) = (2 ^ n - 1) * a n + 2 ^ Nat.choose (n + 1) 2 := by
  unfold a
  rw [Finset.sum_range_succ]
  rw [Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    have hkle : k + 1 ≤ n := by
      simpa using hk
    rw [Nat.Ico_succ_right_eq_insert_Ico hkle]
    rw [Finset.prod_insert]
    · ring
    · simp [Finset.mem_Ico]
  · simp

lemma cast_two_pow_sub_one (p n : ℕ) :
    ((2 ^ n - 1 : ℕ) : ZMod p) = (2 : ZMod p) ^ n - 1 := by
  rw [Nat.cast_sub]
  · simp
  · exact Nat.succ_le_of_lt (pow_pos (by norm_num) n)

lemma cast_a_succ (p n : ℕ) :
    ((a (n + 1) : ℕ) : ZMod p) =
      (((2 : ZMod p) ^ n - 1) * ((a n : ℕ) : ZMod p) +
        (2 : ZMod p) ^ Nat.choose (n + 1) 2) := by
  rw [a_succ]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [cast_two_pow_sub_one]

lemma zmod_two_fermat (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    (2 : ZMod p) ^ (p - 1) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hneq : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdiv : p ∣ 2 := by
      exact (ZMod.natCast_eq_zero_iff 2 p).mp h
    have hp_le : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    have hge : 2 ≤ p := hp.two_le
    exact hp2 (le_antisymm hp_le hge)
  exact ZMod.pow_card_sub_one_eq_one hneq

lemma two_pow_add_period_zmod (p n m : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    (2 : ZMod p) ^ (n + (p - 1) * m) = (2 : ZMod p) ^ n := by
  rw [pow_add, pow_mul, zmod_two_fermat p hp hp2, one_pow, mul_one]

lemma choose_add_two (m : ℕ) :
    Nat.choose (m + 2) 2 = Nat.choose m 2 + 2 * m + 1 := by
  rw [show m + 2 = (m + 1).succ by rfl]
  rw [Nat.choose_succ_succ]
  rw [show (m + 1).choose 1 = m + 1 by simp]
  rw [show (m + 1).choose 2 = (m.succ).choose (1 + 1) by rfl]
  rw [Nat.choose_succ_succ]
  simp
  ring_nf

lemma choose_shift_two (n q : ℕ) :
    Nat.choose (n + 2 * q + 1) 2 =
      Nat.choose (n + 1) 2 + q * (2 * n + 2 * q + 1) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ]
    rw [show n + (2 * q + 2) + 1 = (n + 2 * q + 1) + 2 by omega]
    rw [choose_add_two]
    rw [ih]
    ring_nf

lemma coeff_period_odd (p n : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    (2 : ZMod p) ^ (n + 2 * (p - 1)) = (2 : ZMod p) ^ n := by
  rw [show n + 2 * (p - 1) = n + (p - 1) * 2 by omega]
  exact two_pow_add_period_zmod p n 2 hp hp2

lemma inhom_period_odd (p n : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    (2 : ZMod p) ^ Nat.choose (n + 2 * (p - 1) + 1) 2 =
      (2 : ZMod p) ^ Nat.choose (n + 1) 2 := by
  rw [choose_shift_two n (p - 1)]
  exact two_pow_add_period_zmod p (Nat.choose (n + 1) 2)
    (2 * n + 2 * (p - 1) + 1) hp hp2

lemma a_one : a 1 = 1 := by
  simp [a]

lemma odd_period_zmod (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    ∀ n : ℕ, 1 ≤ n →
      ((a (n + 2 * (p - 1)) : ℕ) : ZMod p) = ((a n : ℕ) : ZMod p) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      rw [show 1 + 2 * (p - 1) = 2 * (p - 1) + 1 by omega]
      rw [cast_a_succ]
      have hc : (2 : ZMod p) ^ (2 * (p - 1)) = 1 := by
        simpa using coeff_period_odd p 0 hp hp2
      have hb : (2 : ZMod p) ^ Nat.choose (2 * (p - 1) + 1) 2 = 1 := by
        simpa using inhom_period_odd p 0 hp hp2
      rw [hc, hb]
      simp [a_one]
  | succ n hn ih =>
      rw [show n + 1 + 2 * (p - 1) = (n + 2 * (p - 1)) + 1 by omega]
      rw [cast_a_succ, cast_a_succ]
      rw [ih, coeff_period_odd p n hp hp2, inhom_period_odd p n hp hp2]

lemma two_zmod_one (n : ℕ) (hn : 1 ≤ n) : ((a n : ℕ) : ZMod 2) = 1 := by
  induction n, hn using Nat.le_induction with
  | base => simp [a_one]
  | succ n hn ih =>
      rw [cast_a_succ]
      have hpow : (2 : ZMod 2) ^ n = 0 := by
        have hnpos : 0 < n := by omega
        rw [show (2 : ZMod 2) = 0 by simpa using (ZMod.natCast_self 2)]
        exact zero_pow hnpos.ne'
      have hchoose_pos : 0 < Nat.choose (n + 1) 2 := Nat.choose_pos (by omega)
      rw [hpow, ih]
      rw [show (2 : ZMod 2) = 0 by simpa using (ZMod.natCast_self 2)]
      rw [zero_pow hchoose_pos.ne']
      decide

lemma two_period_zmod (n : ℕ) (hn : 1 ≤ n) :
    ((a (n + 2 * (2 - 1)) : ℕ) : ZMod 2) = ((a n : ℕ) : ZMod 2) := by
  rw [two_zmod_one (n + 2 * (2 - 1)) (by omega), two_zmod_one n hn]

theorem oeis_340881_conjecture_0 (p : ℕ) (hp : Nat.Prime p) :
  ∀ (n : ℕ), n ≥ 1 → a (n + 2 * (p - 1)) % p = a n % p := by
  intro n hn
  by_cases hp2 : p = 2
  · subst p
    have hz := two_period_zmod n hn
    exact (ZMod.natCast_eq_natCast_iff (a (n + 2 * (2 - 1))) (a n) 2).mp hz
  · have hz := odd_period_zmod p hp hp2 n hn
    exact (ZMod.natCast_eq_natCast_iff (a (n + 2 * (p - 1))) (a n) p).mp hz
