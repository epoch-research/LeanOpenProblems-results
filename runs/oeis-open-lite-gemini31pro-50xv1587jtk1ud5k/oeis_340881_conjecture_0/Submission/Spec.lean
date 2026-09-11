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

lemma a_succ (n : ℕ) : a (n + 1) = (2 ^ n - 1) * a n + 2 ^ (Nat.choose (n + 1) 2) := by
  unfold a
  rw [sum_range_succ]
  have H : ∀ k ∈ range n, Finset.prod (Ico (k + 1) (n + 1)) (fun j => 2 ^ j - 1) =
      (Finset.prod (Ico (k + 1) n) (fun j => 2 ^ j - 1)) * (2 ^ n - 1) := by
    intro k hk
    rw [mem_range] at hk
    have H2 : k + 1 ≤ n := hk
    rw [prod_Ico_succ_top H2]
  have H3 : (∑ x ∈ range n, 2 ^ choose (x + 1) 2 * ∏ j ∈ Ico (x + 1) (n + 1), (2 ^ j - 1)) =
      ∑ x ∈ range n, (2 ^ choose (x + 1) 2 * ∏ j ∈ Ico (x + 1) n, (2 ^ j - 1)) * (2 ^ n - 1) := by
    apply sum_congr rfl
    intro x hx
    rw [H x hx]
    ring
  rw [H3]
  rw [← sum_mul]
  have H4 : ∏ j ∈ Ico (n + 1) (n + 1), (2 ^ j - 1) = 1 := by rw [Ico_self, prod_empty]
  rw [H4]
  ring

lemma two_pow_ge_one (n : ℕ) : 1 ≤ 2 ^ n := Nat.one_le_two_pow

lemma a_succ_zmod (p n : ℕ) [NeZero p] : (a (n + 1) : ZMod p) = ((2 ^ n - 1 : ℕ) : ZMod p) * (a n : ZMod p) + ((2 ^ (Nat.choose (n + 1) 2) : ℕ) : ZMod p) := by
  rw [a_succ]
  push_cast
  rfl

lemma two_pow_mod_p (p : ℕ) [hp : Fact (Nat.Prime p)] (hp2 : p ≠ 2) (x y k : ℕ) (h : x = y + k * (p - 1)) :
    ((2 ^ x : ℕ) : ZMod p) = ((2 ^ y : ℕ) : ZMod p) := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h_eq
    have h_dvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h_eq
    have h_le : p ≤ 2 := Nat.le_of_dvd (by decide) h_dvd
    have h_prime_p : p.Prime := hp.out
    have h_p_ge_2 : p ≥ 2 := h_prime_p.two_le
    have h_p_eq_2 : p = 2 := by omega
    exact hp2 h_p_eq_2
  have h_pow : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2
  have h_cast : ((2 ^ x : ℕ) : ZMod p) = (2 : ZMod p) ^ x := by push_cast; rfl
  have h_cast2 : ((2 ^ y : ℕ) : ZMod p) = (2 : ZMod p) ^ y := by push_cast; rfl
  rw [h_cast, h_cast2, h, pow_add]
  have h_pow_k : (2 : ZMod p) ^ (k * (p - 1)) = 1 := by
    rw [mul_comm, pow_mul, h_pow, one_pow]
  rw [h_pow_k, mul_one]

lemma c_periodic (p : ℕ) [hp : Fact (Nat.Prime p)] (hp2 : p ≠ 2) (n : ℕ) :
    ((2 ^ (n + 2 * (p - 1)) - 1 : ℕ) : ZMod p) = ((2 ^ n - 1 : ℕ) : ZMod p) := by
  have H : ((2 ^ (n + 2 * (p - 1)) : ℕ) : ZMod p) = ((2 ^ n : ℕ) : ZMod p) := by
    apply two_pow_mod_p p hp2 (n + 2 * (p - 1)) n 2
    ring
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ (n + 2 * (p - 1)) := Nat.one_le_two_pow
  rw [Nat.cast_sub h2, Nat.cast_sub h1]
  rw [H]

lemma choose_two_mul_two (x : ℕ) : choose (x + 1) 2 * 2 = x * (x + 1) := by
  induction' x with k ih
  · rfl
  · rw [choose_succ_succ]
    have h1 : choose (k + 1) 1 = k + 1 := by rw [choose_one_right]
    rw [h1]
    calc
      (k + 1 + choose (k + 1) 2) * 2 = (k + 1) * 2 + choose (k + 1) 2 * 2 := by ring
      _ = (k + 1) * 2 + k * (k + 1) := by rw [ih]
      _ = (k + 1) * (k + 1 + 1) := by ring

lemma choose_periodic (p n : ℕ) :
    choose (n + 2 * (p - 1) + 1) 2 = choose (n + 1) 2 + (p - 1) * (2 * n + 2 * (p - 1) + 1) := by
  have H1 : choose (n + 2 * (p - 1) + 1) 2 * 2 = (n + 2 * (p - 1)) * (n + 2 * (p - 1) + 1) := by
    exact choose_two_mul_two (n + 2 * (p - 1))
  have H2 : choose (n + 1) 2 * 2 = n * (n + 1) := by
    exact choose_two_mul_two n
  have H3 : choose (n + 2 * (p - 1) + 1) 2 * 2 = (choose (n + 1) 2 + (p - 1) * (2 * n + 2 * (p - 1) + 1)) * 2 := by
    calc
      choose (n + 2 * (p - 1) + 1) 2 * 2 = (n + 2 * (p - 1)) * (n + 2 * (p - 1) + 1) := H1
      _ = n * (n + 1) + (p - 1) * (2 * n + 2 * (p - 1) + 1) * 2 := by ring
      _ = choose (n + 1) 2 * 2 + (p - 1) * (2 * n + 2 * (p - 1) + 1) * 2 := by rw [H2]
      _ = (choose (n + 1) 2 + (p - 1) * (2 * n + 2 * (p - 1) + 1)) * 2 := by ring
  omega

lemma b_periodic (p : ℕ) [hp : Fact (Nat.Prime p)] (hp2 : p ≠ 2) (n : ℕ) :
    ((2 ^ choose (n + 2 * (p - 1) + 1) 2 : ℕ) : ZMod p) = ((2 ^ choose (n + 1) 2 : ℕ) : ZMod p) := by
  have h := choose_periodic p n
  have h_comm : (p - 1) * (2 * n + 2 * (p - 1) + 1) = (2 * n + 2 * (p - 1) + 1) * (p - 1) := by ring
  rw [h_comm] at h
  exact two_pow_mod_p p hp2 (choose (n + 2 * (p - 1) + 1) 2) (choose (n + 1) 2) (2 * n + 2 * (p - 1) + 1) h

lemma c_M (p : ℕ) [hp : Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    ((2 ^ (2 * (p - 1)) - 1 : ℕ) : ZMod p) = 0 := by
  have H : ((2 ^ (2 * (p - 1)) : ℕ) : ZMod p) = 1 := by
    have H2 : ((2 ^ (2 * (p - 1)) : ℕ) : ZMod p) = ((2 ^ 0 : ℕ) : ZMod p) := by
      apply two_pow_mod_p p hp2 (2 * (p - 1)) 0 2
      ring
    rw [H2]
    push_cast
    rfl
  have h1 : 1 ≤ 2 ^ (2 * (p - 1)) := Nat.one_le_two_pow
  rw [Nat.cast_sub h1]
  rw [H]
  push_cast
  ring

lemma a_zero : a 0 = 0 := rfl

lemma a_one_zmod (p : ℕ) [NeZero p] : (a 1 : ZMod p) = 1 := by
  have : a 1 = 1 := by rfl
  rw [this]
  push_cast
  rfl

lemma a_M_plus_one (p : ℕ) [hp : Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    (a (2 * (p - 1) + 1) : ZMod p) = 1 := by
  rw [a_succ_zmod p (2 * (p - 1))]
  have h_c : ((2 ^ (2 * (p - 1)) - 1 : ℕ) : ZMod p) = 0 := c_M p hp2
  rw [h_c]
  have h_b : ((2 ^ choose (2 * (p - 1) + 1) 2 : ℕ) : ZMod p) = ((2 ^ choose (0 + 1) 2 : ℕ) : ZMod p) := by
    have h_eq : 2 * (p - 1) = 0 + 2 * (p - 1) := by ring
    rw [h_eq]
    exact b_periodic p hp2 0
  rw [h_b]
  have : choose (0 + 1) 2 = 0 := rfl
  rw [this]
  push_cast
  ring

lemma a_periodic (p : ℕ) [hp : Fact (Nat.Prime p)] (hp2 : p ≠ 2) (n : ℕ) (hn : n ≥ 1) :
    (a (n + 2 * (p - 1)) : ZMod p) = (a n : ZMod p) := by
  induction' n, hn using Nat.le_induction with k hk ih
  · have h1 : 1 + 2 * (p - 1) = 2 * (p - 1) + 1 := by ring
    rw [h1]
    rw [a_M_plus_one p hp2]
    rw [a_one_zmod p]
  · have h_eq : k + 1 + 2 * (p - 1) = k + 2 * (p - 1) + 1 := by ring
    rw [h_eq]
    rw [a_succ_zmod p (k + 2 * (p - 1))]
    rw [a_succ_zmod p k]
    have h_c : ((2 ^ (k + 2 * (p - 1)) - 1 : ℕ) : ZMod p) = ((2 ^ k - 1 : ℕ) : ZMod p) := c_periodic p hp2 k
    have h_b : ((2 ^ choose (k + 2 * (p - 1) + 1) 2 : ℕ) : ZMod p) = ((2 ^ choose (k + 1) 2 : ℕ) : ZMod p) := b_periodic p hp2 k
    rw [h_c, h_b, ih]

lemma two_pow_zmod_two_pos (k : ℕ) (hk : k ≠ 0) : ((2 ^ k : ℕ) : ZMod 2) = 0 := by
  have : ((2 ^ k : ℕ) : ZMod 2) = (2 : ZMod 2) ^ k := by push_cast; rfl
  rw [this]
  have H : (2 : ZMod 2) = 0 := rfl
  rw [H]
  exact zero_pow hk

lemma a_mod_two (n : ℕ) (hn : n ≥ 1) : (a n : ZMod 2) = 1 := by
  induction' n, hn using Nat.le_induction with k hk ih
  · rw [a_one_zmod 2]
  · rw [a_succ_zmod 2 k]
    rw [ih]
    have h_pow : ((2 ^ k : ℕ) : ZMod 2) = 0 := by
      have hk0 : k ≠ 0 := by omega
      exact two_pow_zmod_two_pos k hk0
    have h_choose : choose (k + 1) 2 ≠ 0 := by
      have : k + 1 ≥ 2 := by omega
      exact Nat.choose_pos this |>.ne'
    have h_pow2 : ((2 ^ choose (k + 1) 2 : ℕ) : ZMod 2) = 0 := by
      exact two_pow_zmod_two_pos (choose (k + 1) 2) h_choose
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [Nat.cast_sub h1]
    rw [h_pow]
    rw [h_pow2]
    push_cast
    exact rfl

lemma zmod_eq_iff_mod_eq (p : ℕ) (x y : ℕ) [NeZero p] : (x : ZMod p) = (y : ZMod p) ↔ x % p = y % p := by
  exact ZMod.natCast_eq_natCast_iff' x y p

/--
Conjectures: 1) For prime p, the sequence taken modulo p is purely periodic with
minimum period dividing 2*(p - 1).
-/
theorem oeis_340881_conjecture_0 (p : ℕ) (hp : Nat.Prime p) :
  ∀ (n : ℕ), n ≥ 1 → a (n + 2 * (p - 1)) % p = a n % p := by
  intro n hn
  have h_ne_zero : NeZero p := ⟨hp.ne_zero⟩
  rw [← zmod_eq_iff_mod_eq p]
  by_cases hp2 : p = 2
  · rw [hp2]
    have h1 : (a (n + 2 * (2 - 1)) : ZMod 2) = 1 := by
      apply a_mod_two
      omega
    have h2 : (a n : ZMod 2) = 1 := by
      apply a_mod_two n hn
    rw [h1, h2]
  · have hp_fact : Fact (Nat.Prime p) := ⟨hp⟩
    exact a_periodic p hp2 n hn

theorem oeis_340881_conjecture_0.disproof : ¬ (type_of% @oeis_340881_conjecture_0) := sorry
