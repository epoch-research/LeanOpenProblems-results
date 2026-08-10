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

lemma a_succ (n : ℕ) : a (n + 1) = 2 ^ Nat.choose (n + 1) 2 + (2 ^ n - 1) * a n := by
  simp only [a]
  rw [sum_range_succ]
  rw [Ico_self, prod_empty, mul_one]
  rw [add_comm]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  simp only [mem_range] at hk
  have h2 : k + 1 ≤ n := hk
  rw [prod_Ico_succ_top h2]
  ring

lemma a_one : a 1 = 1 := by
  simp [a]

lemma choose_geq_one {n : ℕ} (h : n ≥ 1) : (n + 1).choose 2 ≥ 1 := by
  have h2 : 2 ≤ n + 1 := by omega
  have : 0 < (n + 1).choose 2 := Nat.choose_pos h2
  omega

lemma two_pow_choose_even {n : ℕ} (h : n ≥ 1) : 2 ^ (n + 1).choose 2 % 2 = 0 := by
  have h_choose : (n + 1).choose 2 ≥ 1 := choose_geq_one h
  have h_ne : (n + 1).choose 2 ≠ 0 := by omega
  rcases Nat.exists_eq_succ_of_ne_zero h_ne with ⟨k, hk⟩
  rw [hk, pow_succ]
  simp

lemma two_pow_minus_one_odd {n : ℕ} (h : n ≥ 1) : (2 ^ n - 1) % 2 = 1 := by
  have h_ne : n ≠ 0 := by omega
  rcases Nat.exists_eq_succ_of_ne_zero h_ne with ⟨k, hk⟩
  rw [hk, pow_succ]
  have h_pow : 2 ^ k ≥ 1 := Nat.one_le_pow k 2 (by decide)
  have : 2 * 2 ^ k ≥ 1 := by omega
  omega

lemma a_odd (n : ℕ) : a (n + 1) % 2 = 1 := by
  induction' n with n ih
  · rw [a_one]
  · rw [a_succ]
    rw [Nat.add_mod, Nat.mul_mod]
    have h1 : 2 ^ (n + 2).choose 2 % 2 = 0 := by
      apply two_pow_choose_even
      omega
    have h2 : (2 ^ (n + 1) - 1) % 2 = 1 := by
      apply two_pow_minus_one_odd
      omega
    rw [h1, h2, ih]

theorem p_two_case (n : ℕ) (hn : n ≥ 1) : a (n + 2) % 2 = a n % 2 := by
  have h_ne : n ≠ 0 := by omega
  rcases Nat.exists_eq_succ_of_ne_zero h_ne with ⟨k, rfl⟩
  rw [a_odd, a_odd]

lemma even_mul_consecutive (x : ℕ) : 2 ∣ (x + 1) * x := by
  rcases Nat.even_or_odd x with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · use (2 * k + 1) * k
    ring
  · use (k + 1) * (2 * k + 1)
    ring

lemma two_mul_choose_two (x : ℕ) : 2 * x.choose 2 = x * (x - 1) := by
  induction' x with x ih
  · simp
  · rcases x with _ | x
    · simp
    · have h := Nat.choose_two_right (x + 2)
      have h2 : x + 2 - 1 = x + 1 := by omega
      rw [h2] at h
      rw [h]
      have h3 : 2 ∣ (x + 2) * (x + 1) := even_mul_consecutive (x + 1)
      exact Nat.mul_div_cancel' h3

lemma choose_identity (n k : ℕ) : (n + 2 * k + 1) * (n + 2 * k) = (n + 1) * n + 2 * (2 * n + 2 * k + 1) * k := by ring

lemma choose_relation (p n : ℕ) (hp2 : p > 2) :
  (n + 2 * (p - 1) + 1).choose 2 = (n + 1).choose 2 + (2 * n + 2 * p - 1) * (p - 1) := by
  have h_mul : 2 * (n + 2 * (p - 1) + 1).choose 2 = 2 * ((n + 1).choose 2 + (2 * n + 2 * p - 1) * (p - 1)) := by
    rw [mul_add]
    rw [two_mul_choose_two (n + 2 * (p - 1) + 1)]
    rw [two_mul_choose_two (n + 1)]
    have h_sub1 : n + 2 * (p - 1) + 1 - 1 = n + 2 * (p - 1) := by omega
    have h_sub2 : n + 1 - 1 = n := by omega
    rw [h_sub1, h_sub2]
    -- Now let k = p - 1
    set k := p - 1
    have hpk : p = k + 1 := by omega
    have h_2p1 : 2 * n + 2 * p - 1 = 2 * n + 2 * k + 1 := by omega
    rw [h_2p1]
    -- Both sides are now in terms of n and k
    rw [← mul_assoc]
    exact choose_identity n k
  exact Nat.eq_of_mul_eq_mul_left (by decide) h_mul

lemma pow_M_eq_one (p : ℕ) (hp : Nat.Prime p) (hp2 : p > 2) :
  (2 : ZMod p) ^ (2 * (p - 1)) = 1 := by
  have h_fermat : (2 : ZMod p) ^ (p - 1) = 1 := by
    have : Fact (Nat.Prime p) := ⟨hp⟩
    apply ZMod.pow_card_sub_one_eq_one
    intro h
    have h_val : (2 : ZMod p).val = 0 := by
      rw [h, ZMod.val_zero]
    change ((2 : ℕ) : ZMod p).val = 0 at h_val
    rw [ZMod.val_natCast p 2] at h_val
    rw [Nat.mod_eq_of_lt hp2] at h_val
    contradiction
  rw [mul_comm, pow_mul, h_fermat, one_pow]

lemma two_pow_choose_M_eq (p n : ℕ) (hp : Nat.Prime p) (hp2 : p > 2) :
  (2 : ZMod p) ^ (n + 2 * (p - 1) + 1).choose 2 = (2 : ZMod p) ^ (n + 1).choose 2 := by
  rw [choose_relation p n hp2]
  rw [pow_add]
  have h_fermat : (2 : ZMod p) ^ (p - 1) = 1 := by
    have : Fact (Nat.Prime p) := ⟨hp⟩
    apply ZMod.pow_card_sub_one_eq_one
    intro h
    have h_val : (2 : ZMod p).val = 0 := by
      rw [h, ZMod.val_zero]
    change ((2 : ℕ) : ZMod p).val = 0 at h_val
    rw [ZMod.val_natCast p 2] at h_val
    rw [Nat.mod_eq_of_lt hp2] at h_val
    contradiction
  rw [mul_comm (2 * n + 2 * p - 1) (p - 1), pow_mul, h_fermat, one_pow, mul_one]

theorem general_case (p : ℕ) (hp : Nat.Prime p) (hp2 : p > 2) :
  ∀ (n : ℕ), n ≥ 1 → (a (n + 2 * (p - 1)) : ZMod p) = (a n : ZMod p) := by
  intro n hn
  have h_ne : n ≠ 0 := by omega
  rcases Nat.exists_eq_succ_of_ne_zero h_ne with ⟨k, rfl⟩
  clear hn h_ne
  induction' k with k ih
  · -- Base case: k = 0, so n = 1
    -- We want to show (a (1 + 2 * (p - 1)) : ZMod p) = (a 1 : ZMod p)
    rw [a_one]
    have h_eq : succ 0 + 2 * (p - 1) = 2 * (p - 1) + 1 := by omega
    rw [h_eq]
    -- LHS is a (2 * (p - 1) + 1)
    have h_succ := a_succ (2 * (p - 1))
    have h_le : 1 ≤ 2 ^ (2 * (p - 1)) := by
      have : 2 * (p - 1) ≥ 1 := by omega
      exact Nat.one_le_pow (2 * (p - 1)) 2 (by decide)
    have h_cast : (a (2 * (p - 1) + 1) : ZMod p) = (2 : ZMod p) ^ (2 * (p - 1) + 1).choose 2 + ((2 : ZMod p) ^ (2 * (p - 1)) - 1) * (a (2 * (p - 1)) : ZMod p) := by
      rw [h_succ]
      push_cast [h_le]
      rfl
    rw [h_cast]
    -- Now we can use the lemmas:
    rw [pow_M_eq_one p hp hp2]
    have h_choose_0 : (2 : ZMod p) ^ (0 + 2 * (p - 1) + 1).choose 2 = (2 : ZMod p) ^ (0 + 1).choose 2 := by
      exact two_pow_choose_M_eq p 0 hp hp2
    simp only [zero_add] at h_choose_0
    rw [h_choose_0]
    have h_c : (1 : ℕ).choose 2 = 0 := rfl
    rw [h_c, pow_zero]
    ring
  · -- Induction step
    have h_eq_lhs : (k + 1).succ + 2 * (p - 1) = k + 1 + 2 * (p - 1) + 1 := by omega
    have h_eq_rhs : (k + 1).succ = k + 1 + 1 := by omega
    change (a ((k + 1).succ + 2 * (p - 1)) : ZMod p) = (a (k + 1).succ : ZMod p)
    rw [h_eq_lhs, h_eq_rhs]
    -- LHS is a (k + 1 + 2 * (p - 1) + 1)
    have h_succ_lhs := a_succ (k + 1 + 2 * (p - 1))
    have h_le_lhs : 1 ≤ 2 ^ (k + 1 + 2 * (p - 1)) := by
      have : k + 1 + 2 * (p - 1) ≥ 1 := by omega
      exact Nat.one_le_pow (k + 1 + 2 * (p - 1)) 2 (by decide)
    have h_cast_lhs : (a (k + 1 + 2 * (p - 1) + 1) : ZMod p) = (2 : ZMod p) ^ (k + 1 + 2 * (p - 1) + 1).choose 2 + ((2 : ZMod p) ^ (k + 1 + 2 * (p - 1)) - 1) * (a (k + 1 + 2 * (p - 1)) : ZMod p) := by
      rw [h_succ_lhs]
      push_cast [h_le_lhs]
      rfl
    rw [h_cast_lhs]
    -- RHS is a (k + 1 + 1)
    have h_succ_rhs := a_succ (k + 1)
    have h_le_rhs : 1 ≤ 2 ^ (k + 1) := by
      have : k + 1 ≥ 1 := by omega
      exact Nat.one_le_pow (k + 1) 2 (by decide)
    have h_cast_rhs : (a (k + 1 + 1) : ZMod p) = (2 : ZMod p) ^ (k + 1 + 1).choose 2 + ((2 : ZMod p) ^ (k + 1) - 1) * (a (k + 1) : ZMod p) := by
      rw [h_succ_rhs]
      push_cast [h_le_rhs]
      rfl
    rw [h_cast_rhs]
    -- Now substitute the parts:
    rw [ih]
    rw [two_pow_choose_M_eq p (k + 1) hp hp2]
    have h_pow : (2 : ZMod p) ^ (k + 1 + 2 * (p - 1)) = (2 : ZMod p) ^ (k + 1) := by
      rw [pow_add, pow_M_eq_one p hp hp2, mul_one]
    rw [h_pow]

lemma mod_eq_iff_zmod_eq (p a b : ℕ) [NeZero p] : a % p = b % p ↔ (a : ZMod p) = (b : ZMod p) := by
  rw [← ZMod.val_natCast p a, ← ZMod.val_natCast p b]
  rw [(ZMod.val_injective p).eq_iff]

/--
Conjectures: 1) For prime p, the sequence taken modulo p is purely periodic with
minimum period dividing 2*(p - 1).
-/
theorem oeis_340881_conjecture_0 (p : ℕ) (hp : Nat.Prime p) :
  ∀ (n : ℕ), n ≥ 1 → a (n + 2 * (p - 1)) % p = a n % p := by
  intro n hn
  rcases hp.eq_two_or_odd' with rfl | hp_odd
  · -- Case p = 2
    have h_M : 2 * (2 - 1) = 2 := rfl
    rw [h_M]
    exact p_two_case n hn
  · -- Case p > 2 (odd prime)
    have hp2 : p > 2 := by
      rcases hp_odd with ⟨k, hk⟩
      have : p ≥ 2 := hp.two_le
      omega
    have : NeZero p := ⟨by omega⟩
    rw [mod_eq_iff_zmod_eq]
    exact general_case p hp hp2 n hn
