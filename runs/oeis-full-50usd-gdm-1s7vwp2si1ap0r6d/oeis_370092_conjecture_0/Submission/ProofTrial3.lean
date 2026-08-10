import FormalConjectures.Util.ProblemImports

open Finset Nat

lemma neg_one_pow_even (k : ℕ) : (-1 : ℤ)^(2 * k) = 1 := by
  rw [pow_mul]
  have h1 : (-1 : ℤ)^2 = 1 := by norm_num
  rw [h1, one_pow]

lemma neg_one_pow_odd (k : ℕ) : (-1 : ℤ)^(2 * k + 1) = -1 := by
  rw [pow_add, neg_one_pow_even]
  ring

lemma neg_two_pow_even (k : ℕ) : (-2 : ℤ)^(2 * k) = 2^(2 * k) := by
  rw [pow_mul, pow_mul]
  have h2 : (-2 : ℤ)^2 = 4 := by norm_num
  have h3 : (2 : ℤ)^2 = 4 := by norm_num
  rw [h2, h3]

lemma neg_two_pow_odd (k : ℕ) : (-2 : ℤ)^(2 * k + 1) = - 2^(2 * k + 1) := by
  rw [pow_add, neg_two_pow_even]
  ring

def C (j : ℕ) : ℤ :=
  if j % 2 = 0 then - (2 ^ (j - 1)) else 1 + 2 ^ (j - 1)

lemma C_spec (j : ℕ) (hj : 1 ≤ j) :
    2 * C j = 1 - (-1 : ℤ)^j - (-2 : ℤ)^j := by
  rw [C]
  split_ifs with h_mod
  · -- j is even
    have h_even : Even j := Nat.even_iff.mpr h_mod
    rcases h_even with ⟨k, rfl⟩
    have hk : k ≠ 0 := by omega
    rcases Nat.exists_eq_succ_of_ne_zero hk with ⟨k', rfl⟩
    have hj_eq : 2 * (k' + 1) = 2 * k' + 2 := by ring
    have hj_sub : 2 * (k' + 1) - 1 = 2 * k' + 1 := by omega
    have h_goal_rewrite : k'.succ + k'.succ = 2 * (k' + 1) := by omega
    rw [h_goal_rewrite]
    rw [hj_sub, hj_eq]
    have h_lhs : 2 * - (2 ^ (2 * k' + 1) : ℤ) = - 2 ^ (2 * k' + 2) := by
      rw [mul_neg]
      congr 1
      rw [mul_comm, ← pow_succ]
    rw [h_lhs]
    have h_even_1 : (-1 : ℤ)^(2 * k' + 2) = 1 := by
      have h_eq : 2 * k' + 2 = 2 * (k' + 1) := by ring
      rw [h_eq, neg_one_pow_even]
    have h_even_2 : (-2 : ℤ)^(2 * k' + 2) = 2^(2 * k' + 2) := by
      have h_eq : 2 * k' + 2 = 2 * (k' + 1) := by ring
      rw [h_eq, neg_two_pow_even]
    rw [h_even_1, h_even_2]
    ring
  · -- j is odd
    have h_odd_mod : j % 2 = 1 := by omega
    have h_odd : Odd j := Nat.odd_iff.mpr h_odd_mod
    rcases h_odd with ⟨k, rfl⟩
    have hj_sub : 2 * k + 1 - 1 = 2 * k := by omega
    rw [hj_sub]
    have h_lhs : 2 * (1 + 2 ^ (2 * k) : ℤ) = 2 + 2 ^ (2 * k + 1) := by
      rw [mul_add]
      congr 1
      rw [mul_comm, ← pow_succ]
    rw [h_lhs]
    rw [neg_one_pow_odd k, neg_two_pow_odd k]
    ring

noncomputable def a_int (n : ℕ) : ℤ :=
  match n with
  | 0 => 1
  | m + 1 =>
    let sum_val : ℤ := Finset.sum (Finset.range (m + 1)) (fun k =>
      let j := k + 1
      ((m + 1).choose j : ℤ) * C j * a_int (m + 1 - j)
    )
    (-1 : ℤ)^(m + 1) + sum_val

lemma a_int_recurrence (n : ℕ) (hn : n ≥ 1) :
    2 * a_int n = 2 * (-1 : ℤ)^n + Finset.sum (Finset.range n) (fun k =>
      let j := k + 1
      (n.choose j : ℤ) * (1 - (-1 : ℤ)^j - (-2 : ℤ)^j) * a_int (n - j)
    ) := by
  rcases n with _ | m
  · omega
  · rw [a_int]
    rw [mul_add]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    dsimp only
    have hj : k + 1 ≥ 1 := by omega
    have h_coeff : 2 * C (k + 1) = 1 - (-1 : ℤ)^(k + 1) - (-2 : ℤ)^(k + 1) := C_spec (k + 1) hj
    have hj_sub : m + 1 - (k + 1) = m - k := by omega
    rw [hj_sub]
    have h_ring : 2 * ( ((m + 1).choose (k + 1) : ℤ) * C (k + 1) * a_int (m - k) ) = ((m + 1).choose (k + 1) : ℤ) * (2 * C (k + 1)) * a_int (m - k) := by ring
    rw [h_ring, h_coeff]

noncomputable def a (n : ℕ) : ℚ :=
  match n with
  | 0 => 1
  | m_plus_one@(m + 1) =>
    let sum_val : ℚ := Finset.sum (Finset.range m_plus_one) (fun k =>
      let j : ℕ := k + 1
      let a_term : ℚ := a (m_plus_one - j)
      let coeff_factor : ℚ := 1 - (-1 : ℚ)^j - (-2 : ℚ)^j
      (m_plus_one.choose j : ℚ) * coeff_factor * a_term
    )
    (-1 : ℚ)^m_plus_one + (1 / 2) * sum_val

theorem a_eq_a_int (n : ℕ) : a n = (a_int n : ℚ) := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | m
  · rw [a, a_int]
    rfl
  · rw [a, a_int]
    push_cast
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hj : k + 1 ≥ 1 := by omega
    have h_coeff : 1 - (-1 : ℚ)^(k + 1) - (-2 : ℚ)^(k + 1) = 2 * (C (k + 1) : ℚ) := by
      have h_int : (((1 - (-1 : ℤ)^(k + 1) - (-2 : ℤ)^(k + 1) : ℤ) : ℚ)) = (((2 * C (k + 1) : ℤ) : ℚ)) := by
        congr 1
        rw [← C_spec (k + 1) hj]
      push_cast at h_int
      exact h_int
    rw [ih (m - k) (by omega)]
    rw [h_coeff]
    ring

lemma a_num_eq_a_int (n : ℕ) : (a n).num = a_int n := by
  rw [a_eq_a_int]
  exact Rat.num_intCast (a_int n)

def eventually_periodic {α : Type*} (f : ℕ → α) (P : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → f (n + P) = f n

noncomputable def a_mod_k (k : ℕ) (n : ℕ) : ZMod k :=
  Int.cast (a n).num

lemma a_mod_k_eq_a_int (k : ℕ) (n : ℕ) : a_mod_k k n = (a_int n : ZMod k) := by
  rw [a_mod_k, a_num_eq_a_int]

lemma pow_add_totient_eq (k : ℕ) (g : ZMod k) (n : ℕ) (hn : k ≤ n) :
    g ^ (n + totient k) = g ^ n := by
  sorry
