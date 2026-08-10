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
