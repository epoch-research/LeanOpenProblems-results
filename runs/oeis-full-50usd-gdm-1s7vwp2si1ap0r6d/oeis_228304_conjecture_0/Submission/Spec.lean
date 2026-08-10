import FormalConjectures.Util.ProblemImports

open Nat Finset Matrix

theorem test_odd (p : ℕ) [Fact p.Prime] (h_odd : p ≠ 2) : Odd p := by
  have hp : p.Prime := Fact.out
  rcases hp.eq_two_or_odd with h2 | h_p_odd
  · contradiction
  · rw [Nat.odd_iff]
    exact h_p_odd

theorem test_neg_one_pow (p : ℕ) [Fact p.Prime] (h_odd : p ≠ 2) :
    (-1 : ZMod p) ^ p = -1 := by
  have : Odd p := test_odd p h_odd
  exact Odd.neg_one_pow this

theorem choose_one_div_p (p k : ℕ) [Fact p.Prime] (hk : k < 2 * p) : choose 1 (k / p) = 1 := by
  have h_pos : p > 0 := (Fact.out : p.Prime).pos
  have h2 : k / p < 2 := by
    rwa [Nat.div_lt_iff_lt_mul h_pos]
  generalize hc : k / p = c at h2 ⊢
  have h_div : c = 0 ∨ c = 1 := by omega
  rcases h_div with h0 | h1
  · rw [h0, choose_zero_right]
  · rw [h1, choose_one_right]

theorem choose_p_add_r (p r k : ℕ) [Fact p.Prime] (hr : r < p) :
    (choose (p + r) k : ZMod p) = (choose r (k % p) : ZMod p) * (choose 1 (k / p) : ZMod p) := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div (n := p + r) (k := k) (p := p)
  rw [← ZMod.intCast_eq_intCast_iff] at h
  have h_pos : p > 0 := (Fact.out : p.Prime).pos
  have h_mod : (p + r) % p = r := by
    rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod_of_dvd _ dvd_rfl, Nat.mod_eq_of_lt hr]
  have h_div : (p + r) / p = 1 := by
    rw [Nat.add_div_of_dvd_right dvd_rfl, Nat.div_self h_pos, Nat.div_eq_of_lt hr, Nat.add_zero]
  rw [h_mod, h_div] at h
  push_cast at h
  exact h

theorem choose_p_add_r_eq (p r k : ℕ) [Fact p.Prime] (hr : r < p) (hk : k < 2 * p) :
    (choose (p + r) k : ZMod p) = (choose r (k % p) : ZMod p) := by
  rw [choose_p_add_r p r k hr]
  have h1 : choose 1 (k / p) = 1 := choose_one_div_p p k hk
  rw [h1]
  push_cast
  rw [mul_one]


theorem central_binom_p_add (p k : ℕ) [Fact p.Prime] (hk : k < p) :
    (choose (2 * (p + k)) (p + k) : ZMod p) = 2 * (choose (2 * k) k : ZMod p) := by
  have h_pos : p > 0 := (Fact.out : p.Prime).pos
  have h_rw : 2 * (p + k) = 2 * p + 2 * k := by ring
  rw [h_rw]
  by_cases h_lt : 2 * k < p
  · -- Case 1: 2 * k < p
    have h_mod1 : (2 * p + 2 * k) % p = 2 * k := by
      rw [Nat.add_mod]
      simp
      rw [Nat.mod_eq_of_lt h_lt]
    have h_div1 : (2 * p + 2 * k) / p = 2 := by
      have : 2 * p + 2 * k = 2 * k + p * 2 := by ring
      rw [this, Nat.add_mul_div_left _ _ h_pos]
      have : 2 * k / p = 0 := Nat.div_eq_of_lt h_lt
      rw [this, Nat.zero_add]
    have h_mod2 : (p + k) % p = k := by
      rw [Nat.add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt hk]
    have h_div2 : (p + k) / p = 1 := by
      rw [Nat.add_comm, Nat.add_div_right k h_pos]
      have : k / p = 0 := Nat.div_eq_of_lt hk
      rw [this]
    have h := Choose.choose_modEq_choose_mod_mul_choose_div (n := 2 * p + 2 * k) (k := p + k) (p := p)
    rw [← ZMod.intCast_eq_intCast_iff] at h
    rw [h_mod1, h_div1, h_mod2, h_div2] at h
    have h_choose_two : (choose 2 1 : ZMod p) = 2 := by rfl
    push_cast at h
    rw [h_choose_two] at h
    rw [h]
    ring
  · -- Case 2: 2 * k ≥ p
    have h_ge : 2 * k ≥ p := by omega
    have h_s : ∃ s, 2 * k = p + s ∧ s < k := by
      use 2 * k - p
      constructor <;> omega
    rcases h_s with ⟨s, hs1, hs2⟩
    -- LHS is 0
    have h_LHS : (choose (2 * p + 2 * k) (p + k) : ZMod p) = 0 := by
      have h := Choose.choose_modEq_choose_mod_mul_choose_div (n := 2 * p + 2 * k) (k := p + k) (p := p)
      rw [← ZMod.intCast_eq_intCast_iff] at h
      have h_mod1 : (2 * p + 2 * k) % p = s := by
        have : 2 * p + 2 * k = 2 * k + p * 2 := by ring
        rw [this, Nat.add_mul_mod_self_left _ _ 2, hs1, Nat.add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have h_mod2 : (p + k) % p = k := by
        rw [Nat.add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt hk]
      rw [h_mod1, h_mod2] at h
      have h_choose : choose s k = 0 := choose_eq_zero_of_lt hs2
      rw [h_choose] at h
      push_cast at h
      rw [zero_mul] at h
      exact h
    -- RHS is 0
    have h_RHS : (choose (2 * k) k : ZMod p) = 0 := by
      have h := Choose.choose_modEq_choose_mod_mul_choose_div (n := 2 * k) (k := k) (p := p)
      rw [← ZMod.intCast_eq_intCast_iff] at h
      have h_mod1 : (2 * k) % p = s := by
        rw [hs1, Nat.add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have h_mod2 : k % p = k := Nat.mod_eq_of_lt hk
      rw [h_mod1, h_mod2] at h
      have h_choose : choose s k = 0 := choose_eq_zero_of_lt hs2
      rw [h_choose] at h
      push_cast at h
      rw [zero_mul] at h
      exact h
    rw [h_LHS, h_RHS, mul_zero]





def a (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k => ((-1 : ℤ) ^ k) * ((choose n k : ℤ) ^ 4)

theorem a_split (p n : ℕ) (hp : p ≤ n) :
    a n = (∑ k ∈ range p, ((-1 : ℤ) ^ k) * ((choose n k : ℤ) ^ 4)) +
          (∑ k ∈ Ico p (n + 1), ((-1 : ℤ) ^ k) * ((choose n k : ℤ) ^ 4)) := by
  have h_le : p ≤ n + 1 := by omega
  unfold a
  rw [← Finset.sum_range_add_sum_Ico _ h_le]

theorem a_zmod_eq_zero (p : ℕ) [Fact p.Prime] (h_odd : p ≠ 2) (r : ℕ) (hr : r < p - 1) :
    (a (p + r) : ZMod p) = 0 := by
  have hp_le : p ≤ p + r := by omega
  have h_split := a_split p (p + r) hp_le
  have h_cast := congr_arg (fun x : ℤ => (x : ZMod p)) h_split
  push_cast at h_cast
  rw [h_cast]
  -- Now simplify S1 (sum over range p)
  have h_S1 : ∑ k ∈ range p, (-1 : ZMod p) ^ k * (choose (p + r) k : ZMod p) ^ 4 =
              ∑ k ∈ range (r + 1), (-1 : ZMod p) ^ k * (choose r k : ZMod p) ^ 4 := by
    -- Step 1: Replace (choose (p + r) k : ZMod p) with (choose r k : ZMod p)
    have h_eq : ∀ k ∈ range p, (-1 : ZMod p) ^ k * (choose (p + r) k : ZMod p) ^ 4 =
                               (-1 : ZMod p) ^ k * (choose r k : ZMod p) ^ 4 := by
      intro k hk
      rw [mem_range] at hk
      have hk2 : k < 2 * p := by omega
      have h_choose := choose_p_add_r_eq p r k (by omega) hk2
      have hk_mod : k % p = k := Nat.mod_eq_of_lt hk
      rw [h_choose, hk_mod]
    have h_sum1 := sum_congr rfl h_eq
    rw [h_sum1]
    -- Step 2: Split range p into range (r + 1) and Ico (r + 1) p
    have hr_le : r + 1 ≤ p := by omega
    rw [← sum_range_add_sum_Ico _ hr_le]
    have h_zero : ∑ k ∈ Ico (r + 1) p, (-1 : ZMod p) ^ k * (choose r k : ZMod p) ^ 4 = 0 := by
      apply sum_eq_zero
      intro k hk
      rw [mem_Ico] at hk
      have hk_choose : choose r k = 0 := choose_eq_zero_of_lt hk.left
      rw [hk_choose]
      simp
    rw [h_zero, add_zero]
  -- Now simplify S2 (sum over Ico p (p + r + 1))
  have h_S2 : ∑ k ∈ Ico p (p + r + 1), (-1 : ZMod p) ^ k * (choose (p + r) k : ZMod p) ^ 4 =
              - ∑ k ∈ range (r + 1), (-1 : ZMod p) ^ k * (choose r k : ZMod p) ^ 4 := by
    -- Use sum_Ico_add' with a = 0, b = r + 1, c = p
    have h_Ico := sum_Ico_add' (fun k => (-1 : ZMod p) ^ k * (choose (p + r) k : ZMod p) ^ 4) 0 (r + 1) p
    simp only [zero_add] at h_Ico
    have h_add : r + 1 + p = p + r + 1 := by omega
    rw [h_add] at h_Ico
    rw [← h_Ico]
    -- Now simplify each term inside the sum over range (r + 1)
    have h_eq2 : ∀ k ∈ range (r + 1),
        (-1 : ZMod p) ^ (k + p) * (choose (p + r) (k + p) : ZMod p) ^ 4 =
        - ((-1 : ZMod p) ^ k * (choose r k : ZMod p) ^ 4) := by
      intro k hk
      rw [mem_range] at hk
      have hk_lt : k < p := by omega
      have hk_lt2 : k + p < 2 * p := by omega
      have h_choose2 := choose_p_add_r_eq p r (k + p) (by omega) hk_lt2
      have hk_mod2 : (k + p) % p = k := by
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt hk_lt]
      rw [h_choose2, hk_mod2]
      -- Simplify sign
      rw [pow_add, test_neg_one_pow p h_odd]
      ring
    have h_sum2 := sum_congr rfl h_eq2
    rw [range_eq_Ico] at h_sum2
    rw [h_sum2, ← sum_neg_distrib]
    rw [range_eq_Ico]


  rw [h_S1, h_S2]
  ring

def c (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k =>
    ((-1 : ℤ) ^ k) * ((choose n k : ℤ) ^ 2) * (choose (2 * k) k : ℤ) * (choose (2 * (n - k)) (n - k) : ℤ)

theorem c_split (p n : ℕ) (hp : p ≤ n) :
    c n = (∑ k ∈ range p, ((-1 : ℤ) ^ k) * ((choose n k : ℤ) ^ 2) * (choose (2 * k) k : ℤ) * (choose (2 * (n - k)) (n - k) : ℤ)) +
          (∑ k ∈ Ico p (n + 1), ((-1 : ℤ) ^ k) * ((choose n k : ℤ) ^ 2) * (choose (2 * k) k : ℤ) * (choose (2 * (n - k)) (n - k) : ℤ)) := by
  have h_le : p ≤ n + 1 := by omega
  unfold c
  rw [← Finset.sum_range_add_sum_Ico _ h_le]

theorem c_zmod_eq_zero (p : ℕ) [Fact p.Prime] (h_odd : p ≠ 2) (r : ℕ) (hr : r < p - 1) :
    (c (p + r) : ZMod p) = 0 := by
  have hp_le : p ≤ p + r := by omega
  have h_split := c_split p (p + r) hp_le
  have h_cast := congr_arg (fun x : ℤ => (x : ZMod p)) h_split
  push_cast at h_cast
  rw [h_cast]
  -- Now simplify S1 (sum over range p)
  have h_S1 : ∑ k ∈ range p, (-1 : ZMod p) ^ k * (choose (p + r) k : ZMod p) ^ 2 * (choose (2 * k) k : ZMod p) * (choose (2 * (p + r - k)) (p + r - k) : ZMod p) =
              2 * ∑ k ∈ range (r + 1), (-1 : ZMod p) ^ k * (choose r k : ZMod p) ^ 2 * (choose (2 * k) k : ZMod p) * (choose (2 * (r - k)) (r - k) : ZMod p) := by
    have h_eq : ∀ k ∈ range p,
        (-1 : ZMod p) ^ k * (choose (p + r) k : ZMod p) ^ 2 * (choose (2 * k) k : ZMod p) * (choose (2 * (p + r - k)) (p + r - k) : ZMod p) =
        if k ≤ r then
          2 * ((-1 : ZMod p) ^ k * (choose r k : ZMod p) ^ 2 * (choose (2 * k) k : ZMod p) * (choose (2 * (r - k)) (r - k) : ZMod p))
        else 0 := by
      intro k hk
      rw [mem_range] at hk
      by_cases hk_le : k ≤ r
      · rw [if_pos hk_le]
        have hk2 : k < 2 * p := by omega
        have h_choose := choose_p_add_r_eq p r k (by omega) hk2
        have hk_mod : k % p = k := Nat.mod_eq_of_lt hk
        rw [h_choose, hk_mod]
        have h_sub : p + r - k = p + (r - k) := by omega
        rw [h_sub]
        have h_cb := central_binom_p_add p (r - k) (by omega)
        rw [h_cb]
        ring
      · rw [if_neg hk_le]
        have hk2 : k < 2 * p := by omega
        have h_choose := choose_p_add_r_eq p r k (by omega) hk2
        have hk_mod : k % p = k := Nat.mod_eq_of_lt hk
        rw [h_choose, hk_mod]
        have h_zero : choose r k = 0 := choose_eq_zero_of_lt (by omega)
        rw [h_zero]
        simp
    have h_sum1 := sum_congr rfl h_eq
    rw [h_sum1]
    -- Split range p into range (r + 1) and Ico (r + 1) p
    have hr_le : r + 1 ≤ p := by omega
    rw [← sum_range_add_sum_Ico _ hr_le]
    have h_zero : ∑ k ∈ Ico (r + 1) p, (if k ≤ r then 2 * ((-1 : ZMod p) ^ k * (choose r k : ZMod p) ^ 2 * (choose (2 * k) k : ZMod p) * (choose (2 * (r - k)) (r - k) : ZMod p)) else 0) = 0 := by
      apply sum_eq_zero
      intro k hk
      rw [mem_Ico] at hk
      have hk_not : ¬ k ≤ r := by omega
      rw [if_neg hk_not]
    rw [h_zero, add_zero]
    have h_id : ∑ k ∈ range (r + 1), (if k ≤ r then 2 * ((-1 : ZMod p) ^ k * (choose r k : ZMod p) ^ 2 * (choose (2 * k) k : ZMod p) * (choose (2 * (r - k)) (r - k) : ZMod p)) else 0) =
                ∑ k ∈ range (r + 1), 2 * ((-1 : ZMod p) ^ k * (choose r k : ZMod p) ^ 2 * (choose (2 * k) k : ZMod p) * (choose (2 * (r - k)) (r - k) : ZMod p)) := by
      apply sum_congr rfl
      intro k hk
      rw [mem_range] at hk
      have hk_le : k ≤ r := by omega
      rw [if_pos hk_le]
    rw [h_id, ← mul_sum]

  -- Now simplify S2 (sum over Ico p (p + r + 1))
  have h_S2 : ∑ k ∈ Ico p (p + r + 1), (-1 : ZMod p) ^ k * (choose (p + r) k : ZMod p) ^ 2 * (choose (2 * k) k : ZMod p) * (choose (2 * (p + r - k)) (p + r - k) : ZMod p) =
              - (2 * ∑ k ∈ range (r + 1), (-1 : ZMod p) ^ k * (choose r k : ZMod p) ^ 2 * (choose (2 * k) k : ZMod p) * (choose (2 * (r - k)) (r - k) : ZMod p)) := by
    have h_Ico := sum_Ico_add' (fun k => (-1 : ZMod p) ^ k * (choose (p + r) k : ZMod p) ^ 2 * (choose (2 * k) k : ZMod p) * (choose (2 * (p + r - k)) (p + r - k) : ZMod p)) 0 (r + 1) p
    simp only [zero_add] at h_Ico
    have h_add : r + 1 + p = p + r + 1 := by omega
    rw [h_add] at h_Ico
    rw [← h_Ico]
    have h_eq2 : ∀ k ∈ range (r + 1),
        (-1 : ZMod p) ^ (k + p) * (choose (p + r) (k + p) : ZMod p) ^ 2 * (choose (2 * (k + p)) (k + p) : ZMod p) * (choose (2 * (p + r - (k + p))) (p + r - (k + p)) : ZMod p) =
        - (2 * ((-1 : ZMod p) ^ k * (choose r k : ZMod p) ^ 2 * (choose (2 * k) k : ZMod p) * (choose (2 * (r - k)) (r - k) : ZMod p))) := by
      intro k hk
      rw [mem_range] at hk
      have hk_lt : k < p := by omega
      have hk_lt2 : k + p < 2 * p := by omega
      have h_choose2 := choose_p_add_r_eq p r (k + p) (by omega) hk_lt2
      have hk_mod2 : (k + p) % p = k := by
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt hk_lt]
      rw [h_choose2, hk_mod2]
      have h_cb2 : (choose (2 * (k + p)) (k + p) : ZMod p) = 2 * (choose (2 * k) k : ZMod p) := by
        have : 2 * (k + p) = 2 * (p + k) := by ring
        rw [this, Nat.add_comm k p]
        exact central_binom_p_add p k (by omega)
      rw [h_cb2]
      have h_sub2 : p + r - (k + p) = r - k := by omega
      rw [h_sub2]
      -- Simplify sign
      rw [pow_add, test_neg_one_pow p h_odd]
      ring
    have h_sum2 := sum_congr rfl h_eq2
    rw [range_eq_Ico] at h_sum2
    rw [h_sum2]
    simp only [sum_neg_distrib, mul_sum, range_eq_Ico]

  rw [h_S1, h_S2]
  ring


theorem choose_pred_eq_neg_one_pow (p k : ℕ) [Fact p.Prime] (hk : k < p) :
    (choose (p - 1) k : ZMod p) = (-1) ^ k := by
  induction' k with k ih
  · rw [choose_zero_right, pow_zero, cast_one]
  · have hk_lt : k < p - 1 := by omega
    have h_id := choose_succ_right_eq (p - 1) k
    have h_cast := congr_arg (fun x : ℕ => (x : ZMod p)) h_id
    push_cast at h_cast
    have h_pred : ((p - 1 - k : ℕ) : ZMod p) = - (k + 1 : ZMod p) := by
      have h_sub : p - 1 - k = p - (k + 1) := by omega
      rw [h_sub]
      rw [Nat.cast_sub (by omega)]
      push_cast
      simp
    rw [h_pred] at h_cast
    have ih_val : (choose (p - 1) k : ZMod p) = (-1) ^ k := ih (by omega)
    rw [ih_val] at h_cast
    have h_rhs : (-1 : ZMod p) ^ k * -(k + 1 : ZMod p) = (-1 : ZMod p) ^ (k + 1) * (k + 1 : ZMod p) := by
      rw [pow_succ]
      ring
    rw [h_rhs] at h_cast
    have hk_nz : (k + 1 : ZMod p) ≠ 0 := by
      intro h_zero
      have h_zero' : ((k + 1 : ℕ) : ZMod p) = 0 := by
        push_cast
        exact h_zero
      rw [CharP.cast_eq_zero_iff (ZMod p) p] at h_zero'
      have h_lt_p : k + 1 < p := by omega
      have : k + 1 > 0 := by omega
      have : p ≤ k + 1 := Nat.le_of_dvd this h_zero'
      omega
    exact mul_right_cancel₀ hk_nz h_cast

theorem sum_neg_one_pow_range (p : ℕ) [Fact p.Prime] (h_odd : p ≠ 2) :
    (∑ i ∈ range p, (-1 : ZMod p) ^ i) = 1 := by
  have h_univ := (Fin.sum_univ_eq_sum_range (fun i => (-1 : ZMod p) ^ i) p).symm
  rw [h_univ]
  rw [Fin.sum_neg_one_pow]
  have hp_odd : Odd p := test_odd p h_odd
  have hp_not_even : ¬ Even p := Nat.not_even_iff_odd.mpr hp_odd
  rw [if_neg hp_not_even]

theorem a_pred_zmod_eq_one (p : ℕ) [Fact p.Prime] (h_odd : p ≠ 2) :
    (a (p - 1) : ZMod p) = 1 := by
  have h_p : p - 1 + 1 = p := Nat.sub_add_cancel (Fact.out : p.Prime).pos
  unfold a
  rw [h_p]
  push_cast
  have h_eq : ∀ k ∈ range p, (-1 : ZMod p) ^ k * (choose (p - 1) k : ZMod p) ^ 4 = (-1 : ZMod p) ^ k := by
    intro k hk
    rw [mem_range] at hk
    rw [choose_pred_eq_neg_one_pow p k hk]
    have h4 : ((-1 : ZMod p) ^ k) ^ 4 = 1 := by
      rw [← pow_mul]
      have : k * 4 = 2 * (2 * k) := by ring
      rw [this, pow_mul]
      have : (-1 : ZMod p) ^ 2 = 1 := by ring
      rw [this, one_pow]
    rw [h4, mul_one]
  have h_sum := sum_congr rfl h_eq
  rw [h_sum]
  exact sum_neg_one_pow_range p h_odd


theorem central_binom_eq_zero_of_ge (p k : ℕ) [Fact p.Prime] (hk : k < p) (hge : 2 * k ≥ p) :
    (choose (2 * k) k : ZMod p) = 0 := by
  have h_s : ∃ s, 2 * k = p + s ∧ s < k := by
    use 2 * k - p
    constructor <;> omega
  rcases h_s with ⟨s, hs1, hs2⟩
  have h := Choose.choose_modEq_choose_mod_mul_choose_div (n := 2 * k) (k := k) (p := p)
  rw [← ZMod.intCast_eq_intCast_iff] at h
  have h_mod1 : (2 * k) % p = s := by
    rw [hs1, Nat.add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have h_mod2 : k % p = k := Nat.mod_eq_of_lt hk
  rw [h_mod1, h_mod2] at h
  have h_choose : choose s k = 0 := choose_eq_zero_of_lt hs2
  rw [h_choose] at h
  push_cast at h
  rw [zero_mul] at h
  exact h

theorem c_pred_zmod_eq_neg_one_pow (p : ℕ) [Fact p.Prime] (h_odd : p ≠ 2) :
    (c (p - 1) : ZMod p) = (-1) ^ ((p - 1) / 2) := by
  have hp_odd : Odd p := test_odd p h_odd
  rcases hp_odd with ⟨m, hm_eq⟩
  have h_p : p = 2 * m + 1 := hm_eq
  have hp_pos : p > 0 := by omega
  have h_p_sub_one : p - 1 = 2 * m := by omega
  have h_half : (p - 1) / 2 = m := by
    rw [h_p_sub_one]
    exact Nat.mul_div_cancel_left m (by decide)
  rw [h_half]
  unfold c
  have h_p_cancel : p - 1 + 1 = p := by omega
  rw [h_p_cancel]
  push_cast
  have h_sum : ∑ k ∈ range p, (-1 : ZMod p) ^ k * (choose (p - 1) k : ZMod p) ^ 2 * (choose (2 * k) k : ZMod p) * (choose (2 * (p - 1 - k)) (p - 1 - k) : ZMod p) =
               (-1 : ZMod p) ^ m * (choose (p - 1) m : ZMod p) ^ 2 * (choose (2 * m) m : ZMod p) * (choose (2 * (p - 1 - m)) (p - 1 - m) : ZMod p) := by
    apply sum_eq_single m
    · intro k hk hk_ne
      rw [mem_range] at hk
      by_cases hk_lt : k < m
      · have h_ge : 2 * (p - 1 - k) ≥ p := by omega
        have h_zero : (choose (2 * (p - 1 - k)) (p - 1 - k) : ZMod p) = 0 := by
          apply central_binom_eq_zero_of_ge
          · omega
          · omega
        rw [h_zero]
        ring
      · have h_ge : 2 * k ≥ p := by omega
        have h_zero : (choose (2 * k) k : ZMod p) = 0 := by
          apply central_binom_eq_zero_of_ge
          · omega
          · omega
        rw [h_zero]
        ring
    · intro hm
      exfalso
      rw [mem_range] at hm
      omega
  rw [h_sum]
  have hm_lt : m < p := by omega
  have h_choose_m : (choose (p - 1) m : ZMod p) = (-1) ^ m := choose_pred_eq_neg_one_pow p m hm_lt
  rw [h_choose_m]
  have h_sq : ((-1 : ZMod p) ^ m) ^ 2 = 1 := by
    rw [← pow_mul]
    have : m * 2 = 2 * m := by ring
    rw [this]
    have : (-1 : ZMod p) ^ 2 = 1 := by ring
    rw [pow_mul, this, one_pow]
  rw [h_sq, mul_one]
  have h_sub_m : p - 1 - m = m := by omega
  rw [h_sub_m]
  have h_choose_2m : (choose (2 * m) m : ZMod p) = (-1) ^ m := by
    rw [← h_p_sub_one]
    exact h_choose_m
  rw [h_choose_2m]
  have h_final : (-1 : ZMod p) ^ m * (-1 : ZMod p) ^ m * (-1 : ZMod p) ^ m = (-1 : ZMod p) ^ m := by
    rw [← pow_add, ← pow_add]
    have : m + m + m = 2 * m + m := by ring
    rw [this, pow_add]
    have h_sq2 : (-1 : ZMod p) ^ (2 * m) = 1 := by
      rw [pow_mul]
      have h2 : (-1 : ZMod p) ^ 2 = 1 := by ring
      rw [h2, one_pow]
    rw [h_sq2, one_mul]
  exact h_final



theorem eq_revPerm_of_add_lt (p : ℕ) (hp : p > 0) (σ : Equiv.Perm (Fin p)) (h : ∀ i : Fin p, i.val + (σ i).val < p) :
    σ = Fin.revPerm := by
  have h_le : ∀ i : Fin p, i.val + (σ i).val ≤ p - 1 := by
    intro i
    have := h i
    omega
  have h_sum : ∑ i : Fin p, ((p - 1 : ℤ) - (i.val + (σ i).val : ℤ)) = 0 := by
    rw [sum_sub_distrib]
    rw [sum_add_distrib]
    have h_const : ∑ i : Fin p, (p - 1 : ℤ) = p * (p - 1 : ℤ) := by
      simp
      ring
    have h_equiv : ∑ i : Fin p, ((σ i).val : ℤ) = ∑ i : Fin p, (i.val : ℤ) := by
      exact Fintype.sum_equiv σ _ _ (fun x => rfl)
    rw [h_equiv]
    have h_double : (∑ i : Fin p, (i.val : ℤ)) + (∑ i : Fin p, (i.val : ℤ)) = 2 * (∑ i : Fin p, (i.val : ℤ)) := by ring
    rw [h_double, h_const]
    have h_sum_val : 2 * ∑ i : Fin p, (i.val : ℤ) = p * (p - 1 : ℤ) := by
      have h_range : ∑ i : Fin p, i.val = ∑ i ∈ range p, i := Fin.sum_univ_eq_sum_range (fun i => i) p
      have h_nat : (∑ i ∈ range p, i) * 2 = p * (p - 1) := Finset.sum_range_id_mul_two p
      have h_nat2 : 2 * ∑ i : Fin p, i.val = p * (p - 1) := by
        rw [h_range, mul_comm, h_nat]
      have h_nat2_cast := congr_arg (fun x : ℕ => (x : ℤ)) h_nat2
      push_cast at h_nat2_cast
      have : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
      rw [this] at h_nat2_cast
      exact h_nat2_cast
    rw [h_sum_val]
    ring
  have h_all_zero : ∀ i : Fin p, (p - 1 : ℤ) - (i.val + (σ i).val : ℤ) = 0 := by
    have h_mem := (sum_eq_zero_iff_of_nonneg (by intro i _; have := h_le i; omega)).mp h_sum
    intro i
    exact h_mem i (mem_univ i)
  have h_eq : ∀ i : Fin p, σ i = Fin.revPerm i := by
    intro i
    have hz := h_all_zero i
    have h_val : (σ i).val = p - 1 - i.val := by omega
    have h_rev : (Fin.revPerm i).val = p - (i.val + 1) := rfl
    apply Fin.ext
    omega
  exact Equiv.ext h_eq


theorem blockTriangular_of_anti_triangular [CommRing R] (p : ℕ) (M : Matrix (Fin p) (Fin p) R)
    (hM : ∀ i j : Fin p, p - 1 < i.val + j.val → M i j = 0) :
    BlockTriangular (M.submatrix id Fin.revPerm) id := by
  intro i j hij
  simp only [id_eq] at hij
  simp only [submatrix_apply, id_eq]
  apply hM
  have h_rev : (Fin.revPerm j).val = p - (j.val + 1) := rfl
  rw [h_rev]
  have h_j : j.val < p := j.is_lt
  have h_i : i.val < p := i.is_lt
  omega


theorem det_of_anti_triangular [CommRing R] (p : ℕ) (M : Matrix (Fin p) (Fin p) R)
    (hM : ∀ i j : Fin p, p - 1 < i.val + j.val → M i j = 0) :
    det M = Equiv.Perm.sign (@Fin.revPerm p) * ∏ i : Fin p, M i (Fin.revPerm i) := by
  have h_tri := blockTriangular_of_anti_triangular p M hM
  have h_det := det_of_upperTriangular h_tri
  have h_perm := det_permute' (@Fin.revPerm p) M
  rw [h_perm] at h_det
  have h_mul : (Equiv.Perm.sign (@Fin.revPerm p) : R) * (Equiv.Perm.sign (@Fin.revPerm p) * det M) =
               (Equiv.Perm.sign (@Fin.revPerm p) : R) * ∏ i : Fin p, (M.submatrix id Fin.revPerm) i i := by
    rw [h_det]
  have h_sq : (Equiv.Perm.sign (@Fin.revPerm p) : R) * (Equiv.Perm.sign (@Fin.revPerm p) : R) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (@Fin.revPerm p)) with h1 | h2
    · rw [h1]; simp
    · rw [h2]; simp
  rw [← mul_assoc, h_sq, one_mul] at h_mul
  have h_diag : (∏ i : Fin p, (M.submatrix id Fin.revPerm) i i) = (∏ i : Fin p, M i (Fin.revPerm i)) := by
    apply prod_congr rfl
    intro i _
    rfl
  rw [h_diag] at h_mul
  exact h_mul



theorem test_omega_succ (m : ℕ) : (m + 3) * (m + 2) / 2 = (m + 1) * m / 2 + (2 * m + 3) := by
  have h_eq : (m + 3) * (m + 2) = (m + 1) * m + 2 * (2 * m + 3) := by ring
  rw [h_eq]
  rw [Nat.add_mul_div_left ((m + 1) * m) (2 * m + 3) (by decide)]

theorem test_omega (k : ℕ) : (k + 2) * (k + 1) / 2 = k * (k - 1) / 2 + (2 * k + 1) := by
  rcases k with _ | m
  · rfl
  · exact test_omega_succ m



def fin_equiv (n : ℕ) : Fin n ≃ { i : Fin (n + 2) // i ≠ (0 : Fin (n + 2)) ∧ i ≠ (⟨n + 1, by omega⟩ : Fin (n + 2)) } where
  toFun i := ⟨⟨i.val + 1, by omega⟩, by
    constructor
    · intro h1
      have : i.val + 1 = 0 := by injection h1
      omega
    · intro h2
      have : i.val + 1 = n + 1 := by injection h2
      have : i.val = n := by omega
      have := i.is_lt
      omega⟩
  invFun i := ⟨i.val.val - 1, by
    have h_zero : i.val.val ≠ 0 := by
      intro h
      have : i.val = 0 := by ext; exact h
      exact i.property.left this
    have h_last : i.val.val ≠ n + 1 := by
      intro h
      have : i.val = ⟨n + 1, by omega⟩ := by ext; exact h
      exact i.property.right this
    have h_lt : i.val.val < n + 2 := i.val.is_lt
    omega⟩
  left_inv i := by
    ext
    simp
  right_inv i := by
    ext
    have h_zero : i.val.val ≠ 0 := by
      intro h
      have : i.val = 0 := by ext; exact h
      exact i.property.left this
    simp
    omega


theorem revPerm_decomposition (n : ℕ) :
    (Fin.revPerm : Equiv.Perm (Fin (n + 2))) =
    Equiv.swap (0 : Fin (n + 2)) ⟨n + 1, by omega⟩ * Equiv.Perm.extendDomain (Fin.revPerm : Equiv.Perm (Fin n)) (fin_equiv n) := by
  ext i
  by_cases h0 : i = 0
  · rw [h0]
    simp
    have h_not_p : ¬ (0 ≠ (0 : Fin (n + 2)) ∧ (0 : Fin (n + 2)) ≠ ⟨n + 1, by omega⟩) := by simp
    rw [Equiv.Perm.extendDomain_apply_not_subtype (Fin.revPerm : Equiv.Perm (Fin n)) (fin_equiv n) h_not_p]
    simp
  · by_cases h_last : i = ⟨n + 1, by omega⟩
    · rw [h_last]
      simp
      have h_not_p : ¬ (⟨n + 1, by omega⟩ ≠ (0 : Fin (n + 2)) ∧ ⟨n + 1, by omega⟩ ≠ (⟨n + 1, by omega⟩ : Fin (n + 2))) := by simp
      rw [Equiv.Perm.extendDomain_apply_not_subtype (Fin.revPerm : Equiv.Perm (Fin n)) (fin_equiv n) h_not_p]
      simp
    · have h_prop : i ≠ 0 ∧ i ≠ ⟨n + 1, by omega⟩ := ⟨h0, h_last⟩
      set x : { i : Fin (n + 2) // i ≠ 0 ∧ i ≠ ⟨n + 1, by omega⟩ } := ⟨i, h_prop⟩
      have h_eq : i = x.val := rfl
      rw [h_eq]
      rw [Equiv.Perm.mul_apply]
      rw [Equiv.Perm.extendDomain_apply_subtype (Fin.revPerm : Equiv.Perm (Fin n)) (fin_equiv n) h_prop]
      simp
      have h_symm : ((fin_equiv n).symm x).val = i.val - 1 := rfl
      have h_rev : ((fin_equiv n).symm x).rev.val = n - i.val := by
        have : ((fin_equiv n).symm x).rev.val = n - (((fin_equiv n).symm x).val + 1) := rfl
        have h_left : i.val ≠ 0 := by
          intro h
          have : i = 0 := by ext; exact h
          exact h_prop.left this
        have h_right : i.val ≠ n + 1 := by
          intro h
          have : i = ⟨n + 1, by omega⟩ := by ext; exact h
          exact h_prop.right this
        omega
      have h_fe : (fin_equiv n ((fin_equiv n).symm x).rev).val.val = n - i.val + 1 := by
        change ((fin_equiv n).symm x).rev.val + 1 = n - i.val + 1
        rw [h_rev]
      have h_swap : Equiv.swap (0 : Fin (n + 2)) ⟨n + 1, by omega⟩ (fin_equiv n ((fin_equiv n).symm x).rev) = (fin_equiv n ((fin_equiv n).symm x).rev) := by
        rw [Equiv.swap_apply_of_ne_of_ne]
        · intro h
          have : (fin_equiv n ((fin_equiv n).symm x).rev).val.val = 0 := by rw [h]; rfl
          omega
        · intro h
          have : (fin_equiv n ((fin_equiv n).symm x).rev).val.val = n + 1 := by rw [h]
          omega
      rw [h_swap]
      rw [h_fe]
      omega


theorem sign_revPerm (n : ℕ) : Equiv.Perm.sign (@Fin.revPerm n) = (-1 : ℤˣ) ^ (n * (n - 1) / 2) := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | k
  · rfl
  · rfl
  · rw [revPerm_decomposition k]
    rw [map_mul]
    rw [Equiv.Perm.sign_swap (by simp)]
    have h_ext := Equiv.Perm.sign_extendDomain (Fin.revPerm : Equiv.Perm (Fin k)) (fin_equiv k)
    rw [h_ext]
    have ih1 := ih k (by omega)
    rw [ih1]
    rw [mul_comm, ← pow_succ]
    change (-1 : ℤˣ) ^ (k * (k - 1) / 2 + 1) = (-1 : ℤˣ) ^ ((k + 2) * (k + 1) / 2)
    have h_exp := test_omega k
    rw [h_exp]
    have h_pow_eq : ∀ (A : ℕ), (-1 : ℤˣ) ^ (A + (2 * k + 1)) = (-1 : ℤˣ) ^ (A + 1) := by
      intro A
      have : A + (2 * k + 1) = A + 1 + 2 * k := by omega
      rw [this, pow_add, pow_mul]
      have : (-1 : ℤˣ) ^ 2 = 1 := by decide
      rw [this, one_pow, mul_one]
    exact (h_pow_eq (k * (k - 1) / 2)).symm



theorem a_anti_triangular_cond (p : ℕ) [Fact p.Prime] (h_odd : p ≠ 2) (i j : Fin p) (h : p - 1 < i.val + j.val) :
    (a (i.val + j.val) : ZMod p) = 0 := by
  have h_sum : i.val + j.val = p + (i.val + j.val - p) := by omega
  rw [h_sum]
  apply a_zmod_eq_zero p h_odd (i.val + j.val - p)
  have h_i : i.val < p := i.is_lt
  have h_j : j.val < p := j.is_lt
  omega

theorem c_anti_triangular_cond (p : ℕ) [Fact p.Prime] (h_odd : p ≠ 2) (i j : Fin p) (h : p - 1 < i.val + j.val) :
    (c (i.val + j.val) : ZMod p) = 0 := by
  have h_sum : i.val + j.val = p + (i.val + j.val - p) := by omega
  rw [h_sum]
  apply c_zmod_eq_zero p h_odd (i.val + j.val - p)
  have h_i : i.val < p := i.is_lt
  have h_j : j.val < p := j.is_lt
  omega

theorem neg_one_pow_p_mul (p : ℕ) [Fact p.Prime] (h_odd : p ≠ 2) :
    (-1 : ZMod p) ^ (p * (p - 1) / 2) = (-1 : ZMod p) ^ ((p - 1) / 2) := by
  have hp_odd : Odd p := test_odd p h_odd
  rcases hp_odd with ⟨m, hm⟩
  have hp_sub_one : p - 1 = 2 * m := by omega
  have h_half1 : (p - 1) / 2 = m := by
    rw [hp_sub_one]
    exact Nat.mul_div_cancel_left m (by decide)
  have h_half2 : p * (p - 1) / 2 = p * m := by
    rw [hp_sub_one]
    have : p * (2 * m) = (p * m) * 2 := by ring
    rw [this]
    exact Nat.mul_div_cancel (p * m) (by decide)
  rw [h_half1, h_half2]
  have h_mul_eq : p * m = (2 * m + 1) * m := by rw [hm]
  rw [h_mul_eq]
  have : (2 * m + 1) * m = m + 2 * (m * m) := by ring
  rw [this, pow_add, pow_mul]
  have : (-1 : ZMod p) ^ 2 = 1 := by ring
  rw [this, one_pow, mul_one]


theorem oeis_228304_conjecture_0 (p : ℕ) (hp : Nat.Prime p) (h_odd : p ≠ 2) :
    let N := Fin p
    let half_minus_one := (p - 1) / 2
    let A : Matrix N N ℤ := fun i j => a (i.val + j.val)
    let C : Matrix N N ℤ := fun i j => c (i.val + j.val)
    (Matrix.det A ≡ (-1 : ℤ) ^ half_minus_one [ZMOD p]) ∧ (Matrix.det C ≡ 1 [ZMOD p]) := by
  haveI : Fact p.Prime := ⟨hp⟩
  let N := Fin p
  let half_minus_one := (p - 1) / 2
  let A : Matrix N N ℤ := fun i j => a (i.val + j.val)
  let C : Matrix N N ℤ := fun i j => c (i.val + j.val)
  constructor
  · rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    set A_zmod : Matrix N N (ZMod p) := fun i j => (a (i.val + j.val) : ZMod p)
    have h_anti : ∀ i j : Fin p, p - 1 < i.val + j.val → A_zmod i j = 0 := by
      intro i j hij
      exact a_anti_triangular_cond p h_odd i j hij
    have h_det := det_of_anti_triangular p A_zmod h_anti
    change A_zmod.det = (-1 : ZMod p) ^ half_minus_one
    rw [h_det]
    have h_diag : (∏ i : Fin p, A_zmod i (Fin.revPerm i)) = 1 := by
      have h_ones : (∏ i : Fin p, A_zmod i (Fin.revPerm i)) = (∏ i : Fin p, (1 : ZMod p)) := by
        apply prod_congr rfl
        intro i _
        dsimp [A_zmod]
        have h_sum : (i : ℕ) + (p - ((i : ℕ) + 1)) = p - 1 := by
          have h_lt : (i : ℕ) < p := i.is_lt
          omega
        rw [h_sum]
        exact a_pred_zmod_eq_one p h_odd
      rw [h_ones, prod_const, Finset.card_univ, Fintype.card_fin p, one_pow]
    rw [h_diag, mul_one]
    have h_sign := sign_revPerm p
    have h_sign_cast := congr_arg (fun x : ℤˣ => (x : ZMod p)) h_sign
    push_cast at h_sign_cast
    rw [h_sign_cast]
    exact neg_one_pow_p_mul p h_odd

  · rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    set C_zmod : Matrix N N (ZMod p) := fun i j => (c (i.val + j.val) : ZMod p)
    have h_anti : ∀ i j : Fin p, p - 1 < i.val + j.val → C_zmod i j = 0 := by
      intro i j hij
      exact c_anti_triangular_cond p h_odd i j hij
    have h_det := det_of_anti_triangular p C_zmod h_anti
    change C_zmod.det = 1
    rw [h_det]
    have h_diag : (∏ i : Fin p, C_zmod i (Fin.revPerm i)) = (-1 : ZMod p) ^ (p * (p - 1) / 2) := by
      have h_term : (∏ i : Fin p, C_zmod i (Fin.revPerm i)) = (∏ i : Fin p, (-1 : ZMod p) ^ ((p - 1) / 2)) := by
        apply prod_congr rfl
        intro i _
        dsimp [C_zmod]
        have h_sum : (i : ℕ) + (p - ((i : ℕ) + 1)) = p - 1 := by
          have h_lt : (i : ℕ) < p := i.is_lt
          omega
        rw [h_sum]
        exact c_pred_zmod_eq_neg_one_pow p h_odd
      rw [h_term, prod_const, Finset.card_univ, Fintype.card_fin p, ← pow_mul]
      have hp_odd : Odd p := test_odd p h_odd
      rcases hp_odd with ⟨m, hm⟩
      have hp_sub_one : p - 1 = 2 * m := by omega
      have h_half1 : (p - 1) / 2 = m := by
        rw [hp_sub_one]
        exact Nat.mul_div_cancel_left m (by decide)
      have h_half2 : p * (p - 1) / 2 = m * p := by
        rw [hp_sub_one]
        have : p * (2 * m) = (m * p) * 2 := by ring
        rw [this]
        exact Nat.mul_div_cancel (m * p) (by decide)
      rw [h_half1, h_half2]
    rw [h_diag]
    have h_sign := sign_revPerm p
    have h_sign_cast := congr_arg (fun x : ℤˣ => (x : ZMod p)) h_sign
    push_cast at h_sign_cast
    rw [h_sign_cast]
    rw [← pow_add]
    have : (p * (p - 1) / 2) + (p * (p - 1) / 2) = 2 * (p * (p - 1) / 2) := by ring
    rw [this, pow_mul]
    have : (-1 : ZMod p) ^ 2 = 1 := by ring
    rw [this, one_pow]

























