import FormalConjectures.Util.ProblemImports

open Finset

/--
A048153: $a(n) = \sum_{k=1}^n (k^2 \bmod n)$.
This sequence is defined in Lean as the sum of $k^2 \bmod n$ for $k \in \{0, 1, \dots, n-1\}.
-/
def A048153 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

set_option maxRecDepth 200000
set_option maxHeartbeats 5000000

def bin_sum_fuel (f : ℕ → ℕ) (a b : ℕ) : ℕ → ℕ
  | 0 => 0
  | fuel + 1 =>
    if b < a then 0
    else if a = b then f a
    else
      let mid := (a + b) / 2
      bin_sum_fuel f a mid fuel + bin_sum_fuel f (mid + 1) b fuel

theorem bin_sum_fuel_eq (f : ℕ → ℕ) (a b : ℕ) (fuel : ℕ) (h_fuel : b - a < fuel) :
    bin_sum_fuel f a b fuel = Finset.sum (Finset.Ico a (b + 1)) f := by
  induction fuel generalizing a b with
  | zero =>
    omega
  | succ fuel ih =>
    rw [bin_sum_fuel]
    split_ifs with h1 h2
    · have : a ≥ b + 1 := by omega
      rw [Finset.Ico_eq_empty_of_le this, Finset.sum_empty]
    · subst h2
      simp
    · have h_fuel1 : (a + b) / 2 - a < fuel := by omega
      have h_fuel2 : b - ((a + b) / 2 + 1) < fuel := by omega
      change bin_sum_fuel f a ((a + b) / 2) fuel + bin_sum_fuel f ((a + b) / 2 + 1) b fuel = Finset.sum (Finset.Ico a (b + 1)) f
      rw [ih a ((a + b) / 2) h_fuel1]
      rw [ih ((a + b) / 2 + 1) b h_fuel2]
      have h_le1 : a ≤ (a + b) / 2 + 1 := by omega
      have h_le2 : (a + b) / 2 + 1 ≤ b + 1 := by omega
      rw [← Finset.sum_Ico_consecutive f h_le1 h_le2]

def fast_A048153 (n : ℕ) : ℕ :=
  if n = 0 then 0 else bin_sum_fuel (fun k => k ^ 2 % n) 0 (n - 1) n

theorem fast_A048153_eq (n : ℕ) : fast_A048153 n = Finset.sum (Finset.range n) (fun k => k ^ 2 % n) := by
  by_cases hn : n = 0
  · subst hn
    rfl
  · unfold fast_A048153
    rw [if_neg hn]
    have h_fuel : (n - 1) - 0 < n := by omega
    rw [bin_sum_fuel_eq _ 0 (n - 1) n h_fuel]
    have h_sub_add : n - 1 + 1 = n := by omega
    rw [h_sub_add]
    rw [← range_eq_Ico]

def bin_check_conjecture (a b : ℕ) : ℕ → Bool
  | 0 => true
  | fuel + 1 =>
    if b < a then true
    else if a = b then
      (fast_A048153 a ≤ (a ^ 2 - 1) / 2)
    else
      let mid := (a + b) / 2
      bin_check_conjecture a mid fuel && bin_check_conjecture (mid + 1) b fuel

theorem bin_check_conjecture_eq_true (fuel : ℕ) (a b : ℕ) (h_fuel : b - a < fuel)
    (h_check : bin_check_conjecture a b fuel = true) (n : ℕ) (han : a ≤ n) (hnb : n ≤ b) :
    fast_A048153 n ≤ (n ^ 2 - 1) / 2 := by
  induction fuel generalizing a b with
  | zero =>
    omega
  | succ fuel ih =>
    rw [bin_check_conjecture] at h_check
    split_ifs at h_check with h1 h2
    · omega
    · subst h2
      have : n = a := by omega
      subst this
      rw [decide_eq_true_iff] at h_check
      exact h_check
    · rw [Bool.and_eq_true] at h_check
      rcases h_check with ⟨h_check1, h_check2⟩
      have h_or : n ≤ (a + b) / 2 ∨ n ≥ (a + b) / 2 + 1 := by omega
      rcases h_or with h_le | h_ge
      · have h_fuel1 : (a + b) / 2 - a < fuel := by omega
        exact ih a ((a + b) / 2) h_fuel1 h_check1 han h_le
      · have h_fuel2 : b - ((a + b) / 2 + 1) < fuel := by omega
        exact ih ((a + b) / 2 + 1) b h_fuel2 h_check2 h_ge hnb


theorem k_sq_mod_le_tight (n k : ℕ) (hn : 1 ≤ n) (hk : k < n) : 2 * (k ^ 2 % n) ≤ k * (n - k) + n - 1 := by
  by_cases hk0 : k = 0
  · subst hk0
    simp
  · have h_pos : n > 0 := by omega
    have h_n2 : n ≥ 2 := by omega
    generalize hq : k ^ 2 / n = q
    have h_div : k ^ 2 = q * n + k ^ 2 % n := by
      have h1 := Nat.div_add_mod (k ^ 2) n
      rw [mul_comm] at h1
      rw [hq] at h1
      exact h1.symm
    have h_mod : k ^ 2 % n = k ^ 2 - q * n := by omega
    have h_sub : k * (n - k) = k * n - k ^ 2 := by
      rw [Nat.mul_sub_left_distrib, ← pow_two]
    have h_lt_q : q < k := by
      rw [← hq]
      rw [Nat.div_lt_iff_lt_mul h_pos]
      rw [pow_two]
      exact Nat.mul_lt_mul_of_pos_left hk (by omega : k > 0)
    have h_cases : k - q ≥ 2 ∨ k - q = 1 := by omega
    rcases h_cases with h_ge | h_eq
    · -- Case 1: k - q >= 2
      have h_qn_sub : (k - q) * n = k * n - q * n := by
        rw [Nat.sub_mul]
      have h_qn_sub2 : (k - q + 1) * n = k * n - q * n + n := by
        rw [Nat.add_mul, h_qn_sub, Nat.one_mul]
      have h_le_3n : (k - q + 1) * n ≥ 3 * n := by
        have : k - q + 1 ≥ 3 := by omega
        gcongr
      have h_3r : 3 * (k ^ 2 % n) < 3 * n := by
        linarith [Nat.mod_lt (k ^ 2) h_pos]
      have h_le_final : 3 * (k ^ 2 % n) ≤ (k - q + 1) * n - 1 := by omega
      omega
    · -- Case 2: k - q = 1
      have h_kn_ge : k * n ≥ n := by
        have : 1 * n ≤ k * n := Nat.mul_le_mul_right n (by omega : 1 ≤ k)
        rwa [Nat.one_mul] at this
      have h_qn_sub : q * n + n = k * n := by
        have : q = k - 1 := by omega
        clear h_div h_mod h_sub h_lt_q
        rw [this, Nat.sub_mul, Nat.one_mul]
        omega
      have h_div2 : k ^ 2 + n = k * n + k ^ 2 % n := by
        clear h_sub h_lt_q
        omega
      have h_le_kn2 : k ^ 2 ≤ k * n := by
        rw [pow_two]
        have : k ≤ n := by omega
        gcongr
      have h_le_n : k * n - k ^ 2 ≤ n := by
        clear h_sub h_lt_q
        omega
      have h_r : k ^ 2 % n = n - k * (n - k) := by
        clear h_lt_q h_qn_sub h_div h_mod
        rw [h_sub]
        omega
      have h_min : k * (n - k) ≥ n - 1 := by
        have h_le_kn : q * n + 1 ≥ k ^ 2 := by
          have h_nk1 : n ≥ k + 1 := by omega
          have h_step : q * n ≥ q * (k + 1) := by
            have : q = k - 1 := by omega
            rw [this]
            gcongr
          have h_ring : q * (k + 1) + 1 = k ^ 2 := by
            rcases k with _ | k'
            · omega
            · have : q = k' := by omega
              rw [this]
              ring
          omega
        omega
      omega


theorem k_sq_mod_le_k_mul_sub (n k : ℕ) (hn : 1 ≤ n) (hk : k < n) :
    k ^ 2 % n ≤ k * (n - k) := by
  by_cases hk0 : k = 0
  · subst hk0
    simp
  · have h_pos : n > 0 := by omega
    generalize hq : k ^ 2 / n = q
    have h_div : k ^ 2 = q * n + k ^ 2 % n := by
      have h1 := Nat.div_add_mod (k ^ 2) n
      rw [mul_comm] at h1
      rw [hq] at h1
      exact h1.symm
    have h_lt_q : q < k := by
      rw [← hq]
      rw [Nat.div_lt_iff_lt_mul h_pos]
      rw [pow_two]
      exact Nat.mul_lt_mul_of_pos_left hk (by omega : k > 0)
    have h_sub : k * (n - k) = k * n - k ^ 2 := by
      rw [Nat.mul_sub_left_distrib, ← pow_two]
    have h_cases : k - q ≥ 2 ∨ k - q = 1 := by omega
    rcases h_cases with h_ge | h_eq
    · have h_qn_sub : (k - q) * n = k * n - q * n := by
        rw [Nat.sub_mul]
      have h_rem_lt : k ^ 2 % n < n := Nat.mod_lt _ h_pos
      have h_qn : (k - q) * n ≥ 2 * n := by
        have : k - q ≥ 2 := h_ge
        gcongr
      omega
    · have h_kn_ge : k * n ≥ n := by
        have : 1 * n ≤ k * n := Nat.mul_le_mul_right n (by omega : 1 ≤ k)
        rwa [Nat.one_mul] at this
      have h_qn_sub : q * n + n = k * n := by
        have : q = k - 1 := by omega
        rw [this, Nat.sub_mul, Nat.one_mul]
        omega
      have h_div2 : k ^ 2 + n = k * n + k ^ 2 % n := by
        omega
      have h_le_kn2 : k ^ 2 ≤ k * n := by
        rw [pow_two]
        have : k ≤ n := by omega
        gcongr
      have h_r : k ^ 2 % n = n - k * (n - k) := by
        rw [h_sub]
        omega
      have h_min : k * (n - k) ≥ n - 1 := by
        have h_le_kn : q * n + 1 ≥ k ^ 2 := by
          have h_nk1 : n ≥ k + 1 := by omega
          have h_step : q * n ≥ q * (k + 1) := by
            have : q = k - 1 := by omega
            rw [this]
            gcongr
          have h_ring : q * (k + 1) + 1 = k ^ 2 := by
            rcases k with _ | k'
            · omega
            · have : q = k' := by omega
              rw [this]
              ring
          omega
        omega
      omega


lemma k_mul_sub_mod_eq_sub_mod_self (n k : ℕ) (hn : 1 ≤ n) (hk : k < n) :
    (k * (n - k)) % n = (n - k ^ 2 % n) % n := by
  by_cases hk0 : k = 0
  · subst hk0
    simp
  · have h_pos : n > 0 := by omega
    generalize hq : k ^ 2 / n = q
    have h_div : k ^ 2 = q * n + k ^ 2 % n := by
      have h1 := Nat.div_add_mod (k ^ 2) n
      rw [mul_comm] at h1
      rw [hq] at h1
      exact h1.symm
    have h_lt_q : q < k := by
      rw [← hq]
      rw [Nat.div_lt_iff_lt_mul h_pos]
      rw [pow_two]
      exact Nat.mul_lt_mul_of_pos_left hk (by omega : k > 0)
    have h_sub : k * (n - k) = k * n - k ^ 2 := by
      rw [Nat.mul_sub_left_distrib, ← pow_two]
    have h_qn_sub : (k - q) * n = k * n - q * n := Nat.sub_mul k q n
    have h_div2 : k * n - k ^ 2 = (k - q) * n - k ^ 2 % n := by
      rw [h_qn_sub]
      nth_rw 1 [h_div]
      omega
    have h_div3 : (k - q) * n - k ^ 2 % n = (k - q - 1) * n + (n - k ^ 2 % n) := by
      have : k - q ≥ 1 := by omega
      have h_qn : (k - q) * n = (k - q - 1) * n + n := by
        have : k - q = (k - q - 1) + 1 := by omega
        nth_rw 1 [this]
        rw [Nat.add_mul, Nat.one_mul]
      rw [h_qn]
      rw [Nat.add_sub_assoc]
      exact Nat.le_of_lt (Nat.mod_lt _ h_pos)
    have h_mod_add : ∀ (a b : ℕ), ((a * n) + b) % n = b % n := by
      intro a b
      rw [mul_comm a n, Nat.add_comm]
      exact Nat.add_mul_mod_self_left b n a
    rw [h_sub, h_div2, h_div3]
    exact h_mod_add (k - q - 1) (n - k ^ 2 % n)


lemma sum_self_add_sub_mod_le (n : ℕ) (hn : 1 ≤ n) :
    Finset.sum (Finset.range n) (fun k => k ^ 2 % n + (n - k ^ 2 % n) % n) ≤ n * (n - 1) := by
  have h_pos : n > 0 := by omega
  have h_split : Finset.range n = insert 0 (Finset.erase (Finset.range n) 0) := by
    apply Eq.symm
    apply Finset.insert_erase
    rw [Finset.mem_range]
    exact h_pos
  rw [h_split]
  have h_not_mem : 0 ∉ Finset.erase (Finset.range n) 0 := by
    rw [Finset.mem_erase]
    simp
  rw [Finset.sum_insert h_not_mem]
  have h_zero : 0 ^ 2 % n + (n - 0 ^ 2 % n) % n = 0 := by
    have h1 : 0 ^ 2 % n = 0 := by
      change 0 % n = 0
      exact Nat.zero_mod n
    rw [h1]
    simp
  rw [h_zero, Nat.zero_add]
  have h_le : Finset.sum (Finset.erase (Finset.range n) 0) (fun k => k ^ 2 % n + (n - k ^ 2 % n) % n) ≤ Finset.sum (Finset.erase (Finset.range n) 0) (fun _ => n) := by
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mem_erase, Finset.mem_range] at hk
    have hk2 : k ^ 2 % n < n := Nat.mod_lt _ h_pos
    by_cases hk0 : k ^ 2 % n = 0
    · rw [hk0]
      simp
    · have : n - k ^ 2 % n < n := by omega
      rw [Nat.mod_eq_of_lt this]
      omega
  have h_card : Finset.card (Finset.erase (Finset.range n) 0) = n - 1 := by
    rw [Finset.card_erase_of_mem]
    · simp
    · rw [Finset.mem_range]
      exact h_pos
  rw [Finset.sum_const, h_card, nsmul_eq_mul, mul_comm] at h_le
  exact h_le

/--
Conjecture: a(n) <= (n^2-1)/2. - _Aspen A.M. Meissner_, Mar 06 2025
We require $n \ge 1$ for the difference $n^2 - 1$ to be a natural number.
The division `/ 2` is natural number (integer) division.
-/
theorem oeis_48153_conjecture_0 (n : ℕ) (h : 1 ≤ n) : A048153 n ≤ (n ^ 2 - 1) / 2 := by
  have h_cases : n ≤ 300 ∨ n > 300 := by omega
  rcases h_cases with h_le | h_gt
  · have h_fast : fast_A048153 n ≤ (n ^ 2 - 1) / 2 := by
      apply bin_check_conjecture_eq_true 300 1 300 _ _ n h h_le
      · omega
      · decide
    unfold A048153
    rwa [← fast_A048153_eq]
  · sorry
