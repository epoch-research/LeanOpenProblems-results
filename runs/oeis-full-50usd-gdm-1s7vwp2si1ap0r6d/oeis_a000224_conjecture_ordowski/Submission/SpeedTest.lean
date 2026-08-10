import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

open Finset

noncomputable def A000224 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    Finset.card ((Finset.range n).image (fun k : ℕ => k ^ 2 % n))

theorem A000224_of_ne_zero {n : ℕ} (h_ne : n ≠ 0) :
    A000224 n = Finset.card ((Finset.range n).image (fun k : ℕ => k ^ 2 % n)) := by
  unfold A000224
  split_ifs with h
  · exact False.elim (h_ne h)
  · rfl

theorem A000224_ge_two {n : ℕ} (hn : 1 < n) : A000224 n ≥ 2 := by
  have h_ne : n ≠ 0 := by omega
  rw [A000224_of_ne_zero h_ne]
  have h0 : 0 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  have h1 : 1 ∈ Finset.range n := Finset.mem_range.mpr hn
  have h0_img : 0 ∈ (Finset.range n).image (fun k : ℕ => k ^ 2 % n) := by
    simp only [Finset.mem_image]
    refine ⟨0, h0, by simp⟩
  have h1_img : 1 ∈ (Finset.range n).image (fun k : ℕ => k ^ 2 % n) := by
    simp only [Finset.mem_image]
    refine ⟨1, h1, by simp [Nat.mod_eq_of_lt hn]⟩
  have h_sub : {0, 1} ⊆ (Finset.range n).image (fun k : ℕ => k ^ 2 % n) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h0_img
    · exact h1_img
  have h_card_pair : Finset.card ({0, 1} : Finset ℕ) = 2 := by
    rw [Finset.card_pair (by decide)]
  have h_le := Finset.card_le_card h_sub
  rw [h_card_pair] at h_le
  exact h_le

theorem range_image_eq_range_half {n : ℕ} (h_odd : Odd n) (hn : 1 < n) :
    (Finset.range n).image (fun k : ℕ => k ^ 2 % n) =
    (Finset.range ((n + 1) / 2)).image (fun k : ℕ => k ^ 2 % n) := by
  rcases h_odd with ⟨m, hm⟩
  have h_div : (n + 1) / 2 = m + 1 := by
    rw [hm]
    omega
  ext y
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    by_cases h_lt : k < (n + 1) / 2
    · exact ⟨k, h_lt, rfl⟩
    · -- k ≥ (n+1)/2
      have hk2 : m + 1 ≤ k := by omega
      use n - k
      have hk_lt : n - k < m + 1 := by omega
      have hk_lt_half : n - k < (n + 1) / 2 := by omega
      refine ⟨hk_lt_half, ?_⟩
      -- k^2 % n = (n-k)^2 % n
      have h1 : 2 * k ≥ n := by omega
      have h2 : n ≥ k := by omega
      have h_eq : n * (2 * k - n) + (n - k) ^ 2 = k ^ 2 := by
        zify [h1, h2]
        ring
      rw [← h_eq]
      rw [add_comm]
      rw [Nat.add_mul_mod_self_left]
  · rintro ⟨k, hk, rfl⟩
    use k
    have h_lt : k < n := by omega
    exact ⟨h_lt, rfl⟩

def A000224_fast (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    ((List.range ((n + 1) / 2)).map (fun k : ℕ => k ^ 2 % n)).dedup.length

theorem A000224_fast_eq {n : ℕ} (hn : 1 < n) (h_odd : Odd n) : A000224_fast n = A000224 n := by
  unfold A000224_fast A000224
  have hn_ne : n ≠ 0 := by omega
  simp [hn_ne]
  rw [range_image_eq_range_half h_odd hn]
  dsimp [Finset.image, Finset.card]
  rw [← Multiset.coe_range, Multiset.map_coe, Multiset.coe_dedup, Multiset.coe_card]

def check_ordowski_fast (n : ℕ) : Bool :=
  if n % 2 == 0 then true
  else if decide (Nat.Prime n) then true
  else
    let A := A000224_fast n
    let M := A * (A - 1)
    if M == 0 then true
    else (n * n) % M != 1

def check_up_to_fast : ℕ → Bool
  | 0 => true
  | n + 1 => check_ordowski_fast n && check_up_to_fast n

theorem check_up_to_fast_15 : check_up_to_fast 15 = true := by
  decide

theorem check_interval_15_100 : ∀ n, 15 ≤ n → n < 100 → check_ordowski_fast n = true := by
  decide

theorem check_interval_100_200 : ∀ n, 100 ≤ n → n < 200 → check_ordowski_fast n = true := by
  decide

theorem check_interval_200_300 : ∀ n, 200 ≤ n → n < 300 → check_ordowski_fast n = true := by
  decide

theorem check_interval_300_350 : ∀ n, 350 ≤ n → n < 500 → check_ordowski_fast n = true := by
  decide

lemma contra_of_check_ordowski_fast {n : ℕ} (h_n : 1 < n) (hp : ¬ n.Prime) (hn_odd : Odd n)
    (h_ord : check_ordowski_fast n = true) (h_congr : (n * n) ≡ 1 [MOD A000224 n * (A000224 n - 1)]) : False := by
  unfold check_ordowski_fast at h_ord
  have h_mod2 : n % 2 ≠ 0 := by
    intro h_even
    have : Even n := Nat.even_iff.mpr h_even
    have h_not_odd := Nat.not_even_iff_odd.mpr hn_odd
    exact h_not_odd this
  have h_prime_dec : decide (Nat.Prime n) = false := by
    simp [hp]
  simp [h_mod2, h_prime_dec] at h_ord
  rw [A000224_fast_eq h_n hn_odd] at h_ord
  have h_M_gt : 1 < A000224 n * (A000224 n - 1) := by
    have h_A_ge : A000224 n ≥ 2 := A000224_ge_two h_n
    have h_A_sub : A000224 n - 1 ≥ 1 := by omega
    have : 2 * 1 ≤ A000224 n * (A000224 n - 1) := Nat.mul_le_mul h_A_ge h_A_sub
    omega
  have h_mod_eq : (n * n) % (A000224 n * (A000224 n - 1)) = 1 := by
    rw [Nat.ModEq] at h_congr
    rw [Nat.mod_eq_of_lt h_M_gt] at h_congr
    exact h_congr
  simp [h_mod_eq] at h_ord
  have h_A_ge : A000224 n ≥ 2 := A000224_ge_two h_n
  rcases h_ord with hA1 | hA2
  · omega
  · omega

theorem check_up_to_fast_implies_no_solution (limit : ℕ) :
    check_up_to_fast limit = true → ∀ n, n < limit → 1 < n → ¬ n.Prime → Odd n → ¬ ((n * n) ≡ 1 [MOD A000224 n * (A000224 n - 1)]) := by
  induction limit with
  | zero =>
    intro _ n hn
    omega
  | succ limit ih =>
    intro h_check n hn h_n hp hn_odd h_congr
    unfold check_up_to_fast at h_check
    rw [Bool.and_eq_true] at h_check
    rcases h_check with ⟨h_limit, h_prev⟩
    by_cases hn_limit : n < limit
    · exact ih h_prev n hn_limit h_n hp hn_odd h_congr
    · have hn_eq : n = limit := by omega
      subst hn_eq
      exact contra_of_check_ordowski_fast h_n hp hn_odd h_limit h_congr

lemma no_solution_small :
    ∀ n < 350, 1 < n → ¬ n.Prime → Odd n → ¬ ((n * n) ≡ 1 [MOD A000224 n * (A000224 n - 1)]) := by
  intro n hn h1 hp hn_odd h_congr
  by_cases h15 : n < 15
  · exact check_up_to_fast_implies_no_solution 15 check_up_to_fast_15 n h15 h1 hp hn_odd h_congr
  · have h_ge15 : 15 ≤ n := by omega
    by_cases h100 : n < 100
    · have h_ord := check_interval_15_100 n h_ge15 h100
      exact contra_of_check_ordowski_fast h1 hp hn_odd h_ord h_congr
    · have h_ge100 : 100 ≤ n := by omega
      by_cases h200 : n < 200
      · have h_ord := check_interval_100_200 n h_ge100 h200
        exact contra_of_check_ordowski_fast h1 hp hn_odd h_ord h_congr
      · have h_ge200 : 200 ≤ n := by omega
        by_cases h300 : n < 300
        · have h_ord := check_interval_200_300 n h_ge200 h300
          exact contra_of_check_ordowski_fast h1 hp hn_odd h_ord h_congr
        · have h_ge300 : 300 ≤ n := by omega
          have h350 : n < 350 := hn
          have h_ord := check_interval_300_350 n h_ge300 h350
          exact contra_of_check_ordowski_fast h1 hp hn_odd h_ord h_congr
