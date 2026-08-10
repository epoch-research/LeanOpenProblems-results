import FormalConjectures.Util.ProblemImports

open Finset

def A048153 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

def Sneg (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun k => (n - k ^ 2 % n) % n)

def Wcount (n : ℕ) : ℕ :=
  (Finset.filter (fun k => k ^ 2 % n ≠ 0) (Finset.range n)).card

theorem S_add_Sneg (n : ℕ) (hn : 1 ≤ n) :
    A048153 n + Sneg n = n * Wcount n := by
  unfold A048153 Sneg Wcount
  rw [← Finset.sum_add_distrib, Finset.card_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hlt : k ^ 2 % n < n := Nat.mod_lt _ hn
  by_cases h : k ^ 2 % n = 0
  · simp [h, Nat.mod_self]
  · have h2 : n - k ^ 2 % n < n := by omega
    rw [Nat.mod_eq_of_lt h2, if_pos h]
    omega

theorem Wcount_le (n : ℕ) (hn : 1 ≤ n) : Wcount n ≤ n - 1 := by
  unfold Wcount
  have hsub : (Finset.filter (fun k => k ^ 2 % n ≠ 0) (Finset.range n)) ⊆ (Finset.range n).erase 0 := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    rw [Finset.mem_erase, Finset.mem_range]
    refine ⟨?_, hk.1⟩
    intro h0
    apply hk.2
    rw [h0]; simp
  calc (Finset.filter (fun k => k ^ 2 % n ≠ 0) (Finset.range n)).card
      ≤ ((Finset.range n).erase 0).card := Finset.card_le_card hsub
    _ = n - 1 := by
        rw [Finset.card_erase_of_mem (by rw [Finset.mem_range]; omega), Finset.card_range]

/-- The deep core: S ≤ S'. Equivalent to ∑ k^2%n ≤ (n/2)·#{k : k^2 ≢ 0}. -/
theorem core (n : ℕ) (hn : 1 ≤ n) : A048153 n ≤ Sneg n := by
  sorry

/-- Master inequality 2S ≤ n(n-1). -/
theorem master (n : ℕ) (hn : 1 ≤ n) : 2 * A048153 n ≤ n * (n - 1) := by
  have hid := S_add_Sneg n hn
  have hcore := core n hn
  have hw := Wcount_le n hn
  -- 2S ≤ S + S' = n W ≤ n(n-1)
  have h1 : 2 * A048153 n ≤ n * Wcount n := by
    have : A048153 n + Sneg n = n * Wcount n := hid
    omega
  calc 2 * A048153 n ≤ n * Wcount n := h1
    _ ≤ n * (n - 1) := Nat.mul_le_mul_left n hw

theorem final (n : ℕ) (h : 1 ≤ n) : A048153 n ≤ (n ^ 2 - 1) / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  have h1 : n * (n - 1) ≤ n ^ 2 - 1 := by
    cases n with
    | zero => simp
    | succ m => simp only [Nat.succ_sub_one]; ring_nf; omega
  calc A048153 n * 2 = 2 * A048153 n := by ring
    _ ≤ n * (n - 1) := master n h
    _ ≤ n ^ 2 - 1 := h1
