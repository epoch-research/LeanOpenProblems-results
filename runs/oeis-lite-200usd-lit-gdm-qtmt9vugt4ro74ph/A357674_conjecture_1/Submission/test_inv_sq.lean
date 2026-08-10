import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

lemma sum_range_sq_nat (n : ℕ) : 6 * (∑ k ∈ range n, k ^ 2) = n * (n - 1) * (2 * n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases n with rfl | n
    · simp
    · -- n is succ n, so we are at succ (succ n)
      -- Let's simplify succ and sub_one
      have h_sub1 : succ (succ n) - 1 = succ n := rfl
      have h_sub2 : 2 * succ (succ n) - 1 = 2 * n + 3 := by omega
      have h_sub3 : succ n - 1 = n := rfl
      have h_sub4 : 2 * succ n - 1 = 2 * n + 1 := by omega
      rw [h_sub1, h_sub2]
      -- ih is: 6 * (∑ k ∈ range (succ n), k ^ 2) = succ n * (succ n - 1) * (2 * succ n - 1)
      -- Let's simplify ih using h_sub3 and h_sub4
      rw [h_sub3, h_sub4] at ih
      -- Now LHS of our goal: 6 * ∑ k ∈ range (succ (succ n)), k ^ 2
      -- By sum_range_succ, this is 6 * (∑ k ∈ range (succ n), k ^ 2 + (succ n)^2)
      rw [sum_range_succ]
      -- multiply by 6
      rw [mul_add]
      -- now substitute ih
      rw [ih]
      -- now it's just a polynomial identity in n!
      -- Let's rewrite succ n as n + 1
      simp only [succ_eq_add_one]
      ring

lemma sum_squares_eq_zero (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    ∑ i ∈ range p, ((i : ZMod p) ^ 2) = 0 := by
  have h_fact : Fact p.Prime := ⟨hp⟩
  have h_eq : (6 : ZMod p) * (∑ i ∈ range p, ((i : ZMod p) ^ 2)) = 0 := by
    -- we can cast from sum_range_sq_nat
    have h_nat := sum_range_sq_nat p
    have h_cast : ((6 * (∑ k ∈ range p, k ^ 2) : ℕ) : ZMod p) = ((p * (p - 1) * (2 * p - 1) : ℕ) : ZMod p) := by
      rw [h_nat]
    push_cast at h_cast
    rw [ZMod.natCast_self p] at h_cast
    simp only [zero_mul] at h_cast
    exact h_cast
  -- since p >= 5, 6 is not 0 mod p
  have h_six : (6 : ZMod p) ≠ 0 := by
    change ¬ (((6 : ℕ) : ZMod p) = 0)
    rw [ZMod.natCast_eq_zero_iff]
    intro h_dvd'
    -- since p >= 5 and p is prime, the only prime divisors of 6 are 2 and 3
    have h_dvd_factors : p = 2 ∨ p = 3 := by
      have h6 : 6 = 2 * 3 := by decide
      rw [h6] at h_dvd'
      rcases hp.dvd_mul.mp h_dvd' with h2 | h3
      · left
        exact ((Nat.Prime.dvd_iff_eq (by decide) hp.ne_one).mp h2).symm
      · right
        exact ((Nat.Prime.dvd_iff_eq (by decide) hp.ne_one).mp h3).symm
    rcases h_dvd_factors with rfl | rfl
    · omega
    · omega
  exact (mul_eq_zero.mp h_eq).resolve_left h_six

lemma sum_inv_squares_eq_zero (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    ∑ j ∈ Ico 1 p, ((j : ZMod p)⁻¹ ^ 2) = 0 := by
  have h_fact : Fact p.Prime := ⟨hp⟩
  have h_sum : ∑ j ∈ Ico 1 p, ((j : ZMod p)⁻¹ ^ 2) = ∑ j ∈ Ico 1 p, ((j : ZMod p) ^ 2) := by
    apply Finset.sum_nbij' (fun j => ((j : ZMod p)⁻¹).val) (fun j => ((j : ZMod p)⁻¹).val)
    · intro a ha
      rw [mem_Ico] at ha ⊢
      have ha_nz : (a : ZMod p) ≠ 0 := by
        rw [ZMod.natCast_eq_zero_iff]
        intro hdvd
        have : p ≤ a := Nat.le_of_dvd (by omega) hdvd
        omega
      have h_inv_nz : (a : ZMod p)⁻¹ ≠ 0 := inv_ne_zero ha_nz
      have h_val_nz : ((a : ZMod p)⁻¹).val ≠ 0 := by
        intro h_zero
        apply h_inv_nz
        rw [← ZMod.natCast_val ((a : ZMod p)⁻¹), h_zero]
        rfl
      constructor
      · omega
      · exact ZMod.val_lt ((a : ZMod p)⁻¹)
    · intro a ha
      -- exactly the same as above
      rw [mem_Ico] at ha ⊢
      have ha_nz : (a : ZMod p) ≠ 0 := by
        rw [ZMod.natCast_eq_zero_iff]
        intro hdvd
        have : p ≤ a := Nat.le_of_dvd (by omega) hdvd
        omega
      have h_inv_nz : (a : ZMod p)⁻¹ ≠ 0 := inv_ne_zero ha_nz
      have h_val_nz : ((a : ZMod p)⁻¹).val ≠ 0 := by
        intro h_zero
        apply h_inv_nz
        rw [← ZMod.natCast_val ((a : ZMod p)⁻¹), h_zero]
        rfl
      constructor
      · omega
      · exact ZMod.val_lt ((a : ZMod p)⁻¹)
    · intro a ha
      rw [mem_Ico] at ha
      have : (((a : ZMod p)⁻¹).val : ZMod p) = (a : ZMod p)⁻¹ := ZMod.natCast_val ((a : ZMod p)⁻¹)
      rw [this, inv_inv]
      exact ZMod.val_natCast_of_lt ha.2
    · intro a ha
      rw [mem_Ico] at ha
      have : (((a : ZMod p)⁻¹).val : ZMod p) = (a : ZMod p)⁻¹ := ZMod.natCast_val ((a : ZMod p)⁻¹)
      rw [this, inv_inv]
      exact ZMod.val_natCast_of_lt ha.2
    · intro a ha
      have : (((a : ZMod p)⁻¹).val : ZMod p) = (a : ZMod p)⁻¹ := ZMod.natCast_val ((a : ZMod p)⁻¹)
      rw [this]
  rw [h_sum]
  -- Now we show that ∑ j ∈ Ico 1 p, ((j : ZMod p) ^ 2) = 0
  -- since range p = {0} ∪ Ico 1 p, we can split
  have h_split : ∑ j ∈ range p, ((j : ZMod p) ^ 2) = ((0 : ZMod p) ^ 2) + ∑ j ∈ Ico 1 p, ((j : ZMod p) ^ 2) := by
    rw [← sum_range_succ_left]
    -- wait, sum_range_succ_left shifts the indices... No!
    -- actually, range p is {0} ∪ Ico 1 p.
    -- let's write it using sum_eq_add_of_mem or by range p = insert 0 (Ico 1 p)
    sorry
