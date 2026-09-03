import Submission.BlockSieveBound

/-! Explicit geometric-sum estimates for the block sieve. -/
namespace Erdos970.BlockSieve

theorem geometric_error_sum (J : ℕ) :
    (∑ j : Fin (J + 1), (1 : ℝ) / 2 ^ (J - j.val + 3)) ≤ 1 / 4 := by
  induction J with
  | zero => norm_num
  | succ J ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.sub_self, zero_add]
    have hsum : (∑ j : Fin (J + 1), (1 : ℝ) / 2 ^ (J + 1 - j.val + 3)) =
        (∑ j : Fin (J + 1), (1 : ℝ) / 2 ^ (J - j.val + 3)) / 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      have heq : J + 1 - j.val + 3 = (J - j.val + 3) + 1 := by omega
      rw [heq, pow_succ, div_mul_eq_div_div]
    rw [hsum]
    norm_num
    simp only [one_div] at ih
    linarith

theorem weighted_exponent_sum (J : ℕ) :
    (∑ j : Fin (J + 1), 2 ^ (j.val + 1) * (2 * (J - j.val) + 37)) +
      4 * J + 82 = 156 * 2 ^ J := by
  induction J with
  | zero => norm_num
  | succ J ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.sub_zero, pow_one, Fin.val_succ, Nat.add_sub_add_right]
    have hsum : (∑ j : Fin (J + 1), 2 ^ (j.val + 1 + 1) * (2 * (J - j.val) + 37)) =
        2 * ∑ j : Fin (J + 1), 2 ^ (j.val + 1) * (2 * (J - j.val) + 37) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [pow_succ]
      ring
    rw [hsum]
    simp only [Nat.zero_add, pow_one, pow_succ] at ih ⊢
    nlinarith

theorem two_pow_clog_le (x : ℕ) (hx : 0 < x) : 2 ^ Nat.clog 2 x ≤ 2 * x := by
  by_cases hx1 : x = 1
  · simp [hx1]
  have hx2 : 1 < x := by omega
  have hc := Nat.clog_pos (by decide : 1 < 2) hx2
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hx2
  rw [Nat.pred_eq_sub_one] at hp
  have he : Nat.clog 2 x = (Nat.clog 2 x - 1) + 1 := by omega
  calc
    2 ^ Nat.clog 2 x = 2 ^ (Nat.clog 2 x - 1) * 2 := by
      conv_lhs => rw [he]
      rw [pow_succ]
    _ ≤ 2 * x := by nlinarith

/-- A coarse fixed-power bound for the product of all block costs. -/
theorem block_cost_product_le (k : ℕ) (hk : 0 < k)
    (A : Fin (Nat.clog 2 (Nat.clog 2 (k + 1)) + 1) → ℕ)
    (hA : ∀ j, A j ≤ 2 ^ (2 ^ (j.val + 1))) :
    (∏ j, A j ^ (2 * (Nat.clog 2 (Nat.clog 2 (k + 1)) - j.val + 18) + 1)) ≤
      (k + 1) ^ 624 := by
  let K := k + 1
  let L := Nat.clog 2 K
  let J := Nat.clog 2 L
  have hK : 2 ≤ K := by dsimp [K]; omega
  have hL : 0 < L := Nat.clog_pos (by decide) (by omega)
  have hJpow : 2 ^ J ≤ 2 * L := two_pow_clog_le L hL
  have hLpow : 2 ^ L ≤ 2 * K := two_pow_clog_le K (by omega)
  have hsum := weighted_exponent_sum J
  change (∏ j : Fin (J + 1), A j ^ (2 * (J - j.val + 18) + 1)) ≤ K ^ 624
  calc
    _ ≤ ∏ j : Fin (J + 1), (2 ^ (2 ^ (j.val + 1))) ^ (2 * (J - j.val + 18) + 1) := by
      exact Finset.prod_le_prod' (fun j _ => Nat.pow_le_pow_left (hA j) _)
    _ = 2 ^ (∑ j : Fin (J + 1), 2 ^ (j.val + 1) * (2 * (J - j.val) + 37)) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      apply Finset.prod_congr rfl
      intro j hj
      rw [← pow_mul]
      congr 2
    _ ≤ 2 ^ (156 * 2 ^ J) := Nat.pow_le_pow_right (by decide) (by omega)
    _ ≤ 2 ^ (312 * L) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = (2 ^ L) ^ 312 := by rw [← pow_mul]; congr 1; omega
    _ ≤ (2 * K) ^ 312 := Nat.pow_le_pow_left hLpow _
    _ ≤ (K * K) ^ 312 := Nat.pow_le_pow_left (Nat.mul_le_mul_right K hK) _
    _ = K ^ 624 := by rw [← pow_two, ← pow_mul]

/-- The remaining factors consume at most another eight powers. -/
theorem block_prefactor_le (k : ℕ) (hk : 0 < k) :
    (Nat.clog 2 (Nat.clog 2 (k + 1)) + 2) * (k + 1) *
      2 ^ (Nat.clog 2 (Nat.clog 2 (k + 1)) + 2) ≤ (k + 1) ^ 8 := by
  let K := k + 1
  let L := Nat.clog 2 K
  let J := Nat.clog 2 L
  have hK : 2 ≤ K := by dsimp [K]; omega
  have hL : 0 < L := Nat.clog_pos (by decide) (by omega)
  have hLK : L ≤ K := Nat.clog_le_of_le_pow (Nat.lt_pow_self (by decide : 1 < 2)).le
  have hJpow : 2 ^ J ≤ 2 * L := two_pow_clog_le L hL
  have hJsize : J + 2 ≤ 2 * 2 ^ J := by
    have hh := Nat.lt_pow_self (n := J + 1) (by decide : 1 < 2)
    rw [pow_succ] at hh
    omega
  have h32 : 32 ≤ K ^ 5 := by
    have hh := Nat.pow_le_pow_left hK 5
    norm_num at hh
    exact hh
  change (J + 2) * K * 2 ^ (J + 2) ≤ K ^ 8
  calc
    _ ≤ (2 * 2 ^ J) * K * (4 * 2 ^ J) := by
      have he : 2 ^ (J + 2) = 4 * 2 ^ J := by rw [pow_add]; ring
      rw [he]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right K hJsize)
    _ = 8 * K * (2 ^ J) ^ 2 := by ring
    _ ≤ 8 * K * (2 * L) ^ 2 := by gcongr
    _ = 32 * K * L ^ 2 := by ring
    _ ≤ 32 * K * K ^ 2 := by gcongr
    _ ≤ K ^ 5 * K * K ^ 2 := by gcongr
    _ = K ^ 8 := by ring

#print axioms block_cost_product_le
#print axioms block_prefactor_le
end Erdos970.BlockSieve
