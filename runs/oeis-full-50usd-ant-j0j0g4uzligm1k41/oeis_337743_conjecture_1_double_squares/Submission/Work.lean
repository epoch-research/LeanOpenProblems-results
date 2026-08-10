import FormalConjectures.Util.ProblemImports

open Nat Finset

def is_power_of_four_b (k : ℕ) : Bool :=
  if k = 0 then false
  else
    let m := Nat.log2 k
    k = 2^m ∧ m % 2 = 0

def A337743 (n : ℕ) : ℕ :=
  let max_x := sqrt n
  (range (max_x + 1)).sum fun x =>
    let n' := n - x^2
    let max_y := sqrt n'
    (range (max_y + 1)).sum fun y =>
      if is_power_of_four_b (x + 2 * y) then
        let m := n' - y^2
        let max_z := sqrt (m / 2)
        (range (max_z + 1)).sum fun z =>
          let w_sq := m - z^2
          if sqrt w_sq * sqrt w_sq = w_sq then
            1
          else
            0
      else
        0

-- Witness lemma: if a valid representation exists, the count is positive.
theorem witness_pos (N x y z w : ℕ)
    (hsum : x^2 + y^2 + z^2 + w^2 = N)
    (hp : is_power_of_four_b (x + 2 * y) = true)
    (hzw : z ≤ w) :
    0 < A337743 N := by
  unfold A337743
  -- x ≤ sqrt N
  have hxN : x^2 ≤ N := by omega
  have hx_le : x ≤ sqrt N := by
    rw [Nat.le_sqrt']; exact hxN
  apply Finset.sum_pos'
  · intro i _; exact Nat.zero_le _
  · refine ⟨x, ?_, ?_⟩
    · rw [Finset.mem_range]; omega
    · -- inner sum over y
      simp only
      have hn' : N - x^2 = y^2 + z^2 + w^2 := by omega
      have hyN : y^2 ≤ N - x^2 := by omega
      have hy_le : y ≤ sqrt (N - x^2) := by rw [Nat.le_sqrt']; exact hyN
      apply Finset.sum_pos'
      · intro i _; positivity
      · refine ⟨y, ?_, ?_⟩
        · rw [Finset.mem_range]; omega
        · simp only [hp, if_true]
          -- m = N - x^2 - y^2 = z^2 + w^2
          have hm : N - x^2 - y^2 = z^2 + w^2 := by omega
          have hzw2 : z^2 ≤ w^2 := Nat.pow_le_pow_left hzw 2
          have hz2 : z^2 ≤ (N - x^2 - y^2) / 2 := by
            rw [hm]; omega
          have hz_le : z ≤ sqrt ((N - x^2 - y^2) / 2) := by
            rw [Nat.le_sqrt']; exact hz2
          apply Finset.sum_pos'
          · intro i _; positivity
          · refine ⟨z, ?_, ?_⟩
            · rw [Finset.mem_range]; omega
            · have hwsq : N - x^2 - y^2 - z^2 = w^2 := by omega
              show 0 < (if sqrt (N - x^2 - y^2 - z^2) * sqrt (N - x^2 - y^2 - z^2)
                = N - x^2 - y^2 - z^2 then 1 else 0)
              rw [hwsq, Nat.sqrt_eq', if_pos (by rw [pow_two])]
              exact Nat.one_pos
