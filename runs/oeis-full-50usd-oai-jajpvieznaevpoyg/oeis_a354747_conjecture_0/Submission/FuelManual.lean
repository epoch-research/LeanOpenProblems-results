import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 200000

def N : Nat := 201886 * 3 ^ 39101 - 1
def M : Nat := 2 * 100943 * 3 ^ 39101

theorem N_add_one : N + 1 = M := by
  unfold N M
  have hpos : 1 ≤ 201886 * 3 ^ 39101 := by
    have hpow : 0 < 3 ^ 39101 := pow_pos (by norm_num) _
    exact Nat.succ_le_of_lt (Nat.mul_pos (by norm_num : 0 < 201886) hpow)
  rw [Nat.sub_add_cancel hpos]

theorem fuel_bound : N + 1 < 2 ^ 70000 := by
  rw [N_add_one]
  unfold M
  have hpow3 : 3 ^ 39101 < 2 ^ 62562 := by
    calc
      3 ^ 39101 = (3 ^ 5) ^ 7820 * 3 := by
        rw [show 39101 = 5 * 7820 + 1 by norm_num, pow_add, pow_mul]
        simp
      _ < (2 ^ 8) ^ 7820 * 4 := by
        apply Nat.mul_lt_mul''
        · apply Nat.pow_lt_pow_left
          · norm_num
          · norm_num
        · norm_num
      _ = (2 ^ 8) ^ 7820 * 2 ^ 2 := by norm_num
      _ = 2 ^ (8 * 7820) * 2 ^ 2 := by rw [← pow_mul]
      _ = 2 ^ 62562 := by rw [← pow_add]
  have hprod : (2 * 100943) * 3 ^ 39101 < 2 ^ 18 * 2 ^ 62562 := by
    apply Nat.mul_lt_mul''
    · norm_num
    · exact hpow3
  calc
    (2 * 100943) * 3 ^ 39101 < 2 ^ 18 * 2 ^ 62562 := hprod
    _ = 2 ^ 62580 := by rw [← pow_add]
    _ < 2 ^ 70000 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
