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
