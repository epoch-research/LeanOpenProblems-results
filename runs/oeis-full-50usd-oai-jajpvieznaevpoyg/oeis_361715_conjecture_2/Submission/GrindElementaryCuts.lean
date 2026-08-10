import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 3000000
open Nat Finset

def a (n : ℕ) : ℕ := ∑ k ∈ range n, (n.choose k) ^ 2 * multichoose n k

example (p r : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 2 ≤ r) :
  (a (p ^ r) : ℤ) ≡ a (p ^ (r - 1)) [ZMOD (p ^ (3 * r + 3) : ℕ)] := by
  have hp1 : 1 < p := by omega
  have hp2gt : 3 < p ^ 2 := by nlinarith [Nat.pow_le_pow_right (by omega : 2 ≤ p) (by norm_num : 1 ≤ 2)]
  have hprgt3 : 3 < p ^ r := by
    have hle : p ^ 2 ≤ p ^ r := Nat.pow_le_pow_right (by omega : 1 ≤ p) hr
    omega
  have hprm_pos : 0 < p ^ (r-1) := pow_pos (by omega : 0 < p) _
  have hprm_ne1_or : p ^ (r-1) = 1 ∨ 1 < p ^ (r-1) := by omega
  have hcastp2ne2 : ((p : ℤ)^2) ≠ 2 := by
    have : (2:ℤ) < (p:ℤ)^2 := by nlinarith [show (5:ℤ) ≤ p by exact_mod_cast hp5]
    omega
  have hcastp2ne3 : ((p : ℤ)^2) ≠ 3 := by
    have : (3:ℤ) < (p:ℤ)^2 := by nlinarith [show (5:ℤ) ≤ p by exact_mod_cast hp5]
    omega
  have hpowneq : p ^ r ≠ p ^ (r-1) := by
    have hlt : p ^ (r-1) < p ^ r := Nat.pow_lt_pow_right hp1 (by omega)
    exact Nat.ne_of_gt hlt
  grind [a, Int.ModEq, Nat.Prime]
