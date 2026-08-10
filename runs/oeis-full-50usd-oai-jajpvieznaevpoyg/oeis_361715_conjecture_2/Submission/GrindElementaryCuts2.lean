import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 4000000
open Nat Finset

def a (n : ℕ) : ℕ := ∑ k ∈ range n, (n.choose k) ^ 2 * multichoose n k

example (p r : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 2 ≤ r) :
  (a (p ^ r) : ℤ) ≡ a (p ^ (r - 1)) [ZMOD (p ^ (3 * r + 3) : ℕ)] := by
  have hp1 : 1 < p := by omega
  have hp0 : 0 < p := by omega
  have hprm_gt1 : 1 < p ^ (r - 1) := by
    have hbase : p ^ 1 ≤ p ^ (r - 1) := Nat.pow_le_pow_right (by omega : 1 ≤ p) (by omega : 1 ≤ r - 1)
    simpa using lt_of_lt_of_le hp1 hbase
  have hprm_ne1 : p ^ (r - 1) ≠ 1 := Nat.ne_of_gt hprm_gt1
  have hprgt3 : 3 < p ^ r := by
    have hle : p ^ 2 ≤ p ^ r := Nat.pow_le_pow_right (by omega : 1 ≤ p) hr
    have hp2 : 3 < p ^ 2 := by nlinarith [hp5]
    omega
  have hcastp2ne2 : ((p : ℤ)^2) ≠ 2 := by
    have : (2:ℤ) < (p:ℤ)^2 := by nlinarith [show (5:ℤ) ≤ p by exact_mod_cast hp5]
    omega
  have hcastp2ne3 : ((p : ℤ)^2) ≠ 3 := by
    have : (3:ℤ) < (p:ℤ)^2 := by nlinarith [show (5:ℤ) ≤ p by exact_mod_cast hp5]
    omega
  have hpowneq : p ^ r ≠ p ^ (r-1) := by
    have hlt : p ^ (r-1) < p ^ r := Nat.pow_lt_pow_right hp1 (by omega)
    exact Nat.ne_of_gt hlt
  have hexp : 3 < 3 * r := by nlinarith
  have h3neq : ((p:ℤ)^3) ≠ ((p:ℤ)^(3*r)) := by
    have hlt : p^3 < p^(3*r) := Nat.pow_lt_pow_right hp1 hexp
    exact_mod_cast Nat.ne_of_lt hlt
  grind [a, Int.ModEq, Nat.Prime]
