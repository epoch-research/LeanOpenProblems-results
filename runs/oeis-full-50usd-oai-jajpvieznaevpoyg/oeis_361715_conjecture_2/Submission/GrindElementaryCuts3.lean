import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 5000000
open Nat Finset

def a (n : ℕ) : ℕ := ∑ k ∈ range n, (n.choose k) ^ 2 * multichoose n k

example (p r : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 2 ≤ r) :
  (a (p ^ r) : ℤ) ≡ a (p ^ (r - 1)) [ZMOD (p ^ (3 * r + 3) : ℕ)] := by
  have hp1 : 1 < p := by omega
  have hp0 : 0 < p := by omega
  have hprm_gt1 : 1 < p ^ (r - 1) := by
    have hbase : p ^ 1 ≤ p ^ (r - 1) := Nat.pow_le_pow_right (by omega : 1 ≤ p) (by omega : 1 ≤ r - 1)
    exact lt_of_lt_of_le (by simpa using hp1) hbase
  have hprm_ne1 : p ^ (r - 1) ≠ 1 := Nat.ne_of_gt hprm_gt1
  have hpowlt : p ^ (r-1) < p ^ r := Nat.pow_lt_pow_right hp1 (by omega)
  have hpowneq : p ^ r ≠ p ^ (r-1) := Nat.ne_of_gt hpowlt
  have hcastp2ne2 : ((p : ℤ)^2) ≠ 2 := by
    have : (2:ℤ) < (p:ℤ)^2 := by nlinarith [show (5:ℤ) ≤ p by exact_mod_cast hp5]
    omega
  have hcastp2ne3 : ((p : ℤ)^2) ≠ 3 := by
    have : (3:ℤ) < (p:ℤ)^2 := by nlinarith [show (5:ℤ) ≤ p by exact_mod_cast hp5]
    omega
  have hexp : 3 < 3 * r := by nlinarith
  have h3neq : ((p:ℤ)^3) ≠ ((p:ℤ)^(3*r)) := by
    have hlt : p^3 < p^(3*r) := Nat.pow_lt_pow_right hp1 hexp
    exact_mod_cast Nat.ne_of_lt hlt
  have hfunneq : (fun x => (p ^ r).choose x ^ 2 * (p ^ r).multichoose x) ≠
      (fun x => (p ^ (r - 1)).choose x ^ 2 * (p ^ (r - 1)).multichoose x) := by
    intro h
    have h1 := congrFun h 1
    simp [Nat.choose_one_right, Nat.multichoose_one_right] at h1
    have hcube : (p ^ r) ^ 3 = (p ^ (r - 1)) ^ 3 := by simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using h1
    have hlt3 : (p ^ (r - 1)) ^ 3 < (p ^ r) ^ 3 := Nat.pow_lt_pow_left hpowlt (by norm_num)
    exact (Nat.ne_of_gt hlt3) hcube
  grind [a, Int.ModEq, Nat.Prime]
