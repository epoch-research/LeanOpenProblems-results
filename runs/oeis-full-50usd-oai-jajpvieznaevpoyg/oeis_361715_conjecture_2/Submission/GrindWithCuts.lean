import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 2000000
open Nat Finset

def a (n : ℕ) : ℕ := ∑ k ∈ range n, (n.choose k) ^ 2 * multichoose n k

example (p r : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 2 ≤ r) :
  (a (p ^ r) : ℤ) ≡ a (p ^ (r - 1)) [ZMOD (p ^ (3 * r + 3) : ℕ)] := by
  have hp1 : 1 < p := lt_of_lt_of_le (by norm_num) hp5
  have hrepr : r - 1 + 1 = r := Nat.sub_add_cancel hr
  have hexp : 3 < 3 * r := by nlinarith
  have hnatpow : p ^ 3 < p ^ (3 * r) := Nat.pow_lt_pow_right hp1 hexp
  have h3neq : ((p : ℤ) ^ 3) ≠ ((p : ℤ) ^ (3 * r)) := by
    norm_num [Int.natCast_pow]
    exact ne_of_lt (by exact_mod_cast hnatpow)
  have hrm : r - 1 < r := by omega
  have hpowlt : p ^ (r - 1) < p ^ r := Nat.pow_lt_pow_right hp1 hrm
  have hpowneq : p ^ r ≠ p ^ (r - 1) := by exact ne_of_gt hpowlt
  have hfunneq : (fun x => (p ^ r).choose x ^ 2 * (p ^ r).multichoose x) ≠
      (fun x => (p ^ (r - 1)).choose x ^ 2 * (p ^ (r - 1)).multichoose x) := by
    intro h
    have h1 := congrFun h 1
    simp [Nat.choose_one_right, Nat.multichoose_one_right] at h1
    have : (p ^ r) ^ 3 = (p ^ (r - 1)) ^ 3 := by simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using h1
    have hlt3 : (p ^ (r - 1)) ^ 3 < (p ^ r) ^ 3 := Nat.pow_lt_pow_right (Nat.pos_of_lt hpowlt) hpowlt
    omega
  grind [a, Int.ModEq, Nat.Prime]
