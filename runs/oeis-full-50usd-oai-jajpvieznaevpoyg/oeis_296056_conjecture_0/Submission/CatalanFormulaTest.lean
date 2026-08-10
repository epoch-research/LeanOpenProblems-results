import FormalConjectures.Util.ProblemImports
open Nat
#check catalan_eq_centralBinom_div
#check succ_mul_catalan_eq_centralBinom
#check Nat.centralBinom_eq_two_mul_choose
#check Nat.cast_choose

lemma catalan_cast_formula (m : ℕ) : (catalan m : ℚ) = (Nat.choose (2*m) m : ℚ) / ((m+1:ℕ):ℚ) := by
  have h : ((m+1) * catalan m : ℕ) = Nat.centralBinom m := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using succ_mul_catalan_eq_centralBinom m
  have hc : Nat.centralBinom m = Nat.choose (2*m) m := by
    rfl
  have hm : (((m+1:ℕ):ℚ) ≠ 0) := by positivity
  rw [← hc] 
  have hq : ((m+1:ℕ):ℚ) * (catalan m : ℚ) = (Nat.centralBinom m : ℚ) := by
    norm_num [Nat.cast_mul]
    exact_mod_cast h
  field_simp [hm]
  nlinarith
