import FormalConjectures.Util.ProblemImports

open Nat

set_option maxRecDepth 1000000

def powMod (a e m : ℕ) : ℕ :=
  if h0 : e = 0 then 1 % m
  else if h2 : e % 2 = 0 then
    let r := powMod a (e / 2) m
    (r * r) % m
  else
    (a * powMod a (e - 1) m) % m
termination_by e
decreasing_by
  · have hepos : 0 < e := Nat.pos_of_ne_zero h0
    exact Nat.div_lt_self hepos (by norm_num)
  · omega

lemma powMod_eq (a e m : ℕ) : powMod a e m = a ^ e % m := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    by_cases h0 : e = 0
    · subst e
      simp [powMod]
    · by_cases h2 : e % 2 = 0
      · simp [powMod, h0, h2]
        have hepos : 0 < e := Nat.pos_of_ne_zero h0
        have hhalf : e / 2 < e := Nat.div_lt_self hepos (by norm_num)
        rw [ih (e/2) hhalf]
        have heq : e = 2 * (e / 2) := by
          have := Nat.div_add_mod e 2
          omega
        rw [heq]
        rw [pow_mul]
        norm_num
        simp [Nat.mul_mod, Nat.mod_mod, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      · simp [powMod, h0, h2]
        have hpred : e - 1 < e := by omega
        rw [ih (e-1) hpred]
        have heq : e = (e - 1) + 1 := by omega
        rw [heq]
        simp [pow_succ, Nat.mul_mod, Nat.mod_mod, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

