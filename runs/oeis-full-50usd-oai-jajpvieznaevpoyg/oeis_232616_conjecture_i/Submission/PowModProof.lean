import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0

open Nat

def powMod (a e m : Nat) : Nat :=
  match e with
  | 0 => 1 % m
  | e+1 =>
      let r := powMod ((a*a)%m) ((e+1)/2) m
      if (e+1) % 2 = 0 then r else (r*a)%m
termination_by e

#eval powMod 2 82496875 550172

lemma powMod_lt (a e m : Nat) (hm : m ≠ 0) : powMod a e m < m := by
  induction e using Nat.strong_induction_on generalizing a with
  | h e ih =>
    cases e with
    | zero => simp [powMod, Nat.mod_lt _ (Nat.pos_of_ne_zero hm)]
    | succ e =>
      simp only [powMod]
      split
      · exact ih ((e+1)/2) (Nat.div_lt_self (Nat.succ_pos _) (by norm_num)) _
      · exact Nat.mod_lt _ (Nat.pos_of_ne_zero hm)

lemma powMod_modEq (a e m : Nat) : powMod a e m ≡ a^e [MOD m] := by
  induction e using Nat.strong_induction_on generalizing a with
  | h e ih =>
    cases e with
    | zero => simp [powMod, Nat.ModEq]
    | succ e =>
      simp only [powMod]
      let q := (e + 1) / 2
      have hlt : q < e + 1 := Nat.div_lt_self (Nat.succ_pos _) (by norm_num)
      have ih' : powMod ((a * a) % m) q m ≡ ((a * a) % m) ^ q [MOD m] := ih q hlt ((a*a)%m)
      have hbase : ((a * a) % m) ^ q ≡ (a * a) ^ q [MOD m] :=
        Nat.ModEq.pow q (Nat.mod_modEq (a * a) m)
      have hsq : (a * a) ^ q = a ^ (2 * q) := by
        rw [mul_comm a a, ← sq]
        simp [sq, pow_mul]
      by_cases heven : (e + 1) % 2 = 0
      · simp [heven]
        have hn : e + 1 = 2 * q := by
          have := Nat.div_add_mod (e+1) 2
          omega
        exact ih'.trans <| hbase.trans <| by rw [hsq, hn]
      · have hmod : (e + 1) % 2 = 1 := by omega
        simp [heven]
        have hn : e + 1 = 2 * q + 1 := by
          have := Nat.div_add_mod (e+1) 2
          omega
        have hmul := (ih'.trans hbase).mul_right a
        have htarget : (a * a) ^ q * a = a ^ (e + 1) := by
          rw [hsq, hn]
          rw [pow_succ]
        exact (Nat.mod_modEq _ _).trans (hmul.trans (by rw [htarget]))

lemma powMod_eq_mod_of_pos (a e m : Nat) (hm : m ≠ 0) : powMod a e m = a^e % m := by
  have h := powMod_modEq a e m
  rw [Nat.ModEq] at h
  rw [Nat.mod_eq_of_lt (powMod_lt a e m hm)] at h
  exact h
