import FormalConjectures.Util.ProblemImports
open Nat

def goodJ (n j : ℕ) : Prop := Nat.Prime (j * 2 ^ n - 1) ∧ Nat.Prime (j * 2 ^ n + 1)

lemma two_pow_mod3_of_pos {n : ℕ} (hn : 0 < n) : 2 ^ n % 3 = if n % 2 = 0 then 1 else 2 := by
  -- not needed now; try omega/norm_num cannot do modular induction immediately
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases h : n = 0
      · subst n; norm_num
      · sorry

-- Computational sanity check: for n=3, only j=9 works below 10.
example : goodJ 3 9 := by norm_num [goodJ]
example : ¬ goodJ 3 1 := by norm_num [goodJ]
example : ¬ goodJ 3 2 := by norm_num [goodJ]
example : ¬ goodJ 3 3 := by norm_num [goodJ]
example : ¬ goodJ 3 4 := by norm_num [goodJ]
example : ¬ goodJ 3 5 := by norm_num [goodJ]
example : ¬ goodJ 3 6 := by norm_num [goodJ]
example : ¬ goodJ 3 7 := by norm_num [goodJ]
example : ¬ goodJ 3 8 := by norm_num [goodJ]
