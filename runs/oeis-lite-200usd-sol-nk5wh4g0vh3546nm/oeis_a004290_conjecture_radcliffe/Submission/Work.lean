import FormalConjectures.Util.ProblemImports
open Nat Set

noncomputable def AA (n : ℕ) : ℕ :=
  sInf { m : ℕ | 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 }

def Good (n m : ℕ) : Prop := 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1

lemma digits_pow10 (k : ℕ) : Nat.digits 10 (10^k) = List.replicate k 0 ++ [1] := by
  rw [← show Nat.ofDigits 10 (List.replicate k 0 ++ [1]) = 10^k by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.replicate_succ, List.cons_append, Nat.ofDigits_cons, ih, pow_succ]
      omega]
  apply Nat.digits_ofDigits
  · norm_num
  · aesop
  · simp

lemma good_pow10 (k : ℕ) : Good (10^k) (10^k) := by
  refine ⟨by positivity, dvd_rfl, ?_⟩
  rw [digits_pow10]
  aesop

lemma AA_mem {n : ℕ} (h : ∃ m, Good n m) : Good n (AA n) := by
  change Good n (sInf {m | Good n m})
  exact Nat.sInf_mem h

lemma AA_le {n m : ℕ} (h : Good n m) : AA n ≤ m := by
  change sInf {m | Good n m} ≤ m
  exact Nat.sInf_le h

lemma AA_pow10 (k : ℕ) : AA (10^k) = 10^k := by
  apply Nat.le_antisymm (AA_le (good_pow10 k))
  have h := AA_mem ⟨10^k, good_pow10 k⟩
  exact Nat.le_of_dvd h.1 h.2.1
