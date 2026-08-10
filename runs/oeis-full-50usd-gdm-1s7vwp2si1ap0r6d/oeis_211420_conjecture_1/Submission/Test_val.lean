import FormalConjectures.Util.ProblemImports

open Nat

lemma sum_indicator_eq_self_base (v : ℕ) :
    (Finset.Ico 1 (v + 1)).sum (fun i => if i ≤ v then 1 else 0) = v := by
  induction v with
  | zero => simp
  | succ v ih =>
    rw [Finset.sum_Ico_succ_top (by omega)]
    have : (if v + 1 ≤ v + 1 then 1 else 0) = 1 := by simp
    rw [this]
    have h_eq : (Finset.Ico 1 (v + 1)).sum (fun i => if i ≤ v + 1 then 1 else 0) =
                (Finset.Ico 1 (v + 1)).sum (fun i => if i ≤ v then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mem_Ico] at hx
      have h1 : x ≤ v + 1 := by omega
      have h2 : x ≤ v := by omega
      rw [if_pos h1, if_pos h2]
    rw [h_eq, ih]

lemma sum_indicator_eq_self (v b : ℕ) (h : v < b) :
    (Finset.Ico 1 b).sum (fun i => if i ≤ v then 1 else 0) = v := by
  induction b with
  | zero => omega
  | succ b ih =>
    by_cases hb : v < b
    · rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ b)]
      have : (if b ≤ v then 1 else 0) = 0 := by simp [hb]
      rw [this, add_zero]
      exact ih hb
    · have : b = v := by omega
      subst this
      exact sum_indicator_eq_self_base b
