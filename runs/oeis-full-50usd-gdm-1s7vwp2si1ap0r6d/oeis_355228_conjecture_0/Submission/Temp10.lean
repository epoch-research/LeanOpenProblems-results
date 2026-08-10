import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 1000000
open Finset Nat Set

def can_sum (k : ℕ) (target : ℕ) : List ℕ → Bool
  | [] => k == 0 && target == 0
  | x :: xs =>
    (x ≤ target && k > 0 && can_sum (k - 1) (target - x) xs) || can_sum k target xs

lemma can_sum_false_induction (l : List ℕ) : ∀ (k : ℕ) (target : ℕ) (h_can : can_sum k target l = false)
  (sub : List ℕ) (h_sub : sub.Sublist l) (h_len : sub.length = k), sub.sum ≠ target := by
  induction l with
  | nil =>
    intro k target h_can sub h_sub h_len
    have h_nil := List.eq_nil_of_sublist_nil h_sub
    subst h_nil
    simp only [List.length_nil] at h_len
    subst h_len
    dsimp [can_sum] at h_can
    by_contra hc
    simp only [List.sum_nil] at hc
    subst hc
    simp at h_can
  | cons x xs ih =>
    intro k target h_can sub h_sub h_len
    dsimp [can_sum] at h_can
    rw [Bool.or_eq_false_iff] at h_can
    rcases h_can with ⟨h_opt1, h_opt2⟩
    cases h_sub with
    | cons _ h_sub' =>
      exact ih k target h_opt2 sub h_sub' h_len
    | cons₂ _ h_sub' =>
      rename_i tail
      simp only [List.length_cons] at h_len
      have hk : k > 0 := by omega
      by_contra hc
      simp only [List.sum_cons] at hc
      have hx_le : x ≤ target := by omega
      have h_can_next : can_sum (k - 1) (target - x) xs = false := by
        revert h_opt1
        have h1 : (x ≤ target) = true := by simp [hx_le]
        have h2 : (k > 0) = true := by simp [hk]
        simp [h1, h2]
      have h_sum_sub' : tail.sum = target - x := by omega
      have h_len_sub' : tail.length = k - 1 := by omega
      exact ih (k - 1) (target - x) h_can_next tail h_sub' h_len_sub' h_sum_sub'
