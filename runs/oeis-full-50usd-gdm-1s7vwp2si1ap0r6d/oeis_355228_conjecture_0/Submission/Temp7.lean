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
    rcases List.Sublist.eq_nil h_sub with rfl
    simp only [List.length_nil] at h_len
    subst h_len
    dsimp [can_sum] at h_can
    simp only [decide_true, Bool.and_true, Bool.coe_and_iff, Bool.decide_eq_true, true_and] at h_can
    simp only [List.sum_nil]
    omega
  | cons x xs ih =>
    intro k target h_can sub h_sub h_len
    dsimp [can_sum] at h_can
    simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, Bool.coe_and_iff, Bool.decide_eq_true] at h_can
    rcases h_can with ⟨h_opt1, h_opt2⟩
    -- Analyze how sub is a sublist of x :: xs
    cases h_sub with
    | cons _ h_sub' =>
      -- sub is a sublist of xs
      exact ih k target h_opt2 sub h_sub' h_len
    | consCons _ h_sub' =>
      -- sub is x :: sub'
      simp only [List.length_cons] at h_len
      have hk : k > 0 := by omega
      have hk_dec : (k > 0) = true := by simp [hk]
      by_contra hc
      simp only [List.sum_cons] at hc
      have hx_le : x ≤ target := by omega
      have hx_le_dec : (x ≤ target) = true := by simp [hx_le]
      -- Since opt1 is false, and x ≤ target and k > 0, can_sum (k - 1) (target - x) xs must be false
      have h_can_next : can_sum (k - 1) (target - x) xs = false := by
        revert h_opt1
        simp [hx_le_dec, hk_dec]
      have h_sum_sub' : sub.sum = target - x := by omega
      have h_len_sub' : sub.length = k - 1 := by omega
      exact ih (k - 1) (target - x) h_can_next sub h_sub' h_len_sub' h_sum_sub'
