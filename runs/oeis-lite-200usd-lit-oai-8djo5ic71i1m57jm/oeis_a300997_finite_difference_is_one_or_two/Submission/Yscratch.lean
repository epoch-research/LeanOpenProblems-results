import FormalConjectures.Util.ProblemImports
open Nat

def Y : ℕ → ℕ → ℕ → ℕ
  | N, 0, k => if k + 1 < N then k + 1 else 0
  | N, t+1, k => if k + 1 < N then (Y N t k + Y N t (k+1)) / 2 else 0

lemma Y_first_le_one (N t) : Y N t 0 ≤ 1 := by
  induction t generalizing N with
  | zero => simp [Y]; omega
  | succ t ih =>
      simp [Y]
      split
      · have h0 := ih N
        have h1 : Y N t 1 ≤ 2 := by
          -- need general bound
          sorry
        omega
      · omega

lemma Y_bound (N t k) : Y N t k ≤ k+1 := by
  induction t generalizing N k with
  | zero => simp [Y]; split <;> omega
  | succ t ih =>
      simp [Y]
      split
      · have h0 := ih N k
        have h1 := ih N (k+1)
        omega
      · omega

lemma Y_lower_gen (N t k) : k < N → Y N t k ≤ Y (N+1) (t+1) k := by
  induction t generalizing N k with
  | zero =>
      intro hk
      simp [Y]
      split <;> split <;> omega
  | succ t ih =>
      intro hk
      simp [Y]
      have hkN : k + 1 < N + 1 := by omega
      simp [hkN]
      by_cases hk1 : k + 1 < N
      · simp [hk1]
        have h0 := ih N k hk
        have h1 := ih N (k+1) hk1
        omega
      · simp [hk1]
        omega

lemma Y_upper_first (N t) : Y (N+1) (t+2) 0 ≤ Y N t 0 := by
  induction t generalizing N with
  | zero =>
      simp [Y]
      split <;> omega
  | succ t ih =>
      simp [Y]
      -- ?
      sorry
