import FormalConjectures.Util.ProblemImports

open Nat Finset

namespace MDev

/-- `M r S a` = number of set partitions of an `S`-element set into `r` blocks of
distinct sizes, each of size `≥ a`. Recursion: peel off (or not) a block of size exactly `a`. -/
def M : ℕ → ℕ → ℕ → ℕ
  | 0, S, _ => if S = 0 then 1 else 0
  | (r+1), S, a => if a > S then 0 else (S.choose a) * M r (S - a) (a+1) + M (r+1) S (a+1)
  termination_by r S a => (r, S + 1 - a)
  decreasing_by
    · exact Prod.Lex.left _ _ (Nat.lt_succ_self r)
    · refine Prod.Lex.right _ ?_
      have : a ≤ S := Nat.le_of_not_lt (by simpa using ‹¬ a > S›)
      omega

@[simp] lemma M_zero (S a : ℕ) : M 0 S a = if S = 0 then 1 else 0 := by
  rw [M]

lemma M_succ_of_lt {r S a : ℕ} (h : S < a) : M (r+1) S a = 0 := by
  rw [M]; simp [h]

lemma M_succ {r S a : ℕ} (h : a ≤ S) :
    M (r+1) S a = (S.choose a) * M r (S - a) (a+1) + M (r+1) S (a+1) := by
  rw [M]; simp [Nat.not_lt.2 h]

/-- `tri r a = a + (a+1) + ... + (a+r-1)`, the minimal sum of `r` distinct parts each `≥ a`. -/
def tri (r a : ℕ) : ℕ := r * a + r * (r - 1) / 2

end MDev

