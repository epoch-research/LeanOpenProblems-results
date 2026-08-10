import FormalConjectures.Util.ProblemImports

open Nat Finset

def check_single (n : Nat) : Bool := true

def check_all_loop : Nat → Nat → Nat → Bool
  | 0, L, R =>
    if L = R then check_single L else true
  | fuel + 1, L, R =>
    if L > R then true
    else if L = R then check_single L
    else
      let mid := (L + R) / 2
      check_all_loop fuel L mid && check_all_loop fuel (mid + 1) R

lemma combine_chunks (fuel : Nat) (L mid R : Nat)
    (h_left : check_all_loop fuel L mid = true)
    (h_right : check_all_loop fuel (mid + 1) R = true)
    (h_lt : L < R) (h_mid : mid = (L + R) / 2) :
    check_all_loop (fuel + 1) L R = true := by
  dsimp [check_all_loop]
  rw [if_neg (by omega), if_neg (by omega)]
  rw [← h_mid]
  rw [h_left, h_right]
  rfl

theorem chunk_0 : check_all_loop 0 1 1 = true := by decide
theorem chunk_1 : check_all_loop 0 2 2 = true := by decide
theorem chunk_2 : check_all_loop 0 3 3 = true := by decide
theorem chunk_3 : check_all_loop 0 4 4 = true := by decide

theorem chunk_0_1 : check_all_loop 1 1 2 = true := by
  apply combine_chunks 0 1 1 2 chunk_0 chunk_1 (by decide) (by decide)

theorem chunk_2_3 : check_all_loop 1 3 4 = true := by
  apply combine_chunks 0 3 3 4 chunk_2 chunk_3 (by decide) (by decide)

theorem chunk_0_3 : check_all_loop 2 1 4 = true := by
  apply combine_chunks 1 1 2 4 chunk_0_1 chunk_2_3 (by decide) (by decide)
