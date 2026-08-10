import FormalConjectures.Util.ProblemImports

open Nat Finset

def check_single (bytes : ByteArray) (n : Nat) : Bool := true

def check_all_loop (bytes : ByteArray) : Nat → Nat → Nat → Bool
  | 0, L, R =>
    if L = R then check_single bytes L else true
  | fuel + 1, L, R =>
    if L > R then true
    else if L = R then check_single bytes L
    else
      let mid := (L + R) / 2
      check_all_loop bytes fuel L mid && check_all_loop bytes fuel (mid + 1) R

lemma combine_chunks (s : ByteArray) (fuel : Nat) (L mid R : Nat)
    (h_left : check_all_loop s fuel L mid = true)
    (h_right : check_all_loop s fuel (mid + 1) R = true)
    (h_lt : L < R) (h_mid : mid = (L + R) / 2) :
    check_all_loop s (fuel + 1) L R = true := by
  dsimp [check_all_loop]
  rw [if_neg (by omega), if_neg (by omega)]
  rw [← h_mid]
  rw [h_left, h_right]
  rfl
