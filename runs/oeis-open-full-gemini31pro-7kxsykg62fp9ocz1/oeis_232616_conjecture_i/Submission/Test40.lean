import Mathlib

def checkLoop (n v : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | fuel + 1, k, pow2 =>
      let val := if pow2 < k % n then pow2 + n - k % n else pow2 - k % n
      if val == v then false
      else
        let next_pow2 := (pow2 * 2) % n
        checkLoop n v fuel (k + 1) next_pow2

lemma checkLoop_true : checkLoop 550172 13573 16331504 1 (2 % 550172) = true := by
  decide

#print axioms checkLoop_true
