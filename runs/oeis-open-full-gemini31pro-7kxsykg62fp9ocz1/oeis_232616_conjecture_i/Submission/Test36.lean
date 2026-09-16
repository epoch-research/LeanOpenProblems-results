import Mathlib

def checkLoop (n bound v : ℕ) : Bool :=
  let rec loop (k : ℕ) (pow2 : ℕ) : Bool :=
    if h : k > bound then true
    else
      let val := if pow2 < k % n then pow2 + n - k % n else pow2 - k % n
      if val == v then false
      else
        let next_pow2 := (pow2 * 2) % n
        have : bound + 1 - (k + 1) < bound + 1 - k := by omega
        loop (k + 1) next_pow2
  termination_by bound + 1 - k
  loop 1 (2 % n)

#eval checkLoop 550172 16331504 13573
