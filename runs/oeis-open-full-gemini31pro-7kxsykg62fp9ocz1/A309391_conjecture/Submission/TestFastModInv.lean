def gcd_ext_loop (steps : Nat) (a b : Int) (x0 x1 y0 y1 : Int) : Int :=
  match steps with
  | 0 => x0
  | s + 1 =>
    if b == 0 then x0
    else
      let q := a / b
      let r := a % b
      gcd_ext_loop s b r x1 (x0 - q * x1) y1 (y0 - q * y1)

def modInverse (a mod : Nat) : Nat :=
  let x := gcd_ext_loop 100 a mod 1 0 0 1
  let x_nat := (x % mod)
  if x_nat < 0 then (x_nat + mod).toNat else x_nat.toNat

def sum_bin (depth : Nat) (a : Nat) : Nat :=
  match depth with
  | 0 => if a > 0 ∧ a < 16843 then modInverse a 4777853153507 else 0
  | d + 1 =>
    let n1 := sum_bin d a
    let n2 := sum_bin d (a + (1 <<< d))
    (n1 + n2) % 4777853153507

set_option maxHeartbeats 1000000000
theorem t : sum_bin 15 0 == 0 := by decide
