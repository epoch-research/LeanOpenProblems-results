import FormalConjectures.Util.ProblemImports

open Nat

def search_loop (B n : ℕ) (i : ℕ) : Option (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  match i with
  | 0 => none
  | i + 1 =>
    let w := i / (B * B)
    let z := (i / B) % B
    let y := i % B
    if w * w + z * z + y * y ≤ n then
      let x2 := n - (w * w + z * z + y * y)
      let x := x2.sqrt
      if x * x == x2 then
        if x ≥ y then
          let S2 := x * x + 8 * y * y + 16 * z * z
          let S := S2.sqrt
          if S * S == S2 then
            some (x, y, z, w, S)
          else
            search_loop B n i
        else
          search_loop B n i
      else
        search_loop B n i
    else
      search_loop B n i

def find_sol_fast (n : ℕ) : Option (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  let B := n.sqrt + 1
  search_loop B n (B * B * B)

#eval find_sol_fast 1630
