import FormalConjectures.Util.ProblemImports

open Nat

def tri' (m : ℕ) : ℕ := m * (m + 1) / 2

def midx' (n : ℕ) : ℕ := Nat.findGreatest (fun m => tri' m ≤ n) n

def nextRow (N k : ℕ) (prev : Array ℤ) : Array ℤ :=
  Array.ofFn (fun n : Fin (N + 1) =>
    if n.val < k + 1 then prev[n.val]!
    else prev[n.val]! - (n.val.choose (k + 1) : ℤ) * prev[n.val - (k + 1)]!)

def row0 (N : ℕ) : Array ℤ :=
  Array.ofFn (fun n : Fin (N + 1) => if n.val = 0 then (1 : ℤ) else 0)

/-- Incremental rows: `rows N (k+1)` extends `rows N k` by one row. -/
def rows (N : ℕ) : ℕ → Array (Array ℤ)
  | 0 => #[row0 N]
  | k + 1 =>
    let prevs := rows N k
    prevs.push (nextRow N k prevs[k]!)

def checkDomFast (K : ℕ) : Bool :=
  let N := tri' K
  let rs := rows N K
  Id.run do
    let mut ok := true
    for k in [0:K+1] do
      let row := rs[k]!
      let trik := tri' k
      for n in [0:trik+1] do
        if k + 1 ≤ n then
          let rest := n - (k + 1)
          let mn := midx' n
          let mr := midx' rest
          if decide (Even mn ↔ Even mr) then
            let gn := ((-1 : ℤ) ^ mn) * row[n]!
            let gr := ((-1 : ℤ) ^ mr) * row[rest]!
            let C : ℤ := n.choose (k + 1)
            if !(C * gr < gn) then
              ok := false
    return ok

-- small sanity
example : checkDomFast 10 = true := by native_decide

example : checkDomFast 80 = true := by native_decide
