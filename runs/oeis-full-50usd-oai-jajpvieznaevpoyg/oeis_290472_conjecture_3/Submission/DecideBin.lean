import FormalConjectures.Util.ProblemImports
open Nat
abbrev Triple := ℕ × ℕ × ℕ

def bsSq (fuel lo hi q : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel'+1 =>
    let mid := (lo + hi) / 2
    let m2 := mid * mid
    if m2 = q then true
    else if m2 < q then bsSq fuel' (mid+1) hi q
    else bsSq fuel' lo mid q

def isSq (q : Nat) : Bool := bsSq 12 0 1201 q

def repB (N : ℕ) (t : Triple) : Bool :=
  let x := t.1; let y := t.2.1; let z := t.2.2
  decide (0 < x) && decide (x*x + 3*y*y + 7*z*z = N)

def upd (N : ℕ) (x z q : Nat) (fst : Option Triple) : Sum (Triple × Triple) (Option Triple) :=
  if isSq q then
    let y := Nat.sqrt q
    -- Nat.sqrt only used to build witness, not in the Boolean? repB will verify it, but decide may get stuck.
    updSorry
  else Sum.inr fst
