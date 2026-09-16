import Mathlib
open Nat Finset Int

def a (n : ℕ) : ℤ :=
  (Finset.range (n + 1)).sum fun k : ℕ =>
    (-4 : ℤ) ^ k * (choose n k : ℤ) ^ 2 * (choose (n - k) k : ℤ) ^ 2

def check1 (n : ℕ) : Bool :=
  if n = 0 then true else
  let S := (Finset.range n).sum fun k : ℕ => (20 * (k : ℤ) + 17) * a k
  S % (n : ℤ) == 0

def check2 (p : ℕ) [Fact (Nat.Prime p)] : Bool :=
  if p = 2 then true else
  let S := (Finset.range p).sum fun k : ℕ => (20 * (k : ℤ) + 17) * a k
  let L := legendreSym p (-1)
  (S - (p : ℤ) * (10 * L + 7)) % ((p : ℤ) ^ 2) == 0

#eval! (List.range 20).all check1

#eval! show Bool from let _i : Fact (Nat.Prime 3) := ⟨by decide⟩; check2 3
#eval! show Bool from let _i : Fact (Nat.Prime 5) := ⟨by decide⟩; check2 5
#eval! show Bool from let _i : Fact (Nat.Prime 7) := ⟨by decide⟩; check2 7
#eval! show Bool from let _i : Fact (Nat.Prime 11) := ⟨by decide⟩; check2 11
#eval! show Bool from let _i : Fact (Nat.Prime 13) := ⟨by decide⟩; check2 13
