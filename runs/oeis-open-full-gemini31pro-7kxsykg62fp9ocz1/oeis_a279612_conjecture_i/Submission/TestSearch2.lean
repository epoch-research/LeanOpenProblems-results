import Mathlib
open Nat Finset Int BigOperators

def a (n : ℕ) : ℕ :=
  let B := Nat.sqrt n
  let B_m := 3 * B + 1
  let M := Nat.log 4 B_m
  let powers_of_four : Finset ℕ :=
    (Finset.range (M + 1)).image fun k => 4 ^ k

  (Finset.range (B + 1)).sum fun x =>
  (Finset.range (B + 1)).sum fun y =>
  (Finset.range (B + 1)).sum fun z =>
  (Finset.range (B + 1)).sum fun w =>
    if x^2 + y^2 + z^2 + w^2 = n then
      let m_int : ℤ := (x : ℤ) + 2 * (y : ℤ) - 2 * (z : ℤ)
      if 0 < m_int then
        let m_nat : ℕ := m_int.toNat
        if m_nat ∈ powers_of_four then 1 else 0
      else 0
    else 0

def Q_list : List ℕ := [1, 2, 3, 6, 7, 8, 12, 15, 27, 31, 47, 72, 76, 92, 111, 127]

def main : IO Unit := do
  let mut count := 0
  for n in [1:300] do
    let an := a n
    if an == 0 then
      IO.println s!"Counterexample a({n}) = 0"
      count := count + 1
    if an == 1 then
      let mut tmp := n
      while tmp % 16 == 0 && tmp > 0 do
        tmp := tmp / 16
      if ¬ (Q_list.contains tmp) then
        IO.println s!"Counterexample a({n}) = 1, tmp={tmp}"
        count := count + 1
  IO.println s!"Done! Found {count} counterexamples."
