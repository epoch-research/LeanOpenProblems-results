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

def main : IO Unit := do
  IO.println s!"a(127) = {a 127}"
