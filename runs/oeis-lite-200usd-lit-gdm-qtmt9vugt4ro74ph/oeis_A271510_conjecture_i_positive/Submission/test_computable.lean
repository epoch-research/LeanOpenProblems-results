import Mathlib

open Nat

set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

def binary_sqrt_aux (n low high fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => low
  | fuel' + 1 =>
    if low + 1 ≥ high then low
    else
      let mid := (low + high) / 2
      if mid * mid ≤ n then binary_sqrt_aux n mid high fuel'
      else binary_sqrt_aux n low mid fuel'

def fast_sqrt (n : ℕ) : ℕ :=
  binary_sqrt_aux n 0 (n + 1) 32

def search_z (q x y z : ℕ) : Option (ℕ × ℕ) :=
  match z with
  | 0 => none
  | z' + 1 =>
    let z := z'
    if x^2 + y^2 + z^2 = q then
      let val := x^2 + 8*y^2 + 16*z^2
      let r := fast_sqrt val
      if r * r = val then
        some (z, r)
      else
        search_z q x y z'
    else
      search_z q x y z'

def search_y (q x y : ℕ) : Option (ℕ × ℕ × ℕ × ℕ) :=
  match y with
  | 0 => none
  | y' + 1 =>
    let y := y'
    if x^2 + y^2 ≤ q then
      let q_sqrt := fast_sqrt q
      match search_z q x y (q_sqrt + 1) with
      | some (z, r) => some (x, y, z, r)
      | none => search_y q x y'
    else
      search_y q x y'

def search_x (q x : ℕ) : Option (ℕ × ℕ × ℕ × ℕ) :=
  match x with
  | 0 => none
  | x' + 1 =>
    let x := x'
    if x^2 ≤ q then
      match search_y q x (x + 1) with
      | some sol => some sol
      | none => search_x q x'
    else
      search_x q x'

def find_H0_sol (q : ℕ) : Option (ℕ × ℕ × ℕ × ℕ) :=
  let q_sqrt := fast_sqrt q
  search_x q (q_sqrt + 1)

lemma find_H0_sol_correct_bounded : ∀ (q : ℕ), q ≤ 500 →
  (find_H0_sol q).isSome = true →
  let s := (find_H0_sol q).getD (0, 0, 0, 0)
  s.1^2 + s.2.1^2 + s.2.2.1^2 = q ∧ s.1 ≥ s.2.1 ∧ s.2.2.2^2 = s.1^2 + 8*s.2.1^2 + 16*s.2.2.1^2 := by
  decide
