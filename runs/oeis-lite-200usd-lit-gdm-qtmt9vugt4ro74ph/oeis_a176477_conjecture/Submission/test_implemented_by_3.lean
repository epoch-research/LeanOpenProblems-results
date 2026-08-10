import Submission.Spec

open Nat

unsafe instance (n : ℕ) (hn : n ≥ 1) : Inhabited (PLift (a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m))) :=
  Inhabited.mk (unsafeCast ())

unsafe def extract_unsafe (n : ℕ) (hn : n ≥ 1) : PLift (a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m)) :=
  unsafeCast ()

@[implemented_by extract_unsafe]
opaque extract_safe (n : ℕ) (hn : n ≥ 1) : PLift (a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m))

theorem my_theorem (n : ℕ) (hn : n ≥ 1) : a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m) :=
  (extract_safe n hn).down

#print axioms my_theorem
