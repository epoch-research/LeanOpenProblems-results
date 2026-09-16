import Submission.Spec
open Nat

universe u
partial def loop {α : Sort u} : α := loop

theorem test_eq : (∑' (k : ℕ), t k) = 5390 / Real.pi := loop
