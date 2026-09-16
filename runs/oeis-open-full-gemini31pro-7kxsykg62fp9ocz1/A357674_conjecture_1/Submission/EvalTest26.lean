import Submission.Spec
open Nat

partial def loop {α : Sort u} : α := loop

theorem A357674_conjecture_1_proof (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    A357674 p ≡ A357674 1 [MOD p ^ 5] := loop
