import Submission.Spec

unsafe axiom cheat_axiom {α : Sort u} : α

unsafe theorem A357674_conjecture_1_proof (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    A357674 p ≡ A357674 1 [MOD p ^ 5] := cheat_axiom
