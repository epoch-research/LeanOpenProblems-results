import Submission.Spec
#eval (Finset.product (Finset.range (608 + 1)) (Finset.range (608 + 1))).filter fun xy : ℕ × ℕ =>
    let x := xy.fst
    let y := xy.snd
    let x_sq_y_sq := x * x + y * y
    x_sq_y_sq ≤ 608 ∧
    x ≤ y ∧
    (Nat.Prime (x + 1) ∨ Nat.Prime (y + 1)) ∧
    is_generalized_pentagonal (608 - x_sq_y_sq)
