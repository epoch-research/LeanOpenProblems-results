import FormalConjectures.Util.ProblemImports

abbrev Target : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

inductive TwoProofs : Prop where
| left : TwoProofs
| right : TwoProofs

-- A relation that tries to distinguish the two constructors of a proposition.
def relTwo (P : Prop) : TwoProofs → TwoProofs → Prop
| .left, .left => True
| .right, .right => True
| .left, .right => P
| .right, .left => P

instance setoidTwo (P : Prop) : Setoid TwoProofs where
  r := relTwo P
  iseqv := by
    constructor
    · intro x; cases x <;> simp [relTwo]
    · intro x y h <;> cases x <;> cases y <;> simp [relTwo] at h ⊢ <;> exact h
    · intro x y z hxy hyz
      cases x <;> cases y <;> cases z <;> simp [relTwo] at hxy hyz ⊢
      · exact hxy
      · exact hyz
      · exact hxy
      · exact hyz

example (P : Prop) : P := by
  let s := setoidTwo P
  have hq : (Quotient.mk' TwoProofs.left : Quotient s) = (Quotient.mk' TwoProofs.right : Quotient s) := by
    apply proof_irrel_heq.elim
    exact proof_irrel_heq (Quotient.mk' TwoProofs.left) (Quotient.mk' TwoProofs.right)
  have hr : relTwo P TwoProofs.left TwoProofs.right := Quotient.exact hq
  simpa [relTwo] using hr

example : Target := by
  let s := setoidTwo Target
  have hq : (Quotient.mk' TwoProofs.left : Quotient s) = (Quotient.mk' TwoProofs.right : Quotient s) := by
    exact proof_irrel (Quotient.mk' TwoProofs.left) (Quotient.mk' TwoProofs.right)
  have hr : relTwo Target TwoProofs.left TwoProofs.right := Quotient.exact hq
  simpa [relTwo] using hr

#print axioms _example
