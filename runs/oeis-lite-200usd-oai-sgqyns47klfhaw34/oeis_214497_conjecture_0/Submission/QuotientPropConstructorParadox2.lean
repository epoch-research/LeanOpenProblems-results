import FormalConjectures.Util.ProblemImports

abbrev Target : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

inductive TwoProofs : Prop where
| left : TwoProofs
| right : TwoProofs

#check TwoProofs.casesOn

def relTwo (P : Prop) (a b : TwoProofs) : Prop :=
  TwoProofs.casesOn (motive := fun _ => Prop) a
    (TwoProofs.casesOn (motive := fun _ => Prop) b True P)
    (TwoProofs.casesOn (motive := fun _ => Prop) b P True)

example (P : Prop) : relTwo P TwoProofs.left TwoProofs.right = P := rfl
example (P : Prop) : relTwo P TwoProofs.left TwoProofs.left = True := rfl

instance setoidTwo (P : Prop) : Setoid TwoProofs where
  r := relTwo P
  iseqv := by
    constructor
    · intro x
      cases x <;> rfl
    · intro x y h
      cases x <;> cases y <;> simp [relTwo] at h ⊢ <;> exact h
    · intro x y z hxy hyz
      cases x <;> cases y <;> cases z <;> simp [relTwo] at hxy hyz ⊢
      · exact hxy
      · exact hyz
      · exact hxy
      · exact hyz

example (P : Prop) : P := by
  let s := setoidTwo P
  have hq : (Quotient.mk' TwoProofs.left : Quotient s) = (Quotient.mk' TwoProofs.right : Quotient s) := by
    exact proof_irrel (Quotient.mk' TwoProofs.left) (Quotient.mk' TwoProofs.right)
  have hr : relTwo P TwoProofs.left TwoProofs.right := Quotient.exact hq
  simpa [relTwo] using hr

example : Target := by
  let s := setoidTwo Target
  have hq : (Quotient.mk' TwoProofs.left : Quotient s) = (Quotient.mk' TwoProofs.right : Quotient s) := by
    exact proof_irrel (Quotient.mk' TwoProofs.left) (Quotient.mk' TwoProofs.right)
  have hr : relTwo Target TwoProofs.left TwoProofs.right := Quotient.exact hq
  simpa [relTwo] using hr

theorem target_from_quotient_paradox : Target := by
  let s := setoidTwo Target
  have hq : (Quotient.mk' TwoProofs.left : Quotient s) = (Quotient.mk' TwoProofs.right : Quotient s) := by
    exact proof_irrel (Quotient.mk' TwoProofs.left) (Quotient.mk' TwoProofs.right)
  have hr : relTwo Target TwoProofs.left TwoProofs.right := Quotient.exact hq
  simpa [relTwo] using hr

#print axioms target_from_quotient_paradox
