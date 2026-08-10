import FormalConjectures.Util.ProblemImports

abbrev Target : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

noncomputable def relP (P : Prop) : Bool → Bool → Prop := fun x y => x = y ∨ P

noncomputable def setoidP (P : Prop) : Setoid Bool where
  r := relP P
  iseqv := by
    constructor
    · intro x; left; rfl
    · intro x y h; rcases h with h|h
      · left; exact h.symm
      · right; exact h
    · intro x y z hxy hyz
      rcases hxy with hxy|hp
      · rcases hyz with hyz|hp2
        · left; exact hxy.trans hyz
        · right; exact hp2
      · right; exact hp

#synth Subsingleton (Quotient (setoidP Target))
#synth DecidableEq (Quotient (setoidP Target))

example (P : Prop) (h : (Quotient.mk (setoidP P) false) = (Quotient.mk (setoidP P) true)) : P := by
  have hr : relP P false true := Quotient.exact h
  rcases hr with hft | hp
  · cases hft
  · exact hp

example : Target := by
  apply (show (Quotient.mk (setoidP Target) false) = (Quotient.mk (setoidP Target) true) → Target from ?_)
  intro h
  exact (by
    have hr : relP Target false true := Quotient.exact h
    rcases hr with hft | hp
    · cases hft
    · exact hp)
  -- need equality of quotient classes
