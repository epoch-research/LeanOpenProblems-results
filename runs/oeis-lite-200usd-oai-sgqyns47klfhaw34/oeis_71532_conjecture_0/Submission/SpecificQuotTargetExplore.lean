import FormalConjectures.Util.ProblemImports
open BigOperators Int Real
noncomputable def a (n : ℕ) : ℤ :=
  - Finset.sum (Finset.range n) fun k : ℕ =>
      let k_idx : ℕ := k + 1
      let base_real : ℝ := (3 : ℝ) / 2
      let exponent_int : ℤ := floor (base_real ^ k_idx)
      (-1 : ℤ) ^ exponent_int.toNat
abbrev T : Prop := ∃ N : ℕ, ∀ n : ℕ, n ≥ N → (a n : ℝ) > sqrt (n : ℝ)

-- Raw quotient by relation True on Prop proves quotient equality but only EqvGen, not T.
def qr (P Q : Prop) : Prop := True
example : Quot.mk qr True = Quot.mk qr T := Quot.sound trivial
example : Relation.EqvGen qr True T := (Quot.eq).mp (Quot.sound (r:=qr) trivial)
-- Can `grind` or `aesop` accidentally extract T from EqvGen? expected no.
example (h : Relation.EqvGen qr True T) : T := by
  fail_if_success aesop
  fail_if_success grind
  admit
