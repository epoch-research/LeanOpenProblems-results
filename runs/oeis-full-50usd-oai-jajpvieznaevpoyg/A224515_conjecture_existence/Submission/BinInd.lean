import FormalConjectures.Util.ProblemImports
open Nat
set_option linter.unusedSimpArgs false

theorem xor_add_two_land : ∀ a b : Nat, (a ^^^ b) + 2*(a &&& b) = a + b := by
  intro a
  induction a using Nat.binaryRec with
  | zero => intro b; simp
  | bit abit a ih =>
      intro b
      cases b using Nat.bitCasesOn with
      | bit bbit b =>
          specialize ih b
          cases abit <;> cases bbit
          all_goals
            simp only [Nat.xor_bit, Nat.land_bit, Bool.false_eq_true, Bool.true_eq_false,
              Bool.false_bne, Bool.true_bne, Bool.bne_false, Bool.bne_true]
            simp [Nat.bit, ih]
            omega
