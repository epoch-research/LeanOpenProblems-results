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

theorem land_le_right : ∀ a b : Nat, a &&& b ≤ b := by
  intro a
  induction a using Nat.binaryRec with
  | zero => intro b; simp
  | bit abit a ih =>
      intro b
      cases b using Nat.bitCasesOn with
      | bit bbit b =>
          specialize ih b
          change (Nat.bit abit a &&& Nat.bit bbit b) ≤ Nat.bit bbit b
          rw [Nat.land_bit]
          cases abit <;> cases bbit <;> simp [Nat.bit] <;> omega

theorem xor_square_of_land_eq {k M t : Nat}
    (hM : M = 2*t + 1) (h : k + (k^2 &&& M) = t) :
    Nat.xor (k ^ 2) ((k + 1) ^ 2) = M := by
  let d := k^2 &&& M
  have hk_le_t : k ≤ t := by omega
  have hd_eq : d = t - k := by omega
  have hsum : (k + 1)^2 + 2*d = k^2 + M := by
    rw [hM, hd_eq]
    nlinarith [hk_le_t]
  have hx := xor_add_two_land (k^2) M
  have hx' : (k^2 ^^^ M) = (k+1)^2 := by
    have hx2 : (k^2 ^^^ M) + 2*d = k^2 + M := by
      convert hx using 1
    exact Nat.add_right_cancel (hx2.trans hsum.symm)
  change k^2 ^^^ (k+1)^2 = M
  rw [← hx']
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
