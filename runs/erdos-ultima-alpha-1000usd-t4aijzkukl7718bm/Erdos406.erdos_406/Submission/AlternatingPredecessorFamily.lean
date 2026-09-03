import Submission.GeneralResidueObstruction

/-! A regular family of predecessors of arbitrarily long ternary-good words.
This diagnoses failed invariant models; no pure-power value is asserted. -/
namespace Erdos406AlternatingPredecessor
open Erdos406Work

def word : ℕ → List ℕ
  | 0 => [2, 1, 0, 1]
  | t + 1 => [2, 0] ++ word t

def value (t : ℕ) : ℕ := Nat.ofDigits 3 (word t).reverse

lemma word_length (t : ℕ) : (word t).length = 2 * t + 4 := by
  induction t with
  | zero => rfl
  | succ t ih => simp [word, ih]; omega

lemma value_succ (t : ℕ) : value (t + 1) = value t + 486 * 9 ^ t := by
  unfold value
  rw [word, List.reverse_append, Nat.ofDigits_append, List.length_reverse, word_length]
  have hp : 3 ^ (2 * t + 4) = 81 * 9 ^ t := by
    rw [pow_add, pow_mul]
    norm_num
    ring
  change Nat.ofDigits 3 (word t).reverse + 3 ^ (2 * t + 4) * 6 =
    Nat.ofDigits 3 (word t).reverse + 486 * 9 ^ t
  rw [hp]
  ring

lemma four_mul_value (t : ℕ) : 4 * value t = 243 * 9 ^ t + 13 := by
  induction t with
  | zero => decide
  | succ t ih => rw [value_succ, pow_succ]; nlinarith

lemma four_mul_value_three (t : ℕ) : 4 * value t = 3 ^ (2 * t + 5) + 13 := by
  rw [four_mul_value, pow_add, pow_mul]
  norm_num
  ring

lemma value_mod_three (t : ℕ) : value t % 3 = 1 := by
  have h := congrArg (fun n : ℕ => n % 3) (four_mul_value t)
  simpa [Nat.add_mod, Nat.mul_mod] using h

lemma four_mul_value_good (t : ℕ) : Nat.digits 3 (4 * value t) ⊆ [0, 1] := by
  rw [four_mul_value_three]
  apply good_add_top_power (by decide +kernel : Nat.digits 3 13 ⊆ [0, 1])
  have hlen : (Nat.digits 3 13).length = 3 := by decide +kernel
  rw [hlen]
  omega

lemma four_mul_value_long (t : ℕ) :
    2 * t + 5 < (Nat.digits 3 (4 * value t)).length := by
  rw [four_mul_value_three, four_digit_formula (by omega : 3 ≤ 2 * t + 5)]
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate]
  omega

/-- A modular period gives infinitely many family indices in the same
residue class as the seed 64. -/
lemma value_period_residue (m P j : ℕ)
    (hP : Nat.ModEq (4 * m) (9 ^ P) 1) :
    Nat.ModEq m (value (P * j)) 64 := by
  have hh := (hP.pow j).mul_left 243 |>.add_right 13
  simp only [one_pow, mul_one] at hh
  rw [← pow_mul, ← four_mul_value] at hh
  norm_num at hh
  exact Nat.ModEq.mul_left_cancel' (by decide : 4 ≠ 0) hh

lemma positive_period (m : ℕ) (hm : 0 < m) (hc : Nat.Coprime 3 m) :
    ∃ P : ℕ, 0 < P ∧ Nat.ModEq (4 * m) (9 ^ P) 1 := by
  refine ⟨Nat.totient (4 * m), Nat.totient_pos.mpr (by positivity), ?_⟩
  apply Nat.ModEq.pow_totient
  exact (by decide : Nat.Coprime 9 4).mul_right (by simpa using hc.pow_left 2)

/-- For every modulus coprime to 3, arbitrarily long members are congruent
to 64, and their fourfold multiples are wholly ternary-good. -/
theorem arbitrary_long_modular_family (m B : ℕ) (hm : 0 < m)
    (hc : Nat.Coprime 3 m) :
    ∃ t : ℕ, B ≤ t ∧ Nat.ModEq m (value t) 64 ∧ value t % 3 = 1 ∧
      Nat.digits 3 (4 * value t) ⊆ [0, 1] ∧
      B < (Nat.digits 3 (4 * value t)).length := by
  obtain ⟨P, hP, hmod⟩ := positive_period m hm hc
  have ht : B ≤ P * (B + 1) := by nlinarith
  refine ⟨P * (B + 1), ht, value_period_residue m P (B + 1) hmod,
    value_mod_three _, four_mul_value_good _, ?_⟩
  have hl := four_mul_value_long (P * (B + 1))
  omega

/-- A language accepting the whole displayed regular family cannot be
multiplication-closed on this residue class while having a uniform good-word
length bound. This is an obstruction to a model, not to the conjecture. -/
theorem family_incompatible_with_guarded_closure (m B : ℕ) (hm : 0 < m)
    (hc : Nat.Coprime 3 m) (P : ℕ → Prop)
    (hfamily : ∀ t, P (value t))
    (hclosed : ∀ n, Nat.ModEq m n 64 → n % 3 = 1 → P n → P (4 * n))
    (hbound : ∀ n, P n → Nat.digits 3 n ⊆ [0, 1] → (Nat.digits 3 n).length ≤ B) :
    False := by
  obtain ⟨t, _, hmod, hthree, hgood, hlong⟩ := arbitrary_long_modular_family m B hm hc
  have hh := hbound _ (hclosed _ hmod hthree (hfamily t)) hgood
  omega

#print axioms four_mul_value_good
#print axioms arbitrary_long_modular_family
#print axioms family_incompatible_with_guarded_closure
end Erdos406AlternatingPredecessor
