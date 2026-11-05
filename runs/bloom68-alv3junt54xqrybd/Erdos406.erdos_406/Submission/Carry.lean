import Submission.Descent

/-!
# Short-return exclusions for ternary Cantor integers

The compatible multiplier-sixteen machine has no nonzero finite accepting input.
Together with the complete multiplier-sixty-four machine, this bounds chains of
short good returns. No finiteness conjecture is assumed in this file.
-/

namespace Erdos406.Carry

abbrev ternaryGood (n : ℕ) : Prop := Descent.cantor n

lemma good_low (n : ℕ) (hn : ternaryGood n) : n % 3 = 0 ∨ n % 3 = 1 := by
  have hne := Erdos406.Arithmetic.digits_good_digit_ne_two n 0 hn
  have hlt : n % 3 < 3 := Nat.mod_lt _ (by decide)
  simp only [pow_zero, Nat.div_one] at hne
  omega

lemma div_three_good (n : ℕ) (hn : ternaryGood n) : ternaryGood (n / 3) :=
  Erdos406.Arithmetic.digits_good_div_three n hn

lemma mul_add_div_three (n c : ℕ) :
    (16 * n + c) / 3 = 16 * (n / 3) + (16 * (n % 3) + c) / 3 := by
  omega

lemma mul_add_mod_three (n c : ℕ) :
    (16 * n + c) % 3 = (16 * (n % 3) + c) % 3 := by
  omega

lemma sixteen_carry_obstruction (n c : ℕ)
    (hc : c = 0 ∨ c = 2 ∨ c = 5 ∨ c = 6 ∨ c = 7)
    (hn : ternaryGood n) (hm : ternaryGood (16 * n + c)) : n = 0 ∧ c = 0 := by
  induction n using Nat.strong_induction_on generalizing c with
  | h n ih =>
    by_cases hzero : n = 0
    · subst n
      simp only [mul_zero, zero_add] at hm
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact ⟨rfl, rfl⟩
      · exact False.elim ((by decide +kernel : ¬ ternaryGood 2) hm)
      · exact False.elim ((by decide +kernel : ¬ ternaryGood 5) hm)
      · exact False.elim ((by decide +kernel : ¬ ternaryGood 6) hm)
      · exact False.elim ((by decide +kernel : ¬ ternaryGood 7) hm)
    · have hnq := div_three_good n hn
      have hmlow := good_low (16 * n + c) hm
      rw [mul_add_mod_three] at hmlow
      have hmq := div_three_good (16 * n + c) hm
      rw [mul_add_div_three] at hmq
      have hq : n / 3 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hzero) (by decide)
      rcases good_low n hn with hd | hd <;>
        rcases hc with rfl | rfl | rfl | rfl | rfl <;>
        (norm_num [hd] at hmq; norm_num [hd] at hmlow)
      · have hres := ih (n / 3) hq 0 (Or.inl rfl) hnq hmq
        have hnsmall : n = 0 := by omega
        exact ⟨hnsmall, rfl⟩
      · have hres := ih (n / 3) hq 2 (Or.inr (Or.inl rfl)) hnq hmq
        omega
      · have hres := ih (n / 3) hq 2 (Or.inr (Or.inl rfl)) hnq hmq
        omega
      · have hres := ih (n / 3) hq 5 (Or.inr (Or.inr (Or.inl rfl))) hnq hmq
        omega
      · have hres := ih (n / 3) hq 6 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hnq hmq
        omega
      · have hres := ih (n / 3) hq 7 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hnq hmq
        omega
      · have hres := ih (n / 3) hq 7 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hnq hmq
        omega

/-- No positive Cantor integer remains in the Cantor set after multiplication by 16. -/
theorem no_cantor_mul16 (n : ℕ) (hpos : 0 < n) :
    ¬(Descent.cantor n ∧ Descent.cantor (16 * n)) := by
  rintro ⟨hn, hm⟩
  have hz := sixteen_carry_obstruction n 0 (Or.inl rfl) hn (by simpa using hm)
  omega

/-- Good exponents cannot differ by four. -/
theorem goodExponent_gap_four (k : ℕ) (hk : Arithmetic.goodExponent k) :
    ¬Arithmetic.goodExponent (k + 4) := by
  intro h4
  change Descent.cantor (2 ^ (k + 4)) at h4
  have heq : (2 : ℕ) ^ (k + 4) = 16 * 2 ^ k := by
    rw [pow_add]
    norm_num
    ring
  rw [heq] at h4
  exact no_cantor_mul16 (2 ^ k) (by positivity) ⟨hk, h4⟩

/-- A good return at gap six excludes the following short returns. -/
theorem goodExponent_gap_six_exclusions (k : ℕ)
    (hk : Arithmetic.goodExponent k) (h6 : Arithmetic.goodExponent (k + 6)) :
    ¬Arithmetic.goodExponent (k + 2) ∧
    ¬Arithmetic.goodExponent (k + 8) ∧
    ¬Arithmetic.goodExponent (k + 12) := by
  have h64 : Descent.cantor (64 * 2 ^ k) := by
    change Descent.cantor (2 ^ (k + 6)) at h6
    have heq : (2 : ℕ) ^ (k + 6) = 64 * 2 ^ k := by
      rw [pow_add]
      norm_num
      ring
    simpa only [heq] using h6
  have hbad := Descent.multiplier64_exclusions (2 ^ k) (by positivity) hk h64
  have hshift (j m : ℕ) (heq : (2 : ℕ) ^ j = m)
      (h : ¬Descent.cantor (m * 2 ^ k)) : ¬Arithmetic.goodExponent (k + j) := by
    intro hg
    apply h
    change Descent.cantor (2 ^ (k + j)) at hg
    rw [pow_add, heq, mul_comm] at hg
    exact hg
  exact ⟨hshift 2 4 (by decide) hbad.1,
    hshift 8 256 (by decide) hbad.2.1,
    hshift 12 4096 (by decide) hbad.2.2⟩

/-- Two consecutive short returns can only have ascending gaps two and six. -/
theorem two_short_steps_shape (a b c : ℕ)
    (ha : Arithmetic.goodExponent a) (hb : Arithmetic.goodExponent b)
    (hc : Arithmetic.goodExponent c)
    (hab : b = a + 2 ∨ b = a + 6) (hbc : c = b + 2 ∨ c = b + 6) :
    b = a + 2 ∧ c = b + 6 := by
  rcases hab with hab | hab
  · rcases hbc with hbc | hbc
    · have hc4 : Arithmetic.goodExponent (a + 4) := by
        convert hc using 1; omega
      exact False.elim ((goodExponent_gap_four a ha) hc4)
    · exact ⟨hab, hbc⟩
  · have hb6 : Arithmetic.goodExponent (a + 6) := by simpa only [hab] using hb
    have hbad := goodExponent_gap_six_exclusions a ha hb6
    rcases hbc with hbc | hbc
    · have hc8 : Arithmetic.goodExponent (a + 8) := by
        convert hc using 1; omega
      exact False.elim (hbad.2.1 hc8)
    · have hc12 : Arithmetic.goodExponent (a + 12) := by
        convert hc using 1; omega
      exact False.elim (hbad.2.2 hc12)

/-- Conditional bound from eventual short descent.

No threshold satisfying the displayed hypothesis is asserted here. The proof
uses only the unconditional two-short-step classification above.
-/
theorem bounded_of_eventual_short_descent (K : ℕ)
    (hdesc : ∀ k : ℕ, K < k → Arithmetic.goodExponent k →
      ∃ j : ℕ, Arithmetic.goodExponent j ∧ (k = j + 2 ∨ k = j + 6)) :
    ∀ k : ℕ, Arithmetic.goodExponent k → k ≤ K + 8 := by
  intro k hk
  by_contra hlarge
  have hK : K < k := by omega
  obtain ⟨j, hj, hkj⟩ := hdesc k hK hk
  have hjK : K < j := by rcases hkj with hkj | hkj <;> omega
  obtain ⟨i, hi, hji⟩ := hdesc j hjK hj
  have hshape := two_short_steps_shape i j k hi hj hk hji hkj
  have hiK : K < i := by omega
  obtain ⟨l, hl, hil⟩ := hdesc i hiK hi
  have hshape' := two_short_steps_shape l i j hl hi hj hil hji
  omega

/-- Eventual short descent would prove the requested finiteness statement. -/
theorem finite_of_eventual_short_descent (K : ℕ)
    (hdesc : ∀ k : ℕ, K < k → Arithmetic.goodExponent k →
      ∃ j : ℕ, Arithmetic.goodExponent j ∧ (k = j + 2 ∨ k = j + 6)) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  apply Arithmetic.finite_iff_bounded_goodExponents.mpr
  exact ⟨K + 8, bounded_of_eventual_short_descent K hdesc⟩

/-- An exact reformulation of finiteness, not an unconditional settlement. -/
theorem finite_iff_eventual_short_descent :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite ↔
      ∃ K : ℕ, ∀ k : ℕ, K < k → Arithmetic.goodExponent k →
        ∃ j : ℕ, Arithmetic.goodExponent j ∧ (k = j + 2 ∨ k = j + 6) := by
  constructor
  · intro hf
    obtain ⟨K, hK⟩ := Arithmetic.finite_iff_bounded_goodExponents.mp hf
    refine ⟨K, ?_⟩
    intro k hk hgood
    have hbound := hK k hgood
    omega
  · rintro ⟨K, hdesc⟩
    exact finite_of_eventual_short_descent K hdesc

end Erdos406.Carry
