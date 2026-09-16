import Mathlib

open Nat

lemma div_eq_of (X c q : ℕ) (h1 : q * c ≤ X) (h2 : X < (q + 1) * c) : X / c = q := Nat.div_eq_of_lt_le h1 h2

lemma div_ineq_mod_0 (a b c : ℕ) (hc : c > 0) (ha : a < c) (hb : b < c) (h6a1_0 : 0 * c ≤ 6 * a) (h6a2_0 : 6 * a < 1 * c) :
  (6 * a) / c - (3 * a) / c - (2 * a) / c - a / c + ((6 * b) / c - (3 * b) / c - (2 * b) / c - b / c) ≥ (3 * (a + b)) / c - (2 * (a + b)) / c - (a + b) / c := by
  rcases show (0 * c ≤ 6 * b ∧ 6 * b < 1 * c) ∨ (1 * c ≤ 6 * b ∧ 6 * b < 2 * c) ∨ (2 * c ≤ 6 * b ∧ 6 * b < 3 * c) ∨ (3 * c ≤ 6 * b ∧ 6 * b < 4 * c) ∨ (4 * c ≤ 6 * b ∧ 6 * b < 5 * c) ∨ (5 * c ≤ 6 * b ∧ 6 * b < 6 * c) by omega with ⟨h6b1_0, h6b2_0⟩ | ⟨h6b1_1, h6b2_1⟩ | ⟨h6b1_2, h6b2_2⟩ | ⟨h6b1_3, h6b2_3⟩ | ⟨h6b1_4, h6b2_4⟩ | ⟨h6b1_5, h6b2_5⟩
  · have h6a : (6 * a) / c = 0 := div_eq_of _ _ _ h6a1_0 h6a2_0
    have h3a : (3 * a) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 0 := div_eq_of _ _ _ h6b1_0 h6b2_0
    have h3b : (3 * b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (0 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 1 * c) ∨ (1 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 2 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
  · have h6a : (6 * a) / c = 0 := div_eq_of _ _ _ h6a1_0 h6a2_0
    have h3a : (3 * a) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 1 := div_eq_of _ _ _ h6b1_1 h6b2_1
    have h3b : (3 * b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (1 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 2 * c) ∨ (2 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 3 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
  · have h6a : (6 * a) / c = 0 := div_eq_of _ _ _ h6a1_0 h6a2_0
    have h3a : (3 * a) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 2 := div_eq_of _ _ _ h6b1_2 h6b2_2
    have h3b : (3 * b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (2 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 3 * c) ∨ (3 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 4 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
  · have h6a : (6 * a) / c = 0 := div_eq_of _ _ _ h6a1_0 h6a2_0
    have h3a : (3 * a) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 3 := div_eq_of _ _ _ h6b1_3 h6b2_3
    have h3b : (3 * b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (3 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 4 * c) ∨ (4 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 5 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
  · have h6a : (6 * a) / c = 0 := div_eq_of _ _ _ h6a1_0 h6a2_0
    have h3a : (3 * a) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 4 := div_eq_of _ _ _ h6b1_4 h6b2_4
    have h3b : (3 * b) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (4 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 5 * c) ∨ (5 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 6 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
  · have h6a : (6 * a) / c = 0 := div_eq_of _ _ _ h6a1_0 h6a2_0
    have h3a : (3 * a) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 5 := div_eq_of _ _ _ h6b1_5 h6b2_5
    have h3b : (3 * b) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (5 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 6 * c) ∨ (6 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 7 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 3 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega

lemma div_ineq_mod_1 (a b c : ℕ) (hc : c > 0) (ha : a < c) (hb : b < c) (h6a1_1 : 1 * c ≤ 6 * a) (h6a2_1 : 6 * a < 2 * c) :
  (6 * a) / c - (3 * a) / c - (2 * a) / c - a / c + ((6 * b) / c - (3 * b) / c - (2 * b) / c - b / c) ≥ (3 * (a + b)) / c - (2 * (a + b)) / c - (a + b) / c := by
  rcases show (0 * c ≤ 6 * b ∧ 6 * b < 1 * c) ∨ (1 * c ≤ 6 * b ∧ 6 * b < 2 * c) ∨ (2 * c ≤ 6 * b ∧ 6 * b < 3 * c) ∨ (3 * c ≤ 6 * b ∧ 6 * b < 4 * c) ∨ (4 * c ≤ 6 * b ∧ 6 * b < 5 * c) ∨ (5 * c ≤ 6 * b ∧ 6 * b < 6 * c) by omega with ⟨h6b1_0, h6b2_0⟩ | ⟨h6b1_1, h6b2_1⟩ | ⟨h6b1_2, h6b2_2⟩ | ⟨h6b1_3, h6b2_3⟩ | ⟨h6b1_4, h6b2_4⟩ | ⟨h6b1_5, h6b2_5⟩
  · have h6a : (6 * a) / c = 1 := div_eq_of _ _ _ h6a1_1 h6a2_1
    have h3a : (3 * a) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 0 := div_eq_of _ _ _ h6b1_0 h6b2_0
    have h3b : (3 * b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (1 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 2 * c) ∨ (2 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 3 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
  · have h6a : (6 * a) / c = 1 := div_eq_of _ _ _ h6a1_1 h6a2_1
    have h3a : (3 * a) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 1 := div_eq_of _ _ _ h6b1_1 h6b2_1
    have h3b : (3 * b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (2 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 3 * c) ∨ (3 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 4 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
  · have h6a : (6 * a) / c = 1 := div_eq_of _ _ _ h6a1_1 h6a2_1
    have h3a : (3 * a) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 2 := div_eq_of _ _ _ h6b1_2 h6b2_2
    have h3b : (3 * b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (3 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 4 * c) ∨ (4 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 5 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
  · have h6a : (6 * a) / c = 1 := div_eq_of _ _ _ h6a1_1 h6a2_1
    have h3a : (3 * a) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 3 := div_eq_of _ _ _ h6b1_3 h6b2_3
    have h3b : (3 * b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (4 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 5 * c) ∨ (5 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 6 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
  · have h6a : (6 * a) / c = 1 := div_eq_of _ _ _ h6a1_1 h6a2_1
    have h3a : (3 * a) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 4 := div_eq_of _ _ _ h6b1_4 h6b2_4
    have h3b : (3 * b) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (5 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 6 * c) ∨ (6 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 7 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 3 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega
  · have h6a : (6 * a) / c = 1 := div_eq_of _ _ _ h6a1_1 h6a2_1
    have h3a : (3 * a) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 5 := div_eq_of _ _ _ h6b1_5 h6b2_5
    have h3b : (3 * b) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (6 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 7 * c) ∨ (7 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 8 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 3 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 3 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega

lemma div_ineq_mod_2 (a b c : ℕ) (hc : c > 0) (ha : a < c) (hb : b < c) (h6a1_2 : 2 * c ≤ 6 * a) (h6a2_2 : 6 * a < 3 * c) :
  (6 * a) / c - (3 * a) / c - (2 * a) / c - a / c + ((6 * b) / c - (3 * b) / c - (2 * b) / c - b / c) ≥ (3 * (a + b)) / c - (2 * (a + b)) / c - (a + b) / c := by
  rcases show (0 * c ≤ 6 * b ∧ 6 * b < 1 * c) ∨ (1 * c ≤ 6 * b ∧ 6 * b < 2 * c) ∨ (2 * c ≤ 6 * b ∧ 6 * b < 3 * c) ∨ (3 * c ≤ 6 * b ∧ 6 * b < 4 * c) ∨ (4 * c ≤ 6 * b ∧ 6 * b < 5 * c) ∨ (5 * c ≤ 6 * b ∧ 6 * b < 6 * c) by omega with ⟨h6b1_0, h6b2_0⟩ | ⟨h6b1_1, h6b2_1⟩ | ⟨h6b1_2, h6b2_2⟩ | ⟨h6b1_3, h6b2_3⟩ | ⟨h6b1_4, h6b2_4⟩ | ⟨h6b1_5, h6b2_5⟩
  · have h6a : (6 * a) / c = 2 := div_eq_of _ _ _ h6a1_2 h6a2_2
    have h3a : (3 * a) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 0 := div_eq_of _ _ _ h6b1_0 h6b2_0
    have h3b : (3 * b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (2 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 3 * c) ∨ (3 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 4 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
  · have h6a : (6 * a) / c = 2 := div_eq_of _ _ _ h6a1_2 h6a2_2
    have h3a : (3 * a) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 1 := div_eq_of _ _ _ h6b1_1 h6b2_1
    have h3b : (3 * b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (3 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 4 * c) ∨ (4 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 5 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
  · have h6a : (6 * a) / c = 2 := div_eq_of _ _ _ h6a1_2 h6a2_2
    have h3a : (3 * a) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 2 := div_eq_of _ _ _ h6b1_2 h6b2_2
    have h3b : (3 * b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (4 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 5 * c) ∨ (5 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 6 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
  · have h6a : (6 * a) / c = 2 := div_eq_of _ _ _ h6a1_2 h6a2_2
    have h3a : (3 * a) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 3 := div_eq_of _ _ _ h6b1_3 h6b2_3
    have h3b : (3 * b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (5 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 6 * c) ∨ (6 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 7 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 3 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega
  · have h6a : (6 * a) / c = 2 := div_eq_of _ _ _ h6a1_2 h6a2_2
    have h3a : (3 * a) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 4 := div_eq_of _ _ _ h6b1_4 h6b2_4
    have h3b : (3 * b) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (6 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 7 * c) ∨ (7 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 8 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 3 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 3 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega
  · have h6a : (6 * a) / c = 2 := div_eq_of _ _ _ h6a1_2 h6a2_2
    have h3a : (3 * a) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 5 := div_eq_of _ _ _ h6b1_5 h6b2_5
    have h3b : (3 * b) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (7 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 8 * c) ∨ (8 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 9 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 3 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 4 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega

lemma div_ineq_mod_3 (a b c : ℕ) (hc : c > 0) (ha : a < c) (hb : b < c) (h6a1_3 : 3 * c ≤ 6 * a) (h6a2_3 : 6 * a < 4 * c) :
  (6 * a) / c - (3 * a) / c - (2 * a) / c - a / c + ((6 * b) / c - (3 * b) / c - (2 * b) / c - b / c) ≥ (3 * (a + b)) / c - (2 * (a + b)) / c - (a + b) / c := by
  rcases show (0 * c ≤ 6 * b ∧ 6 * b < 1 * c) ∨ (1 * c ≤ 6 * b ∧ 6 * b < 2 * c) ∨ (2 * c ≤ 6 * b ∧ 6 * b < 3 * c) ∨ (3 * c ≤ 6 * b ∧ 6 * b < 4 * c) ∨ (4 * c ≤ 6 * b ∧ 6 * b < 5 * c) ∨ (5 * c ≤ 6 * b ∧ 6 * b < 6 * c) by omega with ⟨h6b1_0, h6b2_0⟩ | ⟨h6b1_1, h6b2_1⟩ | ⟨h6b1_2, h6b2_2⟩ | ⟨h6b1_3, h6b2_3⟩ | ⟨h6b1_4, h6b2_4⟩ | ⟨h6b1_5, h6b2_5⟩
  · have h6a : (6 * a) / c = 3 := div_eq_of _ _ _ h6a1_3 h6a2_3
    have h3a : (3 * a) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 0 := div_eq_of _ _ _ h6b1_0 h6b2_0
    have h3b : (3 * b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (3 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 4 * c) ∨ (4 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 5 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
  · have h6a : (6 * a) / c = 3 := div_eq_of _ _ _ h6a1_3 h6a2_3
    have h3a : (3 * a) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 1 := div_eq_of _ _ _ h6b1_1 h6b2_1
    have h3b : (3 * b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (4 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 5 * c) ∨ (5 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 6 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
  · have h6a : (6 * a) / c = 3 := div_eq_of _ _ _ h6a1_3 h6a2_3
    have h3a : (3 * a) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 2 := div_eq_of _ _ _ h6b1_2 h6b2_2
    have h3b : (3 * b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (5 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 6 * c) ∨ (6 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 7 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 3 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega
  · have h6a : (6 * a) / c = 3 := div_eq_of _ _ _ h6a1_3 h6a2_3
    have h3a : (3 * a) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 3 := div_eq_of _ _ _ h6b1_3 h6b2_3
    have h3b : (3 * b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (6 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 7 * c) ∨ (7 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 8 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 3 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 3 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega
  · have h6a : (6 * a) / c = 3 := div_eq_of _ _ _ h6a1_3 h6a2_3
    have h3a : (3 * a) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 4 := div_eq_of _ _ _ h6b1_4 h6b2_4
    have h3b : (3 * b) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (7 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 8 * c) ∨ (8 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 9 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 3 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 4 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega
  · have h6a : (6 * a) / c = 3 := div_eq_of _ _ _ h6a1_3 h6a2_3
    have h3a : (3 * a) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 5 := div_eq_of _ _ _ h6b1_5 h6b2_5
    have h3b : (3 * b) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (8 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 9 * c) ∨ (9 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 10 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 4 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 4 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 3 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega

lemma div_ineq_mod_4 (a b c : ℕ) (hc : c > 0) (ha : a < c) (hb : b < c) (h6a1_4 : 4 * c ≤ 6 * a) (h6a2_4 : 6 * a < 5 * c) :
  (6 * a) / c - (3 * a) / c - (2 * a) / c - a / c + ((6 * b) / c - (3 * b) / c - (2 * b) / c - b / c) ≥ (3 * (a + b)) / c - (2 * (a + b)) / c - (a + b) / c := by
  rcases show (0 * c ≤ 6 * b ∧ 6 * b < 1 * c) ∨ (1 * c ≤ 6 * b ∧ 6 * b < 2 * c) ∨ (2 * c ≤ 6 * b ∧ 6 * b < 3 * c) ∨ (3 * c ≤ 6 * b ∧ 6 * b < 4 * c) ∨ (4 * c ≤ 6 * b ∧ 6 * b < 5 * c) ∨ (5 * c ≤ 6 * b ∧ 6 * b < 6 * c) by omega with ⟨h6b1_0, h6b2_0⟩ | ⟨h6b1_1, h6b2_1⟩ | ⟨h6b1_2, h6b2_2⟩ | ⟨h6b1_3, h6b2_3⟩ | ⟨h6b1_4, h6b2_4⟩ | ⟨h6b1_5, h6b2_5⟩
  · have h6a : (6 * a) / c = 4 := div_eq_of _ _ _ h6a1_4 h6a2_4
    have h3a : (3 * a) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 0 := div_eq_of _ _ _ h6b1_0 h6b2_0
    have h3b : (3 * b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (4 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 5 * c) ∨ (5 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 6 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
  · have h6a : (6 * a) / c = 4 := div_eq_of _ _ _ h6a1_4 h6a2_4
    have h3a : (3 * a) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 1 := div_eq_of _ _ _ h6b1_1 h6b2_1
    have h3b : (3 * b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (5 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 6 * c) ∨ (6 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 7 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 3 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega
  · have h6a : (6 * a) / c = 4 := div_eq_of _ _ _ h6a1_4 h6a2_4
    have h3a : (3 * a) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 2 := div_eq_of _ _ _ h6b1_2 h6b2_2
    have h3b : (3 * b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (6 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 7 * c) ∨ (7 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 8 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 3 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 3 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega
  · have h6a : (6 * a) / c = 4 := div_eq_of _ _ _ h6a1_4 h6a2_4
    have h3a : (3 * a) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 3 := div_eq_of _ _ _ h6b1_3 h6b2_3
    have h3b : (3 * b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (7 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 8 * c) ∨ (8 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 9 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 3 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 4 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega
  · have h6a : (6 * a) / c = 4 := div_eq_of _ _ _ h6a1_4 h6a2_4
    have h3a : (3 * a) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 4 := div_eq_of _ _ _ h6b1_4 h6b2_4
    have h3b : (3 * b) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (8 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 9 * c) ∨ (9 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 10 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 4 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 4 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 3 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega
  · have h6a : (6 * a) / c = 4 := div_eq_of _ _ _ h6a1_4 h6a2_4
    have h3a : (3 * a) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 5 := div_eq_of _ _ _ h6b1_5 h6b2_5
    have h3b : (3 * b) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (9 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 10 * c) ∨ (10 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 11 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 4 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 3 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 5 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 3 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega

lemma div_ineq_mod_5 (a b c : ℕ) (hc : c > 0) (ha : a < c) (hb : b < c) (h6a1_5 : 5 * c ≤ 6 * a) (h6a2_5 : 6 * a < 6 * c) :
  (6 * a) / c - (3 * a) / c - (2 * a) / c - a / c + ((6 * b) / c - (3 * b) / c - (2 * b) / c - b / c) ≥ (3 * (a + b)) / c - (2 * (a + b)) / c - (a + b) / c := by
  rcases show (0 * c ≤ 6 * b ∧ 6 * b < 1 * c) ∨ (1 * c ≤ 6 * b ∧ 6 * b < 2 * c) ∨ (2 * c ≤ 6 * b ∧ 6 * b < 3 * c) ∨ (3 * c ≤ 6 * b ∧ 6 * b < 4 * c) ∨ (4 * c ≤ 6 * b ∧ 6 * b < 5 * c) ∨ (5 * c ≤ 6 * b ∧ 6 * b < 6 * c) by omega with ⟨h6b1_0, h6b2_0⟩ | ⟨h6b1_1, h6b2_1⟩ | ⟨h6b1_2, h6b2_2⟩ | ⟨h6b1_3, h6b2_3⟩ | ⟨h6b1_4, h6b2_4⟩ | ⟨h6b1_5, h6b2_5⟩
  · have h6a : (6 * a) / c = 5 := div_eq_of _ _ _ h6a1_5 h6a2_5
    have h3a : (3 * a) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 0 := div_eq_of _ _ _ h6b1_0 h6b2_0
    have h3b : (3 * b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (5 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 6 * c) ∨ (6 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 7 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 3 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega
  · have h6a : (6 * a) / c = 5 := div_eq_of _ _ _ h6a1_5 h6a2_5
    have h3a : (3 * a) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 1 := div_eq_of _ _ _ h6b1_1 h6b2_1
    have h3b : (3 * b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (6 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 7 * c) ∨ (7 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 8 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 3 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 3 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega
  · have h6a : (6 * a) / c = 5 := div_eq_of _ _ _ h6a1_5 h6a2_5
    have h3a : (3 * a) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 2 := div_eq_of _ _ _ h6b1_2 h6b2_2
    have h3b : (3 * b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (7 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 8 * c) ∨ (8 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 9 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 3 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 4 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega
  · have h6a : (6 * a) / c = 5 := div_eq_of _ _ _ h6a1_5 h6a2_5
    have h3a : (3 * a) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 3 := div_eq_of _ _ _ h6b1_3 h6b2_3
    have h3b : (3 * b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (8 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 9 * c) ∨ (9 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 10 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 4 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 4 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 3 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega
  · have h6a : (6 * a) / c = 5 := div_eq_of _ _ _ h6a1_5 h6a2_5
    have h3a : (3 * a) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 4 := div_eq_of _ _ _ h6b1_4 h6b2_4
    have h3b : (3 * b) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (9 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 10 * c) ∨ (10 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 11 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 4 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 3 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 5 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 3 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega
  · have h6a : (6 * a) / c = 5 := div_eq_of _ _ _ h6a1_5 h6a2_5
    have h3a : (3 * a) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
    have h2a : (2 * a) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have ha1 : a / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    have h6b : (6 * b) / c = 5 := div_eq_of _ _ _ h6b1_5 h6b2_5
    have h3b : (3 * b) / c = 2 := div_eq_of _ _ _ (by omega) (by omega)
    have h2b : (2 * b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
    have hb1 : b / c = 0 := div_eq_of _ _ _ (by omega) (by omega)
    rcases show (10 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 11 * c) ∨ (11 * c ≤ 6 * (a + b) ∧ 6 * (a + b) < 12 * c) by omega with ⟨h6ab1_0, h6ab2_0⟩ | ⟨h6ab1_1, h6ab2_1⟩
    · have h3ab : (3 * (a + b)) / c = 5 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 3 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega
    · have h3ab : (3 * (a + b)) / c = 5 := div_eq_of _ _ _ (by omega) (by omega)
      have h2ab : (2 * (a + b)) / c = 3 := div_eq_of _ _ _ (by omega) (by omega)
      have hab : (a + b) / c = 1 := div_eq_of _ _ _ (by omega) (by omega)
      omega

lemma div_ineq_mod (a b c : ℕ) (hc : c > 0) (ha : a < c) (hb : b < c) :
  (6 * a) / c - (3 * a) / c - (2 * a) / c - a / c + ((6 * b) / c - (3 * b) / c - (2 * b) / c - b / c) ≥ (3 * (a + b)) / c - (2 * (a + b)) / c - (a + b) / c := by
  rcases show (0 * c ≤ 6 * a ∧ 6 * a < 1 * c) ∨ (1 * c ≤ 6 * a ∧ 6 * a < 2 * c) ∨ (2 * c ≤ 6 * a ∧ 6 * a < 3 * c) ∨ (3 * c ≤ 6 * a ∧ 6 * a < 4 * c) ∨ (4 * c ≤ 6 * a ∧ 6 * a < 5 * c) ∨ (5 * c ≤ 6 * a ∧ 6 * a < 6 * c) by omega with ⟨h6a1_0, h6a2_0⟩ | ⟨h6a1_1, h6a2_1⟩ | ⟨h6a1_2, h6a2_2⟩ | ⟨h6a1_3, h6a2_3⟩ | ⟨h6a1_4, h6a2_4⟩ | ⟨h6a1_5, h6a2_5⟩
  · exact div_ineq_mod_0 a b c hc ha hb h6a1_0 h6a2_0
  · exact div_ineq_mod_1 a b c hc ha hb h6a1_1 h6a2_1
  · exact div_ineq_mod_2 a b c hc ha hb h6a1_2 h6a2_2
  · exact div_ineq_mod_3 a b c hc ha hb h6a1_3 h6a2_3
  · exact div_ineq_mod_4 a b c hc ha hb h6a1_4 h6a2_4
  · exact div_ineq_mod_5 a b c hc ha hb h6a1_5 h6a2_5
