import Mathlib

lemma digits_3 (B d0 d1 d2 : ℕ) (hB : 1 < B) 
    (h0 : d0 < B) (h1 : d1 < B) (h2 : d2 < B) (h2_pos : 0 < d2) :
    Nat.digits B (d0 + B * (d1 + B * d2)) = [d0, d1, d2] := by
  have H1 : 0 < d1 + B * d2 := by positivity
  have H1' : d1 + B * d2 ≠ 0 := ne_of_gt H1
  rw [Nat.digits_add B hB d0 (d1 + B * d2) h0 (Or.inr H1')]
  have H2' : d2 ≠ 0 := ne_of_gt h2_pos
  rw [Nat.digits_add B hB d1 d2 h1 (Or.inr H2')]
  rw [Nat.digits_def' hB h2_pos]
  have : d2 / B = 0 := Nat.div_eq_of_lt h2
  rw [this, Nat.digits_zero]
  have : d2 % B = d2 := Nat.mod_eq_of_lt h2
  rw [this]

lemma card_3 (d0 d1 d2 : ℕ) (h01 : d0 ≠ d1) (h02 : d0 ≠ d2) (h12 : d1 ≠ d2) :
    ([d0, d1, d2] : List ℕ).toFinset.card = 3 := by
  simp [List.toFinset_cons, List.toFinset_nil]
  rw [Finset.card_insert_of_notMem]
  · rw [Finset.card_insert_of_notMem]
    · rfl
    · simp [h12]
  · simp [h01, h02]

lemma distinct_digits_3 (B d0 d1 d2 k : ℕ) (hB : 1 < B) 
    (h0 : d0 < B) (h1 : d1 < B) (h2 : d2 < B) (h2_pos : 0 < d2) 
    (hk : k = d0 + B * (d1 + B * d2))
    (h01 : d0 ≠ d1) (h02 : d0 ≠ d2) (h12 : d1 ≠ d2) :
    (Nat.digits B k).toFinset.card > 2 := by
  rw [hk, digits_3 B d0 d1 d2 hB h0 h1 h2 h2_pos]
  rw [card_3 d0 d1 d2 h01 h02 h12]
  omega
