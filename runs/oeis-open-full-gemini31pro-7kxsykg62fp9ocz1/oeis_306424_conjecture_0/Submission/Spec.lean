import Mathlib
import FormalConjectures.Util.ProblemImports

open List Finset Nat

def A306424_condition (k : ℕ) : Prop :=
  ∀ b : ℕ, 3 ≤ b ∧ b < k → ((Nat.digits b k).toFinset.card) ≤ 2

noncomputable def a (n : ℕ) : ℕ := n.nth A306424_condition

def check_cond (k : ℕ) : Bool :=
  (List.range k).all (fun b => b < 3 || (Nat.digits b k).toFinset.card ≤ 2)

lemma cond_of_check_cond_true (k : ℕ) (h : check_cond k = true) : A306424_condition k := by
  intro b ⟨h3, hk⟩
  dsimp [check_cond] at h
  rw [List.all_eq_true] at h
  have hb := h b (by simp [hk])
  have hnot : ¬ (b < 3) := by omega
  simp [hnot] at hb
  exact hb


lemma digits_3 (B d0 d1 d2 : ℕ) (hB : 1 < B) 
    (h0 : d0 < B) (h1 : d1 < B) (h2 : d2 < B) (h2_pos : 0 < d2) :
    Nat.digits B (d0 + B * (d1 + B * d2)) = [d0, d1, d2] := by
  have H1 : 0 < d1 + B * d2 := by positivity
  have H1' : d1 + B * d2 ≠ 0 := Nat.ne_of_gt H1
  rw [Nat.digits_add B hB d0 (d1 + B * d2) h0 (Or.inr H1')]
  have H2' : d2 ≠ 0 := Nat.ne_of_gt h2_pos
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

lemma digits_4 (B d0 d1 d2 d3 : ℕ) (hB : 1 < B) 
    (h0 : d0 < B) (h1 : d1 < B) (h2 : d2 < B) (h3 : d3 < B) (h3_pos : 0 < d3) :
    Nat.digits B (d0 + B * (d1 + B * (d2 + B * d3))) = [d0, d1, d2, d3] := by
  have H1 : 0 < d1 + B * (d2 + B * d3) := by positivity
  have H1' : d1 + B * (d2 + B * d3) ≠ 0 := Nat.ne_of_gt H1
  rw [Nat.digits_add B hB d0 (d1 + B * (d2 + B * d3)) h0 (Or.inr H1')]
  have H2 : 0 < d2 + B * d3 := by positivity
  have H2' : d2 + B * d3 ≠ 0 := Nat.ne_of_gt H2
  rw [Nat.digits_add B hB d1 (d2 + B * d3) h1 (Or.inr H2')]
  have H3' : d3 ≠ 0 := Nat.ne_of_gt h3_pos
  rw [Nat.digits_add B hB d2 d3 h2 (Or.inr H3')]
  rw [Nat.digits_def' hB h3_pos]
  have : d3 / B = 0 := Nat.div_eq_of_lt h3
  rw [this, Nat.digits_zero]
  have : d3 % B = d3 := Nat.mod_eq_of_lt h3
  rw [this]

lemma card_4 (d0 d1 d2 d3 : ℕ) (h01 : d0 ≠ d1) (h02 : d0 ≠ d2) (h12 : d1 ≠ d2) :
    ([d0, d1, d2, d3] : List ℕ).toFinset.card > 2 := by
  simp [List.toFinset_cons, List.toFinset_nil]
  have h_sub : {d0, d1, d2} ⊆ ({d0, d1, d2, d3} : Finset ℕ) := by
    intro x
    simp
    intro hx
    tauto
  have h_card : ({d0, d1, d2} : Finset ℕ).card = 3 := by
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_insert_of_notMem]
      · rfl
      · simp [h12]
    · simp [h01, h02]
  have h_le := Finset.card_le_card h_sub
  omega

lemma distinct_digits_4 (B d0 d1 d2 d3 k : ℕ) (hB : 1 < B) 
    (h0 : d0 < B) (h1 : d1 < B) (h2 : d2 < B) (h3 : d3 < B) (h3_pos : 0 < d3) 
    (hk : k = d0 + B * (d1 + B * (d2 + B * d3)))
    (h01 : d0 ≠ d1) (h02 : d0 ≠ d2) (h12 : d1 ≠ d2) :
    (Nat.digits B k).toFinset.card > 2 := by
  rw [hk, digits_4 B d0 d1 d2 d3 hB h0 h1 h2 h3 h3_pos]
  exact card_4 d0 d1 d2 d3 h01 h02 h12

lemma card_4_alt (d0 d1 d2 d3 : ℕ) (h01 : d0 ≠ d1) (h03 : d0 ≠ d3) (h13 : d1 ≠ d3) :
    ([d0, d1, d2, d3] : List ℕ).toFinset.card > 2 := by
  simp [List.toFinset_cons, List.toFinset_nil]
  have h_sub : {d0, d1, d3} ⊆ ({d0, d1, d2, d3} : Finset ℕ) := by
    intro x
    simp
    intro hx
    tauto
  have h_card : ({d0, d1, d3} : Finset ℕ).card = 3 := by
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_insert_of_notMem]
      · rfl
      · simp [h13]
    · simp [h01, h03]
  have h_le := Finset.card_le_card h_sub
  omega

lemma distinct_digits_4_alt (B d0 d1 d2 d3 k : ℕ) (hB : 1 < B) 
    (h0 : d0 < B) (h1 : d1 < B) (h2 : d2 < B) (h3 : d3 < B) (h3_pos : 0 < d3) 
    (hk : k = d0 + B * (d1 + B * (d2 + B * d3)))
    (h01 : d0 ≠ d1) (h03 : d0 ≠ d3) (h13 : d1 ≠ d3) :
    (Nat.digits B k).toFinset.card > 2 := by
  rw [hk, digits_4 B d0 d1 d2 d3 hB h0 h1 h2 h3 h3_pos]
  exact card_4_alt d0 d1 d2 d3 h01 h03 h13


lemma a306424_43 : A306424_condition 43 := by
  intro b hb
  have hb3 : 3 ≤ b := hb.1
  have hbk : b < 43 := hb.2
  interval_cases b
  · change (Nat.digits 3 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 3 43 = [1, 2, 1, 1] := by
      apply digits_4 3 1 2 1 1 <;> decide
    rw [h_dig]
    decide
  · change (Nat.digits 4 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 4 43 = [3, 2, 2] := by
      apply digits_3 4 3 2 2 <;> decide
    rw [h_dig]
    decide
  · change (Nat.digits 5 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 5 43 = [3, 3, 1] := by
      apply digits_3 5 3 3 1 <;> decide
    rw [h_dig]
    decide
  · change (Nat.digits 6 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 6 43 = [1, 1, 1] := by
      apply digits_3 6 1 1 1 <;> decide
    rw [h_dig]
    decide
  · change (Nat.digits 7 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 7 43 = [1, 6] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 7 = 6 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 6 / 7 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 8 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 8 43 = [3, 5] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 8 = 5 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 5 / 8 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 9 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 9 43 = [7, 4] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 9 = 4 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 4 / 9 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 10 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 10 43 = [3, 4] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 10 = 4 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 4 / 10 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 11 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 11 43 = [10, 3] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 11 = 3 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 3 / 11 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 12 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 12 43 = [7, 3] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 12 = 3 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 3 / 12 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 13 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 13 43 = [4, 3] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 13 = 3 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 3 / 13 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 14 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 14 43 = [1, 3] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 14 = 3 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 3 / 14 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 15 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 15 43 = [13, 2] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 15 = 2 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 2 / 15 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 16 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 16 43 = [11, 2] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 16 = 2 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 2 / 16 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 17 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 17 43 = [9, 2] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 17 = 2 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 2 / 17 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 18 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 18 43 = [7, 2] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 18 = 2 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 2 / 18 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 19 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 19 43 = [5, 2] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 19 = 2 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 2 / 19 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 20 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 20 43 = [3, 2] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 20 = 2 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 2 / 20 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 21 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 21 43 = [1, 2] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 21 = 2 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 2 / 21 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 22 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 22 43 = [21, 1] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 22 = 1 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 1 / 22 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 23 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 23 43 = [20, 1] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 23 = 1 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 1 / 23 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 24 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 24 43 = [19, 1] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 24 = 1 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 1 / 24 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 25 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 25 43 = [18, 1] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 25 = 1 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 1 / 25 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 26 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 26 43 = [17, 1] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 26 = 1 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 1 / 26 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 27 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 27 43 = [16, 1] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 27 = 1 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 1 / 27 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 28 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 28 43 = [15, 1] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 28 = 1 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 1 / 28 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 29 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 29 43 = [14, 1] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 29 = 1 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 1 / 29 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 30 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 30 43 = [13, 1] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 30 = 1 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 1 / 30 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 31 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 31 43 = [12, 1] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 31 = 1 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 1 / 31 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 32 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 32 43 = [11, 1] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 32 = 1 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 1 / 32 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 33 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 33 43 = [10, 1] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 33 = 1 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 1 / 33 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 34 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 34 43 = [9, 1] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 34 = 1 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 1 / 34 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 35 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 35 43 = [8, 1] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 35 = 1 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 1 / 35 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 36 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 36 43 = [7, 1] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 36 = 1 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 1 / 36 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 37 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 37 43 = [6, 1] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 37 = 1 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 1 / 37 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 38 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 38 43 = [5, 1] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 38 = 1 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 1 / 38 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 39 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 39 43 = [4, 1] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 39 = 1 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 1 / 39 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 40 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 40 43 = [3, 1] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 40 = 1 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 1 / 40 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 41 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 41 43 = [2, 1] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 41 = 1 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 1 / 41 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide
  · change (Nat.digits 42 43).toFinset.card ≤ 2
    have h_dig : Nat.digits 42 43 = [1, 1] := by
      rw [Nat.digits_def' (by decide) (by decide)]
      have : 43 / 42 = 1 := rfl
      rw [this, Nat.digits_def' (by decide) (by decide)]
      have : 1 / 42 = 0 := rfl
      rw [this, Nat.digits_zero]
    rw [h_dig]
    decide


lemma region1 (b x : ℕ) (h1 : b ≥ 17) (h2 : x = 0) :
  ∃ B, 3 ≤ B ∧ B < b^2 + x ∧ ((Nat.digits B (b^2 + x)).toFinset.card) > 2 := by
  let B := b - 3
  have hB : b = B + 3 := by omega
  clear_value B
  cases hB
  use B
  have H3 : 3 ≤ B := by omega
  have h_sq : B < B * B := by nlinarith
  have h_exp_lt : B * B + 2 * 3 * B + 3^2 + x = (B + 3)^2 + x := by ring
  have H_lt : B < (B + 3)^2 + x := by omega
  refine ⟨H3, H_lt, ?_⟩
  apply distinct_digits_3 B (9) (6) (1) ((B + 3)^2 + x)
  · omega
  · omega
  · omega
  · omega
  · omega
  · have h_exp : (B + 3)^2 = B * B + 2 * 3 * B + 3^2 := by ring
    have h_rhs : B * ((6) + B * (1)) = (6) * B + (1) * (B * B) := by ring
    rw [h_exp, h_rhs]
    clear h_exp h_rhs
    generalize B * B = S
    omega
  · omega
  · omega
  · omega

lemma region2 (b x : ℕ) (h1 : b ≥ 17) (h2 : x = 1) :
  ∃ B, 3 ≤ B ∧ B < b^2 + x ∧ ((Nat.digits B (b^2 + x)).toFinset.card) > 2 := by
  let B := b - 2
  have hB : b = B + 2 := by omega
  clear_value B
  cases hB
  use B
  have H3 : 3 ≤ B := by omega
  have h_sq : B < B * B := by nlinarith
  have h_exp_lt : B * B + 2 * 2 * B + 2^2 + x = (B + 2)^2 + x := by ring
  have H_lt : B < (B + 2)^2 + x := by omega
  refine ⟨H3, H_lt, ?_⟩
  apply distinct_digits_3 B (5) (4) (1) ((B + 2)^2 + x)
  · omega
  · omega
  · omega
  · omega
  · omega
  · have h_exp : (B + 2)^2 = B * B + 2 * 2 * B + 2^2 := by ring
    have h_rhs : B * ((4) + B * (1)) = (4) * B + (1) * (B * B) := by ring
    rw [h_exp, h_rhs]
    clear h_exp h_rhs
    generalize B * B = S
    omega
  · omega
  · omega
  · omega

lemma region3 (b x : ℕ) (h1 : b ≥ 17) (h2 : 2 ≤ x ∧ x ≤ b - 1) :
  ∃ B, 3 ≤ B ∧ B < b^2 + x ∧ ((Nat.digits B (b^2 + x)).toFinset.card) > 2 := by
  let B := b - 0
  have hB : b = B + 0 := by omega
  clear_value B
  cases hB
  use B
  have H3 : 3 ≤ B := by omega
  have h_sq : B < B * B := by nlinarith
  have h_exp_lt : B * B + 2 * 0 * B + 0^2 + x = (B + 0)^2 + x := by ring
  have H_lt : B < (B + 0)^2 + x := by omega
  refine ⟨H3, H_lt, ?_⟩
  apply distinct_digits_3 B (x) (0) (1) ((B + 0)^2 + x)
  · omega
  · omega
  · omega
  · omega
  · omega
  · have h_exp : (B + 0)^2 = B * B + 2 * 0 * B + 0^2 := by ring
    have h_rhs : B * ((0) + B * (1)) = (0) * B + (1) * (B * B) := by ring
    rw [h_exp, h_rhs]
    clear h_exp h_rhs
    generalize B * B = S
    omega
  · omega
  · omega
  · omega

lemma region4 (b x : ℕ) (h1 : b ≥ 17) (h2 : x = b) :
  ∃ B, 3 ≤ B ∧ B < b^2 + x ∧ ((Nat.digits B (b^2 + x)).toFinset.card) > 2 := by
  let B := b - 1
  have hB : b = B + 1 := by omega
  clear_value B
  cases hB
  use B
  have H3 : 3 ≤ B := by omega
  have h_sq : B < B * B := by nlinarith
  have h_exp_lt : B * B + 2 * 1 * B + 1^2 + x = (B + 1)^2 + x := by ring
  have H_lt : B < (B + 1)^2 + x := by omega
  refine ⟨H3, H_lt, ?_⟩
  apply distinct_digits_3 B (2) (3) (1) ((B + 1)^2 + x)
  · omega
  · omega
  · omega
  · omega
  · omega
  · have h_exp : (B + 1)^2 = B * B + 2 * 1 * B + 1^2 := by ring
    have h_rhs : B * ((3) + B * (1)) = (3) * B + (1) * (B * B) := by ring
    rw [h_exp, h_rhs]
    clear h_exp h_rhs
    generalize B * B = S
    omega
  · omega
  · omega
  · omega

lemma region5 (b x : ℕ) (h1 : b ≥ 17) (h2 : x = b + 1) :
  ∃ B, 3 ≤ B ∧ B < b^2 + x ∧ ((Nat.digits B (b^2 + x)).toFinset.card) > 2 := by
  let B := b - 2
  have hB : b = B + 2 := by omega
  clear_value B
  cases hB
  use B
  have H3 : 3 ≤ B := by omega
  have h_sq : B < B * B := by nlinarith
  have h_exp_lt : B * B + 2 * 2 * B + 2^2 + x = (B + 2)^2 + x := by ring
  have H_lt : B < (B + 2)^2 + x := by omega
  refine ⟨H3, H_lt, ?_⟩
  apply distinct_digits_3 B (7) (5) (1) ((B + 2)^2 + x)
  · omega
  · omega
  · omega
  · omega
  · omega
  · have h_exp : (B + 2)^2 = B * B + 2 * 2 * B + 2^2 := by ring
    have h_rhs : B * ((5) + B * (1)) = (5) * B + (1) * (B * B) := by ring
    rw [h_exp, h_rhs]
    clear h_exp h_rhs
    generalize B * B = S
    omega
  · omega
  · omega
  · omega

lemma region6a (b x : ℕ) (h1 : b ≥ 17) (h2 : b + 2 ≤ x ∧ x ≤ 2*b - 4) :
  ∃ B, 3 ≤ B ∧ B < b^2 + x ∧ ((Nat.digits B (b^2 + x)).toFinset.card) > 2 := by
  let B := b - 1
  have hB : b = B + 1 := by omega
  clear_value B
  cases hB
  use B
  have H3 : 3 ≤ B := by omega
  have h_sq : B < B * B := by nlinarith
  have h_exp_lt : B * B + 2 * 1 * B + 1^2 + x = (B + 1)^2 + x := by ring
  have H_lt : B < (B + 1)^2 + x := by omega
  refine ⟨H3, H_lt, ?_⟩
  apply distinct_digits_3 B (x - B + 1) (3) (1) ((B + 1)^2 + x)
  · omega
  · omega
  · omega
  · omega
  · omega
  · have h_exp : (B + 1)^2 = B * B + 2 * 1 * B + 1^2 := by ring
    have h_rhs : B * ((3) + B * (1)) = (3) * B + (1) * (B * B) := by ring
    rw [h_exp, h_rhs]
    clear h_exp h_rhs
    generalize B * B = S
    omega
  · omega
  · omega
  · omega

lemma region6b (b x : ℕ) (h1 : b ≥ 17) (h2 : x = 2*b - 3) :
  ∃ B, 3 ≤ B ∧ B < b^2 + x ∧ ((Nat.digits B (b^2 + x)).toFinset.card) > 2 := by
  let B := b - 1
  have hB : b = B + 1 := by omega
  clear_value B
  cases hB
  use B
  have H3 : 3 ≤ B := by omega
  have h_sq : B < B * B := by nlinarith
  have h_exp_lt : B * B + 2 * 1 * B + 1^2 + x = (B + 1)^2 + x := by ring
  have H_lt : B < (B + 1)^2 + x := by omega
  refine ⟨H3, H_lt, ?_⟩
  apply distinct_digits_3 B (0) (4) (1) ((B + 1)^2 + x)
  · omega
  · omega
  · omega
  · omega
  · omega
  · have h_exp : (B + 1)^2 = B * B + 2 * 1 * B + 1^2 := by ring
    have h_rhs : B * ((4) + B * (1)) = (4) * B + (1) * (B * B) := by ring
    rw [h_exp, h_rhs]
    clear h_exp h_rhs
    generalize B * B = S
    omega
  · omega
  · omega
  · omega

lemma region7 (b x : ℕ) (h1 : b ≥ 17) (h2 : x = 2*b - 2) :
  ∃ B, 3 ≤ B ∧ B < b^2 + x ∧ ((Nat.digits B (b^2 + x)).toFinset.card) > 2 := by
  let B := b - 3
  have hB : b = B + 3 := by omega
  clear_value B
  cases hB
  use B
  have H3 : 3 ≤ B := by omega
  have h_sq : B < B * B := by nlinarith
  have h_exp_lt : B * B + 2 * 3 * B + 3^2 + x = (B + 3)^2 + x := by ring
  have H_lt : B < (B + 3)^2 + x := by omega
  refine ⟨H3, H_lt, ?_⟩
  apply distinct_digits_3 B (13) (8) (1) ((B + 3)^2 + x)
  · omega
  · omega
  · omega
  · omega
  · omega
  · have h_exp : (B + 3)^2 = B * B + 2 * 3 * B + 3^2 := by ring
    have h_rhs : B * ((8) + B * (1)) = (8) * B + (1) * (B * B) := by ring
    rw [h_exp, h_rhs]
    clear h_exp h_rhs
    generalize B * B = S
    omega
  · omega
  · omega
  · omega

lemma region8 (b x : ℕ) (h1 : b ≥ 17) (h2 : x = 2*b - 1) :
  ∃ B, 3 ≤ B ∧ B < b^2 + x ∧ ((Nat.digits B (b^2 + x)).toFinset.card) > 2 := by
  let B := b - 1
  have hB : b = B + 1 := by omega
  clear_value B
  cases hB
  use B
  have H3 : 3 ≤ B := by omega
  have h_sq : B < B * B := by nlinarith
  have h_exp_lt : B * B + 2 * 1 * B + 1^2 + x = (B + 1)^2 + x := by ring
  have H_lt : B < (B + 1)^2 + x := by omega
  refine ⟨H3, H_lt, ?_⟩
  apply distinct_digits_3 B (2) (4) (1) ((B + 1)^2 + x)
  · omega
  · omega
  · omega
  · omega
  · omega
  · have h_exp : (B + 1)^2 = B * B + 2 * 1 * B + 1^2 := by ring
    have h_rhs : B * ((4) + B * (1)) = (4) * B + (1) * (B * B) := by ring
    rw [h_exp, h_rhs]
    clear h_exp h_rhs
    generalize B * B = S
    omega
  · omega
  · omega
  · omega

lemma region9 (b x : ℕ) (h1 : b ≥ 17) (h2 : x = 2*b) :
  ∃ B, 3 ≤ B ∧ B < b^2 + x ∧ ((Nat.digits B (b^2 + x)).toFinset.card) > 2 := by
  let B := b - 0
  have hB : b = B + 0 := by omega
  clear_value B
  cases hB
  use B
  have H3 : 3 ≤ B := by omega
  have h_sq : B < B * B := by nlinarith
  have h_exp_lt : B * B + 2 * 0 * B + 0^2 + x = (B + 0)^2 + x := by ring
  have H_lt : B < (B + 0)^2 + x := by omega
  refine ⟨H3, H_lt, ?_⟩
  apply distinct_digits_3 B (0) (2) (1) ((B + 0)^2 + x)
  · omega
  · omega
  · omega
  · omega
  · omega
  · have h_exp : (B + 0)^2 = B * B + 2 * 0 * B + 0^2 := by ring
    have h_rhs : B * ((2) + B * (1)) = (2) * B + (1) * (B * B) := by ring
    rw [h_exp, h_rhs]
    clear h_exp h_rhs
    generalize B * B = S
    omega
  · omega
  · omega
  · omega


lemma bounded_cases (k : ℕ) (hk1 : 43 < k) (hk2 : k < 289) : ∃ B, 3 ≤ B ∧ B < k ∧ ((Nat.digits B k).toFinset.card) > 2 := by
  interval_cases k
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 4 0 3 2 44
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 4 1 3 2 45
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 3
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 3 1 0 2 1 46
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 3
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 3 2 0 2 1 47
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 3
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 3 0 1 2 1 48
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 4 1 0 3 49
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 4 2 0 3 50
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 3
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 3 0 2 2 1 51
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 4 0 1 3 52
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 5 3 0 2 53
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 4 2 1 3 54
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 3
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 3 1 0 0 2 55
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 4 0 2 3 56
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 3
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 3 0 1 0 2 57
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 5 3 1 2 58
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 3
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 3 2 1 0 2 59
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 0 4 1 60
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 3
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 3 1 2 0 2 61
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 2 4 1 62
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 3 4 1 63
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 3
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 3 1 0 1 2 64
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 3
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 3 2 0 1 2 65
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 3
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 3 0 1 1 2 66
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 3 0 0 1 67
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 2 5 1 68
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 3
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 3 0 2 1 2 69
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 1 0 1 70
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 3 1 0 1 71
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 0 2 0 1 72
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 3
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 3 1 0 2 2 73
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 7
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 7 4 3 1 74
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 3
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 3 0 1 2 2 75
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 0 3 0 1 76
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 1 3 0 1 77
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 3 0 1 78
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 5 4 0 3 79
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 5 0 1 3 80
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 3 1 2 81
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 0 1 1 82
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 3 0 1 1 83
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 5 4 1 3 84
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 5 0 2 3 85
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 5 1 2 3 86
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 7
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 7 3 5 1 87
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 2 1 1 88
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 5 4 2 3 89
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 0 3 2 90
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 3 2 1 1 91
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 3 1 1 92
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 7
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 7 2 6 1 93
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 3 1 1 94
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 5 0 4 3 95
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 5 1 4 3 96
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 1 0 2 1 97
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 2 0 2 1 98
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 3 0 2 1 99
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 1 2 1 100
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 5 1 0 4 101
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 5 2 0 4 102
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 3 1 2 1 103
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 0 2 2 1 104
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 5 0 1 4 105
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 4 5 2 106
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 3 2 2 1 107
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 3 2 1 108
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 1 3 2 1 109
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 2 3 2 1 110
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 5 1 2 4 111
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 4 0 3 112
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 1 0 3 1 113
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 0 3 1 114
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 3 0 3 1 115
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 1 3 1 116
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 5 2 3 4 117
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 1 3 1 118
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 5 1 3 119
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 2 3 1 120
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 1 2 3 1 121
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 8
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 8 2 7 1 122
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 3 2 3 1 123
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 0 3 3 1 124
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 5 2 3 125
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 2 3 3 1 126
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 2 0 0 1 127
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 3 0 0 1 128
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 1 0 0 2 129
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 9
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 9 4 5 1 130
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 3 0 0 2 131
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 0 1 0 2 132
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 3 1 0 1 133
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 1 0 2 134
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 3 1 0 2 135
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 1 2 0 1 136
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 1 2 0 2 137
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 3 2 0 1 138
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 3 2 0 2 139
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 0 3 0 2 140
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 1 3 0 2 141
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 3 0 2 142
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 7
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 7 3 6 2 143
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 4 3 0 1 144
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 1 0 1 2 145
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 0 1 2 146
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 3 0 1 2 147
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 0 1 1 2 148
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 5 0 4 149
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 0 1 4 150
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 3 1 1 2 151
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 2 1 2 152
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 3 0 1 1 153
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 4 0 1 1 154
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 3 2 1 2 155
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 3 1 2 156
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 1 3 1 2 157
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 3 1 2 158
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 3 2 4 159
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 0 2 1 1 160
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 1 0 2 2 161
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 0 3 4 162
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 3 0 2 2 163
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 1 2 2 164
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 0 3 1 1 165
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 7
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 7 5 2 3 166
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 3 1 2 2 167
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 8
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 8 0 5 2 168
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 4 3 1 1 169
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 0 4 1 1 170
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 8
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 8 3 5 2 171
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 3 2 2 172
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 1 3 2 2 173
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 0 5 4 174
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 1 5 4 175
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 1 0 2 1 176
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 1 0 3 2 177
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 0 3 2 178
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 3 0 3 2 179
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 1 3 2 180
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 1 0 5 181
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 1 3 2 182
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 3 1 3 2 183
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 2 3 2 184
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 1 2 3 2 185
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 6 0 1 5 186
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 8
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 8 3 7 2 187
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 0 3 3 2 188
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 1 3 3 2 189
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 0 3 2 1 190
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 1 3 2 1 191
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 2 3 2 1 192
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 1 0 0 3 193
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 2 0 0 3 194
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 0 4 2 1 195
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 0 1 0 3 196
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 2 4 2 1 197
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 1 0 3 198
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 3 1 0 3 199
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 0 2 0 3 200
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 1 2 0 3 201
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 2 0 3 1 202
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 3 2 0 3 203
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 4 0 3 1 204
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 1 3 0 3 205
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 3 0 3 206
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 2 1 3 1 207
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 7
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 7 5 1 4 208
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 1 0 1 3 209
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 0 1 3 210
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 3 0 1 3 211
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 0 1 1 3 212
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 3 2 3 1 213
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 2 1 1 3 214
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 0 3 3 1 215
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 2 1 3 216
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 1 2 1 3 217
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 6 2 0 0 1 218
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 3 2 1 3 219
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 3 1 3 220
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 1 4 3 1 221
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 3 1 3 222
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 3 4 3 1 223
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 6 2 1 0 1 224
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 1 0 2 3 225
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 2 0 2 3 226
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 3 0 2 3 227
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 1 2 3 228
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 4 0 4 1 229
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 2 1 2 3 230
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 3 1 2 3 231
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 0 2 2 3 232
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 4 1 2 2 3 233
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 6 0 3 0 1 234
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 0 2 4 1 235
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 3 2 3 236
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 1 3 2 3 237
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 3 2 4 1 238
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 4 2 4 1 239
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 0 3 4 1 240
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 1 0 3 3 241
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 0 3 3 242
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 6 3 4 0 1 243
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 1 3 3 244
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 0 4 4 1 245
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 2 1 3 3 246
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 2 4 4 1 247
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 0 2 3 3 248
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 4
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 4 1 2 3 3 249
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 6 4 5 0 1 250
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 1 0 0 2 251
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 7
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 7 0 1 5 252
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 3 0 0 2 253
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 4 0 0 2 254
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 0 1 0 2 255
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 6 4 0 1 1 256
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 2 1 0 2 257
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 3 1 0 2 258
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 4 1 0 2 259
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 7
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 7 1 2 5 260
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 1 2 0 2 261
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 7
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 7 3 2 5 262
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 3 2 0 2 263
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 4 2 0 2 264
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 0 3 0 2 265
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 1 3 0 2 266
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 2 3 0 2 267
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 6 4 2 1 1 268
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 4 3 0 2 269
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 0 4 0 2 270
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 1 4 0 2 271
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 2 4 0 2 272
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 3 4 0 2 273
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 6 4 3 1 1 274
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 6 5 3 1 1 275
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 1 0 1 2 276
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 2 0 1 2 277
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 3 0 1 2 278
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 4 0 1 2 279
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 0 1 1 2 280
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 6 5 4 1 1 281
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 6 0 5 1 1 282
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 3 1 1 2 283
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4_alt 5 4 1 1 2 284
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 0 2 1 2 285
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 6
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 6 4 5 1 1 286
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 7
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_3 7 0 6 5 287
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega
  · use 5
    refine ⟨by decide, by decide, ?_⟩
    apply distinct_digits_4 5 3 2 1 2 288
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · rfl
    · omega
    · omega
    · omega

lemma k_ge_289 (k : ℕ) (hk : k ≥ 289) : ∃ B, 3 ≤ B ∧ B < k ∧ ((Nat.digits B k).toFinset.card) > 2 := by
  let b := Nat.sqrt k
  let x := k - b^2
  have h1 : b * b ≤ k := Nat.sqrt_le k
  have h2 : k < (b + 1) * (b + 1) := Nat.lt_succ_sqrt k
  have h_exp : (b + 1) * (b + 1) = b^2 + 2 * b + 1 := by ring
  have h_b : b ≥ 17 := by nlinarith
  have h_x_bound : x ≤ 2 * b := by
    have h_b2 : b * b = b^2 := by ring
    omega
  have hk_eq : k = b^2 + x := by
    have h_b2 : b * b = b^2 := by ring
    omega
  clear_value x b
  cases hk_eq
  have h_cases : x = 0 ∨ x = 1 ∨ 2 ≤ x ∧ x ≤ b - 1 ∨ x = b ∨ x = b + 1 ∨ b + 2 ≤ x ∧ x ≤ 2*b - 4 ∨ x = 2*b - 3 ∨ x = 2*b - 2 ∨ x = 2*b - 1 ∨ x = 2*b := by omega
  rcases h_cases with hc0 | hc1 | hc2 | hc3 | hc4 | hc5 | hc6 | hc7 | hc8 | hc9
  · exact region1 b x h_b hc0
  · exact region2 b x h_b hc1
  · exact region3 b x h_b hc2
  · exact region4 b x h_b hc3
  · exact region5 b x h_b hc4
  · exact region6a b x h_b hc5
  · exact region6b b x h_b hc6
  · exact region7 b x h_b hc7
  · exact region8 b x h_b hc8
  · exact region9 b x h_b hc9


theorem oeis_306424_conjecture_0 : A306424_condition 43 ∧ ∀ k : ℕ, 43 < k → ¬ A306424_condition k := by
  constructor
  · exact a306424_43
  · intros k hk
    intro h_cond
    by_cases h289 : k < 289
    · have ⟨B, hB3, hBk, h_card⟩ := bounded_cases k hk h289
      have h_card_le := h_cond B ⟨hB3, hBk⟩
      omega
    · have ⟨B, hB3, hBk, h_card⟩ := k_ge_289 k (by omega)
      have h_card_le := h_cond B ⟨hB3, hBk⟩
      omega

theorem oeis_306424_conjecture_0.disproof : ¬ (type_of% @oeis_306424_conjecture_0) := sorry
