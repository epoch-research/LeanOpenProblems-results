import Submission.Cases_A
set_option maxHeartbeats 20000000
set_option maxRecDepth 100000

open Finset Nat Set
theorem a_thirteen_le_a081512_thirteen : a 13 ≤ a081512 13 := by
  unfold a a081512
  change sInf (a_candidates 13) ≤ sInf (a081512_candidates 13)
  have hB : (a081512_candidates 13).Nonempty := ⟨180, thirteen_mem_a081512_thirteen⟩
  have hB_ge : 180 ≤ sInf (a081512_candidates 13) := by
    have hmem := Nat.sInf_mem hB
    exact a081512_candidates_13_ge (sInf (a081512_candidates 13)) hmem
  have hA_le : sInf (a_candidates 13) ≤ 180 := Nat.sInf_le thirteen_mem_a_thirteen
  exact le_trans hA_le hB_ge


theorem fourteen_mem_a_fourteen : 180 ∈ a_candidates 14 := by
  dsimp [a_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 9, 10, 12, 15, 18, 20, 30, 45}
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem fourteen_mem_a081512_fourteen : 180 ∈ a081512_candidates 14 := by
  dsimp [a081512_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 9, 10, 12, 15, 18, 20, 30, 45}
  refine ⟨by decide, by decide, by decide⟩

lemma not_mem_a081512_14_120 : 120 ∉ a081512_candidates 14 := by
  apply not_mem_a081512_of_compl 14 120
  · decide
  · decide

lemma not_mem_a081512_14_144 : 144 ∉ a081512_candidates 14 := by
  apply not_mem_a081512_of_compl 14 144
  · decide
  · decide

lemma not_mem_a081512_14_168 : 168 ∉ a081512_candidates 14 := by
  apply not_mem_a081512_of_compl 14 168
  · decide
  · decide

theorem a081512_candidates_14_ge (x : ℕ) (hx : x ∈ a081512_candidates 14) : 180 ≤ x := by
  by_contra! h
  have h_decide : (List.range 180).all (fun y =>
      decide (if y = 120 ∨ y = 144 ∨ y = 168 then True
              else (Nat.divisors y).card < 14)) = true := by decide
  have h_mem : x ∈ List.range 180 := List.mem_range.mpr h
  have h_all := List.all_eq_true.mp h_decide x h_mem
  rw [mem_a081512_candidates_iff] at hx
  rcases hx with ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_div_card : 14 ≤ (Nat.divisors x).card := by
    rw [← hD_card]
    exact Finset.card_le_card hD_pow
  by_cases h120 : x = 120
  · subst h120
    exact not_mem_a081512_14_120 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h144 : x = 144
  · subst h144
    exact not_mem_a081512_14_144 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h168 : x = 168
  · subst h168
    exact not_mem_a081512_14_168 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  have h_not_cond : ¬ (x = 120 ∨ x = 144 ∨ x = 168) := by
    rintro (rfl | rfl | rfl)
    · exact h120 rfl
    · exact h144 rfl
    · exact h168 rfl
  have h_card : (Nat.divisors x).card < 14 := by
    have h_dec := of_decide_eq_true h_all
    by_cases h_cond : x = 120 ∨ x = 144 ∨ x = 168
    · exfalso; exact h_not_cond h_cond
    · rw [if_neg h_cond] at h_dec
      exact h_dec
  omega

theorem a_fourteen_le_a081512_fourteen : a 14 ≤ a081512 14 := by
  unfold a a081512
  change sInf (a_candidates 14) ≤ sInf (a081512_candidates 14)
  have hB : (a081512_candidates 14).Nonempty := ⟨180, fourteen_mem_a081512_fourteen⟩
  have hB_ge : 180 ≤ sInf (a081512_candidates 14) := by
    have hmem := Nat.sInf_mem hB
    exact a081512_candidates_14_ge (sInf (a081512_candidates 14)) hmem
  have hA_le : sInf (a_candidates 14) ≤ 180 := Nat.sInf_le fourteen_mem_a_fourteen
  exact le_trans hA_le hB_ge


theorem fifteen_mem_a_fifteen : 240 ∈ a_candidates 15 := by
  dsimp [a_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 16, 20, 30, 48, 60}
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem fifteen_mem_a081512_fifteen : 240 ∈ a081512_candidates 15 := by
  dsimp [a081512_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 16, 20, 30, 48, 60}
  refine ⟨by decide, by decide, by decide⟩

lemma not_mem_a081512_15_120 : 120 ∉ a081512_candidates 15 := by
  apply not_mem_a081512_of_compl 15 120
  · decide
  · decide

lemma not_mem_a081512_15_144 : 144 ∉ a081512_candidates 15 := by
  apply not_mem_a081512_of_compl 15 144
  · decide
  · decide

lemma not_mem_a081512_15_168 : 168 ∉ a081512_candidates 15 := by
  apply not_mem_a081512_of_compl 15 168
  · decide
  · decide

lemma not_mem_a081512_15_180 : 180 ∉ a081512_candidates 15 := by
  apply not_mem_a081512_of_compl 15 180
  · decide
  · decide

lemma not_mem_a081512_15_210 : 210 ∉ a081512_candidates 15 := by
  apply not_mem_a081512_of_compl 15 210
  · decide
  · decide

lemma not_mem_a081512_15_216 : 216 ∉ a081512_candidates 15 := by
  apply not_mem_a081512_of_compl 15 216
  · decide
  · decide

theorem a081512_candidates_15_ge (x : ℕ) (hx : x ∈ a081512_candidates 15) : 240 ≤ x := by
  by_contra! h
  have h_decide : (List.range 240).all (fun y =>
      decide (if y = 120 ∨ y = 144 ∨ y = 168 ∨ y = 180 ∨ y = 210 ∨ y = 216 then True
              else (Nat.divisors y).card < 15)) = true := by decide
  have h_mem : x ∈ List.range 240 := List.mem_range.mpr h
  have h_all := List.all_eq_true.mp h_decide x h_mem
  rw [mem_a081512_candidates_iff] at hx
  rcases hx with ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_div_card : 15 ≤ (Nat.divisors x).card := by
    rw [← hD_card]
    exact Finset.card_le_card hD_pow
  by_cases h120 : x = 120
  · subst h120
    exact not_mem_a081512_15_120 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h144 : x = 144
  · subst h144
    exact not_mem_a081512_15_144 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h168 : x = 168
  · subst h168
    exact not_mem_a081512_15_168 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h180 : x = 180
  · subst h180
    exact not_mem_a081512_15_180 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h210 : x = 210
  · subst h210
    exact not_mem_a081512_15_210 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h216 : x = 216
  · subst h216
    exact not_mem_a081512_15_216 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  have h_not_cond : ¬ (x = 120 ∨ x = 144 ∨ x = 168 ∨ x = 180 ∨ x = 210 ∨ x = 216) := by
    rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact h120 rfl
    · exact h144 rfl
    · exact h168 rfl
    · exact h180 rfl
    · exact h210 rfl
    · exact h216 rfl
  have h_card : (Nat.divisors x).card < 15 := by
    have h_dec := of_decide_eq_true h_all
    by_cases h_cond : x = 120 ∨ x = 144 ∨ x = 168 ∨ x = 180 ∨ x = 210 ∨ x = 216
    · exfalso; exact h_not_cond h_cond
    · rw [if_neg h_cond] at h_dec
      exact h_dec
  omega

theorem a_fifteen_le_a081512_fifteen : a 15 ≤ a081512 15 := by
  unfold a a081512
  change sInf (a_candidates 15) ≤ sInf (a081512_candidates 15)
  have hB : (a081512_candidates 15).Nonempty := ⟨240, fifteen_mem_a081512_fifteen⟩
  have hB_ge : 240 ≤ sInf (a081512_candidates 15) := by
    have hmem := Nat.sInf_mem hB
    exact a081512_candidates_15_ge (sInf (a081512_candidates 15)) hmem
  have hA_le : sInf (a_candidates 15) ≤ 240 := Nat.sInf_le fifteen_mem_a_fifteen
  exact le_trans hA_le hB_ge


theorem sixteen_mem_a_sixteen : 360 ∈ a_candidates 16 := by
  dsimp [a_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 18, 30, 45, 72, 120}
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem sixteen_mem_a081512_sixteen : 360 ∈ a081512_candidates 16 := by
  dsimp [a081512_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 18, 30, 45, 72, 120}
  refine ⟨by decide, by decide, by decide⟩

lemma not_mem_a081512_16_120 : 120 ∉ a081512_candidates 16 := by
  apply not_mem_a081512_of_compl 16 120
  · decide
  · decide

lemma not_mem_a081512_16_168 : 168 ∉ a081512_candidates 16 := by
  apply not_mem_a081512_of_compl 16 168
  · decide
  · decide

lemma not_mem_a081512_16_180 : 180 ∉ a081512_candidates 16 := by
  apply not_mem_a081512_of_compl 16 180
  · decide
  · decide

lemma not_mem_a081512_16_210 : 210 ∉ a081512_candidates 16 := by
  apply not_mem_a081512_of_compl 16 210
  · decide
  · decide

lemma not_mem_a081512_16_216 : 216 ∉ a081512_candidates 16 := by
  apply not_mem_a081512_of_compl 16 216
  · decide
  · decide

lemma not_mem_a081512_16_240 : 240 ∉ a081512_candidates 16 := by
  apply not_mem_a081512_of_compl 16 240
  · decide
  · decide

lemma not_mem_a081512_16_252 : 252 ∉ a081512_candidates 16 := by
  apply not_mem_a081512_of_compl 16 252
  · decide
  · decide

lemma not_mem_a081512_16_264 : 264 ∉ a081512_candidates 16 := by
  apply not_mem_a081512_of_compl 16 264
  · decide
  · decide

lemma not_mem_a081512_16_270 : 270 ∉ a081512_candidates 16 := by
  apply not_mem_a081512_of_compl 16 270
  · decide
  · decide

lemma not_mem_a081512_16_280 : 280 ∉ a081512_candidates 16 := by
  apply not_mem_a081512_of_compl 16 280
  · decide
  · decide

lemma not_mem_a081512_16_288 : 288 ∉ a081512_candidates 16 := by
  apply not_mem_a081512_of_compl 16 288
  · decide
  · decide

lemma not_mem_a081512_16_300 : 300 ∉ a081512_candidates 16 := by
  apply not_mem_a081512_of_compl 16 300
  · decide
  · decide

lemma not_mem_a081512_16_312 : 312 ∉ a081512_candidates 16 := by
  apply not_mem_a081512_of_compl 16 312
  · decide
  · decide

lemma not_mem_a081512_16_330 : 330 ∉ a081512_candidates 16 := by
  apply not_mem_a081512_of_compl 16 330
  · decide
  · decide

lemma not_mem_a081512_16_336 : 336 ∉ a081512_candidates 16 := by
  apply not_mem_a081512_of_compl 16 336
  · decide
  · decide

theorem a081512_candidates_16_ge (x : ℕ) (hx : x ∈ a081512_candidates 16) : 360 ≤ x := by
  by_contra! h
  have h_decide : (List.range 360).all (fun y =>
      decide (if y = 120 ∨ y = 168 ∨ y = 180 ∨ y = 210 ∨ y = 216 ∨ y = 240 ∨ y = 252 ∨ y = 264 ∨ y = 270 ∨ y = 280 ∨ y = 288 ∨ y = 300 ∨ y = 312 ∨ y = 330 ∨ y = 336 then True
              else (Nat.divisors y).card < 16)) = true := by decide
  have h_mem : x ∈ List.range 360 := List.mem_range.mpr h
  have h_all := List.all_eq_true.mp h_decide x h_mem
  rw [mem_a081512_candidates_iff] at hx
  rcases hx with ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_div_card : 16 ≤ (Nat.divisors x).card := by
    rw [← hD_card]
    exact Finset.card_le_card hD_pow
  by_cases h120 : x = 120
  · subst h120
    exact not_mem_a081512_16_120 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h168 : x = 168
  · subst h168
    exact not_mem_a081512_16_168 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h180 : x = 180
  · subst h180
    exact not_mem_a081512_16_180 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h210 : x = 210
  · subst h210
    exact not_mem_a081512_16_210 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h216 : x = 216
  · subst h216
    exact not_mem_a081512_16_216 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h240 : x = 240
  · subst h240
    exact not_mem_a081512_16_240 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h252 : x = 252
  · subst h252
    exact not_mem_a081512_16_252 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h264 : x = 264
  · subst h264
    exact not_mem_a081512_16_264 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h270 : x = 270
  · subst h270
    exact not_mem_a081512_16_270 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h280 : x = 280
  · subst h280
    exact not_mem_a081512_16_280 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h288 : x = 288
  · subst h288
    exact not_mem_a081512_16_288 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h300 : x = 300
  · subst h300
    exact not_mem_a081512_16_300 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h312 : x = 312
  · subst h312
    exact not_mem_a081512_16_312 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h330 : x = 330
  · subst h330
    exact not_mem_a081512_16_330 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h336 : x = 336
  · subst h336
    exact not_mem_a081512_16_336 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  have h_not_cond : ¬ (x = 120 ∨ x = 168 ∨ x = 180 ∨ x = 210 ∨ x = 216 ∨ x = 240 ∨ x = 252 ∨ x = 264 ∨ x = 270 ∨ x = 280 ∨ x = 288 ∨ x = 300 ∨ x = 312 ∨ x = 330 ∨ x = 336) := by
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact h120 rfl
    · exact h168 rfl
    · exact h180 rfl
    · exact h210 rfl
    · exact h216 rfl
    · exact h240 rfl
    · exact h252 rfl
    · exact h264 rfl
    · exact h270 rfl
    · exact h280 rfl
    · exact h288 rfl
    · exact h300 rfl
    · exact h312 rfl
    · exact h330 rfl
    · exact h336 rfl
  have h_card : (Nat.divisors x).card < 16 := by
    have h_dec := of_decide_eq_true h_all
    by_cases h_cond : x = 120 ∨ x = 168 ∨ x = 180 ∨ x = 210 ∨ x = 216 ∨ x = 240 ∨ x = 252 ∨ x = 264 ∨ x = 270 ∨ x = 280 ∨ x = 288 ∨ x = 300 ∨ x = 312 ∨ x = 330 ∨ x = 336
    · exfalso; exact h_not_cond h_cond
    · rw [if_neg h_cond] at h_dec
      exact h_dec
  omega

theorem a_sixteen_le_a081512_sixteen : a 16 ≤ a081512 16 := by
  unfold a a081512
  change sInf (a_candidates 16) ≤ sInf (a081512_candidates 16)
  have hB : (a081512_candidates 16).Nonempty := ⟨360, sixteen_mem_a081512_sixteen⟩
  have hB_ge : 360 ≤ sInf (a081512_candidates 16) := by
    have hmem := Nat.sInf_mem hB
    exact a081512_candidates_16_ge (sInf (a081512_candidates 16)) hmem
  have hA_le : sInf (a_candidates 16) ≤ 360 := Nat.sInf_le sixteen_mem_a_sixteen
  exact le_trans hA_le hB_ge


theorem seventeen_mem_a_seventeen : 360 ∈ a_candidates 17 := by
  dsimp [a_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 20, 24, 36, 40, 45, 120}
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem seventeen_mem_a081512_seventeen : 360 ∈ a081512_candidates 17 := by
  dsimp [a081512_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 20, 24, 36, 40, 45, 120}
  refine ⟨by decide, by decide, by decide⟩

lemma not_mem_a081512_17_180 : 180 ∉ a081512_candidates 17 := by
  apply not_mem_a081512_of_compl 17 180
  · decide
  · decide

lemma not_mem_a081512_17_240 : 240 ∉ a081512_candidates 17 := by
  apply not_mem_a081512_of_compl 17 240
  · decide
  · decide

lemma not_mem_a081512_17_252 : 252 ∉ a081512_candidates 17 := by
  apply not_mem_a081512_of_compl 17 252
  · decide
  · decide

lemma not_mem_a081512_17_288 : 288 ∉ a081512_candidates 17 := by
  apply not_mem_a081512_of_compl 17 288
  · decide
  · decide

lemma not_mem_a081512_17_300 : 300 ∉ a081512_candidates 17 := by
  apply not_mem_a081512_of_compl 17 300
  · decide
  · decide

lemma not_mem_a081512_17_336 : 336 ∉ a081512_candidates 17 := by
  apply not_mem_a081512_of_compl 17 336
  · decide
  · decide

theorem a081512_candidates_17_ge (x : ℕ) (hx : x ∈ a081512_candidates 17) : 360 ≤ x := by
  by_contra! h
  have h_decide : (List.range 360).all (fun y =>
      decide (if y = 180 ∨ y = 240 ∨ y = 252 ∨ y = 288 ∨ y = 300 ∨ y = 336 then True
              else (Nat.divisors y).card < 17)) = true := by decide
  have h_mem : x ∈ List.range 360 := List.mem_range.mpr h
  have h_all := List.all_eq_true.mp h_decide x h_mem
  rw [mem_a081512_candidates_iff] at hx
  rcases hx with ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_div_card : 17 ≤ (Nat.divisors x).card := by
    rw [← hD_card]
    exact Finset.card_le_card hD_pow
  by_cases h180 : x = 180
  · subst h180
    exact not_mem_a081512_17_180 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h240 : x = 240
  · subst h240
    exact not_mem_a081512_17_240 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h252 : x = 252
  · subst h252
    exact not_mem_a081512_17_252 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h288 : x = 288
  · subst h288
    exact not_mem_a081512_17_288 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h300 : x = 300
  · subst h300
    exact not_mem_a081512_17_300 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h336 : x = 336
  · subst h336
    exact not_mem_a081512_17_336 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  have h_not_cond : ¬ (x = 180 ∨ x = 240 ∨ x = 252 ∨ x = 288 ∨ x = 300 ∨ x = 336) := by
    rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact h180 rfl
    · exact h240 rfl
    · exact h252 rfl
    · exact h288 rfl
    · exact h300 rfl
    · exact h336 rfl
  have h_card : (Nat.divisors x).card < 17 := by
    have h_dec := of_decide_eq_true h_all
    by_cases h_cond : x = 180 ∨ x = 240 ∨ x = 252 ∨ x = 288 ∨ x = 300 ∨ x = 336
    · exfalso; exact h_not_cond h_cond
    · rw [if_neg h_cond] at h_dec
      exact h_dec
  omega

theorem a_seventeen_le_a081512_seventeen : a 17 ≤ a081512 17 := by
  unfold a a081512
  change sInf (a_candidates 17) ≤ sInf (a081512_candidates 17)
  have hB : (a081512_candidates 17).Nonempty := ⟨360, seventeen_mem_a081512_seventeen⟩
  have hB_ge : 360 ≤ sInf (a081512_candidates 17) := by
    have hmem := Nat.sInf_mem hB
    exact a081512_candidates_17_ge (sInf (a081512_candidates 17)) hmem
  have hA_le : sInf (a_candidates 17) ≤ 360 := Nat.sInf_le seventeen_mem_a_seventeen
  exact le_trans hA_le hB_ge


theorem eighteen_mem_a_eighteen : 360 ∈ a_candidates 18 := by
  dsimp [a_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 20, 24, 30, 36, 40, 45, 90}
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem eighteen_mem_a081512_eighteen : 360 ∈ a081512_candidates 18 := by
  dsimp [a081512_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 20, 24, 30, 36, 40, 45, 90}
  refine ⟨by decide, by decide, by decide⟩

lemma not_mem_a081512_18_180 : 180 ∉ a081512_candidates 18 := by
  apply not_mem_a081512_of_compl 18 180
  · decide
  · decide

lemma not_mem_a081512_18_240 : 240 ∉ a081512_candidates 18 := by
  apply not_mem_a081512_of_compl 18 240
  · decide
  · decide

lemma not_mem_a081512_18_252 : 252 ∉ a081512_candidates 18 := by
  apply not_mem_a081512_of_compl 18 252
  · decide
  · decide

lemma not_mem_a081512_18_288 : 288 ∉ a081512_candidates 18 := by
  apply not_mem_a081512_of_compl 18 288
  · decide
  · decide

lemma not_mem_a081512_18_300 : 300 ∉ a081512_candidates 18 := by
  apply not_mem_a081512_of_compl 18 300
  · decide
  · decide

lemma not_mem_a081512_18_336 : 336 ∉ a081512_candidates 18 := by
  apply not_mem_a081512_of_compl 18 336
  · decide
  · decide

theorem a081512_candidates_18_ge (x : ℕ) (hx : x ∈ a081512_candidates 18) : 360 ≤ x := by
  by_contra! h
  have h_decide : (List.range 360).all (fun y =>
      decide (if y = 180 ∨ y = 240 ∨ y = 252 ∨ y = 288 ∨ y = 300 ∨ y = 336 then True
              else (Nat.divisors y).card < 18)) = true := by decide
  have h_mem : x ∈ List.range 360 := List.mem_range.mpr h
  have h_all := List.all_eq_true.mp h_decide x h_mem
  rw [mem_a081512_candidates_iff] at hx
  rcases hx with ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_div_card : 18 ≤ (Nat.divisors x).card := by
    rw [← hD_card]
    exact Finset.card_le_card hD_pow
  by_cases h180 : x = 180
  · subst h180
    exact not_mem_a081512_18_180 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h240 : x = 240
  · subst h240
    exact not_mem_a081512_18_240 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h252 : x = 252
  · subst h252
    exact not_mem_a081512_18_252 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h288 : x = 288
  · subst h288
    exact not_mem_a081512_18_288 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h300 : x = 300
  · subst h300
    exact not_mem_a081512_18_300 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h336 : x = 336
  · subst h336
    exact not_mem_a081512_18_336 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  have h_not_cond : ¬ (x = 180 ∨ x = 240 ∨ x = 252 ∨ x = 288 ∨ x = 300 ∨ x = 336) := by
    rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact h180 rfl
    · exact h240 rfl
    · exact h252 rfl
    · exact h288 rfl
    · exact h300 rfl
    · exact h336 rfl
  have h_card : (Nat.divisors x).card < 18 := by
    have h_dec := of_decide_eq_true h_all
    by_cases h_cond : x = 180 ∨ x = 240 ∨ x = 252 ∨ x = 288 ∨ x = 300 ∨ x = 336
    · exfalso; exact h_not_cond h_cond
    · rw [if_neg h_cond] at h_dec
      exact h_dec
  omega

theorem a_eighteen_le_a081512_eighteen : a 18 ≤ a081512 18 := by
  unfold a a081512
  change sInf (a_candidates 18) ≤ sInf (a081512_candidates 18)
  have hB : (a081512_candidates 18).Nonempty := ⟨360, eighteen_mem_a081512_eighteen⟩
  have hB_ge : 360 ≤ sInf (a081512_candidates 18) := by
    have hmem := Nat.sInf_mem hB
    exact a081512_candidates_18_ge (sInf (a081512_candidates 18)) hmem
  have hA_le : sInf (a_candidates 18) ≤ 360 := Nat.sInf_le eighteen_mem_a_eighteen
  exact le_trans hA_le hB_ge


theorem nineteen_mem_a_nineteen : 360 ∈ a_candidates 19 := by
  dsimp [a_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 18, 20, 24, 30, 36, 40, 45, 72}
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem nineteen_mem_a081512_nineteen : 360 ∈ a081512_candidates 19 := by
  dsimp [a081512_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 18, 20, 24, 30, 36, 40, 45, 72}
  refine ⟨by decide, by decide, by decide⟩

lemma not_mem_a081512_19_240 : 240 ∉ a081512_candidates 19 := by
  apply not_mem_a081512_of_compl 19 240
  · decide
  · decide

lemma not_mem_a081512_19_336 : 336 ∉ a081512_candidates 19 := by
  apply not_mem_a081512_of_compl 19 336
  · decide
  · decide

theorem a081512_candidates_19_ge (x : ℕ) (hx : x ∈ a081512_candidates 19) : 360 ≤ x := by
  by_contra! h
  have h_decide : (List.range 360).all (fun y =>
      decide (if y = 240 ∨ y = 336 then True
              else (Nat.divisors y).card < 19)) = true := by decide
  have h_mem : x ∈ List.range 360 := List.mem_range.mpr h
  have h_all := List.all_eq_true.mp h_decide x h_mem
  rw [mem_a081512_candidates_iff] at hx
  rcases hx with ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_div_card : 19 ≤ (Nat.divisors x).card := by
    rw [← hD_card]
    exact Finset.card_le_card hD_pow
  by_cases h240 : x = 240
  · subst h240
    exact not_mem_a081512_19_240 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h336 : x = 336
  · subst h336
    exact not_mem_a081512_19_336 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  have h_not_cond : ¬ (x = 240 ∨ x = 336) := by
    rintro (rfl | rfl)
    · exact h240 rfl
    · exact h336 rfl
  have h_card : (Nat.divisors x).card < 19 := by
    have h_dec := of_decide_eq_true h_all
    by_cases h_cond : x = 240 ∨ x = 336
    · exfalso; exact h_not_cond h_cond
    · rw [if_neg h_cond] at h_dec
      exact h_dec
  omega

theorem a_nineteen_le_a081512_nineteen : a 19 ≤ a081512 19 := by
  unfold a a081512
  change sInf (a_candidates 19) ≤ sInf (a081512_candidates 19)
  have hB : (a081512_candidates 19).Nonempty := ⟨360, nineteen_mem_a081512_nineteen⟩
  have hB_ge : 360 ≤ sInf (a081512_candidates 19) := by
    have hmem := Nat.sInf_mem hB
    exact a081512_candidates_19_ge (sInf (a081512_candidates 19)) hmem
  have hA_le : sInf (a_candidates 19) ≤ 360 := Nat.sInf_le nineteen_mem_a_nineteen
  exact le_trans hA_le hB_ge


theorem twenty_mem_a_twenty : 672 ∈ a_candidates 20 := by
  dsimp [a_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 6, 7, 8, 12, 14, 16, 21, 24, 28, 32, 42, 48, 56, 84, 96, 168}
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem twenty_mem_a081512_twenty : 672 ∈ a081512_candidates 20 := by
  dsimp [a081512_candidates]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 6, 7, 8, 12, 14, 16, 21, 24, 28, 32, 42, 48, 56, 84, 96, 168}
  refine ⟨by decide, by decide, by decide⟩

lemma not_mem_a081512_20_240 : 240 ∉ a081512_candidates 20 := by
  apply not_mem_a081512_of_compl 20 240
  · decide
  · decide

lemma not_mem_a081512_20_336 : 336 ∉ a081512_candidates 20 := by
  apply not_mem_a081512_of_compl 20 336
  · decide
  · decide

lemma not_mem_a081512_20_360 : 360 ∉ a081512_candidates 20 := by
  apply not_mem_a081512_of_compl 20 360
  · decide
  · decide

lemma not_mem_a081512_20_420 : 420 ∉ a081512_candidates 20 := by
  apply not_mem_a081512_of_compl 20 420
  · decide
  · decide

lemma not_mem_a081512_20_432 : 432 ∉ a081512_candidates 20 := by
  apply not_mem_a081512_of_compl 20 432
  · decide
  · decide

lemma not_mem_a081512_20_480 : 480 ∉ a081512_candidates 20 := by
  apply not_mem_a081512_of_compl 20 480
  · decide
  · decide

lemma not_mem_a081512_20_504 : 504 ∉ a081512_candidates 20 := by
  apply not_mem_a081512_of_compl 20 504
  · decide
  · decide

lemma not_mem_a081512_20_528 : 528 ∉ a081512_candidates 20 := by
  apply not_mem_a081512_of_compl 20 528
  · decide
  · decide

lemma not_mem_a081512_20_540 : 540 ∉ a081512_candidates 20 := by
  apply not_mem_a081512_of_compl 20 540
  · decide
  · decide

lemma not_mem_a081512_20_560 : 560 ∉ a081512_candidates 20 := by
  apply not_mem_a081512_of_compl 20 560
  · decide
  · decide

lemma not_mem_a081512_20_576 : 576 ∉ a081512_candidates 20 := by
  apply not_mem_a081512_of_compl 20 576
  · decide
  · decide

lemma not_mem_a081512_20_600 : 600 ∉ a081512_candidates 20 := by
  apply not_mem_a081512_of_compl 20 600
  · decide
  · decide

lemma not_mem_a081512_20_624 : 624 ∉ a081512_candidates 20 := by
  apply not_mem_a081512_of_compl 20 624
  · decide
  · decide

lemma not_mem_a081512_20_630 : 630 ∉ a081512_candidates 20 := by
  apply not_mem_a081512_of_compl 20 630
  · decide
  · decide

lemma not_mem_a081512_20_648 : 648 ∉ a081512_candidates 20 := by
  apply not_mem_a081512_of_compl 20 648
  · decide
  · decide

lemma not_mem_a081512_20_660 : 660 ∉ a081512_candidates 20 := by
  apply not_mem_a081512_of_compl 20 660
  · decide
  · decide

def f_20 (y : ℕ) : Bool :=
  decide (if y = 240 ∨ y = 336 ∨ y = 360 ∨ y = 420 ∨ y = 432 ∨ y = 480 ∨ y = 504 ∨ y = 528 ∨ y = 540 ∨ y = 560 ∨ y = 576 ∨ y = 600 ∨ y = 624 ∨ y = 630 ∨ y = 648 ∨ y = 660 then True
          else (Nat.divisors y).card < 20)

lemma h1_20 : ∀ y ∈ List.range 200, f_20 y = true := by
  have h_dec : (List.range 200).all f_20 = true := by decide
  exact List.all_eq_true.mp h_dec

lemma h2_20 : ∀ y ∈ (List.range 400).drop 200, f_20 y = true := by
  have h_dec : ((List.range 400).drop 200).all f_20 = true := by decide
  exact List.all_eq_true.mp h_dec

lemma h3_20 : ∀ y ∈ (List.range 672).drop 400, f_20 y = true := by
  have h_dec : ((List.range 672).drop 400).all f_20 = true := by decide
  exact List.all_eq_true.mp h_dec

lemma h_eq_20 : List.range 672 = List.range 200 ++ (List.range 400).drop 200 ++ (List.range 672).drop 400 := rfl

lemma h_all_20 : ∀ y ∈ List.range 672, f_20 y = true := by
  rw [h_eq_20]
  intro y hy
  simp only [List.mem_append] at hy
  rcases hy with (hy | hy) | hy
  · exact h1_20 y hy
  · exact h2_20 y hy
  · exact h3_20 y hy

theorem a081512_candidates_20_ge (x : ℕ) (hx : x ∈ a081512_candidates 20) : 672 ≤ x := by
  by_contra! h
  have h_all_range : (List.range 672).all f_20 = true := List.all_eq_true.mpr h_all_20
  have h_mem : x ∈ List.range 672 := List.mem_range.mpr h
  have h_all := List.all_eq_true.mp h_all_range x h_mem
  rw [mem_a081512_candidates_iff] at hx
  rcases hx with ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_div_card : 20 ≤ (Nat.divisors x).card := by
    rw [← hD_card]
    exact Finset.card_le_card hD_pow
  by_cases h240 : x = 240
  · subst h240
    exact not_mem_a081512_20_240 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h336 : x = 336
  · subst h336
    exact not_mem_a081512_20_336 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h360 : x = 360
  · subst h360
    exact not_mem_a081512_20_360 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h420 : x = 420
  · subst h420
    exact not_mem_a081512_20_420 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h432 : x = 432
  · subst h432
    exact not_mem_a081512_20_432 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h480 : x = 480
  · subst h480
    exact not_mem_a081512_20_480 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h504 : x = 504
  · subst h504
    exact not_mem_a081512_20_504 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h528 : x = 528
  · subst h528
    exact not_mem_a081512_20_528 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h540 : x = 540
  · subst h540
    exact not_mem_a081512_20_540 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h560 : x = 560
  · subst h560
    exact not_mem_a081512_20_560 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h576 : x = 576
  · subst h576
    exact not_mem_a081512_20_576 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h600 : x = 600
  · subst h600
    exact not_mem_a081512_20_600 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h624 : x = 624
  · subst h624
    exact not_mem_a081512_20_624 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h630 : x = 630
  · subst h630
    exact not_mem_a081512_20_630 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h648 : x = 648
  · subst h648
    exact not_mem_a081512_20_648 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  by_cases h660 : x = 660
  · subst h660
    exact not_mem_a081512_20_660 ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  have h_not_cond : ¬ (x = 240 ∨ x = 336 ∨ x = 360 ∨ x = 420 ∨ x = 432 ∨ x = 480 ∨ x = 504 ∨ x = 528 ∨ x = 540 ∨ x = 560 ∨ x = 576 ∨ x = 600 ∨ x = 624 ∨ x = 630 ∨ x = 648 ∨ x = 660) := by
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact h240 rfl
    · exact h336 rfl
    · exact h360 rfl
    · exact h420 rfl
    · exact h432 rfl
    · exact h480 rfl
    · exact h504 rfl
    · exact h528 rfl
    · exact h540 rfl
    · exact h560 rfl
    · exact h576 rfl
    · exact h600 rfl
    · exact h624 rfl
    · exact h630 rfl
    · exact h648 rfl
    · exact h660 rfl
  have h_card : (Nat.divisors x).card < 20 := by
    have h_dec := of_decide_eq_true h_all
    by_cases h_cond : x = 240 ∨ x = 336 ∨ x = 360 ∨ x = 420 ∨ x = 432 ∨ x = 480 ∨ x = 504 ∨ x = 528 ∨ x = 540 ∨ x = 560 ∨ x = 576 ∨ x = 600 ∨ x = 624 ∨ x = 630 ∨ x = 648 ∨ x = 660
    · exfalso; exact h_not_cond h_cond
    · rw [if_neg h_cond] at h_dec
      exact h_dec
  omega

theorem a_twenty_le_a081512_twenty : a 20 ≤ a081512 20 := by
  unfold a a081512
  change sInf (a_candidates 20) ≤ sInf (a081512_candidates 20)
  have hB : (a081512_candidates 20).Nonempty := ⟨672, twenty_mem_a081512_twenty⟩
  have hB_ge : 672 ≤ sInf (a081512_candidates 20) := by
    have hmem := Nat.sInf_mem hB
    exact a081512_candidates_20_ge (sInf (a081512_candidates 20)) hmem
  have hA_le : sInf (a_candidates 20) ≤ 672 := Nat.sInf_le twenty_mem_a_twenty
  exact le_trans hA_le hB_ge


lemma not_mem_s_in_D {s : ℕ} (hs : 0 < s) {D : Finset ℕ} (hD_pow : D ⊆ Nat.divisors s) (hD_card : D.card ≥ 2) (hD_sum : D.sum id = s) :
    s ∉ D := by
  intro h_mem
  have h_sum := D.sum_erase_add id h_mem
  simp only [id_eq] at h_sum hD_sum
  rw [← h_sum] at hD_sum
  have hD_erase_card : (D.erase s).card = D.card - 1 := Finset.card_erase_of_mem h_mem
  have h_ne : (D.erase s).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hc_empty
    rw [hc_empty, Finset.card_empty] at hD_erase_card
    omega
  rcases h_ne with ⟨x, hx⟩
  have hx_D : x ∈ D := Finset.mem_of_mem_erase hx
  have hx_pos : x > 0 := Nat.pos_of_mem_divisors (hD_pow hx_D)
  have h_sum_pos : (D.erase s).sum id > 0 := by
    apply Finset.sum_pos
    · intro y hy
      have hy_D : y ∈ D := Finset.mem_of_mem_erase hy
      exact Nat.pos_of_mem_divisors (hD_pow hy_D)
    · exact ⟨x, hx⟩
  simp only [id_eq] at h_sum_pos
  omega

theorem twentyone_mem_a_twentyone : 720 ∈ a_candidates 21 := by
  rw [mem_a_candidates_iff]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24, 30, 36, 45, 72, 144, 240}
  refine ⟨by decide, by decide, by decide, by decide⟩


theorem twentyone_mem_a081512_twentyone : 720 ∈ a081512_candidates 21 := by
  rw [mem_a081512_candidates_iff]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24, 30, 36, 45, 72, 144, 240}
  refine ⟨by decide, by decide, by decide⟩


theorem a081512_candidates_21_ge (x : ℕ) (hx : x ∈ a081512_candidates 21) : 720 ≤ x := by
  by_contra! h
  have hk21 : 21 ≥ 21 := by omega
  have hx720 : 720 ≤ x := a081512_candidates_ge_twentyone_ge_720 21 hk21 x hx

  have h_decide : ((List.range 0).map (· + 720)).all (fun y =>
      decide ((Nat.divisors y).card < 21)) = true := by decide
  have h_mem : x ∈ ((List.range 0).map (· + 720)) := by
    rw [List.mem_map]
    use x - 720
    constructor
    · rw [List.mem_range]; omega
    · omega
  have h_all := List.all_eq_true.mp h_decide x h_mem

  rw [mem_a081512_candidates_iff] at hx
  rcases hx with ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_div_card : 21 ≤ (Nat.divisors x).card := by
    rw [← hD_card]
    exact Finset.card_le_card hD_pow

  have h_card : (Nat.divisors x).card < 21 := by
    have h_dec := of_decide_eq_true h_all
    exact h_dec
  omega


theorem a_twentyone_le_a081512_twentyone : a 21 ≤ a081512 21 := by
  unfold a a081512
  change sInf (a_candidates 21) ≤ sInf (a081512_candidates 21)
  have hB : (a081512_candidates 21).Nonempty := ⟨720, twentyone_mem_a081512_twentyone⟩
  have hB_ge : 720 ≤ sInf (a081512_candidates 21) := by
    have hmem := Nat.sInf_mem hB
    exact a081512_candidates_21_ge (sInf (a081512_candidates 21)) hmem
  have hA_le : sInf (a_candidates 21) ≤ 720 := Nat.sInf_le twentyone_mem_a_twentyone
  exact le_trans hA_le hB_ge


theorem twentytwo_mem_a_twentytwo : 720 ∈ a_candidates 22 := by
  rw [mem_a_candidates_iff]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24, 30, 40, 45, 60, 72, 80, 240}
  refine ⟨by decide, by decide, by decide, by decide⟩


theorem twentytwo_mem_a081512_twentytwo : 720 ∈ a081512_candidates 22 := by
  rw [mem_a081512_candidates_iff]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24, 30, 40, 45, 60, 72, 80, 240}
  refine ⟨by decide, by decide, by decide⟩


theorem a081512_candidates_22_ge (x : ℕ) (hx : x ∈ a081512_candidates 22) : 720 ≤ x := by
  by_contra! h
  have hk21 : 22 ≥ 21 := by omega
  have hx720 : 720 ≤ x := a081512_candidates_ge_twentyone_ge_720 22 hk21 x hx

  have h_decide : ((List.range 0).map (· + 720)).all (fun y =>
      decide ((Nat.divisors y).card < 22)) = true := by decide
  have h_mem : x ∈ ((List.range 0).map (· + 720)) := by
    rw [List.mem_map]
    use x - 720
    constructor
    · rw [List.mem_range]; omega
    · omega
  have h_all := List.all_eq_true.mp h_decide x h_mem

  rw [mem_a081512_candidates_iff] at hx
  rcases hx with ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_div_card : 22 ≤ (Nat.divisors x).card := by
    rw [← hD_card]
    exact Finset.card_le_card hD_pow

  have h_card : (Nat.divisors x).card < 22 := by
    have h_dec := of_decide_eq_true h_all
    exact h_dec
  omega


theorem a_twentytwo_le_a081512_twentytwo : a 22 ≤ a081512 22 := by
  unfold a a081512
  change sInf (a_candidates 22) ≤ sInf (a081512_candidates 22)
  have hB : (a081512_candidates 22).Nonempty := ⟨720, twentytwo_mem_a081512_twentytwo⟩
  have hB_ge : 720 ≤ sInf (a081512_candidates 22) := by
    have hmem := Nat.sInf_mem hB
    exact a081512_candidates_22_ge (sInf (a081512_candidates 22)) hmem
  have hA_le : sInf (a_candidates 22) ≤ 720 := Nat.sInf_le twentytwo_mem_a_twentytwo
  exact le_trans hA_le hB_ge


theorem twentythree_mem_a_twentythree : 720 ∈ a_candidates 23 := by
  rw [mem_a_candidates_iff]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 30, 36, 40, 45, 48, 60, 72, 80, 180}
  refine ⟨by decide, by decide, by decide, by decide⟩


theorem twentythree_mem_a081512_twentythree : 720 ∈ a081512_candidates 23 := by
  rw [mem_a081512_candidates_iff]
  refine ⟨by decide, ?_⟩
  use {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 30, 36, 40, 45, 48, 60, 72, 80, 180}
  refine ⟨by decide, by decide, by decide⟩


theorem a081512_candidates_23_ge (x : ℕ) (hx : x ∈ a081512_candidates 23) : 720 ≤ x := by
  by_contra! h
  have hk21 : 23 ≥ 21 := by omega
  have hx720 : 720 ≤ x := a081512_candidates_ge_twentyone_ge_720 23 hk21 x hx

  have h_decide : ((List.range 0).map (· + 720)).all (fun y =>
      decide ((Nat.divisors y).card < 23)) = true := by decide
  have h_mem : x ∈ ((List.range 0).map (· + 720)) := by
    rw [List.mem_map]
    use x - 720
    constructor
    · rw [List.mem_range]; omega
    · omega
  have h_all := List.all_eq_true.mp h_decide x h_mem

  rw [mem_a081512_candidates_iff] at hx
  rcases hx with ⟨hx0, D, hD_pow, hD_card, hD_sum⟩
  rw [Finset.mem_powerset] at hD_pow
  have h_div_card : 23 ≤ (Nat.divisors x).card := by
    rw [← hD_card]
    exact Finset.card_le_card hD_pow

  have h_card : (Nat.divisors x).card < 23 := by
    have h_dec := of_decide_eq_true h_all
    exact h_dec
  omega


