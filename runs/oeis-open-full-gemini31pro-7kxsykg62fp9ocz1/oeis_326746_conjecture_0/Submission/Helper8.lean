import Mathlib

def S (n : ℕ) : ℕ := (Nat.digits 10 n).sum
def a_helper (n : ℕ) : ℕ := S n % S (n + 1)

lemma S_10 (q d : ℕ) (hd : d < 10) : S (10 * q + d) = S q + d := by
  by_cases hq : q = 0
  · simp [hq, S]
    cases d with
    | zero => simp
    | succ d =>
      have : d + 1 < 10 := hd
      rw [Nat.digits_of_lt _ _ (by omega) (by omega)]
      simp
  · have h1 : 10 * q + d > 0 := by omega
    have h2 : 1 < 10 := by decide
    unfold S
    rw [Nat.digits_def' h2 h1]
    have h3 : (10 * q + d) % 10 = d := by omega
    have h4 : (10 * q + d) / 10 = q := by omega
    rw [h3, h4]
    simp [add_comm]

lemma S_100 (q d : ℕ) (hd : d < 100) : S (100 * q + d) = S q + d / 10 + d % 10 := by
  have : 100 * q + d = 10 * (10 * q + d / 10) + d % 10 := by omega
  rw [this]
  rw [S_10 (10 * q + d / 10) (d % 10) (by omega)]
  rw [S_10 q (d / 10) (by omega)]

lemma a_100_eq (q d : ℕ) (hd : d < 99) (hneq : d % 10 ≠ 9) :
  a_helper (100 * q + d) = S q + d / 10 + d % 10 := by
  unfold a
  have hd_succ : d + 1 < 100 := by omega
  rw [S_100 q d (by omega)]
  have h_succ : 100 * q + d + 1 = 100 * q + (d + 1) := by omega
  rw [h_succ, S_100 q (d + 1) hd_succ]
  have h_div : (d + 1) / 10 = d / 10 := by omega
  have h_mod : (d + 1) % 10 = d % 10 + 1 := by omega
  rw [h_div, h_mod]
  have : S q + d / 10 + (d % 10 + 1) = S q + d / 10 + d % 10 + 1 := by omega
  rw [this]
  apply Nat.mod_eq_of_lt
  omega

lemma a_100_eq_9 (q d : ℕ) (hd : d < 99) (heq : d % 10 = 9) :
  a_helper (100 * q + d) = 8 % (S q + d / 10 + 1) := by
  unfold a
  have hd_succ : d + 1 < 100 := by omega
  rw [S_100 q d (by omega)]
  have h_succ : 100 * q + d + 1 = 100 * q + (d + 1) := by omega
  rw [h_succ, S_100 q (d + 1) hd_succ]
  have h_div : (d + 1) / 10 = d / 10 + 1 := by omega
  have h_mod : (d + 1) % 10 = 0 := by omega
  rw [h_div, h_mod]
  have eq1 : S q + (d / 10 + 1) + 0 = S q + d / 10 + 1 := by omega
  rw [eq1]
  have h_mod_d : d % 10 = 9 := heq
  rw [h_mod_d]
  have eq2 : S q + d / 10 + 9 = (S q + d / 10 + 1) + 8 := by omega
  rw [eq2]
  rw [Nat.add_mod]
  have : (S q + d / 10 + 1) % (S q + d / 10 + 1) = 0 := Nat.mod_self _
  rw [this]
  simp

lemma countP_block_ne_8 (q C m : ℕ) (hm8 : m ≠ 8) (hC : m ≤ C) (h8 : 8 ≤ C) (hq : S q > C) :
  (List.range 100).countP (fun d => a_helper (100 * q + d) == m) ≤ 1 := by
  have H : ∀ d ∈ List.range 100, d ≠ 99 → a_helper (100 * q + d) ≠ m := by
    intros d hd hd99
    have hd_lt : d < 100 := by simpa using hd
    have hd_lt_99 : d < 99 := by omega
    by_cases hneq : d % 10 = 9
    · rw [a_100_eq_9 q d hd_lt_99 hneq]
      have : S q + d / 10 + 1 > 8 := by omega
      have eq : 8 % (S q + d / 10 + 1) = 8 := Nat.mod_eq_of_lt (by omega)
      rw [eq]
      exact hm8.symm
    · rw [a_100_eq q d hd_lt_99 hneq]
      have : S q + d / 10 + d % 10 > m := by omega
      omega
  have r100 : List.range 100 = List.range 99 ++ [99] := by rfl
  rw [r100, List.countP_append]
  have c99 : (List.range 99).countP (fun d => a_helper (100 * q + d) == m) = 0 := by
    rw [List.countP_eq_zero]
    intros d hd
    simp only [List.mem_range] at hd
    have hd_100 : d ∈ List.range 100 := by simp; omega
    have hd_neq : d ≠ 99 := by omega
    have := H d hd_100 hd_neq
    simp [this]
  rw [c99, zero_add]
  have hl : _ ≤ _ := List.countP_le_length (p := fun d => a_helper (100 * q + d) == m) (l := [99])
  exact hl

lemma countP_block_8_lower (q : ℕ) (hq : S q > 8) :
  9 ≤ (List.range 100).countP (fun d => a_helper (100 * q + d) == 8) := by
  let L := [9, 19, 29, 39, 49, 59, 69, 79, 89]
  have hsub : L.Sublist (List.range 100) := by decide
  have H : ∀ d ∈ L, a_helper (100 * q + d) = 8 := by
    intros d hd
    revert hd
    dsimp [L]
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · rw [a_100_eq_9 q 9 (by decide) (by decide)]
      exact Nat.mod_eq_of_lt (by omega)
    · rw [a_100_eq_9 q 19 (by decide) (by decide)]
      exact Nat.mod_eq_of_lt (by omega)
    · rw [a_100_eq_9 q 29 (by decide) (by decide)]
      exact Nat.mod_eq_of_lt (by omega)
    · rw [a_100_eq_9 q 39 (by decide) (by decide)]
      exact Nat.mod_eq_of_lt (by omega)
    · rw [a_100_eq_9 q 49 (by decide) (by decide)]
      exact Nat.mod_eq_of_lt (by omega)
    · rw [a_100_eq_9 q 59 (by decide) (by decide)]
      exact Nat.mod_eq_of_lt (by omega)
    · rw [a_100_eq_9 q 69 (by decide) (by decide)]
      exact Nat.mod_eq_of_lt (by omega)
    · rw [a_100_eq_9 q 79 (by decide) (by decide)]
      exact Nat.mod_eq_of_lt (by omega)
    · rw [a_100_eq_9 q 89 (by decide) (by decide)]
      exact Nat.mod_eq_of_lt (by omega)
  have h_count : L.countP (fun d => a_helper (100 * q + d) == 8) = 9 := by
    rw [List.countP_eq_length_filter]
    have : L.filter (fun d => a_helper (100 * q + d) == 8) = L := by
      apply List.filter_eq_self.mpr
      intros d hd
      have := H d hd
      simp [this]
    rw [this]
    rfl
  have h_le := List.Sublist.countP_le (p := fun d => a_helper (100 * q + d) == 8) hsub
  omega
