import Mathlib
import Submission.Helper10
import Submission.Helper19
import Submission.Helper23
import Submission.Helper24

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
    intro hfalse
    have h_dec : (a_helper (100 * q + d) = m) := by exact of_decide_eq_true hfalse
    exact this h_dec
  rw [c99, zero_add]
  have hl : _ ≤ _ := List.countP_le_length (p := fun d => a_helper (100 * q + d) == m) (l := [99])
  exact hl

lemma count_m_le_1 (N q C m : ℕ) (hm8 : m ≠ 8) (hC : m ≤ C) (h8 : 8 ≤ C) :
  ((List.range N).filter (fun n => n / 100 == q)).countP (fun n => a_helper n == m) ≤
  if S q ≤ C then 100 else 1 := by
  split_ifs with h
  · have hl : _ ≤ _ := List.countP_le_length (p := fun n => a_helper n == m) (l := ((List.range N).filter (fun n => n / 100 == q)))
    have hl2 : ((List.range N).filter (fun n => n / 100 == q)).length ≤ 100 := count_filter_length_le N q
    omega
  · have h_count : ((List.range N).filter (fun n => n / 100 == q)).countP (fun n => a_helper n == m) ≤ (List.range 100).countP (fun d => a_helper (100 * q + d) == m) := by
      let L := (List.range 100).map (fun d => 100 * q + d)
      have h_subset : ∀ x ∈ ((List.range N).filter (fun n => n / 100 == q)), x ∈ L := by
        intro x hx
        simp only [List.mem_filter, List.mem_range, beq_iff_eq] at hx
        have hx_div : x / 100 = q := hx.right
        have hx_eq : x = 100 * q + x % 100 := by
          have : x = 100 * (x / 100) + x % 100 := Nat.div_add_mod x 100 |>.symm
          rw [hx_div] at this
          exact this
        have hx_mod : x % 100 < 100 := Nat.mod_lt x (by decide)
        simp only [L, List.mem_map, List.mem_range]
        use x % 100
        exact ⟨hx_mod, by omega⟩
      have hl_nodup : ((List.range N).filter (fun n => n / 100 == q)).Nodup := by
        apply List.Nodup.filter
        exact List.nodup_range
      have hL_nodup : L.Nodup := by
        apply List.Nodup.map
        · intros x y hxy
          have : 100 * q + x = 100 * q + y := hxy
          omega
        · exact List.nodup_range
      have hsub : ((List.range N).filter (fun n => n / 100 == q)) ⊆ L := h_subset
      have hl_len : (((List.range N).filter (fun n => n / 100 == q)).filter (fun n => a_helper n == m)).length ≤ (L.filter (fun n => a_helper n == m)).length := by
        apply list_length_le_of_subset_nodup
        · apply List.Nodup.filter
          exact hl_nodup
        · intro x hx
          simp only [List.mem_filter] at hx ⊢
          have hx_l : x ∈ List.filter (fun n => n / 100 == q) (List.range N) := by
            simp only [List.mem_filter]
            exact hx.left
          exact ⟨h_subset x hx_l, hx.right⟩
      have h1 : (((List.range N).filter (fun n => n / 100 == q)).filter (fun n => a_helper n == m)).length = ((List.range N).filter (fun n => n / 100 == q)).countP (fun n => a_helper n == m) := by
        rw [List.countP_eq_length_filter]
      have h2 : (L.filter (fun n => a_helper n == m)).length = (List.range 100).countP (fun d => a_helper (100 * q + d) == m) := by
        have : (L.filter (fun n => a_helper n == m)).length = L.countP (fun n => a_helper n == m) := by rw [List.countP_eq_length_filter]
        rw [this]
        dsimp [L]
        rw [List.countP_map]
        rfl
      omega
    have hq_gt : S q > C := by omega
    have h_block := countP_block_ne_8 q C m hm8 hC h8 hq_gt
    omega
