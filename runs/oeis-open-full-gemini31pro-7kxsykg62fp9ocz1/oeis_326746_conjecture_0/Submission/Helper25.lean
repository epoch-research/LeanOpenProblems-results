import Mathlib
import Submission.Helper10
import Submission.Helper19
import Submission.Helper23
import Submission.Helper24

lemma list_countP_le_of_subset_nodup {α} [DecidableEq α] (l L : List α)
  (p : α → Bool) (h_sub : ∀ x ∈ l, x ∈ L) (hl_nodup : l.Nodup) :
  l.countP p ≤ L.countP p := by
  have H1 : l.countP p = (l.filter p).length := by rw [List.countP_eq_length_filter]
  have H2 : L.countP p = (L.filter p).length := by rw [List.countP_eq_length_filter]
  rw [H1, H2]
  apply list_length_le_of_subset_nodup
  · apply List.Nodup.filter p hl_nodup
  · intro x hx
    simp only [List.mem_filter] at hx ⊢
    exact ⟨h_sub x hx.1, hx.2⟩

lemma countP_block_8_lower (q C : ℕ) (hC : 8 ≤ C) (hq : S q > C) :
  (List.range 100).countP (fun d => a_helper (100 * q + d) == 8) ≥ 9 := by
  let L := [9, 19, 29, 39, 49, 59, 69, 79, 89]
  have h_sub : ∀ x ∈ L, x ∈ List.range 100 := by decide
  have h_nodup : L.Nodup := by decide
  have h_len : L.length = 9 := by decide
  have h_all : ∀ d ∈ L, a_helper (100 * q + d) = 8 := by
    intros d hd
    have hd_lt : d < 99 := by
      revert d hd
      decide
    have heq : d % 10 = 9 := by
      revert d hd
      decide
    rw [a_100_eq_9 q d hd_lt heq]
    apply Nat.mod_eq_of_lt
    omega
  have h_count_L : L.countP (fun d => a_helper (100 * q + d) == 8) = 9 := by
    rw [List.countP_eq_length_filter]
    have : L.filter (fun d => a_helper (100 * q + d) == 8) = L := by
      apply List.filter_eq_self.mpr
      intro x hx
      simp only [beq_iff_eq]
      exact h_all x hx
    rw [this, h_len]
  have h_le : L.countP (fun d => a_helper (100 * q + d) == 8) ≤ (List.range 100).countP (fun d => a_helper (100 * q + d) == 8) := by
    apply list_countP_le_of_subset_nodup L (List.range 100) _ h_sub h_nodup
  exact Nat.le_trans (by omega) h_le

lemma count_8_ge_9 (N q C : ℕ) (hC : 8 ≤ C) (hq : S q > C) (hN : 100 * q + 100 ≤ N) :
  ((List.range N).filter (fun n => n / 100 == q)).countP (fun n => a_helper n == 8) ≥ 9 := by
  let L := (List.range 100).map (fun d => 100 * q + d)
  have h_sub : ∀ x ∈ L, x ∈ ((List.range N).filter (fun n => n / 100 == q)) := by
    intro x hx
    simp only [L, List.mem_map, List.mem_range] at hx
    rcases hx with ⟨d, hd, rfl⟩
    simp only [List.mem_filter, List.mem_range, beq_iff_eq]
    have hd_lt : d < 100 := hd
    refine ⟨by omega, ?_⟩
    have : (100 * q + d) / 100 = q := by
      rw [add_comm, Nat.add_mul_div_left d q (by decide)]
      have : d / 100 = 0 := Nat.div_eq_of_lt hd_lt
      rw [this, zero_add]
    exact this
  have h_nodup : L.Nodup := by
    apply List.Nodup.map
    · intros x y hxy
      dsimp only at hxy
      omega
    · exact List.nodup_range
  have h_le : L.countP (fun n => a_helper n == 8) ≤ ((List.range N).filter (fun n => n / 100 == q)).countP (fun n => a_helper n == 8) := by
    apply list_countP_le_of_subset_nodup L _ _ h_sub h_nodup
  have h_eq : L.countP (fun n => a_helper n == 8) = (List.range 100).countP (fun d => a_helper (100 * q + d) == 8) := by
    dsimp [L]
    rw [List.countP_map]
    rfl
  rw [h_eq] at h_le
  have h_lower := countP_block_8_lower q C hC hq
  exact Nat.le_trans h_lower h_le
