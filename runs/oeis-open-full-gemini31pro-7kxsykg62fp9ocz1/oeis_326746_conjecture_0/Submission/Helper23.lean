import Mathlib
import Submission.Helper10

lemma list_length_le_of_subset_nodup {α} [DecidableEq α] (l L : List α)
  (hl : l.Nodup) (hL : ∀ x ∈ l, x ∈ L) : l.length ≤ L.length := by
  have : l.toFinset ⊆ L.toFinset := by
    intro x hx
    simp only [List.mem_toFinset] at hx ⊢
    exact hL x hx
  have h_card : l.toFinset.card ≤ L.toFinset.card := Finset.card_le_card this
  have h1 : l.toFinset.card = l.length := List.toFinset_card_of_nodup hl
  have h2 : L.toFinset.card ≤ L.length := List.toFinset_card_le L
  omega

lemma count_filter_length_le (N q : ℕ) :
  ((List.range N).filter (fun n => n / 100 == q)).length ≤ 100 := by
  let L := (List.range 100).map (fun d => 100 * q + d)
  have hL_len : L.length = 100 := by simp [L]
  let l := (List.range N).filter (fun n => n / 100 == q)
  have h_nodup : l.Nodup := by
    apply List.Nodup.filter
    exact List.nodup_range
  have h_subset : ∀ x ∈ l, x ∈ L := by
    intro x hx
    simp only [l, List.mem_filter, List.mem_range, beq_iff_eq] at hx
    have hx_div : x / 100 = q := hx.right
    have hx_eq : x = 100 * q + x % 100 := by
      have : x = 100 * (x / 100) + x % 100 := Nat.div_add_mod x 100 |>.symm
      rw [hx_div] at this
      exact this
    have hx_mod : x % 100 < 100 := Nat.mod_lt x (by decide)
    simp only [L, List.mem_map, List.mem_range]
    use x % 100
    exact ⟨hx_mod, by omega⟩
  have hl_len : l.length ≤ L.length := list_length_le_of_subset_nodup l L h_nodup h_subset
  have eq_len : l.length = ((List.range N).filter (fun n => n / 100 == q)).length := by rfl
  omega
