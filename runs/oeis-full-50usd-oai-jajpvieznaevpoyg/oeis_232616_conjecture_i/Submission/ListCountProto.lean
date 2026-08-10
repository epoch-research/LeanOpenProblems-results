import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Finset Nat

def L : List Nat := [2,3,5,7,11]

theorem L_chain : L.IsChain (· < ·) := by decide
theorem L_sorted : L.SortedLT := List.IsChain.sortedLT L_chain
theorem L_nodup : L.Nodup := L_sorted.nodup
theorem L_all_prime : L.Forall Nat.Prime := by repeat constructor <;> norm_num
theorem L_all_lt : L.Forall (fun x => x < 12) := by repeat constructor <;> norm_num

example : 5 ≤ Nat.count Nat.Prime 12 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 5 := by simpa [L] using List.toFinset_card_of_nodup L_nodup
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by
    simpa using (List.mem_toFinset.mp hx)
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ((List.forall_iff_forall_mem.1 L_all_lt) x hxL),
    (List.forall_iff_forall_mem.1 L_all_prime) x hxL⟩

example : Nat.nth Nat.Prime 4 < 12 := by
  have hc : 4 < Nat.count Nat.Prime 12 := by
    have h := (show 5 ≤ Nat.count Nat.Prime 12 from by
      rw [Nat.count_eq_card_filter_range]
      have hcard : L.toFinset.card = 5 := by simpa [L] using List.toFinset_card_of_nodup L_nodup
      rw [← hcard]
      apply Finset.card_le_card
      intro x hx
      have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ((List.forall_iff_forall_mem.1 L_all_lt) x hxL),
        (List.forall_iff_forall_mem.1 L_all_prime) x hxL⟩)
    omega
  exact Nat.nth_lt_of_lt_count hc
