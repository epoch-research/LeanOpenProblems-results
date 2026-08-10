import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Finset Nat Set Classical

def L : List Nat := [2,3,5,7,11]
lemma L_nodup : L.Nodup := by decide
lemma L_prime : L.Forall Nat.Prime := by repeat constructor <;> norm_num
lemma L_bound : L.Forall (fun p => p < 12) := by repeat constructor <;> norm_num

lemma count_lower : 5 ≤ Nat.count Nat.Prime 12 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 5 := by rw [List.toFinset_card_of_nodup L_nodup]; rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp L_bound) x hxL, (List.forall_iff_forall_mem.mp L_prime) x hxL⟩

example : Nat.nth Nat.Prime 3 ≤ 7 := by
  have hlt : 3 < Nat.count Nat.Prime 8 := by
    have h : 4 ≤ Nat.count Nat.Prime 8 := by norm_num [Nat.count, Nat.Prime]
    omega
  exact Nat.le_of_lt_succ (Nat.nth_lt_of_lt_count (p:=Nat.Prime) hlt)
