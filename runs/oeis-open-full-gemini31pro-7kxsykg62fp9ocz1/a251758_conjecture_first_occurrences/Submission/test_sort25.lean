import Mathlib

open List Finset

def list_divisors (n : ℕ) : List ℕ :=
  (List.range (n + 1)).filter (fun x => if h : x > 0 then n % x == 0 else false)

lemma mem_list_divisors {n x : ℕ} (hn : n ≠ 0) : x ∈ list_divisors n ↔ x ∈ Nat.divisors n := by
  rw [list_divisors, mem_filter, List.mem_range, Nat.mem_divisors]
  constructor
  · rintro ⟨h1, h2⟩
    dsimp at h2
    split at h2
    · next hx =>
      have h3 : n % x = 0 := by aesop
      have h4 : x ∣ n := Nat.dvd_of_mod_eq_zero h3
      exact ⟨h4, hn⟩
    · aesop
  · rintro ⟨h1, h2⟩
    have h3 : n % x = 0 := Nat.mod_eq_zero_of_dvd h1
    have hle : x ≤ n := Nat.le_of_dvd (by omega) h1
    have h4 : x < n + 1 := by omega
    refine ⟨h4, ?_⟩
    dsimp
    have hx : x > 0 := by omega
    split
    · aesop
    · contradiction

lemma list_divisors_nodup (n : ℕ) : (list_divisors n).Nodup := by
  apply Nodup.filter
  apply nodup_range

lemma pairwise_le_list_divisors (n : ℕ) : (list_divisors n).Pairwise (· ≤ ·) := by
  apply Pairwise.filter
  have h1 : (List.range (n + 1)).Pairwise (· < ·) := pairwise_lt_range
  apply Pairwise.imp _ h1
  intro a b hab
  omega

theorem list_divisors_eq (n : ℕ) (hn : n ≠ 0) : list_divisors n = (Nat.divisors n).sort (· ≤ ·) := by
  apply List.Perm.eq_of_pairwise _ (fun a b _ _ hab hba => by omega)
  · exact pairwise_le_list_divisors n
  · exact pairwise_sort (· ≤ ·) _
  · apply List.ext_le (by sorry)
    sorry
