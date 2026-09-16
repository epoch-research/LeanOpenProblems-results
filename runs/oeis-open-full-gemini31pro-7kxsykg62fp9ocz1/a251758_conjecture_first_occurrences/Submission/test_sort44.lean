import Mathlib
import Submission.Spec
open List Finset

def list_divisors (n : ℕ) : List ℕ :=
  (List.range (n + 1)).filter (fun x => if x > 0 then n % x == 0 else false)

lemma mem_list_divisors {n x : ℕ} (hn : n ≠ 0) : x ∈ list_divisors n ↔ x ∈ Nat.divisors n := by
  rw [list_divisors, mem_filter, List.mem_range, Nat.mem_divisors]
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : if x > 0 then (n % x == 0) = true else False := by aesop
    split at h3
    · have h4 : n % x = 0 := by aesop
      have h5 : x ∣ n := Nat.dvd_of_mod_eq_zero h4
      exact ⟨h5, hn⟩
    · contradiction
  · rintro ⟨h1, h2⟩
    have h3 : n % x = 0 := Nat.mod_eq_zero_of_dvd h1
    have hle : x ≤ n := Nat.le_of_dvd (by omega) h1
    have h4 : x < n + 1 := by omega
    refine ⟨h4, ?_⟩
    have hx : x > 0 := by
      by_contra hc
      have : x = 0 := by omega
      subst this
      have : n = 0 := eq_zero_of_zero_dvd h1
      contradiction
    rw [if_pos hx]
    aesop

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
  apply List.Perm.eq_of_pairwise (le := (· ≤ ·))
  · exact fun a b _ _ hab hba => by omega
  · exact pairwise_le_list_divisors n
  · exact pairwise_sort _ (· ≤ ·)
  · apply (List.perm_ext_iff_of_nodup (list_divisors_nodup n) (sort_nodup _ _)).mpr
    intro x
    rw [mem_list_divisors hn, mem_sort]

def a_comp (n : ℕ) : ℕ :=
  let divs := list_divisors n
  let s := (divs.zip divs.tail).map (fun p => p.1 * p.2) |>.sum
  if s = 0 then 0 else n ^ 2 / s

theorem a_eq_a_comp (n : ℕ) (hn : n ≠ 0) : a n = a_comp n := by
  unfold a a_comp
  have h := list_divisors_eq n hn
  rw [← h]
