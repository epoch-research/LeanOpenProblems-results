import Mathlib
open Nat Set Finset

noncomputable def A290012 (n : ℕ) : ℕ :=
  let S_n : ℕ := (Finset.range n).sum (fun k => (Nat.nth Nat.Prime k) ^ 2)
  sInf { p : ℕ | p.Prime ∧ S_n ≤ p ^ 2 }

lemma a1 : A290012 1 = 2 := by
  unfold A290012
  have hS : (Finset.range 1).sum (fun k => (Nat.nth Nat.Prime k) ^ 2) = 4 := by
    rw [Finset.sum_range_succ, Finset.sum_range_zero, Nat.nth_prime_zero_eq_two]; norm_num
  simp only [hS]
  apply le_antisymm
  · apply Nat.sInf_le; exact ⟨by norm_num, by norm_num⟩
  · apply le_csInf
    · exact ⟨2, ⟨by norm_num, by norm_num⟩⟩
    · intro b hb; obtain ⟨hp, hb2⟩ := hb; exact hp.two_le

lemma a2 : A290012 2 = 5 := by
  unfold A290012
  have hS : (Finset.range 2).sum (fun k => (Nat.nth Nat.Prime k) ^ 2) = 13 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
        Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]; norm_num
  simp only [hS]
  apply le_antisymm
  · apply Nat.sInf_le; exact ⟨by norm_num, by norm_num⟩
  · apply le_csInf
    · exact ⟨5, ⟨by norm_num, by norm_num⟩⟩
    · intro b hb; obtain ⟨hp, hb2⟩ := hb
      by_contra h; push_neg at h
      interval_cases b <;> simp_all (config := {decide := true})

lemma a3 : A290012 3 = 7 := by
  unfold A290012
  have hS : (Finset.range 3).sum (fun k => (Nat.nth Nat.Prime k) ^ 2) = 38 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three,
        Nat.nth_prime_two_eq_five]; norm_num
  simp only [hS]
  apply le_antisymm
  · apply Nat.sInf_le; exact ⟨by norm_num, by norm_num⟩
  · apply le_csInf
    · exact ⟨7, ⟨by norm_num, by norm_num⟩⟩
    · intro b hb; obtain ⟨hp, hb2⟩ := hb
      by_contra h; push_neg at h
      interval_cases b <;> simp_all (config := {decide := true})

theorem oeis_a290012_conjecture_unique_twin_prime :
  ∀ n : ℕ, 1 ≤ n → (A290012 (n + 1) = A290012 n + 2 ↔ n = 2) :=
by
  intro n hn
  match n, hn with
  | 1, _ =>
    rw [show (1:ℕ)+1 = 2 from rfl, a2, a1]
    constructor
    · intro h; omega
    · intro h; omega
  | 2, _ =>
    rw [show (2:ℕ)+1 = 3 from rfl, a3, a2]
    constructor
    · intro _; rfl
    · intro _; rfl
  | (m+3), _ =>
    apply iff_of_false
    · -- ¬ (A290012 (m+4) = A290012 (m+3) + 2)
      sorry
    · omega
