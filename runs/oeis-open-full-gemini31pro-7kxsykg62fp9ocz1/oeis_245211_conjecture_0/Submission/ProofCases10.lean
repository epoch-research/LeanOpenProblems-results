import Submission.Spec
import Mathlib

open Nat Finset

lemma tau_ge_four {m q r : ℕ} (hm : 0 < m) (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r) (hdq : q ∣ m) (hdr : r ∣ m) :
  4 ≤ (Nat.divisors m).card := by
  have h_coprime : q.Coprime r := by
    rw [hq.coprime_iff_not_dvd]
    intro h
    exact hqr.symm ((hr.eq_one_or_self_of_dvd q h).resolve_left hq.ne_one).symm
  have hdvd : q * r ∣ m := h_coprime.mul_dvd_of_dvd_of_dvd hdq hdr
  have h_sub : {q * r, r, q, 1} ⊆ m.divisors := by
    intro d hd
    rw [mem_divisors]
    simp only [mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨hdvd, hm.ne.symm⟩
    · exact ⟨hdr, hm.ne.symm⟩
    · exact ⟨hdq, hm.ne.symm⟩
    · exact ⟨one_dvd m, hm.ne.symm⟩
  have h_card : ({q * r, r, q, 1} : Finset ℕ).card = 4 := by
    have hq2 : 2 ≤ q := hq.two_le
    have hr2 : 2 ≤ r := hr.two_le
    have h1 : q * r ∉ ({r, q, 1} : Finset ℕ) := by
      simp only [mem_insert, mem_singleton]
      push_neg
      constructor
      · intro h; nlinarith
      · constructor
        · intro h; nlinarith
        · intro h; nlinarith
    have h2 : r ∉ ({q, 1} : Finset ℕ) := by
      simp only [mem_insert, mem_singleton]
      push_neg
      exact ⟨hqr.symm, hr.ne_one⟩
    have h3 : q ∉ ({1} : Finset ℕ) := by
      simp only [mem_singleton]
      exact hq.ne_one
    rw [card_insert_of_notMem h1, card_insert_of_notMem h2, card_insert_of_notMem h3, card_singleton]
  rw [← h_card]
  exact card_le_card h_sub
