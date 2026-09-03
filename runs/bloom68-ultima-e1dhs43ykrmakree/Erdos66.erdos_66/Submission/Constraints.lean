import FormalConjecturesUtil

/-!
# Verified elementary constraints for the logarithmic representation problem

This file is independent of `Submission.Spec`.  It proves only necessary
conditions, not the existence or nonexistence of the set in the problem.
-/

namespace Erdos66Constraints

open Filter AdditiveCombinatorics
open scoped Topology Classical

/-- Any nonzero limit in the question is positive. -/
theorem limit_pos {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) : 0 < c := by
  have hn : 0 ≤ c := ge_of_tendsto' h (fun n ↦
    div_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg n))
  exact lt_of_le_of_ne hn (Ne.symm hc)

/-- Such a set is an asymptotic basis for the nonnegative integers. -/
theorem eventually_sumRep_pos {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    ∀ᶠ n in atTop, 0 < sumRep A n := by
  have hp := h.eventually_const_lt (limit_pos hc h)
  filter_upwards [hp] with n hn
  have hr : (0 : ℝ) < sumRep A n := by
    rcases div_pos_iff.mp hn with hh | hh
    · exact hh.1
    · exact False.elim ((not_lt_of_ge (Nat.cast_nonneg _)) hh.1)
  exact Nat.cast_pos.mp hr

/-- In particular, no finite set can satisfy the proposed limit. -/
theorem infinite_of_limit {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) : A.Infinite := by
  classical
  by_contra hf
  obtain ⟨M, hM⟩ := (Set.not_infinite.mp hf).bddAbove
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_sumRep_pos hc h)
  let n := max N (2 * M + 1)
  have hp := hN n (le_max_left _ _)
  rw [sumRep_def, Finset.card_pos] at hp
  obtain ⟨⟨a, b⟩, hab⟩ := hp
  simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hab
  have ha := hM hab.2.1
  have hb := hM hab.2.2
  have hn : 2 * M + 1 ≤ n := le_max_right _ _
  omega

private noncomputable def repPairs (A : Set ℕ) (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (Finset.antidiagonal n).filter (fun p ↦ p.1 ∈ A ∧ p.2 ∈ A)

private theorem mem_repPairs (A : Set ℕ) (n a b : ℕ) :
    (a, b) ∈ repPairs A n ↔ a + b = n ∧ a ∈ A ∧ b ∈ A := by
  classical
  simp [repPairs, Finset.mem_antidiagonal]

/-- Off-diagonal representations are paired by swapping the two summands. -/
private theorem card_repPairs_split (A : Set ℕ) (n : ℕ) :
    (repPairs A n).card =
      2 * ((repPairs A n).filter (fun p ↦ p.1 < p.2)).card +
      ((repPairs A n).filter (fun p ↦ p.1 = p.2)).card := by
  classical
  let S := repPairs A n
  have hs : ∀ p : ℕ × ℕ, p ∈ S ↔ p.swap ∈ S := by
    rintro ⟨a, b⟩
    simp [S, mem_repPairs, add_comm, and_comm]
  have hswap : (S.filter (fun p ↦ p.1 < p.2)).card =
      (S.filter (fun p ↦ p.2 < p.1)).card := by
    apply Finset.card_bij (fun p _ ↦ p.swap)
    · intro p hp
      simp only [Finset.mem_filter] at hp ⊢
      exact ⟨(hs p).mp hp.1, hp.2⟩
    · intro p hp q hq hpq
      exact Prod.swap_injective hpq
    · intro p hp
      refine ⟨p.swap, ?_, Prod.swap_swap p⟩
      simp only [Finset.mem_filter] at hp ⊢
      exact ⟨(hs p).mp hp.1, hp.2⟩
  have hfirst := Finset.card_filter_add_card_filter_not (s := S)
    (fun p ↦ p.1 < p.2)
  have hsecond := Finset.card_filter_add_card_filter_not
    (s := S.filter (fun p ↦ ¬p.1 < p.2)) (fun p ↦ p.1 = p.2)
  have heq : ((S.filter (fun p ↦ ¬p.1 < p.2)).filter (fun p ↦ p.1 = p.2)) =
      S.filter (fun p ↦ p.1 = p.2) := by
    ext p : 1
    simp only [Finset.mem_filter]
    constructor <;> intro hp
    · exact ⟨hp.1.1, hp.2⟩
    · exact ⟨⟨hp.1, by omega⟩, hp.2⟩
  have hgt : ((S.filter (fun p ↦ ¬p.1 < p.2)).filter (fun p ↦ ¬p.1 = p.2)) =
      S.filter (fun p ↦ p.2 < p.1) := by
    ext p : 1
    simp only [Finset.mem_filter]
    constructor <;> intro hp
    · exact ⟨hp.1.1, by omega⟩
    · exact ⟨⟨hp.1, by omega⟩, by omega⟩
  rw [heq, hgt] at hsecond
  change S.card = 2 * (S.filter (fun p ↦ p.1 < p.2)).card +
    (S.filter (fun p ↦ p.1 = p.2)).card
  omega

/-- The representation count at an even integer has the parity of its diagonal term. -/
theorem sumRep_even_index_mod_two (A : Set ℕ) (m : ℕ) :
    sumRep A (2 * m) % 2 = if m ∈ A then 1 else 0 := by
  classical
  have hd : ((repPairs A (2 * m)).filter (fun p ↦ p.1 = p.2)) =
      if m ∈ A then {(m, m)} else ∅ := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, mem_repPairs]
    by_cases hm : m ∈ A
    · simp only [if_pos hm, Finset.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨hab, ha, hb⟩, heq⟩
        omega
      · rintro ⟨rfl, rfl⟩
        exact ⟨⟨by omega, hm, hm⟩, rfl⟩
    · simp only [if_neg hm, Finset.notMem_empty, iff_false]
      rintro ⟨⟨hab, ha, hb⟩, heq⟩
      have ham : a = m := by omega
      exact hm (ham ▸ ha)
  have hsplit := card_repPairs_split A (2 * m)
  rw [hd] at hsplit
  have hr : sumRep A (2 * m) = (repPairs A (2 * m)).card := sumRep_def A _
  rw [hr, hsplit]
  split_ifs <;> simp

/-- The ordered representation count at an odd integer is always even. -/
theorem sumRep_odd_index_mod_two (A : Set ℕ) (m : ℕ) :
    sumRep A (2 * m + 1) % 2 = 0 := by
  classical
  have hd : ((repPairs A (2 * m + 1)).filter (fun p ↦ p.1 = p.2)) = ∅ := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, mem_repPairs, Finset.notMem_empty, iff_false]
    omega
  have hsplit := card_repPairs_split A (2 * m + 1)
  rw [hd, Finset.card_empty, add_zero] at hsplit
  have hr : sumRep A (2 * m + 1) = (repPairs A (2 * m + 1)).card := sumRep_def A _
  rw [hr, hsplit]
  omega

end Erdos66Constraints

#print axioms Erdos66Constraints.limit_pos
#print axioms Erdos66Constraints.eventually_sumRep_pos
#print axioms Erdos66Constraints.infinite_of_limit
#print axioms Erdos66Constraints.sumRep_even_index_mod_two
#print axioms Erdos66Constraints.sumRep_odd_index_mod_two
