import FormalConjectures.Util.ProblemImports

open Finset Nat Set

-- Definition of candidates for a081512
def S_a08 (n : ℕ) : Set ℕ :=
  { m : ℕ | 0 < m ∧
    ∃ D : Finset ℕ,
      D ⊆ Nat.divisors m ∧
      D.card = n ∧
      D.sum id = m }

-- Proof that 12 is in candidates for n=4
lemma twelve_mem_candidates : 12 ∈ S_a08 4 := by
  dsimp [S_a08]
  refine ⟨by decide, ?_⟩
  -- Witness D = {1, 2, 3, 6}
  use {1, 2, 3, 6}
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> decide
  · rfl
  · rfl

-- We want to prove that no m < 12 is in S_a08 4.
-- Since m < 12 is finite, we can write a decidable predicate.
abbrev is_candidate_dec (n m : ℕ) : Prop :=
  m ≠ 0 ∧ ((Nat.divisors m).powerset.filter (fun D => D.card = n ∧ D.sum id = m)) ≠ ∅

-- Let's prove that is_candidate_dec is equivalent to membership in S_a08
lemma is_candidate_dec_iff (n m : ℕ) : is_candidate_dec n m ↔ m ∈ S_a08 n := by
  dsimp [is_candidate_dec, S_a08]
  constructor
  · rintro ⟨hm0, hD⟩
    refine ⟨Nat.pos_of_ne_zero hm0, ?_⟩
    rcases Finset.nonempty_iff_ne_empty.mpr hD with ⟨D, hDmem⟩
    simp only [Finset.mem_filter, Finset.mem_powerset] at hDmem
    exact ⟨D, hDmem.1, hDmem.2.1, hDmem.2.2⟩
  · rintro ⟨hm0, D, hD, hcard, hsum⟩
    refine ⟨hm0.ne', ?_⟩
    apply Finset.nonempty_iff_ne_empty.mp
    use D
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hD, hcard, hsum⟩

lemma no_smaller_candidate : ∀ m < 12, m ∉ S_a08 4 := by
  intro m hm
  rw [← is_candidate_dec_iff]
  interval_cases m <;> decide

lemma a081512_four : sInf (S_a08 4) = 12 := by
  have h12 : 12 ∈ S_a08 4 := by
    rw [← is_candidate_dec_iff]
    decide
  have h_le : sInf (S_a08 4) ≤ 12 := Nat.sInf_le h12
  have h_ge : 12 ≤ sInf (S_a08 4) := by
    have h_nonempty : (S_a08 4).Nonempty := ⟨12, h12⟩
    have h_mem : sInf (S_a08 4) ∈ S_a08 4 := Nat.sInf_mem h_nonempty
    have h_lt : ¬ sInf (S_a08 4) < 12 := by
      intro hc
      exact no_smaller_candidate _ hc h_mem
    omega
  omega

def S_a (n : ℕ) : Set ℕ :=
  { m : ℕ | 0 < m ∧
    ∃ D : Finset ℕ,
      D ⊆ Nat.divisors m ∧
      D.card = n ∧
      D.sum id = m ∧
      D.lcm id = m }

abbrev is_a_candidate_dec (n m : ℕ) : Prop :=
  m ≠ 0 ∧ ((Nat.divisors m).powerset.filter (fun D => D.card = n ∧ D.sum id = m ∧ D.lcm id = m)) ≠ ∅

lemma is_a_candidate_dec_iff (n m : ℕ) : is_a_candidate_dec n m ↔ m ∈ S_a n := by
  dsimp [is_a_candidate_dec, S_a]
  constructor
  · rintro ⟨hm0, hD⟩
    refine ⟨Nat.pos_of_ne_zero hm0, ?_⟩
    rcases Finset.nonempty_iff_ne_empty.mpr hD with ⟨D, hDmem⟩
    simp only [Finset.mem_filter, Finset.mem_powerset] at hDmem
    exact ⟨D, hDmem.1, hDmem.2.1, hDmem.2.2.1, hDmem.2.2.2⟩
  · rintro ⟨hm0, D, hD, hcard, hsum, hlcm⟩
    refine ⟨hm0.ne', ?_⟩
    apply Finset.nonempty_iff_ne_empty.mp
    use D
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hD, hcard, hsum, hlcm⟩


lemma no_smaller_candidate_a_four : ∀ m < 18, m ∉ S_a 4 := by
  intro m hm
  rw [← is_a_candidate_dec_iff]
  interval_cases m <;> decide

lemma a_four : sInf (S_a 4) = 18 := by
  have h18 : 18 ∈ S_a 4 := by
    rw [← is_a_candidate_dec_iff]
    decide
  have h_le : sInf (S_a 4) ≤ 18 := Nat.sInf_le h18
  have h_ge : 18 ≤ sInf (S_a 4) := by
    have h_nonempty : (S_a 4).Nonempty := ⟨18, h18⟩
    have h_mem : sInf (S_a 4) ∈ S_a 4 := Nat.sInf_mem h_nonempty
    have h_lt : ¬ sInf (S_a 4) < 18 := by
      intro hc
      exact no_smaller_candidate_a_four _ hc h_mem
    omega
  omega

lemma no_smaller_candidate_a08_five : ∀ m < 24, m ∉ S_a08 5 := by
  intro m hm
  rw [← is_candidate_dec_iff]
  interval_cases m <;> decide

lemma a081512_five : sInf (S_a08 5) = 24 := by
  have h24 : 24 ∈ S_a08 5 := by
    rw [← is_candidate_dec_iff]
    decide
  have h_le : sInf (S_a08 5) ≤ 24 := Nat.sInf_le h24
  have h_ge : 24 ≤ sInf (S_a08 5) := by
    have h_nonempty : (S_a08 5).Nonempty := ⟨24, h24⟩
    have h_mem : sInf (S_a08 5) ∈ S_a08 5 := Nat.sInf_mem h_nonempty
    have h_lt : ¬ sInf (S_a08 5) < 24 := by
      intro hc
      exact no_smaller_candidate_a08_five _ hc h_mem
    omega
  omega

lemma no_smaller_candidate_a_five : ∀ m < 28, m ∉ S_a 5 := by
  intro m hm
  rw [← is_a_candidate_dec_iff]
  interval_cases m <;> decide

lemma a_five : sInf (S_a 5) = 28 := by
  have h28 : 28 ∈ S_a 5 := by
    rw [← is_a_candidate_dec_iff]
    decide
  have h_le : sInf (S_a 5) ≤ 28 := Nat.sInf_le h28
  have h_ge : 28 ≤ sInf (S_a 5) := by
    have h_nonempty : (S_a 5).Nonempty := ⟨28, h28⟩
    have h_mem : sInf (S_a 5) ∈ S_a 5 := Nat.sInf_mem h_nonempty
    have h_lt : ¬ sInf (S_a 5) < 28 := by
      intro hc
      exact no_smaller_candidate_a_five _ hc h_mem
    omega
  omega


lemma S_a_subset_S_a08 (n : ℕ) : S_a n ⊆ S_a08 n := by
  intro m hm
  rcases hm with ⟨hm0, D, hD, hcard, hsum, hlcm⟩
  exact ⟨hm0, D, hD, hcard, hsum⟩

-- We want to prove S_a 1 is nonempty
lemma S_a_one_nonempty : (S_a 1).Nonempty := by
  use 1
  dsimp [S_a]
  refine ⟨by decide, ?_⟩
  use {1}
  refine ⟨?_, by decide, by decide, by decide⟩
  intro x hx
  simp only [Finset.mem_singleton] at hx
  rw [hx]
  decide

-- We want to prove S_a n is nonempty for n >= 3
-- But wait, do we really need to prove S_a n is nonempty for n >= 3 to get a081512 n <= a n?
-- What if we just use a081512 n <= a n for the cases we need?
-- Actually, the direction (n = 4 ∨ n = 5) → a n > a081512 n only requires:
-- a 4 > a081512 4 and a 5 > a081512 5.
-- Since we already have a081512 4 = 12, a 4 = 18, a081512 5 = 24, a 5 = 28,
-- we can prove these concrete inequalities without any general theorems!
-- Let's check:
lemma a_four_gt_a08_four : a081512 4 < a 4 := by
  -- Since a081512 4 = 12 and a 4 = 18
  -- wait, we can just rewrite!
  rw [a081512_four, a_four]
  decide

lemma a_five_gt_a08_five : a081512 5 < a 5 := by
  rw [a081512_five, a_five]
  decide

