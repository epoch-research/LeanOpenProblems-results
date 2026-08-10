import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000
open Finset Nat Set

def S_a08 (n : ℕ) : Set ℕ :=
  { m : ℕ | 0 < m ∧
    ∃ D : Finset ℕ,
      D ⊆ Nat.divisors m ∧
      D.card = n ∧
      D.sum id = m }

abbrev is_candidate_dec (n m : ℕ) : Prop :=
  m ≠ 0 ∧ ((Nat.divisors m).powerset.filter (fun D => D.card = n ∧ D.sum id = m)) ≠ ∅

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

lemma t240 : ¬ is_candidate_dec 16 240 := by decide

















