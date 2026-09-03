import Submission.OptimalCoverCore

/-! Exact ordered reduction of finite prime-class covers. At each step the
residue of the chosen prime is determined by the first uncovered position.
This gives a finite permutation reduction, not a bound on its stopping point. -/
namespace Erdos970.GreedyCoverOrder
open Finset

/-- First position, with an arbitrary default once no positions remain. -/
def firstPosition (U : Finset ℕ) : ℕ := if h : U.Nonempty then U.min' h else 0

lemma firstPosition_mem {U : Finset ℕ} (hU : U.Nonempty) : firstPosition U ∈ U := by
  simp only [firstPosition, dif_pos hU]
  exact min'_mem U hU

lemma firstPosition_le {U : Finset ℕ} {i : ℕ} (hi : i ∈ U) : firstPosition U ≤ i := by
  simp only [firstPosition, dif_pos (show U.Nonempty from ⟨i, hi⟩)]
  exact min'_le U i hi

/-- Delete the class of the first uncovered position. -/
def greedyStep (U : Finset ℕ) (p : ℕ) : Finset ℕ :=
  U.filter (fun i => ¬i ≡ firstPosition U [MOD p])

lemma greedyStep_subset (U : Finset ℕ) (p : ℕ) : greedyStep U p ⊆ U := filter_subset _ _

@[simp] lemma greedyStep_empty (p : ℕ) : greedyStep ∅ p = ∅ := by simp [greedyStep]

lemma greedyStep_card_lt {U : Finset ℕ} (hU : U.Nonempty) (p : ℕ) :
    (greedyStep U p).card < U.card := by
  apply card_lt_card
  apply ssubset_iff_subset_ne.mpr
  refine ⟨greedyStep_subset U p, ?_⟩
  intro he
  have hh : firstPosition U ∈ greedyStep U p := by
    simpa only [he] using firstPosition_mem hU
  exact (mem_filter.mp hh).2 (Nat.ModEq.refl _)

/-- Run the successive first-uncovered-position deletions in a specified order. -/
def greedyResidual : Finset ℕ → List ℕ → Finset ℕ
  | U, [] => U
  | U, p :: l => greedyResidual (greedyStep U p) l

@[simp] lemma greedyResidual_empty (l : List ℕ) : greedyResidual ∅ l = ∅ := by
  induction l with
  | nil => rfl
  | cons p l ih => simpa only [greedyResidual, greedyStep_empty] using ih

lemma greedyResidual_subset (U : Finset ℕ) (l : List ℕ) : greedyResidual U l ⊆ U := by
  induction l generalizing U with
  | nil => exact subset_rfl
  | cons p l ih => exact (ih (greedyStep U p)).trans (greedyStep_subset U p)

/-- A residue assignment for the ordered construction. -/
def greedyResidues : Finset ℕ → List ℕ → ℕ → ℕ
  | _, [] => fun _ => 0
  | U, p :: l => Function.update (greedyResidues (greedyStep U p) l) p (firstPosition U)

lemma greedyResidual_covers (U : Finset ℕ) (l : List ℕ) (hl : l.Nodup)
    (i : ℕ) (hi : i ∈ U) (hrem : i ∉ greedyResidual U l) :
    ∃ p ∈ l, i ≡ greedyResidues U l p [MOD p] := by
  induction l generalizing U with
  | nil => exact False.elim (hrem hi)
  | cons p l ih =>
    by_cases hh : i ≡ firstPosition U [MOD p]
    · exact ⟨p, by simp, by simpa [greedyResidues] using hh⟩
    · have hi' : i ∈ greedyStep U p := mem_filter.mpr ⟨hi, hh⟩
      obtain ⟨q, hql, hq⟩ := ih (greedyStep U p) (List.nodup_cons.mp hl).2 hi' hrem
      have hqp : q ≠ p := by rintro rfl; exact (List.nodup_cons.mp hl).1 hql
      refine ⟨q, by simp [hql], ?_⟩
      simpa only [greedyResidues, Function.update_of_ne hqp] using hq

/-- Every cover is represented by some ordering of its moduli, using the
first uncovered position to determine the phase at each step. No primality
assumption is needed for this exact reduction. -/
theorem exists_greedy_order (U P : Finset ℕ) (r : ℕ → ℕ)
    (hcover : ∀ i ∈ U, ∃ p ∈ P, i ≡ r p [MOD p]) :
    ∃ l : List ℕ, l.Nodup ∧ l.toFinset = P ∧ greedyResidual U l = ∅ := by
  classical
  induction hn : P.card using Nat.strong_induction_on generalizing U P r with
  | h n ih =>
    by_cases hU : U.Nonempty
    · obtain ⟨p, hp, hr⟩ := hcover (firstPosition U) (firstPosition_mem hU)
      have hnew : ∀ i ∈ greedyStep U p, ∃ q ∈ P.erase p, i ≡ r q [MOD q] := by
        intro i hi
        obtain ⟨hi, havoid⟩ := mem_filter.mp hi
        obtain ⟨q, hq, hhit⟩ := hcover i hi
        have hqp : q ≠ p := by
          rintro rfl
          exact havoid (hhit.trans hr.symm)
        exact ⟨q, mem_erase.mpr ⟨hqp, hq⟩, hhit⟩
      obtain ⟨l, hl, hlP, hrem⟩ := ih (P.erase p).card
        (by rw [← hn]; exact card_erase_lt_of_mem hp)
        (greedyStep U p) (P.erase p) r hnew rfl
      refine ⟨p :: l, ?_, ?_, hrem⟩
      · apply List.nodup_cons.mpr
        refine ⟨?_, hl⟩
        intro hpl
        have hm : p ∈ l.toFinset := List.mem_toFinset.mpr hpl
        rw [hlP] at hm
        exact (mem_erase.mp hm).1 rfl
      · rw [List.toFinset_cons, hlP, insert_erase hp]
    · have he : U = ∅ := not_nonempty_iff_eq_empty.mp hU
      exact ⟨P.sort (· ≤ ·), P.sort_nodup _, P.sort_toFinset _, by simp [he]⟩

/-- Exact converse: an empty greedy residual supplies a cover with those moduli. -/
theorem cover_iff_greedy_order (U P : Finset ℕ) :
    (∃ r : ℕ → ℕ, ∀ i ∈ U, ∃ p ∈ P, i ≡ r p [MOD p]) ↔
      ∃ l : List ℕ, l.Nodup ∧ l.toFinset = P ∧ greedyResidual U l = ∅ := by
  constructor
  · rintro ⟨r, hr⟩
    exact exists_greedy_order U P r hr
  · rintro ⟨l, hl, hP, he⟩
    refine ⟨greedyResidues U l, ?_⟩
    intro i hi
    obtain ⟨p, hp, hhit⟩ := greedyResidual_covers U l hl i hi (by simp [he])
    refine ⟨p, ?_, hhit⟩
    rw [← hP]
    exact List.mem_toFinset.mpr hp

/-- A finite, phase-free version: it is enough to test the permutations of
one list of the moduli. -/
theorem cover_iff_permutations (U P : Finset ℕ) :
    (∃ r : ℕ → ℕ, ∀ i ∈ U, ∃ p ∈ P, i ≡ r p [MOD p]) ↔
      ∃ l ∈ (P.sort (· ≤ ·)).permutations, greedyResidual U l = ∅ := by
  rw [cover_iff_greedy_order]
  constructor
  · rintro ⟨l, hl, hP, he⟩
    refine ⟨l, List.mem_permutations.mpr ?_, he⟩
    apply List.perm_of_nodup_nodup_toFinset_eq hl (P.sort_nodup _)
    simpa using hP
  · rintro ⟨l, hl, he⟩
    have hp := List.mem_permutations.mp hl
    have hn : l.Nodup := hp.nodup_iff.mpr (P.sort_nodup _)
    refine ⟨l, hn, ?_, he⟩
    ext p
    simpa using hp.mem_iff

/-- The Jacobsthal bound is exactly nontermination of every admissible greedy
prime ordering before the prescribed interval has been exhausted. -/
theorem isJacobsthalBound_iff_greedy (k m : ℕ) :
    IsJacobsthalBound k m ↔
      ∀ l : List ℕ, l.Nodup → (∀ p ∈ l, p.Prime) → l.length ≤ k →
        (greedyResidual (range m) l).Nonempty := by
  classical
  constructor
  · intro hb l hl hp hk
    by_contra hn
    have he : greedyResidual (range m) l = ∅ := not_nonempty_iff_eq_empty.mp hn
    apply ((not_isJacobsthalBound_iff_cover k m).mpr ?_) hb
    refine ⟨l.toFinset, ?_, ?_, greedyResidues (range m) l, ?_⟩
    · intro p hpP
      exact hp p (List.mem_toFinset.mp hpP)
    · rwa [List.toFinset_card_of_nodup hl]
    · intro i hi
      obtain ⟨p, hpl, hhit⟩ := greedyResidual_covers (range m) l hl i
        (mem_range.mpr hi) (by simp [he])
      exact ⟨p, List.mem_toFinset.mpr hpl, hhit⟩
  · intro hall
    by_contra hb
    obtain ⟨P, hP, hk, r, hc⟩ := (not_isJacobsthalBound_iff_cover k m).mp hb
    obtain ⟨l, hl, hlP, he⟩ := exists_greedy_order (range m) P r
      (fun i hi => hc i (mem_range.mp hi))
    have hprime : ∀ p ∈ l, p.Prime := by
      intro p hp
      apply hP p
      rw [← hlP]
      exact List.mem_toFinset.mpr hp
    have hlength : l.length ≤ k := by
      rw [← List.toFinset_card_of_nodup hl, hlP]
      exact hk
    have hh := hall l hl hprime hlength
    rw [he] at hh
    exact not_nonempty_empty hh

#print axioms cover_iff_permutations
#print axioms isJacobsthalBound_iff_greedy

#print axioms exists_greedy_order
#print axioms cover_iff_greedy_order
end Erdos970.GreedyCoverOrder
