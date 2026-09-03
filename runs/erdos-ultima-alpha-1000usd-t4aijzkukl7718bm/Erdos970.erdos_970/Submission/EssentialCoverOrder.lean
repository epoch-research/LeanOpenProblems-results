import Submission.GreedyCoverOrder

/-! Minimal subcovers and residue-preserving ordered encodings. Essentialness
ensures that the greedy process does not stop before every modulus has been
used. No estimate on the maximal covered interval is asserted here. -/
namespace Erdos970.GreedyCoverOrder
open Finset

def Covers (U P : Finset ℕ) (r : ℕ → ℕ) : Prop :=
  ∀ i ∈ U, ∃ p ∈ P, i ≡ r p [MOD p]

/-- Every retained class has a point not covered by any other retained class. -/
def EssentialCover (U P : Finset ℕ) (r : ℕ → ℕ) : Prop :=
  Covers U P r ∧ ∀ p ∈ P, ∃ i ∈ U, i ≡ r p [MOD p] ∧
    ∀ q ∈ P, q ≠ p → ¬i ≡ r q [MOD q]

lemma exists_essential_subcover (U P : Finset ℕ) (r : ℕ → ℕ) (hc : Covers U P r) :
    ∃ Q ⊆ P, EssentialCover U Q r := by
  classical
  have hex : ∃ n : ℕ, ∃ Q ⊆ P, Covers U Q r ∧ Q.card = n :=
    ⟨P.card, P, subset_rfl, hc, rfl⟩
  obtain ⟨Q, hQP, hQ, hcard⟩ := Nat.find_spec hex
  refine ⟨Q, hQP, hQ, ?_⟩
  intro p hp
  by_contra hn
  push_neg at hn
  have hnew : Covers U (Q.erase p) r := by
    intro i hi
    obtain ⟨q, hq, hhit⟩ := hQ i hi
    by_cases hqp : q = p
    · subst q
      obtain ⟨q, hq, hqp, hhit'⟩ := hn i hi hhit
      exact ⟨q, mem_erase.mpr ⟨hqp, hq⟩, hhit'⟩
    · exact ⟨q, mem_erase.mpr ⟨hqp, hq⟩, hhit⟩
  have hmin := Nat.find_min' hex ⟨Q.erase p, (erase_subset p Q).trans hQP, hnew, rfl⟩
  have hlt := card_erase_lt_of_mem hp
  omega

lemma EssentialCover.empty {P : Finset ℕ} {r : ℕ → ℕ}
    (h : EssentialCover ∅ P r) : P = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨i, hi, _⟩ := h.2 p hp
  exact notMem_empty i hi

lemma EssentialCover.step {U P : Finset ℕ} {r : ℕ → ℕ}
    (h : EssentialCover U P r) (p : ℕ) (hp : p ∈ P)
    (hr : firstPosition U ≡ r p [MOD p]) :
    EssentialCover (greedyStep U p) (P.erase p) r := by
  constructor
  · intro i hi
    obtain ⟨hi, havoid⟩ := mem_filter.mp hi
    obtain ⟨q, hq, hhit⟩ := h.1 i hi
    have hqp : q ≠ p := by
      rintro rfl
      exact havoid (hhit.trans hr.symm)
    exact ⟨q, mem_erase.mpr ⟨hqp, hq⟩, hhit⟩
  · intro q hq
    obtain ⟨hqp, hqP⟩ := mem_erase.mp hq
    obtain ⟨i, hi, hhit, hprivate⟩ := h.2 q hqP
    refine ⟨i, mem_filter.mpr ⟨hi, ?_⟩, hhit, ?_⟩
    · intro hh
      exact hprivate p hp hqp.symm (hh.trans hr)
    · intro v hv hvq
      exact hprivate v (mem_of_mem_erase hv) hvq

/-- An essential cover admits a greedy order which reproduces every original
residue, modulo its modulus. This is stronger than just finding another cover. -/
theorem exists_essential_order (U P : Finset ℕ) (r : ℕ → ℕ)
    (hc : EssentialCover U P r) :
    ∃ l : List ℕ, l.Nodup ∧ l.toFinset = P ∧ greedyResidual U l = ∅ ∧
      ∀ p ∈ P, r p ≡ greedyResidues U l p [MOD p] := by
  classical
  induction hn : P.card using Nat.strong_induction_on generalizing U P r with
  | h n ih =>
    by_cases hU : U.Nonempty
    · obtain ⟨p, hp, hr⟩ := hc.1 (firstPosition U) (firstPosition_mem hU)
      obtain ⟨l, hl, hlP, hrem, hres⟩ := ih (P.erase p).card
        (by rw [← hn]; exact card_erase_lt_of_mem hp)
        (greedyStep U p) (P.erase p) r (hc.step p hp hr) rfl
      refine ⟨p :: l, ?_, ?_, hrem, ?_⟩
      · apply List.nodup_cons.mpr
        refine ⟨?_, hl⟩
        intro hpl
        have hm : p ∈ l.toFinset := List.mem_toFinset.mpr hpl
        rw [hlP] at hm
        exact (mem_erase.mp hm).1 rfl
      · rw [List.toFinset_cons, hlP, insert_erase hp]
      · intro q hq
        by_cases hqp : q = p
        · subst q
          simpa only [greedyResidues, Function.update_self] using hr.symm
        · simpa only [greedyResidues, Function.update_of_ne hqp] using
            hres q (mem_erase.mpr ⟨hqp, hq⟩)
    · have he : U = ∅ := not_nonempty_iff_eq_empty.mp hU
      have hP : P = ∅ := (he ▸ hc).empty
      refine ⟨[], by simp, by simp [hP], by simp [greedyResidual, he], ?_⟩
      simp [hP]

/-- At most one normalized essential residue assignment is encoded by each
permutation. The witness here is the encoding, without a probabilistic claim. -/
theorem essential_order_mem_permutations (U P : Finset ℕ) (r : ℕ → ℕ)
    (hc : EssentialCover U P r) :
    ∃ l ∈ (P.sort (· ≤ ·)).permutations,
      ∀ p ∈ P, r p ≡ greedyResidues U l p [MOD p] := by
  obtain ⟨l, hl, hlP, _, hr⟩ := exists_essential_order U P r hc
  refine ⟨l, List.mem_permutations.mpr ?_, hr⟩
  apply List.perm_of_nodup_nodup_toFinset_eq hl (P.sort_nodup _)
  simpa using hlP

/-- Residues already assigned by a prefix are independent of the remaining
ordering, even without a no-repetition assumption. -/
lemma greedyResidues_append_of_mem (U : Finset ℕ) (l t : List ℕ)
    (p : ℕ) (hp : p ∈ l) :
    greedyResidues U (l ++ t) p = greedyResidues U l p := by
  induction l generalizing U with
  | nil => simp at hp
  | cons q l ih =>
    by_cases hpq : p = q
    · subst p
      simp [greedyResidues]
    · have hpl : p ∈ l := (List.mem_cons.mp hp).resolve_left hpq
      simp only [List.cons_append, greedyResidues, Function.update_of_ne hpq]
      exact ih (greedyStep U q) hpl

lemma greedyResidues_take_of_mem (U : Finset ℕ) (l : List ℕ)
    (j p : ℕ) (hp : p ∈ l.take j) :
    greedyResidues U l p = greedyResidues U (l.take j) p := by
  conv_lhs => rw [← List.take_append_drop j l]
  exact greedyResidues_append_of_mem U (l.take j) (l.drop j) p hp

#print axioms greedyResidues_take_of_mem

#print axioms exists_essential_subcover
#print axioms exists_essential_order
#print axioms essential_order_mem_permutations
end Erdos970.GreedyCoverOrder
