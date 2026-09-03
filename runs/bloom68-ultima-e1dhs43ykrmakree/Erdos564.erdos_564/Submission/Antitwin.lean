import Submission.Persistent

/-!
# Antitwin witnesses in critical triple colorings

A link opposite to an old vertex's actual link can only have witnesses avoiding that
vertex. Thus every vertex of a critical coloring has a full near-core of the opposite
link color. For a robust partial coloring at maximum order the near-core may moreover
be chosen persistent. These statements do not assert a quantitative Ramsey bound.
-/

set_option autoImplicit false

namespace AntitwinColoring

open CriticalColoring PersistentColoring

variable {α : Type*} [DecidableEq α]

/-- Complement the old link of `v`. Only pair values matter. -/
def antitwinLink (c : Finset α → Bool) (v : α) (e : Finset α) : Bool :=
  !(c (insert v e))

/-- A core of size at least three matching the antitwin link cannot contain `v`. -/
theorem antitwin_witness_avoids_vertex {c : Finset α → Bool} {v : α}
    {S : Finset α} {b : Bool} (hS : 3 ≤ S.card)
    (hc : MonoTripleOn c S b)
    (hℓ : ∀ e : Finset α, e ⊆ S → e.card = 2 → antitwinLink c v e = b) :
    v ∉ S := by
  intro hv
  have herase : 2 ≤ (S.erase v).card := by
    rw [Finset.card_erase_of_mem hv]
    omega
  obtain ⟨e, he, hecard⟩ := Finset.exists_subset_card_eq herase
  have hve : v ∉ e := fun h => Finset.notMem_erase v S (he h)
  have heS : e ⊆ S := he.trans (Finset.erase_subset v S)
  have hcolor := hc (insert v e) (Finset.insert_subset hv heS)
    (by rw [Finset.card_insert_of_notMem hve, hecard])
  have hcontra := hℓ e heS hecard
  simp only [antitwinLink, hcolor] at hcontra
  cases b <;> cases hcontra

/-- A critical coloring has a monochromatic full near-core disjoint from `v`, with
all triples from `v` to its pairs in the opposite color. -/
theorem exists_mismatching_nearcore {c : Finset α → Bool} {n : ℕ}
    (hn : 4 ≤ n) (hcrit : IsCritical c n) (v : α) :
    ∃ S : Finset α, S.card = n - 1 ∧ v ∉ S ∧ ∃ b : Bool,
      MonoTripleOn c S b ∧
        ∀ e : Finset α, e ⊆ S → e.card = 2 → c (insert v e) = !b := by
  obtain ⟨S, hS, b, hc, hℓ⟩ := hcrit.2 (antitwinLink c v)
  refine ⟨S, hS, antitwin_witness_avoids_vertex (by omega) hc hℓ, b, hc, ?_⟩
  intro e he hecard
  have h := hℓ e he hecard
  change Bool.not (c (insert v e)) = b at h
  simpa using congrArg Bool.not h

/-- The persistent version needs only an UNSAT persistent formula and a completion.
In particular, the same partial pattern supplies a witness for every choice of its
independently free triples. -/
theorem exists_persistent_mismatching_nearcore {P : Finset α → Option Bool}
    {c : Finset α → Bool} {n : ℕ} (hn : 4 ≤ n) (hc : Completes P c)
    (hunsat : ¬ ∃ ℓ : Finset α → Bool, Satisfies P ℓ n) (v : α) :
    ∃ S : Finset α, v ∉ S ∧ ∃ b : Bool,
      PersistentNearCore P n S b ∧
        ∀ e : Finset α, e ⊆ S → e.card = 2 → c (insert v e) = !b := by
  have hw : PersistentWitness P (antitwinLink c v) n := by
    by_contra h
    exact hunsat ⟨antitwinLink c v, h⟩
  obtain ⟨S, b, hS, hℓ⟩ := hw
  have hm : MonoTripleOn c S b := by
    intro e he hcard
    exact hc e hcard b (hS.2 e he hcard)
  refine ⟨S, antitwin_witness_avoids_vertex (by have := hS.1; omega) hm hℓ,
    b, hS, ?_⟩
  intro e he hecard
  have h := hℓ e he hecard
  change Bool.not (c (insert v e)) = b at h
  simpa using congrArg Bool.not h

/-- Maximum-order robustness provides the UNSAT hypothesis in the persistent theorem. -/
theorem exists_persistent_mismatching_nearcore_of_maximum_order [Fintype α]
    {P : Finset α → Option Bool} {c : Finset α → Bool} {n : ℕ}
    (hn : 4 ≤ n) (hR : 0 < Combinatorics.hypergraphRamsey 3 n)
    (hcard : Fintype.card α = Combinatorics.hypergraphRamsey 3 n - 1)
    (hP : Robust P n) (hc : Completes P c) (v : α) :
    ∃ S : Finset α, v ∉ S ∧ ∃ b : Bool,
      PersistentNearCore P n S b ∧
        ∀ e : Finset α, e ⊆ S → e.card = 2 → c (insert v e) = !b :=
  exists_persistent_mismatching_nearcore hn hc (unsat_of_maximum_order hR hcard hP) v

end AntitwinColoring

#print axioms AntitwinColoring.antitwin_witness_avoids_vertex
#print axioms AntitwinColoring.exists_mismatching_nearcore
#print axioms AntitwinColoring.exists_persistent_mismatching_nearcore
#print axioms AntitwinColoring.exists_persistent_mismatching_nearcore_of_maximum_order
