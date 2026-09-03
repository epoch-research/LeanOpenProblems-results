import FormalConjecturesUtil

/-!
An auxiliary obstruction to a proposed optimal-transition argument.
This file does not prove or disprove the original conjecture.
-/

namespace Erdos184.LocalMatchingFace

/-- The fifteen perfect matchings of six labelled ports. Each pair is stored
in increasing order, as are the three first coordinates. -/
def matchings : Fin 15 → Fin 3 → Fin 6 × Fin 6 :=
  ![![(0, 1), (2, 3), (4, 5)],
    ![(0, 1), (2, 4), (3, 5)],
    ![(0, 1), (2, 5), (3, 4)],
    ![(0, 2), (1, 3), (4, 5)],
    ![(0, 2), (1, 4), (3, 5)],
    ![(0, 2), (1, 5), (3, 4)],
    ![(0, 3), (1, 2), (4, 5)],
    ![(0, 3), (1, 4), (2, 5)],
    ![(0, 3), (1, 5), (2, 4)],
    ![(0, 4), (1, 2), (3, 5)],
    ![(0, 4), (1, 3), (2, 5)],
    ![(0, 4), (1, 5), (2, 3)],
    ![(0, 5), (1, 2), (3, 4)],
    ![(0, 5), (1, 3), (2, 4)],
    ![(0, 5), (1, 4), (2, 3)]]

/-- A linear edge-weight objective evaluated on a local matching. -/
def score (w : (Fin 6 × Fin 6) → ℝ) (i : Fin 15) : ℝ :=
  ∑ j : Fin 3, w (matchings i j)

/-- Equality of the incidence vectors of two one-factorizations of K₆,
with their common matching cancelled. -/
theorem factorization_relation (w : (Fin 6 × Fin 6) → ℝ) :
    score w 0 + score w 4 + score w 8 + score w 10 =
      score w 1 + score w 3 + score w 7 + score w 11 := by
  simp only [score, Fin.sum_univ_three]
  change
    (w (0, 1) + w (2, 3) + w (4, 5)) +
    (w (0, 2) + w (1, 4) + w (3, 5)) +
    (w (0, 3) + w (1, 5) + w (2, 4)) +
    (w (0, 4) + w (1, 3) + w (2, 5)) =
    (w (0, 1) + w (2, 4) + w (3, 5)) +
    (w (0, 2) + w (1, 3) + w (4, 5)) +
    (w (0, 3) + w (1, 4) + w (2, 5)) +
    (w (0, 4) + w (1, 5) + w (2, 3))
  ring

/-- If the other fourteen matchings all have the same linear score,
then the remaining matching has that score too. -/
theorem omitted_matching_score (w : (Fin 6 × Fin 6) → ℝ) (b : ℝ)
    (h : ∀ i : Fin 15, i ≠ 0 → score w i = b) : score w 0 = b := by
  have h1 := h 1 (by decide)
  have h3 := h 3 (by decide)
  have h4 := h 4 (by decide)
  have h7 := h 7 (by decide)
  have h8 := h 8 (by decide)
  have h10 := h 10 (by decide)
  have h11 := h 11 (by decide)
  have hr := factorization_relation w
  linarith

/-- No linear objective exposes exactly these fourteen matching vertices.
This does not identify any graph's set of optimal transition matchings. -/
theorem no_exposing_objective :
    ¬ ∃ (w : (Fin 6 × Fin 6) → ℝ) (b : ℝ),
      (∀ i : Fin 15, i ≠ 0 → score w i = b) ∧ score w 0 < b := by
  rintro ⟨w, b, h, hlt⟩
  exact (ne_of_lt hlt) (omitted_matching_score w b h)

end Erdos184.LocalMatchingFace
