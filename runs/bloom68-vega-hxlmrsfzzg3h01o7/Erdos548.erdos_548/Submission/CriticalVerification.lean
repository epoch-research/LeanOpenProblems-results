import Submission.Critical

/-!
# Interface and boundary checks for `Submission.Critical`

First compile `Critical.lean` to
`.lake/build/lib/lean/Submission/Critical.olean`, then run this file with
`lake env lean Submission/CriticalVerification.lean`.
These examples only use the completed infrastructure, not `Spec` or `Auxiliary`.
-/

open SimpleGraph Erdos548.Critical

/-- The `Finite`-only interface produces an ordinary `Copy`. -/
example {A V : Type*} [Finite A] [Finite V] [Nonempty V]
    (T : SimpleGraph A) (G : SimpleGraph V) (m : ℕ)
    (hcard : Nat.card A = m + 1) (hT : T.IsTree)
    (hG : ∀ x, m ≤ (G.neighborSet x).ncard) : Nonempty (T.Copy G) :=
  isContained_of_isTree_of_card_eq_succ_of_neighborSet_ncard T G m hcard hT hG

/-- The minimum-degree theorem includes the one-vertex case. -/
example (T : SimpleGraph (Fin 1)) (G : SimpleGraph (Fin 1)) (hT : T.IsTree) :
    T.IsContained G := by
  classical
  exact fin_tree_isContained_of_minDegree (by omega) T G hT (Nat.zero_le _)

/-- Omitting nonemptiness for the host would make the one-vertex claim false. -/
example (T : SimpleGraph (Fin 1)) (G : SimpleGraph (Fin 0)) : ¬ T.IsContained G := by
  rintro ⟨f⟩
  exact Fin.elim0 (f 0)

/-- A nonempty edgeless graph has positive excess at `k = 0`: no truncated
natural subtraction has silently replaced the negative threshold. -/
example : ∃ s : Set (Fin 1), s.Nonempty ∧
    IsInducedCritical 0 ((⊥ : SimpleGraph (Fin 1)).induce s) := by
  apply exists_induced_critical_of_edge_threshold
  norm_num [SimpleGraph.edgeSet_bot, Nat.card_eq_fintype_card]

/-- No empty graph has positive excess. -/
example (k : ℕ) (G : SimpleGraph (Fin 0)) : ¬ 0 < excess k G := by
  simp

/-- The full reduction accepts the edge-count expression used for `Fin n`. -/
example {n k : ℕ} (G : SimpleGraph (Fin n))
    (hG : ((k : ℚ) - 1) / 2 * n < (G.edgeSet.ncard : ℚ)) :
    ∃ s : Set (Fin n), s.Nonempty ∧ IsInducedCritical k (G.induce s) ∧
      (∀ t : Set s, t.Nonempty →
        ((k : ℚ) - 1) / 2 * t.ncard < ((incidentEdges (G.induce s) t).ncard : ℚ)) ∧
      (∀ x : s, ⌈(k : ℚ) / 2⌉₊ ≤ ((G.induce s).neighborSet x).ncard) ∧
      (∃ x : s, k ≤ ((G.induce s).neighborSet x).ncard) := by
  apply exists_critical_reduction
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using hG

/-- Incident edges of the empty set are empty, explaining the nonempty-set
hypothesis in the strict inequality. -/
example (G : SimpleGraph (Fin 3)) : (incidentEdges G ∅).ncard = 0 := by
  simp
