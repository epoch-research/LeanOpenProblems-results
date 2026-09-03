import Submission.Bipartite

/-!
# Interface and boundary checks for the bipartite-host theorem

Compile `Submission/Bipartite.lean` to the local Lake library directory first.
This file imports neither `Spec` nor the previous auxiliary developments.
The concrete computations use kernel-checked `decide`.
-/

open SimpleGraph Erdos548.Bipartite
open scoped BigOperators

namespace Erdos548.BipartiteVerification

/-- The main interface needs only finite vertex types and returns an ordinary copy. -/
example {A V : Type*} [Finite A] [Finite V]
    (T : SimpleGraph A) (G : SimpleGraph V) (k : ℕ)
    (hcard : Nat.card A = k + 1) (hT : T.IsTree) (hB : G.IsBipartite)
    (hG : ((k : ℚ) - 1) / 2 * Nat.card V < (G.edgeSet.ncard : ℚ)) :
    Nonempty (T.Copy G) :=
  tree_isContained_of_bipartite_edge_threshold T G k hcard hT hB hG

/-- The greedy theorem really preserves the given classes on arbitrary finite types. -/
example {A V : Type*} [Finite A] [Finite V]
    (T : SimpleGraph A) (G : SimpleGraph V)
    (cT : T.Coloring Bool) (cG : G.Coloring Bool) (hT : T.IsTree)
    (hsurj : Function.Surjective cG)
    (hG : ∀ v, Nat.card {x : A // cT x ≠ cG v} ≤ (G.neighborSet v).ncard) :
    ∃ f : T.Copy G, ∀ x, cG (f x) = cT x :=
  exists_color_preserving_copy_of_neighborSet_ncard T G cT cG hT hsurj hG

/-- The weighted-core lemma is graph-independent and gives a nonempty induced core. -/
example {V : Type*} [Fintype V] (G : SimpleGraph V) (w : V → ℕ)
    (h : (∑ v, w v) < G.edgeSet.ncard) :
    ∃ s : Set V, s.Nonempty ∧ ∀ v : s, w v < ((G.induce s).neighborSet v).ncard :=
  exists_weighted_core G w h

/-- The strict `Fin n` interface requires no separate host-size assumption. -/
example (n k : ℕ) (G : SimpleGraph (Fin n)) (hB : G.IsBipartite)
    (hG : ((k : ℚ) - 1) / 2 * n < (G.edgeSet.ncard : ℚ))
    (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree) : T.IsContained G :=
  fin_tree_isContained_of_bipartite_edge_threshold n k G hB hG T hT

/-- The original specification's numerical hypotheses work for bipartite hosts. -/
example (n k : ℕ) (hn : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (hB : G.IsBipartite)
    (hG : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ))
    (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree) : T.IsContained G :=
  erdos_548_bipartite n k hn G hB hG T hT

/-- At `k = 0`, an edgeless singleton has positive excess because the coefficient
is `-1/2`, not a truncated natural subtraction. -/
example : (⊥ : SimpleGraph (Fin 1)).IsContained (⊥ : SimpleGraph (Fin 1)) := by
  have hT : (⊥ : SimpleGraph (Fin 1)).IsTree := IsTree.of_subsingleton
  exact fin_tree_isContained_of_bipartite_edge_threshold 1 0 _
    hT.isBipartite (by norm_num) _ hT

/-- No empty host satisfies the strict threshold, for any `k`. -/
example (k : ℕ) (G : SimpleGraph (Fin 0)) :
    ¬ (((k : ℚ) - 1) / 2 * Nat.card (Fin 0) < (G.edgeSet.ncard : ℚ)) := by
  intro h
  obtain ⟨v⟩ := nonempty_of_edge_threshold k G h
  exact Fin.elim0 v

/-- An empty host cannot contain the one-vertex tree. -/
example (T : SimpleGraph (Fin 1)) (G : SimpleGraph (Fin 0)) : ¬ T.IsContained G := by
  rintro ⟨f⟩
  exact Fin.elim0 (f 0)

private theorem two_vertex_edge_count : (completeGraph (Fin 2)).edgeSet.ncard = 1 := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  change (⊤ : SimpleGraph (Fin 2)).edgeFinset.card = 1
  rw [card_edgeFinset_top_eq_card_choose_two]
  decide

/-- The smallest nontrivial case: one edge suffices at `k = 1`. -/
example (T : SimpleGraph (Fin 2)) (hT : T.IsTree) :
    T.IsContained (completeGraph (Fin 2)) := by
  refine fin_tree_isContained_of_bipartite_edge_threshold 2 1 _
    ⟨(completeGraph (Fin 2)).selfColoring⟩ ?_ T hT
  rw [two_vertex_edge_count]
  norm_num

/-- Strictness matters: at `k = 2`, the one-edge graph is exactly at the
threshold and cannot contain any graph on three vertices. -/
example : (((2 : ℚ) - 1) / 2 * 2 = ((completeGraph (Fin 2)).edgeSet.ncard : ℚ)) ∧
    ∀ T : SimpleGraph (Fin 3), ¬ T.IsContained (completeGraph (Fin 2)) := by
  constructor
  · rw [two_vertex_edge_count]
    norm_num
  · intro T
    rintro ⟨f⟩
    have h := Fintype.card_le_of_injective f f.injective
    norm_num at h

private theorem k23_edge_count : (completeBipartiteGraph (Fin 2) (Fin 3)).edgeSet.ncard = 6 := by
  let G := completeBipartiteGraph (Fin 2) (Fin 3)
  letI : DecidableRel G.Adj := fun v w =>
    inferInstanceAs (Decidable (v.isLeft ∧ w.isRight ∨ v.isRight ∧ w.isLeft))
  have hd : (∑ v, G.degree v) = 12 := by decide
  have hs := G.sum_degrees_eq_twice_card_edges
  rw [hd] at hs
  rw [Set.ncard_eq_toFinset_card']
  change G.edgeFinset.card = 6
  omega

/-- A genuinely nonregular bipartite host: `K₂,₃` contains every four-vertex
tree, with arbitrary finite target labels. Its edge count is `6 > 5`. -/
example {A : Type*} [Finite A] (T : SimpleGraph A)
    (hcard : Nat.card A = 4) (hT : T.IsTree) :
    T.IsContained (completeBipartiteGraph (Fin 2) (Fin 3)) := by
  apply tree_isContained_of_bipartite_edge_threshold T _ 3 hcard hT
  · simpa using (CompleteBipartiteGraph.bicoloring (Fin 2) (Fin 3)).colorable
  · norm_num [k23_edge_count, Nat.card_eq_fintype_card]

#print axioms two_vertex_edge_count
#print axioms k23_edge_count
#print axioms tree_isContained_of_bipartite_edge_threshold
#print axioms exists_color_preserving_copy_of_neighborSet_ncard

end Erdos548.BipartiteVerification
