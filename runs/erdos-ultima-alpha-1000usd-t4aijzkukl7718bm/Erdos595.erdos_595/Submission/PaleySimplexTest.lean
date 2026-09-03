import Submission.VectorThree

/-!
An exact finite obstruction to a convex strengthening of triangle-hitting:
the K4-free Paley graph on 17 vertices has no unit-vector assignment for
which every triangle has sum of pairwise inner products at most -1.
This does not settle Erdős 595 or obstruct the weaker minimum-edge condition.
-/

open SimpleGraph Set
open scoped BigOperators

namespace Erdos595Paley

set_option maxRecDepth 10000
set_option maxHeartbeats 0

def adjacent (a b : Fin 17) : Prop :=
  (a.val + 17 - b.val) % 17 ∈ ([1, 2, 4, 8, 9, 13, 15, 16] : List ℕ)

instance : DecidableRel adjacent := fun _ _ => inferInstanceAs (Decidable (_ ∈ (_ : List ℕ)))

private theorem adj_symm : ∀ a b, adjacent a b → adjacent b a := by decide +kernel
private theorem adj_irrefl : ∀ a, ¬adjacent a a := by decide +kernel

def G : SimpleGraph (Fin 17) where
  Adj := adjacent
  symm := fun a b h => adj_symm a b h
  loopless := adj_irrefl

private def vertices : List (Fin 17) := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16]

private theorem vertices_mem : ∀ a : Fin 17, a ∈ vertices := by decide +kernel


private def vertexColor : Fin 17 → Fin 3 :=
  ![0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 2, 1, 2, 2]

private theorem vertexColor_check : vertices.all (fun a => vertices.all (fun b =>
    vertices.all (fun c => decide (adjacent a b → adjacent a c → adjacent b c →
      ¬(vertexColor a = vertexColor b ∧ vertexColor a = vertexColor c))))) = true := by
  decide +kernel

private theorem vertexColor_valid (a b c : Fin 17)
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    ¬(vertexColor a = vertexColor b ∧ vertexColor a = vertexColor c) := by
  have ha := List.all_eq_true.mp vertexColor_check a (vertices_mem a)
  have hb := List.all_eq_true.mp ha b (vertices_mem b)
  exact (of_decide_eq_true (List.all_eq_true.mp hb c (vertices_mem c))) hab hac hbc

noncomputable def simplex : Fin 3 → EuclideanSpace ℝ (Fin 4) :=
  ![WithLp.toLp 2 ![1/2, 1/2, 1/2, 1/2],
    WithLp.toLp 2 ![-1/2, -1/2, 1/2, -1/2],
    WithLp.toLp 2 ![0, 0, -1, 0]]

private theorem simplex_inner (i j : Fin 3) :
    inner ℝ (simplex i) (simplex j) = if i = j then 1 else -(1 / 2 : ℝ) := by
  fin_cases i <;> fin_cases j <;>
    rw [PiLp.inner_apply] <;>
    norm_num [simplex, Fin.sum_univ_succ]

/-- The weaker, nonconvex triangle-hitting condition does hold on this graph,
even at the -1/2 threshold. Thus the convex obstruction cannot be substituted
for an obstruction to the actual sufficient condition. -/
theorem exists_triangle_hit : ∃ v : Fin 17 → EuclideanSpace ℝ (Fin 4),
    (∀ a, inner ℝ (v a) (v a) = 1) ∧
    (∀ a b c, G.Adj a b → G.Adj a c → G.Adj b c →
      inner ℝ (v a) (v b) ≤ -(1 / 2 : ℝ) ∨
      inner ℝ (v a) (v c) ≤ -(1 / 2 : ℝ) ∨
      inner ℝ (v b) (v c) ≤ -(1 / 2 : ℝ)) := by
  refine ⟨fun a => simplex (vertexColor a), ?_, ?_⟩
  · intro a
    rw [simplex_inner, if_pos rfl]
  · intro a b c hab hac hbc
    have hc := vertexColor_valid a b c hab hac hbc
    by_cases he : vertexColor a = vertexColor b
    · have hn : vertexColor a ≠ vertexColor c := fun h => hc ⟨he, h⟩
      exact Or.inr (Or.inl (by rw [simplex_inner, if_neg hn]))
    · exact Or.inl (by rw [simplex_inner, if_neg he])

theorem G_three_cover : ∃ H : Option Bool → SimpleGraph (Fin 17),
    (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i := by
  obtain ⟨v, hv, ht⟩ := exists_triangle_hit
  exact Erdos595VectorThree.three_cover_of_triangle_hit_neg_half G v hv ht

#print axioms exists_triangle_hit
#print axioms G_three_cover

end Erdos595Paley
