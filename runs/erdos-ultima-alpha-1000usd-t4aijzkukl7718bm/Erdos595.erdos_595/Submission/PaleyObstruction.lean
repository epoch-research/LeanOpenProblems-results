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
set_option maxHeartbeats 2000000
set_option autoImplicit false

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

private theorem no_four_check : vertices.all (fun a => vertices.all (fun b =>
    vertices.all (fun c => vertices.all (fun d => decide
      (¬(adjacent a b ∧ adjacent a c ∧ adjacent a d ∧
        adjacent b c ∧ adjacent b d ∧ adjacent c d)))))) = true := by decide +kernel

private theorem no_four : ∀ a b c d : Fin 17,
    ¬(adjacent a b ∧ adjacent a c ∧ adjacent a d ∧
      adjacent b c ∧ adjacent b d ∧ adjacent c d) := by
  intro a b c d
  have ha := List.all_eq_true.mp no_four_check a (vertices_mem a)
  have hb := List.all_eq_true.mp ha b (vertices_mem b)
  have hc := List.all_eq_true.mp hb c (vertices_mem c)
  exact of_decide_eq_true (List.all_eq_true.mp hc d (vertices_mem d))


theorem G_cliqueFree : G.CliqueFree 4 := by
  classical
  by_contra h
  let f := SimpleGraph.topEmbeddingOfNotCliqueFree h
  apply no_four (f 0) (f 1) (f 2) (f 3)
  exact ⟨f.map_rel_iff.mpr (by decide), f.map_rel_iff.mpr (by decide),
    f.map_rel_iff.mpr (by decide), f.map_rel_iff.mpr (by decide),
    f.map_rel_iff.mpr (by decide), f.map_rel_iff.mpr (by decide)⟩

def edges : Fin 68 → Fin 17 × Fin 17 :=
  ![(0, 1),
    (0, 2),
    (0, 4),
    (0, 8),
    (0, 9),
    (0, 13),
    (0, 15),
    (0, 16),
    (1, 2),
    (1, 3),
    (1, 5),
    (1, 9),
    (1, 10),
    (1, 14),
    (1, 16),
    (2, 3),
    (2, 4),
    (2, 6),
    (2, 10),
    (2, 11),
    (2, 15),
    (3, 4),
    (3, 5),
    (3, 7),
    (3, 11),
    (3, 12),
    (3, 16),
    (4, 5),
    (4, 6),
    (4, 8),
    (4, 12),
    (4, 13),
    (5, 6),
    (5, 7),
    (5, 9),
    (5, 13),
    (5, 14),
    (6, 7),
    (6, 8),
    (6, 10),
    (6, 14),
    (6, 15),
    (7, 8),
    (7, 9),
    (7, 11),
    (7, 15),
    (7, 16),
    (8, 9),
    (8, 10),
    (8, 12),
    (8, 16),
    (9, 10),
    (9, 11),
    (9, 13),
    (10, 11),
    (10, 12),
    (10, 14),
    (11, 12),
    (11, 13),
    (11, 15),
    (12, 13),
    (12, 14),
    (12, 16),
    (13, 14),
    (13, 15),
    (14, 15),
    (14, 16),
    (15, 16)]

def triangles : Fin 68 → Fin 17 × Fin 17 × Fin 17 :=
  ![(0, 1, 2),
    (0, 1, 9),
    (0, 1, 16),
    (0, 2, 4),
    (0, 2, 15),
    (0, 4, 8),
    (0, 4, 13),
    (0, 8, 9),
    (0, 8, 16),
    (0, 9, 13),
    (0, 13, 15),
    (0, 15, 16),
    (1, 2, 3),
    (1, 2, 10),
    (1, 3, 5),
    (1, 3, 16),
    (1, 5, 9),
    (1, 5, 14),
    (1, 9, 10),
    (1, 10, 14),
    (1, 14, 16),
    (2, 3, 4),
    (2, 3, 11),
    (2, 4, 6),
    (2, 6, 10),
    (2, 6, 15),
    (2, 10, 11),
    (2, 11, 15),
    (3, 4, 5),
    (3, 4, 12),
    (3, 5, 7),
    (3, 7, 11),
    (3, 7, 16),
    (3, 11, 12),
    (3, 12, 16),
    (4, 5, 6),
    (4, 5, 13),
    (4, 6, 8),
    (4, 8, 12),
    (4, 12, 13),
    (5, 6, 7),
    (5, 6, 14),
    (5, 7, 9),
    (5, 9, 13),
    (5, 13, 14),
    (6, 7, 8),
    (6, 7, 15),
    (6, 8, 10),
    (6, 10, 14),
    (6, 14, 15),
    (7, 8, 9),
    (7, 8, 16),
    (7, 9, 11),
    (7, 11, 15),
    (7, 15, 16),
    (8, 9, 10),
    (8, 10, 12),
    (8, 12, 16),
    (9, 10, 11),
    (9, 11, 13),
    (10, 11, 12),
    (10, 12, 14),
    (11, 12, 13),
    (11, 13, 15),
    (12, 13, 14),
    (12, 14, 16),
    (13, 14, 15),
    (14, 15, 16)]

private theorem triangles_valid : ∀ t : Fin 68,
    adjacent (triangles t).1 (triangles t).2.1 ∧
    adjacent (triangles t).1 (triangles t).2.2 ∧
    adjacent (triangles t).2.1 (triangles t).2.2 := by decide +kernel

def S (i j : Fin 17) : ℤ := if i = j then 40 else if adjacent i j then 6 else -11

def C (i j : Fin 17) : ℤ := if i = j then 3757 else if adjacent i j then 1445 else 0

/-- An exact integer Gram certificate. It is (17 A + 51 I - 11 J)^2
plus 901 J, equal to 3757 I + 1445 A. -/
private theorem certificate_check : vertices.all (fun i => vertices.all (fun j =>
    decide ((∑ k : Fin 17, S k i * S k j) + 901 = C i j))) = true := by decide +kernel

private theorem certificate : ∀ i j : Fin 17,
    (∑ k : Fin 17, S k i * S k j) + 901 = C i j := by
  intro i j
  have hi := List.all_eq_true.mp certificate_check i (vertices_mem i)
  exact of_decide_eq_true (List.all_eq_true.mp hi j (vertices_mem j))


private theorem triangle_sum (f : Fin 17 → Fin 17 → ℝ) :
    (∑ t : Fin 68, (f (triangles t).1 (triangles t).2.1 +
      f (triangles t).1 (triangles t).2.2 + f (triangles t).2.1 (triangles t).2.2)) =
      3 * ∑ e : Fin 68, f (edges e).1 (edges e).2 := by
  simp only [Fin.sum_univ_succ, triangles, edges, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero]
  ring!


private theorem scalar_energy (f : Fin 17 → Fin 17 → ℝ) :
    (∑ i : Fin 17, ∑ j : Fin 17, (C i j : ℝ) * f (min i j) (max i j)) =
      3757 * (∑ i : Fin 17, f i i) + 2890 * ∑ e : Fin 68, f (edges e).1 (edges e).2 := by
  simp only [Fin.sum_univ_succ, edges, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero]
  simp only [C, adjacent, min_def, max_def, Fin.ext_iff, Fin.le_def]
  norm_num
  ring!


section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem inner_nonneg (x : E) : 0 ≤ inner ℝ x x := by
  simpa only [RCLike.re_to_real] using (inner_self_nonneg (𝕜 := ℝ) (x := x))

private theorem square_sum (v : Fin 17 → E) (M : Fin 17 → Fin 17 → ℝ) :
    (∑ k : Fin 17, inner ℝ (∑ i : Fin 17, M k i • v i) (∑ i : Fin 17, M k i • v i)) =
    ∑ i : Fin 17, ∑ j : Fin 17, (∑ k : Fin 17, M k i * M k j) * inner ℝ (v i) (v j) := by
  calc
    _ = ∑ k : Fin 17, ∑ i : Fin 17, ∑ j : Fin 17,
        (M k i * M k j) * inner ℝ (v i) (v j) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [sum_inner]
      simp only [inner_sum, real_inner_smul_left, real_inner_smul_right, mul_assoc, mul_left_comm]
    _ = ∑ i : Fin 17, ∑ j : Fin 17, ∑ k : Fin 17,
        (M k i * M k j) * inner ℝ (v i) (v j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by simp_rw [Finset.sum_mul]

private theorem energy_nonneg (v : Fin 17 → E) :
    0 ≤ ∑ i : Fin 17, ∑ j : Fin 17, (C i j : ℝ) * inner ℝ (v i) (v j) := by
  let M : Fin 17 → Fin 17 → ℝ := fun i j => (S i j : ℝ)
  have hc : ∀ i j, (∑ k : Fin 17, M k i * M k j) + 901 = (C i j : ℝ) := by
    intro i j
    dsimp only [M]
    exact_mod_cast certificate i j
  have h₁ : 0 ≤ ∑ k : Fin 17,
      inner ℝ (∑ i : Fin 17, M k i • v i) (∑ i : Fin 17, M k i • v i) :=
    Finset.sum_nonneg (fun _ _ => inner_nonneg _)
  have h₂ := mul_nonneg (show (0 : ℝ) ≤ 901 by norm_num) (inner_nonneg (∑ i, v i))
  have he : (∑ k : Fin 17, inner ℝ (∑ i : Fin 17, M k i • v i)
      (∑ i : Fin 17, M k i • v i)) + 901 * inner ℝ (∑ i, v i) (∑ i, v i) =
      ∑ i : Fin 17, ∑ j : Fin 17, (C i j : ℝ) * inner ℝ (v i) (v j) := by
    have hsum : inner ℝ (∑ i, v i) (∑ i, v i) =
        ∑ i : Fin 17, ∑ j : Fin 17, inner ℝ (v i) (v j) := by
      rw [sum_inner]
      simp only [inner_sum]
    rw [square_sum, hsum]
    simp only [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← add_mul, hc]
  rw [← he]
  exact add_nonneg h₁ h₂

/-- The convex requirement that every triangle's three pairwise inner
products sum to at most -1 fails even on this finite K4-free graph. -/
theorem no_convex_triangle_assignment :
    ¬∃ v : Fin 17 → E, (∀ i, inner ℝ (v i) (v i) = 1) ∧
      (∀ a b c, G.Adj a b → G.Adj a c → G.Adj b c →
        inner ℝ (v a) (v b) + inner ℝ (v a) (v c) + inner ℝ (v b) (v c) ≤ -1) := by
  rintro ⟨v, hunit, ht⟩
  have hs : (∑ t : Fin 68, (inner ℝ (v (triangles t).1) (v (triangles t).2.1) +
      inner ℝ (v (triangles t).1) (v (triangles t).2.2) +
      inner ℝ (v (triangles t).2.1) (v (triangles t).2.2))) ≤ -68 := by
    calc
      _ ≤ ∑ _ : Fin 68, (-1 : ℝ) := Finset.sum_le_sum fun t _ =>
        ht _ _ _ (triangles_valid t).1 (triangles_valid t).2.1 (triangles_valid t).2.2
      _ = -68 := by norm_num
  rw [triangle_sum (fun i j => inner ℝ (v i) (v j))] at hs
  have he := energy_nonneg v
  have hsym : ∀ i j, inner ℝ (v i) (v j) = inner ℝ (v (min i j)) (v (max i j)) := by
    intro i j
    rcases le_total i j with hij | hji
    · rw [min_eq_left hij, max_eq_right hij]
    · rw [min_eq_right hji, max_eq_left hji, real_inner_comm]
  have heq : (∑ i : Fin 17, ∑ j : Fin 17, (C i j : ℝ) * inner ℝ (v i) (v j)) =
      ∑ i : Fin 17, ∑ j : Fin 17, (C i j : ℝ) *
        inner ℝ (v (min i j)) (v (max i j)) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym i j]
  rw [heq, scalar_energy (fun i j => inner ℝ (v i) (v j))] at he
  simp only [hunit, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at he
  norm_num at he
  linarith only [he, hs]

/-- In particular, making every edge at most -1/3 is already impossible on
this finite K4-free graph. This does not exclude the minimum-edge condition. -/
theorem no_unit_all_edges_le_neg_third :
    ¬∃ v : Fin 17 → E, (∀ i, inner ℝ (v i) (v i) = 1) ∧
      (∀ a b, G.Adj a b → inner ℝ (v a) (v b) ≤ -(1 / 3 : ℝ)) := by
  rintro ⟨v, hunit, hv⟩
  apply no_convex_triangle_assignment (E := E)
  refine ⟨v, hunit, ?_⟩
  intro a b c hab hac hbc
  have h₁ := hv a b hab
  have h₂ := hv a c hac
  have h₃ := hv b c hbc
  linarith

#print axioms no_unit_all_edges_le_neg_third
#print axioms G_cliqueFree
#print axioms no_convex_triangle_assignment

end Inner

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
