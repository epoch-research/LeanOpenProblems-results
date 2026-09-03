import Submission.PaleyData
open SimpleGraph Set
open scoped BigOperators
namespace Erdos595Paley
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option profiler true
private theorem triangle_sum (f : Fin 17 → Fin 17 → ℝ) :
    (∑ t : Fin 68, (f (triangles t).1 (triangles t).2.1 +
      f (triangles t).1 (triangles t).2.2 + f (triangles t).2.1 (triangles t).2.2)) =
      3 * ∑ e : Fin 68, f (edges e).1 (edges e).2 := by
  simp only [Fin.sum_univ_succ, triangles, edges, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero]
  ring!

#check triangle_sum

private theorem scalar_energy (f : Fin 17 → Fin 17 → ℝ) :
    (∑ i : Fin 17, ∑ j : Fin 17, (C i j : ℝ) * f (min i j) (max i j)) =
      3757 * (∑ i : Fin 17, f i i) + 2890 * ∑ e : Fin 68, f (edges e).1 (edges e).2 := by
  simp only [Fin.sum_univ_succ, edges, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero]
  simp only [C, adjacent, min_def, max_def, Fin.ext_iff, Fin.le_def]
  norm_num
  ring!

#check scalar_energy

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

#print axioms G_cliqueFree
#print axioms no_convex_triangle_assignment

end Inner
end Erdos595Paley
