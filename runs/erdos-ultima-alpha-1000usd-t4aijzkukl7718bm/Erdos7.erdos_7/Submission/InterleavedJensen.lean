import Submission.InterleavedGeometricCompression

/-! Finite equal-weight Jensen splitting for the terminal/stem comparison.
The slices remain individually indexed; this does not identify separate
future families from different budget summands. -/
namespace Erdos7InterleavedJensen
open scoped BigOperators
open Erdos7InterleavedGeometricCompression
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem equal_weight_split (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ)
    (A : ℝ) (X : ℕ → ℝ) (n : ℕ) (hn : 0 < n) :
    φ (A+∑ j ∈ Finset.range n, X j) ≤
      (∑ j ∈ Finset.range n, φ (A+(n : ℝ)*X j))/(n : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hm : (∑ j ∈ Finset.range n, (1/(n : ℝ))) = 1 := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have hh := hφ.map_sum_le (t := Finset.range n) (w := fun _ => 1/(n : ℝ))
    (p := fun j => A+(n : ℝ)*X j)
    (fun _ _ => by positivity) hm (fun _ _ => Set.mem_univ _)
  have he : (∑ j ∈ Finset.range n, (1/(n : ℝ)) • (A+(n : ℝ)*X j)) =
      A+∑ j ∈ Finset.range n, X j := by
    simp only [smul_eq_mul, mul_add]
    rw [Finset.sum_add_distrib]
    have hj (j : ℕ) : 1/(n : ℝ)*((n : ℝ)*X j) = X j := by field_simp
    simp only [hj, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  rw [he] at hh
  simpa only [smul_eq_mul, one_div_mul_eq_div, ← Finset.sum_div] using hh

/-- At a terminal stage there are `n` full earlier slices and one terminal
slice. The new terminal count is not confused with its accompanying stem. -/
theorem partial_split (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ)
    (A : ℝ) (B : ℕ → ℝ) (T : ℝ) (n : ℕ) :
    φ (A+(∑ j ∈ Finset.range n, B j)+T) ≤
      ((∑ j ∈ Finset.range n, φ (A+((n : ℝ)+1)*B j))+
        φ (A+((n : ℝ)+1)*T))/((n : ℝ)+1) := by
  let X (j : ℕ) := if j=n then T else B j
  have hh := equal_weight_split φ hφ A X (n+1) (by omega)
  have he : (∑ j ∈ Finset.range (n+1), X j) = (∑ j ∈ Finset.range n, B j)+T := by
    rw [Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      simp [X, Nat.ne_of_lt (Finset.mem_range.mp hj)]
    · simp [X]
  rw [he] at hh
  have he' : (∑ j ∈ Finset.range (n+1), φ (A+((n+1 : ℕ) : ℝ)*X j)) =
      (∑ j ∈ Finset.range n, φ (A+((n : ℝ)+1)*B j))+
        φ (A+((n : ℝ)+1)*T) := by
    rw [Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      simp [X, Nat.ne_of_lt (Finset.mem_range.mp hj)]
    · simp [X]
  rw [he'] at hh
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hh

/-- A positive finite bound after Jensen splitting, including the final
reserve. Subsequent reindexing can retain each `(T j,S j)` as one action. -/
theorem split_geometric_comparison (φ : ℝ → ℝ)
    (hφ : ConvexOn ℝ Set.univ φ) (A p : ℝ) (hp : 2 ≤ p)
    (T S : ℕ → ℝ) (R : ℕ) (hR : 0 < R) :
    (φ A/p+∑ a ∈ Finset.range R,
        ((p-2)/p^(a+1)*φ (A+cumulative T S a+T a)+
         1/p^(a+2)*φ (A+cumulative T S (a+1)))+
      (p-1)/p^(R+1)*φ (A+cumulative T S R)) ≤
    φ A/p+∑ a ∈ Finset.range R,
      ((p-2)/p^(a+1)*
        (((∑ j ∈ Finset.range a, φ (A+((a : ℝ)+1)*(T j+S j)))+
          φ (A+((a : ℝ)+1)*T a))/((a : ℝ)+1))+
       1/p^(a+2)*
        ((∑ j ∈ Finset.range (a+1), φ (A+((a : ℝ)+1)*(T j+S j)))/((a : ℝ)+1)))+
      (p-1)/p^(R+1)*
        ((∑ j ∈ Finset.range R, φ (A+(R : ℝ)*(T j+S j)))/(R : ℝ)) := by
  have hp0 : 0 < p := by linarith
  apply add_le_add
  · apply add_le_add (le_refl _)
    apply Finset.sum_le_sum
    intro a ha
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left
      · exact partial_split φ hφ A (fun j => T j+S j) (T a) a
      · exact div_nonneg (by linarith) (le_of_lt (pow_pos hp0 _))
    · apply mul_le_mul_of_nonneg_left
      · simpa only [Nat.cast_add, Nat.cast_one] using
          equal_weight_split φ hφ A (fun j => T j+S j) (a+1) (by omega)
      · positivity
  · apply mul_le_mul_of_nonneg_left
    · exact equal_weight_split φ hφ A (fun j => T j+S j) R hR
    · exact div_nonneg (by linarith) (le_of_lt (pow_pos hp0 _))

#print axioms equal_weight_split
#print axioms partial_split
#print axioms split_geometric_comparison
end Erdos7InterleavedJensen
