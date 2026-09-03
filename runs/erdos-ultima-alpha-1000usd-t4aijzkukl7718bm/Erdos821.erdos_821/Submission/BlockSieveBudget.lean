import Submission.BlockCompositeGain

/-!
# Telescoping bounds for the blockwise sieve coefficient

These inequalities concern the sufficient method budget, not upper bounds
on the actual totient multiplicity function.
-/
open Nat Finset Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

lemma blockMainLimit_eq_reciprocal_sum (t b h : ℕ) :
    blockMainLimit t b h = (8192/675 : ℝ)*(t : ℝ)*
      ∑ j ∈ range h, 1/((b : ℝ)+j-1)^2 := by
  unfold blockMainLimit
  rw [← sum_range_reflect (fun j => independentMainLimit t (blockCutoff b h j) 1) h,
    mul_sum]
  apply sum_congr rfl
  intro j hj
  have hc : blockCutoff b h (h-1-j)=b+j := by
    have hj' := mem_range.mp hj
    dsimp [blockCutoff]
    omega
  rw [hc]
  simp only [independentMainLimit,Nat.cast_add,Nat.cast_one,mul_one]
  ring

lemma reciprocal_sq_le_adjacent_diff (x : ℝ) (hx : 1<x) :
    1/x^2 ≤ 1/(x-1)-1/x := by
  have hx0 : 0<x := by linarith
  have hxm : 0<x-1 := by linarith
  calc
    _ ≤ 1/((x-1)*x) := one_div_le_one_div_of_le (mul_pos hxm hx0) (by nlinarith)
    _ = _ := by field_simp; ring

lemma adjacent_diff_le_reciprocal_sq (x : ℝ) (hx : 0<x) :
    1/x-1/(x+1) ≤ 1/x^2 := by
  have hxp : 0<x+1 := by linarith
  calc
    _ = 1/(x*(x+1)) := by field_simp; ring
    _ ≤ _ := one_div_le_one_div_of_le (sq_pos_of_pos hx) (by nlinarith)

lemma blockMainLimit_le_telescoped (t b h : ℕ) (hb : 3 ≤ b) :
    blockMainLimit t b h ≤
      (8192/675 : ℝ)*(t : ℝ)*h/(((b : ℝ)-2)*((b : ℝ)+h-2)) := by
  have hbR : (3 : ℝ) ≤ b := by exact_mod_cast hb
  have hsum : (∑ j ∈ range h, 1/((b : ℝ)+j-1)^2) ≤
      1/((b : ℝ)-2)-1/((b : ℝ)+h-2) := by
    have hs := sum_le_sum (s := range h) (fun j _ =>
      reciprocal_sq_le_adjacent_diff ((b : ℝ)+j-1) (by
        have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        linarith))
    have he : (∑ j ∈ range h,
        (1/((b : ℝ)+j-1-1)-1/((b : ℝ)+j-1))) =
        1/((b : ℝ)-2)-1/((b : ℝ)+h-2) := by
      convert sum_range_sub' (fun j : ℕ => 1/((b : ℝ)+j-2)) h using 1
      · apply sum_congr rfl
        intro j hj
        push_cast
        congr 1 <;> congr 1 <;> ring
      · simp
    exact he ▸ hs
  rw [blockMainLimit_eq_reciprocal_sum]
  apply (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ (8192/675 : ℝ)*(t : ℝ))).trans_eq
  have hb0 : (0 : ℝ)<(b : ℝ)-2 := by linarith
  have hbh0 : (0 : ℝ)<(b : ℝ)+h-2 := by linarith [Nat.cast_nonneg (α := ℝ) h]
  field_simp
  ring

lemma telescoped_le_blockMainLimit (t b h : ℕ) (hb : 2 ≤ b) :
    (8192/675 : ℝ)*(t : ℝ)*h/(((b : ℝ)-1)*((b : ℝ)+h-1)) ≤
      blockMainLimit t b h := by
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hsum : 1/((b : ℝ)-1)-1/((b : ℝ)+h-1) ≤
      ∑ j ∈ range h, 1/((b : ℝ)+j-1)^2 := by
    have hs := sum_le_sum (s := range h) (fun j _ =>
      adjacent_diff_le_reciprocal_sq ((b : ℝ)+j-1) (by
        have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        linarith))
    have he : (∑ j ∈ range h,
        (1/((b : ℝ)+j-1)-1/((b : ℝ)+j-1+1))) =
        1/((b : ℝ)-1)-1/((b : ℝ)+h-1) := by
      convert sum_range_sub' (fun j : ℕ => 1/((b : ℝ)+j-1)) h using 1
      · apply sum_congr rfl
        intro j hj
        push_cast
        congr 1
        congr 1
        ring
      · simp
    exact he ▸ hs
  rw [blockMainLimit_eq_reciprocal_sum]
  apply le_trans _ (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ (8192/675 : ℝ)*(t : ℝ)))
  apply le_of_eq
  have hb0 : (0 : ℝ)<(b : ℝ)-1 := by linarith
  have hbh0 : (0 : ℝ)<(b : ℝ)+h-1 := by linarith [Nat.cast_nonneg (α := ℝ) h]
  field_simp
  ring

end Erdos821
