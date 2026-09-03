import Submission.SupportLowerLaw

/-! Exact finite geometric moment bounds for the two-variable support law.
These estimates are auxiliary to a prefix certificate, not a settlement. -/
namespace Erdos7SupportMomentBounds
open scoped BigOperators
open Erdos7SupportCompression Erdos7SupportPolynomialTail Erdos7SupportTailIteration
open Erdos7CompressionSieve
set_option autoImplicit false
set_option maxHeartbeats 3000000

lemma increment_mean_geometric (p E : ℕ) (hp : 1 < p) (c : ℚ) (hc : 0 ≤ c) :
    op E (powerTail p c E) (fun a => (a:ℚ)) ≤ c/((p:ℚ)-1) := by
  have hpQ : (1:ℚ) < p := by exact_mod_cast hp
  have hp0 : (0:ℚ) < p := by linarith
  have hr : (p:ℚ)⁻¹ < 1 := (inv_lt_one₀ hp0).mpr hpQ
  have hg := geom_sum_mul_neg (p:ℚ)⁻¹ E
  have hs : (∑ a ∈ Finset.range E,((p:ℚ)⁻¹)^a) ≤ 1/(1-(p:ℚ)⁻¹) := by
    apply (le_div_iff₀ (by linarith : 0 < 1-(p:ℚ)⁻¹)).mpr
    nlinarith [pow_nonneg (show 0 ≤ (p:ℚ)⁻¹ by positivity) E]
  have he : op E (powerTail p c E) (fun a => (a:ℚ)) =
      c*(p:ℚ)⁻¹*(∑ a ∈ Finset.range E,((p:ℚ)⁻¹)^a) := by
    rw [op_eq_increments E _ (powerTail_terminal p c E)]
    norm_num only [Nat.cast_zero,zero_add]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [powerTail,if_pos (Finset.mem_range.mp ha),pow_succ]
    push_cast
    ring
  rw [he]
  apply (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ c*(p:ℚ)⁻¹)).trans_eq
  field_simp
  <;> ring

def squareTail (r : ℚ) (E : ℕ) : ℚ :=
  r^E*((2*(E:ℚ)+1)/(1-r)+2*r/(1-r)^2)

lemma squareTail_step (r : ℚ) (hr : r < 1) (E : ℕ) :
    squareTail r E=(2*(E:ℚ)+1)*r^E+squareTail r (E+1) := by
  have hn : 1-r≠0 := by linarith
  unfold squareTail
  push_cast
  rw [pow_succ]
  field_simp
  <;> ring

lemma squareTail_sum (r : ℚ) (hr : r < 1) (E : ℕ) :
    (∑ a ∈ Finset.range E,(2*(a:ℚ)+1)*r^a)+squareTail r E=squareTail r 0 := by
  induction E with
  | zero => simp
  | succ E ih =>
    rw [Finset.sum_range_succ]
    have h := squareTail_step r hr E
    linarith

lemma increment_square_geometric (p E : ℕ) (hp : 1 < p) (c : ℚ) (hc : 0 ≤ c) :
    op E (powerTail p c E) (fun a => (a:ℚ)^2) ≤ c*((p:ℚ)+1)/(p-1)^2 := by
  have hpQ : (1:ℚ) < p := by exact_mod_cast hp
  have hp0 : (0:ℚ) < p := by linarith
  have hr : (p:ℚ)⁻¹ < 1 := (inv_lt_one₀ hp0).mpr hpQ
  have ht := squareTail_sum (p:ℚ)⁻¹ hr E
  have hn : 0 ≤ squareTail (p:ℚ)⁻¹ E := by
    unfold squareTail
    have : 0 ≤ 1-(p:ℚ)⁻¹ := by linarith
    positivity
  have hs : (∑ a ∈ Finset.range E,(2*(a:ℚ)+1)*((p:ℚ)⁻¹)^a) ≤
      squareTail (p:ℚ)⁻¹ 0 := by linarith
  have he : op E (powerTail p c E) (fun a => (a:ℚ)^2) =
      c*(p:ℚ)⁻¹*(∑ a ∈ Finset.range E,(2*(a:ℚ)+1)*((p:ℚ)⁻¹)^a) := by
    rw [op_eq_increments E _ (powerTail_terminal p c E)]
    norm_num only [Nat.cast_zero,zero_pow (by omega : 2≠0),zero_add]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [powerTail,if_pos (Finset.mem_range.mp ha),pow_succ]
    push_cast
    ring
  rw [he]
  apply (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ c*(p:ℚ)⁻¹)).trans_eq
  unfold squareTail
  norm_num only [Nat.cast_zero,pow_zero,mul_zero,add_zero,zero_add,one_mul]
  field_simp
  <;> ring

lemma cubic_polynomial_op (p E : ℕ) (hp : 1 < p) (c : ℚ) (hc : 0 ≤ c)
    (b₀ b₁ b₂ b₃ : ℚ) (h₁ : 0 ≤ b₁) (h₂ : 0 ≤ b₂) (h₃ : 0 ≤ b₃) :
    op E (powerTail p c E) (fun a => b₀+b₁*(a:ℚ)+b₂*(a:ℚ)^2+b₃*(a:ℚ)^3) ≤
      b₀+b₁*(c/((p:ℚ)-1))+b₂*(c*((p:ℚ)+1)/(p-1)^2)+b₃*(c*((p:ℚ)^2+4*p+1)/(p-1)^3) := by
  rw [op_add,op_add,op_add,op_const E _ (powerTail_terminal p c E),op_mul,op_mul,op_mul]
  exact add_le_add (add_le_add (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (increment_mean_geometric p E hp c hc) h₁))
      (mul_le_mul_of_nonneg_left (increment_square_geometric p E hp c hc) h₂))
        (mul_le_mul_of_nonneg_left (increment_cube_geometric p E hp c hc) h₃)

#print axioms cubic_polynomial_op
end Erdos7SupportMomentBounds
