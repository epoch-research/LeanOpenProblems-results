import Submission.TailPowerExpansion

/-!
A columnwise residue family, not a proof of Erdős 68.
The target of the integer forms varies with the column index.
-/
namespace FallingResidueForms
open Erdos68Development TailPowerExpansion

noncomputable def remainder (r k : ℕ) : ℝ :=
  powerTerm r k - 2 * (2 : ℝ) ^ (r+1) * powerTerm r (k+1) +
    (6 : ℝ) ^ (r+1) * powerTerm r (k+2)

lemma convex_power_strict (a b c : ℝ) (ha : c ≤ a)
    (hc : 0 ≤ c) (hb : 0 < b) (hgap : 2*b < a+c) (r : ℕ) :
    0 < a^(r+1) - 2*b^(r+1) + c^(r+1) := by
  have ha0 : 0 ≤ a := hc.trans ha
  have hgap' : b-c ≤ a-b := by linarith
  have hab : 0 ≤ a-b := by linarith
  induction r with
  | zero => simpa using (show 0 < a-2*b+c by linarith)
  | succ r ih =>
    have hp : c^(r+1) ≤ a^(r+1) := pow_le_pow_left₀ hc ha _
    have hm : (b-c)*c^(r+1) ≤ (a-b)*a^(r+1) :=
      mul_le_mul hgap' hp (by positivity) hab
    have ht := mul_pos hb ih
    simp only [pow_succ] at *
    nlinarith

lemma numerator_pos (r k : ℕ) :
    0 < (((k+4 : ℝ)*(k+3))^(r+1) -
      2*(2*(k+4 : ℝ))^(r+1) + (6 : ℝ)^(r+1)) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  apply convex_power_strict <;> nlinarith

lemma remainder_eq (r k : ℕ) :
    remainder r k =
      (((k+4 : ℝ)*(k+3))^(r+1) -
        2*(2*(k+4 : ℝ))^(r+1) + (6 : ℝ)^(r+1)) /
      ((k+4).factorial : ℝ)^(r+1) := by
  have hf : ((k+2).factorial : ℝ) ≠ 0 := by positivity
  have hk3 : (k+3 : ℝ) ≠ 0 := by positivity
  have hk4 : (k+4 : ℝ) ≠ 0 := by positivity
  have h3 : ((k+3).factorial : ℝ) = (k+3 : ℝ)*((k+2).factorial : ℝ) := by
    rw [show k+3 = (k+2)+1 by omega, Nat.factorial_succ]
    push_cast; ring_nf
  have h4 : ((k+4).factorial : ℝ) =
      (k+4 : ℝ)*(k+3)*((k+2).factorial : ℝ) := by
    rw [show k+4 = (k+3)+1 by omega, Nat.factorial_succ]
    push_cast
    rw [h3]
    ring_nf
  simp only [remainder, powerTerm, show k+1+2=k+3 by omega,
    show k+2+2=k+4 by omega, h3, h4, mul_pow]
  field_simp

lemma remainder_pos (r k : ℕ) : 0 < remainder r k := by
  rw [remainder_eq]
  exact div_pos (numerator_pos r k) (by positivity)

lemma summable_remainder (r : ℕ) : Summable (remainder r) := by
  have h1 := (summable_nat_add_iff 1).mpr (summable_powerTerm r)
  have h2 := (summable_nat_add_iff 2).mpr (summable_powerTerm r)
  exact ((summable_powerTerm r).sub (h1.mul_left (2*2^(r+1)))).add
    (h2.mul_left (6^(r+1)))

noncomputable def leading (r : ℕ) : ℤ := 6^(r+1) - 2*2^(r+1) + 1
noncomputable def boundary (r : ℕ) : ℤ := 3^(r+1) - 1

lemma remainder_sum (r : ℕ) :
    (∑' k : ℕ, remainder r k) =
      (leading r : ℝ)*(∑' k : ℕ, powerTerm r k) - (boundary r : ℝ) := by
  have h1 := (summable_nat_add_iff 1).mpr (summable_powerTerm r)
  have h2 := (summable_nat_add_iff 2).mpr (summable_powerTerm r)
  have ht1 := (summable_powerTerm r).sum_add_tsum_nat_add 1
  have ht2 := (summable_powerTerm r).sum_add_tsum_nat_add 2
  have ht0 : powerTerm r 0 = 1/(2:ℝ)^(r+1) := by norm_num [powerTerm]
  have htone : powerTerm r 1 = 1/(6:ℝ)^(r+1) := by norm_num [powerTerm]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, ht0, htone] at ht1 ht2
  have he1 : (∑' k : ℕ, powerTerm r (k+1)) =
      (∑' k : ℕ, powerTerm r k) - 1/(2:ℝ)^(r+1) := by linarith [ht1]
  have he2 : (∑' k : ℕ, powerTerm r (k+2)) =
      (∑' k : ℕ, powerTerm r k) - 1/(2:ℝ)^(r+1) - 1/(6:ℝ)^(r+1) := by
    linarith [ht2]
  simp only [remainder]
  rw [Summable.tsum_add ((summable_powerTerm r).sub (h1.mul_left _)) (h2.mul_left _),
    Summable.tsum_sub (summable_powerTerm r) (h1.mul_left _), tsum_mul_left,
    tsum_mul_left, he1, he2]
  simp only [leading, boundary, Int.cast_sub, Int.cast_add, Int.cast_pow,
    Int.cast_mul, Int.cast_ofNat, Int.cast_one]
  have h6 : (6:ℝ)^(r+1) = (2:ℝ)^(r+1) * (3:ℝ)^(r+1) := by
    rw [← mul_pow]; norm_num
  rw [h6]
  field_simp
  ring_nf

lemma column_form_pos (r : ℕ) :
    0 < (leading r : ℝ)*(∑' k : ℕ, powerTerm r k) - (boundary r : ℝ) := by
  rw [← remainder_sum]
  exact (summable_remainder r).tsum_pos (fun k => (remainder_pos r k).le) 0
    (remainder_pos r 0)

lemma remainder_lt (r k : ℕ) : remainder r k < powerTerm r k := by
  have hh : (6:ℝ)^(r+1)*powerTerm r (k+2) ≤
      (2:ℝ)^(r+1)*powerTerm r (k+1) := by
    rw [show k+2 = (k+1)+1 by omega, powerTerm_succ]
    push_cast
    rw [show (k:ℝ)+1+3 = k+4 by ring_nf]
    rw [← mul_assoc, ← mul_pow, mul_one_div]
    apply mul_le_mul_of_nonneg_right _ (powerTerm_pos r (k+1)).le
    apply pow_le_pow_left₀ (by positivity)
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hp : 0 < (2:ℝ)^(r+1)*powerTerm r (k+1) :=
    mul_pos (by positivity) (powerTerm_pos r (k+1))
  unfold remainder
  nlinarith

theorem column_form_bounds (r : ℕ) :
    0 < (leading r : ℝ)*(∑' k : ℕ, powerTerm r k) - (boundary r : ℝ) ∧
    (leading r : ℝ)*(∑' k : ℕ, powerTerm r k) - (boundary r : ℝ) <
      (3/2:ℝ) / (2:ℝ)^(r+1) := by
  refine ⟨column_form_pos r, ?_⟩
  rw [← remainder_sum]
  have hs : (∑' k : ℕ, remainder r k) < ∑' k : ℕ, powerTerm r k := by
    exact Summable.tsum_lt_tsum (fun k => (remainder_lt r k).le) (remainder_lt r 0)
      (summable_remainder r) (summable_powerTerm r)
  apply hs.trans_le
  simpa [powerTerm, mul_div_assoc] using (powerTerm_tail_bounds r 0).2

open Filter
open scoped Topology

theorem tendsto_column_forms :
    Tendsto (fun r : ℕ => (leading r : ℝ)*(∑' k : ℕ, powerTerm r k) -
      (boundary r : ℝ)) atTop (𝓝 0) := by
  have ht : Tendsto (fun r : ℕ => (3/2:ℝ)/(2:ℝ)^(r+1)) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ)<1)).mul_const (3/4:ℝ)
    convert h using 1
    · ext r
      rw [pow_succ, div_pow, one_pow]
      ring_nf
    · ring_nf
  exact squeeze_zero (fun r => (column_form_bounds r).1.le)
    (fun r => (column_form_bounds r).2.le) ht

end FallingResidueForms

#print axioms FallingResidueForms.column_form_pos

#print axioms FallingResidueForms.column_form_bounds
#print axioms FallingResidueForms.tendsto_column_forms
