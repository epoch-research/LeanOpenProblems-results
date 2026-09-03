import Submission.LambertBoundaryForms
import Submission.BoundedBoundaryDependence

/-!
An explicit asymptotic small-or-zero construction with a quadratic sampling
window and polynomially bounded integer weights. The weight vector is nonzero,
but neither its coefficient pair nor its value is asserted to be nonzero.
Consequently these results do not prove irrationality of the target.
-/

namespace LambertQuadraticWindow

open Finset Erdos68Development LambertBoundaryClearing LambertBoundaryForms
open Filter
open scoped Topology

lemma shift_sum_bound (K : ℕ) (hK : 1 ≤ K) :
    (List.range' 2 K).sum ≤ 2*K^2 := by
  have hs := List.sum_le_card_nsmul (List.range' 2 K) (K+1) (by
    intro x hx
    obtain ⟨i, hi, he⟩ := List.mem_range'.mp hx
    omega)
  simp only [List.length_range', nsmul_eq_mul] at hs
  nlinarith

lemma quadratic_window_card (K : ℕ) (hK : 1 ≤ K) :
    commonMultiplier (List.range' 2 K) (K^2 + (K^2-1)) <
      ((4*K^2)^4+1) ^ (K^2) := by
  have hn : K^2 + (K^2-1) + (List.range' 2 K).sum ≤ 4*K^2 := by
    have hs := shift_sum_bound K hK
    omega
  calc
    _ ≤ (K^2 + (K^2-1) + (List.range' 2 K).sum).factorial := Nat.div_le_self _ _
    _ ≤ (4*K^2).factorial := Nat.factorial_le hn
    _ ≤ (4*K^2) ^ (4*K^2) := Nat.factorial_le_pow _
    _ = ((4*K^2)^4) ^ (K^2) := by rw [pow_mul]
    _ < _ := Nat.pow_lt_pow_left (by omega) (by positivity)

lemma quadratic_window_exponent (K : ℕ) (hK : 16 ≤ K) :
    K+13 ≤ K^2/2-1 := by
  have hm : K+14 ≤ K^2/2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr
    have hh := Nat.mul_le_mul_left K hK
    nlinarith
  omega

lemma quadratic_window_error_bound (K : ℕ) (hK : 16 ≤ K) :
    ((K^2 : ℕ) : ℝ) * (((4*K^2)^4 : ℕ) : ℝ) *
      (2^(K+1) / ((K+1 : ℕ) : ℝ)^(K^2/2-1)) ≤ 256 / (K : ℝ)^2 := by
  have hk : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hb : (1 : ℝ) ≤ K+1 := by linarith
  have he := quadratic_window_exponent K hK
  have hp : (K : ℝ)^12 * 2^(K+1) ≤ (K+1 : ℝ)^(K^2/2-1) := by
    calc
      _ ≤ (K+1 : ℝ)^12 * (K+1 : ℝ)^(K+1) := by
        apply mul_le_mul
        · gcongr; linarith
        · gcongr; exact_mod_cast (show 2 ≤ K+1 by omega)
        · positivity
        · positivity
      _ = (K+1 : ℝ)^(K+13) := by rw [← pow_add]; congr 1; omega
      _ ≤ _ := pow_le_pow_right₀ hb he
  push_cast
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (by positivity) (sq_pos_of_pos hk)).mpr
  calc
    _ = 256 * ((K : ℝ)^12 * 2^(K+1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by norm_num)

/-- The weights have size at most 256*K^8, and the resulting integral form
has absolute value at most 256/K^2. Its value is allowed to be zero. -/
theorem quadratic_window_small_or_zero (K : ℕ) (hK : 16 ≤ K) :
    ∃ w : Fin (K^2) → ℤ, w ≠ 0 ∧ (∀ i, |w i| ≤ (4*K^2)^4) ∧ ∃ b : ℤ,
      (∑ i, (w i : ℝ) * (boundary (List.range' 2 K) (K^2 + i) : ℝ)) = b ∧
      |(coefficient (List.range' 2 K) * ∑ i, w i : ℤ) *
        (∑' k : ℕ, term k) - b| ≤ 256 / (K : ℝ)^2 := by
  have hH : 4 ≤ K^2 := by nlinarith
  obtain ⟨w, hw, hs, b, hb, he⟩ := window_small_or_zero_form K (K^2) (K^2)
    ((4*K^2)^4) hH (quadratic_window_card K (by omega))
  exact ⟨w, hw, hs, b, hb, he.trans (quadratic_window_error_bound K hK)⟩

/-- Arbitrarily small integer forms, with nonzero polynomially bounded
weights. This deliberately makes no nonvanishing assertion about the forms. -/
theorem arbitrarily_small_or_zero (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, 16 ≤ K ∧ ∃ w : Fin (K^2) → ℤ,
      w ≠ 0 ∧ (∀ i, |w i| ≤ (4*K^2)^4) ∧ ∃ b : ℤ,
      (∑ i, (w i : ℝ) * (boundary (List.range' 2 K) (K^2 + i) : ℝ)) = b ∧
      |(coefficient (List.range' 2 K) * ∑ i, w i : ℤ) *
        (∑' k : ℕ, term k) - b| < ε := by
  obtain ⟨K, hK⟩ := exists_nat_gt (max 16 (256/ε))
  have hK16 : 16 ≤ K := by
    have ht : (16 : ℝ) < K := lt_of_le_of_lt (le_max_left _ _) hK
    exact_mod_cast ht.le
  have hk : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hsmall : 256 / (K : ℝ)^2 < ε := by
    have ht : 256 / ε < (K : ℝ) := lt_of_le_of_lt (le_max_right _ _) hK
    have ht' := (div_lt_iff₀ hε).mp ht
    have h1 : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
    have hsq : (K : ℝ) ≤ (K : ℝ)^2 := by nlinarith
    apply (div_lt_iff₀ (sq_pos_of_pos hk)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsq hε.le]
  obtain ⟨w, hw, hs, b, hb, he⟩ := quadratic_window_small_or_zero K hK16
  exact ⟨K, hK16, w, hw, hs, b, hb, he.trans_lt hsmall⟩

lemma quadratic_window_rank_bound (K : ℕ) (hK : 32 ≤ K) :
    2 * (((K^2 : ℕ) : ℝ) * (((4*K^2)^4 : ℕ) : ℝ)) *
      (((K^2 : ℕ) : ℝ) * (((4*K^2)^4 : ℕ) : ℝ) *
        (2^(K+1) / ((K+1 : ℕ) : ℝ)^(K^2/2-1))) < 1 := by
  have hk : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have he : K+25 ≤ K^2/2-1 := by
    have hm : K+26 ≤ K^2/2 := by
      apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr
      have hh := Nat.mul_le_mul_left K hK
      nlinarith
    omega
  have hb : (1 : ℝ) ≤ K+1 := by linarith
  have hp : (K : ℝ)^20 * 2^(K+1) ≤ (K+1 : ℝ)^(K+21) := by
    calc
      _ ≤ (K+1 : ℝ)^20 * (K+1 : ℝ)^(K+1) := by
        apply mul_le_mul
        · gcongr; linarith
        · gcongr; exact_mod_cast (show 2 ≤ K+1 by omega)
        · positivity
        · positivity
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hconst : (131072 : ℝ) < (K+1 : ℝ)^4 := by
    calc
      _ < (32 : ℝ)^4 := by norm_num
      _ ≤ _ := by gcongr; exact_mod_cast (show 32 ≤ K+1 by omega)
  have hnum : 131072 * ((K : ℝ)^20 * 2^(K+1)) < (K+1 : ℝ)^(K^2/2-1) := by
    calc
      _ ≤ 131072 * (K+1 : ℝ)^(K+21) := mul_le_mul_of_nonneg_left hp (by norm_num)
      _ < (K+1 : ℝ)^4 * (K+1 : ℝ)^(K+21) :=
        mul_lt_mul_of_pos_right hconst (by positivity)
      _ = (K+1 : ℝ)^(K+25) := by rw [← pow_add]; congr 1; omega
      _ ≤ _ := pow_le_pow_right₀ hb he
  push_cast
  have hid : 2 * ((K : ℝ)^2 * (4*(K : ℝ)^2)^4) *
      ((K : ℝ)^2 * (4*(K : ℝ)^2)^4 * (2^(K+1)/(K+1 : ℝ)^(K^2/2-1))) =
      (131072 * ((K : ℝ)^20 * 2^(K+1))) / (K+1 : ℝ)^(K^2/2-1) := by ring
  rw [hid]
  exact (div_lt_one (by positivity)).mpr hnum

/-- Every two integrally cleared forms in this particular quadratic window
with the displayed polynomial weight bound have dependent coefficient pairs.
Thus this family cannot meet an independent-pair criterion at large K. -/
theorem quadratic_window_pair_dependence (K : ℕ) (hK : 32 ≤ K)
    (w v : Fin (K^2) → ℤ)
    (hw : ∀ i, |w i| ≤ (4*K^2)^4) (hv : ∀ i, |v i| ≤ (4*K^2)^4)
    (b d : ℤ)
    (hb : ∑ i, (w i : ℝ) * (boundary (List.range' 2 K) (K^2+i) : ℝ) = b)
    (hd : ∑ i, (v i : ℝ) * (boundary (List.range' 2 K) (K^2+i) : ℝ) = d) :
    (∑ i, w i)*d - b*(∑ i, v i) = 0 := by
  apply BoundedBoundaryDependence.bounded_window_dependence (K^2) ((4*K^2)^4)
    (coefficient (List.range' 2 K)) (∑' k : ℕ, term k)
    (2^(K+1) / ((K+1 : ℕ) : ℝ)^(K^2/2-1))
    (fun i => (boundary (List.range' 2 K) (K^2+i) : ℝ))
    (fun i => window_error_bound K (K^2) (K^2+i) (by nlinarith) (by omega))
    (quadratic_window_rank_bound K hK) w v hw hv b d hb hd

end LambertQuadraticWindow

#print axioms LambertQuadraticWindow.quadratic_window_small_or_zero
#print axioms LambertQuadraticWindow.arbitrarily_small_or_zero

#print axioms LambertQuadraticWindow.quadratic_window_pair_dependence
