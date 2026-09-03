import Submission.SelbergCost

/-! A logarithmically improved remainder in the divisor-cutoff Selberg upper sieve. -/
namespace Erdos970.FiniteSelberg
open Finset Real
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def canonicalOrthogonal (q : ι → ℝ) (D : Finset (Finset ι)) (Q : Finset ι) : ℝ :=
  weight q Q * if Q ∈ D then 1 / normalizer q D else 0

lemma linearKernel_canonical (q : ι → ℝ) (D : Finset (Finset ι)) (ω : ι → Bool) :
    linearKernel q (canonicalOrthogonal q D) ω = kernel q D ω / normalizer q D := by
  classical
  unfold linearKernel canonicalOrthogonal
  simp only [mul_ite, mul_zero, ite_mul, zero_mul]
  rw [← sum_filter]
  simp only [filter_mem_eq_inter, univ_inter]
  unfold kernel
  rw [sum_div]
  apply sum_congr rfl
  intro Q hQ
  rw [weight_eq_inverse_variance]
  ring

lemma kernelCost_canonical (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (D : Finset (Finset ι)) (hDn : D.Nonempty) :
    kernelCost q (canonicalOrthogonal q D) =
      (∑ Q ∈ D, ∏ i ∈ Q, ((1 + q i) / (1 - q i))) / normalizer q D := by
  classical
  unfold canonicalOrthogonal
  rw [kernelCost_weighted q hq _ (fun Q => by split_ifs; exact one_div_pos.mpr (normalizer_pos q hq D hDn) |>.le; rfl)]
  simp only [ite_mul, zero_mul]
  rw [← sum_filter]
  simp only [filter_mem_eq_inter, univ_inter]
  rw [sum_div]
  apply sum_congr rfl
  intro Q hQ
  ring

lemma prime_canonical_cost_le (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hpinj : Function.Injective p) (R : ℕ) (hR : 0 < R) :
    kernelCost (fun i => 1 / (p i : ℝ))
      (canonicalOrthogonal (fun i => 1 / (p i : ℝ)) (divisorSupport p R)) ≤
      exp 2 * R / normalizer (fun i => 1 / (p i : ℝ)) (divisorSupport p R) := by
  have hq (i : ι) : 0 < 1 / (p i : ℝ) ∧ 1 / (p i : ℝ) < 1 := by
    have hpi : (1 : ℝ) < p i := by exact_mod_cast (hp i).one_lt
    exact ⟨by positivity, (div_lt_one (by linarith)).mpr hpi⟩
  rw [kernelCost_canonical _ hq _ (divisorSupport_nonempty p R hR)]
  apply div_le_div_of_nonneg_right _ (normalizer_pos _ hq _ (divisorSupport_nonempty p R hR)).le
  have heq (i : ι) : (1 + 1 / (p i : ℝ)) / (1 - 1 / (p i : ℝ)) =
      ((p i : ℝ) + 1) / (p i - 1) := by
    have h0 : (p i : ℝ) ≠ 0 := by exact_mod_cast (hp i).ne_zero
    have h1 : (p i : ℝ) - 1 ≠ 0 := by
      have h : (1 : ℝ) < p i := by exact_mod_cast (hp i).one_lt
      linarith
    field_simp
  simp_rw [heq]
  exact divisor_cost_sum_le p hp hpinj R

/-- The canonical upper square has an error bounded by its actual ordinary coefficient cost. -/
theorem majorant_interval_error_cost (q : ι → ℝ) (D : Finset (Finset ι))
    (m : ℕ) (ω : ℕ → ι → Bool)
    (herr : ∀ T : Finset ι,
      |(∑ j ∈ range m, hitMonomial T (ω j)) - (m : ℝ) * ∏ i ∈ T, q i| ≤ 1) :
    |(∑ j ∈ range m, majorant q D (ω j)) - (m : ℝ) * average q (majorant q D)| ≤
      kernelCost q (canonicalOrthogonal q D) ^ 2 := by
  have h := arbitrary_square_hit_error q (canonicalOrthogonal q D) m ω herr ∅
  simpa only [linearKernel_canonical, hitMonomial, prod_empty, one_mul, majorant] using h

theorem prime_survivors_le_sharp_cutoff (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hpinj : Function.Injective p) (r : ℕ → ℕ) (m R : ℕ) (hR : 0 < R) :
    (((range m).filter (fun j => ∀ i, ¬j ≡ r (p i) [MOD p i])).card : ℝ) ≤
      (m : ℝ) / normalizer (fun i => 1 / (p i : ℝ)) (divisorSupport p R) +
        (exp 2 * R / normalizer (fun i => 1 / (p i : ℝ)) (divisorSupport p R)) ^ 2 := by
  classical
  let q : ι → ℝ := fun i => 1 / (p i : ℝ)
  let D := divisorSupport p R
  let ω : ℕ → ι → Bool := fun j i => decide (j ≡ r (p i) [MOD p i])
  have hq (i : ι) : 0 < q i ∧ q i < 1 := by
    have hpi : (1 : ℝ) < p i := by exact_mod_cast (hp i).one_lt
    exact ⟨by dsimp [q]; positivity, (div_lt_one (by linarith)).mpr hpi⟩
  have hD := divisorSupport_nonempty p R hR
  have hcount : (((range m).filter (fun j => ∀ i, ¬j ≡ r (p i) [MOD p i])).card : ℝ) ≤
      ∑ j ∈ range m, majorant q D (ω j) := by
    rw [card_eq_sum_ones]
    push_cast
    rw [sum_filter]
    apply sum_le_sum
    intro j hj
    have hh := indicator_empty_le_majorant q hq D hD (ω j)
    have heq : ω j = (fun _ => false) ↔ ∀ i, ¬j ≡ r (p i) [MOD p i] := by simp [ω, funext_iff]
    simpa only [heq] using hh
  have he := (abs_le.mp (majorant_interval_error_cost q D m ω
    (prime_hits_intersection_error p hp hpinj r m))).2
  rw [majorant_average q hq D hD] at he
  have hc := prime_canonical_cost_le p hp hpinj R hR
  have hcost0 : 0 ≤ kernelCost q (canonicalOrthogonal q D) := sum_nonneg (fun T _ => abs_nonneg _)
  have hcsq := sq_le_sq₀ hcost0 (le_trans hcost0 hc) |>.mpr hc
  dsimp only [q, D] at hcount he hcsq
  simp only [mul_one_div] at he
  linarith

/-- Explicit upper sieve with a log-squared saving in the remainder. -/
theorem prime_survivors_le_sharp_log (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hpinj : Function.Injective p) (r : ℕ → ℕ) (m R : ℕ) (hR : 0 < R)
    (hfull : ∀ a, a.Prime → a ≤ R → ∃ i, p i = a) :
    (((range m).filter (fun j => ∀ i, ¬j ≡ r (p i) [MOD p i])).card : ℝ) ≤
      (m : ℝ) / log (R + 1) + (exp 2 * R / log (R + 1)) ^ 2 := by
  apply (prime_survivors_le_sharp_cutoff p hp hpinj r m R hR).trans
  have hl : 0 < log (R + 1) := log_pos (by exact_mod_cast Nat.lt_succ_of_le hR)
  have hn : log (R + 1) ≤ normalizer (fun i => 1 / (p i : ℝ)) (divisorSupport p R) := by
    have hh : log (R + 1) ≤ (harmonic R : ℝ) := by exact_mod_cast log_add_one_le_harmonic R
    exact hh.trans (harmonic_le_normalizer p hp hpinj R hfull)
  have hn0 := hl.trans_le hn
  apply add_le_add
  · exact div_le_div_of_nonneg_left (Nat.cast_nonneg m) hl hn
  · apply pow_le_pow_left₀ (by positivity)
    exact div_le_div_of_nonneg_left (by positivity) hl hn

#print axioms prime_survivors_le_sharp_log
end Erdos970.FiniteSelberg
