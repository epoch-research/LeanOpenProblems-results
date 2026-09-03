import Submission.SmoothPrimeCore
import Submission.Sublinear

/-!
# Pointwise extraction of a large smooth-core divisor

These results strengthen exponent preservation by retaining a divisor of the
original output and a lower bound on its size. They do not create higher
multiplicity exponents.
-/

open Nat Filter
open scoped Classical BigOperators

namespace Erdos821

set_option maxHeartbeats 2000000

/-- A single divisor realizes the normalized core sum up to its number of terms. -/
lemma exists_smooth_core_divisor_weight (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : 0 < n) :
    ∃ d ∈ n.divisors,
      (g n : ℝ) ≤ ((n.divisors.card : ℝ)*Real.exp ((k : ℝ)*n.primeFactors.card)) *
        (n : ℝ)^(1-1/(k : ℝ)) *
          ((gSmoothCore k d : ℝ)*(d : ℝ)^(-(1-1/(k : ℝ)))) := by
  let s := 1-1/(k : ℝ)
  let w : ℕ → ℝ := fun d => (gSmoothCore k d : ℝ)*(d : ℝ)^(-s)
  obtain ⟨d, hd, hmax⟩ := Finset.exists_max_image n.divisors w
    ⟨1, Nat.one_mem_divisors.mpr hn.ne'⟩
  refine ⟨d, hd, ?_⟩
  have hsum : (∑ e ∈ n.divisors, w e) ≤ (n.divisors.card : ℝ)*w d := by
    calc
      _ ≤ ∑ _e ∈ n.divisors, w d := Finset.sum_le_sum hmax
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  calc
    (g n : ℝ) ≤ (n : ℝ)^s*Real.exp ((k : ℝ)*n.primeFactors.card)*
        ∑ e ∈ n.divisors, w e := g_le_smooth_core_divisor_sum k hk n hn
    _ ≤ (n : ℝ)^s*Real.exp ((k : ℝ)*n.primeFactors.card)*
        ((n.divisors.card : ℝ)*w d) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by dsimp [w, s]; ring

/-- At every sufficiently large qualifying output, not merely along an
unspecified subsequence, a divisor retains the desired normalized mass. -/
theorem eventually_extract_smooth_core_divisor (k : ℕ) (hk : 1 ≤ k)
    (β ε : ℝ) (hβ : 1-1/(k : ℝ) ≤ β) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ)^(β+ε) < g n →
      ∃ d ∈ n.divisors,
        (n : ℝ)^(β-(1-1/(k : ℝ)))*(d : ℝ)^(1-1/(k : ℝ)) < gSmoothCore k d ∧
          (d : ℝ)^β < gSmoothCore k d := by
  let s := 1-1/(k : ℝ)
  filter_upwards [eventually_core_rough_cost_le_rpow k 1 ε (by norm_num) hε,
    eventually_ge_atTop 1] with n hcost hn
  intro hg
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  simp only [one_mul] at hcost
  obtain ⟨d, hd, hbound⟩ := exists_smooth_core_divisor_weight k hk n hn0
  have hd0 := Nat.pos_of_mem_divisors hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hdle : (d : ℝ) ≤ n := by exact_mod_cast Nat.divisor_le hd
  let w : ℝ := (gSmoothCore k d : ℝ)*(d : ℝ)^(-s)
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hprod : (n : ℝ)^(β+ε) < (n : ℝ)^(ε+s)*w := by
    calc
      _ < (g n : ℝ) := hg
      _ ≤ ((n.divisors.card : ℝ)*Real.exp ((k : ℝ)*n.primeFactors.card))*(n : ℝ)^s*w := hbound
      _ ≤ (n : ℝ)^ε*(n : ℝ)^s*w :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcost (Real.rpow_nonneg hnR.le _)) hw
      _ = _ := by rw [← Real.rpow_add hnR]
  have he : (n : ℝ)^(β+ε) = (n : ℝ)^(ε+s)*(n : ℝ)^(β-s) := by
    rw [← Real.rpow_add hnR]
    congr 1
    ring
  rw [he] at hprod
  have hweight : (n : ℝ)^(β-s) < w :=
    (mul_lt_mul_iff_right₀ (Real.rpow_pos_of_pos hnR (ε+s))).mp hprod
  have hcore : (n : ℝ)^(β-s)*(d : ℝ)^s < gSmoothCore k d := by
    have h := mul_lt_mul_of_pos_right hweight (Real.rpow_pos_of_pos hdR s)
    dsimp [w] at h
    simpa only [mul_assoc, ← Real.rpow_add hdR, neg_add_cancel, Real.rpow_zero, mul_one] using h
  refine ⟨d, hd, hcore, ?_⟩
  calc
    (d : ℝ)^β = (d : ℝ)^(β-s)*(d : ℝ)^s := by
      rw [← Real.rpow_add hdR, sub_add_cancel]
    _ ≤ (n : ℝ)^(β-s)*(d : ℝ)^s :=
      mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hdR.le hdle (sub_nonneg.mpr hβ)) (Real.rpow_nonneg hdR.le s)
    _ < _ := hcore

/-- An eventual full-fiber upper exponent controls how small the extracted
core output can be. The upper-bound hypothesis remains explicit. -/
theorem eventually_extract_smooth_core_divisor_of_upper_bound
    (k : ℕ) (hk : 1 ≤ k) (a β ε : ℝ)
    (ha : 1-1/(k : ℝ) < a) (hβ : 1-1/(k : ℝ) < β) (hε : 0 < ε)
    (H : ∀ᶠ d : ℕ in atTop, (g d : ℝ) ≤ (d : ℝ)^a) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ)^(β+ε) < g n →
      ∃ d ∈ n.divisors,
        (n : ℝ)^((β-(1-1/(k : ℝ)))/(a-(1-1/(k : ℝ)))) < d ∧
          (d : ℝ)^β < gSmoothCore k d := by
  let s := 1-1/(k : ℝ)
  obtain ⟨D, hD⟩ := eventually_atTop.mp H
  let M : ℝ := ∑ d ∈ Finset.range D, (gSmoothCore k d : ℝ)*(d : ℝ)^(-s)
  have hlim : Tendsto (fun n : ℕ => (n : ℝ)^(β-s)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hβ)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_extract_smooth_core_divisor k hk β ε hβ.le hε,
    hlim.eventually (eventually_ge_atTop M), eventually_ge_atTop 1] with n hn hMn hn1
  intro hg
  obtain ⟨d, hd, hcore, hdg⟩ := hn hg
  have hd0 := Nat.pos_of_mem_divisors hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  change (n : ℝ)^(β-s)*(d : ℝ)^s < gSmoothCore k d at hcore
  have hweight : (n : ℝ)^(β-s) < (gSmoothCore k d : ℝ)*(d : ℝ)^(-s) := by
    have h := mul_lt_mul_of_pos_right hcore (Real.rpow_pos_of_pos hdR (-s))
    simpa only [mul_assoc, ← Real.rpow_add hdR, add_neg_cancel, Real.rpow_zero, mul_one] using h
  have hDd : D ≤ d := by
    by_contra h
    have hm := Finset.single_le_sum
      (fun e (_ : e ∈ Finset.range D) =>
        mul_nonneg (Nat.cast_nonneg (gSmoothCore k e)) (Real.rpow_nonneg (Nat.cast_nonneg e) (-s)))
      (Finset.mem_range.mpr (Nat.lt_of_not_ge h))
    exact (hMn.trans_lt hweight).not_ge hm
  have hcore_le : (gSmoothCore k d : ℝ) ≤ g d := by
    exact_mod_cast (gSquarefreeOn_le_g (fun p => p-1 ∈ smoothShiftedPredecessors k) d)
  have hupper : (gSmoothCore k d : ℝ) ≤ (d : ℝ)^a := hcore_le.trans (hD d hDd)
  have hpower : (n : ℝ)^(β-s) < (d : ℝ)^(a-s) := by
    calc
      _ < (gSmoothCore k d : ℝ)*(d : ℝ)^(-s) := hweight
      _ ≤ (d : ℝ)^a*(d : ℝ)^(-s) :=
        mul_le_mul_of_nonneg_right hupper (Real.rpow_nonneg hdR.le _)
      _ = (d : ℝ)^(a-s) := by rw [← Real.rpow_add hdR]; rfl
  refine ⟨d, hd, ?_, hdg⟩
  change (n : ℝ)^((β-s)/(a-s)) < d
  apply (Real.rpow_lt_rpow_iff (Real.rpow_nonneg hnR.le _) hdR.le (sub_pos.mpr ha)).mp
  rw [← Real.rpow_mul hnR.le, div_mul_cancel₀ _ (sub_pos.mpr ha).ne']
  exact hpower

/-- Unconditionally, the selected core is polynomially large in the original
output. This uses the proved eventual sublinearity of g. -/
theorem eventually_extract_polynomially_large_smooth_core
    (k : ℕ) (hk : 1 ≤ k) (β ε : ℝ)
    (hβ : 1-1/(k : ℝ) < β) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ)^(β+ε) < g n →
      ∃ d ∈ n.divisors,
        (n : ℝ)^((k : ℝ)*(β-(1-1/(k : ℝ)))) < d ∧
          (d : ℝ)^β < gSmoothCore k d := by
  have H : ∀ᶠ d : ℕ in atTop, (g d : ℝ) ≤ (d : ℝ)^(1 : ℝ) := by
    filter_upwards [eventually_g_lt_self] with d hd
    simpa only [Real.rpow_one] using (show (g d : ℝ) ≤ d by exact_mod_cast hd.le)
  have ha := (reciprocal_exponent_bounds k hk).2
  have h := eventually_extract_smooth_core_divisor_of_upper_bound k hk 1 β ε ha hβ hε H
  have he : (β-(1-1/(k : ℝ)))/(1-(1-1/(k : ℝ))) = (k : ℝ)*(β-(1-1/(k : ℝ))) := by
    rw [sub_sub_cancel]
    field_simp
  simpa only [he] using h

/-- Near a hypothesized upper exponent, a qualifying output has a smooth
core of almost the same logarithmic size. The near-extremal fibers are not
asserted to exist by this theorem. -/
theorem near_upper_exponent_has_large_smooth_core (k : ℕ) (hk : 1 ≤ k)
    (a : ℝ) (ha : 1-1/(k : ℝ) < a) (ha1 : a ≤ 1)
    (H : ∀ᶠ d : ℕ in atTop, (g d : ℝ) ≤ (d : ℝ)^a)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop,
      (n : ℝ)^(a-δ) < g n → ∃ d ∈ n.divisors,
        (n : ℝ)^(1-η) < d ∧ (d : ℝ)^(a-η) < gSmoothCore k d := by
  let s := 1-1/(k : ℝ)
  let δ := η*(a-s)/4
  let β := a-2*δ
  have hs : 0 ≤ s := (reciprocal_exponent_bounds k hk).1
  have has : 0 < a-s := sub_pos.mpr ha
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hηas : η*(a-s) ≤ a-s := mul_le_of_le_one_left has.le hη1
  have hβ : s < β := by dsimp [β, δ]; nlinarith
  have hηas' : η*(a-s) ≤ η := mul_le_of_le_one_right hη.le (by linarith)
  have hβlower : a-η ≤ β := by dsimp [β, δ]; nlinarith
  have he : (β-s)/(a-s) = 1-η/2 := by
    dsimp [β, δ]
    field_simp
    ring
  have hbe : β+δ = a-δ := by dsimp [β]; ring
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [eventually_extract_smooth_core_divisor_of_upper_bound k hk a β δ
    ha hβ hδ H, eventually_ge_atTop 1] with n hn hn1
  intro hg
  rw [hbe] at hn
  obtain ⟨d, hd, hsize, hcore⟩ := hn hg
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  refine ⟨d, hd, ?_, ?_⟩
  · rw [he] at hsize
    exact (Real.rpow_le_rpow_of_exponent_le hnR1 (by linarith : 1-η ≤ 1-η/2)).trans_lt hsize
  · exact (Real.rpow_le_rpow_of_exponent_le hd1 hβlower).trans_lt hcore

end Erdos821
