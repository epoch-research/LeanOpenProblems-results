import Submission.RectangularVarianceScaleBarrier
import Submission.CoreTailSieve

/-! Iterating a uniform rectangular variance estimate forces a uniform
power-saving discrepancy from full-period density. This is an implication,
not an assertion that the variance estimate holds. -/
namespace Erdos970.GapAverages
open Finset Real Filter
open scoped Topology

lemma roughCount_error (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) (m : ℕ) :
    |roughCount P m - (m : ℝ) * density P| ≤ (2 : ℝ) ^ P.card := by
  have hh := CoreTailSieve.siftCount_error P ∅ hP (by simp) (by simp) (fun _ => 0) m
  simpa only [CoreTailSieve.siftCount, CoreTailSieve.siftSet,
    CoreTailSieve.density, density, roughCount, notMem_empty, forall_const,
    IsEmpty.forall_iff, and_true, prod_empty, div_one, Nat.modEq_zero_iff_dvd] using hh

lemma roughCount_scaled_limit (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    (n p : ℕ) (hp : 1 < p) :
    Tendsto (fun j : ℕ => roughCount P (n * p ^ j) / (p : ℝ) ^ j)
      atTop (𝓝 ((n : ℝ) * density P)) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [norm_eq_abs]
  apply squeeze_zero' (g := fun j => (2 : ℝ) ^ P.card / (p : ℝ) ^ j)
    (Eventually.of_forall (fun _ => abs_nonneg _))
  · apply Eventually.of_forall
    intro j
    have hpj : (0 : ℝ) < (p : ℝ) ^ j := pow_pos (by linarith) _
    have he : |roughCount P (n * p ^ j) / (p : ℝ) ^ j - (n : ℝ) * density P| =
        |roughCount P (n * p ^ j) - (n * p ^ j : ℕ) * density P| / (p : ℝ) ^ j := by
      calc
        _ = |(roughCount P (n * p ^ j) - (n * p ^ j : ℕ) * density P) / (p : ℝ) ^ j| := by
          congr 1
          push_cast
          field_simp
        _ = _ := by rw [abs_div, abs_of_pos hpj]
    rw [he]
    exact div_le_div_of_nonneg_right (roughCount_error P hP _) hpj.le
  · exact (tendsto_pow_atTop_atTop_of_one_lt hpR).const_div_atTop _

lemma upper_of_halving_recurrence_at (f : ℕ → ℝ) (p D L : ℝ) (hp : 0 < p)
    (hlim : Tendsto (fun j => f j / p ^ j) atTop (𝓝 L))
    (hstep : ∀ j, f j - f (j + 1) / p ≤ D * (p / 2) ^ j) :
    ∀ k, f k ≤ L * p ^ k + 2 * D * (p / 2) ^ k := by
  let g := fun j : ℕ => (f j - 2 * D * (p / 2) ^ j) / p ^ j
  have he (j : ℕ) : g j = f j / p ^ j - 2 * D * (1 / 2 : ℝ) ^ j := by
    dsimp only [g]
    rw [sub_div, mul_div_assoc, ← div_pow]
    congr 2
    field_simp
  have hmono : Monotone g := by
    apply monotone_nat_of_le_succ
    intro j
    have hnum : 0 ≤ f (j + 1) - p * f j + p * D * (p / 2) ^ j := by
      have hh := (sub_le_iff_le_add).mp (hstep j)
      have hh' := mul_le_mul_of_nonneg_left hh hp.le
      rw [mul_add, mul_div_cancel₀ _ hp.ne'] at hh'
      linarith only [hh']
    have hid : g (j + 1) - g j =
        (f (j + 1) - p * f j + p * D * (p / 2) ^ j) / (p ^ j * p) := by
      dsimp only [g]
      rw [pow_succ, pow_succ]
      field_simp [hp.ne']
      ring
    have hh : 0 ≤ g (j + 1) - g j := by rw [hid]; positivity
    linarith only [hh]
  have hglim : Tendsto g atTop (𝓝 L) := by
    simp_rw [show g = (fun j => f j / p ^ j - 2 * D * (1 / 2 : ℝ) ^ j) from funext he]
    convert hlim.sub ((tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).const_mul (2 * D)) using 1
    ring
  intro k
  have hh : g k ≤ L := ge_of_tendsto hglim
    (by filter_upwards [eventually_ge_atTop k] with j hj; exact hmono hj)
  have hh' := (div_le_iff₀ (pow_pos hp k)).mp hh
  linarith only [hh']

lemma upper_of_halving_recurrence (f : ℕ → ℝ) (p D L : ℝ) (hp : 0 < p)
    (hlim : Tendsto (fun j => f j / p ^ j) atTop (𝓝 L))
    (hstep : ∀ j, f j - f (j + 1) / p ≤ D * (p / 2) ^ j) :
    f 0 ≤ L + 2 * D := by
  simpa only [pow_zero, mul_one] using upper_of_halving_recurrence_at f p D L hp hlim hstep 0

lemma abs_sub_le_of_halving_recurrence (f : ℕ → ℝ) (p D L : ℝ) (hp : 0 < p)
    (hlim : Tendsto (fun j => f j / p ^ j) atTop (𝓝 L))
    (hstep : ∀ j, |f j - f (j + 1) / p| ≤ D * (p / 2) ^ j) :
    |f 0 - L| ≤ 2 * D := by
  have hu := upper_of_halving_recurrence f p D L hp hlim (fun j => (abs_le.mp (hstep j)).2)
  have hl := upper_of_halving_recurrence (fun j => -f j) p D (-L) hp
    (by simpa only [neg_div] using hlim.neg) (fun j => by
      have hh := (abs_le.mp (hstep j)).1
      rw [neg_div]
      linarith only [hh])
  exact abs_le.mpr ⟨by linarith only [hl], by linarith only [hu]⟩

lemma sixth_halving_growth (p : ℝ) (hp : 8 ≤ p) : p ^ 4 ≤ (p / 2) ^ 6 := by
  have hp2 : (8 : ℝ) ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ (by norm_num) hp 2
  have hh := mul_le_mul_of_nonneg_left hp2 (show 0 ≤ p ^ 4 by positivity)
  nlinarith only [hh]

/-- A uniform variance-cube bound at every larger rectangle would imply a
sixth-root power-saving discrepancy. The constants are kept algebraic. -/
theorem roughCount_discrepancy_of_variance_cube (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime) (n p : ℕ) (hp : 8 ≤ p)
    (hc : ∀ q ∈ P, p.Coprime q) (C D : ℝ) (hD : 0 ≤ D)
    (hbudget : (p : ℝ) ^ 3 * (C * (n : ℝ) ^ 4) ≤ D ^ 6)
    (hV : ∀ j : ℕ,
      rowConditionalVariance P (p * (n * p ^ j)) p (zeroPhase P hP) ^ 3 ≤
        C * (n * p ^ j : ℕ) ^ 4) :
    |roughCount P n - (n : ℝ) * density P| ≤ 2 * D := by
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hh := abs_sub_le_of_halving_recurrence
    (fun j => roughCount P (n * p ^ j)) (p : ℝ) D ((n : ℝ) * density P) hpR
    (roughCount_scaled_limit P hP n p (by omega)) ?_
  · simpa only [pow_zero, Nat.mul_one] using hh
  intro j
  have hbound := roughCount_gap_sixth_le P hP (n * p ^ j) p hp0 hc C (hV j)
  have hmul : p * (n * p ^ j) = n * p ^ (j + 1) := by rw [pow_succ]; ring
  rw [hmul] at hbound
  have hpower : (p : ℝ) ^ (4 * j) ≤ ((p : ℝ) / 2) ^ (6 * j) := by
    have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ 4)
      (sixth_halving_growth (p : ℝ) (by exact_mod_cast hp)) j
    simpa only [← pow_mul] using hpow
  have hbudget' : (p : ℝ) ^ 3 * (C * (n * p ^ j : ℕ) ^ 4) ≤
      (D * ((p : ℝ) / 2) ^ j) ^ 6 := by
    calc
      _ = ((p : ℝ) ^ 3 * (C * (n : ℝ) ^ 4)) * (p : ℝ) ^ (4 * j) := by
        push_cast
        ring
      _ ≤ D ^ 6 * ((p : ℝ) / 2) ^ (6 * j) :=
        mul_le_mul hbudget hpower (by positivity) (by positivity)
      _ = _ := by ring
  apply le_of_pow_le_pow_left₀ (by norm_num : (6 : ℕ) ≠ 0) (by positivity)
  rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, sq_abs, ← pow_mul]
  exact hbound.trans hbudget'

#print axioms roughCount_scaled_limit
#print axioms roughCount_discrepancy_of_variance_cube
end Erdos970.GapAverages
