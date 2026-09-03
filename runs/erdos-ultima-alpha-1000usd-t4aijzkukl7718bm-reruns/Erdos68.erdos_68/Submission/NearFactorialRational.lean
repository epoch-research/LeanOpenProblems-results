import FormalConjecturesUtil

/-!
A rational reciprocal series with denominators congruent to -1 modulo (n+1)!,
and within a linear factor of (n+1)!. This is an auxiliary obstruction to
weaker growth-based approaches, not a disproof of the conjecture in Spec.lean.
-/

namespace NearFactorialRational

open Filter
open scoped Topology

def roundCoeff (A r b : ℚ) : ℤ :=
  ⌊(1 / (r - b) + 1) / A⌋ + 1

def roundDen (A r b : ℚ) : ℚ := (roundCoeff A r b : ℚ) * A - 1

def roundStep (A r b : ℚ) : ℚ := r - 1 / roundDen A r b

lemma roundDen_bounds {A r b : ℚ} (hA : 0 < A) :
    1 / (r - b) < roundDen A r b ∧
      roundDen A r b ≤ 1 / (r - b) + A := by
  have hl : (1 / (r - b) + 1) / A < (roundCoeff A r b : ℚ) := by
    simpa only [roundCoeff, Int.cast_add, Int.cast_one] using
      Int.lt_floor_add_one ((1 / (r - b) + 1) / A)
  have hu : (roundCoeff A r b : ℚ) ≤ (1 / (r - b) + 1) / A + 1 := by
    have h := Int.floor_le ((1 / (r - b) + 1) / A)
    simp only [roundCoeff, Int.cast_add, Int.cast_one]
    linarith
  have hl' := (div_lt_iff₀ hA).mp hl
  have hu' := mul_le_mul_of_nonneg_right hu hA.le
  rw [add_mul, div_mul_cancel₀ _ hA.ne', one_mul] at hu'
  unfold roundDen
  constructor <;> linarith

lemma roundStep_bounds {A r b : ℚ} (hA : 0 < A) (hb : 0 < b) (hbr : b < r) :
    b < roundStep A r b ∧ roundStep A r b ≤ b + A * r ^ 2 := by
  obtain ⟨hd, hu⟩ := roundDen_bounds (r := r) (b := b) hA
  have hrb : 0 < r - b := sub_pos.mpr hbr
  have hp : 0 < roundDen A r b := (one_div_pos.mpr hrb).trans hd
  constructor
  · have hi := one_div_lt_one_div_of_lt (one_div_pos.mpr hrb) hd
    rw [one_div_one_div] at hi
    unfold roundStep
    linarith
  · have hu' := mul_le_mul_of_nonneg_right hu hrb.le
    rw [add_mul, one_div_mul_cancel hrb.ne'] at hu'
    have hl' : 1 ≤ (r - b) * roundDen A r b := by
      have h := (div_lt_iff₀ hp).mp
        (show 1 / roundDen A r b < r - b by
          simpa only [one_div_one_div] using
            one_div_lt_one_div_of_lt (one_div_pos.mpr hrb) hd)
      nlinarith
    have hm := mul_le_mul_of_nonneg_left hl'
      (show 0 ≤ A * (r - b) by positivity)
    have hs : (r - b) ^ 2 ≤ r ^ 2 := by nlinarith
    have hm' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs hA.le) hp.le
    have hfinal : (r - b - A * r ^ 2) * roundDen A r b ≤ 1 := by
      nlinarith
    have hfinal' := (le_div_iff₀ hp).mpr hfinal
    unfold roundStep
    linarith

def rem : ℕ → ℚ
  | 0 => 1 / 16
  | n + 1 => roundStep (n + 1).factorial (rem n) (1 / (16 * (n + 3).factorial))

def coeff (n : ℕ) : ℤ :=
  roundCoeff (n + 1).factorial (rem n) (1 / (16 * (n + 3).factorial))

def denom (n : ℕ) : ℤ := coeff n * (n + 1).factorial - 1

lemma factorial_step_bound (n : ℕ) :
    (1 / (16 * (n + 3).factorial) : ℚ) +
        (n + 1).factorial * (1 / (4 * (n + 2).factorial) : ℚ) ^ 2 ≤
      1 / (4 * (n + 3).factorial) := by
  have hF : (0 : ℚ) < (n + 1).factorial := by positivity
  have hn : (0 : ℚ) ≤ n := by positivity
  have h2 : ((n + 2).factorial : ℚ) = (n + 2) * (n + 1).factorial := by
    exact_mod_cast Nat.factorial_succ (n + 1)
  have h3 : ((n + 3).factorial : ℚ) = (n + 3) * (n + 2).factorial := by
    exact_mod_cast Nat.factorial_succ (n + 2)
  rw [h3, h2]
  field_simp
  nlinarith

lemma rem_bounds (n : ℕ) :
    (1 / (16 * (n + 2).factorial) : ℚ) ≤ rem n ∧
      rem n ≤ 1 / (4 * (n + 2).factorial) := by
  induction n with
  | zero => norm_num [rem]
  | succ n ih =>
    have hf : (0 : ℚ) < (n + 1).factorial := by positivity
    have hb : (0 : ℚ) < 1 / (16 * (n + 3).factorial) := by positivity
    have hbr : (1 / (16 * (n + 3).factorial) : ℚ) < rem n := by
      apply lt_of_lt_of_le _ ih.1
      apply one_div_lt_one_div_of_lt (by positivity)
      have h : (n + 2).factorial < (n + 3).factorial :=
        Nat.factorial_lt_of_lt (by omega) (by omega)
      exact_mod_cast (show 16 * (n + 2).factorial < 16 * (n + 3).factorial by omega)
    obtain ⟨hl, hu⟩ := roundStep_bounds hf hb hbr
    constructor
    · simpa only [rem, Nat.add_assoc, Nat.reduceAdd] using hl.le
    · have hs : rem n ^ 2 ≤ (1 / (4 * (n + 2).factorial) : ℚ) ^ 2 := by
        have hr : 0 < rem n := lt_of_lt_of_le (by positivity) ih.1
        nlinarith [ih.2]
      have hh := mul_le_mul_of_nonneg_left hs hf.le
      have hx := factorial_step_bound n
      simp only [rem, Nat.add_assoc, Nat.reduceAdd]
      linarith

lemma rem_pos (n : ℕ) : 0 < rem n :=
  lt_of_lt_of_le (by positivity) (rem_bounds n).1

lemma rem_sub_succ (n : ℕ) : rem n - rem (n + 1) = 1 / (denom n : ℚ) := by
  simp only [rem, roundStep, roundDen, denom, coeff, Int.cast_sub, Int.cast_mul,
    Int.cast_natCast, Int.cast_one]
  ring

lemma denom_pos (n : ℕ) : 0 < denom n := by
  have hf : (0 : ℚ) < (n + 1).factorial := by positivity
  have hb : (0 : ℚ) < 1 / (16 * (n + 3).factorial) := by positivity
  have hbr : (1 / (16 * (n + 3).factorial) : ℚ) < rem n := by
    apply lt_of_lt_of_le _ (rem_bounds n).1
    apply one_div_lt_one_div_of_lt (by positivity)
    have h : (n + 2).factorial < (n + 3).factorial :=
      Nat.factorial_lt_of_lt (by omega) (by omega)
    exact_mod_cast (show 16 * (n + 2).factorial < 16 * (n + 3).factorial by omega)
  have hd := (roundDen_bounds (r := rem n) (b := 1 / (16 * (n + 3).factorial)) hf).1
  have hp : (0 : ℚ) < roundDen (n + 1).factorial (rem n)
      (1 / (16 * (n + 3).factorial)) :=
    (one_div_pos.mpr (sub_pos.mpr hbr)).trans hd
  have hc : (denom n : ℚ) = roundDen (n + 1).factorial (rem n)
      (1 / (16 * (n + 3).factorial)) := by
    simp [denom, coeff, roundDen]
  rw [← hc] at hp
  exact_mod_cast hp

lemma rem_tendsto : Tendsto (fun n => (rem n : ℝ)) atTop (𝓝 0) := by
  have hf : Tendsto (fun n => 1 / ((n + 2).factorial : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp
      (factorial_tendsto_atTop.comp (tendsto_add_atTop_nat 2))
  apply squeeze_zero (fun n => (show (0 : ℝ) < rem n by exact_mod_cast rem_pos n).le) _ hf
  intro n
  have h : (rem n : ℝ) ≤ 1 / (4 * (n + 2).factorial) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr (rem_bounds n).2
    push_cast at hh
    exact hh
  apply h.trans
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [Nat.cast_nonneg (α := ℝ) (n + 2).factorial]

lemma partial_sum (n : ℕ) :
    (∑ k ∈ Finset.range n, 1 / (denom k : ℝ)) = 1 / 16 - (rem n : ℝ) := by
  induction n with
  | zero => norm_num [rem]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h : (rem n : ℝ) - rem (n + 1) = 1 / (denom n : ℝ) := by
      exact_mod_cast rem_sub_succ n
    linarith

lemma hasSum_reciprocal : HasSum (fun n => 1 / (denom n : ℝ)) (1 / 16) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => by
    have h : (0 : ℝ) < denom n := by exact_mod_cast denom_pos n
    positivity) _).mpr
  simpa only [partial_sum, sub_zero] using
    (tendsto_const_nhds (x := (1 / 16 : ℝ))).sub rem_tendsto

lemma sum_reciprocal : (∑' n : ℕ, 1 / (denom n : ℝ)) = 1 / 16 :=
  hasSum_reciprocal.tsum_eq

lemma factorial_dvd_denom_add_one (n : ℕ) :
    ((n + 1).factorial : ℤ) ∣ denom n + 1 := by
  refine ⟨coeff n, ?_⟩
  simp only [denom, sub_add_cancel]
  ring

lemma rem_minus_base_lower (n : ℕ) :
    (1 / (16 * (n + 3) * (n + 1).factorial) : ℚ) ≤
      rem n - 1 / (16 * (n + 3).factorial) := by
  have h2 : ((n + 2).factorial : ℚ) = (n + 2) * (n + 1).factorial := by
    exact_mod_cast Nat.factorial_succ (n + 1)
  have h3 : ((n + 3).factorial : ℚ) = (n + 3) * (n + 2).factorial := by
    exact_mod_cast Nat.factorial_succ (n + 2)
  have hid : (1 / (16 * (n + 2).factorial) : ℚ) -
      1 / (16 * (n + 3).factorial) = 1 / (16 * (n + 3) * (n + 1).factorial) := by
    rw [h3, h2]
    field_simp
    ring
  linarith [(rem_bounds n).1]

lemma denom_bounds_rat (n : ℕ) :
    (4 * (n + 2).factorial : ℚ) < denom n ∧
      (denom n : ℚ) ≤ (16 * (n + 3) + 1) * (n + 1).factorial := by
  have hf : (0 : ℚ) < (n + 1).factorial := by positivity
  have hb : (0 : ℚ) < 1 / (16 * (n + 3).factorial) := by positivity
  have hc : (denom n : ℚ) = roundDen (n + 1).factorial (rem n)
      (1 / (16 * (n + 3).factorial)) := by
    simp [denom, coeff, roundDen]
  obtain ⟨hd, hu⟩ := roundDen_bounds (r := rem n)
    (b := 1 / (16 * (n + 3).factorial)) hf
  rw [← hc] at hd hu
  have hlo := rem_minus_base_lower n
  have hpos : (0 : ℚ) < rem n - 1 / (16 * (n + 3).factorial) :=
    lt_of_lt_of_le (by positivity) hlo
  have hup := one_div_le_one_div_of_le (by positivity) hlo
  rw [one_div_one_div] at hup
  constructor
  · have hsmall : rem n - 1 / (16 * (n + 3).factorial) <
        (1 / (4 * (n + 2).factorial) : ℚ) := by
      linarith [(rem_bounds n).2]
    have hi := one_div_lt_one_div_of_lt hpos hsmall
    rw [one_div_one_div] at hi
    exact hi.trans hd
  · nlinarith

lemma denom_bounds (n : ℕ) :
    (4 * (n + 2).factorial : ℤ) < denom n ∧
      denom n ≤ (16 * (n + 3) + 1 : ℤ) * (n + 1).factorial := by
  exact_mod_cast denom_bounds_rat n

def natDenom (n : ℕ) : ℕ := (denom n).toNat

lemma cast_natDenom_int (n : ℕ) : (natDenom n : ℤ) = denom n :=
  Int.toNat_of_nonneg (denom_pos n).le

lemma cast_natDenom_real (n : ℕ) : (natDenom n : ℝ) = (denom n : ℝ) := by
  exact_mod_cast cast_natDenom_int n

/-- This constructs a different reciprocal series, not the series in Erdős 68. -/
theorem exists_rational_factorial_rough_series :
    ∃ d : ℕ → ℕ,
      (∀ n, (n + 1).factorial ∣ d n + 1 ∧
        4 * (n + 2).factorial < d n ∧
        d n ≤ (16 * (n + 3) + 1) * (n + 1).factorial) ∧
      (∑' n : ℕ, 1 / (d n : ℝ)) = 1 / 16 := by
  refine ⟨natDenom, ?_, ?_⟩
  · intro n
    have hd := factorial_dvd_denom_add_one n
    have hb := denom_bounds n
    rw [← cast_natDenom_int n] at hd hb
    constructor
    · exact_mod_cast hd
    · exact_mod_cast hb
  · simpa only [cast_natDenom_real] using sum_reciprocal

lemma first_denominators : natDenom 0 = 20 ∧ natDenom 1 = 103 ∧ natDenom 2 = 443 := by
  norm_num [natDenom, denom, coeff, roundCoeff, rem, roundStep, roundDen]
  decide

#print axioms exists_rational_factorial_rough_series

#print axioms rem_bounds
#print axioms denom_pos
#print axioms sum_reciprocal

end NearFactorialRational
