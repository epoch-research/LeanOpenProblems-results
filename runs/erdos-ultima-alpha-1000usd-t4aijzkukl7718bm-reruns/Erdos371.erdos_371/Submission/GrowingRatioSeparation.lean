import FormalConjecturesUtil
import Submission.RectangleSeparation
import Submission.LogarithmicPrimeGap

/-! A growing unsigned separation of consecutive largest prime factors.
The allowed ratio grows as an exponential of a fourth root of a logarithm.
This does not establish either orientation's density. -/

namespace Erdos371GrowingRatioSeparation

open Filter Erdos371RectangleSeparation Erdos371SieveScaleBands Erdos371SieveParameters
open scoped Topology

/-- A convenient integer fourth-root scale on binary logarithms. -/
def rank (t : ℕ) : ℕ := Nat.log 16 t

def width (t : ℕ) : ℕ := 2^(rank t)
def level (t : ℕ) : ℕ := 3*rank t
def smoothLevel (t : ℕ) : ℕ := exponent (level t)

def ratio (n : ℕ) : ℕ := 2^(width (Nat.log 2 n))

lemma rank_tendsto : Tendsto rank atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (16^b)] with t ht
  exact Nat.le_log_of_pow_le (by decide) ht

lemma rank_bracket {t : ℕ} (ht : 0 < t) :
    16^(rank t) ≤ t ∧ t < 16^(rank t+1) :=
  ⟨Nat.pow_log_le_self _ ht.ne', Nat.lt_pow_succ_log_self (by decide) _⟩

lemma rank_mono : Monotone rank := fun _ _ h => Nat.log_mono_right h
lemma width_mono : Monotone width := fun _ _ h => Nat.pow_le_pow_right (by decide) (rank_mono h)
lemma ratio_mono : Monotone ratio := fun _ _ h =>
  Nat.pow_le_pow_right (by decide) (width_mono (Nat.log_mono_right h))

lemma exponent_ge_pow (k : ℕ) : 2^k ≤ exponent k := by
  have hh := depth_pos k
  unfold exponent
  calc
    2^k = 1*2^k := by omega
    _ ≤ (12*depth k)*2^k := Nat.mul_le_mul_right _ (by omega)

lemma smoothLevel_pos (t : ℕ) : 0 < smoothLevel t := exponent_pos _
lemma smoothLevel_ge (t : ℕ) : 2^(level t) ≤ smoothLevel t := exponent_ge_pow _
lemma width_le_smoothLevel (t : ℕ) : width t ≤ smoothLevel t := by
  apply (Nat.pow_le_pow_right (by decide : 0 < 2) (show rank t ≤ 3*rank t by omega)).trans
  exact smoothLevel_ge t

lemma exponent_ratio_eq (r : ℕ) :
    (exponent (3*r):ℝ)/(16:ℝ)^r = 3072*(3*(r:ℝ)+1)^2*(1/2:ℝ)^r := by
  calc
    _ = 3072*(3*(r:ℝ)+1)^2*((8:ℝ)^r/(16:ℝ)^r) := by
      simp only [exponent,depth,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat,pow_mul]
      norm_num
      ring
    _ = _ := by rw [← div_pow]; norm_num

lemma exponent_ratio_tendsto :
    Tendsto (fun r : ℕ => (exponent (3*r):ℝ)/(16:ℝ)^r) atTop (𝓝 0) := by
  have h0 := tendsto_pow_const_mul_const_pow_of_lt_one 0 (r := (1/2:ℝ)) (by norm_num) (by norm_num)
  have h1 := tendsto_pow_const_mul_const_pow_of_lt_one 1 (r := (1/2:ℝ)) (by norm_num) (by norm_num)
  have h2 := tendsto_pow_const_mul_const_pow_of_lt_one 2 (r := (1/2:ℝ)) (by norm_num) (by norm_num)
  have hh := ((h2.const_mul 9).add ((h1.const_mul 6).add h0)).const_mul 3072
  norm_num at hh
  apply hh.congr
  intro r
  rw [exponent_ratio_eq]
  ring

lemma smoothLevel_div_tendsto :
    Tendsto (fun t : ℕ => (smoothLevel t:ℝ)/t) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (exponent_ratio_tendsto.comp rank_tendsto)
  · exact Eventually.of_forall fun _ => by positivity
  · filter_upwards [eventually_gt_atTop 0] with t ht
    change (exponent (3*rank t):ℝ)/t ≤ (exponent (3*rank t):ℝ)/(16:ℝ)^(rank t)
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
      (by exact_mod_cast (rank_bracket ht).1)

lemma width_div_tendsto :
    Tendsto (fun t : ℕ => (width t:ℝ)/t) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds smoothLevel_div_tendsto
  · intro t; positivity
  · intro t
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (width_le_smoothLevel t)) (Nat.cast_nonneg _)

lemma small_ratio_bound (r : ℕ) :
    ((2^r+1:ℕ):ℝ)/(exponent (3*r):ℝ) ≤ 2*(1/4:ℝ)^r := by
  have he : (0:ℝ) < exponent (3*r) := Nat.cast_pos.mpr (exponent_pos _)
  have hpow : (0:ℝ) < (2:ℝ)^(3*r) := by positivity
  have hexp : (2:ℝ)^(3*r) ≤ (exponent (3*r):ℝ) := by exact_mod_cast exponent_ge_pow (3*r)
  have hh : ((2^r+1:ℕ):ℝ) ≤ 2*(2:ℝ)^r := by
    have h := Nat.one_le_two_pow (n := r)
    exact_mod_cast (show 2^r+1 ≤ 2*2^r by omega)
  calc
    _ ≤ (2*(2:ℝ)^r)/(exponent (3*r):ℝ) := div_le_div_of_nonneg_right hh he.le
    _ ≤ (2*(2:ℝ)^r)/(2:ℝ)^(3*r) := div_le_div_of_nonneg_left (by positivity) hpow hexp
    _ = _ := by
      rw [pow_mul]
      norm_num
      rw [mul_div_assoc,← div_pow]
      norm_num

lemma width_over_smooth_tendsto :
    Tendsto (fun t : ℕ => ((width t+1:ℕ):ℝ)/smoothLevel t) atTop (𝓝 0) := by
  have hu : Tendsto (fun t : ℕ => 2*(1/4:ℝ)^(rank t)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1/4:ℝ))
      (by norm_num) (by norm_num)).comp rank_tendsto).const_mul 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
  · intro t; positivity
  · intro t; exact small_ratio_bound _

lemma sieve_ratio_bound {t : ℕ} (ht : 0 < t) :
    ((t+1:ℕ):ℝ)*((width t+2:ℕ):ℝ)/(4:ℝ)^(level t) ≤ 96*(1/2:ℝ)^(rank t) := by
  have hb := (rank_bracket ht).2
  have h1 : ((t+1:ℕ):ℝ) ≤ 2*(16:ℝ)^(rank t+1) := by
    exact_mod_cast (show t+1 ≤ 2*16^(rank t+1) by omega)
  have h2 : ((width t+2:ℕ):ℝ) ≤ 3*(2:ℝ)^(rank t) := by
    have hh := Nat.one_le_two_pow (n := rank t)
    change ((2^(rank t)+2:ℕ):ℝ) ≤ _
    exact_mod_cast (show 2^(rank t)+2 ≤ 3*2^(rank t) by omega)
  calc
    _ ≤ (2*(16:ℝ)^(rank t+1))*(3*(2:ℝ)^(rank t))/(4:ℝ)^(level t) := by gcongr
    _ = _ := by
      unfold level
      rw [pow_succ,pow_mul]
      norm_num
      have he : (16:ℝ)^(rank t)*(2:ℝ)^(rank t)=(32:ℝ)^(rank t) := by rw [← mul_pow]; norm_num
      calc
        _ = 96*((16:ℝ)^(rank t)*(2:ℝ)^(rank t)/(64:ℝ)^(rank t)) := by ring
        _ = _ := by rw [he,← div_pow]; norm_num

lemma sieve_ratio_tendsto :
    Tendsto (fun t : ℕ => ((t+1:ℕ):ℝ)*((width t+2:ℕ):ℝ)/(4:ℝ)^(level t)) atTop (𝓝 0) := by
  have hu : Tendsto (fun t : ℕ => 96*(1/2:ℝ)^(rank t)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1/2:ℝ))
      (by norm_num) (by norm_num)).comp rank_tendsto).const_mul 96
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun _ => by positivity
  · filter_upwards [eventually_gt_atTop 0] with t ht
    exact sieve_ratio_bound ht

lemma parameters_admissible : ∀ᶠ t : ℕ in atTop, 0 < t ∧ 2*(width t+2) ≤ t := by
  have hh : Tendsto (fun t : ℕ => 2*((width t:ℝ)/t)+4/(t:ℝ)) atTop (𝓝 0) := by
    simpa using (width_div_tendsto.const_mul 2).add (tendsto_const_div_atTop_nhds_zero_nat 4)
  filter_upwards [eventually_gt_atTop 0, hh.eventually_lt_const (by norm_num : (0:ℝ) < 1)] with t ht hh
  refine ⟨ht,?_⟩
  have he : 2*((width t:ℝ)/t)+4/(t:ℝ)=(2*((width t:ℝ)+2))/(t:ℝ) := by ring
  rw [he] at hh
  have h := (div_lt_iff₀ (Nat.cast_pos.mpr ht)).mp hh
  exact_mod_cast (show 2*((width t:ℝ)+2) ≤ (t:ℝ) by linarith)

/-- The fraction of comparisons within `2^(width t)` tends to zero below `2^t`. -/
theorem growing_ratio_count_tendsto :
    Tendsto (fun t : ℕ => ((closeInputs (width t) (2^t)).card:ℝ)/(2:ℝ)^t) atTop (𝓝 0) := by
  have hpow : Tendsto (fun t : ℕ => (2:ℝ)^t) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hsqrt : Tendsto (fun t : ℕ => 2/Real.sqrt ((2:ℝ)^t)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp hpow)).const_mul 2
  have hsmall : Tendsto (fun t : ℕ => 2/(2:ℝ)^t) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp hpow).const_mul 2
  have hsm : Tendsto (fun t : ℕ => 8*((smoothLevel t+2:ℕ):ℝ)/t) atTop (𝓝 0) := by
    simpa [Nat.cast_add,Nat.cast_ofNat,add_div,mul_div_assoc] using
      (smoothLevel_div_tendsto.add (tendsto_const_div_atTop_nhds_zero_nat 2)).const_mul 8
  have hlow : Tendsto (fun t : ℕ => 128*((width t+1:ℕ):ℝ)/smoothLevel t) atTop (𝓝 0) := by
    simpa [mul_div_assoc] using width_over_smooth_tendsto.const_mul 128
  have hmid : Tendsto (fun t : ℕ => 32*((exponent (level t)+width t+3:ℕ):ℝ)/t) atTop (𝓝 0) := by
    simpa [smoothLevel,Nat.cast_add,Nat.cast_ofNat,add_div,mul_div_assoc] using
      ((smoothLevel_div_tendsto.add width_div_tendsto).add
        (tendsto_const_div_atTop_nhds_zero_nat 3)).const_mul 32
  have hhigh : Tendsto (fun t : ℕ =>
      96*(Real.exp 1)^2*((t+1:ℕ):ℝ)*((width t+2:ℕ):ℝ)/(4:ℝ)^(level t)) atTop (𝓝 0) := by
    convert sieve_ratio_tendsto.const_mul (96*(Real.exp 1)^2) using 1
    · ext t; ring
    · simp
  have hu := ((((hsqrt.add hsmall).add hsm).add hlow).add hmid).add hhigh
  norm_num only [add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun _ => by positivity
  · filter_upwards [parameters_admissible] with t ht
    exact closeInputs_ratio_bound (smoothLevel_pos t) (smoothLevel_ge t) ht.1 ht.2

lemma log_two_tendsto : Tendsto (Nat.log 2) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (2^b)] with n hn
  exact Nat.le_log_of_pow_le (by decide) hn

lemma ratio_tendsto : Tendsto ratio atTop atTop := by
  have hpow : Tendsto (fun t : ℕ => (2:ℕ)^t) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by decide)
  exact hpow.comp (hpow.comp (rank_tendsto.comp log_two_tendsto))

lemma ratio_eq (n : ℕ) : ratio n = 2^(2^(Nat.log 2 (Nat.log 2 n)/4)) := by
  unfold ratio width rank
  rw [show (16:ℕ)=2^4 by norm_num, Nat.log_pow_left]

lemma ratio_log_bracket {n : ℕ} (hn : 2 ≤ n) :
    (Nat.log 2 (ratio n))^4 ≤ Nat.log 2 n ∧
      Nat.log 2 n < 16*(Nat.log 2 (ratio n))^4 := by
  have ht : 0 < Nat.log 2 n := by
    have h := Nat.le_log_of_pow_le (by decide : 1 < (2:ℕ)) (show 2^1 ≤ n by simpa using hn)
    omega
  have hh := rank_bracket ht
  have he : (Nat.log 2 (ratio n))^4 = 16^(rank (Nat.log 2 n)) := by
    simp only [ratio,Nat.log_pow (by decide : 1 < (2:ℕ)),width]
    rw [← pow_mul,mul_comm, pow_mul]
    norm_num
  rw [he]
  exact ⟨hh.1,by simpa [pow_succ,mul_comm] using hh.2⟩

def comparable : Set ℕ := {n | max (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n+1)) ≤
  ratio n * min (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n+1))}

lemma comparable_density_dyadic :
    Tendsto (fun t : ℕ => comparable.partialDensity Set.univ (2^t)) atTop (𝓝 0) := by
  classical
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds growing_ratio_count_tendsto
  · intro t
    unfold Set.partialDensity
    positivity
  · intro t
    change comparable.partialDensity Set.univ (2^t) ≤ ((closeInputs (width t) (2^t)).card:ℝ)/(2:ℝ)^t
    rw [Erdos371ReflectionRange.partialDensity_eq_filter_card]
    have hc : ((Finset.range (2^t)).filter fun n => n ∈ comparable).card ≤
        (closeInputs (width t) (2^t)).card := by
      apply Finset.card_le_card
      intro n hn
      obtain ⟨hnN,hc⟩ := Finset.mem_filter.mp hn
      have hr : ratio n ≤ 2^(width t) := by
        have hh := ratio_mono (Finset.mem_range.mp hnN).le
        simpa [ratio,Nat.log_pow (by decide : 1 < (2:ℕ))] using hh
      exact Finset.mem_filter.mpr ⟨hnN,
        hc.trans (Nat.mul_le_mul_right _ hr)⟩
    have hh := div_le_div_of_nonneg_right (Nat.cast_le (α := ℝ) |>.mpr hc)
      (show (0:ℝ) ≤ (2:ℝ)^t by positivity)
    simpa using hh

/-- Even the explicitly growing multiplicative comparison window has density
zero. This is a statement about gap magnitudes, not the balance of their signs. -/
theorem growing_ratio_hasDensity_zero : comparable.HasDensity 0 := by
  apply Erdos371LogarithmicPrimeGap.hasDensity_zero_of_geometric
  have ht : Tendsto (fun t : ℕ => 2*t) atTop atTop :=
    tendsto_atTop_mono (fun t => by omega : ∀ t : ℕ, t ≤ 2*t) tendsto_id
  have hh := comparable_density_dyadic.comp ht
  convert hh using 1
  ext t
  have he : (2:ℕ)^(2*t)=4^t := by rw [pow_mul]; norm_num
  change comparable.partialDensity Set.univ (4^t) = comparable.partialDensity Set.univ (2^(2*t))
  rw [he]

end Erdos371GrowingRatioSeparation

#print axioms Erdos371GrowingRatioSeparation.growing_ratio_count_tendsto
#print axioms Erdos371GrowingRatioSeparation.growing_ratio_hasDensity_zero
#print axioms Erdos371GrowingRatioSeparation.ratio_log_bracket
