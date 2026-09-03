import FormalConjecturesUtil
import Submission.CofactorSieve

/-! Summing the sieve over dyadic cofactor boxes by explicit scale bands. -/

namespace Erdos371SieveScaleBands

open Finset Filter Erdos371CofactorSieve Erdos371SieveParameters
open scoped Topology

/-- Binary logarithm of the sieve length threshold. -/
def exponent (k : ℕ) : ℕ := 12 * depth k * 2^k

lemma threshold_eq_pow (k : ℕ) : threshold k = 2^(exponent k) := by
  unfold threshold cutoff exponent
  rw [← pow_mul]
  congr 1
  ring

lemma index_le_exponent (k : ℕ) : k ≤ exponent k := by
  have hd := index_le_depth k
  have hp := Nat.one_le_two_pow (n := k)
  unfold exponent
  nlinarith

lemma exponent_pos (k : ℕ) : 0 < exponent k := by
  unfold exponent
  exact Nat.mul_pos (by have := depth_pos k; omega) (by positivity)

/-- Indices of cofactor boxes whose progression length lies in band `k`. -/
def band (k t : ℕ) : Finset ℕ :=
  (Finset.range (t+1)).filter fun j => 2*j+exponent k ≤ t ∧ t < 2*j+exponent (k+1)

lemma exists_band {K t j : ℕ} (hK : 2*j+exponent K ≤ t) :
    ∃ k ∈ Finset.Ico K (t+1), j ∈ band k t := by
  let s := t-2*j
  let k := Nat.findGreatest (fun k => exponent k ≤ s) t
  have hKs : exponent K ≤ s := by dsimp [s]; omega
  have hKt : K ≤ t := by have := index_le_exponent K; omega
  have hKk : K ≤ k := Nat.le_findGreatest hKt hKs
  have hkt : k ≤ t := Nat.findGreatest_le t
  have hspec : exponent k ≤ s := Nat.findGreatest_spec (P := fun k => exponent k ≤ s) hKt hKs
  have hnext : s < exponent (k+1) := by
    by_cases hkn : k+1 ≤ t
    · have hh := Nat.findGreatest_is_greatest (P := fun k => exponent k ≤ s)
        (by dsimp [k]; omega : k<k+1) hkn
      omega
    · have hh := index_le_exponent (k+1)
      dsimp [s]
      omega
  refine ⟨k, Finset.mem_Ico.mpr ⟨hKk,by omega⟩, Finset.mem_filter.mpr ?_⟩
  refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
  dsimp [s] at hspec hnext
  omega

lemma band_card_le (k t : ℕ) : (band k t).card ≤ exponent (k+1) := by
  calc
    _ ≤ (Finset.range (exponent (k+1))).card := by
      apply Finset.card_le_card_of_injOn (fun j => t-2*j)
      · intro j hj
        change j ∈ band k t at hj
        have hh := (Finset.mem_filter.mp hj).2
        apply Finset.mem_range.mpr
        change t-2*j < exponent (k+1)
        omega
      · intro i hi j hj he
        change i ∈ band k t at hi
        change j ∈ band k t at hj
        have hi := (Finset.mem_filter.mp hi).2.1
        have hj := (Finset.mem_filter.mp hj).2.1
        change t-2*i=t-2*j at he
        omega
    _ = _ := Finset.card_range _

noncomputable def coefficient (k : ℕ) : ℝ := (exponent (k+1):ℝ)/(4:ℝ)^k
noncomputable def tail (K : ℕ) : ℝ := ∑' j : ℕ, coefficient (j+K)

lemma coefficient_nonneg (k : ℕ) : 0 ≤ coefficient k := by unfold coefficient; positivity

lemma coefficient_eq (k : ℕ) : coefficient k = 6144*((k:ℝ)+2)^2*(1/2:ℝ)^k := by
  unfold coefficient exponent depth
  push_cast
  rw [pow_succ]
  have h4 : (4:ℝ)^k = (2:ℝ)^k*(2:ℝ)^k := by rw [← mul_pow]; norm_num
  rw [h4, div_pow]
  field_simp
  ring

lemma coefficient_summable : Summable coefficient := by
  have h0 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0 (r := 1/2) (by norm_num)
  have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := 1/2) (by norm_num)
  have h2 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 (r := 1/2) (by norm_num)
  have hh := ((h2.add (h1.mul_left 4)).add (h0.mul_left 4)).mul_left 6144
  apply hh.congr
  intro k
  rw [coefficient_eq]
  ring

lemma tail_nonneg (K : ℕ) : 0 ≤ tail K := tsum_nonneg (fun j => coefficient_nonneg _)

lemma tail_tendsto_zero : Tendsto tail atTop (𝓝 0) := tendsto_sum_nat_add coefficient

lemma coefficient_sum_le_tail (K T : ℕ) :
    (∑ k ∈ Finset.Ico K T, coefficient k) ≤ tail K := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hh := (summable_nat_add_iff K).mpr coefficient_summable
  have hsum := sum_le_hasSum (Finset.range (T-K)) (fun j _ => coefficient_nonneg (j+K)) hh.hasSum
  simpa [tail, Nat.add_comm] using hsum

noncomputable def scaleCover (K C t : ℕ) : Finset ℕ :=
  (Finset.Ico K (t+1)).biUnion fun k =>
    (band k t).biUnion fun j => cofactorBox k (2^j) (C*2^j) (2^t)

lemma box_bound_of_mem_band {j k t : ℕ} (hj : j ∈ band k t) (C : ℕ) :
    (cofactorBox k (2^j) (C*2^j) (2^t)).card ≤
      12*(Real.exp 1)^2*(C:ℝ)^2*(2:ℝ)^t/(4:ℝ)^k := by
  have hh := (Finset.mem_filter.mp hj).2.1
  have hpow : 2^j*2^j ≤ (2:ℕ)^t := by
    rw [← pow_add]
    apply Nat.pow_le_pow_right (by decide)
    omega
  have hmul : threshold k*(2^j*2^j) ≤ (2:ℕ)^t := by
    rw [threshold_eq_pow, ← pow_add, ← pow_add]
    apply Nat.pow_le_pow_right (by decide)
    omega
  have hdiv := (Nat.le_div_iff_mul_le (by positivity : 0<2^j*2^j)).mpr hmul
  have hlarge : threshold k ≤ 2^t/(2^j*2^j)+1 := by omega
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    cofactorBox_scaled_bound (by positivity) hpow k C hlarge

/-- All large-length scale bands have a total bound with a summable tail. -/
theorem scaleCover_card_bound (K C t : ℕ) :
    (scaleCover K C t).card ≤
      12*(Real.exp 1)^2*(C:ℝ)^2*(2:ℝ)^t * tail K := by
  have hc : (scaleCover K C t).card ≤
      ∑ k ∈ Finset.Ico K (t+1), ∑ j ∈ band k t,
        (cofactorBox k (2^j) (C*2^j) (2^t)).card :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun _ _ => Finset.card_biUnion_le))
  let B : ℝ := 12*(Real.exp 1)^2*(C:ℝ)^2*(2:ℝ)^t
  have hB : 0 ≤ B := by dsimp [B]; positivity
  calc
    _ ≤ ∑ k ∈ Finset.Ico K (t+1), ∑ j ∈ band k t,
        ((cofactorBox k (2^j) (C*2^j) (2^t)).card:ℝ) := by exact_mod_cast hc
    _ ≤ ∑ k ∈ Finset.Ico K (t+1), ∑ _j ∈ band k t, B/(4:ℝ)^k := by
      exact Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun _ hj => box_bound_of_mem_band hj C))
    _ ≤ ∑ k ∈ Finset.Ico K (t+1), (exponent (k+1):ℝ)*(B/(4:ℝ)^k) := by
      apply Finset.sum_le_sum
      intro k hk
      simp only [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (band_card_le k t))
      positivity
    _ = B * (∑ k ∈ Finset.Ico K (t+1), coefficient k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      unfold coefficient
      ring
    _ ≤ B * tail K := mul_le_mul_of_nonneg_left (coefficient_sum_le_tail K (t+1)) hB

end Erdos371SieveScaleBands

#print axioms Erdos371SieveScaleBands.coefficient_summable
#print axioms Erdos371SieveScaleBands.scaleCover_card_bound
