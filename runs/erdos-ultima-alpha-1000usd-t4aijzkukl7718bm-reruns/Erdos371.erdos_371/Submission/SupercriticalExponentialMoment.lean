import FormalConjecturesUtil
import Submission.SupercriticalExponentialTail

/-! A uniform exponential moment of the supercritical-pair multiplicity.
No signed cancellation is asserted. -/

namespace Erdos371SupercriticalExponentialMoment

open Finset Erdos371SupercriticalMultiplicityTail Erdos371SupercriticalExponentialTail

noncomputable def exponentialMean (N : ℕ) : ℝ :=
  (∑ n ∈ range N, (2:ℝ)^(Erdos371SupercriticalPrimePairs.multiplicity n/32))/(N:ℝ)

lemma exp_layer_bound {m J : ℕ} (hJ : m/32 ≤ J) :
    (2:ℝ)^(m/32) ≤ 4+
      ∑ j ∈ Ico 2 J, (2:ℝ)^(j+1)*(if 32*(j+1) ≤ m then 1 else 0) := by
  have hs : (0:ℝ) ≤ ∑ j ∈ Ico 2 J,
      (2:ℝ)^(j+1)*(if 32*(j+1) ≤ m then 1 else 0) := by
    exact sum_nonneg fun j _ => by positivity
  by_cases hm : m/32 ≤ 2
  · have hh : (2:ℝ)^(m/32) ≤ 4 := by
      have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hm
      norm_num at hh
      exact hh
    linarith
  · have hu : 3 ≤ m/32 := by omega
    have he : m/32-1+1=m/32 := by omega
    have hmem : m/32-1∈Ico 2 J := mem_Ico.mpr ⟨by omega,by omega⟩
    have hh := single_le_sum (s := Ico 2 J)
      (f := fun j => (2:ℝ)^(j+1)*(if 32*(j+1) ≤ m then 1 else 0))
      (fun j _ => by positivity) hmem
    dsimp only at hh
    have hd : 32*(m/32) ≤ m := Nat.mul_div_le m 32
    rw [he,if_pos hd,mul_one] at hh
    linarith

noncomputable def linearEnvelope (k : ℕ) : ℝ := (2*(k:ℝ)+4)/(2:ℝ)^k

lemma linearEnvelope_nonneg (k : ℕ) : 0 ≤ linearEnvelope k := by
  unfold linearEnvelope
  positivity

lemma linearEnvelope_difference (j : ℕ) :
    linearEnvelope j-linearEnvelope (j+1)=(j+1:ℕ)/(2:ℝ)^j := by
  unfold linearEnvelope
  push_cast
  rw [pow_succ]
  have hp : (2:ℝ)^j≠0 := by positivity
  field_simp
  ring

lemma linear_sum_bound (J : ℕ) :
    (∑ j ∈ Ico 2 J, ((j+1:ℕ):ℝ)/(2:ℝ)^j) ≤ 2 := by
  by_cases h : 2 ≤ J
  · have he : (∑ j ∈ Ico 2 J, ((j+1:ℕ):ℝ)/(2:ℝ)^j)=
        linearEnvelope 2-linearEnvelope J := by
      simp_rw [← linearEnvelope_difference]
      have hh := sum_Ico_sub (fun j => -linearEnvelope j) h
      simpa only [neg_sub_neg] using hh
    rw [he]
    have h2 : linearEnvelope 2=2 := by norm_num [linearEnvelope]
    rw [h2]
    linarith [linearEnvelope_nonneg J]
  · have he : Ico 2 J=∅ := Ico_eq_empty_of_le (by omega)
    simp [he]

lemma exp_layer_weight (j : ℕ) :
    (2:ℝ)^(j+1)*(128*(j+1:ℕ)/(2:ℝ)^(2*j))=
      256*((j+1:ℕ):ℝ)/(2:ℝ)^j := by
  have he : 2*j=j+j := by omega
  rw [he,pow_add,pow_succ]
  have hp : (2:ℝ)^j≠0 := by positivity
  field_simp
  ring

/-- A single constant bounds the exponential moment in every empirical
prefix, including prefixes too short for asymptotic sieve estimates. -/
theorem exponentialMean_bound (N : ℕ) : exponentialMean N ≤ 516 := by
  by_cases hN : N=0
  · subst N
    norm_num [exponentialMean]
  have hNr : (0:ℝ)<N := by exact_mod_cast (Nat.pos_of_ne_zero hN)
  let J := (range N).sup (fun n => Erdos371SupercriticalPrimePairs.multiplicity n/32)
  have hs : (∑ n ∈ range N, (2:ℝ)^(Erdos371SupercriticalPrimePairs.multiplicity n/32)) ≤
      (N:ℝ)*4+∑ j ∈ Ico 2 J, (2:ℝ)^(j+1)*(tailCount (32*(j+1)) N:ℝ) := by
    have hh := sum_le_sum (s := range N) (fun n hn => exp_layer_bound
      (show Erdos371SupercriticalPrimePairs.multiplicity n/32 ≤ J from le_sup (f := fun n => Erdos371SupercriticalPrimePairs.multiplicity n/32) hn))
    rw [sum_add_distrib,sum_const,card_range,nsmul_eq_mul,sum_comm] at hh
    have he (j : ℕ) : (∑ n ∈ range N,
        (2:ℝ)^(j+1)*(if 32*(j+1) ≤ Erdos371SupercriticalPrimePairs.multiplicity n then 1 else 0)) =
        (2:ℝ)^(j+1)*(tailCount (32*(j+1)) N:ℝ) := by
      rw [← mul_sum]
      simp [tailCount]
    simpa only [he] using hh
  have hmean : exponentialMean N ≤ 4+
      ∑ j ∈ Ico 2 J, (2:ℝ)^(j+1)*((tailCount (32*(j+1)) N:ℝ)/(N:ℝ)) := by
    have hh := div_le_div_of_nonneg_right hs hNr.le
    simpa only [exponentialMean,add_div,sum_div,mul_div_assoc,
      mul_div_cancel_left₀ (4:ℝ) hNr.ne'] using hh
  calc
    _ ≤ _ := hmean
    _ ≤ 4+∑ j ∈ Ico 2 J, (2:ℝ)^(j+1)*(128*(j+1:ℕ)/(2:ℝ)^(2*j)) := by
      apply add_le_add le_rfl
      apply sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (uniform_exp_tail (mem_Ico.mp hj).1 N) (by positivity)
    _ = 4+256*(∑ j ∈ Ico 2 J, ((j+1:ℕ):ℝ)/(2:ℝ)^j) := by
      simp_rw [exp_layer_weight]
      rw [mul_sum]
      congr 1
      apply sum_congr rfl
      intro j _
      ring
    _ ≤ 4+256*2 := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (linear_sum_bound J) (by norm_num : (0:ℝ) ≤ 256))
    _ = _ := by norm_num

end Erdos371SupercriticalExponentialMoment

#print axioms Erdos371SupercriticalExponentialMoment.exponentialMean_bound
