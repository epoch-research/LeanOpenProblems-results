import FormalConjecturesUtil
import Submission.SupercriticalUniformTail

/-! Uniform control of the large-multiplicity contribution. This does not
assert cancellation of the signed supercritical-pair sum. -/

namespace Erdos371SupercriticalUniformIntegrability

open Finset Filter Erdos371PrimeDiscrepancy Erdos371SupercriticalPrimePairs
open Erdos371SupercriticalMultiplicityTail Erdos371SupercriticalUniformTail
open scoped Topology

noncomputable def tailMean (k N : ℕ) : ℝ :=
  (∑ n ∈ range N, if 2^k ≤ Erdos371SupercriticalPrimePairs.multiplicity n
    then (Erdos371SupercriticalPrimePairs.multiplicity n:ℝ) else 0)/(N:ℝ)

lemma layer_bound {m k J : ℕ} (hJ : Nat.log 2 m<J) :
    (if 2^k ≤ m then (m:ℝ) else 0) ≤
      ∑ j ∈ Ico k J, (2:ℝ)^(j+1)*(if 2^j ≤ m then 1 else 0) := by
  by_cases hm : 2^k ≤ m
  · rw [if_pos hm]
    have hm0 : m≠0 := by
      have hpow : 0<2^k := by positivity
      omega
    have hk : k ≤ Nat.log 2 m := Nat.le_log_of_pow_le (by omega) hm
    have hmem : Nat.log 2 m∈Ico k J := mem_Ico.mpr ⟨hk,hJ⟩
    have hh := single_le_sum (s := Ico k J)
      (f := fun j => (2:ℝ)^(j+1)*(if 2^j ≤ m then 1 else 0))
      (fun j _ => by positivity) hmem
    dsimp only at hh
    rw [if_pos (Nat.pow_log_le_self 2 hm0),mul_one] at hh
    have hb : (m:ℝ) ≤ (2:ℝ)^(Nat.log 2 m+1) := by
      exact_mod_cast (Nat.lt_pow_succ_log_self (by omega : 1<2) m).le
    exact hb.trans hh
  · rw [if_neg hm]
    exact sum_nonneg fun j _ => by positivity

lemma finite_layer_bound (k N : ℕ) : ∃ J : ℕ,
    tailMean k N ≤ ∑ j ∈ Ico k J,
      (2:ℝ)^(j+1)*((tailCount (2^j) N:ℝ)/(N:ℝ)) := by
  let J := (range N).sup (fun n => Nat.log 2 (Erdos371SupercriticalPrimePairs.multiplicity n)+1)
  have hs : (∑ n ∈ range N, if 2^k ≤ Erdos371SupercriticalPrimePairs.multiplicity n
      then (Erdos371SupercriticalPrimePairs.multiplicity n:ℝ) else 0) ≤
      ∑ n ∈ range N, ∑ j ∈ Ico k J,
        (2:ℝ)^(j+1)*(if 2^j ≤ Erdos371SupercriticalPrimePairs.multiplicity n then 1 else 0) := by
    apply sum_le_sum
    intro n hn
    apply layer_bound
    have hh := le_sup (f := fun n => Nat.log 2 (Erdos371SupercriticalPrimePairs.multiplicity n)+1) hn
    change Nat.log 2 (Erdos371SupercriticalPrimePairs.multiplicity n)+1 ≤ J at hh
    omega
  rw [sum_comm] at hs
  have he (j : ℕ) : (∑ n ∈ range N,
      (2:ℝ)^(j+1)*(if 2^j ≤ Erdos371SupercriticalPrimePairs.multiplicity n then 1 else 0)) =
      (2:ℝ)^(j+1)*(tailCount (2^j) N:ℝ) := by
    rw [← mul_sum]
    simp [tailCount]
  simp_rw [he] at hs
  refine ⟨J,?_⟩
  have hh := div_le_div_of_nonneg_right hs (Nat.cast_nonneg (α := ℝ) N)
  simpa only [tailMean,sum_div,mul_div_assoc] using hh

noncomputable def envelope (k : ℕ) : ℝ :=
  (2*(k:ℝ)^2+8*k+12)/(2:ℝ)^k

lemma envelope_nonneg (k : ℕ) : 0 ≤ envelope k := by unfold envelope; positivity

lemma envelope_difference (j : ℕ) :
    envelope j-envelope (j+1)=(j+1:ℕ)^2/(2:ℝ)^j := by
  unfold envelope
  push_cast
  rw [pow_succ]
  have hp : (2:ℝ)^j≠0 := by positivity
  field_simp
  ring

lemma envelope_sum_bound (k J : ℕ) :
    (∑ j ∈ Ico k J, ((j+1:ℕ):ℝ)^2/(2:ℝ)^j) ≤ envelope k := by
  by_cases h : k ≤ J
  · have he : (∑ j ∈ Ico k J, ((j+1:ℕ):ℝ)^2/(2:ℝ)^j)=envelope k-envelope J := by
      simp_rw [← envelope_difference]
      have hh := sum_Ico_sub (fun j => -envelope j) h
      simpa only [neg_sub_neg] using hh
    rw [he]
    linarith [envelope_nonneg J]
  · have he : Ico k J=∅ := Ico_eq_empty_of_le (by omega)
    rw [he,sum_empty]
    exact envelope_nonneg k

lemma layer_weight (j : ℕ) :
    (2:ℝ)^(j+1)*(512*(j+1:ℕ)^2/(2:ℝ)^(2*j))=
      1024*((j+1:ℕ):ℝ)^2/(2:ℝ)^j := by
  have he : 2*j=j+j := by omega
  rw [he,pow_add,pow_succ]
  have hp : (2:ℝ)^j≠0 := by positivity
  field_simp
  ring

/-- A quantitative bound on the contribution of all large multiplicities,
not merely on the proportion of inputs where they occur. -/
theorem tailMean_bound {k : ℕ} (hk : 2 ≤ k) (N : ℕ) :
    tailMean k N ≤ 1024*envelope k := by
  obtain ⟨J,hJ⟩ := finite_layer_bound k N
  calc
    _ ≤ _ := hJ
    _ ≤ ∑ j ∈ Ico k J, (2:ℝ)^(j+1)*(512*(j+1:ℕ)^2/(2:ℝ)^(2*j)) := by
      apply sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (uniform_tail_bound (hk.trans (mem_Ico.mp hj).1) N)
        (by positivity)
    _ = 1024*(∑ j ∈ Ico k J, ((j+1:ℕ):ℝ)^2/(2:ℝ)^j) := by
      simp_rw [layer_weight]
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (envelope_sum_bound k J) (by norm_num)

lemma envelope_tendsto_zero : Tendsto envelope atTop (𝓝 0) := by
  have h2 := (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2
    (r := 1/2) (by norm_num)).tendsto_atTop_zero
  have h1 := (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
    (r := 1/2) (by norm_num)).tendsto_atTop_zero
  have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)<1)
  have hh := ((h2.const_mul 2).add (h1.const_mul 8)).add (h0.const_mul 12)
  simp only [mul_zero,add_zero] at hh
  apply hh.congr
  intro k
  simp only [envelope,pow_one,div_eq_mul_inv,one_mul,← inv_pow]
  ring

/-- Explicit uniform integrability of the finite empirical multiplicities. -/
theorem multiplicity_uniform_integrability (ε : ℝ) (hε : 0<ε) :
    ∃ k : ℕ, 2 ≤ k ∧ ∀ N : ℕ, tailMean k N<ε := by
  have ht := envelope_tendsto_zero.const_mul 1024
  simp only [mul_zero] at ht
  obtain ⟨k,hk,hsmall⟩ := ((eventually_ge_atTop 2).and
    (ht.eventually (gt_mem_nhds hε))).exists
  exact ⟨k,hk,fun N => (tailMean_bound hk N).trans_lt hsmall⟩

noncomputable def truncatedSignedPairs (k n : ℕ) : ℤ :=
  if Erdos371SupercriticalPrimePairs.multiplicity n<2^k then signedPairs n else 0

lemma truncated_error (k n : ℕ) :
    |(signedPairs n:ℝ)-(truncatedSignedPairs k n:ℝ)|=
      if 2^k ≤ Erdos371SupercriticalPrimePairs.multiplicity n
      then (Erdos371SupercriticalPrimePairs.multiplicity n:ℝ) else 0 := by
  have hs : |(sign n:ℝ)|=1 := by unfold sign; split_ifs <;> norm_num
  by_cases hm : Erdos371SupercriticalPrimePairs.multiplicity n<2^k
  · simp [truncatedSignedPairs,hm,show ¬2^k ≤ Erdos371SupercriticalPrimePairs.multiplicity n by omega]
  · rw [truncatedSignedPairs,if_neg hm]
    simp only [Int.cast_zero,sub_zero,signedPairs_eq,Int.cast_mul,Int.cast_natCast,
      abs_mul,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _),hs,mul_one,if_pos (by omega : 2^k ≤ Erdos371SupercriticalPrimePairs.multiplicity n)]

/-- Large-multiplicity truncation is uniformly harmless for the signed mean.
Cancellation of the bounded-multiplicity mean is still a separate problem. -/
theorem signed_truncation_bound {k : ℕ} (hk : 2 ≤ k) (N : ℕ) :
    |(∑ n ∈ range N, ((signedPairs n:ℝ)-(truncatedSignedPairs k n:ℝ)))/(N:ℝ)| ≤
      1024*envelope k := by
  calc
    _ = |∑ n ∈ range N, ((signedPairs n:ℝ)-(truncatedSignedPairs k n:ℝ))|/(N:ℝ) := by
      rw [abs_div,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
    _ ≤ (∑ n ∈ range N, |(signedPairs n:ℝ)-(truncatedSignedPairs k n:ℝ)|)/(N:ℝ) :=
      div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (Nat.cast_nonneg N)
    _ = tailMean k N := by simp only [truncated_error,tailMean]
    _ ≤ _ := tailMean_bound hk N

end Erdos371SupercriticalUniformIntegrability

#print axioms Erdos371SupercriticalUniformIntegrability.tailMean_bound
#print axioms Erdos371SupercriticalUniformIntegrability.multiplicity_uniform_integrability
#print axioms Erdos371SupercriticalUniformIntegrability.signed_truncation_bound
