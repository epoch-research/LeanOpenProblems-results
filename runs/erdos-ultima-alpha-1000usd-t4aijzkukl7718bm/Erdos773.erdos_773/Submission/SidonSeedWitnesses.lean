import Submission.SidonPartitionScales
import Submission.BernoulliCarrier

/-! Weighted witnesses for large Sidon subsets in Bernoulli integer sets.
This is a generic integer-set counting argument, not an upper bound for squares. -/
namespace Erdos773.SidonSeedWitnesses
open Finset SidonPartitionFunction SidonDifferenceGraph SidonPartitionScales BernoulliCarrier
set_option maxHeartbeats 3000000
noncomputable section
attribute [local instance] Classical.propDecidable

def host (n : ℕ) : Finset ℕ := Icc 1 (n^40)
def seeds (n : ℕ) : Finset (Finset ℕ) := ((host n).powersetCard (n^14)).filter (fun T => IsSidon (T:Set ℕ))
def density (n : ℕ) : ℝ := 1/(4*(n:ℝ)^24)
def witnesses (n : ℕ) (B : Finset ℕ) : ℝ :=
  ∑ T ∈ seeds n, ∑ I ∈ indSets (Adj T) (host n), if I ⊆ B then (n:ℝ)^I.card else 0
def penalty (n : ℕ) (B : Finset ℕ) : ℝ := witnesses n B / (n:ℝ)^(n^15-n^14)

lemma host_card (n : ℕ) : (host n).card=n^40 := by simp [host]
lemma mem_seeds {n : ℕ} {T : Finset ℕ} :
    T ∈ seeds n ↔ T ⊆ host n ∧ T.card=n^14 ∧ IsSidon (T:Set ℕ) := by
  simp only [seeds,mem_filter,mem_powersetCard,and_assoc]
lemma witnesses_nonneg (n : ℕ) (B : Finset ℕ) : 0 ≤ witnesses n B := by
  apply sum_nonneg
  intro T hT
  apply sum_nonneg
  intro I hI
  split_ifs <;> positivity
lemma penalty_nonneg (n : ℕ) (B : Finset ℕ) : 0 ≤ penalty n B :=
  div_nonneg (witnesses_nonneg n B) (by positivity)

/-- Every large Sidon set contributes at least one full unit of penalty. -/
lemma penalty_large {n : ℕ} (hn : 1 ≤ n) {B S : Finset ℕ} (hB : B ⊆ host n)
    (hSB : S ⊆ B) (hS : IsSidon (S:Set ℕ)) (hcard : n^15 ≤ S.card) :
    1 ≤ penalty n B := by
  have htk : n^14 ≤ n^15 := Nat.pow_le_pow_right hn (by omega)
  obtain ⟨T,hTS,hTcard⟩ := exists_subset_card_eq (htk.trans hcard)
  have hT : T ∈ seeds n := mem_seeds.mpr ⟨hTS.trans (hSB.trans hB),hTcard,
    fun a ha b hb c hc d hd he => hS a (hTS ha) b (hTS hb) c (hTS hc) d (hTS hd) he⟩
  have hI : S\T ∈ indSets (Adj T) (host n) := mem_indSets.mpr
    ⟨sdiff_subset.trans (hSB.trans hB),remainder_independent hS hTS⟩
  have hnn : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hsize : n^15-n^14 ≤ (S\T).card := by rw [card_sdiff_of_subset hTS,hTcard]; omega
  have hp := pow_le_pow_right₀ hnn hsize
  have hin := single_le_sum (s := indSets (Adj T) (host n))
    (f := fun I => if I ⊆ B then (n:ℝ)^I.card else 0)
    (fun I hI => by dsimp only; split_ifs <;> positivity) hI
  dsimp only at hin
  rw [if_pos (show S\T ⊆ B from sdiff_subset.trans hSB)] at hin
  have hout := single_le_sum (s := seeds n)
    (f := fun U => ∑ I ∈ indSets (Adj U) (host n), if I ⊆ B then (n:ℝ)^I.card else 0)
    (fun U hU => sum_nonneg (fun I hI => by split_ifs <;> positivity)) hT
  have hh := hp.trans (hin.trans hout)
  unfold penalty
  exact (one_le_div (by positivity)).mpr hh

lemma seeds_card (n : ℕ) : (seeds n).card ≤ (n^40)^(n^14) := by
  exact card_filter_le _ _ |>.trans (by rw [card_powersetCard,host_card]; exact Nat.choose_le_pow _ _)

lemma weighted_witnesses (n : ℕ) :
    (∑ f : host n → Bool, trialWeight (density n) f * witnesses n (sample (host n) f)) =
      ∑ T ∈ seeds n, Z (Adj T) (host n) (fugacity n) := by
  have he : density n*(n:ℝ)=fugacity n := by
    by_cases hn : n=0
    · simp [hn,density,fugacity]
    · have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn
      unfold density fugacity
      field_simp
  unfold witnesses
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro T hT
  simpa only [mul_sum,he,Z] using weighted_family (host n)
    (indSets (Adj T) (host n)) (fun I hI => (mem_indSets.mp hI).1) (density n) (n:ℝ)

lemma expected_penalty_bound {n : ℕ} (hn : 1000 ≤ n) :
    (∑ f : host n → Bool, trialWeight (density n) f * penalty n (sample (host n) f)) ≤
      (n:ℝ)^(40*n^14)*Real.exp ((5/4:ℝ)*(n:ℝ)^15)/(n:ℝ)^(n^15-n^14) := by
  unfold penalty
  simp_rw [← mul_div_assoc]
  rw [← sum_div,weighted_witnesses]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ ∑ _T ∈ seeds n, Real.exp ((5/4:ℝ)*(n:ℝ)^15) := by
      apply sum_le_sum
      intro T hT
      obtain ⟨hTm,hTc,hTs⟩ := mem_seeds.mp hT
      exact seed_partition_bound hn hTs hTm hTc
    _ = (seeds n).card*Real.exp ((5/4:ℝ)*(n:ℝ)^15) := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      have hh : ((seeds n).card:ℝ) ≤ ((n:ℝ)^40)^(n^14) := by exact_mod_cast seeds_card n
      simpa only [pow_mul] using hh

lemma expected_penalty_small {n : ℕ} (hn : 1000 ≤ n) (hlog : 5 ≤ Real.log (n:ℝ)) :
    (∑ f : host n → Bool, trialWeight (density n) f * penalty n (sample (host n) f)) ≤
      Real.exp (-(n:ℝ)^15) := by
  have hnR : (1000:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith only [hnR]
  have htk : n^14 ≤ n^15 := Nat.pow_le_pow_right (by omega) (by omega)
  have hp (a : ℕ) : (n:ℝ)^a=Real.exp ((a:ℝ)*Real.log (n:ℝ)) := by
    rw [Real.exp_nat_mul,Real.exp_log hn0]
  apply (expected_penalty_bound hn).trans
  rw [hp (40*n^14),hp (n^15-n^14),← Real.exp_add,← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  rw [Nat.cast_sub htk]
  push_cast
  have ht : 41*(n:ℝ)^14 ≤ (n:ℝ)^15/4 := by
    have hh := mul_nonneg (show (0:ℝ) ≤ (n:ℝ)-164 by linarith only [hnR]) (pow_nonneg hn0.le 14)
    nlinarith only [hh]
  have hh := mul_le_mul_of_nonneg_right ht (show 0 ≤ Real.log (n:ℝ) by linarith only [hlog])
  have hk := mul_le_mul_of_nonneg_left hlog (pow_nonneg hn0.le 15)
  nlinarith only [hh,hk,pow_nonneg hn0.le 15]

lemma exponential_penalty_budget {n : ℕ} (hn : 2 ≤ n) :
    (n:ℝ)^40*Real.exp (-(n:ℝ)^15) ≤ 1 := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith only [hnR]
  have hh := Real.pow_div_factorial_le_exp ((n:ℝ)^15) (by positivity) 3
  norm_num at hh
  have h5 : (6:ℝ) ≤ (n:ℝ)^5 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hnR 5
    norm_num at h
    linarith only [h]
  have hm := mul_le_mul_of_nonneg_left h5 (pow_nonneg hn0.le 40)
  have hb : (n:ℝ)^40 ≤ Real.exp ((n:ℝ)^15) := by nlinarith only [hh,hm]
  rw [Real.exp_neg]
  exact (mul_inv_le_iff₀ (Real.exp_pos _)).mpr (by simpa only [one_mul] using hb)

#print axioms expected_penalty_small
#print axioms exponential_penalty_budget
#print axioms penalty_large
#print axioms weighted_witnesses
#print axioms expected_penalty_bound
end
end Erdos773.SidonSeedWitnesses
