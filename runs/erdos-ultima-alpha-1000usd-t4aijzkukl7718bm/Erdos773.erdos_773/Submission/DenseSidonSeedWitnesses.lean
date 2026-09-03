import Submission.DenseSidonPartitionScales
import Submission.BernoulliCarrier

/-! Weighted witnesses for large Sidon subsets in Bernoulli integer sets.
This is a generic integer-set counting argument, not an upper bound for squares. -/
namespace Erdos773.DenseSidonSeedWitnesses
open Finset SidonPartitionFunction SidonDifferenceGraph DenseSidonPartitionScales BernoulliCarrier
set_option maxHeartbeats 3000000
noncomputable section
attribute [local instance] Classical.propDecidable

def host (R : ℕ) : Finset ℕ := Icc 1 (R^100)
def seeds (R : ℕ) : Finset (Finset ℕ) := ((host R).powersetCard (R^36)).filter (fun T => IsSidon (T:Set ℕ))
def density (n R : ℕ) : ℝ := 1/(4*(R:ℝ)^50*n)
def witnesses (n R : ℕ) (B : Finset ℕ) : ℝ :=
  ∑ T ∈ seeds R, ∑ I ∈ indSets (Adj T) (host R), if I ⊆ B then (n:ℝ)^I.card else 0
def penalty (n R : ℕ) (B : Finset ℕ) : ℝ := witnesses n R B / (n:ℝ)^(R^40-R^36)

lemma host_card (R : ℕ) : (host R).card=R^100 := by simp [host]
lemma mem_seeds {R : ℕ} {T : Finset ℕ} :
    T ∈ seeds R ↔ T ⊆ host R ∧ T.card=R^36 ∧ IsSidon (T:Set ℕ) := by
  simp only [seeds,mem_filter,mem_powersetCard,and_assoc]
lemma witnesses_nonneg (n R : ℕ) (B : Finset ℕ) : 0 ≤ witnesses n R B := by
  apply sum_nonneg
  intro T hT
  apply sum_nonneg
  intro I hI
  split_ifs <;> positivity
lemma penalty_nonneg (n R : ℕ) (B : Finset ℕ) : 0 ≤ penalty n R B :=
  div_nonneg (witnesses_nonneg n R B) (by positivity)

/-- Every large Sidon set contributes at least one full unit of penalty. -/
lemma penalty_large {n R : ℕ} (hn : 1 ≤ n) (hR : 1 ≤ R) {B S : Finset ℕ} (hB : B ⊆ host R)
    (hSB : S ⊆ B) (hS : IsSidon (S:Set ℕ)) (hcard : R^40 ≤ S.card) :
    1 ≤ penalty n R B := by
  have htk : R^36 ≤ R^40 := Nat.pow_le_pow_right hR (by omega)
  obtain ⟨T,hTS,hTcard⟩ := exists_subset_card_eq (htk.trans hcard)
  have hT : T ∈ seeds R := mem_seeds.mpr ⟨hTS.trans (hSB.trans hB),hTcard,
    fun a ha b hb c hc d hd he => hS a (hTS ha) b (hTS hb) c (hTS hc) d (hTS hd) he⟩
  have hI : S\T ∈ indSets (Adj T) (host R) := mem_indSets.mpr
    ⟨sdiff_subset.trans (hSB.trans hB),remainder_independent hS hTS⟩
  have hnn : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hsize : R^40-R^36 ≤ (S\T).card := by rw [card_sdiff_of_subset hTS,hTcard]; omega
  have hp := pow_le_pow_right₀ hnn hsize
  have hin := single_le_sum (s := indSets (Adj T) (host R))
    (f := fun I => if I ⊆ B then (n:ℝ)^I.card else 0)
    (fun I hI => by dsimp only; split_ifs <;> positivity) hI
  dsimp only at hin
  rw [if_pos (show S\T ⊆ B from sdiff_subset.trans hSB)] at hin
  have hout := single_le_sum (s := seeds R)
    (f := fun U => ∑ I ∈ indSets (Adj U) (host R), if I ⊆ B then (n:ℝ)^I.card else 0)
    (fun U hU => sum_nonneg (fun I hI => by split_ifs <;> positivity)) hT
  have hh := hp.trans (hin.trans hout)
  unfold penalty
  exact (one_le_div (by positivity)).mpr hh

lemma seeds_card (R : ℕ) : (seeds R).card ≤ (R^100)^(R^36) := by
  exact card_filter_le _ _ |>.trans (by rw [card_powersetCard,host_card]; exact Nat.choose_le_pow _ _)

lemma weighted_witnesses {n : ℕ} (hn : 0<n) (R : ℕ) :
    (∑ f : host R → Bool, trialWeight (density n R) f * witnesses n R (sample (host R) f)) =
      ∑ T ∈ seeds R, Z (Adj T) (host R) (fugacity R) := by
  have he : density n R*(n:ℝ)=fugacity R := by
    have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    unfold density fugacity
    field_simp
  unfold witnesses
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro T hT
  simpa only [mul_sum,he,Z] using weighted_family (host R)
    (indSets (Adj T) (host R)) (fun I hI => (mem_indSets.mp hI).1) (density n R) (n:ℝ)

lemma expected_penalty_bound {n R : ℕ} (hn : 0<n) (hR : 1000 ≤ R) :
    (∑ f : host R → Bool, trialWeight (density n R) f * penalty n R (sample (host R) f)) ≤
      (R:ℝ)^(100*R^36)*Real.exp ((5/4:ℝ)*(R:ℝ)^40)/(n:ℝ)^(R^40-R^36) := by
  unfold penalty
  simp_rw [← mul_div_assoc]
  rw [← sum_div,weighted_witnesses hn]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ ∑ _T ∈ seeds R, Real.exp ((5/4:ℝ)*(R:ℝ)^40) := by
      apply sum_le_sum
      intro T hT
      obtain ⟨hTm,hTc,hTs⟩ := mem_seeds.mp hT
      exact seed_partition_bound hR hTs hTm hTc
    _ = (seeds R).card*Real.exp ((5/4:ℝ)*(R:ℝ)^40) := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      have hh : ((seeds R).card:ℝ) ≤ ((R:ℝ)^100)^(R^36) := by exact_mod_cast seeds_card R
      simpa only [pow_mul] using hh

lemma entropy_budget {n R : ℕ} (hR : 1000 ≤ R) (hlog : 5 ≤ Real.log (n:ℝ)) :
    (100*Real.log (R:ℝ)+Real.log (n:ℝ))*(R:ℝ)^36 ≤
      (R:ℝ)^40*Real.log (n:ℝ)/4 := by
  have hRR : (1000:ℝ) ≤ R := by exact_mod_cast hR
  have hR0 : (0:ℝ)<R := by linarith only [hRR]
  have hlogR : Real.log (R:ℝ) ≤ R := by
    have hh := Real.log_le_sub_one_of_pos hR0
    linarith only [hh]
  have h3 : (800:ℝ) ≤ (R:ℝ)^3 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1000) hRR 3
    norm_num at hh
    linarith only [hh]
  have h4 : (8:ℝ) ≤ (R:ℝ)^4 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1000) hRR 4
    norm_num at hh
    linarith only [hh]
  have h3m := mul_le_mul_of_nonneg_right h3 hR0.le
  have hm := mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ Real.log (n:ℝ) by linarith only [hlog])
    (pow_nonneg hR0.le 4)
  have hm' := mul_le_mul_of_nonneg_right h4 (show (0:ℝ) ≤ Real.log (n:ℝ) by linarith only [hlog])
  have hb : 100*Real.log (R:ℝ)+Real.log (n:ℝ) ≤ (R:ℝ)^4*Real.log (n:ℝ)/4 := by
    nlinarith only [hlogR,h3m,hm,hm']
  have hh := mul_le_mul_of_nonneg_right hb (pow_nonneg hR0.le 36)
  nlinarith only [hh]

lemma expected_penalty_small {n R : ℕ} (hn : 0<n) (hR : 1000 ≤ R)
    (hlog : 5 ≤ Real.log (n:ℝ)) :
    (∑ f : host R → Bool, trialWeight (density n R) f * penalty n R (sample (host R) f)) ≤
      Real.exp (-(R:ℝ)^40) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hR0 : (0:ℝ)<R := by exact_mod_cast (show 0<R by omega)
  have htk : R^36 ≤ R^40 := Nat.pow_le_pow_right (by omega) (by omega)
  have hp (a : ℕ) : (n:ℝ)^a=Real.exp ((a:ℝ)*Real.log (n:ℝ)) := by
    rw [Real.exp_nat_mul,Real.exp_log hn0]
  have hpR (a : ℕ) : (R:ℝ)^a=Real.exp ((a:ℝ)*Real.log (R:ℝ)) := by
    rw [Real.exp_nat_mul,Real.exp_log hR0]
  apply (expected_penalty_bound hn hR).trans
  rw [hpR (100*R^36),hp (R^40-R^36),← Real.exp_add,← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  rw [Nat.cast_sub htk]
  push_cast
  have ht := entropy_budget hR hlog
  have hk := mul_le_mul_of_nonneg_left hlog (pow_nonneg hR0.le 40)
  nlinarith only [ht,hk,pow_nonneg hR0.le 40]

lemma exponential_penalty_budget {R : ℕ} (hR : 2 ≤ R) :
    (R:ℝ)^100*Real.exp (-(R:ℝ)^40) ≤ 1 := by
  have hRR : (2:ℝ) ≤ R := by exact_mod_cast hR
  have hR0 : (0:ℝ)<R := by linarith only [hRR]
  have hh := Real.pow_div_factorial_le_exp ((R:ℝ)^40) (by positivity) 3
  norm_num at hh
  have h20 : (6:ℝ) ≤ (R:ℝ)^20 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hRR 20
    norm_num at h
    linarith only [h]
  have hm := mul_le_mul_of_nonneg_left h20 (pow_nonneg hR0.le 100)
  have hb : (R:ℝ)^100 ≤ Real.exp ((R:ℝ)^40) := by nlinarith only [hh,hm]
  rw [Real.exp_neg]
  exact (mul_inv_le_iff₀ (Real.exp_pos _)).mpr (by simpa only [one_mul] using hb)

#print axioms expected_penalty_small
#print axioms exponential_penalty_budget
#print axioms penalty_large
#print axioms weighted_witnesses
#print axioms expected_penalty_bound
end
end Erdos773.DenseSidonSeedWitnesses
