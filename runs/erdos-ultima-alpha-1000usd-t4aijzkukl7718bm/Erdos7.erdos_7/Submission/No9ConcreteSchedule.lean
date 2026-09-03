import Submission.No9Invariant
import Submission.No9FiniteMass
import Submission.CubicBudgetSequence

/-! Concrete caps, losses, and positive masses for any compatible prime sequence. -/
namespace Erdos7No9Certificate
open scoped BigOperators
open Erdos7KilledSieve Erdos7Distortion Erdos7CompressionSieve
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

structure PrimeSchedule {n : ℕ} (p E : Fin n → ℕ) : Prop where
  small_le : smallLength ≤ n
  monotone : StrictMono p
  E_pos : ∀ i,0 < E i
  prefix_stage : ∀ i : Fin n,i.val < prefixLength →
    p i=(prefixControl i.val).p ∧
    (if (prefixControl i.val).p=3 then E i=1 else (prefixControl i.val).R ≤ E i)
  block_stage : ∀ (i : Fin n) (b j : ℕ),b < blockLength → j < (blockControl b).count →
    i.val=blockOffset b+j →
    (blockControl b).lo ≤ p i ∧ p i ≤ (blockControl b).hi ∧ (blockControl b).R ≤ E i
  tail_stage : ∀ i : Fin n,smallLength ≤ i.val → (p i).Prime ∧ 1500000 ≤ p i

def scheduleCap (t : ℕ) : ℚ :=
  if t < prefixLength then ((prefixControl t).A:ℚ)/(prefixControl t).B else 5/4

def scheduleNormalizer {n : ℕ} (p : Fin n → ℕ) (i : Fin n) : ℚ :=
  if i.val < prefixLength then 1/(denominator (prefixControl i.val).p:ℚ) else 1/(p i-1:ℚ)

noncomputable def scheduleLoss {n : ℕ} (p : Fin n → ℕ) (i : Fin n) : ℚ :=
  if i.val < smallLength then smallLoss i.val else Erdos7CubicSieve.sequenceLoss p smallLength finalCubic i
noncomputable def scheduleMass {n : ℕ} (p : Fin n → ℕ) (t : ℕ) : ℚ :=
  smallMass t-Erdos7CubicSieve.sequenceCost p smallLength finalCubic t
noncomputable def scheduleCubic {n : ℕ} (p : Fin n → ℕ) (t : ℕ) : ℚ :=
  Erdos7CubicSieve.sequenceCubic p smallLength finalCubic t

lemma scheduleMass_small {n : ℕ} (p : Fin n → ℕ) (t : ℕ) (ht : t ≤ smallLength) :
    scheduleMass p t=smallMass t := by
  simp only [scheduleMass,Erdos7CubicSieve.sequenceCost_initial p smallLength finalCubic t ht,sub_zero]

lemma scheduleMass_zero {n : ℕ} (p : Fin n → ℕ) : scheduleMass p 0=1 := by
  rw [scheduleMass_small p 0 (Nat.zero_le _),smallMass_zero]

lemma scheduleMass_succ {n : ℕ} (p E : Fin n → ℕ) (hp : PrimeSchedule p E) (i : Fin n) :
    scheduleMass p (i.val+1)=scheduleMass p i.val-scheduleLoss p i := by
  by_cases hi : i.val < smallLength
  · rw [scheduleMass_small p (i.val+1) (by omega),scheduleMass_small p i.val hi.le,smallMass_succ i.val hi]
    simp only [scheduleLoss,if_pos hi]
  · simp only [scheduleMass,smallMass_after i.val (by omega),smallMass_after (i.val+1) (by omega),
      Erdos7CubicSieve.sequenceCost_succ p hp.monotone smallLength finalCubic i (by omega),scheduleLoss,if_neg hi]
    ring

lemma scheduleMass_pos {n : ℕ} (p E : Fin n → ℕ) (hp : PrimeSchedule p E) (t : ℕ) :
    0 < scheduleMass p t := by
  by_cases ht : t ≤ smallLength
  · rw [scheduleMass_small p t ht]
    exact smallMass_pos t
  · have hcost := Erdos7CubicSieve.sequenceCost_bound p smallLength finalCubic finalCubic_nonneg 1500000
      (by norm_num) hp.tail_stage t
    rw [scheduleMass,smallMass_after t (by omega)]
    have hm := finalMargin
    linarith

lemma scheduleCubic_nonneg {n : ℕ} (p E : Fin n → ℕ) (hp : PrimeSchedule p E) (t : ℕ) :
    0 ≤ scheduleCubic p t := by
  apply Erdos7CubicSieve.sequenceCubic_nonneg p smallLength finalCubic finalCubic_nonneg _ t
  intro i hi
  have hh := (hp.tail_stage i hi).2
  omega

lemma primeSchedule_gt_one {n : ℕ} (p E : Fin n → ℕ) (hp : PrimeSchedule p E) (i : Fin n) : 1 < p i := by
  by_cases hi : i.val < prefixLength
  · have hh := (prefix_checked i.val hi).p_three
    rw [(hp.prefix_stage i hi).1]
    omega
  · by_cases ht : i.val < smallLength
    · obtain ⟨b,j,hb,hj,heq⟩ := small_index_block i.val (by omega) ht
      have hs := hp.block_stage i b j hb hj heq
      have hn := (block_checked b hb).analytic.lo_two
      omega
    · have hn := (hp.tail_stage i (by omega)).2
      omega

lemma scheduleCap_one_le (t : ℕ) : 1 ≤ scheduleCap t := by
  unfold scheduleCap
  split_ifs with ht
  · have hh := (prefix_checked t ht).geometry
    exact (one_le_div (by exact_mod_cast hh.B_pos)).mpr (by exact_mod_cast hh.B_le_A)
  · norm_num

lemma scheduleCap_le_prime {n : ℕ} (p E : Fin n → ℕ) (hp : PrimeSchedule p E) (i : Fin n) :
    scheduleCap i.val ≤ p i := by
  unfold scheduleCap
  split_ifs with hi
  · have hh := prefix_checked i.val hi
    rw [(hp.prefix_stage i hi).1]
    exact (div_le_iff₀ (by exact_mod_cast hh.geometry.B_pos)).mpr (by
      exact_mod_cast (hh.cap_le.trans_eq (Nat.mul_comm _ _)))
  · have hn : (2:ℚ) ≤ p i := by exact_mod_cast primeSchedule_gt_one p E hp i
    linarith

lemma scheduleNormalizer_pos {n : ℕ} (p E : Fin n → ℕ) (hp : PrimeSchedule p E) (i : Fin n) :
    0 < scheduleNormalizer p i := by
  unfold scheduleNormalizer
  split_ifs with hi
  · exact div_pos (by norm_num) (by exact_mod_cast (prefix_checked i.val hi).geometry.q_pos)
  · have hn : (2:ℚ) ≤ p i := by exact_mod_cast primeSchedule_gt_one p E hp i
    exact div_pos (by norm_num) (by linarith)

lemma concrete_certificate_schedule {n : ℕ} (p E : Fin n → ℕ) (hp : PrimeSchedule p E) :
    CertificateSchedule p E (fun i => scheduleCap i.val) (scheduleNormalizer p) (scheduleLoss p)
      (scheduleMass p) (scheduleCubic p) := by
  refine ⟨hp.small_le,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i hi
    obtain ⟨hpi,hEi⟩ := hp.prefix_stage i hi
    have hsmall : i.val < smallLength := hi.trans_le prefix_le_small
    refine ⟨hpi,?_,?_,hEi,?_⟩
    · simp only [scheduleCap,if_pos hi]
    · simp only [scheduleNormalizer,if_pos hi]
    · simp only [scheduleLoss,if_pos hsmall,smallLoss_prefix i.val hi,realPrefixLoss]
  · intro i b j hb hj heq
    obtain ⟨hp0,hp1,hEi⟩ := hp.block_stage i b j hb hj heq
    have hbounds := block_index_bounds b j hb hj
    have hn : ¬i.val < prefixLength := by omega
    have hsmall : i.val < smallLength := by omega
    refine ⟨hp0,hp1,?_,?_,hEi,?_⟩
    · simp only [scheduleCap,if_neg hn]
    · simp only [scheduleNormalizer,if_neg hn]
    · simp only [scheduleLoss,heq,if_pos hbounds.2,smallLoss_block b j hb hj,realBlockLoss]
  · intro i hi
    have hpi := (hp.tail_stage i hi).2
    have hn : ¬i.val < prefixLength := by have := prefix_le_small; omega
    refine ⟨by omega,?_,?_,?_,?_⟩
    · simp only [scheduleCap,if_neg hn]
    · simp only [scheduleNormalizer,if_neg hn]
    · simp only [scheduleLoss,if_neg (Nat.not_lt.mpr hi),Erdos7CubicSieve.sequenceLoss,scheduleCubic]
    · exact Erdos7CubicSieve.sequenceCubic_succ p hp.monotone smallLength finalCubic i hi
  · intro t ht
    rw [scheduleMass_small p t (ht.trans prefix_le_small),smallMass_prefix_le t ht]
    rfl
  · intro b hb
    have hsmall : blockOffset b ≤ smallLength := by
      simpa only [block_offset_last] using block_offset_mono hb le_rfl
    rw [scheduleMass_small p _ hsmall,smallMass_boundary b hb]
    rfl
  · exact Erdos7CubicSieve.sequenceCubic_initial p smallLength finalCubic smallLength le_rfl
  · intro t ht htn
    exact scheduleCubic_nonneg p E hp t

theorem concrete_schedule_certificate {n : ℕ} (p E : Fin n → ℕ) (hp : PrimeSchedule p E) :
    SieveInvariantCertificate E (fun i => scheduleCap i.val) (scheduleNormalizer p)
      (scheduleTail p E (fun i => scheduleCap i.val)) (scheduleLoss p) (scheduleMass p) :=
  schedule_certificate p E _ _ _ _ _ (concrete_certificate_schedule p E hp)
    (fun i => scheduleCap_one_le i.val) (scheduleMass_succ p E hp)
    (fun t ht => (scheduleMass_pos p E hp t).le)

#print axioms scheduleMass_pos
#print axioms concrete_schedule_certificate
end Erdos7No9Certificate
