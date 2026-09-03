import Submission.No9Schedule
import Submission.No9BlockSoundness

/-! Stage-wise invariant for the checked prefix, checked blocks, and cubic tail. -/
namespace Erdos7No9Certificate
open scoped BigOperators
open Erdos7KilledSieve Erdos7Distortion Erdos7CompressionSieve
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

structure CertificateSchedule {n : ℕ} (p E : Fin n → ℕ) (c s L : Fin n → ℚ)
    (m Ctail : ℕ → ℚ) : Prop where
  small_le : smallLength ≤ n
  prefix_stage : ∀ i : Fin n,i.val < prefixLength →
    p i=(prefixControl i.val).p ∧
    c i=((prefixControl i.val).A:ℚ)/(prefixControl i.val).B ∧
    s i=1/(denominator (prefixControl i.val).p:ℚ) ∧
    (if (prefixControl i.val).p=3 then E i=1 else (prefixControl i.val).R ≤ E i) ∧
    L i=(loss (prefixControl i.val) (prefixState i.val).values:ℚ)/scale
  block_stage : ∀ (i : Fin n) (b j : ℕ),b < blockLength → j < (blockControl b).count →
    i.val=blockOffset b+j →
    (blockControl b).lo ≤ p i ∧ p i ≤ (blockControl b).hi ∧
    c i=5/4 ∧ s i=1/(p i-1:ℚ) ∧ (blockControl b).R ≤ E i ∧
    L i=(blockLoss (blockControl b) (blockState b).values (blockY1 b) (blockY2 b) (blockY3 b):ℚ)/scale
  tail_stage : ∀ i : Fin n,smallLength ≤ i.val →
    1 < p i ∧ c i=5/4 ∧ s i=1/(p i-1:ℚ) ∧
    L i=Erdos7CubicSieve.charge (p i)*Ctail i.val ∧
    Ctail (i.val+1)=Erdos7CubicSieve.multiplier (p i)*Ctail i.val
  prefix_mass : ∀ t,t ≤ prefixLength → m t=((prefixState t).mass:ℚ)/scale
  block_mass : ∀ b,b ≤ blockLength → m (blockOffset b)=((blockState b).mass:ℚ)/scale
  tail_initial : Ctail smallLength=((blockState blockLength).cubic:ℚ)/scale
  tail_nonneg : ∀ t,smallLength ≤ t → t ≤ n → 0 ≤ Ctail t

def scheduleTail {n : ℕ} (p E : Fin n → ℕ) (c : Fin n → ℚ) : Fin n → ℕ → ℚ :=
  fun i => powerTail (p i) (c i) (E i)

section Invariant
variable {n : ℕ} (κ : Type*) (A : Fin n → Type*)
variable [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)] [∀ i,DecidableEq (A i)]

def ScheduleInvariant (p E : Fin n → ℕ) (c : Fin n → ℚ) (Ctail : ℕ → ℚ)
    (t : ℕ) (μ : (∀ i,A i) → ℚ) : Prop :=
  (t < prefixLength ∧
    CompleteGridBound κ A E c (scheduleTail p E c) t μ realGrid (realValues (prefixState t).values) ∧
    CompleteMomentBound κ A E c (scheduleTail p E c) t μ 3 (((prefixState t).cubic:ℚ)/scale)) ∨
  (∃ b j,b < blockLength ∧ j < (blockControl b).count ∧ t=blockOffset b+j ∧
    CompleteGridBound κ A E c (scheduleTail p E c) t μ realGrid
      ((blockOperator (blockControl b)^j) (realValues (blockState b).values)) ∧
    CompleteMomentBound κ A E c (scheduleTail p E c) t μ 3
      ((blockCubicFactor (blockControl b))^j*(((blockState b).cubic:ℚ)/scale))) ∨
  (smallLength ≤ t ∧ CompleteMomentBound κ A E c (scheduleTail p E c) t μ 3 (Ctail t))

lemma scheduleInvariant_boundary (p E : Fin n → ℕ) (c s L : Fin n → ℚ) (m Ctail : ℕ → ℚ)
    (hsched : CertificateSchedule p E c s L m Ctail) (b : ℕ) (hb : b ≤ blockLength)
    (μ : (∀ i,A i) → ℚ)
    (hgrid : CompleteGridBound κ A E c (scheduleTail p E c) (blockOffset b) μ realGrid (realValues (blockState b).values))
    (hmoment : CompleteMomentBound κ A E c (scheduleTail p E c) (blockOffset b) μ 3 (((blockState b).cubic:ℚ)/scale)) :
    ScheduleInvariant κ A p E c Ctail (blockOffset b) μ := by
  by_cases hlast : b=blockLength
  · subst b
    right; right
    rw [block_offset_last] at *
    exact ⟨le_rfl,by simpa only [hsched.tail_initial] using hmoment⟩
  · right; left
    refine ⟨b,0,by omega,block_count_pos b (by omega),by omega,?_,?_⟩
    · simpa only [pow_zero,Module.End.one_apply] using hgrid
    · simpa only [pow_zero,one_mul] using hmoment

lemma scheduleInvariant_initial (p E : Fin n → ℕ) (c : Fin n → ℚ) (Ctail : ℕ → ℚ)
    (μ : (∀ i,A i) → ℚ) (hm : (∑ x,μ x)=1) : ScheduleInvariant κ A p E c Ctail 0 μ := by
  left
  have hstate : prefixState 0=initial := rfl
  refine ⟨by decide +kernel,?_,?_⟩
  · rw [hstate]
    exact completeGridBound_initial κ A E c (scheduleTail p E c) μ hm
  · rw [hstate]
    have hh := completeMomentBound_initial κ A E c (scheduleTail p E c) μ hm 3
    simpa only [initial,div_self (ne_of_gt scale_pos)] using hh

lemma scheduleInvariant_test (p E : Fin n → ℕ) (c s L : Fin n → ℚ) (m Ctail : ℕ → ℚ)
    (hsched : CertificateSchedule p E c s L m Ctail)
    (i : Fin n) (μ : (∀ i,A i) → ℚ) (hμ : ∀ x,0 ≤ μ x)
    (hI : ScheduleInvariant κ A p E c Ctail i.val μ) :
    CompleteTestBound κ A E c (scheduleTail p E c) i.val μ 1
      (fun z => residual (c i) (s i*z)) (L i) := by
  rcases hI with ⟨hi,hgrid,hmoment⟩ | ⟨b,j,hb,hj,heq,hgrid,hmoment⟩ | ⟨hi,hmoment⟩
  · have hcheck := prefix_checked i.val hi
    obtain ⟨hp,hc,hs,hE,hL⟩ := hsched.prefix_stage i hi
    rw [hc,hs,hL]
    exact completeGridBound_rounded_loss κ A E c (scheduleTail p E c) i.val μ hμ _ hgrid _ hcheck.geometry
  · have hcheck := block_checked b hb
    obtain ⟨hp0,hp1,hc,hs,hE,hL⟩ := hsched.block_stage i b j hb hj heq
    rw [hc,hs,hL]
    exact completeGridBound_rounded_block_loss κ A E c (scheduleTail p E c) i.val μ hμ
      (blockControl b) hcheck.analytic hcheck.geometry (blockState b).values (blockY1 b) (blockY2 b) (blockY3 b)
      hcheck.top hcheck.power1 hcheck.power2 hcheck.power3 j hj.le hgrid (p i) hp0
  · obtain ⟨hp,hc,hs,hL,hC⟩ := hsched.tail_stage i hi
    rw [hc,hs,hL]
    exact completeMomentBound_tail_residual κ A E c (scheduleTail p E c) i.val μ hμ _ hmoment (p i) hp

lemma scheduleInvariant_step (p E : Fin n → ℕ) (c s L : Fin n → ℚ) (m Ctail : ℕ → ℚ)
    (hsched : CertificateSchedule p E c s L m Ctail) (hc : ∀ i,1 ≤ c i)
    (hmsucc : ∀ i : Fin n,m (i.val+1)=m i.val-L i) (hmpos : ∀ t,t ≤ n → 0 ≤ m t)
    (i : Fin n) (μ : (∀ i,A i) → ℚ) (B : Finset (∀ i,A i)) (hμ : ∀ x,0 ≤ μ x)
    (hm : (∑ x,μ x)=m i.val) (hI : ScheduleInvariant κ A p E c Ctail i.val μ)
    (hL : (∑ x,μ x*residual (c i) (coordinateFraction A i B x)) ≤ L i) :
    ScheduleInvariant κ A p E c Ctail (i.val+1) (killedResample A i μ B (c i) (L i)) := by
  let ν := killedResample A i μ B (c i) (L i)
  change ScheduleInvariant κ A p E c Ctail (i.val+1) ν
  have hLm : L i ≤ ∑ x,μ x := by
    rw [hm]
    have hh := hmpos (i.val+1) (by omega)
    rw [hmsucc i] at hh
    linarith
  have hν : ∀ x,0 ≤ ν x := killedResample_nonneg A i μ hμ B (c i) (L i) (hc i) hLm
  have hνtotal : (∑ x,ν x)=m (i.val+1) := by
    rw [show (∑ x,ν x)=m i.val-L i from by
      simpa only [hm] using killedResample_total A i μ B (c i) (L i) (hc i) hLm hL]
    exact (hmsucc i).symm
  rcases hI with ⟨hi,hgrid,hmoment⟩ | ⟨b,j,hb,hj,heq,hgrid,hmoment⟩ | ⟨hi,hmoment⟩
  · have hcheck := prefix_checked i.val hi
    obtain ⟨hp,hci,hsi,hEi,hLi⟩ := hsched.prefix_stage i hi
    have hqi : scheduleTail p E c i=powerTail (prefixControl i.val).p (c i) (E i) := by
      simp only [scheduleTail,hp]
    have hnew := complete_rounded_prefix_step κ A E c (scheduleTail p E c) i.val i.isLt μ hμ B (prefixState i.val)
      (hm.trans (hsched.prefix_mass i.val hi.le)) hgrid hmoment (prefixControl i.val)
      hcheck.p_three hcheck.R_pos hcheck.R_le hcheck.geometry.B_pos hcheck.geometry.B_le_A hcheck.cap_le hcheck.cut_lt
      hci hqi hEi hcheck.loss_lt.le (by simpa only [hLi] using hL)
    have hνeq : killedResample A i μ B (c i) ((loss (prefixControl i.val) (prefixState i.val).values:ℚ)/scale)=ν := by
      dsimp [ν]
      rw [hLi]
    rw [hνeq,← hcheck.values,← hcheck.cubic] at hnew
    by_cases hnext : i.val+1 < prefixLength
    · exact Or.inl ⟨hnext,hnew.1,hnew.2⟩
    · have hend : i.val+1=prefixLength := by omega
      have hg : CompleteGridBound κ A E c (scheduleTail p E c) (blockOffset 0) ν realGrid (realValues (blockState 0).values) := by
        simpa only [block_offset_zero,hend,prefix_block_state_agree] using hnew.1
      have hC : CompleteMomentBound κ A E c (scheduleTail p E c) (blockOffset 0) ν 3 (((blockState 0).cubic:ℚ)/scale) := by
        simpa only [block_offset_zero,hend,prefix_block_state_agree] using hnew.2
      have hh := scheduleInvariant_boundary κ A p E c s L m Ctail hsched 0 (Nat.zero_le _) ν hg hC
      simpa only [block_offset_zero,hend] using hh
  · have hcheck := block_checked b hb
    obtain ⟨hp0,hp1,hci,hsi,hEi,hLi⟩ := hsched.block_stage i b j hb hj heq
    have hnew := complete_rounded_block_substep κ A E c (scheduleTail p E c) i.val i.isLt μ hμ B
      (blockControl b) hcheck.analytic (p i) hp0 hp1 hci rfl hEi (blockState b).values
      (((blockState b).cubic:ℚ)/scale) (by positivity) j hgrid hmoment (L i) hLm hL
    change CompleteGridBound κ A E c (scheduleTail p E c) (i.val+1) ν realGrid
        ((blockOperator (blockControl b)^(j+1)) (realValues (blockState b).values)) ∧
      CompleteMomentBound κ A E c (scheduleTail p E c) (i.val+1) ν 3
        ((blockCubicFactor (blockControl b))^(j+1)*(((blockState b).cubic:ℚ)/scale)) at hnew
    by_cases hnext : j+1 < (blockControl b).count
    · exact Or.inr (Or.inl ⟨b,j+1,hb,hnext,by omega,hnew.1,hnew.2⟩)
    · have hend : j+1=(blockControl b).count := by omega
      have ht : i.val+1=blockOffset (b+1) := by rw [block_offset_succ b hb]; omega
      have hmfinish : (∑ x,ν x)=((blockStep (blockControl b) (blockState b) (blockY1 b) (blockY2 b) (blockY3 b)).mass:ℚ)/scale := by
        rw [hνtotal,ht,hsched.block_mass (b+1) (by omega),hcheck.mass]
      rw [hend] at hnew
      have hfinish := complete_rounded_block_finish κ A E c (scheduleTail p E c) (i.val+1) ν hν
        (blockControl b) hcheck.analytic hcheck.cut_lt (blockState b) (blockY1 b) (blockY2 b) (blockY3 b)
        hcheck.top hcheck.power1 hcheck.power2 hcheck.power3 hmfinish hnew.1 hnew.2
      rw [← hcheck.values,← hcheck.cubic] at hfinish
      have hh := scheduleInvariant_boundary κ A p E c s L m Ctail hsched (b+1) (by omega) ν
        (by simpa only [ht] using hfinish.1) (by simpa only [ht] using hfinish.2)
      simpa only [ht] using hh
  · obtain ⟨hp,hci,hsi,hLi,hCi⟩ := hsched.tail_stage i hi
    have hc0 : 0 ≤ c i := by have := hc i; linarith
    have hpQ : (2:ℚ) ≤ p i := by exact_mod_cast (by omega : 2 ≤ p i)
    have hcp : c i ≤ p i := by rw [hci]; linarith
    have hr := completeMomentBound_resample κ A E c (scheduleTail p E c) i.val i.isLt μ hμ 3 (Ctail i.val) hmoment B (hc i)
      (powerTail_zero_le_one (p i) hp (c i) hcp (E i))
      (fun g hg => powerTail_decreasing (p i) hp (c i) hc0 (E i) g)
      (powerTail_terminal (p i) (c i) (E i))
    have hfactor : momentFactor (E i) (scheduleTail p E c i) 3 ≤ Erdos7CubicSieve.multiplier (p i) := by
      simpa only [scheduleTail,hci,Erdos7CubicSieve.multiplier] using
        geometric_cubic_factor (p i) (E i) hp (c i) hc0
    have hbound := completeMomentBound_mono κ A E c (scheduleTail p E c) (i.val+1) _ 3 hr
      (mul_le_mul_of_nonneg_right hfactor (hsched.tail_nonneg i.val hi i.isLt.le))
    have hk := completeMomentBound_kill κ A E c (scheduleTail p E c) (i.val+1) i μ hμ B (hc i) (L i) hLm hL 3 _ hbound
    exact Or.inr (Or.inr ⟨by omega,by simpa only [hCi] using hk⟩)

end Invariant

theorem schedule_certificate {n : ℕ} (p E : Fin n → ℕ) (c s L : Fin n → ℚ) (m Ctail : ℕ → ℚ)
    (hsched : CertificateSchedule p E c s L m Ctail) (hc : ∀ i,1 ≤ c i)
    (hmsucc : ∀ i : Fin n,m (i.val+1)=m i.val-L i) (hmpos : ∀ t,t ≤ n → 0 ≤ m t) :
    SieveInvariantCertificate E c s (scheduleTail p E c) L m := by
  intro κ A hfin hnonempty hdec
  refine ⟨ScheduleInvariant κ A p E c Ctail,?_,?_,?_⟩
  · intro B
    exact scheduleInvariant_initial κ A p E c Ctail _ (towerWeights_total A B c hc 0)
  · intro i μ hμ hm hI
    exact scheduleInvariant_test κ A p E c s L m Ctail hsched i μ hμ hI
  · intro i μ B hμ hm hI hL
    exact scheduleInvariant_step κ A p E c s L m Ctail hsched hc hmsucc hmpos i μ B hμ hm hI hL

#print axioms schedule_certificate
#print axioms scheduleInvariant_test
#print axioms scheduleInvariant_step
end Erdos7No9Certificate
