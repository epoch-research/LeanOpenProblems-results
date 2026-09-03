import Submission.No9Schedule

/-! The exact rational mass schedule for the checked finite program. -/
namespace Erdos7No9Certificate
open scoped BigOperators
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

def realPrefixMass (i : ℕ) : ℚ := ((prefixState i).mass:ℚ)/scale
def realBlockMass (b : ℕ) : ℚ := ((blockState b).mass:ℚ)/scale
def realPrefixLoss (i : ℕ) : ℚ := (loss (prefixControl i) (prefixState i).values:ℚ)/scale
def realBlockLoss (b : ℕ) : ℚ :=
  (blockLoss (blockControl b) (blockState b).values (blockY1 b) (blockY2 b) (blockY3 b):ℚ)/scale
def finalMass : ℚ := realBlockMass blockLength
def finalCubic : ℚ := ((blockState blockLength).cubic:ℚ)/scale

lemma realPrefixMass_pos (i : ℕ) (hi : i ≤ prefixLength) : 0 < realPrefixMass i :=
  div_pos (by exact_mod_cast prefix_mass_pos i hi) scale_pos
lemma realBlockMass_pos (i : ℕ) (hi : i ≤ blockLength) : 0 < realBlockMass i :=
  div_pos (by exact_mod_cast block_mass_pos i hi) scale_pos
lemma realPrefixLoss_nonneg (i : ℕ) : 0 ≤ realPrefixLoss i := by exact div_nonneg (Nat.cast_nonneg _) scale_pos.le
lemma realBlockLoss_nonneg (i : ℕ) : 0 ≤ realBlockLoss i := by exact div_nonneg (Nat.cast_nonneg _) scale_pos.le
lemma finalMass_pos : 0 < finalMass := realBlockMass_pos blockLength le_rfl
lemma finalCubic_nonneg : 0 ≤ finalCubic := by exact div_nonneg (Nat.cast_nonneg _) scale_pos.le

theorem finalMargin : finalCubic*(6/(1500000:ℚ)^2) < finalMass := by decide +kernel

lemma realPrefixMass_succ (i : ℕ) (hi : i < prefixLength) :
    realPrefixMass (i+1)=realPrefixMass i-realPrefixLoss i := by
  have hh := prefix_checked i hi
  unfold realPrefixMass realPrefixLoss
  rw [hh.mass]
  change (((prefixState i).mass-loss (prefixControl i) (prefixState i).values:ℕ):ℚ)/scale=_
  rw [Nat.cast_sub hh.loss_lt.le,sub_div]

lemma realBlockMass_succ (b : ℕ) (hb : b < blockLength) :
    realBlockMass (b+1)=realBlockMass b-(blockControl b).count*realBlockLoss b := by
  have hh := block_checked b hb
  unfold realBlockMass realBlockLoss
  rw [hh.mass]
  change (((blockState b).mass-(blockControl b).count*blockLoss (blockControl b)
    (blockState b).values (blockY1 b) (blockY2 b) (blockY3 b):ℕ):ℚ)/scale=_
  rw [Nat.cast_sub hh.loss_lt.le,Nat.cast_mul,sub_div,mul_div_assoc]

noncomputable def smallMass (t : ℕ) : ℚ :=
  if t < prefixLength then realPrefixMass t else
  if t < smallLength then realBlockMass (blockPosition t).1-(blockPosition t).2*realBlockLoss (blockPosition t).1 else finalMass

noncomputable def smallLoss (t : ℕ) : ℚ :=
  if t < prefixLength then realPrefixLoss t else realBlockLoss (blockPosition t).1

lemma smallMass_prefix (i : ℕ) (hi : i < prefixLength) : smallMass i=realPrefixMass i := by
  simp only [smallMass,if_pos hi]
lemma smallLoss_prefix (i : ℕ) (hi : i < prefixLength) : smallLoss i=realPrefixLoss i := by
  simp only [smallLoss,if_pos hi]

lemma smallMass_block (b j : ℕ) (hb : b < blockLength) (hj : j < (blockControl b).count) :
    smallMass (blockOffset b+j)=realBlockMass b-(j:ℚ)*realBlockLoss b := by
  have hh := block_index_bounds b j hb hj
  simp only [smallMass,if_neg (Nat.not_lt.mpr hh.1),if_pos hh.2,blockPosition_eq b j hb hj]

lemma smallLoss_block (b j : ℕ) (hb : b < blockLength) (hj : j < (blockControl b).count) :
    smallLoss (blockOffset b+j)=realBlockLoss b := by
  have hh := block_index_bounds b j hb hj
  simp only [smallLoss,if_neg (Nat.not_lt.mpr hh.1),blockPosition_eq b j hb hj]

lemma smallMass_after (t : ℕ) (ht : smallLength ≤ t) : smallMass t=finalMass := by
  have hp : prefixLength ≤ t := prefix_le_small.trans ht
  simp only [smallMass,if_neg (Nat.not_lt.mpr hp),if_neg (Nat.not_lt.mpr ht)]

lemma smallMass_boundary (b : ℕ) (hb : b ≤ blockLength) : smallMass (blockOffset b)=realBlockMass b := by
  by_cases hlast : b=blockLength
  · subst b
    rw [block_offset_last,smallMass_after smallLength le_rfl]
    rfl
  · have hh := smallMass_block b 0 (by omega) (block_count_pos b (by omega))
    simpa only [Nat.add_zero,Nat.cast_zero,zero_mul,sub_zero] using hh

lemma smallMass_prefix_le (i : ℕ) (hi : i ≤ prefixLength) : smallMass i=realPrefixMass i := by
  by_cases hlast : i=prefixLength
  · subst i
    have hh := smallMass_boundary 0 (Nat.zero_le _)
    simpa only [block_offset_zero,realBlockMass,realPrefixMass,prefix_block_state_agree] using hh
  · exact smallMass_prefix i (by omega)

lemma smallMass_block_le (b j : ℕ) (hb : b < blockLength) (hj : j ≤ (blockControl b).count) :
    smallMass (blockOffset b+j)=realBlockMass b-(j:ℚ)*realBlockLoss b := by
  by_cases hlast : j=(blockControl b).count
  · subst j
    rw [← block_offset_succ b hb,smallMass_boundary (b+1) (by omega),realBlockMass_succ b hb]
  · exact smallMass_block b j hb (by omega)

lemma smallMass_succ (t : ℕ) (ht : t < smallLength) : smallMass (t+1)=smallMass t-smallLoss t := by
  by_cases hp : t < prefixLength
  · rw [smallMass_prefix_le (t+1) (by omega),smallMass_prefix t hp,smallLoss_prefix t hp,realPrefixMass_succ t hp]
  · obtain ⟨b,j,hb,hj,rfl⟩ := small_index_block t (by omega) ht
    have heq : blockOffset b+j+1=blockOffset b+(j+1) := by omega
    rw [heq,smallMass_block_le b (j+1) hb (by omega),smallMass_block b j hb hj,smallLoss_block b j hb hj]
    push_cast
    ring

lemma smallMass_pos (t : ℕ) : 0 < smallMass t := by
  by_cases hp : t < prefixLength
  · rw [smallMass_prefix t hp]
    exact realPrefixMass_pos t hp.le
  · by_cases ht : t < smallLength
    · obtain ⟨b,j,hb,hj,rfl⟩ := small_index_block t (by omega) ht
      rw [smallMass_block b j hb hj]
      have hnext := realBlockMass_pos (b+1) (by omega)
      rw [realBlockMass_succ b hb] at hnext
      have hmul := mul_le_mul_of_nonneg_right (show (j:ℚ) ≤ (blockControl b).count from by exact_mod_cast hj.le)
        (realBlockLoss_nonneg b)
      linarith
    · rw [smallMass_after t (by omega)]
      exact finalMass_pos

lemma smallLoss_nonneg (t : ℕ) : 0 ≤ smallLoss t := by
  unfold smallLoss
  split_ifs
  · exact realPrefixLoss_nonneg t
  · exact realBlockLoss_nonneg _

lemma smallMass_zero : smallMass 0=1 := by
  rw [smallMass_prefix 0 (by decide +kernel)]
  change (scale:ℚ)/scale=1
  exact div_self (ne_of_gt scale_pos)

#print axioms smallMass_succ
#print axioms smallMass_pos
#print axioms finalMargin
end Erdos7No9Certificate
