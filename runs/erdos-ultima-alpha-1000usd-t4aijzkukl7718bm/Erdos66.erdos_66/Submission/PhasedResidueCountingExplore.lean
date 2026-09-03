import Submission.OccurrencePhaseBalanceExplore
import Submission.ResidueCountingExplore
import Submission.IntegerBlockExplore

/-! Actual natural residue counts for occurrence-phased block templates. -/
namespace Erdos66PhasedResidueCounting
open Erdos66OccurrencePhaseBalance Erdos66TranslatedPrefixPalette
  Erdos66Counting Erdos66ResidueCounting Erdos66IntegerBlock
open Filter
open scoped Classical Topology
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000

variable (M : ℕ) [NeZero M]

lemma cast_eq_iff_val (x : ℕ) (hx : x<M) (z : ZMod M) :
    (x:ZMod M)=z ↔ x=z.val := by
  constructor
  · intro h
    have hh := congrArg ZMod.val h
    simpa only [ZMod.val_natCast_of_lt hx] using hh
  · rintro rfl
    exact ZMod.natCast_zmod_val z

lemma one_block_residue_sum (C : ℕ → Finset (ZMod M)) (k : ℕ) (z : ZMod M) :
    (∑ x∈Finset.range M,
      if k*M+x∈residueSet M (blockSet M C) z then 1 else 0)=
      if z∈C k then 1 else (0:ℕ) := by
  have he : (∑ x∈Finset.range M,
      if k*M+x∈residueSet M (blockSet M C) z then 1 else 0)=
      ∑ x∈Finset.range M, if x=z.val ∧ z∈C k then 1 else (0:ℕ) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hx' := Finset.mem_range.mp hx
    simp only [residueSet,Set.mem_setOf_eq,mem_blockSet M C k x hx',
      Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,mul_zero,zero_add,
      cast_eq_iff_val M x hx' z]
    by_cases hz : x=z.val
    · subst x; simp
    · simp [hz]
  rw [he]
  by_cases hz : z∈C k <;> simp [hz,ZMod.val_lt]

lemma count_residue_blocks (C : ℕ → Finset (ZMod M)) (N : ℕ) (z : ZMod M) :
    count (residueSet M (blockSet M C) z) (N*M)=
      ∑ k∈Finset.range N, if z∈C k then 1 else (0:ℕ) := by
  induction N with
  | zero => simp [count,cutoff]
  | succ N ih =>
    have hh : count (residueSet M (blockSet M C) z) ((N+1)*M)=
        count (residueSet M (blockSet M C) z) (N*M)+
          ∑ x∈Finset.range M,
            if N*M+x∈residueSet M (blockSet M C) z then 1 else (0:ℕ) := by
      simp only [count,cutoff,Finset.card_filter,Nat.succ_mul,Finset.sum_range_add]
    rw [hh,ih,one_block_residue_sum,Finset.sum_range_succ]

lemma count_eq_sum_residues (A : Set ℕ) (N : ℕ) :
    count A N=∑ z : ZMod M, count (residueSet M A z) N := by
  simp only [count,cutoff,Finset.card_filter,residueSet,Set.mem_setOf_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases ha : x∈A <;> simp [ha]

lemma count_blocks (C : ℕ → Finset (ZMod M)) (N : ℕ) :
    count (blockSet M C) (N*M)=∑ k∈Finset.range N, (C k).card := by
  rw [count_eq_sum_residues M]
  simp_rw [count_residue_blocks]
  rw [Finset.sum_comm]
  simp

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def balancedBlockSet (f : ℕ → α) (C : α → Finset (ZMod M)) : Set ℕ :=
  blockSet M (fun k ↦ shift M (C (f k)) (phase M f k))

/-- The bound is for actual natural-number counts, not product-group counts. -/
theorem balanced_block_residue_discrepancy (f : ℕ → α)
    (C : α → Finset (ZMod M)) (N : ℕ) (z : ZMod M) :
    |(count (residueSet M (balancedBlockSet M f C) z) (N*M):ℝ)-
      count (balancedBlockSet M f C) (N*M)/M| ≤ (Fintype.card α:ℝ)*M := by
  simp only [balancedBlockSet,count_residue_blocks,count_blocks,shift_card]
  push_cast
  exact phase_balance M f C N z

lemma count_add_bounds (A : Set ℕ) (N R : ℕ) :
    count A N ≤ count A (N+R) ∧ count A (N+R) ≤ count A N+R := by
  have he : count A (N+R)=count A N+
      ∑ j∈Finset.range R, if N+j∈A then 1 else (0:ℕ) := by
    simp only [count,cutoff,Finset.card_filter,Finset.sum_range_add]
  rw [he]
  constructor
  · omega
  · have hh : (∑ j∈Finset.range R, if N+j∈A then 1 else (0:ℕ))≤R := by
      calc
        _ ≤ ∑ _j∈Finset.range R, (1:ℕ) :=
          Finset.sum_le_sum (fun j _ ↦ by split_ifs <;> omega)
        _ = R := by simp
    omega

/-- A partial final block adds at most two block lengths to the discrepancy. -/
theorem balanced_residue_discrepancy (f : ℕ → α)
    (C : α → Finset (ZMod M)) (X : ℕ) (z : ZMod M) :
    |(count (residueSet M (balancedBlockSet M f C) z) X:ℝ)-
      count (balancedBlockSet M f C) X/M| ≤ ((Fintype.card α:ℝ)+2)*M := by
  let A := balancedBlockSet M f C
  let Y := X/M*M
  let R := X%M
  have hX : X=Y+R := by simpa [Y,R,Nat.mul_comm] using (Nat.div_add_mod X M).symm
  have hR : (R:ℝ) ≤ M := by exact_mod_cast (Nat.mod_lt X (NeZero.pos M)).le
  have hM : (1:ℝ)≤M := by exact_mod_cast NeZero.pos M
  have hM0 : (0:ℝ)<M := by linarith
  obtain ⟨ha,ha'⟩ := count_add_bounds A Y R
  obtain ⟨hz,hz'⟩ := count_add_bounds (residueSet M A z) Y R
  rw [←hX] at ha ha' hz hz'
  have ha₀ : 0 ≤ (count A X:ℝ)-count A Y := by
    have hh : (count A Y:ℝ)≤count A X := by exact_mod_cast ha
    linarith
  have ha₁ : (count A X:ℝ)-count A Y≤R := by
    have hh : (count A X:ℝ)≤count A Y+R := by exact_mod_cast ha'
    linarith
  have hz₀ : 0 ≤ (count (residueSet M A z) X:ℝ)-count (residueSet M A z) Y := by
    have hh : (count (residueSet M A z) Y:ℝ)≤count (residueSet M A z) X := by exact_mod_cast hz
    linarith
  have hz₁ : (count (residueSet M A z) X:ℝ)-count (residueSet M A z) Y≤R := by
    have hh : (count (residueSet M A z) X:ℝ)≤count (residueSet M A z) Y+R := by exact_mod_cast hz'
    linarith
  have ht := balanced_block_residue_discrepancy M f C (X/M) z
  change |(count (residueSet M A z) Y:ℝ)-count A Y/M| ≤ (Fintype.card α:ℝ)*M at ht
  have hd₀ : 0≤((count A X:ℝ)-count A Y)/M := div_nonneg ha₀ hM0.le
  have hd₁ : ((count A X:ℝ)-count A Y)/M≤M := by
    apply (div_le_iff₀ hM0).mpr
    have hh : (M:ℝ)≤M*M := by nlinarith
    linarith
  have hd₂ : (count A X:ℝ)/M-count A Y/M=((count A X:ℝ)-count A Y)/M := by ring
  rw [abs_le] at ht ⊢
  change _ ≤ (count (residueSet M A z) X:ℝ)-count A X/M ∧
    (count (residueSet M A z) X:ℝ)-count A X/M ≤ _
  constructor <;> linarith

lemma count_atTop_of_infinite (A : Set ℕ) (hA : A.Infinite) :
    Tendsto (count A) atTop atTop := by
  apply tendsto_atTop.mpr
  intro m
  obtain ⟨F,hF,hcard⟩ := hA.exists_subset_card_eq m
  filter_upwards [eventually_ge_atTop (F.sup id+1)] with N hN
  rw [←hcard]
  apply Finset.card_le_card
  intro a ha
  apply mem_cutoff.mpr
  have hh : a≤F.sup id := Finset.le_sup (f := id) ha
  exact ⟨by omega,hF ha⟩

/-- If the phased output is infinite, its ordinary counts are equidistributed
    modulo the fixed block modulus. No representation limit is assumed. -/
theorem balanced_residue_equidistribution (f : ℕ → α)
    (C : α → Finset (ZMod M)) (hA : (balancedBlockSet M f C).Infinite) (z : ZMod M) :
    Tendsto (fun N ↦ (count (residueSet M (balancedBlockSet M f C) z) N:ℝ)/
      count (balancedBlockSet M f C) N) atTop (𝓝 (1/(M:ℝ))) := by
  let A := balancedBlockSet M f C
  let D : ℝ := ((Fintype.card α:ℝ)+2)*M
  have ht : Tendsto (fun N ↦ (count A N:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (count_atTop_of_infinite A hA)
  have he : Tendsto (fun N ↦ D/(count A N:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ht
  have hl := (tendsto_const_nhds (x := (1/(M:ℝ)))).sub he
  have hu := (tendsto_const_nhds (x := (1/(M:ℝ)))).add he
  simp only [sub_zero,add_zero] at hl hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [ht.eventually_gt_atTop 0] with N hN
    have hb := (abs_le.mp (balanced_residue_discrepancy M f C N z)).1
    change -D ≤ (count (residueSet M A z) N:ℝ)-count A N/M at hb
    have heq : 1/(M:ℝ)-D/(count A N:ℝ)=
        ((count A N:ℝ)/M-D)/(count A N:ℝ) := by
      field_simp
    rw [heq]
    apply div_le_div_of_nonneg_right _ hN.le
    linarith
  · filter_upwards [ht.eventually_gt_atTop 0] with N hN
    have hb := (abs_le.mp (balanced_residue_discrepancy M f C N z)).2
    change (count (residueSet M A z) N:ℝ)-count A N/M ≤ D at hb
    have heq : 1/(M:ℝ)+D/(count A N:ℝ)=
        ((count A N:ℝ)/M+D)/(count A N:ℝ) := by
      field_simp
    rw [heq]
    apply div_le_div_of_nonneg_right _ hN.le
    linarith

end Erdos66PhasedResidueCounting
