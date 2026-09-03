import Submission.ResidueCountingExplore
import Submission.PrefixCopyExplore

/-! Quantitative cost of retaining a fixed set of low residues. These are
necessary conditions on a hypothetical witness, not a disproof of its existence. -/
namespace Erdos66ResidueSupportMass
open Filter AdditiveCombinatorics Erdos66Counting Erdos66ResidueCounting Erdos66PrefixCopy
open scoped Topology Classical

variable (M : ℕ) [NeZero M]

def supportRestriction (A : Set ℕ) (S : Finset (ZMod M)) : Set ℕ :=
  {n | n ∈ A ∧ (n : ZMod M) ∈ S}

lemma support_count_decomposition (A : Set ℕ) (S : Finset (ZMod M)) (N : ℕ) :
    count (supportRestriction M A S) N = ∑ z ∈ S, count (residueSet M A z) N := by
  have hr : ∀ z : ZMod M, cutoff (residueSet M A z) N =
      (cutoff A N).filter (fun n : ℕ ↦ (n : ZMod M)=z) := by
    intro z
    ext n
    simp only [mem_cutoff,residueSet,Set.mem_setOf_eq,Finset.mem_filter]
    tauto
  have hs : cutoff (supportRestriction M A S) N =
      (cutoff A N).filter (fun n : ℕ ↦ (n : ZMod M) ∈ S) := by
    ext n
    simp only [mem_cutoff,supportRestriction,Set.mem_setOf_eq,Finset.mem_filter]
    tauto
  simp only [count,hr,hs]
  exact (Finset.sum_card_fiberwise_eq_card_filter _ _ _).symm

/-- Exact limiting fraction of the witness occupying any fixed residue support. -/
theorem witness_support_fraction {A : Set ℕ} {c : ℝ} (hc : c≠0)
    (ht : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c))
    (S : Finset (ZMod M)) :
    Tendsto (fun N ↦ (count (supportRestriction M A S) N : ℝ)/count A N)
      atTop (𝓝 ((S.card : ℝ)/M)) := by
  have hh := tendsto_finset_sum S (fun z hz ↦
    witness_ordinary_residue_equidistribution M hc ht z)
  have he : (∑ z ∈ S, (1/(M:ℝ))) = (S.card : ℝ)/M := by simp [div_eq_mul_inv]
  rw [he] at hh
  apply hh.congr
  intro N
  simp only [support_count_decomposition,Nat.cast_sum,Finset.sum_div]

/-- A core contained in a fixed residue support can occupy at most its
proportion of the final witness, regardless of its high-block choices. -/
theorem eventual_core_fraction {A B : Set ℕ} {c : ℝ} (hc : c≠0)
    (ht : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c))
    (S : Finset (ZMod M)) (hBA : B ⊆ A)
    (hB : ∀ a ∈ B, (a : ZMod M) ∈ S) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N in atTop, (count B N : ℝ)/count A N < (S.card : ℝ)/M+ε := by
  have hh := (witness_support_fraction M hc ht S).eventually_lt_const
    (show (S.card : ℝ)/M < (S.card : ℝ)/M+ε by linarith)
  filter_upwards [hh] with N hN
  have hb : count B N ≤ count (supportRestriction M A S) N :=
    Finset.card_le_card (fun a ha ↦ mem_cutoff.mpr
      ⟨(mem_cutoff.mp ha).1,hBA (mem_cutoff.mp ha).2,hB a (mem_cutoff.mp ha).2⟩)
  exact (div_le_div_of_nonneg_right (by exact_mod_cast hb) (Nat.cast_nonneg _)).trans_lt hN

/-- Any additive repair must supply the missing fraction of counting mass. -/
theorem eventual_repair_fraction (B D : Set ℕ) {c : ℝ} (hc : c≠0)
    (ht : Tendsto (fun n ↦ (sumRep (B ∪ D) n : ℝ)/Real.log n) atTop (𝓝 c))
    (S : Finset (ZMod M)) (hB : ∀ a ∈ B, (a : ZMod M) ∈ S)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N in atTop, 1-(S.card : ℝ)/M-ε < (count D N : ℝ)/count (B ∪ D) N := by
  have hh := eventual_core_fraction M hc ht S Set.subset_union_left hB ε hε
  filter_upwards [hh,count_pos_eventually hc ht] with N hN hpos
  have hp : (0:ℝ)<count (B ∪ D) N := by exact_mod_cast hpos
  have he : cutoff (B ∪ D) N = cutoff B N ∪ cutoff D N := by
    ext a
    simp only [mem_cutoff,Finset.mem_union,Set.mem_union]
    tauto
  have hb : count (B ∪ D) N ≤ count B N+count D N := by
    unfold count
    rw [he]
    exact Finset.card_union_le _ _
  have hr : (count (B ∪ D) N : ℝ) ≤ count B N+count D N := by exact_mod_cast hb
  have hh := div_le_div_of_nonneg_right hr hp.le
  rw [div_self hp.ne',add_div] at hh
  linarith

/-- A proper fixed support cannot be repaired by additions of negligible
relative counting mass. The conclusion concerns this core, not arbitrary sets. -/
theorem no_negligible_fixed_support_repair (B D : Set ℕ)
    (S : Finset (ZMod M)) (hS : S≠Finset.univ)
    (hB : ∀ a ∈ B, (a : ZMod M) ∈ S)
    (hD : Tendsto (fun N ↦ (count D N : ℝ)/count (B ∪ D) N) atTop (𝓝 0)) :
    ¬ ∃ c : ℝ, c≠0 ∧
      Tendsto (fun n ↦ (sumRep (B ∪ D) n : ℝ)/Real.log n) atTop (𝓝 c) := by
  rintro ⟨c,hc,ht⟩
  have hm : (0:ℝ)<M := by exact_mod_cast NeZero.pos M
  have hsc : S.card<M := by simpa using Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hS)
  have hs : (S.card:ℝ)/M<1 := (div_lt_one hm).mpr (by exact_mod_cast hsc)
  have he : 0 < (1-(S.card:ℝ)/M)/2 := by linarith
  have hlo := eventual_repair_fraction M B D hc ht S hB _ he
  have hhi := hD.eventually_lt_const he
  obtain ⟨N,hN,hN'⟩ := (hlo.and hhi).exists
  linarith

end Erdos66ResidueSupportMass
