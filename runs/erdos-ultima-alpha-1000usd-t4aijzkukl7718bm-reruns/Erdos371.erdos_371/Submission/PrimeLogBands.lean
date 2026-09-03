import FormalConjecturesUtil
import Submission.PrimeHarmonicBlocks

/-! Reciprocal-prime mass in a band of dyadic indices. -/

namespace Erdos371PrimeLogBands

open Finset Erdos371PrimeHarmonicBlocks

noncomputable def band (L U : ℕ) : Finset ℕ := (Ico L U).biUnion block

lemma mem_band {p L U : ℕ} : p ∈ band L U ↔
    p.Prime ∧ 2^L ≤ p ∧ p < 2^U := by
  constructor
  · intro hp
    obtain ⟨j,hj,hp⟩ := mem_biUnion.mp hp
    obtain ⟨hL,hU⟩ := mem_Ico.mp hj
    obtain ⟨hprime,hlo,hhi⟩ := mem_block.mp hp
    exact ⟨hprime,(Nat.pow_le_pow_right (by omega : 0<2) hL).trans hlo,
      hhi.trans_le (Nat.pow_le_pow_right (by omega : 0<2) (by omega))⟩
  · rintro ⟨hp,hlo,hhi⟩
    let j := Nat.log 2 p
    have hL : L ≤ j := Nat.le_log_of_pow_le (by omega) hlo
    have hU : j < U := by
      by_contra h
      have hh := (Nat.pow_le_pow_right (by omega : 0<2) (show U≤j by omega)).trans
        (Nat.pow_log_le_self 2 hp.ne_zero)
      omega
    exact mem_biUnion.mpr ⟨j,mem_Ico.mpr ⟨hL,hU⟩,mem_block.mpr
      ⟨hp,Nat.pow_log_le_self 2 hp.ne_zero,Nat.lt_pow_succ_log_self (by omega) p⟩⟩

lemma band_primes {p L U : ℕ} (hp : p ∈ band L U) : p.Prime := (mem_band.mp hp).1

lemma band_mass_eq (L U : ℕ) :
    (∑ p ∈ band L U, 1/(p:ℝ)) = ∑ j ∈ Ico L U, blockMass j := by
  apply sum_biUnion
  intro i _ j _ hij
  apply disjoint_left.mpr
  intro p hpi hpj
  have hi := mem_block.mp hpi
  have hj := mem_block.mp hpj
  exact hij ((Nat.log_eq_of_pow_le_of_lt_pow hi.2.1 hi.2.2).symm.trans
    (Nat.log_eq_of_pow_le_of_lt_pow hj.2.1 hj.2.2))

lemma block_index_interval_bound {L : ℕ} (hL : 0<L) :
    (∑ j ∈ Ico L (2*L), blockMass j) ≤ 4 := by
  have hLr : (0:ℝ)<L := by exact_mod_cast hL
  calc
    _ ≤ ∑ _j ∈ Ico L (2*L), 4/(L:ℝ) := by
      apply sum_le_sum
      intro j hj
      have hLj := (mem_Ico.mp hj).1
      exact (blockMass_le (hL.trans_le hLj)).trans
        (div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤4) hLr (by exact_mod_cast hLj))
    _ = 4 := by simp [Nat.card_Ico,show 2*L-L=L by omega]; field_simp

lemma block_index_mass_bound {L : ℕ} (hL : 0<L) (B : ℕ) :
    (∑ j ∈ Ico L (2^B*L), blockMass j) ≤ 4*(B:ℝ) := by
  induction B with
  | zero => simp
  | succ B ih =>
    have hpow : 0<2^B*L := Nat.mul_pos (by positivity) hL
    have hlo : L≤2^B*L := by nlinarith [Nat.one_le_pow B 2 (by omega)]
    have hhi : 2^B*L≤2*(2^B*L) := by omega
    have he : 2^(B+1)*L=2*(2^B*L) := by rw [pow_succ]; ring
    rw [he,← sum_Ico_consecutive blockMass hlo hhi]
    have hh := block_index_interval_bound hpow
    push_cast
    linarith

/-- The dependence is logarithmic in the ratio of the dyadic indices. -/
theorem band_mass_bound {L U B : ℕ} (hL : 0<L) (hU : U≤2^B*L) :
    (∑ p ∈ band L U, 1/(p:ℝ)) ≤ 4*(B:ℝ) := by
  rw [band_mass_eq]
  apply le_trans _ (block_index_mass_bound hL B)
  apply sum_le_sum_of_subset_of_nonneg
  · intro j hj
    obtain ⟨hjL,hjU⟩ := mem_Ico.mp hj
    exact mem_Ico.mpr ⟨hjL,hjU.trans_le hU⟩
  · intro j _ _
    exact blockMass_nonneg j

end Erdos371PrimeLogBands

#print axioms Erdos371PrimeLogBands.band_mass_bound
