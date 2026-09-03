import FormalConjecturesUtil
import Submission.TerminalCompression

/-! Dyadic reciprocal-prime bounds from Chebyshev's theorem. -/

namespace Erdos371PrimeHarmonicBlocks

open Finset

def block (k : ℕ) : Finset ℕ :=
  (2^(k+1)).primesBelow.filter fun p => 2^k ≤ p

lemma mem_block {p k : ℕ} :
    p ∈ block k ↔ p.Prime ∧ 2^k ≤ p ∧ p < 2^(k+1) := by
  simp [block, Nat.mem_primesBelow, and_comm, and_left_comm]

noncomputable def blockMass (k : ℕ) : ℝ := ∑ p ∈ block k, 1/(p:ℝ)

lemma block_log_sum_le (k : ℕ) :
    (∑ p ∈ block k, Real.log p) ≤ Real.log 4 * (2:ℝ)^(k+1) := by
  calc
    _ ≤ Chebyshev.theta (2^(k+1):ℕ) := by
      rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨hp, _, hlt⟩ := mem_block.mp hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, hlt.le⟩, hp⟩
      · intro p _ _
        exact Real.log_natCast_nonneg p
    _ ≤ _ := by
      simpa using Chebyshev.theta_le_log4_mul_x
        (by positivity : (0:ℝ) ≤ (2^(k+1):ℕ))

lemma block_card_le {k : ℕ} (hk : 0 < k) :
    ((block k).card : ℝ) ≤ 4*(2:ℝ)^k/k := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hk' : (0:ℝ) < k := Nat.cast_pos.mpr hk
  have hlo : ((block k).card:ℝ) * ((k:ℝ)*Real.log 2) ≤
      ∑ p ∈ block k, Real.log p := by
    calc
      _ = ∑ _p ∈ block k, (k:ℝ)*Real.log 2 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun p hp => by
        have hp0 := (mem_block.mp hp).2.1
        have hh := Real.log_le_log (by positivity : (0:ℝ) < (2:ℝ)^k)
          (show (2:ℝ)^k ≤ p by exact_mod_cast hp0)
        simpa [Real.log_pow] using hh)
  have hlog4 : Real.log 4 = 2*Real.log 2 := by
    calc
      Real.log 4 = Real.log ((2:ℝ)^2) := by norm_num
      _ = _ := by rw [Real.log_pow]; norm_num
  have hh := hlo.trans (block_log_sum_le k)
  rw [hlog4, pow_succ] at hh
  apply (le_div_iff₀ hk').mpr
  have hc : (((block k).card:ℝ) * k) * Real.log 2 ≤
      (4*(2:ℝ)^k) * Real.log 2 := by nlinarith
  exact (mul_le_mul_iff_left₀ hl).mp hc

lemma blockMass_nonneg (k : ℕ) : 0 ≤ blockMass k := by
  exact Finset.sum_nonneg (fun _ _ => by positivity)

lemma blockMass_le {k : ℕ} (hk : 0 < k) : blockMass k ≤ 4/(k:ℝ) := by
  have hpow : (0:ℝ) < (2:ℝ)^k := by positivity
  calc
    _ ≤ ∑ _p ∈ block k, 1/(2:ℝ)^k := by
      apply Finset.sum_le_sum
      intro p hp
      apply one_div_le_one_div_of_le hpow
      exact_mod_cast (mem_block.mp hp).2.1
    _ = ((block k).card:ℝ)/(2:ℝ)^k := by simp [div_eq_mul_inv]
    _ ≤ (4*(2:ℝ)^k/(k:ℝ))/(2:ℝ)^k :=
      div_le_div_of_nonneg_right (block_card_le hk) hpow.le
    _ = _ := by field_simp

/-- The reciprocal sum over a pair of dyadic prime blocks. -/
noncomputable def pairMass (k j : ℕ) : ℝ :=
  ∑ p ∈ block k, ∑ q ∈ block j, 1/((p:ℝ)*q)

lemma pairMass_eq (k j : ℕ) : pairMass k j = blockMass k * blockMass j := by
  simp [pairMass, blockMass, Finset.sum_mul_sum, mul_comm]

lemma pairMass_le {k j : ℕ} (hk : 0 < k) (hkj : k ≤ j) :
    pairMass k j ≤ 16/(k:ℝ)^2 := by
  rw [pairMass_eq]
  have hk' : (0:ℝ) < k := Nat.cast_pos.mpr hk
  have hkj' : (k:ℝ) ≤ j := Nat.cast_le.mpr hkj
  have hj := (blockMass_le (hk.trans_le hkj)).trans
    (div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 4) hk' hkj')
  calc
    _ ≤ (4/(k:ℝ)) * (4/(k:ℝ)) :=
      mul_le_mul (blockMass_le hk) hj (blockMass_nonneg j) (by positivity)
    _ = _ := by ring

/-- A summable tail for pairs with dyadic prime indices at bounded distance. -/
lemma nearby_blocks_tail_bound {K : ℕ} (hK : 0 < K) (L T : ℕ) :
    (∑ k ∈ Finset.Ico K T, ∑ j ∈ Finset.Icc k (k+L), pairMass k j) ≤
      32*(L+1:ℕ)/(K:ℝ) := by
  calc
    _ ≤ ∑ k ∈ Finset.Ico K T,
        ∑ _j ∈ Finset.Icc k (k+L), 16/(k:ℝ)^2 := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro j hj
      exact pairMass_le (hK.trans_le (Finset.mem_Ico.mp hk).1) (Finset.mem_Icc.mp hj).1
    _ = (16*(L+1:ℕ):ℝ) * (∑ k ∈ Finset.Ico K T, 1/(k:ℝ)^2) := by
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
      have he (k : ℕ) : k+L+1-k = L+1 := by omega
      simp only [he, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ (16*(L+1:ℕ):ℝ) * (2/(K:ℝ)) :=
      mul_le_mul_of_nonneg_left (Erdos371TerminalCompression.sum_reciprocal_sq hK T)
        (by positivity)
    _ = _ := by ring

end Erdos371PrimeHarmonicBlocks

#print axioms Erdos371PrimeHarmonicBlocks.blockMass_le
#print axioms Erdos371PrimeHarmonicBlocks.nearby_blocks_tail_bound
