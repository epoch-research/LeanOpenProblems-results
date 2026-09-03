import FormalConjecturesUtil
import Submission.PrimeHarmonicBlocks
import Submission.ElementaryEnergy

/-! The energy obtained by discarding signs BEFORE summing within winning-prime
groups is genuinely superlinear. This concerns the actual largest-prime-factor
sequence, not a model; it does not give a lower bound on the signed energy. -/

namespace Erdos371UnsignedEnergyGrowth

open Finset Erdos371PrimeDiscrepancy Erdos371PrimeHarmonicBlocks

noncomputable def mass (p N : ℕ) : ℝ :=
  (((range N).filter fun n => winner n=p).card:ℝ)

noncomputable def unsignedEnergy (N : ℕ) : ℝ :=
  ∑ p ∈ (N+1).primesBelow, mass p N^2

lemma unsignedEnergy_nonneg (N : ℕ) : 0 ≤ unsignedEnergy N :=
  sum_nonneg (fun _ _ => sq_nonneg _)

noncomputable def touches (p N : ℕ) : Finset ℕ :=
  ((range N).filter fun n => n ≠ 0 ∧ p ∣ n) ∪
  ((range N).filter fun n => p ∣ n+1)

lemma touches_card_bound (p N : ℕ) : ((touches p N).card:ℝ) ≤ 2*(N:ℝ)/p := by
  have hc : ((range N).filter fun n => n ≠ 0 ∧ p ∣ n).card ≤ N/p := by
    rw [← Nat.card_multiples']
    exact card_le_card (filter_subset_filter _ (range_mono (by omega : N ≤ N+1)))
  have hu : (touches p N).card ≤ 2*(N/p) := by
    have hh := card_union_le ((range N).filter fun n => n ≠ 0 ∧ p ∣ n)
      ((range N).filter fun n => p ∣ n+1)
    rw [Nat.card_multiples] at hh
    unfold touches
    omega
  calc
    _ ≤ 2*((N/p:ℕ):ℝ) := by exact_mod_cast hu
    _ ≤ 2*((N:ℝ)/p) := mul_le_mul_of_nonneg_left Nat.cast_div_le (by norm_num)
    _ = _ := by ring

noncomputable def highCover (K L N : ℕ) : Finset ℕ :=
  (Icc K L).biUnion fun k => (block k).biUnion fun p => touches p N

lemma highCover_card_bound {K : ℕ} (hK : 0 < K) (L N : ℕ) :
    ((highCover K L N).card:ℝ) ≤ 8*N*(L+1-K:ℕ)/K := by
  have hc : (highCover K L N).card ≤
      ∑ k ∈ Icc K L, ∑ p ∈ block k, (touches p N).card := by
    exact card_biUnion_le.trans (sum_le_sum (fun k hk => card_biUnion_le))
  have hm : (∑ k ∈ Icc K L, blockMass k) ≤ (L+1-K:ℕ)*(4/(K:ℝ)) := by
    calc
      _ ≤ ∑ _k ∈ Icc K L, 4/(K:ℝ) := by
        apply sum_le_sum
        intro k hk
        have hKk := (mem_Icc.mp hk).1
        exact (blockMass_le (hK.trans_le hKk)).trans
          (div_le_div_of_nonneg_left (by norm_num) (Nat.cast_pos.mpr hK) (Nat.cast_le.mpr hKk))
      _ = _ := by simp
  calc
    _ ≤ ∑ k ∈ Icc K L, ∑ p ∈ block k, ((touches p N).card:ℝ) := by exact_mod_cast hc
    _ ≤ ∑ k ∈ Icc K L, ∑ p ∈ block k, 2*(N:ℝ)/p :=
      sum_le_sum (fun k hk => sum_le_sum (fun p hp => touches_card_bound p N))
    _ = 2*N*∑ k ∈ Icc K L, blockMass k := by simp [blockMass,mul_sum,div_eq_mul_inv]
    _ ≤ 2*N*((L+1-K:ℕ)*(4/(K:ℝ))) := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

lemma high_winner_in_cover {K L N n : ℕ} (hN : N ≤ 2^L) (hn : n<N)
    (hh : 2^K < winner n) : n ∈ highCover K L N := by
  have hn0 : 0 < n := by
    by_contra h
    have he : n=0 := by omega
    subst n
    have he : winner 0=1 := by decide +kernel
    rw [he] at hh
    have : 0 < 2^K := by positivity
    omega
  have hp := winner_prime hn0
  have hlo : K ≤ Nat.log 2 (winner n) := Nat.le_log_of_pow_le (by decide) hh.le
  have hhi : Nat.log 2 (winner n) ≤ L := by
    have hh := Nat.log_mono_right (b := 2) ((winner_le hn).trans hN)
    rwa [Nat.log_pow (by decide)] at hh
  apply mem_biUnion.mpr
  refine ⟨Nat.log 2 (winner n),mem_Icc.mpr ⟨hlo,hhi⟩,mem_biUnion.mpr ?_⟩
  refine ⟨winner n,mem_block.mpr ⟨hp,Nat.pow_log_le_self 2 hp.ne_zero,
    Nat.lt_pow_succ_log_self (by decide) _⟩,?_⟩
  unfold touches
  by_cases h : P n ≤ P (n+1)
  · apply mem_union_right
    apply mem_filter.mpr
    refine ⟨mem_range.mpr hn,?_⟩
    rw [winner,max_eq_right h]
    exact Nat.maxPrimeFac_dvd
  · apply mem_union_left
    apply mem_filter.mpr
    refine ⟨mem_range.mpr hn,hn0.ne',?_⟩
    rw [winner,max_eq_left (by omega)]
    exact Nat.maxPrimeFac_dvd

lemma high_winner_count_bound {K : ℕ} (hK : 0 < K) {L N : ℕ} (hN : N ≤ 2^L) :
    (((range N).filter fun n => 2^K < winner n).card:ℝ) ≤ 8*N*(L+1-K:ℕ)/K := by
  apply le_trans _ (highCover_card_bound hK L N)
  apply Nat.cast_le.mpr
  exact card_le_card (fun n hn => high_winner_in_cover hN (mem_range.mp (mem_filter.mp hn).1)
    (mem_filter.mp hn).2)

lemma low_mass_eq (K N : ℕ) :
    (∑ p ∈ (K+1).primesBelow, mass p N) =
      (((range N).filter fun n => 0<n ∧ winner n ≤ K).card:ℝ) := by
  have hh (n : ℕ) : winner n ∈ (K+1).primesBelow ↔ 0<n ∧ winner n ≤ K := by
    constructor
    · intro hn
      obtain ⟨hK,hp⟩ := Nat.mem_primesBelow.mp hn
      refine ⟨?_,by omega⟩
      by_contra h
      have he : n=0 := by omega
      subst n
      have he : winner 0=1 := by decide +kernel
      rw [he] at hp
      exact Nat.not_prime_one hp
    · rintro ⟨hn,hK⟩
      exact Nat.mem_primesBelow.mpr ⟨by omega,winner_prime hn⟩
  simp only [mass,← sum_boole]
  rw [sum_comm]
  simp [hh]

lemma low_mass_square_le {K N : ℕ} (hKN : K ≤ N) :
    (∑ p ∈ (K+1).primesBelow, mass p N)^2 ≤ (K:ℝ)*unsignedEnergy N := by
  have hcard : ((K+1).primesBelow.card:ℝ) ≤ K := by
    have hs : (K+1).primesBelow ⊆ Icc 1 K := by
      intro p hp
      obtain ⟨hpK,hp⟩ := Nat.mem_primesBelow.mp hp
      exact mem_Icc.mpr ⟨hp.one_lt.le,by omega⟩
    exact_mod_cast (card_le_card hs).trans (by simp : (Icc 1 K).card ≤ K)
  have hs : (∑ p ∈ (K+1).primesBelow, mass p N^2) ≤ unsignedEnergy N := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpK,hp⟩ := Nat.mem_primesBelow.mp hp
      exact Nat.mem_primesBelow.mpr ⟨by omega,hp⟩
    · intro p hp hp'
      exact sq_nonneg _
  exact sq_sum_le_card_mul_sum_sq.trans
    (mul_le_mul hcard hs (sum_nonneg fun p hp => sq_nonneg _) (Nat.cast_nonneg K))

lemma geometric_low_mass {T : ℕ} (hT : 0 < T) :
    (2:ℝ)^(64*T)/2 ≤ ∑ p ∈ (2^(63*T)+1).primesBelow, mass p (2^(64*T)) := by
  let N : ℕ := 2^(64*T)
  let K : ℕ := 2^(63*T)
  let lo := (range N).filter fun n => 0<n ∧ winner n ≤ K
  let hi := (range N).filter fun n => K < winner n
  have hb : (hi.card:ℝ) ≤ (16/63:ℝ)*N := by
    have hh := high_winner_count_bound (K := 63*T) (L := 64*T) (N := N) (by omega) le_rfl
    have he : 64*T+1-63*T = T+1 := by omega
    rw [he] at hh
    have ht : (0:ℝ) < T := Nat.cast_pos.mpr hT
    have ht1 : (1:ℝ) ≤ T := by exact_mod_cast hT
    change (hi.card:ℝ) ≤ _ at hh
    apply hh.trans
    push_cast
    apply (div_le_iff₀ (by positivity : (0:ℝ)<63*(T:ℝ))).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hcover : range N ⊆ insert 0 (lo ∪ hi) := by
    intro n hn
    by_cases h0 : n=0
    · simp [h0]
    · apply mem_insert_of_mem
      by_cases h : winner n ≤ K
      · exact mem_union_left _ (mem_filter.mpr ⟨hn,by omega,h⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨hn,by omega⟩)
  have hc : N ≤ 1+lo.card+hi.card := by
    have h1 := card_le_card hcover
    have h2 := card_insert_le 0 (lo ∪ hi)
    have h3 := card_union_le lo hi
    rw [card_range] at h1
    omega
  have hN : 8 ≤ N := by
    calc
      _ = 2^3 := by norm_num
      _ ≤ 2^(64*T) := Nat.pow_le_pow_right (by decide) (by omega)
  have hc' : (N:ℝ) ≤ 1+(lo.card:ℝ)+(hi.card:ℝ) := by exact_mod_cast hc
  have hN' : (8:ℝ) ≤ N := by exact_mod_cast hN
  rw [low_mass_eq]
  change (2:ℝ)^(64*T)/2 ≤ (lo.card:ℝ)
  have he : (N:ℝ)=(2:ℝ)^(64*T) := by simp [N]
  rw [← he]
  linarith

/-- At `N=2^(64T)`, unsigned group energy is at least `N^(65/64)/4`.
The signed group energy has no such asserted lower bound. -/
theorem geometric_unsigned_energy_lower_bound {T : ℕ} (hT : 0 < T) :
    (2:ℝ)^(65*T)/4 ≤ unsignedEnergy (2^(64*T)) := by
  have hl := geometric_low_mass hT
  have hc := low_mass_square_le (K := 2^(63*T)) (N := 2^(64*T))
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hs : ((2:ℝ)^(64*T)/2)^2 ≤
      (∑ p ∈ (2^(63*T)+1).primesBelow,mass p (2^(64*T)))^2 :=
    (sq_le_sq₀ (by positivity) (sum_nonneg fun p hp => Nat.cast_nonneg _)).mpr hl
  have hpow : (2:ℝ)^(63*T)*(2:ℝ)^(65*T) = ((2:ℝ)^(64*T))^2 := by
    rw [← pow_add,← pow_mul]
    congr 1
    omega
  push_cast at hc
  have hp : (0:ℝ)<(2:ℝ)^(63*T) := by positivity
  apply (mul_le_mul_iff_right₀ hp).mp
  nlinarith

open Filter
open scoped Topology

/-- Counting all occurrences in a group cannot supply a near-linear energy
majorant: even an eventual fixed-polylogarithmic upper bound is false. -/
theorem not_eventually_polylog_unsignedEnergy (B : ℕ) (C : ℝ) :
    ¬ ∀ᶠ N : ℕ in atTop, unsignedEnergy N ≤ C*N*Real.log (N:ℝ)^B := by
  intro h
  have hnseq : Tendsto (fun T : ℕ => (2:ℕ)^(64*T)) atTop atTop := by
    simpa only [pow_mul] using
      (tendsto_pow_atTop_atTop_of_one_lt (show (1:ℕ) < 2^64 by norm_num))
  have hu := hnseq.eventually h
  have hz : Tendsto (fun T : ℕ => C*(64*Real.log 2)^B*((T:ℝ)^B/(2:ℝ)^T)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_const_div_const_pow_of_one_lt B (show (1:ℝ)<2 by norm_num)).const_mul
        (C*(64*Real.log 2)^B)
  obtain ⟨T,hT,hupper,hsmall⟩ := ((eventually_gt_atTop 0).and
    (hu.and (hz.eventually_lt_const (by norm_num : (0:ℝ)<1/4)))).exists
  have hlow := geometric_unsigned_energy_lower_bound hT
  have hlog : Real.log ((2^(64*T):ℕ):ℝ) = (64*Real.log 2)*(T:ℝ) := by
    push_cast
    rw [Real.log_pow]
    push_cast
    ring
  rw [hlog] at hupper
  push_cast at hupper
  have hpow : (2:ℝ)^(65*T) = (2:ℝ)^(64*T)*(2:ℝ)^T := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow] at hlow
  have hnpos : (0:ℝ)<(2:ℝ)^(64*T) := by positivity
  have hpos : (0:ℝ)<(2:ℝ)^T := by positivity
  have hb : (2:ℝ)^T/4 ≤ C*((64*Real.log 2)*(T:ℝ))^B := by
    apply (mul_le_mul_iff_right₀ hnpos).mp
    nlinarith
  have hb' : (1/4:ℝ) ≤ C*(64*Real.log 2)^B*((T:ℝ)^B/(2:ℝ)^T) := by
    calc
      _ ≤ C*((64*Real.log 2)*(T:ℝ))^B/(2:ℝ)^T := by
        apply (le_div_iff₀ hpos).mpr
        linarith
      _ = _ := by rw [mul_pow]; ring
  linarith

end Erdos371UnsignedEnergyGrowth

#print axioms Erdos371UnsignedEnergyGrowth.geometric_unsigned_energy_lower_bound

#print axioms Erdos371UnsignedEnergyGrowth.not_eventually_polylog_unsignedEnergy
