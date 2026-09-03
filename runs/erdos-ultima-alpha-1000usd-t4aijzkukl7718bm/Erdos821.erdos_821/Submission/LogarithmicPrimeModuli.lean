import Submission.WidePrimePools

/-!
# A growing reciprocal mass of prime moduli

Disjoint logarithmic intervals are summed before applying the progression
estimate. Their total reciprocal mass grows with the number of intervals.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

lemma widePrimePool_separated (a b c d m : ℕ) (hbc : b ≤ c) :
    Disjoint (widePrimePool a b m) (widePrimePool c d m) := by
  apply disjoint_left.mpr
  intro p hp hq
  have hp' := mem_widePrimePool.mp hp
  have hq' := mem_widePrimePool.mp hq
  have hscale := progressionScaleN_monotone (Nat.mul_le_mul_right m hbc)
  have he : p = progressionScaleN (b*m) := by omega
  have hpr := hp'.1
  rw [he] at hpr
  exact Nat.Prime.not_prime_pow' (by omega : 64*(b*m) ≠ 1) hpr

lemma prime_pool_composite_error_le (P : Finset ℕ) (N Q : ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ Q) :
    (∑ p ∈ P, compositeProgressionError p N) ≤ primitivePoolMean P N+
      4*(P.card : ℝ)*(Nat.log 2 N : ℝ)*Real.log Q := by
  have hmain : (∑ p ∈ P, primitiveConductorMangoldtMajorant p N / p.totient) =
      primitivePoolMean P N := by
    unfold primitivePoolMean
    apply sum_congr rfl
    intro p hp
    have he : p.divisors.erase 1 = {p} := by
      rw [(hP p hp).1.divisors]
      simp [(hP p hp).1.ne_one.symm]
    simp only [primitiveConductorMangoldtMajorant,he,sum_singleton]
  simp only [compositeProgressionError,add_div,sum_add_distrib]
  rw [hmain]
  apply _root_.add_le_add le_rfl
  have hloc (p : ℕ) (hp : p ∈ P) :
      (((p : ℝ)+1)*characterLiftError p N)/(p.totient : ℝ) ≤
        4*(Nat.log 2 N : ℝ)*Real.log Q := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).1.two_le
    have hφ : (p.totient : ℝ) = (p : ℝ)-1 := by
      rw [Nat.totient_prime (hP p hp).1,Nat.cast_sub (hP p hp).1.one_lt.le,Nat.cast_one]
    have hφ0 : (0 : ℝ) < p.totient := by rw [hφ]; linarith
    have hratio : (p : ℝ)+1 ≤ 4*p.totient := by rw [hφ]; linarith
    have hlift := mul_le_mul_of_nonneg_left (log_nat_mono (hP p hp).2)
      (Nat.cast_nonneg (α := ℝ) (Nat.log 2 N))
    change characterLiftError p N ≤ (Nat.log 2 N : ℝ)*Real.log Q at hlift
    apply (div_le_iff₀ hφ0).mpr
    calc
      _ ≤ (4*(p.totient : ℝ))*((Nat.log 2 N : ℝ)*Real.log Q) :=
        mul_le_mul hratio hlift (characterLiftError_nonneg _ _) (by positivity)
      _ = _ := by ring
  apply (sum_le_sum hloc).trans_eq
  rw [sum_const,nsmul_eq_mul]
  ring

def logMomentScale (m : ℕ) : ℕ := 2^(m+5)
def logMomentTop (m : ℕ) : ℕ := 2^(m+3)
def logMomentX (m : ℕ) : ℕ := progressionScaleN (logMomentScale m*logMomentScale m)
def logMomentBlocks (m : ℕ) : Finset ℕ := Icc 1 (logMomentTop m-1)
noncomputable def logMomentModuli (m : ℕ) : Finset ℕ :=
  (logMomentBlocks m).biUnion (fun a => widePrimePool a (a+1) (logMomentScale m))

lemma logMomentScale_ge (m : ℕ) : 32 ≤ logMomentScale m := by
  exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 5 ≤ m+5)

lemma logMomentTop_four (m : ℕ) : 4*logMomentTop m = logMomentScale m := by
  unfold logMomentTop logMomentScale
  rw [show m+5 = (m+3)+2 by omega,pow_add]
  ring

lemma logMomentBlocks_disjoint (m : ℕ) :
    (↑(logMomentBlocks m) : Set ℕ).PairwiseDisjoint
      (fun a => widePrimePool a (a+1) (logMomentScale m)) := by
  intro a ha b hb hab
  rcases lt_or_gt_of_ne hab with h | h
  · exact widePrimePool_separated _ _ _ _ _ (by omega)
  · exact (widePrimePool_separated _ _ _ _ _ (by omega)).symm

lemma sum_logMomentModuli (m : ℕ) (F : ℕ → ℝ) :
    (∑ p ∈ logMomentModuli m, F p) =
      ∑ a ∈ logMomentBlocks m, ∑ p ∈ widePrimePool a (a+1) (logMomentScale m), F p := by
  exact sum_biUnion (logMomentBlocks_disjoint m)

lemma logMomentModuli_prime_bound (m p : ℕ) (hp : p ∈ logMomentModuli m) :
    p.Prime ∧ p ≤ progressionScaleN (logMomentTop m*logMomentScale m) := by
  obtain ⟨a,ha,hp⟩ := mem_biUnion.mp hp
  have hp' := mem_widePrimePool.mp hp
  have ha' := mem_Icc.mp ha
  have hB : 0 < logMomentTop m := by unfold logMomentTop; positivity
  refine ⟨hp'.1,hp'.2.2.trans (progressionScaleN_monotone ?_)⟩
  exact Nat.mul_le_mul_right _ (by omega)

lemma logMomentModuli_card_le (m : ℕ) :
    (logMomentModuli m).card ≤ progressionScaleN (logMomentTop m*logMomentScale m) := by
  have hsub : logMomentModuli m ⊆ Icc 1 (progressionScaleN (logMomentTop m*logMomentScale m)) := by
    intro p hp
    have h := logMomentModuli_prime_bound m p hp
    exact mem_Icc.mpr ⟨h.1.pos,h.2⟩
  exact (card_le_card hsub).trans_eq (by simp)

lemma sum_reciprocal_successors (B : ℕ) (hB : 0 < B) :
    (∑ a ∈ Icc 1 (B-1), ((a+1 : ℕ) : ℝ)⁻¹)+1 = (harmonic B : ℝ) := by
  have he : (range B).erase 0 = Icc 1 (B-1) := by
    ext a
    simp only [mem_erase,mem_range,mem_Icc]
    omega
  have h := sum_erase_add (range B) (fun a : ℕ => ((a+1 : ℕ) : ℝ)⁻¹) (mem_range.mpr hB)
  rw [he] at h
  simpa only [harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,Nat.zero_add,Nat.cast_one,inv_one] using h

/-- The mass grows linearly in m, whereas log log of the prime scale also
has linear size in m. -/
theorem logMomentModuli_mass_lower (m : ℕ) :
    (m : ℝ)/4096 ≤ poolTotientMass (logMomentModuli m) := by
  have hE : 1 ≤ logMomentScale m := (by decide : 1 ≤ 32).trans (logMomentScale_ge m)
  have hlow : (∑ a ∈ logMomentBlocks m, 1/(2048*((a : ℝ)+1))) ≤ poolTotientMass (logMomentModuli m) := by
    unfold poolTotientMass
    rw [sum_logMomentModuli]
    apply sum_le_sum
    intro a ha
    have h := widePrimePool_mass_lower a (a+1) (logMomentScale m) (by omega) hE
    simpa only [Nat.add_sub_cancel_left,Nat.cast_one,Nat.cast_add] using h
  have hH := log_add_one_le_harmonic (logMomentTop m)
  have hB : 0 < logMomentTop m := by unfold logMomentTop; positivity
  have hlog : ((m : ℝ)+3)/2 ≤ Real.log (logMomentTop m) := by
    unfold logMomentTop
    rw [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,Nat.cast_add,Nat.cast_ofNat]
    have h2 : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have h := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ (m : ℝ)+3)
    linarith
  have hlogB : Real.log (logMomentTop m : ℝ) ≤ Real.log ((logMomentTop m+1 : ℕ) : ℝ) :=
    log_nat_mono (Nat.le_succ _)
  have hsum := sum_reciprocal_successors (logMomentTop m) hB
  have he : (∑ a ∈ logMomentBlocks m, 1/(2048*((a : ℝ)+1))) =
      (∑ a ∈ Icc 1 (logMomentTop m-1), ((a+1 : ℕ) : ℝ)⁻¹)/2048 := by
    rw [sum_div]
    apply sum_congr rfl
    intro a ha
    push_cast
    simp only [mul_inv_rev,div_eq_mul_inv,one_mul]
  rw [he] at hlow
  linarith only [hlow,hH,hlog,hlogB,hsum]

lemma logMoment_block_primitive_bound (m a : ℕ) (ha : a ∈ logMomentBlocks m) :
    primitivePoolMean (widePrimePool a (a+1) (logMomentScale m)) (logMomentX m) ≤
      4000000000000*((logMomentScale m : ℝ)+1)^10*
        (2 : ℝ)^((64*logMomentScale m-1)*logMomentScale m) := by
  have ha' := mem_Icc.mp ha
  have hE := logMomentScale_ge m
  have hB := logMomentTop_four m
  have hB0 : 0 < logMomentTop m := by unfold logMomentTop; positivity
  have haB : a+1 ≤ logMomentTop m := by omega
  have hhalf : 2*(a+1) ≤ logMomentScale m := by omega
  have h1 : 4*(a+1)+1 ≤ logMomentScale m+2*a := by omega
  have h2 : 64*(a+1)+1 ≤ 64*a+3*logMomentScale m := by omega
  have h := wide_primitive_mean_bound (widePrimePool a (a+1) (logMomentScale m))
    a (a+1) (logMomentScale m) (logMomentScale m) ha'.1 (by omega) hhalf h1 h2
    (fun p hp => ⟨(mem_widePrimePool.mp hp).1.two_le,(mem_widePrimePool.mp hp).2⟩)
  change _ ≤ _ at h
  convert h using 1
  simp only [wideMeanConstant,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
  ring

lemma logMoment_primitive_bound (m : ℕ) :
    primitivePoolMean (logMomentModuli m) (logMomentX m) ≤
      4000000000000*((logMomentScale m : ℝ)+1)^11*
        (2 : ℝ)^((64*logMomentScale m-1)*logMomentScale m) := by
  unfold primitivePoolMean
  rw [sum_logMomentModuli]
  have h := sum_le_sum (fun a ha => logMoment_block_primitive_bound m a ha)
  apply h.trans
  rw [sum_const,nsmul_eq_mul]
  have hcard : (logMomentBlocks m).card ≤ logMomentScale m+1 := by
    simp only [logMomentBlocks,Nat.card_Icc,Nat.add_sub_cancel]
    have := logMomentTop_four m
    omega
  have hc : ((logMomentBlocks m).card : ℝ) ≤ (logMomentScale m : ℝ)+1 := by exact_mod_cast hcard
  calc
    _ ≤ ((logMomentScale m : ℝ)+1)*(4000000000000*((logMomentScale m : ℝ)+1)^10*
        (2 : ℝ)^((64*logMomentScale m-1)*logMomentScale m)) := by gcongr
    _ = _ := by ring

end Erdos821
