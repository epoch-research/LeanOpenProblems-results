import Submission.MertensShiftedMoments
import Submission.FiniteLocalLimit

/-!
# Stability of a positive smooth-shifted-prime supply under cutoff refinement

This is a first-moment estimate on actual primes. It retains the strict
half-level restriction and explicitly charges the lost prime mass.
-/
open Nat Finset Filter ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 3000000

noncomputable def smoothPrimeLogMass (N Y : ℕ) : ℝ :=
  ∑ p ∈ smoothPrimePool N Y, Real.log (p : ℝ)

lemma smoothPrimeLogMass_nonneg (N Y : ℕ) : 0 ≤ smoothPrimeLogMass N Y :=
  sum_nonneg (fun p _ => Real.log_natCast_nonneg p)

lemma smoothPrimeLogMass_le_log_card (N Y : ℕ) :
    smoothPrimeLogMass N Y ≤ Real.log N*((smoothPrimePool N Y).card : ℝ) := by
  calc
    _ ≤ ∑ _p ∈ smoothPrimePool N Y, Real.log (N : ℝ) := by
      apply sum_le_sum
      intro p hp
      have hh := Nat.mem_primesBelow.mp (mem_filter.mp hp).1
      exact Real.log_le_log (by exact_mod_cast hh.2.pos)
        (by exact_mod_cast (show p ≤ N by omega))
    _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring

lemma smoothPrimeLogMass_cutoff_le_incidence (N A B : ℕ) (P : Finset ℕ)
    (hP : ∀ q : ℕ, q.Prime → A ≤ q → q < B → q ∈ P) :
    smoothPrimeLogMass N B ≤ smoothPrimeLogMass N A+primePoolIncidenceMoment P N := by
  unfold smoothPrimeLogMass smoothPrimePool primePoolIncidenceMoment
  simp only [sum_filter,← sum_add_distrib]
  apply sum_le_sum
  intro p hp
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
  by_cases hB : p-1 ∈ Nat.smoothNumbers B
  · rw [if_pos hB]
    by_cases hA : p-1 ∈ Nat.smoothNumbers A
    · rw [if_pos hA]
      exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hlog)
    · rw [if_neg hA,zero_add]
      have hx : ∃ q : ℕ, q.Prime ∧ q ∣ p-1 ∧ A ≤ q := by
        rw [Nat.mem_smoothNumbers'] at hA
        push_neg at hA
        obtain ⟨q,hq,hqd,hqA⟩ := hA
        exact ⟨q,hq,hqd,hqA⟩
      obtain ⟨q,hq,hqd,hqA⟩ := hx
      have hqB := Nat.mem_smoothNumbers'.mp hB q hq hqd
      have hc : 1 ≤ (P.filter (fun d => d ∣ p-1)).card :=
        Nat.succ_le_iff.mpr (card_pos.mpr ⟨q,mem_filter.mpr ⟨hP q hq hqA hqB,hqd⟩⟩)
      have hh := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ (P.filter (fun d => d ∣ p-1)).card by exact_mod_cast hc) hlog
      simpa only [one_mul] using hh
  · rw [if_neg hB]
    exact add_nonneg (by split_ifs <;> positivity) (mul_nonneg (Nat.cast_nonneg _) hlog)

lemma smoothPrimeLogMass_power_cutoff_le (a b t m : ℕ) (ha : 1 ≤ a) (hm : 1 ≤ m) :
    smoothPrimeLogMass (progressionScaleN (t*m)) (progressionScaleN (b*m)) ≤
      smoothPrimeLogMass (progressionScaleN (t*m)) (progressionScaleN (a*m))+
        primeBinomialMoment (powerIntervalPrimes (64*a) (64*b) m) 1 (progressionScaleN (t*m)) := by
  have hh := smoothPrimeLogMass_cutoff_le_incidence (progressionScaleN (t*m))
    (progressionScaleN (a*m)) (progressionScaleN (b*m)) (powerIntervalPrimes (64*a) (64*b) m) (by
      intro q hq hqa hqb
      have hne : q ≠ progressionScaleN (a*m) := by
        intro he
        rw [he] at hq
        apply Nat.Prime.not_prime_pow (show 2 ≤ 64*(a*m) by
          have ham := Nat.le_mul_of_pos_left m ha
          nlinarith only [ham,hm]) hq
      apply mem_filter.mpr
      refine ⟨mem_Ioc.mpr ⟨?_,?_⟩,hq⟩
      · simpa only [progressionScaleN,mul_assoc] using lt_of_le_of_ne hqa (Ne.symm hne)
      · simpa only [progressionScaleN,mul_assoc] using hqb.le)
  simpa only [primePoolIncidenceMoment,primeBinomialMoment,Nat.choose_one_right] using hh

/-- The loss is any fixed constant strictly above log(b/a), measured
against the actual Mangoldt mass. -/
theorem eventually_smoothPrimeLogMass_cutoff_loss (a b t : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) (ht : 22 ≤ t) (hlevel : 2*b+5 ≤ t)
    (c : ℝ) (hc : Real.log ((b : ℝ)/a)<c) :
    ∀ᶠ m : ℕ in atTop,
      smoothPrimeLogMass (progressionScaleN (t*m)) (progressionScaleN (b*m)) ≤
        smoothPrimeLogMass (progressionScaleN (t*m)) (progressionScaleN (a*m))+
          c*mangoldtSum (progressionScaleN (t*m)) := by
  have hlim := tendsto_powerInterval_primeBinomialMoment a b 1 t ha hab (by decide) ht
    (by simpa only [mul_one] using hlevel)
  simp only [pow_one,Nat.factorial_one,Nat.cast_one,div_one] at hlim
  filter_upwards [hlim.eventually (eventually_le_nhds hc),eventually_ge_atTop 1,
    (progressionScaleN_mul_tendsto t (by omega)).eventually eventually_mangoldt_nine_tenths]
    with m hm hm1 hpsi
  have hN : (0 : ℝ)<progressionScaleN (t*m) := by unfold progressionScaleN; positivity
  have hpsi0 : 0 < mangoldtSum (progressionScaleN (t*m)) := by linarith only [hpsi,hN]
  exact (smoothPrimeLogMass_power_cutoff_le a b t m ha hm1).trans
    (add_le_add le_rfl ((div_le_iff₀ hpsi0).mp hm))

/-- A positive density persists at a smaller cutoff whenever the charged
first-moment loss is below the available density margin. -/
theorem smoothPrimeLogMass_transfer (a b t : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) (ht : 22 ≤ t) (hlevel : 2*b+5 ≤ t)
    (c d : ℝ) (hmargin : Real.log ((b : ℝ)/a)<c-d)
    (H : ∀ᶠ m : ℕ in atTop, c*mangoldtSum (progressionScaleN (t*m)) ≤
      smoothPrimeLogMass (progressionScaleN (t*m)) (progressionScaleN (b*m))) :
    ∀ᶠ m : ℕ in atTop, d*mangoldtSum (progressionScaleN (t*m)) ≤
      smoothPrimeLogMass (progressionScaleN (t*m)) (progressionScaleN (a*m)) := by
  filter_upwards [H,eventually_smoothPrimeLogMass_cutoff_loss a b t ha hab ht hlevel (c-d) hmargin]
    with m hm hloss
  nlinarith only [hm,hloss]

lemma exists_cutoff_refinement_length (b : ℕ) (hb : 1 ≤ b) (c : ℝ) (hc : 0<c) :
    ∃ K : ℕ, 2 ≤ K ∧ Real.log (((b*K : ℕ) : ℝ)/((b*K-1 : ℕ) : ℝ)) < c/2 := by
  obtain ⟨K,hK⟩ := exists_nat_gt (max 2 (1+2/c))
  have hKR : (2 : ℝ)<K := (le_max_left _ _).trans_lt hK
  have hK2 : 2 ≤ K := by exact_mod_cast hKR.le
  have hbK : K ≤ b*K := Nat.le_mul_of_pos_left K hb
  have hBK1 : 1 ≤ b*K := by omega
  have he : ((b*K-1 : ℕ) : ℝ) = ((b*K : ℕ) : ℝ)-1 := by
    rw [Nat.cast_sub hBK1,Nat.cast_one]
  have hA : (0 : ℝ)<((b*K-1 : ℕ) : ℝ) := by exact_mod_cast (show 0<b*K-1 by omega)
  have hlarge : 2/c < ((b*K-1 : ℕ) : ℝ) := by
    rw [he]
    have hh : (K : ℝ) ≤ ((b*K : ℕ) : ℝ) := by exact_mod_cast hbK
    have hhigh := (le_max_right _ _).trans_lt hK
    linarith only [hh,hhigh]
  have hrec : 1/((b*K-1 : ℕ) : ℝ) < c/2 := by
    have hh := (div_lt_iff₀ hc).mp hlarge
    apply (div_lt_iff₀ hA).mpr
    linarith only [hh]
  refine ⟨K,hK2,?_⟩
  have hlog := Real.log_le_sub_one_of_pos
    (show 0<((b*K : ℕ) : ℝ)/((b*K-1 : ℕ) : ℝ) by positivity)
  have hid : ((b*K : ℕ) : ℝ)/((b*K-1 : ℕ) : ℝ)-1 = 1/((b*K-1 : ℕ) : ℝ) := by
    have hne : ((b*K : ℕ) : ℝ)-1 ≠ 0 := by rw [← he]; exact hA.ne'
    rw [he]
    field_simp
    ring
  exact (hlog.trans_eq hid).trans_lt hrec

/-- The density is halved at this step. No uniform lower bound under
arbitrarily many repetitions is asserted. -/
theorem exists_strictly_smaller_weighted_cutoff (b t : ℕ) (hb : 1 ≤ b)
    (ht : 22 ≤ t) (hlevel : 2*b+5 ≤ t) (c : ℝ) (hc : 0<c)
    (H : ∀ᶠ m : ℕ in atTop, c*mangoldtSum (progressionScaleN (t*m)) ≤
      smoothPrimeLogMass (progressionScaleN (t*m)) (progressionScaleN (b*m))) :
    ∃ K : ℕ, 2 ≤ K ∧
      (((b*K-1 : ℕ) : ℝ)/((t*K : ℕ) : ℝ) < (b : ℝ)/(t : ℝ)) ∧
      ∀ᶠ m : ℕ in atTop, (c/2)*mangoldtSum (progressionScaleN ((t*K)*m)) ≤
        smoothPrimeLogMass (progressionScaleN ((t*K)*m)) (progressionScaleN ((b*K-1)*m)) := by
  obtain ⟨K,hK,hlog⟩ := exists_cutoff_refinement_length b hb c hc
  have hmul : Tendsto (fun m : ℕ => K*m) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m (by omega : 0<K)) tendsto_id
  have H' : ∀ᶠ m : ℕ in atTop, c*mangoldtSum (progressionScaleN ((t*K)*m)) ≤
      smoothPrimeLogMass (progressionScaleN ((t*K)*m)) (progressionScaleN ((b*K)*m)) := by
    simpa only [mul_assoc] using hmul.eventually H
  have hbK := Nat.le_mul_of_pos_left K hb
  have htK := Nat.le_mul_of_pos_right t (by omega : 0<K)
  have hlev := Nat.mul_le_mul_right K hlevel
  have Hsmall := smoothPrimeLogMass_transfer (b*K-1) (b*K) (t*K)
    (by omega) (Nat.sub_le _ _) (by omega) (by nlinarith only [hlev,hK]) c (c/2)
    (by linarith only [hlog]) H'
  refine ⟨K,hK,?_,Hsmall⟩
  have htR : (0 : ℝ)<t := by exact_mod_cast (show 0<t by omega)
  have hKR : (0 : ℝ)<K := by exact_mod_cast (show 0<K by omega)
  have hsub : ((b*K-1 : ℕ) : ℝ) = (b : ℝ)*K-1 := by
    rw [Nat.cast_sub (show 1 ≤ b*K by omega),Nat.cast_mul,Nat.cast_one]
  rw [hsub,Nat.cast_mul]
  apply (div_lt_div_iff₀ (mul_pos htR hKR) htR).mpr
  nlinarith only [htR]

end Erdos821
