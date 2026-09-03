import Submission.SourceCollisionGrowth

/-!
Positive lower density of the large-prime-factor source, proved using an elementary
prime-counting lower bound and an injective count of prime/cofactor pairs.
This auxiliary estimate does not prove the positive-density cube-Sidon conjecture.
-/

namespace Erdos1206.LargePrimeSourceDensity
open Finset Filter
open scoped Topology Classical

lemma two_pow_le_centralBinom (n : ℕ) : 2^n ≤ n.centralBinom := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hr := Nat.succ_mul_centralBinom_succ n
    have hm := Nat.mul_le_mul_left (2 * (n+1)) ih
    rw [pow_succ]
    nlinarith

lemma centralBinom_le_pow_primeCounting {m : ℕ} (hm : 0 < m) :
    m.centralBinom ≤ (2*m)^(Nat.primeCounting (2*m)) := by
  rw [← Nat.prod_pow_factorization_centralBinom]
  have he : (∏ p ∈ range (2*m+1), p^m.centralBinom.factorization p) =
      ∏ p ∈ (range (2*m+1)).filter Nat.Prime, p^m.centralBinom.factorization p := by
    symm
    apply prod_subset (filter_subset _ _)
    intro p hp hnot
    have hn : ¬p.Prime := by simpa [hp] using hnot
    simp [Nat.factorization_eq_zero_of_not_prime _ hn]
  rw [he]
  calc
    _ ≤ ∏ _p ∈ (range (2*m+1)).filter Nat.Prime, 2*m := by
      apply prod_le_prod (fun _ _ => Nat.zero_le _)
      intro p hp
      exact Nat.pow_factorization_choose_le (by omega)
    _ = _ := by
      simp only [prod_const, Nat.primeCounting, Nat.primeCounting',
        Nat.count_eq_card_filter_range]

/-- A weak, fully elementary form of Chebyshev's lower bound. -/
lemma primeCounting_lower_mul_log {n : ℕ} (hn : 2 ≤ n) :
    Real.log 2 * (n : ℝ) ≤ 4 * Nat.primeCounting n * Real.log n := by
  let m := n/2
  have hm : 0 < m := by dsimp [m]; omega
  have hmn : 2*m ≤ n := Nat.mul_div_le n 2
  have hnm : n ≤ 4*m := by dsimp [m]; omega
  have hpow := (two_pow_le_centralBinom m).trans (centralBinom_le_pow_primeCounting hm)
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2:ℝ)^m)
    (show (2:ℝ)^m ≤ (2*(m:ℝ))^(Nat.primeCounting (2*m)) by exact_mod_cast hpow)
  rw [Real.log_pow, Real.log_pow] at hlog
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmono : (Nat.primeCounting (2*m) : ℝ) * Real.log (2*(m:ℝ)) ≤
      Nat.primeCounting n * Real.log n := by
    apply mul_le_mul
    · exact_mod_cast Nat.monotone_primeCounting hmn
    · apply Real.log_le_log
      · positivity
      · exact_mod_cast hmn
    · apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ 2*m by omega)
    · positivity
  have hnmR : (n : ℝ) ≤ 4*m := by exact_mod_cast hnm
  nlinarith


/-- Counting primes against all small cofactors recovers a linear number of pairs. -/
lemma prime_cofactor_sum_lower {t d : ℕ} (ht : 2 ≤ t) (hd : 2 ≤ d) :
    Real.log 2 * (t^d : ℕ) ≤
      8 * d * (∑ m ∈ Icc 1 t, Nat.primeCounting (t^d/m) : ℕ) := by
  have ht0 : 0 < t := by omega
  have hN : 2*t ≤ t^d := by
    have hh := Nat.pow_le_pow_right ht0 hd
    nlinarith [show t^2 ≤ t^d from hh]
  have hterm (m : ℕ) (hm : m ∈ Icc 1 t) :
      Real.log 2 * (t^d : ℕ) * (m : ℝ)⁻¹ ≤
        8 * Real.log (t^d : ℕ) * Nat.primeCounting (t^d/m) := by
    obtain ⟨hm0,hmt⟩ := mem_Icc.mp hm
    have hq : 2 ≤ t^d/m := (Nat.le_div_iff_mul_le hm0).mpr (by omega)
    have hfloor := Nat.lt_mul_div_succ (t^d) hm0
    have hfloor' : t^d ≤ 2*m*(t^d/m) := by nlinarith
    have hqN : t^d/m ≤ t^d := Nat.div_le_self _ _
    have hl := primeCounting_lower_mul_log hq
    have hlog : Real.log (t^d/m : ℕ) ≤ Real.log (t^d : ℕ) := by
      apply Real.log_le_log
      · exact_mod_cast (show 0 < t^d/m by omega)
      · exact_mod_cast hqN
    have hl' := mul_le_mul_of_nonneg_left hlog
      (show (0:ℝ) ≤ 4*Nat.primeCounting (t^d/m) by positivity)
    have hfR : (t^d : ℕ) ≤ 2*(m:ℝ)*(t^d/m : ℕ) := by exact_mod_cast hfloor'
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hmul := mul_le_mul_of_nonneg_left hfR hl2
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ (by exact_mod_cast hm0 : (0:ℝ) < m)).mpr
    have hh := mul_le_mul_of_nonneg_left (hl.trans hl')
      (show (0:ℝ) ≤ 2*m by positivity)
    nlinarith
  have hs := sum_le_sum (fun m hm => hterm m hm)
  have hH : Real.log t ≤ ∑ m ∈ Icc 1 t, (m : ℝ)⁻¹ := by
    have hh := log_add_one_le_harmonic t
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at hh
    exact (Real.log_le_log (by positivity) (by simp)).trans hh
  have hh := mul_le_mul_of_nonneg_left hH
    (show (0 : ℝ) ≤ Real.log 2 * (t^d : ℕ) by positivity)
  simp only [← mul_sum, ← Nat.cast_sum] at hs
  rw [Nat.cast_pow, Real.log_pow] at hs
  have hlt : 0 < Real.log t := Real.log_pos (by exact_mod_cast ht)
  apply (mul_le_mul_iff_right₀ hlt).mp
  simp only [Nat.cast_pow, Nat.cast_sum] at hh hs ⊢
  nlinarith

noncomputable def primeCofactorPairs (k t : ℕ) : Finset ((m : ℕ) × ℕ) :=
  (Icc 1 t).sigma fun m =>
    ((range (t^(2*k)/m+1)).filter Nat.Prime).filter (fun p => t^(k-1) < p)

lemma prime_cofactor_count_upper (k t : ℕ) :
    (∑ m ∈ Icc 1 t, Nat.primeCounting (t^(2*k)/m)) ≤
      (primeCofactorPairs k t).card + t * t^(k-1) := by
  have hterm (m : ℕ) : Nat.primeCounting (t^(2*k)/m) ≤
      (((range (t^(2*k)/m+1)).filter Nat.Prime).filter
        (fun p => t^(k-1) < p)).card + t^(k-1) := by
    have he := card_filter_add_card_filter_not
      (s := (range (t^(2*k)/m+1)).filter Nat.Prime) (fun p => t^(k-1) < p)
    have hbad : (((range (t^(2*k)/m+1)).filter Nat.Prime).filter
        (fun p => ¬t^(k-1) < p)).card ≤ t^(k-1) := by
      calc
        _ ≤ (Icc 1 (t^(k-1))).card := card_le_card (by
          intro p hp
          simp only [mem_filter, mem_range] at hp
          exact mem_Icc.mpr ⟨hp.1.2.pos, by omega⟩)
        _ = _ := by simp
    simpa only [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
      using (show ((range (t^(2*k)/m+1)).filter Nat.Prime).card ≤ _ from by omega)
  have hh := sum_le_sum (fun m (_ : m ∈ Icc 1 t) => hterm m)
  simpa [primeCofactorPairs, card_sigma, sum_add_distrib] using hh

lemma prime_cofactor_image_injective {k t : ℕ} (hk : 2 ≤ k) :
    Set.InjOn (fun z : (m : ℕ) × ℕ => z.1*z.2) (primeCofactorPairs k t) := by
  intro x hx y hy he
  dsimp only at he
  have hx' := mem_sigma.mp hx
  have hy' := mem_sigma.mp hy
  have hxm := mem_Icc.mp hx'.1
  have hym := mem_Icc.mp hy'.1
  have hxp := mem_filter.mp hx'.2
  have hyp := mem_filter.mp hy'.2
  have hpx : x.2.Prime := (mem_filter.mp hxp.1).2
  have hpy : y.2.Prime := (mem_filter.mp hyp.1).2
  have ht : t ≤ t^(k-1) := Nat.le_self_pow (by omega) t
  have hxy : x.2 ∣ y.1*y.2 := he ▸ dvd_mul_left x.2 x.1
  have hpp : x.2 ∣ y.2 := (hpx.dvd_mul.mp hxy).resolve_left (by
    intro hd
    have := Nat.le_of_dvd hym.1 hd
    omega)
  have hpeq : x.2 = y.2 := (Nat.dvd_prime hpy).mp hpp |>.resolve_left hpx.ne_one
  have hmeq : x.1 = y.1 := by
    rw [hpeq] at he
    exact Nat.eq_of_mul_eq_mul_right hpy.pos he
  exact Sigma.ext hmeq (by simpa [hmeq] using hpeq)

lemma prime_cofactor_image_subset {k t : ℕ} (hk : 2 ≤ k) :
    (primeCofactorPairs k t).image (fun z => z.1*z.2) ⊆
      (range (t^(2*k)+1)).filter (fun n => n ∈ largePrimeSource k) := by
  intro n hn
  obtain ⟨⟨m,p⟩,hmp,rfl⟩ := mem_image.mp hn
  obtain ⟨hm,hp⟩ := mem_sigma.mp hmp
  obtain ⟨hpr,hpt⟩ := mem_filter.mp hp
  obtain ⟨hpN,hprime⟩ := mem_filter.mp hpr
  have hm' := mem_Icc.mp hm
  have hp' : p ≤ t^(2*k)/m := by simpa [mem_range] using hpN
  apply mem_filter.mpr
  constructor
  · exact mem_range.mpr (by
      have hh := (Nat.le_div_iff_mul_le hm'.1).mp hp'
      nlinarith)
  · rw [Nat.mul_comm]
    apply prime_mul_mem_largePrimeSource (by omega) hprime hm'.1
    exact (Nat.pow_le_pow_left hm'.2 _).trans_lt hpt


lemma prime_cofactor_card_le_prefix {k t : ℕ} (hk : 2 ≤ k) :
    (primeCofactorPairs k t).card ≤
      (largePrimeSource k ∩ Set.Iio (t^(2*k)+1)).ncard := by
  have hh := card_le_card (prime_cofactor_image_subset (t := t) hk)
  rw [card_image_of_injOn (prime_cofactor_image_injective hk)] at hh
  convert hh using 1
  rw [← Set.ncard_coe_finset]
  congr 1
  ext n
  simp [and_comm]

/-- A uniform linear lower bound along polynomial cutoffs. -/
lemma source_power_prefix_lower {k t : ℕ} (hk : 2 ≤ k) (ht : 2 ≤ t)
    (hlarge : 32*(k:ℝ) ≤ Real.log 2 * (t^k : ℕ)) :
    (Real.log 2 / (32*k)) * (t^(2*k) : ℕ) ≤
      (largePrimeSource k ∩ Set.Iio (t^(2*k)+1)).ncard := by
  have hs := prime_cofactor_sum_lower ht (show 2 ≤ 2*k by omega)
  have hc := prime_cofactor_count_upper k t
  have hcp := prime_cofactor_card_le_prefix (t := t) hk
  have hpow : t*t^(k-1) = t^k := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ k)]
  rw [hpow] at hc
  have hcR : (∑ m ∈ Icc 1 t, Nat.primeCounting (t^(2*k)/m) : ℕ) ≤
      ((largePrimeSource k ∩ Set.Iio (t^(2*k)+1)).ncard : ℝ) + (t^k : ℕ) := by
    exact_mod_cast hc.trans (Nat.add_le_add_right hcp _)
  have hsR : Real.log 2 * (t^(2*k) : ℕ) ≤
      16*(k:ℝ) * (∑ m ∈ Icc 1 t, Nat.primeCounting (t^(2*k)/m) : ℕ) := by
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hs
    nlinarith only [hs]
  have hlarge' := mul_le_mul_of_nonneg_right hlarge
    (show (0:ℝ) ≤ (t^k : ℕ) by positivity)
  have he : ((t^k : ℕ) : ℝ)^2 = (t^(2*k) : ℕ) := by
    norm_cast
    rw [← pow_mul, Nat.mul_comm k 2]
  have he' : Real.log 2 * (t^k : ℕ) * (t^k : ℕ) =
      Real.log 2 * (t^(2*k) : ℕ) := by nlinarith [congrArg (fun z => Real.log 2*z) he]
  rw [he'] at hlarge'
  have hcR' := mul_le_mul_of_nonneg_left hcR (show (0:ℝ) ≤ 16*k by positivity)
  have hbound : Real.log 2 * (t^(2*k) : ℕ) ≤
      32*(k:ℝ) * (largePrimeSource k ∩ Set.Iio (t^(2*k)+1)).ncard := by
    nlinarith
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ (by positivity : (0:ℝ) < 32*k)).mpr (by nlinarith [hbound])

/-- Linear prefix bounds at all sufficiently large power cutoffs imply positive
lower natural density. The interpolation loses only a fixed factor `2^d`. -/
lemma positive_lowerDensity_of_power_prefix {S : Set ℕ} {a : ℝ} {d T : ℕ}
    (ha : 0 < a) (hd : 0 < d)
    (hcount : ∀ t ≥ T, a*(t^d : ℕ) ≤ (S ∩ Set.Iio (t^d+1)).ncard) :
    0 < S.lowerDensity := by
  let δ : ℝ := a / (2:ℝ)^d
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hevent : ∀ᶠ N : ℕ in atTop, δ ≤ S.partialDensity Set.univ N := by
    apply eventually_atTop.mpr
    refine ⟨(max T 1)^d+1, fun N hN => ?_⟩
    let t := Nat.findGreatest (fun t => t^d+1 ≤ N) N
    have hTN : max T 1 ≤ N :=
      (Nat.le_self_pow (n := d) (by omega) (max T 1)).trans ((Nat.le_succ _).trans hN)
    have hT : max T 1 ≤ t := Nat.le_findGreatest hTN hN
    have ht : 0 < t := by omega
    have hspec : t^d+1 ≤ N :=
      Nat.findGreatest_spec (P := fun t => t^d+1 ≤ N) hTN hN
    have hnext : N ≤ (t+1)^d := by
      by_cases hh : t+1 ≤ N
      · have := Nat.findGreatest_is_greatest (P := fun t => t^d+1 ≤ N)
          (show t < t+1 by omega) hh
        omega
      · exact (show N ≤ t+1 by omega).trans (Nat.le_self_pow (by omega) _)
    have hscale : N ≤ 2^d*t^d := by
      calc
        N ≤ (t+1)^d := hnext
        _ ≤ (2*t)^d := Nat.pow_le_pow_left (by omega) d
        _ = _ := mul_pow _ _ _
    have hpre := hcount t (by omega)
    have hmono : (S ∩ Set.Iio (t^d+1)).ncard ≤ (S ∩ Set.Iio N).ncard := by
      apply Set.ncard_le_ncard
      · exact Set.inter_subset_inter_right _ (Set.Iio_subset_Iio hspec)
      · exact Set.Finite.inter_of_right (Set.finite_Iio N) S
    have hmonoR : ((S ∩ Set.Iio (t^d+1)).ncard : ℝ) ≤ (S ∩ Set.Iio N).ncard := by
      exact_mod_cast hmono
    have hscaleR : (N:ℝ) ≤ (2:ℝ)^d*(t^d : ℕ) := by exact_mod_cast hscale
    have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
    apply (le_div_iff₀ hN0).mpr
    dsimp [δ]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 2^d)).mpr
    have hh := mul_le_mul_of_nonneg_left hscaleR ha.le
    have hh' := mul_le_mul_of_nonneg_right (hpre.trans hmonoR)
      (show (0:ℝ) ≤ 2^d by positivity)
    nlinarith
  have hlim : δ ≤ S.lowerDensity := le_liminf_of_le
    (isCoboundedUnder_ge_of_le atTop (fun n => Set.partialDensity_le_one S Set.univ n)) hevent
  exact hδ.trans_le hlim

/-- The set of integers with a prime factor exceeding `n^((k-1)/k)` has
positive lower natural density. -/
theorem largePrimeSource_lowerDensity_pos {k : ℕ} (hk : 2 ≤ k) :
    0 < (largePrimeSource k).lowerDensity := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨T,hT⟩ := exists_nat_gt (32*(k:ℝ)/Real.log 2)
  apply positive_lowerDensity_of_power_prefix
    (a := Real.log 2 / (32*k)) (d := 2*k) (T := max T 2)
    (by positivity) (by omega)
  intro t ht
  apply source_power_prefix_lower hk (by omega)
  have htT : T ≤ t^k := (show T ≤ t by omega).trans (Nat.le_self_pow (by omega) t)
  have htTR : (T:ℝ) ≤ (t^k : ℕ) := by exact_mod_cast htT
  have hh := (div_lt_iff₀ hl2).mp hT
  nlinarith

/-- The previous conditional source-count theorem is now unconditional.
This is about edge counts, not independence density. -/
theorem largePrimeSource_collision_count_superlinear {k : ℕ} (hk : 0 < k) (C : ℝ) :
    ∃ M : ℕ, ∀ N ≥ M,
      C*N < ((sourceCollisionsUpTo (largePrimeSource k) N).card : ℝ) :=
  largePrimeSource_prefix_superlinear hk
    (largePrimeSource_lowerDensity_pos (by omega)) C

#print axioms largePrimeSource_lowerDensity_pos
#print axioms largePrimeSource_collision_count_superlinear
end Erdos1206.LargePrimeSourceDensity
