import Submission.Explore
import Submission.DivisorExplore

/-! Exact small-divisor/large-divisor decomposition of the prime-factor sign. -/

namespace Erdos371

lemma squarefree_prod_primes (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p) :
    Squarefree (∏ p ∈ s, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hs p hp) (hs q hq)).mpr hpq)
  · exact fun p hp => (hs p hp).squarefree

lemma sum_squarefree_divisors_eq_powerset (n : ℕ) (hn : n ≠ 0) (f : Finset ℕ → ℝ) :
    ∑ d ∈ n.divisors, (if Squarefree d then f d.primeFactors else 0) =
      ∑ t ∈ n.primeFactors.powerset, f t := by
  classical
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun t _ => ∏ p ∈ t, p) ?_ ?_ ?_ ?_
  · intro t ht
    have hts := Finset.mem_powerset.mp ht
    have hp : ∀ p ∈ t, Nat.Prime p := fun p hp => Nat.prime_of_mem_primeFactors (hts hp)
    refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_, hn⟩,
      squarefree_prod_primes t hp⟩
    exact (Finset.prod_dvd_prod_of_subset t n.primeFactors id hts).trans
      (Nat.prod_primeFactors_dvd n)
  · intro t ht u hu heq
    have ht' : ∀ p ∈ t, Nat.Prime p := fun p hp =>
      Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp ht hp)
    have hu' : ∀ p ∈ u, Nat.Prime p := fun p hp =>
      Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp hu hp)
    simpa only [Nat.primeFactors_prod ht', Nat.primeFactors_prod hu'] using
      congrArg Nat.primeFactors heq
  · intro d hd
    obtain ⟨hdn, hds⟩ := Finset.mem_filter.mp hd
    refine ⟨d.primeFactors, Finset.mem_powerset.mpr
      (Nat.primeFactors_mono (Nat.mem_divisors.mp hdn).1 hn), ?_⟩
    exact Nat.prod_primeFactors_of_squarefree hds
  · intro t ht
    have ht' : ∀ p ∈ t, Nat.Prime p := fun p hp =>
      Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp ht hp)
    rw [Nat.primeFactors_prod ht']

lemma min_primeFactors_eq_minFac (n : ℕ) (hn : 1 < n) :
    n.primeFactors.min' (Nat.nonempty_primeFactors.mpr hn) = n.minFac := by
  apply le_antisymm
  · exact Finset.min'_le _ _ (Nat.mem_primeFactors.mpr
      ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd n, by omega⟩)
  · exact Nat.minFac_le_of_dvd
      (Nat.prime_of_mem_primeFactors (Finset.min'_mem _ _)).two_le
      (Nat.dvd_of_mem_primeFactors (Finset.min'_mem _ _))

noncomputable def leastFactorTerm (f : ℕ → ℝ) (d : ℕ) : ℝ :=
  if Squarefree d ∧ 1 < d then (-1 : ℝ)^d.primeFactors.card * f d.minFac else 0

lemma leastFactorTerm_eq (f : ℕ → ℝ) (d : ℕ) :
    leastFactorTerm f d = if Squarefree d then subsetMinTerm f d.primeFactors else 0 := by
  classical
  by_cases hd : Squarefree d
  · by_cases hd1 : 1 < d
    · simp only [leastFactorTerm, if_pos hd, and_self, hd, hd1, if_true,
        subsetMinTerm, dif_pos (Nat.nonempty_primeFactors.mpr hd1), min_primeFactors_eq_minFac d hd1]
    · have hemp : d.primeFactors = ∅ := by
        apply Nat.primeFactors_eq_empty.mpr
        omega
      simp [leastFactorTerm, hd, hd1, subsetMinTerm, hemp]
  · simp [leastFactorTerm, hd]

lemma alladi_divisors (n : ℕ) (hn : 1 < n) (f : ℕ → ℝ) :
    ∑ d ∈ n.divisors, leastFactorTerm f d = -f (Nat.maxPrimeFac n) := by
  simp_rw [leastFactorTerm_eq]
  rw [sum_squarefree_divisors_eq_powerset n (by omega), alladi_maxPrimeFac n hn]

noncomputable def orientedDivisorTerm (d n : ℕ) : ℝ :=
  if d ∣ n * (n + 1) then leastFactorTerm (fun p => if p ∣ n + 1 then 1 else -1) d else 0

lemma orientedDivisorTerm_le_one (d n : ℕ) : ‖orientedDivisorTerm d n‖ ≤ 1 := by
  classical
  unfold orientedDivisorTerm leastFactorTerm
  dsimp only
  split_ifs <;> simp [norm_mul, norm_pow]

lemma orientedDivisorTerm_eq_zero_of_le_one (d n : ℕ) (hd : d ≤ 1) :
    orientedDivisorTerm d n = 0 := by
  classical
  simp [orientedDivisorTerm, leastFactorTerm, not_lt.mpr hd]

lemma orientedDivisorTerm_periodic (d : ℕ) : Function.Periodic (orientedDivisorTerm d) d := by
  classical
  intro n
  have hn : Nat.ModEq d (n + d) n := by simp [Nat.ModEq]
  have hm := (hn.mul (hn.add_right 1)).dvd_iff (dvd_refl d)
  have hp := (hn.add_right 1).dvd_iff (Nat.minFac_dvd d)
  simp only [orientedDivisorTerm, leastFactorTerm, hm, hp]

lemma reflected_polynomial_modEq (d a b : ℕ) (h : a + b + 1 = d) :
    Nat.ModEq d (a * (a + 1)) (b * (b + 1)) := by
  rw [Nat.modEq_iff_dvd]
  refine ⟨(b : ℤ) - a, ?_⟩
  rw [← h]
  push_cast
  ring

lemma reflected_divisor_color (d a b : ℕ) (h : a + b + 1 = d)
    (hd : 1 < d) (hr : d ∣ a * (a + 1)) :
    (d.minFac ∣ b + 1) ↔ ¬ (d.minFac ∣ a + 1) := by
  have hp := Nat.minFac_prime (n := d) (by omega)
  have hpab : d.minFac ∣ a + (b + 1) := by
    rw [← Nat.add_assoc, h]
    exact Nat.minFac_dvd d
  have hab : (d.minFac ∣ b + 1) ↔ (d.minFac ∣ a) := by
    constructor
    · intro hb
      exact (Nat.dvd_add_iff_left hb).mpr hpab
    · intro ha
      exact (Nat.dvd_add_iff_right ha).mpr hpab
  rw [hab]
  have hpaa := hp.dvd_mul.mp ((Nat.minFac_dvd d).trans hr)
  constructor
  · intro ha ha1
    exact hp.not_dvd_one ((Nat.dvd_add_iff_right ha).mpr ha1)
  · intro ha1
    exact hpaa.resolve_right ha1

lemma orientedDivisorTerm_reflection (d n : ℕ) (hn : n < d) :
    orientedDivisorTerm d (d - 1 - n) = -orientedDivisorTerm d n := by
  classical
  by_cases hd : 1 < d
  · have he : n + (d - 1 - n) + 1 = d := by omega
    have hm := (reflected_polynomial_modEq d n (d - 1 - n) he).dvd_iff (dvd_refl d)
    by_cases hr : d ∣ n * (n + 1)
    · have hr' := hm.mp hr
      have hc := reflected_divisor_color d n (d - 1 - n) he hd hr
      simp only [orientedDivisorTerm, if_pos hr, if_pos hr', leastFactorTerm, hc]
      by_cases hsq : Squarefree d <;> by_cases hp : d.minFac ∣ n + 1 <;>
        simp [hsq, hd, hp]
    · have hr' : ¬d ∣ (d - 1 - n) * (d - 1 - n + 1) := fun h => hr (hm.mpr h)
      simp only [orientedDivisorTerm, if_neg hr, if_neg hr', neg_zero]
  · rw [orientedDivisorTerm_eq_zero_of_le_one _ _ (by omega),
      orientedDivisorTerm_eq_zero_of_le_one _ _ (by omega), neg_zero]

lemma orientedDivisorTerm_mean_zero (d : ℕ) :
    ∑ n ∈ Finset.range d, orientedDivisorTerm d n = 0 := by
  have he := Finset.sum_range_reflect (orientedDivisorTerm d) d
  have hf : ∑ n ∈ Finset.range d, orientedDivisorTerm d (d - 1 - n) =
      -(∑ n ∈ Finset.range d, orientedDivisorTerm d n) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun n hn =>
      orientedDivisorTerm_reflection d n (Finset.mem_range.mp hn)
  linarith

lemma orientedDivisorTerm_prefix_bound (d N : ℕ) :
    ‖∑ n ∈ Finset.range N, orientedDivisorTerm d n‖ ≤ d := by
  by_cases hd : 0 < d
  · exact periodic_sum_zero_bound (orientedDivisorTerm d) d hd
      (orientedDivisorTerm_periodic d) (orientedDivisorTerm_mean_zero d)
      (orientedDivisorTerm_le_one d) N
  · have hd0 : d = 0 := by omega
    simp only [hd0, orientedDivisorTerm_eq_zero_of_le_one 0 _ (by omega),
      Finset.sum_const_zero, norm_zero, Nat.cast_zero, le_refl]


lemma sum_orientedDivisorTerm (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ (n * (n + 1)).divisors, orientedDivisorTerm d n = -factorSign n := by
  classical
  have he : (∑ d ∈ (n * (n + 1)).divisors, orientedDivisorTerm d n) =
      -(if Nat.maxPrimeFac (n * (n + 1)) ∣ n + 1 then (1 : ℝ) else -1) := by
    calc
      _ = ∑ d ∈ (n * (n + 1)).divisors,
          leastFactorTerm (fun p => if p ∣ n + 1 then 1 else -1) d := by
        apply Finset.sum_congr rfl
        intro d hd
        simp only [orientedDivisorTerm, if_pos (Nat.mem_divisors.mp hd).1]
      _ = _ := alladi_divisors (n * (n + 1)) (by nlinarith) _
  rw [he, Nat.maxPrimeFac_mul hn.ne' (by omega)]
  by_cases h1 : n = 1
  · subst n
    norm_num [factorSign, predicateSign, Nat.prime_two.maxPrimeFac_eq_self]
  · have hpn : ¬ Nat.maxPrimeFac n ∣ n + 1 := by
      intro hd
      exact (Nat.prime_maxPrimeFac_of_one_lt n (by omega)).not_dvd_one
        ((Nat.dvd_add_iff_right Nat.maxPrimeFac_dvd).mpr hd)
    by_cases h : Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1)
    · simp only [max_eq_right h.le, if_pos Nat.maxPrimeFac_dvd, factorSign,
        predicateSign, if_pos h]
    · simp only [max_eq_left (le_of_not_gt h), if_neg hpn, factorSign, predicateSign, if_neg h]

noncomputable def smallDivisorSum (D n : ℕ) : ℝ :=
  ∑ d ∈ Finset.range (D + 1), orientedDivisorTerm d n

noncomputable def largeDivisorTail (D n : ℕ) : ℝ :=
  ∑ d ∈ (n * (n + 1)).divisors with D < d, orientedDivisorTerm d n

lemma smallDivisorSum_eq (D n : ℕ) (hn : 0 < n) :
    smallDivisorSum D n =
      ∑ d ∈ (n * (n + 1)).divisors with d ≤ D, orientedDivisorTerm d n := by
  classical
  have hs : (Finset.range (D + 1)).filter (fun d => d ∣ n * (n + 1)) =
      (n * (n + 1)).divisors.filter (fun d => d ≤ D) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors]
    constructor
    · rintro ⟨hD, hd⟩
      exact ⟨⟨hd, Nat.mul_ne_zero hn.ne' (by omega)⟩, by omega⟩
    · rintro ⟨⟨hd, _⟩, hD⟩
      exact ⟨by omega, hd⟩
  calc
    _ = ∑ d ∈ Finset.range (D + 1),
        if d ∣ n * (n + 1) then orientedDivisorTerm d n else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      by_cases h : d ∣ n * (n + 1) <;> simp [orientedDivisorTerm, h]
    _ = ∑ d ∈ (Finset.range (D + 1)).filter (fun d => d ∣ n * (n + 1)),
        orientedDivisorTerm d n := (Finset.sum_filter _ _).symm
    _ = _ := by rw [hs]

lemma small_add_tail (D n : ℕ) (hn : 0 < n) :
    smallDivisorSum D n + largeDivisorTail D n = -factorSign n := by
  classical
  rw [smallDivisorSum_eq D n hn, largeDivisorTail]
  have he := Finset.sum_filter_add_sum_filter_not (s := (n * (n + 1)).divisors)
    (fun d => d ≤ D) (orientedDivisorTerm · n)
  simp only [not_le] at he
  rw [he, sum_orientedDivisorTerm n hn]

lemma orientedDivisorTerm_shifted_prefix_bound (d N : ℕ) :
    ‖∑ n ∈ Finset.range N, orientedDivisorTerm d (n + 1)‖ ≤ (d : ℝ) + 1 := by
  have he : (∑ n ∈ Finset.range N, orientedDivisorTerm d (n + 1)) =
      (∑ n ∈ Finset.range (N + 1), orientedDivisorTerm d n) - orientedDivisorTerm d 0 := by
    rw [Finset.sum_range_succ']
    ring
  rw [he]
  exact (norm_sub_le _ _).trans
    (add_le_add (orientedDivisorTerm_prefix_bound d (N + 1)) (orientedDivisorTerm_le_one d 0))

lemma smallDivisorSum_prefix_bound (D N : ℕ) :
    ‖∑ n ∈ Finset.range N, smallDivisorSum D (n + 1)‖ ≤ (D + 1 : ℝ)^2 := by
  classical
  unfold smallDivisorSum
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ d ∈ Finset.range (D + 1),
        ‖∑ n ∈ Finset.range N, orientedDivisorTerm d (n + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.range (D + 1), ((d : ℝ) + 1) :=
      Finset.sum_le_sum fun d _ => orientedDivisorTerm_shifted_prefix_bound d N
    _ ≤ ∑ d ∈ Finset.range (D + 1), (D + 1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hd' : d ≤ D := by have := Finset.mem_range.mp hd; omega
      exact_mod_cast Nat.add_le_add_right hd' 1
    _ = _ := by simp [pow_two]; ring

open Filter in
lemma smallDivisorSum_quarterRoot_tendsto :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N,
      smallDivisorSum N.sqrt.sqrt (n + 1)) / N) atTop (nhds 0) := by
  have hsqrt (N : ℕ) : (N.sqrt : ℝ) ≤ Real.sqrt N := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast Nat.sqrt_le' N
  have hb (N : ℕ) : ‖(∑ n ∈ Finset.range N, smallDivisorSum N.sqrt.sqrt (n + 1)) / N‖ ≤
      3 * (Real.sqrt N)⁻¹ + 1 / N := by
    rw [norm_div, Real.norm_natCast]
    calc
      _ ≤ (N.sqrt.sqrt + 1 : ℝ)^2 / N := div_le_div_of_nonneg_right
        (smallDivisorSum_prefix_bound N.sqrt.sqrt N) (Nat.cast_nonneg N)
      _ ≤ (3 * N.sqrt + 1 : ℝ) / N := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
        have h₁ : (N.sqrt.sqrt : ℝ)^2 ≤ N.sqrt := by exact_mod_cast Nat.sqrt_le' N.sqrt
        have h₂ : (N.sqrt.sqrt : ℝ) ≤ N.sqrt := by exact_mod_cast Nat.sqrt_le_self N.sqrt
        nlinarith
      _ ≤ (3 * Real.sqrt N + 1) / N := by gcongr; exact hsqrt N
      _ = _ := by rw [add_div, mul_div_assoc, Real.sqrt_div_self]
  have hi : Tendsto (fun N : ℕ => (Real.sqrt N)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  apply squeeze_zero_norm hb
  simpa using (hi.const_mul 3).add tendsto_one_div_atTop_nhds_zero_nat


lemma factorSign_sum_eq_signed_count (N : ℕ) :
    (∑ n ∈ Finset.range N, factorSign n) = (risingCount N : ℝ) - fallingCount N := by
  change (∑ n ∈ Finset.range N, predicateSign
    (fun n => Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1)) n) = _
  rw [predicateSign_sum]
  change 2 * (risingCount N : ℝ) - N = _
  have hc : (risingCount N : ℝ) + fallingCount N = N := by
    exact_mod_cast comparison_count_partition N
  linarith

lemma factorSign_norm (n : ℕ) : ‖factorSign n‖ = 1 := by
  unfold factorSign predicateSign
  split_ifs <;> norm_num

open Filter in
lemma density_iff_shifted_sign_average :
    {n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}.HasDensity (1 / 2) ↔
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, factorSign (n + 1)) / N)
        atTop (nhds 0) := by
  rw [density_iff_signed_count]
  simp_rw [← factorSign_sum_eq_signed_count]
  have he (N : ℕ) : (∑ n ∈ Finset.range N, factorSign (n + 1)) -
      (∑ n ∈ Finset.range N, factorSign n) = factorSign N - factorSign 0 := by
    have h := Finset.sum_range_succ' factorSign N
    rw [Finset.sum_range_succ] at h
    linarith
  have hd : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, factorSign (n + 1)) / N -
      (∑ n ∈ Finset.range N, factorSign n) / N) atTop (nhds 0) := by
    apply squeeze_zero_norm (a := fun N : ℕ => 2 / N)
    · intro N
      rw [← sub_div, he N, norm_div, Real.norm_natCast]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
      have h := norm_sub_le (factorSign N) (factorSign 0)
      simpa only [factorSign_norm, one_add_one_eq_two] using h
    · exact tendsto_const_div_atTop_nhds_zero_nat 2
  constructor
  · intro h
    simpa only [sub_add_cancel, add_zero] using hd.add h
  · intro h
    have ht := h.sub hd
    simp only [sub_zero] at ht
    apply ht.congr
    intro N
    ring

open Filter in
/-- The original conjecture is equivalent to cancellation of one explicit
large-divisor remainder. The contribution of all divisors up to the fourth
root of the counting interval has already been proved negligible. -/
theorem density_iff_large_divisor_tail :
    {n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}.HasDensity (1 / 2) ↔
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N,
        largeDivisorTail N.sqrt.sqrt (n + 1)) / N) atTop (nhds 0) := by
  rw [density_iff_shifted_sign_average]
  have he (N : ℕ) :
      (∑ n ∈ Finset.range N, smallDivisorSum N.sqrt.sqrt (n + 1)) / N +
        (∑ n ∈ Finset.range N, largeDivisorTail N.sqrt.sqrt (n + 1)) / N =
      -((∑ n ∈ Finset.range N, factorSign (n + 1)) / N) := by
    rw [← add_div, ← Finset.sum_add_distrib]
    simp_rw [small_add_tail _ _ (Nat.zero_lt_succ _)]
    rw [Finset.sum_neg_distrib, neg_div]
  constructor
  · intro h
    have ht := h.neg.sub smallDivisorSum_quarterRoot_tendsto
    simp only [neg_zero, sub_zero] at ht
    apply ht.congr
    intro N
    linarith [he N]
  · intro h
    have ht := (smallDivisorSum_quarterRoot_tendsto.add h).neg
    simp only [add_zero, neg_zero] at ht
    apply ht.congr
    intro N
    linarith [he N]


lemma leastFactorTerm_eq_moebius (f : ℕ → ℝ) (d : ℕ) :
    leastFactorTerm f d = if 1 < d then
      (ArithmeticFunction.moebius d : ℝ) * f d.minFac else 0 := by
  classical
  by_cases hd : Squarefree d
  · have hc : d.primeFactors.card = ArithmeticFunction.cardFactors d := by
      rw [ArithmeticFunction.cardFactors_apply, ← Nat.toFinset_factors]
      exact List.toFinset_card_of_nodup hd.nodup_primeFactorsList
    simp [leastFactorTerm, hd, ArithmeticFunction.moebius_apply_of_squarefree hd, ← hc]
  · simp [leastFactorTerm, hd, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd]

lemma prime_orientedDivisorTerm (p n : ℕ) (hp : Nat.Prime p) :
    orientedDivisorTerm p n =
      (if p ∣ n then (1 : ℝ) else 0) - (if p ∣ n + 1 then (1 : ℝ) else 0) := by
  classical
  have hnot : ¬(p ∣ n ∧ p ∣ n + 1) := fun h =>
    hp.not_dvd_one ((Nat.dvd_add_iff_right h.1).mpr h.2)
  rw [orientedDivisorTerm, leastFactorTerm_eq_moebius]
  simp only [hp.dvd_mul, if_pos hp.one_lt, ArithmeticFunction.moebius_apply_prime hp,
    hp.minFac_eq, Int.cast_neg, Int.cast_one]
  by_cases h₁ : p ∣ n <;> by_cases h₂ : p ∣ n + 1 <;> simp_all

lemma prime_orientedDivisorTerm_prefix (p N : ℕ) (hp : Nat.Prime p) :
    (∑ n ∈ Finset.range N, orientedDivisorTerm p (n + 1)) =
      -(if p ∣ N + 1 then (1 : ℝ) else 0) := by
  classical
  simp_rw [prime_orientedDivisorTerm p _ hp]
  induction N with
  | zero => simp [hp.not_dvd_one]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    ring

lemma nat_sq_le_two_pow (k : ℕ) (hk : 4 ≤ k) : k^2 ≤ 2^k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ (2 : ℕ) k]
    have h := Nat.mul_le_mul_left k hk
    nlinarith

lemma primeFactors_card_le_sqrt_add_three (n : ℕ) (hn : 0 < n) :
    n.primeFactors.card ≤ n.sqrt + 3 := by
  have hp : 2^n.primeFactors.card ≤ n := by
    apply (Finset.pow_card_le_prod n.primeFactors id 2
      (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)).trans
    exact Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
  by_cases hc : 4 ≤ n.primeFactors.card
  · exact (Nat.le_sqrt'.mpr ((nat_sq_le_two_pow _ hc).trans hp)).trans (by omega)
  · omega

/-- Prime-only terms telescope, even if the chosen finite set of primes varies
arbitrarily with the counting interval. -/
lemma prime_subset_prefix_bound (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, ∑ p ∈ S, orientedDivisorTerm p (n + 1)‖ ≤ (N.sqrt : ℝ) + 4 := by
  classical
  rw [Finset.sum_comm]
  have he : (∑ p ∈ S, ∑ n ∈ Finset.range N, orientedDivisorTerm p (n + 1)) =
      -((S.filter (fun p => p ∣ N + 1)).card : ℝ) := by
    simp_rw [Finset.sum_congr rfl (fun p hp => prime_orientedDivisorTerm_prefix p N (hS p hp))]
    rw [Finset.sum_neg_distrib]
    congr 1
    simp only [Finset.sum_boole]
  rw [he, norm_neg, Real.norm_natCast]
  have hsub : S.filter (fun p => p ∣ N + 1) ⊆ (N + 1).primeFactors := by
    intro p hp
    obtain ⟨hpS, hpN⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hS p hpS, hpN, by omega⟩
  have hc := (Finset.card_le_card hsub).trans (primeFactors_card_le_sqrt_add_three (N + 1) (by omega))
  have hs := Nat.sqrt_succ_le_succ_sqrt N
  change (N + 1).sqrt ≤ N.sqrt + 1 at hs
  exact_mod_cast (show (S.filter (fun p => p ∣ N + 1)).card ≤ N.sqrt + 4 by omega)

open Filter in
lemma prime_subset_average_tendsto_zero (S : ℕ → Finset ℕ)
    (hS : ∀ N p, p ∈ S N → Nat.Prime p) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, ∑ p ∈ S N,
      orientedDivisorTerm p (n + 1)) / N) atTop (nhds 0) := by
  have hsqrt (N : ℕ) : (N.sqrt : ℝ) ≤ Real.sqrt N := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast Nat.sqrt_le' N
  have hb (N : ℕ) :
      ‖(∑ n ∈ Finset.range N, ∑ p ∈ S N, orientedDivisorTerm p (n + 1)) / N‖ ≤
        (Real.sqrt N)⁻¹ + 4 / N := by
    rw [norm_div, Real.norm_natCast]
    calc
      _ ≤ ((N.sqrt : ℝ) + 4) / N := div_le_div_of_nonneg_right
        (prime_subset_prefix_bound (S N) (hS N) N) (Nat.cast_nonneg N)
      _ ≤ (Real.sqrt N + 4) / N := by gcongr; exact hsqrt N
      _ = _ := by rw [add_div, Real.sqrt_div_self]
  have hi : Tendsto (fun N : ℕ => (Real.sqrt N)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  apply squeeze_zero_norm hb
  simpa using hi.add (tendsto_const_div_atTop_nhds_zero_nat (4 : ℝ))


/-- The largest divisor in the remainder contributes an alternating two-point
Möbius correlation. This identity alone does not estimate that correlation. -/
lemma top_divisor_term_moebius (n : ℕ) (hn : 0 < n) :
    orientedDivisorTerm (n * (n + 1)) n =
      (if 2 ∣ n then (-1 : ℝ) else 1) *
        (ArithmeticFunction.moebius n : ℝ) * (ArithmeticFunction.moebius (n + 1) : ℝ) := by
  classical
  have h2 : 2 ∣ n * (n + 1) := by
    rcases (show 2 ∣ n ∨ 2 ∣ n + 1 by omega) with h | h
    · exact dvd_mul_of_dvd_left h (n + 1)
    · exact dvd_mul_of_dvd_right h n
  have hmin : (n * (n + 1)).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr h2
  rw [orientedDivisorTerm, if_pos (dvd_refl _), leastFactorTerm_eq_moebius,
    if_pos (show 1 < n * (n + 1) by nlinarith), hmin,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by simp)]
  push_cast
  by_cases h : 2 ∣ n
  · have h' : ¬2 ∣ n + 1 := by omega
    simp only [if_pos h, if_neg h']
    ring
  · have h' : 2 ∣ n + 1 := by omega
    simp only [if_neg h, if_pos h']
    ring

#print axioms alladi_divisors
#print axioms small_add_tail
#print axioms smallDivisorSum_quarterRoot_tendsto
#print axioms density_iff_large_divisor_tail
#print axioms prime_subset_average_tendsto_zero
#print axioms top_divisor_term_moebius

end Erdos371
