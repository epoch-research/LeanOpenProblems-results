import Submission.FixedRoughFactorCount
import Submission.MappedSquarefreeDivisorExpansion
import Submission.AsymmetricDiagonalBudget

/-! Repeated prime factors can be removed from the growing-roughness
almost-prime theorem. Squarefree almost-prime outputs are not asserted
to be prime. -/
namespace Erdos972SquarefreeRoughAlmostPrime

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972PrimePowerError Erdos972PrimeAlmostPrime
open Erdos972PrimeRoughOutputs Erdos972GrowingCoprimeCandidates
open Erdos972EfficientPrimeAlmostPrime Erdos972FourthPowerAlmostPrime
open Erdos972MappedSquarefreeDivisorExpansion Erdos972SquarefreeDivisorExpansion
open Erdos972FixedRoughFactorCount Erdos972ChebyshevRowMean

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 6145
attribute [local irreducible] quarterRoot fourthConstant
  Erdos972EfficientSieveScale.fastRoot Erdos972PolynomialRowScales.root64

lemma squarefreeTruncation_eq_one_of_rough {q Z : ℕ} (hZ : 0 < Z)
    (hc : q.Coprime Z.factorial) : squarefreeTruncation Z q = 1 := by
  classical
  unfold squarefreeTruncation
  rw [sum_eq_single 1]
  · simp
  · intro d hd hd1
    have hnot : ¬ d^2 ∣ q := by
      intro h
      have hdq : d ∣ q := (show d ∣ d^2 by simp [pow_two]).trans h
      exact hd1 (Nat.eq_one_of_dvd_coprimes hc hdq
        (Nat.dvd_factorial (mem_Ioc.mp hd).1 (mem_Ioc.mp hd).2))
    simp [hnot]
  · intro h
    exact (h (mem_Ioc.mpr ⟨by decide, hZ⟩)).elim

noncomputable def squarefreeRoughInputs (α : ℝ) (Z N : ℕ) : Finset ℕ := by
  classical
  exact (Ioc 0 N).filter (fun p => p.Prime ∧
    (floorMul α p).Coprime Z.factorial ∧ Squarefree (floorMul α p))

noncomputable def squarefreeRoughWeight (α : ℝ) (Z N : ℕ) : ℝ :=
  ∑ p ∈ squarefreeRoughInputs α Z N, Real.log p

lemma squarefreeRoughWeight_eq (α : ℝ) (Z N : ℕ) :
    squarefreeRoughWeight α Z N =
      ∑ p ∈ (Ioc 0 N).filter
        (fun p => p.Prime ∧ (floorMul α p).Coprime Z.factorial),
          Real.log p * |(moebius (floorMul α p) : ℝ)| := by
  classical
  simp only [squarefreeRoughWeight, squarefreeRoughInputs, sum_filter]
  apply sum_congr rfl
  intro p hp
  by_cases h : p.Prime ∧ (floorMul α p).Coprime Z.factorial
  · by_cases hs : Squarefree (floorMul α p)
    · simp [h.1, hs]
    · simp [h.1, hs]
  · have hh : ¬ (p.Prime ∧ (floorMul α p).Coprime Z.factorial ∧
        Squarefree (floorMul α p)) := fun hp => h ⟨hp.1, hp.2.1⟩
    simp [h, hh]

/-- The loss from removing repeated factors has a summable square-divisor
tail. The output cap, and therefore its factor alpha, is retained. -/
theorem squarefree_rough_weight_loss {α : ℝ} (hα : 1 ≤ α) {N Z : ℕ}
    (hZ : 0 < Z) (hZN : Z ≤ N) :
    coprimePrimeWeight α Z.factorial N - squarefreeRoughWeight α Z N ≤
      Real.log N*(floorMul α N : ℝ)/Z := by
  classical
  let S := (Ioc 0 N).filter
    (fun p => p.Prime ∧ (floorMul α p).Coprime Z.factorial)
  have hh := mapped_squarefree_tail S (fun p => Real.log p) (floorMul α)
    hZ (hZN.trans (self_le_floorMul hα N)) (Real.log_natCast_nonneg N)
    (floorMul_strictMono hα).injective.injOn
    (by
      intro p hp
      have hpI := (mem_filter.mp hp).1
      exact mem_Ioc.mpr ⟨floorMul_pos hα (mem_Ioc.mp hpI).1,
        (floorMul_strictMono hα).monotone (mem_Ioc.mp hpI).2⟩)
    (by intro p hp; exact Real.log_natCast_nonneg p)
    (by intro p hp; exact log_input_le (mem_filter.mp hp).1)
  have ht : (∑ p ∈ S, Real.log p * squarefreeTruncation Z (floorMul α p)) =
      coprimePrimeWeight α Z.factorial N := by
    unfold coprimePrimeWeight
    apply sum_congr rfl
    intro p hp
    rw [squarefreeTruncation_eq_one_of_rough hZ (mem_filter.mp hp).2.2, mul_one]
  rw [ht] at hh
  change |(∑ p ∈ (Ioc 0 N).filter
    (fun p => p.Prime ∧ (floorMul α p).Coprime Z.factorial),
      Real.log p * |(moebius (floorMul α p) : ℝ)|) - _| ≤ _ at hh
  rw [← squarefreeRoughWeight_eq] at hh
  exact (abs_sub_le_iff.mp hh).2

lemma quarterRoot_log_div_tendsto (C : ℝ) (hC : 0 < C) (k : ℕ) :
    Tendsto (fun u : ℕ => C*(1+Real.log (u+1:ℕ))^k/(quarterRoot u : ℝ))
      atTop (𝓝 0) := by
  have hh := Erdos972AsymmetricDiagonalBudget.cutoff_log_div_tendsto
    (C*2^k) (by positivity) k
  apply squeeze_zero_norm' _ hh
  filter_upwards [eventually_ge_atTop (1:ℕ)] with u hu
  have hF : 1 ≤ Erdos972EfficientSieveScale.fastRoot u :=
    (Erdos972EfficientSieveScale.le_fastRoot_iff 1 u).mpr (by simpa using hu)
  have hFQ : Erdos972EfficientSieveScale.fastRoot u ≤ quarterRoot u := by
    apply (le_quarterRoot_iff _ _).mpr
    exact (Nat.pow_le_pow_right hF (by decide : 1024 ≤ 4096)).trans
      ((Erdos972EfficientSieveScale.le_fastRoot_iff _ _).mp le_rfl)
  have hF0 : (0:ℝ) < Erdos972EfficientSieveScale.fastRoot u := Nat.cast_pos.mpr hF
  have hl : 1+Real.log (u+1:ℕ) ≤ 2*(1+Real.log u) := by
    have hbound : ((u+1:ℕ):ℝ) ≤ 2*(u:ℝ) := by exact_mod_cast (show u+1 ≤ 2*u by omega)
    have hu0 : (0:ℝ) < u := Nat.cast_pos.mpr hu
    have hg := Real.log_le_log (show (0:ℝ) < (u+1:ℕ) by positivity) hbound
    rw [Real.log_mul (by norm_num) hu0.ne'] at hg
    have htwo : Real.log 2 ≤ 1 := by
      simpa only [show (2:ℝ)-1 = 1 by norm_num] using
        Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    nlinarith only [hg, htwo, Real.log_natCast_nonneg u]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity [Real.log_natCast_nonneg (u+1)])]
  rw [show Erdos972AsymmetricDiagonalBudget.mobiusCutoff u =
    Erdos972EfficientSieveScale.fastRoot u by
      unfold Erdos972AsymmetricDiagonalBudget.mobiusCutoff Erdos972EfficientSieveScale.fastRoot
      rfl]
  calc
    _ ≤ C*(2*(1+Real.log u))^k/(quarterRoot u : ℝ) := by gcongr
    _ ≤ C*(2*(1+Real.log u))^k/(Erdos972EfficientSieveScale.fastRoot u : ℝ) :=
      div_le_div_of_nonneg_left (by positivity [Real.log_natCast_nonneg u]) hF0
        (Nat.cast_le.mpr hFQ)
    _ = _ := by rw [mul_pow]; ring

lemma eventually_squarefree_rough_loss {α : ℝ} (hα : 1 ≤ α) :
    ∀ᶠ u : ℕ in atTop,
      Real.log (u^6:ℕ)*(floorMul α (u^6) : ℝ)/(quarterRoot u : ℝ) ≤
        (u:ℝ)^6/(2*fourthConstant*(1+Real.log (u+1:ℕ))) := by
  have hC := fourthConstant_pos
  have hα0 : 0 < α := lt_of_lt_of_le zero_lt_one hα
  have hlim := quarterRoot_log_div_tendsto (12*α*fourthConstant) (by positivity) 2
  filter_upwards [(tendsto_order.mp hlim).2 1 zero_lt_one,
    eventually_ge_atTop (1:ℕ)] with u hb hu
  have hZ : 0 < quarterRoot u := (quarterRoot_eligible hu).1
  have hZR : (0:ℝ) < quarterRoot u := Nat.cast_pos.mpr hZ
  have hL : 0 < 1+Real.log (u+1:ℕ) := by positivity [Real.log_natCast_nonneg (u+1)]
  have hbudget : 12*α*fourthConstant*(1+Real.log (u+1:ℕ))^2 ≤ quarterRoot u := by
    have hh := (div_lt_iff₀ hZR).mp hb
    simpa only [one_mul] using hh.le
  have hcoef : 6*α*(1+Real.log (u+1:ℕ))/(quarterRoot u : ℝ) ≤
      1/(2*fourthConstant*(1+Real.log (u+1:ℕ))) := by
    apply (div_le_div_iff₀ hZR (by positivity)).mpr
    nlinarith only [hbudget]
  have hlog : Real.log (u^6:ℕ) ≤ 6*(1+Real.log (u+1:ℕ)) := by
    rw [Nat.cast_pow, Real.log_pow]
    have hh := Erdos972ExponentialSum.monotone_log_natCast (Nat.le_succ u)
    norm_num only [Nat.cast_ofNat]
    linarith only [hh]
  have hfloor : (floorMul α (u^6) : ℝ) ≤ α*(u:ℝ)^6 := by
    have hh := floorMul_le_real hα (le_refl (u^6))
    rw [Nat.cast_pow] at hh
    exact hh
  calc
    _ ≤ (6*(1+Real.log (u+1:ℕ)))*(α*(u:ℝ)^6)/(quarterRoot u : ℝ) := by gcongr
    _ = (6*α*(1+Real.log (u+1:ℕ))/(quarterRoot u : ℝ))*(u:ℝ)^6 := by ring
    _ ≤ (1/(2*fourthConstant*(1+Real.log (u+1:ℕ))))*(u:ℝ)^6 :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = _ := by ring

/-- The actual rough-output weight remains positive at its logarithmic
order after ALL nonsquarefree outputs have been removed. -/
theorem exists_squarefree_rough_log_scale {α : ℝ} (hα : 1 < α)
    (hI : Irrational α) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ B < quarterRoot u ∧
      (u:ℝ)^6/(2*fourthConstant*(1+Real.log (u+1:ℕ))) ≤
        squarefreeRoughWeight α (quarterRoot u) (u^6) := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_squarefree_rough_loss hα.le)
  obtain ⟨u, hu, hZ, hw⟩ :=
    Erdos972FourthPowerAlmostPrime.exists_prime_rough_log_scale hα hI (max B T)
  have hu1 : 1 ≤ u := (Nat.zero_le _).trans_lt hu
  have hZ1 := (quarterRoot_eligible hu1).1
  have hZN : quarterRoot u ≤ u^6 := by
    have hzpow := (le_quarterRoot_iff (quarterRoot u) u).mp le_rfl
    exact ((Nat.le_self_pow (by decide : 1024 ≠ 0) _).trans hzpow).trans
      (Nat.le_self_pow (by decide : 6 ≠ 0) u)
  have he := squarefree_rough_weight_loss hα.le hZ1 hZN
  have hb := hT u ((le_max_right B T).trans hu.le)
  have hid : (u:ℝ)^6/(fourthConstant*(1+Real.log (u+1:ℕ))) =
      2*((u:ℝ)^6/(2*fourthConstant*(1+Real.log (u+1:ℕ)))) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  refine ⟨u, (le_max_left B T).trans_lt hu, (le_max_left B T).trans_lt hZ, ?_⟩
  linarith only [he, hb, hw, hid]

lemma prime_beyond_of_squarefree_rough_weight {α : ℝ} {Z N B : ℕ}
    (hlarge : 7*(B:ℝ) < squarefreeRoughWeight α Z N) :
    ∃ p : ℕ, B < p ∧ p ≤ N ∧ p.Prime ∧
      (floorMul α p).Coprime Z.factorial ∧ Squarefree (floorMul α p) := by
  classical
  by_contra hh
  have hsmall : ∀ p ∈ squarefreeRoughInputs α Z N, p ≤ B := by
    intro p hp
    obtain ⟨hpI, hp, hc, hs⟩ := mem_filter.mp hp
    exact le_of_not_gt (fun hBp => hh ⟨p, hBp, (mem_Ioc.mp hpI).2, hp, hc, hs⟩)
  have hbound : squarefreeRoughWeight α Z N ≤ Chebyshev.theta B := by
    unfold squarefreeRoughWeight Chebyshev.theta
    rw [Nat.floor_natCast]
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      have hpI := (mem_filter.mp hp).1
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp hpI).1, hsmall p hp⟩,
        (mem_filter.mp hp).2.1⟩
    · intro p hp hn
      exact Real.log_natCast_nonneg p
  have hθ := (Chebyshev.theta_le_psi (B:ℝ)).trans
    (psi_le_seven_mul (Nat.cast_nonneg B))
  linarith only [hlarge, hbound, hθ]

/-- Arbitrarily large genuine prime inputs, with squarefree rough output
and the same factor bound 6144. -/
theorem exists_squarefree_rough_almostPrime_beyond {α : ℝ} (hα : 1 < α)
    (hI : Irrational α) (B Z : ℕ) :
    ∃ p : ℕ, B < p ∧ p.Prime ∧
      (floorMul α p).primeFactorsList.length ≤ 6144 ∧
      (floorMul α p).Coprime Z.factorial ∧ Squarefree (floorMul α p) := by
  let C := 2*fourthConstant
  have hC : 0 < C := mul_pos (by norm_num) fourthConstant_pos
  let T := max (max ⌈14*C*(B:ℝ)⌉₊ ⌈α⌉₊) Z
  obtain ⟨u, hu, hZ, hweight⟩ := exists_squarefree_rough_log_scale hα hI T
  have hu1 : 1 ≤ u := (Nat.zero_le T).trans_lt hu
  have hlargeU : 14*C*(B:ℝ) < u :=
    (Nat.le_ceil _).trans_lt (Nat.cast_lt.mpr
      (((le_max_left _ _).trans (le_max_left _ _)).trans_lt hu))
  have hweightLarge : 7*(B:ℝ) < squarefreeRoughWeight α (quarterRoot u) (u^6) :=
    (seven_mul_lt_div hC hlargeU).trans_le
      ((linear_below_log_weight hC hu1).trans hweight)
  obtain ⟨p, hpB, hpN, hp, hpc, hsf⟩ := prime_beyond_of_squarefree_rough_weight hweightLarge
  have hαZ : α ≤ quarterRoot u := (Nat.le_ceil α).trans
    (Nat.cast_le.mpr (((le_max_right _ _).trans (le_max_left _ _)).trans hZ.le))
  have hZZ : Z ≤ quarterRoot u := (le_max_right _ _).trans hZ.le
  exact ⟨p, hpB, hp,
    Erdos972FourthPowerAlmostPrime.rough_output_factor_bound hα.le hp.pos hpN hαZ hpc,
    Nat.Coprime.of_dvd_right (Nat.factorial_dvd_factorial hZZ) hpc, hsf⟩

theorem infinite_prime_squarefree_almostPrime_inputs {α : ℝ}
    (hα : 1 < α) (hI : Irrational α) :
    {p : ℕ | p.Prime ∧ Squarefree (floorMul α p) ∧
      (floorMul α p).primeFactorsList.length ≤ 6144}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro B
  obtain ⟨p, hpB, hp, hlen, _, hsf⟩ :=
    exists_squarefree_rough_almostPrime_beyond hα hI B 0
  exact ⟨p, ⟨hp, hsf, hlen⟩, hpB⟩

/-- Finite pigeonholing chooses one count for every pair of thresholds;
all its witnesses now have squarefree output. -/
theorem exists_fixed_squarefree_rough_count {α : ℝ} (hα : 1 < α)
    (hI : Irrational α) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ 6144 ∧ ∀ B Z : ℕ,
      ∃ p : ℕ, B < p ∧ p.Prime ∧
        (floorMul α p).primeFactorsList.length = k ∧
        (floorMul α p).Coprime Z.factorial ∧ Squarefree (floorMul α p) := by
  have hf : ∃ᶠ n : ℕ in atTop, ∃ k ∈ Icc 1 6144,
      ∃ p : ℕ, n < p ∧ p.Prime ∧
        (floorMul α p).primeFactorsList.length = k ∧
        (floorMul α p).Coprime n.factorial ∧ Squarefree (floorMul α p) := by
    apply Filter.Eventually.frequently
    apply Filter.Eventually.of_forall
    intro n
    obtain ⟨p, hnp, hp, hlen, hc, hs⟩ := exists_squarefree_rough_almostPrime_beyond hα hI n n
    have hq : 1 < floorMul α p := hp.one_lt.trans_le (self_le_floorMul hα.le p)
    have hlenpos : 0 < (floorMul α p).primeFactorsList.length :=
      List.length_pos_iff.mpr (Nat.primeFactorsList_ne_nil _ |>.mpr hq)
    exact ⟨_, mem_Icc.mpr ⟨hlenpos, hlen⟩, p, hnp, hp, rfl, hc, hs⟩
  obtain ⟨k, hk, hkfreq⟩ := (Finset.frequently_exists (Icc 1 6144)).mp hf
  refine ⟨k, (mem_Icc.mp hk).1, (mem_Icc.mp hk).2, ?_⟩
  intro B Z
  obtain ⟨n, hn, p, hnp, hp, hlen, hc, hs⟩ := frequently_atTop.mp hkfreq (max B Z)
  exact ⟨p, ((le_max_left B Z).trans hn).trans_lt hnp, hp, hlen,
    Nat.Coprime.of_dvd_right
      (Nat.factorial_dvd_factorial ((le_max_right B Z).trans hn)) hc, hs⟩

/-- A counterexample would supply arbitrarily rough SQUAREFREE composites
with one fixed number of prime factors. Proper prime powers are excluded. -/
theorem fixed_squarefree_composite_count_of_finite {α : ℝ} (hα : 1 < α)
    (hI : Irrational α)
    (hfin : {p : ℕ | p.Prime ∧ (floorMul α p).Prime}.Finite) :
    ∃ k : ℕ, 2 ≤ k ∧ k ≤ 6144 ∧ ∀ B Z : ℕ,
      ∃ p : ℕ, B < p ∧ p.Prime ∧ Squarefree (floorMul α p) ∧
        (floorMul α p).primeFactorsList.length = k ∧
        ∀ r : ℕ, r.Prime → r ∣ floorMul α p → Z < r := by
  obtain ⟨k, hk1, hkK, hk⟩ := exists_fixed_squarefree_rough_count hα hI
  have hkne : k ≠ 1 := by
    intro he
    obtain ⟨B, hB⟩ := hfin.bddAbove
    obtain ⟨p, hpB, hp, hlen, _⟩ := hk B 0
    have hq : (floorMul α p).Prime :=
      (prime_iff_factor_length_one (floorMul_pos hα.le hp.pos).ne').mpr (hlen.trans he)
    exact (not_le_of_gt hpB) (hB ⟨hp, hq⟩)
  refine ⟨k, by omega, hkK, ?_⟩
  intro B Z
  obtain ⟨p, hpB, hp, hlen, hc, hs⟩ := hk B Z
  exact ⟨p, hpB, hp, hs, hlen, fun r hr hrd =>
    prime_factor_gt_of_coprime_factorial hc hr hrd⟩


lemma squarefreeRoughWeight_card_upper (α : ℝ) (Z u : ℕ) :
    squarefreeRoughWeight α Z (u^6) ≤
      6*(1+Real.log (u+1:ℕ))*(squarefreeRoughInputs α Z (u^6)).card := by
  classical
  have hlog : Real.log (u^6:ℕ) ≤ 6*(1+Real.log (u+1:ℕ)) := by
    rw [Nat.cast_pow, Real.log_pow]
    have hh := Erdos972ExponentialSum.monotone_log_natCast (Nat.le_succ u)
    norm_num only [Nat.cast_ofNat]
    linarith only [hh]
  have hs : (∑ p ∈ squarefreeRoughInputs α Z (u^6), Real.log p) ≤
      ∑ p ∈ squarefreeRoughInputs α Z (u^6), 6*(1+Real.log (u+1:ℕ)) := by
    apply sum_le_sum
    intro p hp
    exact (log_input_le (mem_filter.mp hp).1).trans hlog
  simpa only [squarefreeRoughWeight, sum_const, nsmul_eq_mul, mul_comm] using hs

noncomputable def squarefreeAlmostPrimeInputs (α : ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Ioc 0 N).filter (fun p => p.Prime ∧ Squarefree (floorMul α p) ∧
    (floorMul α p).primeFactorsList.length ≤ 6144)

/-- A cardinality lower bound of logarithmic order, with squarefree output
and at most 6144 prime factors. -/
theorem exists_squarefree_almostPrime_card_scale {α : ℝ} (hα : 1 < α)
    (hI : Irrational α) (B : ℕ) :
    ∃ u : ℕ, B < u ∧
      (u:ℝ)^6/(12*fourthConstant*(1+Real.log (u+1:ℕ))^2) ≤
        (squarefreeAlmostPrimeInputs α (u^6)).card := by
  classical
  obtain ⟨u, hu, hZ, hweight⟩ := exists_squarefree_rough_log_scale hα hI (max B ⌈α⌉₊)
  have hαZ : α ≤ quarterRoot u := (Nat.le_ceil α).trans
    (Nat.cast_le.mpr ((le_max_right B _).trans hZ.le))
  have hcount := logarithmic_count_transfer (mul_pos (by norm_num : (0:ℝ) < 2) fourthConstant_pos)
    (show 0 < 1+Real.log (u+1:ℕ) by positivity [Real.log_natCast_nonneg (u+1)])
    (hweight.trans (squarefreeRoughWeight_card_upper α (quarterRoot u) u))
  have hcount' : (u:ℝ)^6/(12*fourthConstant*(1+Real.log (u+1:ℕ))^2) ≤
      (squarefreeRoughInputs α (quarterRoot u) (u^6)).card := by
    convert hcount using 1
    ring
  refine ⟨u, (le_max_left B _).trans_lt hu, hcount'.trans ?_⟩
  apply Nat.cast_le.mpr
  apply card_le_card
  intro p hp
  obtain ⟨hpI, hprime, hc, hs⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨hpI, hprime, hs,
    Erdos972FourthPowerAlmostPrime.rough_output_factor_bound hα.le hprime.pos
      (mem_Ioc.mp hpI).2 hαZ hc⟩

#print axioms squarefree_rough_weight_loss
#print axioms quarterRoot_log_div_tendsto
#print axioms exists_squarefree_rough_log_scale
#print axioms infinite_prime_squarefree_almostPrime_inputs
#print axioms exists_fixed_squarefree_rough_count
#print axioms fixed_squarefree_composite_count_of_finite
#print axioms exists_squarefree_almostPrime_card_scale

end Erdos972SquarefreeRoughAlmostPrime
