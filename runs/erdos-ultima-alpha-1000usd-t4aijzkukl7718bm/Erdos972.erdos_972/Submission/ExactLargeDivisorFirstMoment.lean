import Submission.LargeDivisorBlockMoment

/-! Exact complementary-divisor switching, retaining both endpoints of a
large divisor block. These identities and first-moment estimates do not
assert a lower bound for prime pairs. -/
namespace Erdos972ExactLargeDivisorFirstMoment

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972PrimePowerError Erdos972PrimeRoughOutputs Erdos972SelbergLowerTest
open Erdos972LargeDivisorBlockMoment Erdos972PrimeLeastFactorScales
open Erdos972PolynomialRowScales Erdos972DualPrimeRows Erdos972ScaledPrimeRows
open Erdos972PrimeRotation Erdos972GrowingCoprimeCandidates

set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local irreducible] root64

/-- The last natural input whose floor output is at most m. -/
noncomputable def outputPrefix (α : ℝ) (m : ℕ) : ℕ :=
  ⌈((m : ℝ)+1)/α⌉₊-1

lemma floorMul_le_iff_outputPrefix {α : ℝ} (hα : 0 < α) (p m : ℕ) :
    floorMul α p ≤ m ↔ p ≤ outputPrefix α m := by
  have hc : 0 < ⌈((m : ℝ)+1)/α⌉₊ := Nat.ceil_pos.mpr (by positivity)
  have he : floorMul α p < m+1 ↔ p < ⌈((m : ℝ)+1)/α⌉₊ := by
    rw [Nat.lt_ceil, lt_div_iff₀ hα]
    unfold floorMul
    rw [Nat.floor_lt (by positivity)]
    push_cast
    rw [mul_comm]
  unfold outputPrefix
  omega

lemma outputPrefix_mono {α : ℝ} (hα : 0 < α) : Monotone (outputPrefix α) := by
  intro m n hmn
  exact (floorMul_le_iff_outputPrefix hα _ _).mp
    (((floorMul_le_iff_outputPrefix hα _ _).mpr le_rfl).trans hmn)

lemma block_divisor_card_eq_cofactor_card {D K n : ℕ}
    (hD : 0 < D) (hn : 0 < n) (hnK : n ≤ D*K) :
    ((Ioc D (2*D)).filter (fun d => d ∣ n)).card =
      ((Ioc 0 K).filter (fun k => k ∣ n ∧ D*k < n ∧ n ≤ 2*D*k)).card := by
  classical
  apply card_bij (fun d _ => n/d)
  · intro d hd
    obtain ⟨hdI, hdn⟩ := mem_filter.mp hd
    have hd0 : 0 < d := hD.trans (mem_Ioc.mp hdI).1
    have hk0 : 0 < n/d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
    have hkd : d*(n/d) = n := Nat.mul_div_cancel' hdn
    have hkK : n/d ≤ K := by
      have hdD := (mem_Ioc.mp hdI).1
      nlinarith
    refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨hk0, hkK⟩, Nat.div_dvd_of_dvd hdn, ?_, ?_⟩
    · have hh := Nat.mul_lt_mul_of_pos_right (mem_Ioc.mp hdI).1 hk0
      nlinarith only [hh, hkd]
    · have hh := Nat.mul_le_mul_right (n/d) (mem_Ioc.mp hdI).2
      nlinarith only [hh, hkd]
  · intro d hd e he hde
    obtain ⟨hdI, hdn⟩ := mem_filter.mp hd
    obtain ⟨heI, hen⟩ := mem_filter.mp he
    have hk0 : 0 < n/d := Nat.div_pos (Nat.le_of_dvd hn hdn)
      (hD.trans (mem_Ioc.mp hdI).1)
    have hkd : d*(n/d) = n := Nat.mul_div_cancel' hdn
    have hke : e*(n/d) = n := by rw [hde]; exact Nat.mul_div_cancel' hen
    nlinarith
  · intro k hk
    obtain ⟨hkI, hkn, hklo, hkhi⟩ := mem_filter.mp hk
    have hk0 := (mem_Ioc.mp hkI).1
    have hdk : (n/k)*k = n := Nat.div_mul_cancel hkn
    have hdD : D < n/k := by nlinarith
    have hd2D : n/k ≤ 2*D := by nlinarith
    refine ⟨n/k, mem_filter.mpr ⟨mem_Ioc.mpr ⟨hdD, hd2D⟩,
      Nat.div_dvd_of_dvd hkn⟩, ?_⟩
    exact Nat.div_div_self hkn hn.ne'

lemma row_outputPrefix {α : ℝ} (hα : 0 < α) (N m k : ℕ) (a : ℕ → ℝ) :
    row ((Ioc 0 N).filter (fun p => floorMul α p ≤ m)) a (floorMul α) k =
      row (Ioc 0 (min N (outputPrefix α m))) a (floorMul α) k := by
  congr 1
  ext p
  simp only [mem_filter, mem_Ioc, le_min_iff, floorMul_le_iff_outputPrefix hα]
  tauto

/-- Both endpoints, including their exact rounding, survive switching. -/
theorem block_firstMoment_exact {α : ℝ} (hα : 1 ≤ α) {N D K : ℕ}
    (hD : 0 < D) (hNK : floorMul α N ≤ D*K) (a : ℕ → ℝ) :
    (∑ d ∈ Ioc D (2*D), row (Ioc 0 N) a (floorMul α) d) =
      ∑ k ∈ Ioc 0 K,
        (row (Ioc 0 (min N (outputPrefix α (2*D*k)))) a (floorMul α) k -
         row (Ioc 0 (min N (outputPrefix α (D*k)))) a (floorMul α) k) := by
  classical
  have hα0 : 0 < α := by linarith
  have hpoint (p : ℕ) (hp : p ∈ Ioc 0 N) :
      (∑ d ∈ Ioc D (2*D), if d ∣ floorMul α p then a p else 0) =
        ∑ k ∈ Ioc 0 K,
          if k ∣ floorMul α p ∧ D*k < floorMul α p ∧ floorMul α p ≤ 2*D*k
          then a p else 0 := by
    rw [← sum_filter, ← sum_filter, sum_const, sum_const,
      block_divisor_card_eq_cofactor_card hD
        (floorMul_pos hα (mem_Ioc.mp hp).1)
        (((floorMul_strictMono hα).monotone (mem_Ioc.mp hp).2).trans hNK)]
  simp only [row] at ⊢
  rw [sum_comm]
  have hsum := sum_congr rfl hpoint
  rw [hsum, sum_comm]
  apply sum_congr rfl
  intro k hk
  have hupper := row_outputPrefix hα0 N (2*D*k) k a
  have hlower := row_outputPrefix hα0 N (D*k) k a
  simp only [row, sum_filter] at hupper hlower
  rw [← hupper, ← hlower, ← sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  have hh : D*k ≤ 2*D*k := by nlinarith
  simp only [← not_le]
  by_cases hdiv : k ∣ floorMul α p <;>
    by_cases hlo : floorMul α p ≤ D*k <;>
    by_cases hhi : floorMul α p ≤ 2*D*k <;>
    simp [hdiv, hlo, hhi] <;> omega

noncomputable def blockChebyshevMain (α : ℝ) (N D K : ℕ) : ℝ :=
  ∑ k ∈ Ioc 0 K,
    (Chebyshev.psi (min N (outputPrefix α (2*D*k)) : ℕ) -
     Chebyshev.psi (min N (outputPrefix α (D*k)) : ℕ))/(k : ℝ)

/-- Small-row prefix estimates now give a two-sided block estimate, rather
than just the earlier upper bound. -/
theorem block_firstMoment_discrepancy {α : ℝ} (hα : 1 ≤ α) {N D K : ℕ}
    (hD : 0 < D) (hNK : floorMul α N ≤ D*K) {E : ℝ}
    (hrows : ∀ k : ℕ, 0 < k → k ≤ K → ∀ X : ℕ, X ≤ N →
      |row (Ioc 0 X) primeWeight (floorMul α) k-Chebyshev.psi X/(k:ℝ)| ≤ E) :
    |(∑ d ∈ Ioc D (2*D), row (Ioc 0 N) primeWeight (floorMul α) d)-
      blockChebyshevMain α N D K| ≤ 2*(K:ℝ)*E := by
  rw [block_firstMoment_exact hα hD hNK, blockChebyshevMain, ← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ k ∈ Ioc 0 K, 2*E := by
      apply sum_le_sum
      intro k hk
      have hu := hrows k (mem_Ioc.mp hk).1 (mem_Ioc.mp hk).2
        (min N (outputPrefix α (2*D*k))) (min_le_left _ _)
      have hl := hrows k (mem_Ioc.mp hk).1 (mem_Ioc.mp hk).2
        (min N (outputPrefix α (D*k))) (min_le_left _ _)
      have he :
          row (Ioc 0 (min N (outputPrefix α (2*D*k)))) primeWeight (floorMul α) k -
          row (Ioc 0 (min N (outputPrefix α (D*k)))) primeWeight (floorMul α) k -
          (Chebyshev.psi (min N (outputPrefix α (2*D*k)) : ℕ) -
           Chebyshev.psi (min N (outputPrefix α (D*k)) : ℕ))/(k:ℝ) =
          (row (Ioc 0 (min N (outputPrefix α (2*D*k)))) primeWeight (floorMul α) k -
           Chebyshev.psi (min N (outputPrefix α (2*D*k)) : ℕ)/(k:ℝ)) -
          (row (Ioc 0 (min N (outputPrefix α (D*k)))) primeWeight (floorMul α) k -
           Chebyshev.psi (min N (outputPrefix α (D*k)) : ℕ)/(k:ℝ)) := by ring
      rw [he]
      exact (abs_sub _ _).trans (by linarith only [hu, hl])
    _ = _ := by simp only [sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]; ring

lemma primePowerMass_mono_nat {X N : ℕ} (hXN : X ≤ N) :
    Chebyshev.psi X-Chebyshev.theta X ≤ Chebyshev.psi N-Chebyshev.theta N := by
  simp only [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, sum_filter]
  apply sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_right hXN)
  intro n hn hnot
  split_ifs <;> first | exact vonMangoldt_nonneg | exact le_rfl

lemma primeRowError_weighted_tendsto :
    Tendsto (fun u : ℕ => (root64 u : ℝ)*primeRowError u/(u:ℝ)^6)
      atTop (𝓝 0) := by
  have hE := summed_scaledRowError_tendsto 1 0
  simp only [pow_zero, mul_one] at hE
  simpa only [primeRowError, mul_add, add_div, add_zero] using
    hE.add sixth_scale_primePower_tendsto

/-- The small prime-input rows and their summed error budget hold at a
common scale. The error includes all proper prime powers. -/
theorem exists_small_prime_prefix_rows {α ε : ℝ}
    (hα : 1 < α) (hI : Irrational α) (hε : 0 < ε) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ 0 < u ∧
      2*(root64 u:ℝ)*primeRowError u ≤ ε*(u:ℝ)^6 ∧
      ∀ k : ℕ, 0 < k → k ≤ root64 u → ∀ X : ℕ, X ≤ u^6 →
        |row (Ioc 0 X) primeWeight (floorMul α) k-Chebyshev.psi X/(k:ℝ)| ≤ primeRowError u := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (((tendsto_order.mp primeRowError_weighted_tendsto).2 (ε/2) (by positivity)).and
      (root64_tendsto.eventually_ge_atTop 2048))
  let A := max T (B+1)
  obtain ⟨r, hr, hden⟩ := Erdos972RationalRoute.exists_good_approximant_large_den hα hI (A^4)
  let u := Nat.sqrt (Nat.sqrt r.den)
  have hAu : A ≤ u := (le_fourth_root_iff A r.den).mpr hden.le
  have hTu : T ≤ u := (le_max_left T (B+1)).trans hAu
  have hBu : B < u := by have := (le_max_right T (B+1)).trans hAu; omega
  obtain ⟨hu, hlo, hhi⟩ := fourth_root_bounds r.pos
  change 0 < u at hu
  change u^4 ≤ r.den at hlo
  change r.den ≤ 16*u^4 at hhi
  clear_value u
  obtain ⟨hbudget, hv⟩ := hT u hTu
  have hbudget' : 2*(root64 u:ℝ)*primeRowError u ≤ ε*(u:ℝ)^6 := by
    have hh := (div_lt_iff₀ (show 0 < (u:ℝ)^6 by positivity)).mp hbudget
    nlinarith only [hh]
  have hrows (k : ℕ) (hk : 0 < k) (hkv : k ≤ root64 u) (X : ℕ) (hX : X ≤ u^6) :
      |row (Ioc 0 X) primeWeight (floorMul α) k-Chebyshev.psi X/(k:ℝ)| ≤ primeRowError u := by
    have hh := prime_row_discrepancy α k X (input_divisor_row_discrepancy
      (show 0 ≤ α by linarith) r hr.le (K := 1) (by norm_num) (by simpa using hv)
      (root64_bounds hu).2.1 (by simpa using hlo) (by simpa using hhi) hk hkv hX)
    exact hh.trans (add_le_add le_rfl (primePowerMass_mono_nat hX))
  exact ⟨u, hBu, hu, hbudget', hrows⟩

/-- At arbitrarily large actual irrational good scales, all eligible large
blocks have a two-sided first-moment error at most epsilon*N. -/
theorem exists_block_firstMoment_scale {α ε : ℝ}
    (hα : 1 < α) (hI : Irrational α) (hε : 0 < ε) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ 0 < u ∧ ∀ D K : ℕ, 0 < D → K ≤ root64 u →
      floorMul α (u^6) ≤ D*K →
      |(∑ d ∈ Ioc D (2*D), row (Ioc 0 (u^6)) primeWeight (floorMul α) d)-
        blockChebyshevMain α (u^6) D K| ≤ ε*(u:ℝ)^6 := by
  obtain ⟨u, hBu, hu, hbudget, hrows⟩ := exists_small_prime_prefix_rows hα hI hε B
  refine ⟨u, hBu, hu, ?_⟩
  intro D K hD hKv hNK
  apply (block_firstMoment_discrepancy hα.le hD hNK
    (fun k hk hkK X hX => hrows k hk (hkK.trans hKv) X hX)).trans
  have hh := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hKv : (K:ℝ) ≤ root64 u)
    (primeRowError_nonneg u)
  nlinarith only [hh, hbudget]

lemma block_reciprocal_square_sum {D : ℕ} (hD : 0 < D) :
    (∑ d ∈ Ioc D (2*D), 1/(d:ℝ)^2) ≤ 1/(2*(D:ℝ)) := by
  have hh := sum_Ioc_inv_sq_le_sub (α := ℝ) hD.ne' (show D ≤ 2*D by omega)
  simp only [← one_div, Nat.cast_mul, Nat.cast_ofNat] at hh
  apply hh.trans_eq
  field_simp
  ring

/-- The first moment supplies a retained negative term in the centered
energy. This does not assume that the second moment has its expected value. -/
theorem centered_block_energy_upper (R : ℕ → ℝ) {D : ℕ} (hD : 0 < D)
    {X : ℝ} (hX : 0 ≤ X) (hR : ∀ d ∈ Ioc D (2*D), 0 ≤ R d) :
    (∑ d ∈ Ioc D (2*D), (R d-X/(d:ℝ))^2) ≤
      (∑ d ∈ Ioc D (2*D), (R d)^2)-
        (X/(D:ℝ))*(∑ d ∈ Ioc D (2*D), R d)+X^2/(2*(D:ℝ)) := by
  have hDR : (0:ℝ) < D := Nat.cast_pos.mpr hD
  have hpoint (d : ℕ) (hd : d ∈ Ioc D (2*D)) :
      (R d-X/(d:ℝ))^2 ≤ (R d)^2-(X/(D:ℝ))*R d+X^2/(d:ℝ)^2 := by
    have hdR : (0:ℝ) < d := Nat.cast_pos.mpr (hD.trans (mem_Ioc.mp hd).1)
    have hdhi : (d:ℝ) ≤ 2*(D:ℝ) := by exact_mod_cast (mem_Ioc.mp hd).2
    have hu : X/(2*(D:ℝ)) ≤ X/(d:ℝ) :=
      div_le_div_of_nonneg_left hX hdR hdhi
    have hm := mul_le_mul_of_nonneg_right hu (hR d hd)
    have he : (X/(d:ℝ))^2 = X^2/(d:ℝ)^2 := by ring
    have he' : 2*(X/(2*(D:ℝ)))*R d = (X/(D:ℝ))*R d := by ring
    nlinarith only [hm, he, he']
  apply (sum_le_sum hpoint).trans
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum]
  have hs : (∑ d ∈ Ioc D (2*D), X^2/(d:ℝ)^2) ≤ X^2/(2*(D:ℝ)) := by
    simp_rw [show ∀ d : ℕ, X^2/(d:ℝ)^2 = X^2*(1/(d:ℝ)^2) from fun _ => by ring]
    rw [← mul_sum]
    simpa only [mul_one_div] using
      mul_le_mul_of_nonneg_left (block_reciprocal_square_sum hD) (sq_nonneg X)
  linarith only [hs]

/-- Instantiation of the retained centering term on actual irrational
scales. The raw second moment is deliberately not replaced by an unproved
asymptotic. -/
theorem exists_centered_block_firstMoment_scale {α ε : ℝ}
    (hα : 1 < α) (hI : Irrational α) (hε : 0 < ε) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ 0 < u ∧ ∀ D K : ℕ, 0 < D → K ≤ root64 u →
      floorMul α (u^6) ≤ D*K →
      (∑ d ∈ Ioc D (2*D),
        (row (Ioc 0 (u^6)) primeWeight (floorMul α) d-Chebyshev.psi (u^6 : ℕ)/(d:ℝ))^2) ≤
        (∑ d ∈ Ioc D (2*D), (row (Ioc 0 (u^6)) primeWeight (floorMul α) d)^2)-
          (Chebyshev.psi (u^6 : ℕ)/(D:ℝ))*(blockChebyshevMain α (u^6) D K-ε*(u:ℝ)^6)+
          (Chebyshev.psi (u^6 : ℕ))^2/(2*(D:ℝ)) := by
  obtain ⟨u, hBu, hu, hb⟩ := exists_block_firstMoment_scale hα hI hε B
  refine ⟨u, hBu, hu, ?_⟩
  intro D K hD hKv hNK
  have hr0 (d : ℕ) (hd : d ∈ Ioc D (2*D)) :
      0 ≤ row (Ioc 0 (u^6)) primeWeight (floorMul α) d := by
    unfold row
    apply sum_nonneg
    intro p hp
    split_ifs <;> first | exact primeWeight_nonneg p | exact le_rfl
  have hh := centered_block_energy_upper
    (fun d => row (Ioc 0 (u^6)) primeWeight (floorMul α) d) hD
    (Chebyshev.psi_nonneg (u^6 : ℕ)) hr0
  apply hh.trans
  have hlo := (abs_le.mp (hb D K hD hKv hNK)).1
  have hc : 0 ≤ Chebyshev.psi (u^6 : ℕ)/(D:ℝ) :=
    div_nonneg (Chebyshev.psi_nonneg _) (Nat.cast_nonneg D)
  have hl : blockChebyshevMain α (u^6) D K-ε*(u:ℝ)^6 ≤
      ∑ d ∈ Ioc D (2*D), row (Ioc 0 (u^6)) primeWeight (floorMul α) d := by
    linarith only [hlo]
  have hm := mul_le_mul_of_nonneg_left hl hc
  dsimp only at hh ⊢
  linarith only [hm]

/-- The retained first moment and the proved raw second-moment upper bound
can be used at the same scale. All centering terms remain explicit. -/
theorem exists_explicit_centered_block_bound {α ε : ℝ}
    (hα : 1 < α) (hI : Irrational α) (hε : 0 < ε) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ 0 < u ∧ ∀ D K M : ℕ, 0 < D → 0 < M →
      K ≤ root64 u → floorMul α (u^6) ≤ D*K → α*(M:ℝ) < D → u^6 ≤ D*M →
      |(∑ d ∈ Ioc D (2*D), row (Ioc 0 (u^6)) primeWeight (floorMul α) d)-
        blockChebyshevMain α (u^6) D K| ≤ ε*(u:ℝ)^6 ∧
      (∑ d ∈ Ioc D (2*D),
        (row (Ioc 0 (u^6)) primeWeight (floorMul α) d-Chebyshev.psi (u^6 : ℕ)/(d:ℝ))^2) ≤
        ((M:ℝ)*Real.log (u^6 : ℕ))*(14*(D:ℝ)*K+ε*(u:ℝ)^6/2)-
          (Chebyshev.psi (u^6 : ℕ)/(D:ℝ))*(blockChebyshevMain α (u^6) D K-ε*(u:ℝ)^6)+
          (Chebyshev.psi (u^6 : ℕ))^2/(2*(D:ℝ)) := by
  obtain ⟨u, hBu, hu, hbudget, hrows⟩ := exists_small_prime_prefix_rows hα hI hε B
  refine ⟨u, hBu, hu, ?_⟩
  intro D K M hD hM hKv hNK hDM hNM
  have hEK : (K:ℝ)*primeRowError u ≤ ε*(u:ℝ)^6/2 := by
    have hh := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hKv : (K:ℝ) ≤ root64 u)
      (primeRowError_nonneg u)
    nlinarith only [hh, hbudget]
  have hfirst := (block_firstMoment_discrepancy hα.le hD hNK
    (fun k hk hkK X hX => hrows k hk (hkK.trans hKv) X hX)).trans
      (show 2*(K:ℝ)*primeRowError u ≤ ε*(u:ℝ)^6 by nlinarith only [hEK])
  refine ⟨hfirst, ?_⟩
  have hrupper (k : ℕ) (hk : 0 < k) (hkK : k ≤ K) (X : ℕ) (hX : X ≤ u^6) :
      row (Ioc 0 X) primeWeight (floorMul α) k ≤ 7*(X:ℝ)/k+primeRowError u := by
    have hh := (abs_le.mp (hrows k hk (hkK.trans hKv) X hX)).2
    have hm := div_le_div_of_nonneg_right
      (Erdos972ChebyshevRowMean.psi_le_seven_mul (Nat.cast_nonneg X)) (Nat.cast_nonneg k : (0:ℝ) ≤ k)
    linarith only [hh, hm]
  have hsecond := block_secondMoment_upper hα.le hD hM hNK hDM hNM hrupper
  have hsecond' :
      (∑ d ∈ Ioc D (2*D), (row (Ioc 0 (u^6)) primeWeight (floorMul α) d)^2) ≤
        ((M:ℝ)*Real.log (u^6 : ℕ))*(14*(D:ℝ)*K+ε*(u:ℝ)^6/2) := by
    apply hsecond.trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Nat.cast_nonneg M) (Real.log_natCast_nonneg _))
    nlinarith only [hEK]
  have hr0 (d : ℕ) (hd : d ∈ Ioc D (2*D)) :
      0 ≤ row (Ioc 0 (u^6)) primeWeight (floorMul α) d := by
    unfold row
    apply sum_nonneg
    intro p hp
    split_ifs <;> first | exact primeWeight_nonneg p | exact le_rfl
  have hc := centered_block_energy_upper
    (fun d => row (Ioc 0 (u^6)) primeWeight (floorMul α) d) hD
    (Chebyshev.psi_nonneg (u^6 : ℕ)) hr0
  have hlo : blockChebyshevMain α (u^6) D K-ε*(u:ℝ)^6 ≤
      ∑ d ∈ Ioc D (2*D), row (Ioc 0 (u^6)) primeWeight (floorMul α) d := by
    linarith only [(abs_le.mp hfirst).1]
  have hm := mul_le_mul_of_nonneg_left hlo
    (div_nonneg (Chebyshev.psi_nonneg (u^6 : ℕ)) (Nat.cast_nonneg D : (0:ℝ) ≤ D))
  dsimp only at hc
  linarith only [hc, hm, hsecond']

#print axioms block_firstMoment_exact
#print axioms block_firstMoment_discrepancy
#print axioms primeRowError_weighted_tendsto
#print axioms exists_small_prime_prefix_rows
#print axioms exists_block_firstMoment_scale
#print axioms centered_block_energy_upper
#print axioms exists_centered_block_firstMoment_scale
#print axioms exists_explicit_centered_block_bound
end Erdos972ExactLargeDivisorFirstMoment
