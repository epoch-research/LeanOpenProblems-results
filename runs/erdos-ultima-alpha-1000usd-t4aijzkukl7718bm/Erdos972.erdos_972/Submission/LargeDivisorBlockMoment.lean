import Submission.PrimeRowResidueInjection
import Submission.PrimeLeastFactorScales

/-! Complementary-divisor switching for large divisor blocks. The estimates
are upper moments, not a prime-pair lower bound. -/
namespace Erdos972LargeDivisorBlockMoment

open Finset ArithmeticFunction
open Erdos972PrimePowerError Erdos972PrimeRoughOutputs Erdos972SelbergLowerTest
open Erdos972PrimeOutputGcdDeterminant Erdos972PrimeRowResidueInjection
open Erdos972ChebyshevRowMean
set_option autoImplicit false
set_option maxHeartbeats 2500000

lemma block_divisor_card_le_cofactor_card {D K p n : ℕ}
    (hD : 0 < D) (hn : 0 < n) (hnK : n ≤ D*K) (hpn : p ≤ n) :
    ((Ioc D (2*D)).filter (fun d => d ∣ n)).card ≤
      ((Ioc 0 K).filter (fun k => k ∣ n ∧ p ≤ 2*D*k)).card := by
  classical
  apply card_le_card_of_injOn (fun d => n/d)
  · intro d hd
    change d ∈ (Ioc D (2*D)).filter (fun d => d ∣ n) at hd
    obtain ⟨hdI, hdn⟩ := mem_filter.mp hd
    have hd0 : 0 < d := hD.trans (mem_Ioc.mp hdI).1
    have hkd : d*(n/d) = n := Nat.mul_div_cancel' hdn
    have hk0 : 0 < n/d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
    have hkK : n/d ≤ K := by
      have hdD := (mem_Ioc.mp hdI).1
      nlinarith
    have hpK : p ≤ 2*D*(n/d) := by
      have hh := Nat.mul_le_mul_right (n/d) (mem_Ioc.mp hdI).2
      nlinarith only [hkd, hh, hpn]
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hk0, hkK⟩, Nat.div_dvd_of_dvd hdn, hpK⟩
  · intro d hd e he hde
    change d ∈ (Ioc D (2*D)).filter (fun d => d ∣ n) at hd
    change e ∈ (Ioc D (2*D)).filter (fun d => d ∣ n) at he
    obtain ⟨hdI, hdn⟩ := mem_filter.mp hd
    obtain ⟨heI, hen⟩ := mem_filter.mp he
    have hd0 : 0 < d := hD.trans (mem_Ioc.mp hdI).1
    have hk0 : 0 < n/d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
    have hkd : d*(n/d) = n := Nat.mul_div_cancel' hdn
    dsimp only at hde
    have hke : e*(n/d) = n := by rw [hde]; exact Nat.mul_div_cancel' hen
    nlinarith

/-- Each divisor in (D,2D] has a small complementary divisor; its source
input belongs to a correspondingly shortened prefix. No weights are lost. -/
theorem block_firstMoment_switch {α : ℝ} (hα : 1 ≤ α) {N D K : ℕ}
    (hD : 0 < D) (hNK : floorMul α N ≤ D*K) :
    (∑ d ∈ Ioc D (2*D), row (Ioc 0 N) primeWeight (floorMul α) d) ≤
      ∑ k ∈ Ioc 0 K, row (Ioc 0 (min N (2*D*k))) primeWeight (floorMul α) k := by
  classical
  have hpoint (p : ℕ) (hp : p ∈ Ioc 0 N) :
      (∑ d ∈ Ioc D (2*D), if d ∣ floorMul α p then primeWeight p else 0) ≤
      ∑ k ∈ Ioc 0 K, if k ∣ floorMul α p ∧ p ≤ 2*D*k then primeWeight p else 0 := by
    rw [← sum_filter, ← sum_filter, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (primeWeight_nonneg p)
    exact Nat.cast_le.mpr (block_divisor_card_le_cofactor_card hD
      (floorMul_pos hα (mem_Ioc.mp hp).1)
      (((floorMul_strictMono hα).monotone (mem_Ioc.mp hp).2).trans hNK)
      (self_le_floorMul hα p))
  simp only [row]
  rw [sum_comm]
  apply (sum_le_sum hpoint).trans
  rw [sum_comm]
  apply le_of_eq
  apply sum_congr rfl
  intro k hk
  have hs : Ioc 0 (min N (2*D*k)) = (Ioc 0 N).filter (fun p => p ≤ 2*D*k) := by
    ext p
    simp only [mem_Ioc, mem_filter, le_min_iff]
    tauto
  rw [hs, sum_filter]
  apply sum_congr rfl
  intro p hp
  by_cases hdiv : k ∣ floorMul α p <;> by_cases hcut : p ≤ 2*D*k <;> simp [hdiv, hcut]

/-- Small-divisor upper prefix estimates imply a log-free first-moment
bound for a complementary large-divisor block. -/
theorem block_firstMoment_upper {α : ℝ} (hα : 1 ≤ α) {N D K : ℕ}
    (hD : 0 < D) (hNK : floorMul α N ≤ D*K) {E : ℝ}
    (hrows : ∀ k : ℕ, 0 < k → k ≤ K → ∀ X : ℕ, X ≤ N →
      row (Ioc 0 X) primeWeight (floorMul α) k ≤ 7*(X:ℝ)/k+E) :
    (∑ d ∈ Ioc D (2*D), row (Ioc 0 N) primeWeight (floorMul α) d) ≤
      (K:ℝ)*(14*D+E) := by
  apply (block_firstMoment_switch hα hD hNK).trans
  calc
    _ ≤ ∑ k ∈ Ioc 0 K, (14*(D:ℝ)+E) := by
      apply sum_le_sum
      intro k hk
      have hk0 := (mem_Ioc.mp hk).1
      have hr := hrows k hk0 (mem_Ioc.mp hk).2 (min N (2*D*k)) (min_le_left _ _)
      have hX : ((min N (2*D*k):ℕ):ℝ) ≤ (2:ℝ)*D*k := by
        exact_mod_cast (min_le_right N (2*D*k))
      have hb : 7*((min N (2*D*k):ℕ):ℝ)/k ≤ 14*(D:ℝ) := by
        apply (div_le_iff₀ (Nat.cast_pos.mpr hk0 : (0:ℝ) < k)).mpr
        nlinarith only [hX]
      linarith only [hr, hb]
    _ = _ := by simp only [sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]

/-- When d exceeds alpha*M, every prime input in its row exceeds M.
The modular injection therefore applies to the full row. -/
theorem prime_row_upper_of_large_divisor {α : ℝ} (hα : 1 ≤ α) {N d M : ℕ}
    (hM : 0 < M) (hd : α*(M:ℝ) < d) (hN : N ≤ d*M) :
    row (Ioc 0 N) primeWeight (floorMul α) d ≤ (M:ℝ)*Real.log N := by
  classical
  have hdα : α < (d:ℝ) := by
    have hM1 : (1:ℝ) ≤ M := Nat.one_le_cast.mpr hM
    nlinarith only [hd, hM1, hα]
  have hpM (p : ℕ) (hp : p ∈ Ioc 0 N) (hdp : d ∣ floorMul α p) : M < p := by
    have hdle : d ≤ floorMul α p := Nat.le_of_dvd (floorMul_pos hα (mem_Ioc.mp hp).1) hdp
    have hreal : (d:ℝ) ≤ α*p := (Nat.cast_le.mpr hdle).trans
      (Nat.floor_le (by positivity : 0 ≤ α*(p:ℝ)))
    by_contra hnot
    have hpM : (p:ℝ) ≤ M := Nat.cast_le.mpr (le_of_not_gt hnot)
    nlinarith only [hreal, hpM, hd, hα]
  have he : row (Ioc 0 N) primeWeight (floorMul α) d =
      ∑ p ∈ (Ioc M N).filter (fun p => p.Prime ∧ d ∣ floorMul α p), Real.log p := by
    unfold row primeWeight
    rw [sum_filter]
    have hs : Ioc M N ⊆ Ioc 0 N := by
      intro p hp
      exact mem_Ioc.mpr ⟨(Nat.zero_le M).trans_lt (mem_Ioc.mp hp).1, (mem_Ioc.mp hp).2⟩
    rw [sum_subset hs]
    · apply sum_congr rfl
      intro p hp
      by_cases hpp : p.Prime <;> by_cases hdp : d ∣ floorMul α p <;> simp [hpp, hdp]
    · intro p hp hnot
      by_cases hdp : d ∣ floorMul α p
      · exact (hnot (mem_Ioc.mpr ⟨hpM p hp hdp, (mem_Ioc.mp hp).2⟩)).elim
      · simp [hdp]
  rw [he]
  calc
    _ ≤ ∑ p ∈ (Ioc M N).filter (fun p => p.Prime ∧ d ∣ floorMul α p), Real.log N := by
      apply sum_le_sum
      intro p hp
      exact Erdos972ExponentialSum.monotone_log_natCast (mem_Ioc.mp (mem_filter.mp hp).1).2
    _ = (((Ioc M N).filter (fun p => p.Prime ∧ d ∣ floorMul α p)).card:ℝ)*Real.log N := by
      rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (prime_divisor_row_card_le hα hdα hM hN)) (Real.log_natCast_nonneg N)

/-- Combining the first moment with row multiplicity controls the full
(noncentered) second moment in a block below N. -/
theorem block_secondMoment_upper {α : ℝ} (hα : 1 ≤ α) {N D K M : ℕ}
    (hD : 0 < D) (hM : 0 < M) (hNK : floorMul α N ≤ D*K)
    (hDM : α*(M:ℝ) < D) (hNM : N ≤ D*M) {E : ℝ}
    (hrows : ∀ k : ℕ, 0 < k → k ≤ K → ∀ X : ℕ, X ≤ N →
      row (Ioc 0 X) primeWeight (floorMul α) k ≤ 7*(X:ℝ)/k+E) :
    (∑ d ∈ Ioc D (2*D), (row (Ioc 0 N) primeWeight (floorMul α) d)^2) ≤
      ((M:ℝ)*Real.log N)*((K:ℝ)*(14*D+E)) := by
  have hm : 0 ≤ (M:ℝ)*Real.log N := mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  calc
    _ ≤ ∑ d ∈ Ioc D (2*D), ((M:ℝ)*Real.log N)*row (Ioc 0 N) primeWeight (floorMul α) d := by
      apply sum_le_sum
      intro d hd
      have hdD := (mem_Ioc.mp hd).1.le
      have hnonneg : 0 ≤ row (Ioc 0 N) primeWeight (floorMul α) d := by
        unfold row
        apply sum_nonneg
        intro p hp
        split_ifs <;> first | exact primeWeight_nonneg p | exact le_rfl
      have hu := prime_row_upper_of_large_divisor hα hM
        (hDM.trans_le (Nat.cast_le.mpr hdD)) (hNM.trans (Nat.mul_le_mul_right M hdD))
      nlinarith only [hnonneg, hu]
    _ = ((M:ℝ)*Real.log N)*(∑ d ∈ Ioc D (2*D), row (Ioc 0 N) primeWeight (floorMul α) d) := by
      rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (block_firstMoment_upper hα hD hNK hrows) hm


open Filter Erdos972PolynomialRowScales Erdos972PrimeRotation
open Erdos972ScaledPrimeRows Erdos972DualPrimeRows
attribute [local irreducible] root64

/-- The complementary first and second moments hold simultaneously on
arbitrarily large actual irrational good scales. No divisor-row estimate
is left as a hypothesis in this theorem. -/
theorem exists_large_block_moment_scale {α : ℝ} (hα : 1 < α) (hI : Irrational α) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ 0 < u ∧ ∀ D K M : ℕ, 0 < D → 0 < M →
      K ≤ root64 u → floorMul α (u^6) ≤ D*K → α*(M:ℝ) < D → u^6 ≤ D*M →
      (∑ d ∈ Ioc D (2*D), row (Ioc 0 (u^6)) primeWeight (floorMul α) d) ≤
          14*(D:ℝ)*K+(u:ℝ)^6 ∧
      (∑ d ∈ Ioc D (2*D), (row (Ioc 0 (u^6)) primeWeight (floorMul α) d)^2) ≤
          ((M:ℝ)*Real.log (u^6 : ℕ))*(14*(D:ℝ)*K+(u:ℝ)^6) := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (eventually_rough_prime_budget.and (root64_tendsto.eventually_ge_atTop 2048))
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
  obtain ⟨⟨hpsi, hbudget⟩, hv⟩ := hT u hTu
  let E := scaledRowError 1 u (root64 u)
  have hE0 : 0 ≤ E := scaledRowError_nonneg _ _ _
  have hEv : E*(root64 u:ℝ) ≤ (u:ℝ)^6 := by
    have hvR : (0:ℝ) < root64 u := Nat.cast_pos.mpr (root64_bounds hu).1
    have hpw := sub_nonneg.mpr (Chebyshev.theta_le_psi (u^6 : ℕ))
    have hb := (le_div_iff₀ (show 0 < 16*(root64 u:ℝ) by positivity)).mp hbudget
    change (E+(Chebyshev.psi (u^6 : ℕ)-Chebyshev.theta (u^6 : ℕ)))*
      (16*(root64 u:ℝ)) ≤ ((u^6:ℕ):ℝ) at hb
    rw [Nat.cast_pow] at hb
    have hm := mul_nonneg hpw hvR.le
    simp only [Nat.cast_pow] at hm
    have hEm := mul_nonneg hE0 hvR.le
    nlinarith only [hb, hm, hEm]
  have hrows (k : ℕ) (hk : 0 < k) (hkv : k ≤ root64 u) (X : ℕ) (hX : X ≤ u^6) :
      row (Ioc 0 X) primeWeight (floorMul α) k ≤ 7*(X:ℝ)/k+E := by
    have hr' := input_divisor_row_discrepancy
      (show 0 ≤ α by linarith) r hr.le (K := 1) (by norm_num) (by simpa using hv)
      (root64_bounds hu).2.1 (by simpa using hlo) (by simpa using hhi) hk hkv hX
    have hsub := (inputDivisorRow_prime_error α k X).1
    have hupper := (abs_le.mp hr').2
    have hmean : Chebyshev.psi X/(k:ℝ) ≤ 7*(X:ℝ)/k :=
      div_le_div_of_nonneg_right (psi_le_seven_mul (Nat.cast_nonneg X)) (Nat.cast_nonneg k)
    change inputDivisorRow α k X-Chebyshev.psi X/(k:ℝ) ≤ E at hupper
    linarith only [hsub, hupper, hmean]
  refine ⟨u, hBu, hu, ?_⟩
  intro D K M hD hM hKv hNK hDM hNM
  have hEK : E*(K:ℝ) ≤ (u:ℝ)^6 :=
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hKv) hE0).trans hEv
  have hmain : (K:ℝ)*(14*D+E) ≤ 14*(D:ℝ)*K+(u:ℝ)^6 := by
    nlinarith only [hEK]
  have hfirst := block_firstMoment_upper hα.le hD hNK
    (fun k hk hkK X hX => hrows k hk (hkK.trans hKv) X hX)
  have hsecond := block_secondMoment_upper hα.le hD hM hNK hDM hNM
    (fun k hk hkK X hX => hrows k hk (hkK.trans hKv) X hX)
  exact ⟨hfirst.trans hmain, hsecond.trans (mul_le_mul_of_nonneg_left hmain
    (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)))⟩


/-- Passing to squared centered row errors retains an explicit mean-square
cost. This inequality does not assert cancellation of the off-diagonal. -/
theorem block_centeredEnergy_le_secondMoment (α : ℝ) (N : ℕ) {D : ℕ} (hD : 0 < D) :
    (∑ d ∈ Ioc D (2*D), (row (Ioc 0 N) primeWeight (floorMul α) d-
      Chebyshev.psi N/(d:ℝ))^2) ≤
      (∑ d ∈ Ioc D (2*D), (row (Ioc 0 N) primeWeight (floorMul α) d)^2)+
        49*(N:ℝ)^2/D := by
  have hDR : (0:ℝ) < D := Nat.cast_pos.mpr hD
  have hs : (∑ d ∈ Ioc D (2*D), (row (Ioc 0 N) primeWeight (floorMul α) d-
      Chebyshev.psi N/(d:ℝ))^2) ≤
      ∑ d ∈ Ioc D (2*D), ((row (Ioc 0 N) primeWeight (floorMul α) d)^2+
        (7*(N:ℝ)/D)^2) := by
    apply sum_le_sum
    intro d hd
    have hr0 : 0 ≤ row (Ioc 0 N) primeWeight (floorMul α) d := by
      unfold row
      apply sum_nonneg
      intro p hp
      split_ifs <;> first | exact primeWeight_nonneg p | exact le_rfl
    have hx0 : 0 ≤ Chebyshev.psi N/(d:ℝ) :=
      div_nonneg (Chebyshev.psi_nonneg _) (Nat.cast_nonneg _)
    have hx : Chebyshev.psi N/(d:ℝ) ≤ 7*(N:ℝ)/D := by
      apply (div_le_div_of_nonneg_right (psi_le_seven_mul (Nat.cast_nonneg N)) (Nat.cast_nonneg d)).trans
      exact div_le_div_of_nonneg_left (by positivity) hDR
        (Nat.cast_le.mpr (mem_Ioc.mp hd).1.le)
    have hsq := pow_le_pow_left₀ hx0 hx 2
    have hm := mul_nonneg hr0 hx0
    nlinarith only [hsq, hm]
  apply hs.trans_eq
  rw [sum_add_distrib]
  congr 1
  simp only [sum_const, Nat.card_Ioc, show 2*D-D = D by omega, nsmul_eq_mul]
  field_simp
  ring

/-- A centered block-energy bound at the same actual irrational good scales.
Both the row second moment and the mean-square correction are accounted for. -/
theorem exists_large_block_dispersion_scale {α : ℝ} (hα : 1 < α) (hI : Irrational α) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ 0 < u ∧ ∀ D K M : ℕ, 0 < D → 0 < M →
      K ≤ root64 u → floorMul α (u^6) ≤ D*K → α*(M:ℝ) < D → u^6 ≤ D*M →
      (∑ d ∈ Ioc D (2*D), (row (Ioc 0 (u^6)) primeWeight (floorMul α) d-
        Chebyshev.psi (u^6 : ℕ)/(d:ℝ))^2) ≤
          ((M:ℝ)*Real.log (u^6 : ℕ))*(14*(D:ℝ)*K+(u:ℝ)^6)+
            49*((u^6:ℕ):ℝ)^2/D := by
  obtain ⟨u, hBu, hu, hb⟩ := exists_large_block_moment_scale hα hI B
  refine ⟨u, hBu, hu, ?_⟩
  intro D K M hD hM hKv hNK hDM hNM
  exact (block_centeredEnergy_le_secondMoment α (u^6) hD).trans
    (add_le_add (hb D K M hD hM hKv hNK hDM hNM).2 le_rfl)

#print axioms block_centeredEnergy_le_secondMoment
#print axioms exists_large_block_dispersion_scale
#print axioms exists_large_block_moment_scale
#print axioms block_firstMoment_switch
#print axioms block_firstMoment_upper
#print axioms prime_row_upper_of_large_divisor
#print axioms block_secondMoment_upper
end Erdos972LargeDivisorBlockMoment
