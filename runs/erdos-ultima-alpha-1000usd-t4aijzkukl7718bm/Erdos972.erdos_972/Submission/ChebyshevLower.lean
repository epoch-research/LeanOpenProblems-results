import FormalConjecturesUtil

/-!
Elementary lower Chebyshev bounds used in developing an averaged prime-pair
count. These estimates concern primes individually and do not prove Erdős 972.
-/

namespace Erdos972ChebyshevLower

open Finset ArithmeticFunction

/-- Every prime-power divisor of a binomial coefficient is at most its top index. -/
lemma prime_power_divisor_choose_le {n k d : ℕ} (hn : 0 < n) (hk : k ≤ n)
    (hd : d ∣ n.choose k) (hpow : IsPrimePow d) : d ≤ n := by
  obtain ⟨p, j, hp, _, rfl⟩ := (isPrimePow_nat_iff d).mp hpow
  have hj := (hp.pow_dvd_iff_le_factorization (Nat.choose_ne_zero hk)).mp hd
  exact (Nat.pow_le_pow_right hp.pos hj).trans (Nat.pow_factorization_choose_le hn)

/-- The von Mangoldt divisor identity bounds `log (n choose k)` by `ψ(n)`. -/
lemma log_choose_le_psi {n k : ℕ} (hk : k ≤ n) :
    Real.log (n.choose k) ≤ Chebyshev.psi n := by
  classical
  by_cases hn : n = 0
  · subst n
    have : k = 0 := by omega
    subst k
    simp [Chebyshev.psi]
  rw [← vonMangoldt_sum, Chebyshev.psi, Nat.floor_natCast]
  calc
    (∑ d ∈ (n.choose k).divisors, Λ d) =
        ∑ d ∈ (n.choose k).divisors.filter IsPrimePow, Λ d := by
      symm
      apply sum_filter_of_ne
      intro d _ hd
      exact vonMangoldt_ne_zero_iff.mp hd
    _ ≤ ∑ d ∈ Ioc 0 n, Λ d := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro d hd
        obtain ⟨hd, hpow⟩ := mem_filter.mp hd
        exact mem_Ioc.mpr ⟨Nat.pos_of_mem_divisors hd,
          prime_power_divisor_choose_le (Nat.pos_of_ne_zero hn) hk
            (Nat.dvd_of_mem_divisors hd) hpow⟩
      · intro _ _ _
        exact vonMangoldt_nonneg

/-- A quantitative lower bound, valid at every even natural argument. -/
theorem psi_two_mul_lower (n : ℕ) :
    (n : ℝ) * Real.log 4 - Real.log (2 * n + 1) ≤ Chebyshev.psi (2 * n) := by
  have hbin := Nat.four_pow_le_two_mul_add_one_mul_central_binom n
  have hcast : (4 : ℝ) ^ n ≤ (2 * n + 1) * ((2 * n).choose n : ℕ) := by
    exact_mod_cast hbin
  have hcpos : (0 : ℝ) < ((2 * n).choose n : ℕ) := by
    exact_mod_cast Nat.choose_pos (by omega : n ≤ 2 * n)
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (4 : ℝ) ^ n) hcast
  rw [Real.log_pow, Real.log_mul (by positivity) hcpos.ne'] at hlog
  have hu := log_choose_le_psi (by omega : n ≤ 2 * n)
  push_cast at hu
  linarith

/-- A lower Chebyshev estimate on the real line, with an explicit logarithmic error. -/
theorem psi_lower {x : ℝ} (hx : 2 ≤ x) :
    Real.log 2 * x - 2 * Real.log 2 - Real.log (x + 1) ≤ Chebyshev.psi x := by
  let n : ℕ := ⌊x / 2⌋₊
  have hnle : (2 : ℝ) * n ≤ x := by
    have h := Nat.floor_le (by linarith : 0 ≤ x / 2)
    change (n : ℝ) ≤ x / 2 at h
    linarith
  have hnlo : x - 2 ≤ (2 : ℝ) * n := by
    have h := Nat.lt_floor_add_one (x / 2)
    change x / 2 < (n : ℝ) + 1 at h
    linarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 * n + 1)
    (show (2 : ℝ) * n + 1 ≤ x + 1 by linarith)
  have hl := psi_two_mul_lower n
  have hm := Chebyshev.psi_mono hnle
  rw [hlog4] at hl
  have hp := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  nlinarith

/-- Removing prime powers gives an unconditional lower bound for `θ`. -/
theorem theta_lower {x : ℝ} (hx : 2 ≤ x) :
    Real.log 2 * x - 2 * Real.log 2 - Real.log (x + 1) -
      2 * Real.sqrt x * Real.log x ≤ Chebyshev.theta x := by
  have hpsi := psi_lower hx
  have herr := (le_abs_self (Chebyshev.psi x - Chebyshev.theta x)).trans
    (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith : 1 ≤ x))
  linarith

open Filter in
/-- In particular, the prime-weighted counting function has a positive linear
lower bound for every sufficiently large real argument. -/
theorem eventually_theta_lower :
    ∀ᶠ x : ℝ in atTop, (Real.log 2 / 2) * x ≤ Chebyshev.theta x := by
  have hε : 0 < Real.log 2 / 8 := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hlog := Real.isLittleO_log_id_atTop.bound hε
  have hsqrt := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).bound hε
  filter_upwards [eventually_ge_atTop (24 : ℝ), hlog, hsqrt] with x hx hl hs
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hs0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hx0,
    abs_of_nonneg hlog0] at hl
  rw [← Real.sqrt_eq_rpow] at hs
  simp only [Real.norm_eq_abs, abs_of_nonneg hlog0, abs_of_nonneg hs0] at hs
  have hsmul := mul_le_mul_of_nonneg_left hs hs0
  have hs2 := Real.sq_sqrt hx0
  have hlogshift : Real.log (x + 1) ≤ Real.log 2 + Real.log x := by
    calc
      _ ≤ Real.log (2 * x) := Real.log_le_log (by linarith) (by linarith)
      _ = _ := Real.log_mul (by norm_num) (by linarith)
  have hlower := theta_lower (by linarith : 2 ≤ x)
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

/-- A difference of theta values is the logarithmic prime sum on the intervening
natural interval. -/
lemma theta_sub_eq_sum {a b : ℕ} (hab : a ≤ b) :
    Chebyshev.theta b - Chebyshev.theta a =
      ∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log p := by
  classical
  simp only [Chebyshev.theta, Nat.floor_natCast, sum_filter]
  have h := sum_Ioc_consecutive (fun p : ℕ => if p.Prime then Real.log p else 0)
    (Nat.zero_le a) hab
  linarith

open MeasureTheory

/-- One weighted prime-pair window in slope space. -/
noncomputable def pairBox (p q : ℕ) (α : ℝ) : ℝ :=
  (Set.Ico ((q : ℝ) / p) (((q : ℝ) + 1) / p)).indicator
    (fun _ => Real.log p * Real.log q) α

lemma integrable_pairBox (p q : ℕ) : Integrable (pairBox p q) := by
  exact (integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Ico

lemma integral_pairBox {p : ℕ} (hp : 0 < p) (q : ℕ) :
    (∫ α : ℝ, pairBox p q α) = Real.log p * Real.log q / p := by
  unfold pairBox
  rw [integral_indicator_const _ measurableSet_Ico, Real.volume_real_Ico,
    smul_eq_mul]
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have he : ((q : ℝ) + 1) / p - (q : ℝ) / p = 1 / p := by ring
  rw [he, max_eq_left (by positivity)]
  ring

/-- Prime inputs at most `N`, and prime outputs strictly between `p` and `8p`.
The function is supported on slopes strictly between one and nine. -/
noncomputable def weightedPairs (N : ℕ) (α : ℝ) : ℝ := by
  classical
  exact ∑ p ∈ (Ioc 0 N).filter Nat.Prime,
    ∑ q ∈ (Ioc p (8 * p)).filter Nat.Prime, pairBox p q α

lemma integrable_weightedPairs (N : ℕ) : Integrable (weightedPairs N) := by
  classical
  apply integrable_finset_sum
  intro p hp
  exact integrable_finset_sum _ (fun q _ => integrable_pairBox p q)

/-- An exact first moment for this genuine prime-pair count. -/
theorem integral_weightedPairs (N : ℕ) :
    (∫ α : ℝ, weightedPairs N α) =
      ∑ p ∈ (Ioc 0 N).filter Nat.Prime,
        (Real.log p / p) * (Chebyshev.theta (8 * p) - Chebyshev.theta p) := by
  classical
  unfold weightedPairs
  rw [integral_finset_sum _ (fun p _ =>
    integrable_finset_sum _ (fun q _ => integrable_pairBox p q))]
  apply sum_congr rfl
  intro p hp
  have hp0 : 0 < p := (mem_Ioc.mp (mem_filter.mp hp).1).1
  rw [integral_finset_sum _ (fun q _ => integrable_pairBox p q)]
  simp_rw [integral_pairBox hp0]
  rw [show (8 : ℝ) * p = ((8 * p : ℕ) : ℝ) by push_cast; rfl,
    theta_sub_eq_sum (by omega : p ≤ 8 * p), mul_sum]
  apply sum_congr rfl
  intro q hq
  ring

lemma weightedPairs_nonneg (N : ℕ) (α : ℝ) : 0 ≤ weightedPairs N α := by
  classical
  apply sum_nonneg
  intro p hp
  apply sum_nonneg
  intro q hq
  apply Set.indicator_nonneg
  intro _ _
  exact mul_nonneg
    (Real.log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_le))
    (Real.log_nonneg (by exact_mod_cast (mem_filter.mp hq).2.one_le))

lemma exists_positive_summand {ι : Type*} {s : Finset ι} {f : ι → ℝ}
    (h : 0 < ∑ i ∈ s, f i) : ∃ i ∈ s, 0 < f i :=
  exists_lt_of_sum_lt (f := fun _ => 0) (by simpa only [sum_const_zero] using h)

/-- Positivity of the first-moment integrand really supplies a prime pair. -/
theorem prime_pair_of_weightedPairs_pos {N : ℕ} {α : ℝ}
    (h : 0 < weightedPairs N α) :
    ∃ p : ℕ, p ≤ N ∧ p.Prime ∧ (⌊α * p⌋₊).Prime := by
  classical
  obtain ⟨p, hp, hsum⟩ := exists_positive_summand h
  obtain ⟨q, hq, hbox⟩ := exists_positive_summand hsum
  have hpp := (mem_filter.mp hp).2
  have hqp := (mem_filter.mp hq).2
  have hm : α ∈ Set.Ico ((q : ℝ) / p) (((q : ℝ) + 1) / p) := by
    by_contra hn
    simp only [pairBox, Set.indicator_of_notMem hn] at hbox
    linarith
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hpp.pos
  have hfloor : ⌊α * p⌋₊ = q := (Nat.floor_eq_iff' hqp.ne_zero).mpr
    ⟨(div_le_iff₀ hpR).mp hm.1, (lt_div_iff₀ hpR).mp hm.2⟩
  exact ⟨p, (mem_Ioc.mp (mem_filter.mp hp).1).2, hpp, by simpa only [hfloor] using hqp⟩

lemma weightedPairs_eq_zero_of_not_mem (N : ℕ) {α : ℝ}
    (hα : α ∉ Set.Ioo (1 : ℝ) 9) : weightedPairs N α = 0 := by
  classical
  apply sum_eq_zero
  intro p hp
  apply sum_eq_zero
  intro q hq
  apply Set.indicator_of_notMem
  intro hm
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.one_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hqp : (p : ℝ) < q := by
    exact_mod_cast (mem_Ioc.mp (mem_filter.mp hq).1).1
  have hq8 : (q : ℝ) ≤ 8 * p := by
    exact_mod_cast (mem_Ioc.mp (mem_filter.mp hq).1).2
  have hleft := (div_le_iff₀ hp0).mp hm.1
  have hright := (lt_div_iff₀ hp0).mp hm.2
  apply hα
  exact ⟨by nlinarith, by nlinarith⟩

/-- Chebyshev bounds alone give a lower bound for the averaged pair count,
after discarding finitely many small prime inputs. -/
theorem exists_integral_weightedPairs_lower :
    ∃ B : ℕ, ∀ N : ℕ, B ≤ N →
      2 * Real.log 2 * (Chebyshev.theta N - Chebyshev.theta B) ≤
        ∫ α : ℝ, weightedPairs N α := by
  classical
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp eventually_theta_lower
  let B : ℕ := ⌈x₀⌉₊
  have hB : x₀ ≤ (B : ℝ) := Nat.le_ceil x₀
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  let F : ℕ → ℝ := fun p => (Real.log p / p) *
    (Chebyshev.theta (8 * p) - Chebyshev.theta p)
  have hFnonneg (p : ℕ) (hp : p.Prime) : 0 ≤ F p := by
    apply mul_nonneg
    · exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_le)) (Nat.cast_nonneg p)
    · exact sub_nonneg.mpr (Chebyshev.theta_mono (by nlinarith [Nat.cast_nonneg (α := ℝ) p] : (p : ℝ) ≤ 8 * p))
  have hFlb (p : ℕ) (hp : p.Prime) (hBp : B < p) :
      2 * Real.log 2 * Real.log p ≤ F p := by
    have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
    have hBpR : (B : ℝ) < p := Nat.cast_lt.mpr hBp
    have hl := hx₀ (8 * p) (by linarith)
    have hu := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg p)
    rw [hlog4] at hu
    have hdiff : 2 * Real.log 2 * p ≤ Chebyshev.theta (8 * p) - Chebyshev.theta p := by
      nlinarith
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
    calc
      _ = (Real.log p / p) * (2 * Real.log 2 * p) := by field_simp
      _ ≤ F p := mul_le_mul_of_nonneg_left hdiff (div_nonneg hlogp hpR.le)
  refine ⟨B, ?_⟩
  intro N hBN
  rw [integral_weightedPairs, theta_sub_eq_sum hBN, mul_sum]
  calc
    _ ≤ ∑ p ∈ (Ioc B N).filter Nat.Prime, F p := by
      apply sum_le_sum
      intro p hp
      exact hFlb p (mem_filter.mp hp).2 (mem_Ioc.mp (mem_filter.mp hp).1).1
    _ ≤ ∑ p ∈ (Ioc 0 N).filter Nat.Prime, F p := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨hp, hpp⟩ := mem_filter.mp hp
        obtain ⟨hBp, hpN⟩ := mem_Ioc.mp hp
        exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, hpN⟩, hpp⟩
      · intro p hp _
        exact hFnonneg p (mem_filter.mp hp).2

open Filter in
/-- An unconditional linear first-moment lower bound for a weighted count of
actual prime pairs. This is an average over slopes, not a pointwise assertion. -/
theorem eventually_integral_weightedPairs_lower :
    ∀ᶠ N : ℕ in atTop, (Real.log 2 ^ 2 / 2) * N ≤
      ∫ α : ℝ, weightedPairs N α := by
  obtain ⟨B, hB⟩ := exists_integral_weightedPairs_lower
  have htheta : ∀ᶠ N : ℕ in atTop,
      (Real.log 2 / 2) * N ≤ Chebyshev.theta N :=
    tendsto_natCast_atTop_atTop.eventually eventually_theta_lower
  have hlarge : ∀ᶠ N : ℕ in atTop,
      4 * Chebyshev.theta B / Real.log 2 ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop B, htheta, hlarge] with N hBN ht hN
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmul := (div_le_iff₀ hp).mp hN
  have hmul' := mul_le_mul_of_nonneg_left hmul hp.le
  have ht' := mul_le_mul_of_nonneg_left ht (show 0 ≤ 2 * Real.log 2 by positivity)
  have hi := hB N hBN
  nlinarith

#print axioms weightedPairs_eq_zero_of_not_mem
#print axioms eventually_integral_weightedPairs_lower

#print axioms integral_weightedPairs
#print axioms prime_pair_of_weightedPairs_pos

#print axioms eventually_theta_lower

#print axioms log_choose_le_psi
#print axioms psi_lower
#print axioms theta_lower

end Erdos972ChebyshevLower
