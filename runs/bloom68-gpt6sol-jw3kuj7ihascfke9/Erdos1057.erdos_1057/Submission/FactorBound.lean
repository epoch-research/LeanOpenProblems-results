import Submission.Korselt

/-!
# Carmichael numbers with boundedly many prime factors

Take a largest prime factor `q` of a Carmichael number `n`, and let `m = n/q`.
Squarefreeness and the number of prime factors bound `m`, while Korselt's
congruence makes `q - 1` a divisor of `m - 1`. Counting these divisors and
using the elementary summatory-divisor bound yields a power-saving upper bound
when the number of prime factors is fixed. This auxiliary upper bound does not
resolve the unrestricted Erdős 1057 counting problem.
-/
namespace Erdos1057
open Nat

/-- An integer cutoff for the cofactor after removing a largest prime factor. -/
noncomputable def cofactorCutoff (X r : ℕ) : ℕ :=
  ⌊(X : ℝ) ^ (((r - 1 : ℕ) : ℝ) / (r : ℝ))⌋₊

/-- A Carmichael number with at most `r` distinct prime factors has a prime factor `q`
whose cofactor `m` is controlled by `m ^ r ≤ n ^ (r-1)` and `q-1 ∣ m-1`. -/
theorem isCarmichael_exists_power_bounded_cofactor {n r : ℕ}
    (hn : IsCarmichael n) (hr : 1 ≤ r) (hcard : n.primeFactors.card ≤ r) :
    ∃ q m : ℕ, q.Prime ∧ n = q * m ∧ n ≤ q ^ r ∧
      m ^ r ≤ n ^ (r - 1) ∧ q - 1 ∣ m - 1 := by
  have hn1 : 1 < n := (hn 1 (by omega) (by simp)).2.2
  have hnonempty : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hn1
  let q : ℕ := n.primeFactors.max' hnonempty
  have hqmem : q ∈ n.primeFactors := Finset.max'_mem _ _
  have hq : q.Prime := Nat.prime_of_mem_primeFactors hqmem
  have hnprod : (∏ p ∈ n.primeFactors, p) = n :=
    Nat.prod_primeFactors_of_squarefree (isCarmichael_squarefree hn)
  have hqbound (p : ℕ) (hp : p ∈ n.primeFactors) : p ≤ q := by
    exact Finset.le_max' _ _ hp
  have hn_le_qcard : n ≤ q ^ n.primeFactors.card := by
    calc
      n = (∏ p ∈ n.primeFactors, p) := hnprod.symm
      _ ≤ q ^ n.primeFactors.card :=
        Finset.prod_le_pow_card n.primeFactors id q (fun p hp => hqbound p hp)
  have hn_le_qpow : n ≤ q ^ r :=
    hn_le_qcard.trans (pow_le_pow_right₀ (hq.one_le) hcard)
  obtain ⟨m, hm⟩ := Nat.dvd_of_mem_primeFactors hqmem
  have hnfac : n = q * m := hm
  have hmpow : m ≤ q ^ (r - 1) := by
    apply Nat.le_of_mul_le_mul_left (c := q) ?_ hq.pos
    calc
      q * m = n := hnfac.symm
      _ ≤ q ^ r := hn_le_qpow
      _ = q ^ ((r - 1) + 1) := by rw [Nat.sub_add_cancel hr]
      _ = q * q ^ (r - 1) := by simp only [Nat.pow_succ, mul_comm]
  have hmr : m ^ r ≤ n ^ (r - 1) := by
    calc
      m ^ r = m ^ ((r - 1) + 1) := by rw [Nat.sub_add_cancel hr]
      _ = m * m ^ (r - 1) := by simp only [Nat.pow_succ, mul_comm]
      _ ≤ q ^ (r - 1) * m ^ (r - 1) :=
        Nat.mul_le_mul_right (m ^ (r - 1)) hmpow
      _ = n ^ (r - 1) := by rw [hnfac, mul_pow]
  exact ⟨q, m, hq, hnfac, hn_le_qpow, hmr,
    isCarmichael_cofactor_constraint hn hq hnfac⟩

/-- The cofactor of a largest prime factor is at most `X^((r-1)/r)` (rounded down). -/
theorem isCarmichael_exists_cofactor_le_cutoff {n X r : ℕ}
    (hn : IsCarmichael n) (hX : n ≤ X) (hr : 1 ≤ r)
    (hcard : n.primeFactors.card ≤ r) :
    ∃ q m : ℕ, q.Prime ∧ n = q * m ∧ q - 1 ∣ m - 1 ∧ m ≤ cofactorCutoff X r := by
  obtain ⟨q, m, hq, hnfac, _, hmr, hdiv⟩ :=
    isCarmichael_exists_power_bounded_cofactor hn hr hcard
  have hmrX : m ^ r ≤ X ^ (r - 1) :=
    hmr.trans (Nat.pow_le_pow_left hX (r - 1))
  let a : ℝ := (X : ℝ) ^ (((r - 1 : ℕ) : ℝ) / (r : ℝ))
  have hra : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have har : a ^ r = (X : ℝ) ^ (r - 1 : ℕ) := by
    have heq : (((r - 1 : ℕ) : ℝ) / (r : ℝ)) * (r : ℝ) = (r - 1 : ℕ) := by
      field_simp
    calc
      a ^ r = (X : ℝ) ^ ((((r - 1 : ℕ) : ℝ) / (r : ℝ)) * (r : ℝ)) := by
        dsimp [a]
        exact (Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ X) _ r).symm
      _ = (X : ℝ) ^ ((r - 1 : ℕ) : ℝ) := by rw [heq]
      _ = (X : ℝ) ^ (r - 1 : ℕ) := Real.rpow_natCast _ _
  have hmreal : (m : ℝ) ≤ a := by
    apply (Real.rpow_le_rpow_iff (by positivity : (0 : ℝ) ≤ m) ha hra).mp
    rw [Real.rpow_natCast (m : ℝ) r, Real.rpow_natCast a r, har]
    exact_mod_cast hmrX
  exact ⟨q, m, hq, hnfac, hdiv, Nat.le_floor hmreal⟩

/-- Carmichael numbers `n ≤ X` with at most `r` distinct prime factors. -/
def boundedFactorCarmichaels (X r : ℕ) : Set ℕ :=
  {n | IsCarmichael n ∧ n ≤ X ∧ n.primeFactors.card ≤ r}

/-- The divisor-sum bound, before estimating the summatory divisor function. -/
theorem boundedFactorCarmichaels_card_le_divisor_sum (X r : ℕ) (hr : 1 ≤ r) :
    (boundedFactorCarmichaels X r).ncard ≤
      ∑ t ∈ Finset.Ioc 0 (cofactorCutoff X r), t.divisors.card := by
  classical
  let M := cofactorCutoff X r
  let s : Finset ℕ := (Finset.Ioc 0 M).biUnion fun t =>
    t.divisors.image (fun d => (d + 1) * (t + 1))
  have hcover : boundedFactorCarmichaels X r ⊆ (s : Set ℕ) := by
    intro n hn
    obtain ⟨hnC, hnX, hncard⟩ := hn
    obtain ⟨q, m, hq, hnfac, hdiv, hmM⟩ :=
      isCarmichael_exists_cofactor_le_cutoff hnC hnX hr hncard
    have hm2 : 2 ≤ m := hq.two_le.trans (isCarmichael_prime_le_cofactor hnC hq hnfac)
    let t : ℕ := m - 1
    have htpos : 0 < t := by dsimp [t]; omega
    have htM : t ≤ M := by dsimp [M, t]; omega
    have hqd : q - 1 ∈ t.divisors :=
      Nat.mem_divisors.mpr ⟨hdiv, by omega⟩
    change n ∈ s
    apply Finset.mem_biUnion.mpr
    refine ⟨t, Finset.mem_Ioc.mpr ⟨htpos, htM⟩, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨q - 1, hqd, ?_⟩
    change (q - 1 + 1) * (t + 1) = n
    dsimp [t]
    rw [Nat.sub_add_cancel hq.one_le, Nat.sub_add_cancel (by omega : 1 ≤ m)]
    exact hnfac.symm
  calc
    (boundedFactorCarmichaels X r).ncard ≤ s.card := by
      simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hcover
    _ ≤ ∑ t ∈ Finset.Ioc 0 M,
        (t.divisors.image (fun d => (d + 1) * (t + 1))).card := Finset.card_biUnion_le
    _ ≤ ∑ t ∈ Finset.Ioc 0 M, t.divisors.card :=
      Finset.sum_le_sum fun t _ => Finset.card_image_le

/-- Elementary summatory divisor bound, using `∑_{d ≤ M} ⌊M/d⌋` and the harmonic sum. -/
private theorem sum_card_divisors_le (M : ℕ) :
    ((∑ t ∈ Finset.Ioc 0 M, t.divisors.card : ℕ) : ℝ) ≤
      (M : ℝ) * (1 + Real.log (M : ℝ)) := by
  have hsum : (∑ t ∈ Finset.Ioc 0 M, t.divisors.card) =
      (∑ t ∈ Finset.Ioc 0 M, (M / t : ℕ)) := by
    simpa only [ArithmeticFunction.sigma_zero_apply] using
      (ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div M)
  have hharm : (∑ t ∈ Finset.Ioc 0 M, (t : ℝ)⁻¹) = (harmonic M : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    simp only [Rat.cast_inv, Rat.cast_natCast, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]
  calc
    ((∑ t ∈ Finset.Ioc 0 M, t.divisors.card : ℕ) : ℝ) =
        ((∑ t ∈ Finset.Ioc 0 M, (M / t : ℕ) : ℕ) : ℝ) := by rw [hsum]
    _ = ∑ t ∈ Finset.Ioc 0 M, ((M / t : ℕ) : ℝ) := by rw [Nat.cast_sum]
    _ ≤ ∑ t ∈ Finset.Ioc 0 M, (M : ℝ) / (t : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      exact Nat.cast_div_le
    _ = (M : ℝ) * (∑ t ∈ Finset.Ioc 0 M, (t : ℝ)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      rw [div_eq_mul_inv]
    _ = (M : ℝ) * (harmonic M : ℝ) := by rw [hharm]
    _ ≤ (M : ℝ) * (1 + Real.log (M : ℝ)) :=
      mul_le_mul_of_nonneg_left (harmonic_le_one_add_log M) (Nat.cast_nonneg M)

/-- The divisor-sum bound in logarithmic form, with a natural-number cofactor cutoff. -/
theorem boundedFactorCarmichaels_card_le_cutoff_log (X r : ℕ) (hr : 1 ≤ r) :
    ((boundedFactorCarmichaels X r).ncard : ℝ) ≤
      (cofactorCutoff X r : ℝ) * (1 + Real.log (cofactorCutoff X r : ℝ)) := by
  calc
    ((boundedFactorCarmichaels X r).ncard : ℝ) ≤
        ((∑ t ∈ Finset.Ioc 0 (cofactorCutoff X r), t.divisors.card : ℕ) : ℝ) := by
      exact_mod_cast boundedFactorCarmichaels_card_le_divisor_sum X r hr
    _ ≤ _ := sum_card_divisors_le (cofactorCutoff X r)

/-- An unconditional `X^((r-1)/r) (1+log X)` bound for Carmichael numbers
with at most `r` distinct prime factors, for `X ≥ 1` and `r ≥ 1`. -/
theorem boundedFactorCarmichaels_card_le_power_log_of_pos (X r : ℕ)
    (hX : 1 ≤ X) (hr : 1 ≤ r) :
    ((boundedFactorCarmichaels X r).ncard : ℝ) ≤
      (X : ℝ) ^ (((r - 1 : ℕ) : ℝ) / (r : ℝ)) * (1 + Real.log (X : ℝ)) := by
  let M := cofactorCutoff X r
  let a : ℝ := (X : ℝ) ^ (((r - 1 : ℕ) : ℝ) / (r : ℝ))
  have hra : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hMr : (M : ℝ) ≤ a := Nat.floor_le ha
  have he : (((r - 1 : ℕ) : ℝ) / (r : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ hra).mpr
    simpa only [one_mul] using
      (show (((r - 1 : ℕ) : ℝ) ≤ (r : ℝ)) by exact_mod_cast Nat.sub_le r 1)
  have haX : a ≤ (X : ℝ) := by
    dsimp [a]
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast hX : (1 : ℝ) ≤ X) he)
  have hlog : Real.log (M : ℝ) ≤ Real.log (X : ℝ) := by
    by_cases hM0 : M = 0
    · simpa only [hM0, Nat.cast_zero, Real.log_zero] using Real.log_natCast_nonneg X
    · exact Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero hM0))
        (hMr.trans haX)
  have hnonneg : 0 ≤ 1 + Real.log (X : ℝ) := by
    have := Real.log_natCast_nonneg X
    linarith
  calc
    ((boundedFactorCarmichaels X r).ncard : ℝ) ≤
        (M : ℝ) * (1 + Real.log (M : ℝ)) :=
      boundedFactorCarmichaels_card_le_cutoff_log X r hr
    _ ≤ (M : ℝ) * (1 + Real.log (X : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg M)
    _ ≤ a * (1 + Real.log (X : ℝ)) :=
      mul_le_mul_of_nonneg_right hMr hnonneg

/-- For every `X` and `r ≥ 3`, there are at most
`X^((r-1)/r) * (1 + log X)` Carmichael numbers up to `X` with at most
`r` distinct prime factors. -/
theorem boundedFactorCarmichaels_card_le_power_log (X r : ℕ) (hr : 3 ≤ r) :
    ((boundedFactorCarmichaels X r).ncard : ℝ) ≤
      (X : ℝ) ^ (((r - 1 : ℕ) : ℝ) / (r : ℝ)) * (1 + Real.log (X : ℝ)) := by
  by_cases hX : X = 0
  · subst X
    have he : (0 : ℝ) < (((r - 1 : ℕ) : ℝ) / (r : ℝ)) := by
      have hprev : (0 : ℝ) < (r - 1 : ℕ) := by
        exact_mod_cast (by omega : 0 < r - 1)
      have hrreal : (0 : ℝ) < (r : ℝ) := by
        exact_mod_cast (by omega : 0 < r)
      exact div_pos hprev hrreal
    have hpow : (0 : ℝ) ^ (((r - 1 : ℕ) : ℝ) / (r : ℝ)) = 0 :=
      Real.zero_rpow he.ne'
    have hcutzero : cofactorCutoff 0 r = 0 := by simp [cofactorCutoff, hpow]
    have hle := boundedFactorCarmichaels_card_le_cutoff_log 0 r (by omega : 1 ≤ r)
    simpa only [hpow, hcutzero, Nat.cast_zero, Real.log_zero, zero_mul] using hle
  · exact boundedFactorCarmichaels_card_le_power_log_of_pos X r
      (Nat.one_le_iff_ne_zero.mpr hX) (by omega)

/-- Equivalent version of the bound written with exponent `1 - 1/r`. -/
theorem boundedFactorCarmichaels_card_le (X r : ℕ) (hr : 3 ≤ r) :
    ((boundedFactorCarmichaels X r).ncard : ℝ) ≤
      (X : ℝ) ^ (1 - 1 / (r : ℝ)) * (1 + Real.log (X : ℝ)) := by
  have hr1 : 1 ≤ r := by omega
  have hrnz : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  have he : (((r - 1 : ℕ) : ℝ) / (r : ℝ)) = 1 - 1 / (r : ℝ) := by
    rw [Nat.cast_sub hr1, Nat.cast_one]
    field_simp [hrnz]
  rw [← he]
  exact boundedFactorCarmichaels_card_le_power_log X r hr

end Erdos1057
