import FormalConjecturesUtil

/-!
# Exact dyadic identities for the Erdős 371 signed count

This is unconditional proof infrastructure, not a proof of the density
conjecture. The only import is `FormalConjecturesUtil`; in particular this
file neither imports nor modifies `Submission.Spec`.

We use the library's conventions `P(0) = 0` and `P(1) = 1`. Consequently the
pair at zero contributes an exceptional `2`, which is retained in every
finite-sum identity. All finite counts and defects are first proved in `ℤ`.
-/

namespace Erdos371Dyadic

local notation "P" => Nat.maxPrimeFac

/-- The signed upward/downward comparison of consecutive greatest prime factors. -/
def s (n : ℕ) : ℤ := if P n < P (n + 1) then 1 else -1

/-- Strict betweenness of the odd intermediate greatest prime factor. -/
def B (n : ℕ) : Prop :=
  min (P n) (P (n + 1)) < P (2 * n + 1) ∧
    P (2 * n + 1) < max (P n) (P (n + 1))

instance (n : ℕ) : Decidable (B n) := by unfold B; infer_instance

/-- The sum of the two signs in a dyadic pair. -/
def t (n : ℕ) : ℤ := s (2 * n) + s (2 * n + 1)

/-- Signed count over the half-open interval `[0, N)`. -/
def D (N : ℕ) : ℤ := ∑ n ∈ Finset.range N, s n

/-- Signed bypass count, with the same half-open endpoint convention. -/
def T (N : ℕ) : ℤ := ∑ n ∈ Finset.range N, if B n then 0 else s n

/-- A common greatest prime factor of coprime numbers would divide `1`. -/
theorem maxPrimeFac_ne_of_coprime {a b : ℕ} (ha : 1 < a)
    (hab : a.Coprime b) : P a ≠ P b := by
  intro heq
  have hb : P a ∣ b := by rw [heq]; exact Nat.maxPrimeFac_dvd
  exact Nat.not_coprime_of_dvd_of_dvd
    (Nat.prime_maxPrimeFac_of_one_lt a ha).one_lt Nat.maxPrimeFac_dvd hb hab

/-- No ties at consecutive integers, including zero and one. -/
theorem maxPrimeFac_succ_ne (n : ℕ) : P (n + 1) ≠ P n := by
  cases n with
  | zero => simp
  | succ n =>
    exact maxPrimeFac_ne_of_coprime (by omega) (by simp)

/-- The three integers underlying the betweenness test are pairwise coprime. -/
theorem dyadic_coprime (n : ℕ) :
    n.Coprime (n + 1) ∧ n.Coprime (2 * n + 1) ∧
      (n + 1).Coprime (2 * n + 1) := by
  refine ⟨by simp, by simp, ?_⟩
  rw [show 2 * n + 1 = (n + 1) + n by omega]
  simp

/-- In particular the three greatest prime factors are distinct for `n ≥ 1`.
The argument also covers `n = 1`, where one of the factors is the convention `P(1) = 1`. -/
theorem triple_maxPrimeFac_ne {n : ℕ} (hn : 1 ≤ n) :
    P n ≠ P (n + 1) ∧ P n ≠ P (2 * n + 1) ∧
      P (n + 1) ≠ P (2 * n + 1) := by
  obtain ⟨h01, h02, h12⟩ := dyadic_coprime n
  exact ⟨(maxPrimeFac_ne_of_coprime (by omega) h01.symm).symm,
    (maxPrimeFac_ne_of_coprime (by omega) h02.symm).symm,
    maxPrimeFac_ne_of_coprime (by omega) h12⟩

/-- Doubling preserves the greatest prime factor once `n ≥ 2`. -/
theorem maxPrimeFac_double {n : ℕ} (hn : 2 ≤ n) : P (2 * n) = P n := by
  rw [Nat.maxPrimeFac_mul (by omega) (by omega), Nat.prime_two.maxPrimeFac_eq_self]
  exact max_eq_right (Nat.prime_maxPrimeFac_of_one_lt n (by omega)).two_le

/-- The abstract ordering calculation behind the dyadic identity. -/
theorem sign_pair_of_distinct (a b c : ℕ) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    (if a < c then (1 : ℤ) else -1) + (if c < b then 1 else -1) =
      2 * (if a < b then 1 else -1) *
        (if min a b < c ∧ c < max a b then 1 else 0) := by
  rcases lt_or_gt_of_ne hab with hab | hba <;>
    simp only [min_def, max_def] <;> split_ifs <;> omega

@[simp] theorem s_zero : s 0 = 1 := by decide +kernel
@[simp] theorem s_one : s 1 = 1 := by decide +kernel
@[simp] theorem not_B_zero : ¬ B 0 := by decide +kernel
@[simp] theorem not_B_one : ¬ B 1 := by decide +kernel

/-- The exceptional pair at zero is `2`, not the betweenness expression `0`. -/
@[simp] theorem t_zero : t 0 = 2 := by decide +kernel

/-- The other small endpoint must be evaluated directly: doubling does not
preserve `P(1)`, but its two signs cancel. -/
@[simp] theorem t_one : t 1 = 0 := by decide +kernel

/-- Exact pointwise doubling identity for every positive integer. -/
theorem sign_double {n : ℕ} (hn : 1 ≤ n) :
    s (2 * n) + s (2 * n + 1) =
      2 * s n * (if B n then 1 else 0) := by
  by_cases h1 : n = 1
  · subst n
    change t 1 = _
    simp
  · have hn2 : 2 ≤ n := by omega
    obtain ⟨h01, h02, h12⟩ := triple_maxPrimeFac_ne hn
    have hnext : P (2 * n + 1 + 1) = P (n + 1) := by
      rw [show 2 * n + 1 + 1 = 2 * (n + 1) by omega]
      exact maxPrimeFac_double (by omega)
    simpa only [s, B, maxPrimeFac_double hn2, hnext] using
      sign_pair_of_distinct (P n) (P (n + 1)) (P (2 * n + 1)) h01 h02 h12

/-- Equivalent form using the dyadic-pair notation. -/
theorem t_eq {n : ℕ} (hn : 1 ≤ n) :
    t n = 2 * s n * (if B n then 1 else 0) := sign_double hn

/-- An all-indices identity displaying the correction at zero explicitly. -/
theorem t_eq_with_boundary (n : ℕ) :
    t n = 2 * s n - 2 * (if B n then 0 else s n) +
      (if n = 0 then 2 else 0) := by
  by_cases h0 : n = 0
  · subst n
    simp
  · rw [t_eq (by omega), if_neg h0]
    by_cases hB : B n <;> simp [hB]

/-- Grouping an initial even-length interval into consecutive pairs. -/
theorem D_double_pair_sum (N : ℕ) :
    D (2 * N) = ∑ n ∈ Finset.range N, t n := by
  induction N with
  | zero => simp [D]
  | succ N ih =>
    rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega]
    simp only [D, Finset.sum_range_succ] at ih ⊢
    rw [ih]
    simp only [t]
    ring

/-- Exact finite-sum defect, valid even at `N = 0` with an explicit boundary term. -/
theorem D_double_defect_all (N : ℕ) :
    D (2 * N) - 2 * D N = (if N = 0 then 0 else 2) - 2 * T N := by
  rw [D_double_pair_sum]
  simp_rw [t_eq_with_boundary]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum, D, T]
  have hboundary : (∑ n ∈ Finset.range N, if n = 0 then (2 : ℤ) else 0) =
      if N = 0 then 0 else 2 := by
    by_cases h0 : N = 0
    · simp [h0]
    · have hN : 0 < N := by omega
      simp [h0, hN]
  rw [hboundary]
  ring

/-- The requested finite-sum defect on every nonempty initial interval. -/
theorem D_double_defect {N : ℕ} (hN : 1 ≤ N) :
    D (2 * N) - 2 * D N = 2 - 2 * T N := by
  simpa [show N ≠ 0 by omega] using D_double_defect_all N

/-- Real normalization of the exact integer identity. The endpoint in the
first numerator is the natural number `2 * N`, and its denominator is exactly
its real cast, `2 * (N : ℝ)`. -/
theorem normalized_double_defect {N : ℕ} (hN : 1 ≤ N) :
    (D (2 * N) : ℝ) / (2 * (N : ℝ)) - (D N : ℝ) / (N : ℝ) =
      (1 - (T N : ℝ)) / (N : ℝ) := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hdefect : (D (2 * N) : ℝ) - 2 * (D N : ℝ) =
      2 - 2 * (T N : ℝ) := by
    exact_mod_cast D_double_defect hN
  field_simp [hNR]
  nlinarith [hdefect]

/-- Dyadic flatness is exactly the vanishing of the signed bypass mean.
Neither of these limits is asserted unconditionally. -/
theorem dyadic_flatness_iff_bypassMean_zero :
    Filter.Tendsto
      (fun N : ℕ => (D (2 * N) : ℝ) / (2 * (N : ℝ)) - (D N : ℝ) / (N : ℝ))
      Filter.atTop (nhds 0) ↔
    Filter.Tendsto (fun N : ℕ => (T N : ℝ) / (N : ℝ))
      Filter.atTop (nhds 0) := by
  have he :
      (fun N : ℕ => (D (2 * N) : ℝ) / (2 * (N : ℝ)) - (D N : ℝ) / (N : ℝ))
        =ᶠ[Filter.atTop]
      (fun N : ℕ => 1 / (N : ℝ) - (T N : ℝ) / (N : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
    rw [normalized_double_defect hN, sub_div]
  have hunit : Filter.Tendsto (fun N : ℕ => 1 / (N : ℝ))
      Filter.atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
  rw [Filter.tendsto_congr' he]
  constructor
  · intro h
    have hid (x y : ℝ) : x - (x - y) = y := by ring
    simpa only [hid, sub_self] using hunit.sub h
  · intro h
    simpa only [sub_self] using hunit.sub h

/-- The easy implication: a vanishing signed mean has vanishing dyadic
differences, and hence vanishing signed bypass mean. -/
theorem bypassMean_zero_of_signedMean_zero
    (hD : Filter.Tendsto (fun N : ℕ => (D N : ℝ) / (N : ℝ))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun N : ℕ => (T N : ℝ) / (N : ℝ))
      Filter.atTop (nhds 0) := by
  apply dyadic_flatness_iff_bypassMean_zero.mp
  have hdbl : Filter.Tendsto (fun N : ℕ => 2 * N) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun N => by change N ≤ 2 * N; omega) Filter.tendsto_id
  simpa only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat, sub_self] using
    (hD.comp hdbl).sub hD

/-- The exact relation to the upward counting function, without importing
any conjecture statement or the separate reflection infrastructure. -/
theorem D_eq_count (N : ℕ) :
    D N = 2 * (((Finset.range N).filter (fun n => P n < P (n + 1))).card : ℤ) - N := by
  unfold D
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.range_add_one, Finset.filter_insert]
    have hn : N ∉ (Finset.range N).filter (fun n => P n < P (n + 1)) := by simp
    by_cases h : P N < P (N + 1)
    · simp only [h, if_true, Finset.card_insert_of_notMem hn, Nat.cast_add,
        Nat.cast_one, s]
      ring
    · simp only [h, if_false, Nat.cast_add, Nat.cast_one, s]
      ring

/-- The natural-density target is equivalent to vanishing of this exact
signed mean. This is an equivalence of propositions, not a proof of either one. -/
theorem hasDensity_iff_signedMean :
    {n | P (n + 1) > P n}.HasDensity (1 / 2) ↔
      Filter.Tendsto (fun N : ℕ => (D N : ℝ) / (N : ℝ))
        Filter.atTop (nhds 0) := by
  have hsum (N : ℕ) : (D N : ℝ) =
      2 * (((Finset.range N).filter (fun n => P n < P (n + 1))).card : ℝ) - N := by
    exact_mod_cast D_eq_count N
  have hcard (N : ℕ) : ({n | P n < P (n + 1)} ∩ Set.Iio N).ncard =
      ((Finset.range N).filter (fun n => P n < P (n + 1))).card := by
    have heq : {n | P n < P (n + 1)} ∩ Set.Iio N =
        ((Finset.range N).filter (fun n => P n < P (n + 1)) : Set ℕ) := by
      ext n
      simp [and_comm]
    rw [heq]
    exact Set.ncard_coe_finset _
  have hpartial (N : ℕ) : {n | P n < P (n + 1)}.partialDensity Set.univ N =
      (((Finset.range N).filter (fun n => P n < P (n + 1))).card : ℝ) / N := by
    simp [Set.partialDensity, hcard]
  have he : (fun N : ℕ => (D N : ℝ) / (N : ℝ)) =ᶠ[Filter.atTop]
      (fun N : ℕ => 2 * {n | P n < P (n + 1)}.partialDensity Set.univ N - 1) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    rw [hsum, hpartial, sub_div, mul_div_assoc, div_self hn]
  constructor
  · intro h
    change Filter.Tendsto (fun N => {n | P n < P (n + 1)}.partialDensity Set.univ N)
      Filter.atTop (nhds (1 / 2 : ℝ)) at h
    have ht : Filter.Tendsto
        (fun N => 2 * {n | P n < P (n + 1)}.partialDensity Set.univ N - 1)
        Filter.atTop (nhds 0) := by
      convert (h.const_mul (2 : ℝ)).sub_const 1 using 1
      norm_num
    exact ht.congr' he.symm
  · intro h
    have ht := h.congr' he
    change Filter.Tendsto (fun N => {n | P n < P (n + 1)}.partialDensity Set.univ N)
      Filter.atTop (nhds (1 / 2 : ℝ))
    have hid (x : ℝ) : (2 * x - 1 + 1) / 2 = x := by ring
    simpa only [hid, zero_add] using (ht.add_const 1).div_const 2

/-- The density target implies a zero bypass mean; no converse is asserted. -/
theorem bypassMean_zero_of_hasDensity
    (h : {n | P (n + 1) > P n}.HasDensity (1 / 2)) :
    Filter.Tendsto (fun N : ℕ => (T N : ℝ) / (N : ℝ))
      Filter.atTop (nhds 0) :=
  bypassMean_zero_of_signedMean_zero (hasDensity_iff_signedMean.mp h)

/-
The converse of the last theorem is deliberately absent. Dyadic flatness
alone is not a decay statement for the signed mean. The proposed converse
route would need an additional Banach/bad-scale result excluding persistent
biased scales. No such result, and no unconditional density or mean-zero
limit, is assumed or proved in this file.
-/

#print axioms normalized_double_defect
#print axioms dyadic_flatness_iff_bypassMean_zero
#print axioms bypassMean_zero_of_signedMean_zero
#print axioms D_eq_count
#print axioms hasDensity_iff_signedMean
#print axioms bypassMean_zero_of_hasDensity
#print axioms maxPrimeFac_ne_of_coprime
#print axioms maxPrimeFac_succ_ne
#print axioms dyadic_coprime
#print axioms triple_maxPrimeFac_ne
#print axioms maxPrimeFac_double
#print axioms sign_pair_of_distinct
#print axioms s_zero
#print axioms s_one
#print axioms not_B_zero
#print axioms not_B_one
#print axioms t_zero
#print axioms t_one
#print axioms sign_double
#print axioms t_eq
#print axioms t_eq_with_boundary
#print axioms D_double_pair_sum
#print axioms D_double_defect_all
#print axioms D_double_defect

end Erdos371Dyadic
