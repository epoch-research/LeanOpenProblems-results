import FormalConjecturesUtil
import Submission.AveragingCriterion
import Submission.ReflectionDynamics
import Submission.BoundedPrimeGap

/-! The prime-factor reflection almost never stays in a fixed linear counting
range. This is a range obstruction, not a resolution of Erdős 371. -/

namespace Erdos371ReflectionRange

open Erdos371SmallPrimeAveraging Erdos371AveragingCriterion
open Erdos371Cofactor Erdos371ReflectionDynamics
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable

lemma mean_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (N : ℕ) : 0 ≤ mean f N := by
  exact div_nonneg (Finset.sum_nonneg (fun n _ => hf n)) (Nat.cast_nonneg N)

lemma mean_mono {f g : ℕ → ℝ} (h : ∀ n, f n ≤ g n) (N : ℕ) :
    mean f N ≤ mean g N := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun n _ => h n))
    (Nat.cast_nonneg N)

/-- A bounded nonnegative function supported where the small-prime divisor
count is uniformly bounded has mean zero. -/
lemma mean_zero_of_bounded_prime_weight (f : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf0 : ∀ n, 0 ≤ f n) (hf1 : ∀ n, f n ≤ 1)
    (hw : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → ∀ N,
      mean (fun n => f n * smallCount s n) N ≤ B * mean f N) :
    Tendsto (mean f) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨s, hs, hM⟩ := prime_mass_unbounded (max (2*B+1) (8/ε^2))
  let M := mass s
  have hMB : 2*B+1 < M := (le_max_left _ _).trans_lt hM
  have hMε : 8/ε^2 < M := (le_max_right _ _).trans_lt hM
  have hM0 : 0 < M := by linarith
  have hprod : 8 < M*ε^2 := (div_lt_iff₀ (sq_pos_of_pos hε)).mp hMε
  have hlarge : 2*M < (M*ε/2)^2 := by
    have hh := mul_lt_mul_of_pos_left hprod hM0
    nlinarith
  have hv := (varianceMean_tendsto s hs).eventually_lt_const
    ((variance_limit_le_mass s).trans_lt (show mass s < 2*M by dsimp [M]; linarith))
  filter_upwards [hv] with N hvN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mean_nonneg hf0 N)]
  by_contra he
  have hεN : ε ≤ mean f N := le_of_not_gt he
  have hfn := mean_nonneg hf0 N
  have hweight := hw s hs N
  have hbound : M*ε/2 ≤ M * mean f N - mean (fun n => f n * smallCount s n) N := by
    have hh := mul_le_mul_of_nonneg_left hεN hM0.le
    nlinarith
  have hf (n : ℕ) : |f n| ≤ 1 := by rw [abs_of_nonneg (hf0 n)]; exact hf1 n
  have hb := averaging_square_bound s f hf N
  have hsq := sq_le_sq₀ (by positivity : 0 ≤ M*ε/2)
    ((show 0 ≤ M*ε/2 by positivity).trans hbound)
  have hh := hsq.mpr hbound
  change (M * mean f N - mean (fun n => f n * smallCount s n) N)^2 ≤ _ at hb
  linarith

def semiprime (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p*q

noncomputable def semiIndicator (n : ℕ) : ℝ := if semiprime (n+1) then 1 else 0

lemma smallCount_eq_card (s : Finset ℕ) (n : ℕ) :
    smallCount s n = ((s.filter fun p => p ∣ n+1).card : ℝ) := by
  simp [smallCount, ind]

lemma smallCount_semiprime {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    {n : ℕ} (hn : semiprime (n+1)) : smallCount s n ≤ 2 := by
  obtain ⟨p, q, hp, hq, he⟩ := hn
  rw [smallCount_eq_card]
  have hsub : s.filter (fun r => r ∣ n+1) ⊆ {p,q} := by
    intro r hr
    obtain ⟨hrs, hrd⟩ := Finset.mem_filter.mp hr
    rw [he] at hrd
    rcases (hs r hrs).dvd_mul.mp hrd with h | h
    · have hh := (Nat.dvd_prime hp).mp h
      rcases hh with hh | hh
      · exact False.elim ((hs r hrs).ne_one hh)
      · simp [hh]
    · have hh := (Nat.dvd_prime hq).mp h
      rcases hh with hh | hh
      · exact False.elim ((hs r hrs).ne_one hh)
      · simp [hh]
  have hc : (s.filter (fun r => r ∣ n+1)).card ≤ 2 :=
    (Finset.card_le_card hsub).trans (by simpa using Finset.card_insert_le p ({q} : Finset ℕ))
  exact_mod_cast hc

lemma semi_mean_zero : Tendsto (mean semiIndicator) atTop (𝓝 0) := by
  apply mean_zero_of_bounded_prime_weight semiIndicator 2 (by norm_num)
  · intro n; unfold semiIndicator; split_ifs <;> norm_num
  · intro n; unfold semiIndicator; split_ifs <;> norm_num
  · intro s hs N
    rw [← mean_const_mul]
    apply mean_mono
    intro n
    by_cases h : semiprime (n+1)
    · simp only [semiIndicator, if_pos h, one_mul, mul_one]
      exact smallCount_semiprime hs h
    · simp [semiIndicator, h]

lemma indicator_mean_eq_density (S : Set ℕ) (N : ℕ) :
    mean (fun n => if n ∈ S then 1 else 0) N = S.partialDensity Set.univ N := by
  classical
  simp only [mean, Finset.sum_boole, Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
  have he : S ∩ Set.Iio N = ↑((Finset.range N).filter fun n => n ∈ S) := by
    ext n
    simp [and_comm]
  rw [he, Set.ncard_coe_finset]

lemma shifted_semiprime_density : {n | semiprime (n+1)}.HasDensity 0 := by
  have h := semi_mean_zero
  change Tendsto (fun N => mean (fun n => if n ∈ {k | semiprime (k+1)} then 1 else 0) N)
    atTop (𝓝 0) at h
  simpa only [indicator_mean_eq_density] using h


def encode (n : ℕ) : ℕ × Bool :=
  (P n * P (n+1) - 1, decide (P n < P (n+1)))

lemma prime_factors_determined_by_product_and_order {p q r s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hprod : p*q = r*s) (hord : (p<q ↔ r<s)) : p=r ∧ q=s := by
  have hmax : max p q = max r s := by
    have hh := congrArg Nat.maxPrimeFac hprod
    simpa [Nat.maxPrimeFac_mul hp.ne_zero hq.ne_zero,
      Nat.maxPrimeFac_mul hr.ne_zero hs.ne_zero, hp.maxPrimeFac_eq_self,
      hq.maxPrimeFac_eq_self, hr.maxPrimeFac_eq_self, hs.maxPrimeFac_eq_self] using hh
  by_cases h : p < q
  · have h' := hord.mp h
    rw [max_eq_right h.le, max_eq_right h'.le] at hmax
    subst s
    exact ⟨Nat.mul_right_cancel hq.pos hprod, rfl⟩
  · have h' : ¬r<s := fun hh => h (hord.mpr hh)
    rw [max_eq_left (by omega), max_eq_left (by omega)] at hmax
    subst r
    exact ⟨rfl, Nat.mul_left_cancel hp.pos hprod⟩

/-- Below their prime product, the two residues and the orientation determine
an input uniquely. -/
lemma encode_injective_on_valid : Set.InjOn encode {n | valid n} := by
  intro n hn m hm he
  have hprod0 := congrArg Prod.fst he
  have hord0 := congrArg Prod.snd he
  change P n * P (n+1)-1 = P m * P (m+1)-1 at hprod0
  change decide (P n < P (n+1)) = decide (P m < P (m+1)) at hord0
  have hprod : P n * P (n+1) = P m * P (m+1) := by
    have := hn.2
    have := hm.2
    omega
  have hn1 : 1 < n := hn.1
  have hm1 : 1 < m := hm.1
  have hp := Nat.prime_maxPrimeFac_of_one_lt n hn.1
  have hq := Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega : 1 < n+1)
  have hr := Nat.prime_maxPrimeFac_of_one_lt m hm.1
  have hs := Nat.prime_maxPrimeFac_of_one_lt (m+1) (by omega : 1 < m+1)
  obtain ⟨hpn, hqn⟩ := prime_factors_determined_by_product_and_order hp hq hr hs
    hprod (decide_eq_decide.mp hord0)
  change P n = P m at hpn
  change P (n+1) = P (m+1) at hqn
  have hmp : P n ∣ m := by rw [hpn]; exact Nat.maxPrimeFac_dvd
  have hmq : P (n+1) ∣ m+1 := by rw [hqn]; exact Nat.maxPrimeFac_dvd
  have hmodp : Nat.ModEq (P n) n m := by
    show n % P n = m % P n
    rw [Nat.mod_eq_zero_of_dvd Nat.maxPrimeFac_dvd, Nat.mod_eq_zero_of_dvd hmp]
  have hmodq : Nat.ModEq (P (n+1)) n m := by
    apply Nat.ModEq.add_right_cancel' 1
    show (n+1) % P (n+1) = (m+1) % P (n+1)
    rw [Nat.mod_eq_zero_of_dvd Nat.maxPrimeFac_dvd, Nat.mod_eq_zero_of_dvd hmq]
  have hcop : (P n).Coprime (P (n+1)) := (Nat.coprime_primes hp hq).mpr
    (Ne.symm (Erdos371PrimeDiscrepancy.consecutive_ne n))
  have hh := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hmodp, hmodq⟩
  change n % (P n * P (n+1)) = m % (P n * P (n+1)) at hh
  rw [Nat.mod_eq_of_lt (by have := hn.2; omega),
    Nat.mod_eq_of_lt (by have := hm.2; omega)] at hh
  exact hh

noncomputable def semiCount (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n => semiprime (n+1)).card

noncomputable def internalReflection (N M : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun n => valid n ∧ reflect n < M

lemma internalReflection_card_le (N M : ℕ) :
    (internalReflection N M).card ≤ 2 * semiCount (N+M) := by
  let T := ((Finset.range (N+M)).filter fun n => semiprime (n+1)).product
    (Finset.univ : Finset Bool)
  have hc : (internalReflection N M).card ≤ T.card := by
    apply Finset.card_le_card_of_injOn encode
    · intro n hn
      change n ∈ (Finset.range N).filter (fun n => valid n ∧ reflect n < M) at hn
      obtain ⟨hnN, hv, hrM⟩ := Finset.mem_filter.mp hn
      have hnN' := Finset.mem_range.mp hnN
      have hv1 : 1 < n := hv.1
      have hh := reflection_sum hv
      have henc : (encode n).1 = n + reflect n := by simp only [encode]; omega
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩, Finset.mem_univ _⟩
      · rw [henc]
        omega
      · refine ⟨P n, P (n+1), Nat.prime_maxPrimeFac_of_one_lt n hv.1,
          Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega : 1 < n+1), ?_⟩
        rw [henc]
        omega
    · intro n hn m hm he
      change n ∈ (Finset.range N).filter (fun n => valid n ∧ reflect n < M) at hn
      change m ∈ (Finset.range N).filter (fun n => valid n ∧ reflect n < M) at hm
      exact encode_injective_on_valid (Finset.mem_filter.mp hn).2.1
        (Finset.mem_filter.mp hm).2.1 he
  simpa [T, semiCount, Nat.mul_comm] using hc

lemma semiCount_ratio_zero :
    Tendsto (fun N : ℕ => (semiCount N : ℝ)/N) atTop (𝓝 0) := by
  apply semi_mean_zero.congr'
  exact Eventually.of_forall (fun N => by simp [mean, semiIndicator, semiCount])


lemma scaled_semiCount_ratio_zero {A : ℕ} (hA : 0 < A) :
    Tendsto (fun N : ℕ => (semiCount (A*N) : ℝ)/N) atTop (𝓝 0) := by
  have ht : Tendsto (fun N : ℕ => A*N) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with N hN
    nlinarith
  have hh := (tendsto_const_nhds (x := (A:ℝ))).mul (semiCount_ratio_zero.comp ht)
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have ha : (A:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hA.ne'
  have hn : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  change (A:ℝ) * ((semiCount (A*N):ℝ) / (A*N:ℕ)) = (semiCount (A*N):ℝ)/N
  push_cast
  field_simp

/-- Only `o(N)` valid inputs below `N` have their reflection below `C*N`,
for each fixed natural number `C`. -/
theorem internalReflection_ratio_zero (C : ℕ) :
    Tendsto (fun N : ℕ => ((internalReflection N (C*N)).card : ℝ)/N)
      atTop (𝓝 0) := by
  have hh := (tendsto_const_nhds (x := (2:ℝ))).mul
    (scaled_semiCount_ratio_zero (A := C+1) (by omega))
  simp only [mul_zero] at hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh
  · intro N; positivity
  · intro N
    change ((internalReflection N (C*N)).card : ℝ)/N ≤
      2 * ((semiCount ((C+1)*N):ℝ)/N)
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    have hc := internalReflection_card_le N (C*N)
    have he : N+C*N = (C+1)*N := by ring
    rw [he] at hc
    exact_mod_cast hc

lemma partialDensity_eq_filter_card (S : Set ℕ) (N : ℕ) :
    S.partialDensity Set.univ N =
      (((Finset.range N).filter fun n => n ∈ S).card : ℝ)/N := by
  rw [← indicator_mean_eq_density]
  simp [mean]

/-- On its valid domain, the reflection expands by more than any fixed
factor, outside a set of natural density zero. This does not assert any
density for the valid domain or for either comparison orientation. -/
theorem bounded_expansion_hasDensity_zero (C : ℕ) :
    {n | valid n ∧ reflect n ≤ C*n}.HasDensity 0 := by
  have hh := internalReflection_ratio_zero (C+1)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh
  · intro N
    unfold Set.partialDensity
    positivity
  · intro N
    change {n | valid n ∧ reflect n ≤ C*n}.partialDensity Set.univ N ≤ _
    rw [partialDensity_eq_filter_card]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_setOf_eq] at hn
    obtain ⟨hnN, hv, hr⟩ := hn
    simp only [internalReflection, Finset.mem_filter, Finset.mem_range]
    refine ⟨hnN, hv, ?_⟩
    have hh : C*n ≤ C*N := Nat.mul_le_mul_left C hnN.le
    nlinarith

/-- A fixed multiplicative-width band immediately above `n` contains the
product of the two largest prime factors only on a density-zero set. -/
theorem critical_prime_product_band_hasDensity_zero (C : ℕ) :
    {n | 1 < n ∧ n+1 < P n * P (n+1) ∧ P n * P (n+1) ≤ C*n}.HasDensity 0 := by
  apply Erdos371Exploration.density_zero_of_subset _ (bounded_expansion_hasDensity_zero C)
  intro n hn
  refine ⟨⟨hn.1, hn.2.1⟩, ?_⟩
  have hh := reflection_sum (show valid n from ⟨hn.1, hn.2.1⟩)
  have := hn.2.2
  omega

end Erdos371ReflectionRange

#print axioms Erdos371ReflectionRange.shifted_semiprime_density
#print axioms Erdos371ReflectionRange.encode_injective_on_valid
#print axioms Erdos371ReflectionRange.internalReflection_card_le
#print axioms Erdos371ReflectionRange.internalReflection_ratio_zero
#print axioms Erdos371ReflectionRange.bounded_expansion_hasDensity_zero
#print axioms Erdos371ReflectionRange.critical_prime_product_band_hasDensity_zero
