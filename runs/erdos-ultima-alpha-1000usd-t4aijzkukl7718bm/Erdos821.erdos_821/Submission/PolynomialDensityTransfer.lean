import Submission.RationalSmoothMultiplicity

/-!
# Removing polynomial losses from a fixed smooth-prime density estimate

A prime-count lower bound with a polynomial loss and a fixed smoothness
cutoff yields every multiplicity exponent below the complementary cutoff.
The application here sharpens a fixed exponent above one half. It does not
produce a sequence of exponents tending to one.
-/

open Nat Filter
open scoped Classical

namespace Erdos821

open AnalyticSieve

lemma dyadic_family_of_eventual_polynomial_count (t b K C d k : ℕ)
    (ht : 0 < t) (hk : 1 ≤ k)
    (H : ∀ᶠ m : ℕ in atTop, ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (t * m) ∧
        p - 1 ∈ Nat.smoothNumbers (K * 2 ^ (b * m))) ∧
      2 ^ (t * m) ≤ C * (m + 1) ^ d * P.card) (M : ℕ) :
    ∃ L : ℕ, M ≤ L ∧ ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ ((t * k) * L) ∧
        p - 1 ∈ Nat.smoothNumbers (2 ^ ((b * k + 1) * L))) ∧
      2 ^ ((t * k - 1) * L) ≤ P.card := by
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp H
  obtain ⟨M₁, hM₁⟩ := eventually_atTop.mp (eventually_nat_poly_le_two_pow k C d)
  let L := max M (max M₀ (max M₁ K))
  have hML : M ≤ L := le_max_left _ _
  have hL₀ : M₀ ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have hL₁ : M₁ ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hKL : K ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hLk : L ≤ k * L := by simpa only [one_mul] using Nat.mul_le_mul_right L hk
  obtain ⟨P, hP, hcard⟩ := hM₀ (k * L) (hL₀.trans hLk)
  have hpoly : C * (k * L + 1) ^ d ≤ 2 ^ L := hM₁ L hL₁
  refine ⟨L, hML, P, ?_, ?_⟩
  · intro p hp
    obtain ⟨hprime, hpN, hpsmooth⟩ := hP p hp
    refine ⟨hprime, by simpa only [mul_assoc] using hpN, ?_⟩
    apply Nat.smoothNumbers_mono _ hpsmooth
    calc
      K * 2 ^ (b * (k * L)) ≤ 2 ^ L * 2 ^ (b * (k * L)) :=
        Nat.mul_le_mul_right _ (hKL.trans Nat.lt_two_pow_self.le)
      _ = 2 ^ ((b * k + 1) * L) := by rw [← pow_add]; congr 1; ring
  · have htk : 1 ≤ t * k := Nat.mul_pos ht (by omega)
    have hpowers : 2 ^ L * 2 ^ ((t * k - 1) * L) = 2 ^ (t * (k * L)) := by
      rw [← pow_add]
      congr 1
      have heq : t * k - 1 + 1 = t * k := Nat.sub_add_cancel htk
      nlinarith only [congrArg (fun z : ℕ => z * L) heq]
    apply Nat.le_of_mul_le_mul_left (c := 2 ^ L) _ (by positivity)
    rw [hpowers]
    exact hcard.trans (Nat.mul_le_mul_right P.card hpoly)

theorem infinite_g_gt_of_eventual_polynomial_count (t b K C d : ℕ)
    (hbt : b < t)
    (H : ∀ᶠ m : ℕ in atTop, ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (t * m) ∧
        p - 1 ∈ Nat.smoothNumbers (K * 2 ^ (b * m))) ∧
      2 ^ (t * m) ≤ C * (m + 1) ^ d * P.card)
    (γ : ℝ) (hγ : γ < 1 - (b : ℝ) / t) :
    {n : ℕ | (g n : ℝ) > (n : ℝ) ^ γ}.Infinite := by
  have ht : 0 < t := lt_of_le_of_lt (Nat.zero_le b) hbt
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hγ' : γ < ((t : ℝ) - b) / t := by
    convert hγ using 1
    field_simp
  have hmargin : 0 < (t : ℝ) - b - t * γ := by
    have h := (lt_div_iff₀ htR).mp hγ'
    nlinarith only [h]
  obtain ⟨k, hk⟩ := exists_nat_gt (max 5 (4 / ((t : ℝ) - b - t * γ)))
  have hk5R : (5 : ℝ) < k := (le_max_left _ _).trans_lt hk
  have hk5 : 5 ≤ k := by exact_mod_cast hk5R.le
  have h4 : 4 < (k : ℝ) * ((t : ℝ) - b - t * γ) :=
    (div_lt_iff₀ hmargin).mp ((le_max_right _ _).trans_lt hk)
  have hgap : b * k + 5 ≤ t * k := by
    have h := Nat.mul_le_mul_right k (show b + 1 ≤ t by omega)
    nlinarith only [h, hk5]
  have hinf := infinite_g_gt_of_general_dyadic_density (t * k) (t * k - 1) (b * k + 1)
    (by omega) (by omega) (by omega)
    (dyadic_family_of_eventual_polynomial_count t b K C d k ht (by omega) H)
  have hnum : ((t * k - 1 - (b * k + 1) - 2 : ℕ) : ℝ) =
      (t : ℝ) * k - b * k - 4 := by
    rw [Nat.cast_sub (by omega : 2 ≤ t * k - 1 - (b * k + 1)),
      Nat.cast_sub (by omega : b * k + 1 ≤ t * k - 1),
      Nat.cast_sub (by omega : 1 ≤ t * k)]
    push_cast
    ring
  have htkR : (0 : ℝ) < (t * k : ℕ) := by
    exact_mod_cast Nat.mul_pos ht (by omega : 0 < k)
  have hγk : γ < ((t * k - 1 - (b * k + 1) - 2 : ℕ) : ℝ) / (t * k : ℕ) := by
    apply (lt_div_iff₀ htkR).mpr
    rw [hnum, Nat.cast_mul]
    nlinarith only [h4]
  apply (hinf.diff (Set.finite_singleton 0)).mono
  intro n hn
  have hn0 : n ≠ 0 := by simpa only [Set.mem_singleton_iff] using hn.2
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  exact (Real.rpow_le_rpow_of_exponent_le hn1 hγk.le).trans_lt hn.1

lemma eventually_sieved_polynomial_count (r : ℕ) (hr : 1 ≤ r)
    (hC : 150994944 * Sieve.totientRatioAverageConstant ≤ (r : ℝ)) :
    ∀ᶠ m : ℕ in atTop, ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ ((16384 * r) * m) ∧
        p - 1 ∈ Nat.smoothNumbers (2 * 2 ^ ((8192 * r - 384) * m))) ∧
      2 ^ ((16384 * r) * m) ≤ (137438953472 * r ^ 2) * (m + 1) ^ 1 * P.card := by
  filter_upwards [eventually_nat_poly_le_two_pow (256 * r) 32768000000000000 7,
    eventually_ge_atTop 1] with m hpoly hm
  let P := sievedProgressionPrimes (256 * r * m) (192 * m)
  have hNeq : progressionScaleN (256 * r * m) = 2 ^ ((16384 * r) * m) := by
    unfold progressionScaleN
    congr 1
    ring
  have hYeq : progressionSieveY (256 * r * m) (192 * m) =
      2 * 2 ^ ((8192 * r - 384) * m) := by
    unfold progressionSieveY progressionScaleQ
    congr 2
    rw [Nat.sub_mul]
    congr 1 <;> ring
  refine ⟨P, ?_, ?_⟩
  · intro p hp
    obtain ⟨hpW, hpS⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpI, hprime, _⟩ := Finset.mem_filter.mp hpW
    refine ⟨hprime, ?_, ?_⟩
    · simpa only [hNeq] using (Finset.mem_Icc.mp hpI).2
    · simpa only [hYeq] using hpS
  · have hcount := square_root_sieved_prime_count r m hr hm hC hpoly
    rw [hNeq] at hcount
    exact hcount.trans (Nat.mul_le_mul_right P.card
      (Nat.mul_le_mul_left (137438953472 * r ^ 2) (by simp only [pow_one]; omega)))

/-- The limiting exponent supplied by the current sieve, with all fixed
polynomial and dyadic rounding losses removed. The parameter r must still
exceed the fixed sieve constant. -/
theorem infinite_g_gt_sieved_limit (r : ℕ) (hr : 1 ≤ r)
    (hC : 150994944 * Sieve.totientRatioAverageConstant ≤ (r : ℝ))
    (γ : ℝ) (hγ : γ < 1 / 2 + 3 / (128 * (r : ℝ))) :
    {n : ℕ | (g n : ℝ) > (n : ℝ) ^ γ}.Infinite := by
  apply infinite_g_gt_of_eventual_polynomial_count (16384 * r) (8192 * r - 384)
    2 (137438953472 * r ^ 2) 1 (by omega)
    (eventually_sieved_polynomial_count r hr hC) γ
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have heq : 1 - ((8192 * r - 384 : ℕ) : ℝ) / ((16384 * r : ℕ) : ℝ) =
      1 / 2 + 3 / (128 * (r : ℝ)) := by
    rw [Nat.cast_sub (by omega : 384 ≤ 8192 * r)]
    push_cast
    field_simp
    ring
  rw [heq]
  exact hγ

end Erdos821
