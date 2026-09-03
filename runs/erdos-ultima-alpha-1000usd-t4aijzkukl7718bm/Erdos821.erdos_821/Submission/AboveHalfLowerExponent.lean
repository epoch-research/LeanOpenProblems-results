import Submission.SievedProgressionScales
import Submission.LowerExponent

/-!
# An unconditional inverse-totient multiplicity exponent above one half

The second sieve produces a fixed power saving below square-root smoothness.
This is a strict improvement on the previously formalized one-half limit, but
still not a proof of exponents approaching one.
-/

open Nat Filter

namespace Erdos821

open AnalyticSieve

lemma sieved_smooth_prime_family (r L : ℕ) (hr : 1 ≤ r) (hL : 1 ≤ L)
    (hC : 150994944 * Sieve.totientRatioAverageConstant ≤ (r : ℝ))
    (hsmall : 32768000000000000 * (4 * r * L + 1) ^ 7 ≤ 2 ^ L) :
    ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (256 * r * L) ∧
        p - 1 ∈ Nat.smoothNumbers (2 ^ ((128 * r - 5) * L))) ∧
      2 ^ ((256 * r - 1) * L) ≤ P.card := by
  let s := 4 * r * L
  have hLs : 3 * L ≤ s := by dsimp [s]; nlinarith
  have hsmall' : 32768000000000000 * (s + 1) ^ 7 ≤ 2 ^ (3 * L) :=
    hsmall.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hC' : 201326592 * Sieve.totientRatioAverageConstant * ((3 * L : ℕ) : ℝ) ≤ (s : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hC (by positivity : (0 : ℝ) ≤ 4 * (L : ℝ))
    dsimp [s]
    push_cast
    nlinarith
  let P := sievedProgressionPrimes s (3 * L)
  have hcount : progressionScaleN s ≤ 262144 * s ^ 2 * P.card :=
    sieved_progression_prime_count (by omega) hLs (show 4 * (r * L) = s by dsimp [s]; ring) hsmall' hC'
  have hpoly : 262144 * s ^ 2 ≤ 2 ^ L := by
    have hp : s ^ 2 ≤ (s + 1) ^ 7 :=
      (Nat.pow_le_pow_left (Nat.le_succ s) 2).trans
        (Nat.pow_le_pow_right (show 0 < s + 1 by omega) (by norm_num : 2 ≤ 7))
    change 32768000000000000 * (s + 1) ^ 7 ≤ 2 ^ L at hsmall
    omega
  have hpower : 2 ^ L * 2 ^ ((256 * r - 1) * L) = progressionScaleN s := by
    rw [← pow_add]
    unfold progressionScaleN s
    congr 1
    calc
      L + (256 * r - 1) * L = (1 + (256 * r - 1)) * L := by ring
      _ = (256 * r) * L := by congr 1; omega
      _ = 64 * (4 * r * L) := by ring
  refine ⟨P, ?_, ?_⟩
  · intro p hp
    obtain ⟨hpW, hpsmooth⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpI, hprime, _⟩ := Finset.mem_filter.mp hpW
    have hpN := (Finset.mem_Icc.mp hpI).2
    refine ⟨hprime, ?_, ?_⟩
    · convert hpN using 1
      unfold progressionScaleN s
      congr 1
      ring
    · apply Nat.smoothNumbers_mono _ hpsmooth
      have hrel : 32 * s = (128 * r - 5) * L + 5 * L := by
        calc
          32 * s = (128 * r) * L := by dsimp [s]; ring
          _ = ((128 * r - 5) + 5) * L := by rw [Nat.sub_add_cancel (by omega : 5 ≤ 128 * r)]
          _ = _ := by ring
      simp only [progressionSieveY, progressionScaleQ]
      rw [show 2 * 2 ^ (32 * s - 2 * (3 * L)) = 2 ^ (32 * s - 2 * (3 * L) + 1) by rw [pow_succ]; ring]
      exact Nat.pow_le_pow_right (by decide) (by omega)
  · apply Nat.le_of_mul_le_mul_left (c := 2 ^ L)
      (show 2 ^ L * 2 ^ ((256 * r - 1) * L) ≤ 2 ^ L * P.card from ?_) (by positivity)
    rw [hpower]
    exact hcount.trans (Nat.mul_le_mul_right P.card hpoly)

lemma eventually_sieved_smooth_prime_family (r : ℕ) (hr : 1 ≤ r)
    (hC : 150994944 * Sieve.totientRatioAverageConstant ≤ (r : ℝ)) :
    ∀ᶠ L : ℕ in atTop, ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (256 * r * L) ∧
        p - 1 ∈ Nat.smoothNumbers (2 ^ ((128 * r - 5) * L))) ∧
      2 ^ ((256 * r - 1) * L) ≤ P.card := by
  filter_upwards [eventually_nat_poly_le_two_pow (4 * r) 32768000000000000 7,
    eventually_ge_atTop 1] with L hpoly hL
  exact sieved_smooth_prime_family r L hr hL hC hpoly

/-- A fixed exponent strictly above 1/2, for any sufficiently large fixed r. -/
theorem infinite_g_gt_above_half_parameter (r : ℕ) (hr : 1 ≤ r)
    (hC : 150994944 * Sieve.totientRatioAverageConstant ≤ (r : ℝ)) :
    {n : ℕ | (g n : ℝ) > (n : ℝ) ^ ((128 * (r : ℝ) + 2) / (256 * (r : ℝ)))}.Infinite := by
  have H : ∀ M : ℕ, ∃ L : ℕ, M ≤ L ∧ ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (256 * r * L) ∧
        p - 1 ∈ Nat.smoothNumbers (2 ^ ((128 * r - 5) * L))) ∧
      2 ^ ((256 * r - 1) * L) ≤ P.card := by
    obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp (eventually_sieved_smooth_prime_family r hr hC)
    intro M
    exact ⟨max M L₀, le_max_left _ _, hL₀ _ (le_max_right _ _)⟩
  have hinf := infinite_g_gt_of_general_dyadic_density (256 * r) (256 * r - 1) (128 * r - 5)
    (by omega) (by omega) (by omega) H
  have hnat : 256 * r - 1 - (128 * r - 5) - 2 = 128 * r + 2 := by omega
  have hnum : ((256 * r - 1 - (128 * r - 5) - 2 : ℕ) : ℝ) = 128 * (r : ℝ) + 2 := by
    rw [hnat]
    push_cast
    rfl
  simpa only [hnum, Nat.cast_mul, Nat.cast_ofNat] using hinf

/-- Unconditional strict improvement beyond the square-root exponent.
This does not assert exponents arbitrarily close to one. -/
theorem exists_multiplicity_exponent_above_half :
    ∃ δ : ℝ, 1 / 2 < δ ∧ δ < 1 ∧
      {n : ℕ | (g n : ℝ) > (n : ℝ) ^ δ}.Infinite := by
  obtain ⟨r, hr⟩ := exists_nat_gt (max 1 (150994944 * Sieve.totientRatioAverageConstant))
  have hr1R : (1 : ℝ) < r := (le_max_left _ _).trans_lt hr
  have hr1 : 1 ≤ r := by exact_mod_cast hr1R.le
  have hrpos : (0 : ℝ) < r := by linarith
  have hC : 150994944 * Sieve.totientRatioAverageConstant ≤ (r : ℝ) :=
    ((le_max_right _ _).trans_lt hr).le
  refine ⟨(128 * (r : ℝ) + 2) / (256 * (r : ℝ)), ?_, ?_,
    infinite_g_gt_above_half_parameter r hr1 hC⟩
  · apply (lt_div_iff₀ (by positivity)).mpr
    linarith
  · apply (div_lt_one (by positivity)).mpr
    linarith

/-- The original assertion holds above a fixed epsilon cutoff strictly less
than one half. The interval between zero and that cutoff remains unresolved. -/
theorem exists_epsilon_cutoff_below_half :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 / 2 ∧ ∀ ε : ℝ, ε₀ ≤ ε →
      {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite := by
  obtain ⟨δ, hδ, hδ1, hinf⟩ := exists_multiplicity_exponent_above_half
  refine ⟨1 - δ, by linarith, by linarith, ?_⟩
  intro ε hε
  apply (hinf.diff (Set.finite_singleton 0)).mono
  intro n hn
  have hn0 : n ≠ 0 := by simpa only [Set.mem_singleton_iff] using hn.2
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  exact (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith : 1 - ε ≤ δ)).trans_lt hn.1

end Erdos821
