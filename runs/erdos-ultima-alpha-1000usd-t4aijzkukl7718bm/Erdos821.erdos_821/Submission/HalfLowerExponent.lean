import Submission.ShiftedPrimeCounting
import Submission.LowerExponent

/-!
# An unconditional multiplicity exponent approaching one half

The prime-modulus progression estimates supply sufficiently many primes with
predecessors smooth to any fixed power greater than one half.  Combined with
the finite inverse-totient construction, this proves the Erdős 821 assertion
for epsilon > 1/2.  It does not settle the conjecture for all epsilon > 0.
-/

open Nat Filter

namespace Erdos821

open AnalyticSieve

lemma progression_scale_smooth_prime_family (r L : ℕ) (hr : 1 ≤ r) (hL : 1 ≤ L)
    (hsmall : 32768000000000000 * (r * L + 1) ^ 7 ≤ 2 ^ L) :
    ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (64 * r * L) ∧
        p - 1 ∈ Nat.smoothNumbers (2 ^ ((32 * r + 4) * L))) ∧
      2 ^ ((64 * r - 1) * L) ≤ P.card := by
  let s := r * L
  have hLs : L ≤ s := by dsimp [s]; nlinarith
  let M := primeModuliBetween (progressionScaleD s L) (progressionScaleQ s L)
  let P := shiftedWitnessPrimes M (progressionScaleB s L) (progressionScaleN s)
  have hcount : progressionScaleN s ≤ 8388608 * s ^ 3 * P.card :=
    progression_scale_prime_count hL hLs hsmall
  have hpoly : 8388608 * s ^ 3 ≤ 2 ^ L := by
    have hp : s ^ 3 ≤ (s + 1) ^ 7 :=
      (Nat.pow_le_pow_left (Nat.le_succ s) 3).trans
        (Nat.pow_le_pow_right (show 0 < s + 1 by omega) (by norm_num : 3 ≤ 7))
    change 32768000000000000 * (s + 1) ^ 7 ≤ 2 ^ L at hsmall
    omega
  have hpower : 2 ^ L * 2 ^ ((64 * r - 1) * L) = progressionScaleN s := by
    rw [← pow_add]
    unfold progressionScaleN s
    congr 1
    calc
      L + (64 * r - 1) * L = (1 + (64 * r - 1)) * L := by ring
      _ = (64 * r) * L := by congr 1; omega
      _ = 64 * (r * L) := by ring
  refine ⟨P, ?_, ?_⟩
  · intro p hp
    have hQN : progressionScaleQ s L ≤ progressionScaleN s / progressionScaleD s L := by
      rw [progression_scale_cofactor hLs]
      unfold progressionScaleQ
      exact Nat.pow_le_pow_right (by decide) (by omega)
    obtain ⟨hprime, _, hpN, hfactor⟩ := shiftedWitnessPrimes_factor_bound M
      (progressionScaleD s L) (progressionScaleQ s L) (progressionScaleB s L)
      (progressionScaleN s) (by unfold progressionScaleD; positivity) hQN
      (fun q hq => mem_primeModuliBetween.mp hq) hp
    refine ⟨hprime, by simpa only [progressionScaleN, s, mul_assoc] using hpN, ?_⟩
    apply Nat.mem_smoothNumbers.mpr
    refine ⟨Nat.ne_of_gt (Nat.sub_pos_of_lt hprime.one_lt), ?_⟩
    intro ℓ hℓ
    have hf := hfactor ℓ hℓ
    rw [progression_scale_cofactor hLs] at hf
    apply hf.trans_lt
    apply Nat.pow_lt_pow_right (by norm_num)
    dsimp [s]
    nlinarith
  · apply Nat.le_of_mul_le_mul_left (c := 2 ^ L)
      (show 2 ^ L * 2 ^ ((64 * r - 1) * L) ≤ 2 ^ L * P.card from ?_) (by positivity)
    rw [hpower]
    exact hcount.trans (Nat.mul_le_mul_right P.card hpoly)

lemma eventually_progression_scale_smooth_prime_family (r : ℕ) (hr : 1 ≤ r) :
    ∀ᶠ L : ℕ in atTop, ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (64 * r * L) ∧
        p - 1 ∈ Nat.smoothNumbers (2 ^ ((32 * r + 4) * L))) ∧
      2 ^ ((64 * r - 1) * L) ≤ P.card := by
  filter_upwards [eventually_nat_poly_le_two_pow r 32768000000000000 7,
    eventually_ge_atTop 1] with L hpoly hL
  exact progression_scale_smooth_prime_family r L hr hL hpoly

/-- An explicit sequence of unconditional multiplicity exponents tending to 1/2. -/
theorem infinite_g_gt_half_approximant (r : ℕ) (hr : 1 ≤ r) :
    {n : ℕ | (g n : ℝ) > (n : ℝ) ^ ((32 * (r : ℝ) - 7) / (64 * (r : ℝ)))}.Infinite := by
  have H : ∀ M : ℕ, ∃ L : ℕ, M ≤ L ∧ ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (64 * r * L) ∧
        p - 1 ∈ Nat.smoothNumbers (2 ^ ((32 * r + 4) * L))) ∧
      2 ^ ((64 * r - 1) * L) ≤ P.card := by
    obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp (eventually_progression_scale_smooth_prime_family r hr)
    intro M
    exact ⟨max M L₀, le_max_left _ _, hL₀ _ (le_max_right _ _)⟩
  have hinf := infinite_g_gt_of_general_dyadic_density (64 * r) (64 * r - 1) (32 * r + 4)
    (by omega) (by omega) (by omega) H
  have hnat : 64 * r - 1 - (32 * r + 4) - 2 = 32 * r - 7 := by omega
  have hnum : ((64 * r - 1 - (32 * r + 4) - 2 : ℕ) : ℝ) = 32 * (r : ℝ) - 7 := by
    rw [hnat, Nat.cast_sub (by omega : 7 ≤ 32 * r)]
    push_cast
    rfl
  simpa only [hnum, Nat.cast_mul, Nat.cast_ofNat] using hinf

/-- Unconditionally, every exponent strictly below one half is attained
infinitely often.  There is no assertion here for exponents at least one half. -/
theorem infinite_g_gt_rpow_of_lt_half (γ : ℝ) (hγ : γ < 1 / 2) :
    {n : ℕ | (g n : ℝ) > (n : ℝ) ^ γ}.Infinite := by
  have hgap : 0 < 32 - 64 * γ := by linarith
  obtain ⟨r, hr⟩ := exists_nat_gt (7 / (32 - 64 * γ) + 1)
  have hrR : (1 : ℝ) < r := by
    have := div_pos (by norm_num : (0 : ℝ) < 7) hgap
    linarith
  have hr1 : 1 ≤ r := by exact_mod_cast hrR.le
  have hrpos : (0 : ℝ) < r := by linarith
  have hprod : 7 < (r : ℝ) * (32 - 64 * γ) := by
    apply (div_lt_iff₀ hgap).mp
    linarith
  have hexp : γ ≤ (32 * (r : ℝ) - 7) / (64 * (r : ℝ)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  have hinf := infinite_g_gt_half_approximant r hr1
  apply (hinf.diff (Set.finite_singleton 0)).mono
  intro n hn
  have hn0 : n ≠ 0 := by simpa only [Set.mem_singleton_iff] using hn.2
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  exact (Real.rpow_le_rpow_of_exponent_le hn1 hexp).trans_lt hn.1

/-- The range epsilon > 1/2 of the original conjecture. -/
theorem erdos_821_of_half_lt (ε : ℝ) (hε : 1 / 2 < ε) :
    {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite :=
  infinite_g_gt_rpow_of_lt_half (1 - ε) (by linarith)

end Erdos821
