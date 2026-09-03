import Submission.SmoothCompositeModuli
import Submission.LowerExponent

/-!
# An explicit near-full progression-distribution criterion for Erdős 821

The hypothesis below is an Elliott–Halberstam-type assertion on a geometric
subsequence, for residue one. It is NOT proved in this file and is NOT added as
an axiom. Every application keeps it as an explicit theorem argument.

The unconditional composite-modulus supply shows that this distribution
hypothesis would provide smooth shifted primes at arbitrarily small powers.
-/

open scoped Classical BigOperators
open Nat Finset Filter

namespace Erdos821

open AnalyticSieve

noncomputable def progressionPrimeCount (d N : ℕ) : ℕ :=
  ((N + 1).primesBelow.filter (fun p => d ∣ p - 1)).card

noncomputable def geometricProgressionError (t m : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (2 ^ (64 * (t - 1) * m)),
    |(progressionPrimeCount d (2 ^ (64 * t * m)) : ℝ) -
      (((2 ^ (64 * t * m) + 1).primesBelow.card : ℝ) / Nat.totient d)|

/-- An unproved distribution hypothesis, stated as a proposition rather than an axiom. -/
def GeometricProgressionDistribution : Prop :=
  ∀ t : ℕ, 3 ≤ t → ∀ A : ℕ, ∀ᶠ m : ℕ in atTop,
    geometricProgressionError t m ≤ (2 : ℝ) ^ (64 * t * m) / ((m : ℝ) + 1) ^ A

lemma progression_count_main_lower (D : Finset ℕ) (N Q : ℕ)
    (hD : D ⊆ Finset.Icc 1 Q) :
    ((N + 1).primesBelow.card : ℝ) * (∑ d ∈ D, (Nat.totient d : ℝ)⁻¹) -
      (∑ d ∈ Finset.Icc 1 Q, |(progressionPrimeCount d N : ℝ) -
        ((N + 1).primesBelow.card : ℝ) / Nat.totient d|) ≤
      ∑ d ∈ D, (progressionPrimeCount d N : ℝ) := by
  have hpoint (d : ℕ) : ((N + 1).primesBelow.card : ℝ) / Nat.totient d ≤
      (progressionPrimeCount d N : ℝ) + |(progressionPrimeCount d N : ℝ) -
        ((N + 1).primesBelow.card : ℝ) / Nat.totient d| := by
    have h := neg_le_abs ((progressionPrimeCount d N : ℝ) -
      ((N + 1).primesBelow.card : ℝ) / Nat.totient d)
    linarith
  have hsum := Finset.sum_le_sum (fun d (_ : d ∈ D) => hpoint d)
  rw [sum_add_distrib] at hsum
  have herr := Finset.sum_le_sum_of_subset_of_nonneg hD
    (fun d _ _ => abs_nonneg ((progressionPrimeCount d N : ℝ) -
      ((N + 1).primesBelow.card : ℝ) / Nat.totient d))
  simp only [div_eq_mul_inv] at hsum herr
  rw [← Finset.mul_sum] at hsum
  simp only [div_eq_mul_inv]
  linarith

lemma geometric_total_prime_count_lower (t m : ℕ) (ht : 3 ≤ t) (hm : 1 ≤ m) :
    2 ^ (64 * t * m) ≤ 128 * t * (m + 1) * (2 ^ (64 * t * m) + 1).primesBelow.card := by
  have hE : 1 ≤ 64 * t * m := by nlinarith
  have hN : 2 ≤ 2 ^ (64 * t * m) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by norm_num : 0 < 2) hE
  have hc : 1 ≤ (2 ^ (64 * t * m) + 1).primesBelow.card := by
    exact Nat.succ_le_iff.mpr (Finset.card_pos.mpr ⟨2, Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_two⟩⟩)
  have hb := dyadic_prime_count_bound (64 * t * m) hE
  have hh : 2 ^ (64 * t * m) ≤ 128 * t * m * (2 ^ (64 * t * m) + 1).primesBelow.card := by
    calc
      _ ≤ (64 * t * m) * ((2 ^ (64 * t * m) + 1).primesBelow.card + 1) := hb
      _ ≤ (64 * t * m) * (2 * (2 ^ (64 * t * m) + 1).primesBelow.card) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  exact hh.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left (128 * t) (Nat.le_succ m)))

/-- Abstract comparison of a polynomially small main term and a still smaller error. -/
lemma polynomial_main_survives (X P S T a c z : ℝ) (r : ℕ)
    (hX : 0 ≤ X) (hP : 0 ≤ P) (ha : 0 < a) (hc : 0 < c) (hz : 0 < z)
    (hPlo : X ≤ a * z * P) (hSlo : 1 / (c * z ^ r) ≤ S)
    (hcount : P * S - X / z ^ (r + 2) ≤ T)
    (hsmall : 2 * a * c ≤ z) :
    X ≤ 2 * a * c * z ^ (r + 1) * T := by
  have hP' : X / (a * z) ≤ P := (div_le_iff₀ (mul_pos ha hz)).mpr (by nlinarith only [hPlo])
  have hmain : X / (a * c * z ^ (r + 1)) ≤ P * S := by
    calc
      _ = (X / (a * z)) * (1 / (c * z ^ r)) := by rw [pow_succ]; field_simp
      _ ≤ _ := mul_le_mul hP' hSlo (by positivity) hP
  have herr : X / z ^ (r + 2) ≤ X / (2 * a * c * z ^ (r + 1)) := by
    apply div_le_div_of_nonneg_left hX (by positivity)
    calc
      _ ≤ z * z ^ (r + 1) := mul_le_mul_of_nonneg_right hsmall (by positivity)
      _ = z ^ (r + 2) := by rw [show r + 2 = (r + 1) + 1 by omega, pow_succ]; ring
  have heq : X / (a * c * z ^ (r + 1)) = 2 * (X / (2 * a * c * z ^ (r + 1))) := by ring
  rw [heq] at hmain
  have hT : X / (2 * a * c * z ^ (r + 1)) ≤ T := by linarith
  exact (div_le_iff₀ (by positivity)).mp hT |>.trans_eq (by ring)

def geometricSmoothCountConstant (t : ℕ) : ℕ :=
  256 * t * primeProductMassConstant (t - 2) * (64 * t) ^ (t - 2)

lemma geometricSmoothCountConstant_pos {t : ℕ} (ht : 3 ≤ t) :
    0 < geometricSmoothCountConstant t := by
  unfold geometricSmoothCountConstant
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega))
    (primeProductMassConstant_pos _)) (pow_pos (by omega) _)

/-- The one-sided aggregate deficit for the constructed smooth modulus family.
It can be negative; no absolute value is imposed on its summands. -/
noncomputable def geometricSmoothModulusDeficit (t m : ℕ) : ℝ :=
  (((2 ^ (64 * t * m) + 1).primesBelow.card : ℝ) *
    (∑ d ∈ primeProductModuli (t - 2) m, (Nat.totient d : ℝ)⁻¹)) -
  (∑ d ∈ primeProductModuli (t - 2) m,
    (progressionPrimeCount d (2 ^ (64 * t * m)) : ℝ))

lemma geometric_smooth_deficit_le_error (t m : ℕ) (ht : 3 ≤ t)
    (hm : max 2 (t - 2) ≤ m) :
    geometricSmoothModulusDeficit t m ≤ geometricProgressionError t m := by
  have hD : primeProductModuli (t - 2) m ⊆ Finset.Icc 1 (2 ^ (64 * (t - 1) * m)) := by
    intro d hd
    exact (primeProductModuli_progression_parameters t m ht hm hd).2.2.2.2
  have h := progression_count_main_lower (primeProductModuli (t - 2) m)
    (2 ^ (64 * t * m)) (2 ^ (64 * (t - 1) * m)) hD
  unfold geometricSmoothModulusDeficit geometricProgressionError
  linarith only [h]

/-- Only a one-sided aggregate deficit bound is needed for the finite transfer. -/
theorem geometric_signed_deficit_smooth_prime_count (t m : ℕ) (ht : 3 ≤ t)
    (hm : max 2 (t - 2) ≤ m)
    (hsmall : 4096 * (t - 2) * (m + 1) ≤ progressionScaleN m)
    (hbudget : 256 * t * primeProductMassConstant (t - 2) ≤ m + 1)
    (herr : geometricSmoothModulusDeficit t m ≤ (2 : ℝ) ^ (64 * t * m) / ((m : ℝ) + 1) ^ ((t - 2) + 2)) :
    2 ^ (64 * t * m) ≤ geometricSmoothCountConstant t * (m + 1) ^ (2 * (t - 2) + 1) *
      (((2 ^ (64 * t * m) + 1).primesBelow).filter
        (fun p => p - 1 ∈ Nat.smoothNumbers (2 ^ (128 * m)))).card := by
  let r := t - 2
  let N := 2 ^ (64 * t * m)
  let z : ℝ := (m : ℝ) + 1
  let C := primeProductMassConstant r
  let D := primeProductModuli r m
  let P := (N + 1).primesBelow
  let G := P.filter (fun p => p - 1 ∈ Nat.smoothNumbers (2 ^ (128 * m)))
  let S : ℝ := ∑ d ∈ D, (Nat.totient d : ℝ)⁻¹
  let T : ℝ := ∑ d ∈ D, (progressionPrimeCount d N : ℝ)
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hC : (0 : ℝ) < C := by exact_mod_cast primeProductMassConstant_pos r
  have hz : 0 < z := by dsimp [z]; positivity
  have hS : 1 / ((C : ℝ) * z ^ r) ≤ S := primeProductModuli_reciprocal_lower r m hsmall
  have hP : (N : ℝ) ≤ (128 * (t : ℝ)) * z * (P.card : ℝ) := by
    dsimp [N, z, P]
    exact_mod_cast geometric_total_prime_count_lower t m ht (by omega)
  have he : (P.card : ℝ) * S - (N : ℝ) / z ^ (r + 2) ≤ T := by
    have he' : geometricSmoothModulusDeficit t m ≤ (N : ℝ) / z ^ (r + 2) := by
      simpa only [N, Nat.cast_pow, Nat.cast_ofNat] using herr
    change (P.card : ℝ) * S - T ≤ (N : ℝ) / z ^ (r + 2) at he'
    linarith only [he']
  have hbudget' : 2 * (128 * (t : ℝ)) * (C : ℝ) ≤ z := by
    have h : (256 : ℝ) * t * C ≤ (m : ℝ) + 1 := by exact_mod_cast hbudget
    dsimp [z]
    nlinarith only [h]
  have hcount := polynomial_main_survives (N : ℝ) (P.card : ℝ) S T (128 * (t : ℝ)) (C : ℝ) z r
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by positivity) hC hz hP hS he hbudget'
  have hPdata : ∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (64 * t * m) := by
    intro p hp
    have h := Nat.mem_primesBelow.mp hp
    exact ⟨h.2, by omega⟩
  have hDdata : ∀ d ∈ D, d ∈ Nat.smoothNumbers (2 ^ (128 * m)) ∧
      2 ^ (64 * t * m) ≤ d * 2 ^ (128 * m) ∧ Squarefree d ∧ d.primeFactors.card = r := by
    intro d hd
    have h := primeProductModuli_progression_parameters t m ht hm hd
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  have hsum := large_smooth_moduli_ap_sum_le D P (64 * t * m) (2 ^ (128 * m)) r hPdata hDdata
  have hT : T ≤ (G.card : ℝ) * ((64 * t * m : ℕ) : ℝ) ^ r := by
    dsimp [T, progressionPrimeCount, G]
    change (∑ d ∈ D, ((P.filter (fun p => d ∣ p - 1)).card : ℝ)) ≤ _
    exact_mod_cast hsum
  have hE : ((64 * t * m : ℕ) : ℝ) ^ r ≤ (64 * (t : ℝ)) ^ r * z ^ r := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (Nat.cast_nonneg _)
    dsimp [z]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hfinal : (N : ℝ) ≤ (geometricSmoothCountConstant t : ℝ) * z ^ (2 * r + 1) * (G.card : ℝ) := by
    calc
      _ ≤ 2 * (128 * (t : ℝ)) * C * z ^ (r + 1) * T := hcount
      _ ≤ 2 * (128 * (t : ℝ)) * C * z ^ (r + 1) *
          ((G.card : ℝ) * ((64 * (t : ℝ)) ^ r * z ^ r)) := by
        exact mul_le_mul_of_nonneg_left (hT.trans
          (mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg _))) (by positivity)
      _ = _ := by
        simp only [geometricSmoothCountConstant, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        change _ = (256 * (t : ℝ) * C * (64 * (t : ℝ)) ^ r) * z ^ (2 * r + 1) * (G.card : ℝ)
        rw [show 2 * r + 1 = (r + 1) + r by omega, pow_add]
        ring
  dsimp [N, z, r, G, P] at hfinal
  exact_mod_cast hfinal

/-- The stronger all-modulus absolute-error hypothesis also supplies the finite transfer. -/
theorem geometric_distribution_smooth_prime_count (t m : ℕ) (ht : 3 ≤ t)
    (hm : max 2 (t - 2) ≤ m)
    (hsmall : 4096 * (t - 2) * (m + 1) ≤ progressionScaleN m)
    (hbudget : 256 * t * primeProductMassConstant (t - 2) ≤ m + 1)
    (herr : geometricProgressionError t m ≤ (2 : ℝ) ^ (64 * t * m) / ((m : ℝ) + 1) ^ ((t - 2) + 2)) :
    2 ^ (64 * t * m) ≤ geometricSmoothCountConstant t * (m + 1) ^ (2 * (t - 2) + 1) *
      (((2 ^ (64 * t * m) + 1).primesBelow).filter
        (fun p => p - 1 ∈ Nat.smoothNumbers (2 ^ (128 * m)))).card :=
  geometric_signed_deficit_smooth_prime_count t m ht hm hsmall hbudget
    ((geometric_smooth_deficit_le_error t m ht hm).trans herr)

/-- The explicit distribution hypothesis supplies the needed prime families
at every sufficiently large geometric scale. -/
lemma eventually_geometric_smooth_prime_family (H : GeometricProgressionDistribution)
    (t : ℕ) (ht : 3 ≤ t) :
    ∀ᶠ m : ℕ in atTop, ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (64 * t * m) ∧
        p - 1 ∈ Nat.smoothNumbers (2 ^ (128 * m))) ∧
      2 ^ ((64 * t - 1) * m) ≤ P.card := by
  have hpoly₁ := eventually_nat_poly_le_two_pow 1 (4096 * (t - 2)) 1
  have hpoly₂ := eventually_nat_poly_le_two_pow 1 (geometricSmoothCountConstant t) (2 * (t - 2) + 1)
  simp only [one_mul, pow_one] at hpoly₁
  simp only [one_mul] at hpoly₂
  filter_upwards [H t ht ((t - 2) + 2), hpoly₁, hpoly₂,
    eventually_ge_atTop (max (max 2 (t - 2)) (256 * t * primeProductMassConstant (t - 2)))]
    with m herr hsmall hpoly hm
  have hm' : max 2 (t - 2) ≤ m := (le_max_left _ _).trans hm
  have hbudget : 256 * t * primeProductMassConstant (t - 2) ≤ m + 1 :=
    ((le_max_right _ _).trans hm).trans (Nat.le_succ m)
  have hsmall' : 4096 * (t - 2) * (m + 1) ≤ progressionScaleN m :=
    hsmall.trans (Nat.pow_le_pow_right (by decide) (by omega))
  let P := ((2 ^ (64 * t * m) + 1).primesBelow).filter
    (fun p => p - 1 ∈ Nat.smoothNumbers (2 ^ (128 * m)))
  refine ⟨P, ?_, ?_⟩
  · intro p hp
    obtain ⟨hpP, hps⟩ := mem_filter.mp hp
    obtain ⟨hpN, hp⟩ := Nat.mem_primesBelow.mp hpP
    exact ⟨hp, by omega, hps⟩
  · have hc := geometric_distribution_smooth_prime_count t m ht hm' hsmall' hbudget herr
    have hpow : 2 ^ m * 2 ^ ((64 * t - 1) * m) = 2 ^ (64 * t * m) := by
      rw [← pow_add]
      congr 1
      calc
        m + (64 * t - 1) * m = (1 + (64 * t - 1)) * m := by ring
        _ = _ := by rw [Nat.add_sub_of_le (by omega : 1 ≤ 64 * t)]
    apply Nat.le_of_mul_le_mul_left (c := 2 ^ m) _ (by positivity)
    rw [hpow]
    exact hc.trans (Nat.mul_le_mul_right P.card hpoly)

lemma infinite_g_gt_of_geometric_distribution (H : GeometricProgressionDistribution)
    (t : ℕ) (ht : 3 ≤ t) :
    {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - 131 / (64 * (t : ℝ)))}.Infinite := by
  have hfamily : ∀ M : ℕ, ∃ m : ℕ, M ≤ m ∧ ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2 ^ (64 * t * m) ∧
        p - 1 ∈ Nat.smoothNumbers (2 ^ (128 * m))) ∧
      2 ^ ((64 * t - 1) * m) ≤ P.card := by
    obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp (eventually_geometric_smooth_prime_family H t ht)
    intro M
    exact ⟨max M m₀, le_max_left _ _, hm₀ _ (le_max_right _ _)⟩
  have hinf := infinite_g_gt_of_general_dyadic_density (64 * t) (64 * t - 1) 128
    (by omega) (by omega) (by omega) hfamily
  have hnat : 64 * t - 1 - 128 - 2 = 64 * t - 131 := by omega
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hexp : (((64 * t - 1 - 128 - 2 : ℕ) : ℝ) / ((64 * t : ℕ) : ℝ)) =
      1 - 131 / (64 * (t : ℝ)) := by
    rw [hnat, Nat.cast_sub (by omega : 131 ≤ 64 * t)]
    push_cast
    field_simp
  simpa only [hexp] using hinf

/-- A complete conditional implication. Its distribution hypothesis is explicit
and remains unproved; this theorem is not an unconditional settlement. -/
theorem erdos_821_of_geometric_progression_distribution (H : GeometricProgressionDistribution) :
    ∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite := by
  intro ε hε
  obtain ⟨t, ht⟩ := exists_nat_gt (max 3 (131 / (64 * ε)))
  have ht3R : (3 : ℝ) < t := (le_max_left _ _).trans_lt ht
  have ht3 : 3 ≤ t := by exact_mod_cast ht3R.le
  have htpos : (0 : ℝ) < t := by linarith
  have htbound : 131 / (64 * ε) < (t : ℝ) := (le_max_right _ _).trans_lt ht
  have hprod : 131 < (t : ℝ) * (64 * ε) := (div_lt_iff₀ (by positivity)).mp htbound
  have hexp : 1 - ε ≤ 1 - 131 / (64 * (t : ℝ)) := by
    have h : 131 / (64 * (t : ℝ)) ≤ ε := (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hprod])
    linarith
  have hinf := infinite_g_gt_of_geometric_distribution H t ht3
  apply (hinf.diff (Set.finite_singleton 0)).mono
  intro n hn
  have hn0 : n ≠ 0 := by simpa only [Set.mem_singleton_iff] using hn.2
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  exact (Real.rpow_le_rpow_of_exponent_le hn1 hexp).trans_lt hn.1

end Erdos821
