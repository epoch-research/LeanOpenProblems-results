import Submission.CoreTailSieve
import Submission.ExactCoverLinear

/-!
A subquadratic bound for covers under sum(1/p) <= 1. The square of their length
is O(k^3). This does not apply to unrestricted prime sets in Erdős 970.
-/
namespace Erdos970.ReciprocalBudget
open Finset Real Filter
open Erdos970.WeightedMertens

/-- One exact core prime gives a length bound linear in that prime and in the
number of selected primes. All overlaps remain allowed. -/
theorem cover_length_le_four_prime_card (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (r : ℕ → ℕ) (m : ℕ)
    (hs : (∑ p ∈ P, 1 / (p : ℝ)) ≤ 1)
    (hcover : ∀ x < m, ∃ p ∈ P, x ≡ r p [MOD p])
    (p : ℕ) (hp : p ∈ P) : (m : ℝ) ≤ 4 * p * P.card := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hden : 1 / 2 ≤ 1 - 1 / (p : ℝ) := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2
    linarith
  have hsplit := sum_erase_add P (fun q : ℕ => 1 / (q : ℝ)) hp
  have htail : 1 / (p : ℝ) ≤ 1 - ∑ q ∈ P.erase p, 1 / (q : ℝ) := by linarith
  have hunion : {p} ∪ P.erase p = P := by simp [hp]
  have hc := CoreTailSieve.cover_core_tail_bound {p} (P.erase p)
    (by simpa using hP p hp) (fun q hq => hP q (mem_erase.mp hq).2)
    (by simp) r m (by simpa only [hunion] using hcover)
  have hk : 1 ≤ P.card := card_pos.mpr ⟨p, hp⟩
  have hcard : ((P.erase p).card : ℝ) + 1 = P.card := by
    exact_mod_cast (show (P.erase p).card + 1 = P.card by rw [card_erase_of_mem hp]; omega)
  simp only [CoreTailSieve.density, prod_singleton, card_singleton, pow_one, hcard] at hc
  have hprod : (1 / 2 : ℝ) * (1 / (p : ℝ)) ≤
      (1 - 1 / (p : ℝ)) * (1 - ∑ q ∈ P.erase p, 1 / (q : ℝ)) :=
    mul_le_mul hden htail (by positivity) (by linarith)
  have hm := mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg m)
  have hdiv : (m : ℝ) / (2 * p) ≤ 2 * P.card := by
    have he : (m : ℝ) * ((1 / 2 : ℝ) * (1 / (p : ℝ))) = (m : ℝ) / (2 * p) := by ring
    rw [he] at hm
    nlinarith only [hm, hc]
  have hh := (div_le_iff₀ (show (0 : ℝ) < 2 * p by positivity)).mp hdiv
  nlinarith only [hh]

/-- If the least selected prime is large and its square exceeds 16k, then
Mertens bounds the entire reciprocal mass away from one. -/
lemma reciprocal_small_of_large_min (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (p : ℕ) (hp : p ∈ P) (hmin : ∀ q ∈ P, p ≤ q)
    (hx : 12 ≤ sqrt (p : ℝ))
    (hlog : 12 * (boundConstant + 1) ≤ log (sqrt (p : ℝ)))
    (hsize : 16 * (P.card : ℝ) ≤ (p : ℝ) ^ 2) :
    (∑ q ∈ P, (q : ℝ)⁻¹) ≤ 7 / 8 := by
  classical
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
  have hsqrt := sq_sqrt hp0.le
  have hp144 : (144 : ℝ) ≤ p := by nlinarith [sq_nonneg (sqrt (p : ℝ) - 12)]
  have hfilter : P.filter (fun q : ℕ => sqrt (p : ℝ) ^ 2 < (q : ℝ)) = P.erase p := by
    ext q
    simp only [mem_filter, mem_erase, hsqrt]
    constructor
    · rintro ⟨hq, hlt⟩
      exact ⟨by intro he; subst q; exact lt_irrefl _ hlt, hq⟩
    · rintro ⟨hne, hq⟩
      refine ⟨hq, ?_⟩
      exact_mod_cast (show p < q by have := hmin q hq; omega)
  have hfour : sqrt (p : ℝ) ^ 4 = (p : ℝ) ^ 2 := by nlinarith [sq_sqrt hp0.le]
  have ht := DisjointCover.tail_power_bound P hP (sqrt (p : ℝ)) hx hlog 2
    (by omega) (by omega)
  rw [hfilter, hfour] at ht
  norm_num only [Nat.cast_ofNat, show (4 : ℝ) / 2 = 2 by norm_num] at ht
  have hc : (P.card : ℝ) / (p : ℝ) ^ 2 ≤ 1 / 16 := by
    apply (div_le_iff₀ (sq_pos_of_pos hp0)).mpr
    linarith only [hsize]
  have hi : (p : ℝ)⁻¹ ≤ 1 / 144 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 144) hp144
  have hsplit := sum_erase_add P (fun q : ℕ => (q : ℝ)⁻¹) hp
  linarith only [ht, hc, hi, hsplit, log_two_lt_d9]

/-- Uniform subquadratic bound, expressed without real fractional powers:
under the reciprocal budget, m^2 <= C*k^3 for one absolute C. -/
theorem prime_cover_square_le_card_cube :
    ∃ C > (0 : ℝ), ∀ (P : Finset ℕ) (r : ℕ → ℕ) (m : ℕ),
      (∀ p ∈ P, p.Prime) → (∑ p ∈ P, 1 / (p : ℝ)) ≤ 1 →
      (∀ x < m, ∃ p ∈ P, x ≡ r p [MOD p]) →
      (m : ℝ) ^ 2 ≤ C * (P.card : ℝ) ^ 3 := by
  have hroot : Tendsto (fun p : ℕ => sqrt (p : ℝ)) atTop atTop :=
    tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hx : ∀ᶠ p : ℕ in atTop, 12 ≤ sqrt (p : ℝ) :=
    hroot.eventually (eventually_ge_atTop _)
  have hl : ∀ᶠ p : ℕ in atTop,
      12 * (boundConstant + 1) ≤ log (sqrt (p : ℝ)) :=
    (tendsto_log_atTop.comp hroot).eventually (eventually_ge_atTop _)
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hx.and hl)
  let C : ℝ := 16 * ((M : ℝ) + 4) ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  have hC256 : (256 : ℝ) ≤ C := by
    dsimp [C]
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    nlinarith [sq_nonneg (M : ℝ)]
  refine ⟨C, hC, ?_⟩
  intro P r m hP hs hcover
  by_cases hm : m = 0
  · simp only [hm, Nat.cast_zero, zero_pow (by omega : 2 ≠ 0)]
    positivity
  have hne : P.Nonempty := by
    obtain ⟨p, hp, _⟩ := hcover 0 (by omega)
    exact ⟨p, hp⟩
  let p := P.min' hne
  have hp : p ∈ P := min'_mem P hne
  have hk : (1 : ℝ) ≤ P.card := by exact_mod_cast card_pos.mpr hne
  have hk0 : (0 : ℝ) ≤ P.card := Nat.cast_nonneg _
  have hpk := cover_length_le_four_prime_card P hP r m hs hcover p hp
  have hsquare : (m : ℝ) ^ 2 ≤ 16 * (p : ℝ) ^ 2 * (P.card : ℝ) ^ 2 := by
    have hh := (sq_le_sq₀ (Nat.cast_nonneg m) (by positivity : (0 : ℝ) ≤ 4 * p * P.card)).mpr hpk
    nlinarith only [hh]
  by_cases hpM : p < M
  · have hpR : (p : ℝ) ≤ M := by exact_mod_cast hpM.le
    have hcoef : 16 * (p : ℝ) ^ 2 ≤ C := by
      dsimp [C]
      have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
      nlinarith [sq_nonneg ((M : ℝ) - p)]
    have hkpow : (P.card : ℝ) ^ 2 ≤ (P.card : ℝ) ^ 3 := by nlinarith [sq_nonneg ((P.card : ℝ) - 1)]
    exact hsquare.trans ((mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hkpow hC.le))
  · by_cases hpsq : (p : ℝ) ^ 2 ≤ 16 * P.card
    · have hh := mul_le_mul_of_nonneg_right hpsq (show (0 : ℝ) ≤ 16 * (P.card : ℝ) ^ 2 by positivity)
      have hfinal : (m : ℝ) ^ 2 ≤ 256 * (P.card : ℝ) ^ 3 := by nlinarith only [hsquare, hh]
      exact hfinal.trans (mul_le_mul_of_nonneg_right hC256 (by positivity))
    · have htail := reciprocal_small_of_large_min P hP p hp
        (fun q hq => min'_le P q hq) (hM p (by omega)).1 (hM p (by omega)).2
        (le_of_not_ge hpsq)
      have hcount := DisjointCover.cover_length_real_le hcover hP
      have hmul := mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg m)
      have hlin : (m : ℝ) ≤ 8 * P.card := by linarith
      have hsq := (sq_le_sq₀ (Nat.cast_nonneg m) (by positivity : (0 : ℝ) ≤ 8 * P.card)).mpr hlin
      have hkpow : (P.card : ℝ) ^ 2 ≤ (P.card : ℝ) ^ 3 := by nlinarith [sq_nonneg ((P.card : ℝ) - 1)]
      have h64 : (64 : ℝ) ≤ C := by linarith
      calc
        (m : ℝ) ^ 2 ≤ 64 * (P.card : ℝ) ^ 2 := by nlinarith only [hsq]
        _ ≤ 64 * (P.card : ℝ) ^ 3 := mul_le_mul_of_nonneg_left hkpow (by norm_num)
        _ ≤ C * (P.card : ℝ) ^ 3 := mul_le_mul_of_nonneg_right h64 (by positivity)

#print axioms cover_length_le_four_prime_card
#print axioms reciprocal_small_of_large_min
#print axioms prime_cover_square_le_card_cube
end Erdos970.ReciprocalBudget
