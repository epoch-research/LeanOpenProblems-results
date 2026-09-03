import Submission.QuadraticDifferenceLayerCake
import Submission.CumulativePrimeSharp
import Submission.PrimeAllLogMoments
import Submission.SelbergCubicEnergy

/-! Prime-indexed quadratic logarithmic profile estimates. The name refers to
 the profile, not to a quadratic bound for Jacobsthal's function. -/
namespace Erdos970.FiniteSelberg
open Finset Real
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def primeQuadraticProfile (p : ι → ℕ) (L : ℝ) (Q : Finset ι) : ℝ :=
  quadraticProfile L (primeLogLocation p Q)

lemma quadraticProfile_zero (L x : ℝ) (hL : 0 ≤ L) (hx : L ≤ x) :
    quadraticProfile L x = 0 := by
  unfold quadraticProfile
  apply max_eq_right
  nlinarith

lemma quadraticProfile_shift_cap (L a v : ℝ) (hL : 0 ≤ L) (ha : 0 ≤ a) :
    quadraticProfile L (a + v) = quadraticProfile L (a + min v L) := by
  by_cases hv : v ≤ L
  · rw [min_eq_left hv]
  · rw [min_eq_right (le_of_not_ge hv), quadraticProfile_zero L (a + v) hL (by linarith),
      quadraticProfile_zero L (a + L) hL (by linarith)]

lemma primeQuadraticProfile_difference (p : ι → ℕ) (L : ℝ) (hL : 0 ≤ L)
    (Q : Finset ι) (i : ι) (hi : i ∉ Q) :
    primeQuadraticProfile p L Q - primeQuadraticProfile p L (insert i Q) =
      quadraticProfile L (primeLogLocation p Q) -
        quadraticProfile L (primeLogLocation p Q + min (log (p i : ℝ)) L) := by
  unfold primeQuadraticProfile
  have he : primeLogLocation p (insert i Q) = primeLogLocation p Q + log (p i : ℝ) := by
    unfold primeLogLocation
    rw [sum_insert hi, add_comm]
  rw [he, quadraticProfile_shift_cap L _ _ hL (primeLogLocation_nonneg p Q)]

lemma prime_quadratic_square_lower (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (R : ℕ) (hR : 0 < R)
    (hfull : ∀ a, a.Prime → a ≤ R → ∃ i, p i = a) :
    (8 / 15) * log (R : ℝ) ^ 5 - log (R : ℝ) ^ 4 ≤
      ∑ Q : Finset ι, weight (fun i => 1 / (p i : ℝ)) Q * primeQuadraticProfile p (log R) Q ^ 2 := by
  simpa only [one_mul, primeQuadraticProfile] using
    quadratic_square_lower (weight (fun i => 1 / (p i : ℝ))) (primeLogLocation p)
      (primeLogLocation_nonneg p) (log R) 1 (log_natCast_nonneg R)
      (fun t ht => cumulative_prime_lower p hp hinj R hR hfull t ht.1 ht.2)

lemma prime_quadratic_dirichlet_coordinate (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (R : ℕ) (hR : 0 < R)
    (hfull : ∀ a, a.Prime → a ≤ R → ∃ i, p i = a)
    (B : ℕ) (hB : 0 < B) (i : ι) :
    let L := log (R : ℝ)
    let v := min (log (p i : ℝ)) L
    let E := L / B + normalizerOffset (B + 1) + 1
    (∑ Q ∈ (univ.erase i).powerset, weight (fun i => 1 / (p i : ℝ)) Q *
      (primeQuadraticProfile p L Q - primeQuadraticProfile p L (insert i Q)) ^ 2) ≤
      (4 / 3) * L ^ 3 * v ^ 2 - (2 / 3) * L ^ 2 * v ^ 3 - (2 / 15) * v ^ 5 +
        8 * E * L ^ 2 * v ^ 2 := by
  dsimp only
  let L := log (R : ℝ)
  let v := min (log (p i : ℝ)) L
  let E := L / B + normalizerOffset (B + 1) + 1
  have hL : 0 ≤ L := log_natCast_nonneg R
  have hv : 0 ≤ v := le_min (log_natCast_nonneg _) hL
  have hvL : v ≤ L := min_le_right _ _
  have hE : 0 ≤ E := by
    have := normalizerOffset_pos (B + 1)
    dsimp [E]
    positivity
  have hh := quadratic_difference_error (weight (fun i => 1 / (p i : ℝ)))
    (primeLogLocation p) (primeLogLocation_nonneg p) L v E hv hvL hE
    (fun t ht => cumulative_prime_uniform_error p hp hinj R hR hfull B hB t ht.1 ht.2)
  have hup := (abs_le.mp hh).2
  have hs : (∑ Q ∈ (univ.erase i).powerset, weight (fun i => 1 / (p i : ℝ)) Q *
      (primeQuadraticProfile p L Q - primeQuadraticProfile p L (insert i Q)) ^ 2) ≤
      ∑ Q : Finset ι, weight (fun i => 1 / (p i : ℝ)) Q *
        (quadraticProfile L (primeLogLocation p Q) - quadraticProfile L (primeLogLocation p Q + v)) ^ 2 := by
    calc
      _ = ∑ Q ∈ (univ.erase i).powerset, weight (fun i => 1 / (p i : ℝ)) Q *
          (quadraticProfile L (primeLogLocation p Q) - quadraticProfile L (primeLogLocation p Q + v)) ^ 2 := by
        apply sum_congr rfl
        intro Q hQ
        rw [primeQuadraticProfile_difference p L hL Q i (not_mem_of_erase_powerset hQ)]
      _ ≤ _ := by
        apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
        intro Q hQ hn
        exact mul_nonneg (weight_pos _ (prime_marginals p hp) Q).le (sq_nonneg _)
  change _ ≤ (4 / 3) * L ^ 3 * v ^ 2 - (2 / 3) * L ^ 2 * v ^ 3 - (2 / 15) * v ^ 5 +
    8 * E * L ^ 2 * v ^ 2
  linarith

/-- The total Dirichlet cost is expressed through moments2,3,5, retaining the
  negative fifth-moment term and the variation error. -/
theorem prime_quadratic_dirichlet_le (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (R : ℕ) (hR : 0 < R)
    (hfull : ∀ a, a.Prime → a ≤ R → ∃ i, p i = a)
    (B : ℕ) (hB : 0 < B) :
    let L := log (R : ℝ)
    let E := L / B + normalizerOffset (B + 1) + 1
    (∑ i, (1 / (p i : ℝ)) * ∑ Q ∈ (univ.erase i).powerset,
      weight (fun i => 1 / (p i : ℝ)) Q *
        (primeQuadraticProfile p L Q - primeQuadraticProfile p L (insert i Q)) ^ 2) ≤
      (4 / 3) * L ^ 3 * cappedLogMoment p L 2 - (2 / 3) * L ^ 2 * cappedLogMoment p L 3 -
        (2 / 15) * cappedLogMoment p L 5 + 8 * E * L ^ 2 * cappedLogMoment p L 2 := by
  dsimp only
  calc
    _ ≤ ∑ i, (1 / (p i : ℝ)) *
        ((4 / 3) * log (R : ℝ) ^ 3 * min (log (p i : ℝ)) (log R) ^ 2 -
          (2 / 3) * log (R : ℝ) ^ 2 * min (log (p i : ℝ)) (log R) ^ 3 -
          (2 / 15) * min (log (p i : ℝ)) (log R) ^ 5 +
          8 * (log (R : ℝ) / B + normalizerOffset (B + 1) + 1) * log (R : ℝ) ^ 2 *
            min (log (p i : ℝ)) (log R) ^ 2) := by
      apply sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (prime_quadratic_dirichlet_coordinate p hp hinj R hR hfull B hB i) (by positivity)
    _ = _ := by
      unfold cappedLogMoment
      simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
      apply sum_congr rfl
      intro i hi
      ring

#print axioms prime_quadratic_square_lower
#print axioms prime_quadratic_dirichlet_le
end Erdos970.FiniteSelberg
