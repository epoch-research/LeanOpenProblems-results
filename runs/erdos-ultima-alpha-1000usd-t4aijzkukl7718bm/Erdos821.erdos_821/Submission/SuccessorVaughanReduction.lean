import Submission.FiniteConvolution

/-!
# Vaughan reduction for weighted successors

These are finite identities and a conditional prime-count transfer. The
Type II term retains the weight of the OUTPUT product r*s. Bounds for
input character sums or successor divisibility do not estimate this term.
No new smooth-prime lower bound is asserted here.
-/

open Nat Finset ArithmeticFunction
open scoped Classical BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius

namespace Erdos821.AnalyticSieve.SuccessorVaughan

set_option maxHeartbeats 3000000

noncomputable def weightedSum (f : ArithmeticFunction ℝ) (w : ℕ → ℝ) (X : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 X, f n * w n

noncomputable def hyperbolicSum (f g : ArithmeticFunction ℝ) (w : ℕ → ℝ) (X : ℕ) : ℝ :=
  ∑ r ∈ Icc 1 X, ∑ s ∈ Icc 1 X,
    if r*s ≤ X then (f r*g s)*w (r*s) else 0

lemma weightedSum_add (f g : ArithmeticFunction ℝ) (w : ℕ → ℝ) (X : ℕ) :
    weightedSum (f+g) w X = weightedSum f w X + weightedSum g w X := by
  simp only [weightedSum, ArithmeticFunction.add_apply, add_mul, sum_add_distrib]

lemma weightedSum_sub (f g : ArithmeticFunction ℝ) (w : ℕ → ℝ) (X : ℕ) :
    weightedSum (f-g) w X = weightedSum f w X - weightedSum g w X := by
  simp only [weightedSum, (show ∀ n, (f-g) n = f n-g n from fun n => rfl), sub_mul, sum_sub_distrib]

lemma weightedSum_convolution (f g : ArithmeticFunction ℝ) (w : ℕ → ℝ) (X : ℕ) :
    weightedSum (f*g) w X = hyperbolicSum f g w X :=
  sum_convolution_weighted f g w (le_refl X)

/-- Exact identity for an arbitrary output weight, with no primality or
positivity hypothesis on that weight. -/
theorem weighted_vaughan_identity (w : ℕ → ℝ) (U V X : ℕ) :
    weightedSum vonMangoldt w X =
      weightedSum (shortPart vonMangoldt U) w X +
      hyperbolicSum (shortPart (μ : ArithmeticFunction ℝ) V) log w X -
      hyperbolicSum (vaughanTypeI U V) (ζ : ArithmeticFunction ℝ) w X +
      hyperbolicSum (vaughanTypeII V) (longPart vonMangoldt U) w X := by
  have h := congrArg (fun f => weightedSum f w X)
    (vaughan_identity_typeI_typeII U V)
  simpa only [weightedSum_add, weightedSum_sub, weightedSum_convolution] using h

lemma weightedSum_weight_sub (f : ArithmeticFunction ℝ) (w v : ℕ → ℝ) (X : ℕ) :
    weightedSum f (fun n => w n-v n) X = weightedSum f w X-weightedSum f v X := by
  simp only [weightedSum, mul_sub, sum_sub_distrib]

/-- A valid transfer needs control of the output-factorization discrepancy
as well as the two Type I discrepancies and the short term. -/
theorem weighted_mangoldt_discrepancy_le (w v : ℕ → ℝ) (U V X : ℕ) :
    |weightedSum vonMangoldt w X-weightedSum vonMangoldt v X| ≤
      |weightedSum (shortPart vonMangoldt U) (fun n => w n-v n) X| +
      |hyperbolicSum (shortPart (μ : ArithmeticFunction ℝ) V) log
        (fun n => w n-v n) X| +
      |hyperbolicSum (vaughanTypeI U V) (ζ : ArithmeticFunction ℝ)
        (fun n => w n-v n) X| +
      |hyperbolicSum (vaughanTypeII V) (longPart vonMangoldt U)
        (fun n => w n-v n) X| := by
  rw [← weightedSum_weight_sub, weighted_vaughan_identity (fun n => w n-v n) U V X]
  exact (abs_add_le _ _).trans (add_le_add
    ((abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)

noncomputable def positivePrimeOutputs (w : ℕ → ℝ) (X : ℕ) : Finset ℕ :=
  (Icc 1 X).filter (fun n => n.Prime ∧ 0 < w n)

lemma weighted_prime_sum_le (w : ℕ → ℝ) (X : ℕ) (B : ℝ)
    (hw : ∀ n ∈ Icc 1 X, 0 ≤ w n)
    (hB : ∀ n ∈ Icc 1 X, w n ≤ B) :
    (∑ n ∈ (Icc 1 X).filter Nat.Prime, vonMangoldt n*w n) ≤
      B*Real.log X*((positivePrimeOutputs w X).card : ℝ) := by
  have he : (∑ n ∈ (Icc 1 X).filter Nat.Prime, vonMangoldt n*w n) =
      ∑ n ∈ positivePrimeOutputs w X, vonMangoldt n*w n := by
    symm
    apply sum_subset
    · intro n hn
      obtain ⟨hn, hp, _⟩ := mem_filter.mp hn
      exact mem_filter.mpr ⟨hn,hp⟩
    · intro n hn hnot
      obtain ⟨hn,hp⟩ := mem_filter.mp hn
      have hz : w n = 0 := by
        have hh : ¬ 0 < w n := fun h => hnot (mem_filter.mpr ⟨hn,hp,h⟩)
        exact le_antisymm (le_of_not_gt hh) (hw n hn)
      rw [hz, mul_zero]
  rw [he]
  calc
    _ ≤ ∑ _n ∈ positivePrimeOutputs w X, B*Real.log X := by
      apply sum_le_sum
      intro n hn
      obtain ⟨hn,hp,hpos⟩ := mem_filter.mp hn
      rw [vonMangoldt_apply_prime hp]
      have hnR : (0 : ℝ) < n := by exact_mod_cast hp.pos
      have hlog : Real.log (n : ℝ) ≤ Real.log X :=
        Real.log_le_log hnR (Nat.cast_le.mpr (mem_Icc.mp hn).2)
      calc
        _ ≤ Real.log X*w n := mul_le_mul_of_nonneg_right hlog hpos.le
        _ ≤ Real.log X*B := mul_le_mul_of_nonneg_left (hB n hn)
          (Real.log_natCast_nonneg X)
        _ = _ := mul_comm _ _
    _ = _ := by rw [sum_const, nsmul_eq_mul]; ring

lemma weighted_nonprime_sum_le (w : ℕ → ℝ) (X : ℕ) (hX : 1 ≤ X) (B : ℝ)
    (hB0 : 0 ≤ B) (hB : ∀ n ∈ Icc 1 X, w n ≤ B) :
    (∑ n ∈ (Icc 1 X).filter (fun n => ¬n.Prime), vonMangoldt n*w n) ≤
      2*B*Real.sqrt X*Real.log X := by
  have he : (∑ n ∈ (Icc 1 X).filter (fun n => ¬n.Prime), vonMangoldt n) =
      Chebyshev.psi (X : ℝ)-Chebyshev.theta (X : ℝ) := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast]
    rfl
  calc
    _ ≤ ∑ n ∈ (Icc 1 X).filter (fun n => ¬n.Prime), vonMangoldt n*B := by
      apply sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_left (hB n (mem_filter.mp hn).1) vonMangoldt_nonneg
    _ = B*(Chebyshev.psi (X : ℝ)-Chebyshev.theta (X : ℝ)) := by
      rw [← sum_mul, he, mul_comm]
    _ ≤ B*|Chebyshev.psi (X : ℝ)-Chebyshev.theta (X : ℝ)| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hB0
    _ ≤ B*(2*Real.sqrt X*Real.log X) := mul_le_mul_of_nonneg_left
      (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by exact_mod_cast hX)) hB0
    _ = _ := by ring

/-- Prime powers are charged separately, and the output-weight bound B
pays for collisions when the weight counts multiple representations. -/
theorem weighted_mangoldt_le_prime_outputs (w : ℕ → ℝ) (X : ℕ) (hX : 1 ≤ X)
    (B : ℝ) (hB0 : 0 ≤ B) (hw : ∀ n ∈ Icc 1 X, 0 ≤ w n)
    (hB : ∀ n ∈ Icc 1 X, w n ≤ B) :
    weightedSum vonMangoldt w X ≤
      B*Real.log X*((positivePrimeOutputs w X).card : ℝ) +
      2*B*Real.sqrt X*Real.log X := by
  unfold weightedSum
  rw [← sum_filter_add_sum_filter_not (Icc 1 X) Nat.Prime]
  exact add_le_add (weighted_prime_sum_le w X B hw hB)
    (weighted_nonprime_sum_le w X hX B hB0 hB)

/-- A finite prime-detection implication. Its strict lower bound on the
Vaughan expression is an explicit hypothesis, not an available estimate. -/
theorem prime_output_card_gt_of_vaughan_lower (w : ℕ → ℝ)
    (U V X : ℕ) (hX : 1 ≤ X) (B K : ℝ) (hB0 : 0 ≤ B)
    (hw : ∀ n ∈ Icc 1 X, 0 ≤ w n) (hB : ∀ n ∈ Icc 1 X, w n ≤ B)
    (H : B*Real.log X*K+2*B*Real.sqrt X*Real.log X <
      weightedSum (shortPart vonMangoldt U) w X +
      hyperbolicSum (shortPart (μ : ArithmeticFunction ℝ) V) log w X -
      hyperbolicSum (vaughanTypeI U V) (ζ : ArithmeticFunction ℝ) w X +
      hyperbolicSum (vaughanTypeII V) (longPart vonMangoldt U) w X) :
    K < ((positivePrimeOutputs w X).card : ℝ) := by
  rw [← weighted_vaughan_identity] at H
  have hb := weighted_mangoldt_le_prime_outputs w X hX B hB0 hw hB
  by_contra h
  have hc : ((positivePrimeOutputs w X).card : ℝ) ≤ K := le_of_not_gt h
  have hmul := mul_le_mul_of_nonneg_left hc
    (mul_nonneg hB0 (Real.log_natCast_nonneg X))
  linarith

noncomputable def rectangleOutputWeight (P A B : Finset ℕ) (n : ℕ) : ℝ :=
  (((P ×ˢ (A ×ˢ B)).filter (fun z => z.1*z.2.1*z.2.2+1=n)).card : ℝ)

lemma rectangleOutputWeight_nonneg (P A B : Finset ℕ) (n : ℕ) :
    0 ≤ rectangleOutputWeight P A B n := Nat.cast_nonneg _

/-- Reindexing by the output retains all representation multiplicities. -/
lemma rectangle_weightedSum_eq (f : ArithmeticFunction ℝ)
    (P A B : Finset ℕ) (X : ℕ)
    (hX : ∀ z ∈ P ×ˢ (A ×ˢ B), z.1*z.2.1*z.2.2+1 ≤ X) :
    weightedSum f (rectangleOutputWeight P A B) X =
      ∑ z ∈ P ×ˢ (A ×ˢ B), f (z.1*z.2.1*z.2.2+1) := by
  let T := P ×ˢ (A ×ˢ B)
  let F : ℕ × (ℕ × ℕ) → ℕ := fun z => z.1*z.2.1*z.2.2+1
  have hmap : ∀ z ∈ T, F z ∈ Icc 1 X := by
    intro z hz
    exact mem_Icc.mpr ⟨Nat.succ_pos _, hX z hz⟩
  have he := sum_fiberwise_of_maps_to hmap (fun z => f (F z))
  change (∑ n ∈ Icc 1 X, ∑ z ∈ T with F z=n, f (F z)) = _ at he
  rw [← he]
  unfold weightedSum rectangleOutputWeight
  apply sum_congr rfl
  intro n hn
  have hf : (∑ z ∈ T with F z=n, f (F z)) =
      ∑ z ∈ T with F z=n, f n := by
    apply sum_congr rfl
    intro z hz
    rw [(mem_filter.mp hz).2]
  rw [hf, sum_const, nsmul_eq_mul]
  exact mul_comm _ _

/-- Distinct representations of a positive predecessor are charged to
pairs of divisors; the third coordinate is then determined. -/
lemma rectangleOutputWeight_le_divisors_sq (P A B : Finset ℕ) (n : ℕ)
    (hn : 2 ≤ n) :
    rectangleOutputWeight P A B n ≤ ((n-1).divisors.card : ℝ)^2 := by
  let T := (P ×ˢ (A ×ˢ B)).filter (fun z => z.1*z.2.1*z.2.2+1=n)
  let D := (n-1).divisors
  have he (z : ℕ × (ℕ × ℕ)) (hz : z ∈ T) :
      z.1*z.2.1*z.2.2 = n-1 := by
    have hh := (mem_filter.mp hz).2
    omega
  have hpos (z : ℕ × (ℕ × ℕ)) (hz : z ∈ T) : 0 < z.1*z.2.1 := by
    have hh := he z hz
    by_contra h
    have hz0 : z.1*z.2.1 = 0 := by omega
    rw [hz0, zero_mul] at hh
    omega
  have hc : T.card ≤ (D ×ˢ D).card := by
    apply card_le_card_of_injOn (fun z : ℕ × (ℕ × ℕ) => (z.1,z.2.1))
    · intro z hz
      apply mem_product.mpr
      constructor
      · apply Nat.mem_divisors.mpr
        refine ⟨?_, by omega⟩
        rw [← he z hz]
        exact (Nat.dvd_mul_right z.1 z.2.1).trans
          (Nat.dvd_mul_right (z.1*z.2.1) z.2.2)
      · apply Nat.mem_divisors.mpr
        refine ⟨?_, by omega⟩
        rw [← he z hz]
        exact (Nat.dvd_mul_left z.2.1 z.1).trans
          (Nat.dvd_mul_right (z.1*z.2.1) z.2.2)
    · intro z hz z' hz' hh
      have h₁ : z.1=z'.1 := congrArg (fun t : ℕ × ℕ => t.1) hh
      have h₂ : z.2.1=z'.2.1 := congrArg (fun t : ℕ × ℕ => t.2) hh
      apply Prod.ext h₁
      apply Prod.ext h₂
      apply Nat.eq_of_mul_eq_mul_left (hpos z hz)
      calc
        z.1*z.2.1*z.2.2 = n-1 := he z hz
        _ = z'.1*z'.2.1*z'.2.2 := (he z' hz').symm
        _ = z.1*z.2.1*z'.2.2 := by rw [h₁,h₂]
  rw [card_product] at hc
  change (T.card : ℝ) ≤ _
  have hcast : (T.card : ℝ) ≤ (D.card : ℝ)*(D.card : ℝ) := by exact_mod_cast hc
  simpa only [D, pow_two] using hcast

lemma rectangleOutputWeight_one (P A B : Finset ℕ)
    (hP : ∀ p ∈ P, 0 < p) (hA : ∀ a ∈ A, 0 < a) (hB : ∀ b ∈ B, 0 < b) :
    rectangleOutputWeight P A B 1 = 0 := by
  have he : (P ×ˢ (A ×ˢ B)).filter
      (fun z => z.1*z.2.1*z.2.2+1=1) = ∅ := by
    apply filter_eq_empty_iff.mpr
    intro z hz hh
    obtain ⟨hp,hab⟩ := mem_product.mp hz
    obtain ⟨ha,hb⟩ := mem_product.mp hab
    have hpos := Nat.mul_pos (Nat.mul_pos (hP _ hp) (hA _ ha)) (hB _ hb)
    omega
  simp only [rectangleOutputWeight, he, card_empty, Nat.cast_zero]

/-- The output Type II term is supported on r*s=p*a*b+1 and retains both
Vaughan coefficients. This is not the unweighted congruence count. -/
theorem rectangle_typeII_eq (P A B : Finset ℕ) (U V X : ℕ) :
    hyperbolicSum (vaughanTypeII V) (longPart vonMangoldt U)
      (rectangleOutputWeight P A B) X =
    ∑ r ∈ Icc 1 X, ∑ s ∈ Icc 1 X,
      if r*s ≤ X then (vaughanTypeII V r*longPart vonMangoldt U s)*
        (((P ×ˢ (A ×ˢ B)).filter
          (fun z => z.1*z.2.1*z.2.2+1=r*s)).card : ℝ) else 0 := rfl

end Erdos821.AnalyticSieve.SuccessorVaughan
