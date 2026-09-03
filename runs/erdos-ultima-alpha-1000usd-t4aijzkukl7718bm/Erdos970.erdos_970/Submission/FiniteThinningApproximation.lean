import Submission.PrimeDilution
import Submission.FiniteThinningMoments

/-! A quantitative, finite version of prime thinning. No independence of
positions is assumed: the error is proved from exact joint moments. -/
namespace Erdos970.GapAverages.FiniteThinning
open Finset Real Erdos970.PrimeDilution

lemma joint_nonneg (P A : Finset ℕ) : 0 ≤ joint P A := by
  unfold joint phaseMean
  apply div_nonneg _ (by positivity)
  apply sum_nonneg
  intro r _
  apply prod_nonneg
  intro x _
  rcases point_eq_zero_or_one P x r with h | h <;> simp [h]

lemma joint_le_one (P A : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) : joint P A ≤ 1 := by
  rw [← phaseMean_const P hP 1]
  apply phaseMean_mono
  intro r
  apply prod_le_one
  · intro x _
    rcases point_eq_zero_or_one P x r with h | h <;> simp [h]
  · intro x _
    rcases point_eq_zero_or_one P x r with h | h <;> simp [h]

lemma reciprocal_square_sum_le (R : Finset ℕ) (B : ℕ) (hB : 0 < B)
    (hR : ∀ p ∈ R, B ≤ p) (hs : (∑ p ∈ R, 1/(p : ℝ)) ≤ 1) :
    (∑ p ∈ R, (1/(p : ℝ))^2) ≤ 1/(B : ℝ) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hsum : (∑ p ∈ R, (1/(p : ℝ))^2) ≤
      (1/(B : ℝ)) * ∑ p ∈ R, 1/(p : ℝ) := by
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have hpB : (B : ℝ) ≤ p := by exact_mod_cast hR p hp
    have hh := one_div_le_one_div_of_le hB0 hpB
    nlinarith [mul_le_mul_of_nonneg_right hh (show 0 ≤ 1/(p : ℝ) by positivity)]
  exact hsum.trans (by nlinarith [mul_le_mul_of_nonneg_left hs (show 0 ≤ 1/(B : ℝ) by positivity)])

lemma joint_product_target_error (R : Finset ℕ) (B s : ℕ) (hB : 4 ≤ B)
    (hsB : s ≤ B) (hR : ∀ p ∈ R, B ≤ p)
    (hlo : (63/64 : ℝ)-1/(B : ℝ) ≤ ∏ p ∈ R, (1-1/(p : ℝ)))
    (hhi : (∏ p ∈ R, (1-1/(p : ℝ))) ≤ (63/64 : ℝ))
    (hsum : (∑ p ∈ R, 1/(p : ℝ)) ≤ 1) :
    0 ≤ (63/64 : ℝ)^s - ∏ p ∈ R, (1-(s : ℝ)/p) ∧
      (63/64 : ℝ)^s - ∏ p ∈ R, (1-(s : ℝ)/p) ≤
        ((s : ℝ)^2+s)/(B : ℝ) := by
  let d : ℝ := ∏ p ∈ R, (1-1/(p : ℝ))
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hd0 : 0 ≤ d := by
    apply prod_nonneg
    intro p hp
    have hpB : (B : ℝ) ≤ p := by exact_mod_cast hR p hp
    have hp0 : (0 : ℝ) < p := hB0.trans_le hpB
    have hb : (4 : ℝ) ≤ B := by exact_mod_cast hB
    exact sub_nonneg.mpr ((div_le_one hp0).mpr (by linarith))
  have hprod := joint_product_error R s (fun p hp => ⟨by have := hR p hp; omega, hsB.trans (hR p hp)⟩)
  have hsq := reciprocal_square_sum_le R B (by omega) hR hsum
  have hpowers := prod_difference_le_sum (range s) (fun _ => d) (fun _ => (63/64 : ℝ))
    (fun _ _ => hd0) (fun _ _ => hhi) (fun _ _ => by norm_num)
  simp only [prod_const, card_range, sum_const, nsmul_eq_mul] at hpowers
  have hu : d^s - ∏ p ∈ R, (1-(s : ℝ)/p) ≤ (s : ℝ)^2/(B : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hsq (sq_nonneg (s : ℝ))
    dsimp only [d]
    exact hprod.2.trans (by simpa only [mul_one_div] using hh)
  have hn : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hb := mul_le_mul_of_nonneg_left (show (63/64 : ℝ)-d ≤ 1/(B : ℝ) by linarith) hn
  change 0 ≤ d^s - ∏ p ∈ R, (1-(s : ℝ)/p) ∧ _ at hprod
  constructor
  · linarith [hprod.1, hpowers.1]
  · rw [add_div]
    simp only [mul_one_div] at hb
    linarith [hpowers.2]

/-- Uniform error for all interval lengths up to B. -/
theorem covered_laplace_error (P R : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (B m : ℕ) (hB : 4 ≤ B) (hmB : m ≤ B) (hdis : Disjoint P R)
    (hR : ∀ p ∈ R, B ≤ p)
    (hlo : (63/64 : ℝ)-1/(B : ℝ) ≤ ∏ p ∈ R, (1-1/(p : ℝ)))
    (hhi : (∏ p ∈ R, (1-1/(p : ℝ))) ≤ (63/64 : ℝ))
    (hsum : (∑ p ∈ R, 1/(p : ℝ)) ≤ 1) :
    |coveredFraction (P ∪ R) m - countLaplace P (log 64) m| ≤
      (2 : ℝ)^m * ((m : ℝ)^2+m)/(B : ℝ) := by
  classical
  rw [covered_expansion, laplace_expansion_64, ← sum_sub_distrib]
  have hterm (A : Finset ℕ) (hA : A ∈ (range m).powerset) :
      |(-1 : ℝ)^A.card * joint (P ∪ R) A -
        (-1 : ℝ)^A.card * (63/64 : ℝ)^A.card * joint P A| ≤
          ((m : ℝ)^2+m)/(B : ℝ) := by
    have hAsub : A ⊆ range m := mem_powerset.mp hA
    have hAm : A.card ≤ m := (card_le_card hAsub).trans_eq (card_range _)
    have he := joint_union_large P R A hdis (fun p hp =>
      ⟨by have := hR p hp; omega, hAsub.trans (range_mono (hmB.trans (hR p hp)))⟩)
    have hh := joint_product_target_error R B A.card hB (hAm.trans hmB) hR hlo hhi hsum
    rw [he]
    have heq : (-1 : ℝ)^A.card * (joint P A * ∏ p ∈ R, (1-(A.card : ℝ)/p)) -
        (-1 : ℝ)^A.card * (63/64 : ℝ)^A.card * joint P A =
        -((-1 : ℝ)^A.card * joint P A *
          ((63/64 : ℝ)^A.card - ∏ p ∈ R, (1-(A.card : ℝ)/p))) := by ring
    rw [heq, abs_neg, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (joint_nonneg P A), abs_of_nonneg hh.1]
    have hu := mul_le_mul_of_nonneg_right (joint_le_one P A hP) hh.1
    have hcast : (A.card : ℝ) ≤ m := by exact_mod_cast hAm
    have hn : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
    have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
    calc
      _ ≤ (63/64 : ℝ)^A.card - ∏ p ∈ R, (1-(A.card : ℝ)/p) := by simpa only [one_mul] using hu
      _ ≤ ((A.card : ℝ)^2+A.card)/(B : ℝ) := hh.2
      _ ≤ ((m : ℝ)^2+m)/(B : ℝ) := div_le_div_of_nonneg_right (by nlinarith) hB0.le
  calc
    _ ≤ ∑ A ∈ (range m).powerset,
        |(-1 : ℝ)^A.card * joint (P ∪ R) A - (-1 : ℝ)^A.card * (63/64 : ℝ)^A.card * joint P A| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _A ∈ (range m).powerset, ((m : ℝ)^2+m)/(B : ℝ) := sum_le_sum hterm
    _ = _ := by simp [card_powerset, card_range]; ring

/-- One finite set of added primes approximates all the specified interval
lengths at once. The chosen primes are genuine, distinct, and disjoint from P. -/
theorem exists_padding_approx (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (M : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ R : Finset ℕ, Disjoint P R ∧ (∀ p ∈ R, p.Prime ∧ M ≤ p) ∧
      ∀ m ≤ M, |coveredFraction (P ∪ R) m - countLaplace P (log 64) m| < η := by
  classical
  let K : ℝ := (2 : ℝ)^M * ((M : ℝ)^2+M)
  obtain ⟨b,hb⟩ := exists_nat_gt (K/η)
  let B : ℕ := max 4 (max M (max (P.sup id + 1) b))
  have hB4 : 4 ≤ B := le_max_left _ _
  have hMB : M ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hsB : P.sup id + 1 ≤ B :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hbB : b ≤ B :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hKB : K < η*(B : ℝ) := by
    have hbB' : (b : ℝ) ≤ B := by exact_mod_cast hbB
    have hh := (div_lt_iff₀ hη).mp hb
    nlinarith
  obtain ⟨R,hR,hlo,hhi,hsum⟩ := exists_dilution_primes B hB4
  have hdis : Disjoint P R := by
    apply disjoint_left.mpr
    intro p hpP hpR
    have hp : p ≤ P.sup id := le_sup (f := id) hpP
    have hpB := (hR p hpR).2
    omega
  refine ⟨R,hdis,fun p hp => ⟨(hR p hp).1,hMB.trans (hR p hp).2⟩,?_⟩
  intro m hm
  have he := covered_laplace_error P R hP B m hB4 (hm.trans hMB) hdis
    (fun p hp => (hR p hp).2) hlo hhi hsum
  have hmn : (m : ℝ) ≤ M := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hpow : (2 : ℝ)^m ≤ 2^M := pow_le_pow_right₀ (by norm_num) hm
  have hK : (2 : ℝ)^m * ((m : ℝ)^2+m) ≤ K :=
    mul_le_mul hpow (by nlinarith) (by positivity) (by positivity)
  exact he.trans_lt ((div_le_div_of_nonneg_right hK hB0.le).trans_lt
    ((div_lt_iff₀ hB0).mpr (by nlinarith)))

#print axioms covered_laplace_error
#print axioms exists_padding_approx
end Erdos970.GapAverages.FiniteThinning
