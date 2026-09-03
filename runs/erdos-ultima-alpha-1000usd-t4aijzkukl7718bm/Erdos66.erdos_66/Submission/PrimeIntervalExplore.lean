import Submission.FiniteFieldExplore
import Submission.SignEnergyExplore
import Submission.IntervalSignExplore

/-! Prime-field parameter intervals with small signed additive fibers.
These are finite constructions, not witnesses to Erdős Problem 66. -/
namespace Erdos66PrimeInterval
open Polynomial Erdos66SignEnergy Erdos66FiniteField Erdos66IntervalSign

lemma polynomial_coeff_convolution {P : ℤ[X]} {h : ℕ} (hP : SupportedBelow P h) (k : ℕ) :
    (P ^ 2).coeff k = ∑ i ∈ Finset.range h, ∑ j ∈ Finset.range h,
      if i + j = k then P.coeff i * P.coeff j else 0 := by
  have he : P = ∑ i ∈ Finset.range h, monomial i (P.coeff i) := by
    ext i
    rw [finset_sum_coeff]
    simp only [coeff_monomial, Finset.sum_ite_eq']
    by_cases hi : i < h
    · simp [hi]
    · simp [hi, hP i (by omega)]
  calc
    (P ^ 2).coeff k =
        ((∑ i ∈ Finset.range h, monomial i (P.coeff i)) *
          (∑ j ∈ Finset.range h, monomial j (P.coeff j))).coeff k := by
      rw [← he, pow_two]
    _ = _ := by
      simp only [Finset.sum_mul, Finset.mul_sum, finset_sum_coeff,
        monomial_mul_monomial, coeff_monomial]
      exact Finset.sum_comm

lemma pushed_convolution {P : ℤ[X]} {h : ℕ} (hP : SupportedBelow P h)
    (p a : ℕ) [NeZero p] (w : ZMod p) :
    (∑ i ∈ Finset.range h, ∑ j ∈ Finset.range h,
      if ((a + i : ℕ) : ZMod p) + ((a + j : ℕ) : ZMod p) = w
        then P.coeff i * P.coeff j else 0) =
      ∑ k ∈ Finset.range (2 * h), if ((2 * a + k : ℕ) : ZMod p) = w
        then (P ^ 2).coeff k else 0 := by
  simp_rw [polynomial_coeff_convolution hP]
  have hdist (k : ℕ) :
      (if ((2 * a + k : ℕ) : ZMod p) = w then
        ∑ i ∈ Finset.range h, ∑ j ∈ Finset.range h,
          (if i + j = k then P.coeff i * P.coeff j else 0) else 0) =
      ∑ i ∈ Finset.range h, ∑ j ∈ Finset.range h,
        if i + j = k then
          (if ((2 * a + k : ℕ) : ZMod p) = w then P.coeff i * P.coeff j else 0) else 0 := by
    split_ifs with hw
    · simp only [if_pos hw]
    · simp only [if_neg hw, ite_self, Finset.sum_const_zero]
  simp_rw [hdist]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_ite_eq]
  have hk : i + j ∈ Finset.range (2 * h) := by
    simp only [Finset.mem_range] at hi hj ⊢
    omega
  rw [if_pos hk]
  congr 1
  congr 1
  push_cast
  ring

lemma sum_abs_push_le {α β : Type*} [Fintype β] [DecidableEq β]
    (S : Finset α) (f : α → β) (c : α → ℤ) :
    (∑ b : β, |∑ i ∈ S, if f i = b then c i else 0|) ≤ ∑ i ∈ S, |c i| := by
  calc
    _ ≤ ∑ b : β, ∑ i ∈ S, |if f i = b then c i else 0| :=
      Finset.sum_le_sum (fun _ _ ↦ Finset.abs_sum_le_sum_abs _ _)
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [apply_ite abs, abs_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

noncomputable def parameterInterval (p a h : ℕ) : Finset (ZMod p) :=
  (Finset.range h).image (fun i ↦ ((a + i : ℕ) : ZMod p))

lemma interval_injOn {p a h : ℕ} [NeZero p] (hp : a + h < p) :
    Set.InjOn (fun i : ℕ ↦ ((a + i : ℕ) : ZMod p)) (Finset.range h) := by
  intro i hi j hj hij
  have hi' := Finset.mem_range.mp hi
  have hj' := Finset.mem_range.mp hj
  have hv := congrArg ZMod.val hij
  rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv
  omega

lemma parameterInterval_card {p a h : ℕ} [NeZero p] (hp : a + h < p) :
    (parameterInterval p a h).card = h := by
  rw [parameterInterval, Finset.card_image_of_injOn (interval_injOn hp), Finset.card_range]

lemma interval_character_fibers {p a h : ℕ} [Fact p.Prime]
    (hp : a + h < p) {P : ℤ[X]} (hP : SupportedBelow P h)
    (hchar : ∀ i < h, quadraticChar (ZMod p) ((a + i : ℕ) : ZMod p) = P.coeff i) :
    (∑ w : ZMod p, |charFiber (parameterInterval p a h) w|) ≤
      ∑ k ∈ Finset.range (2 * h), |(P ^ 2).coeff k| := by
  have hF (w : ZMod p) : charFiber (parameterInterval p a h) w =
      ∑ k ∈ Finset.range (2 * h), if ((2 * a + k : ℕ) : ZMod p) = w
        then (P ^ 2).coeff k else 0 := by
    unfold charFiber parameterInterval
    rw [Finset.sum_image (interval_injOn hp)]
    simp_rw [Finset.sum_image (interval_injOn hp)]
    calc
      _ = ∑ i ∈ Finset.range h, ∑ j ∈ Finset.range h,
          if ((a + i : ℕ) : ZMod p) + ((a + j : ℕ) : ZMod p) = w
            then P.coeff i * P.coeff j else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [hchar i (Finset.mem_range.mp hi), hchar j (Finset.mem_range.mp hj)]
      _ = _ := pushed_convolution hP p a w
  simp_rw [hF]
  exact sum_abs_push_le _ _ _

/-- Prime-field parameter sets with an arbitrarily small relative signed-fiber
error as their cardinality tends to infinity. The prime can be arbitrarily large. -/
theorem exists_prime_parameters (h N : ℕ) :
    ∃ p : ℕ, ∃ hp : p.Prime,
      letI : Fact p.Prime := ⟨hp⟩
      N < p ∧ p % 8 = 1 ∧
      ∃ U : Finset (ZMod p), U.card = h ∧
        (∀ u ∈ U, u ≠ 0) ∧ (∀ u ∈ U, ∀ v ∈ U, u + v ≠ 0) ∧
        ∃ E : ℤ, 0 ≤ E ∧ E ^ 2 ≤ 4 * (h : ℤ) ^ 3 ∧
          (∑ w : ZMod p, |charFiber U w|) ≤ E := by
  obtain ⟨P, hP, hsign, hE⟩ := exists_sign_polynomial_l1 h
  obtain ⟨a, ha, hall⟩ := exists_interval_all_signs h
  obtain ⟨p, hp, hpN, hp8, hchars⟩ := hall (fun i ↦ P.coeff i.val)
    (fun i ↦ hsign i.val i.isLt) (max N (2 * (a + h)))
  letI : Fact p.Prime := ⟨hp⟩
  have hbig : 2 * (a + h) < p := lt_of_le_of_lt (le_max_right _ _) hpN
  have hsmall : a + h < p := by omega
  refine ⟨p, hp, lt_of_le_of_lt (le_max_left _ _) hpN, hp8,
    parameterInterval p a h, parameterInterval_card hsmall, ?_, ?_,
    ∑ k ∈ Finset.range (2 * h), |(P ^ 2).coeff k|,
    Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _), hE, ?_⟩
  · intro u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    have hi' := Finset.mem_range.mp hi
    intro hz
    have hv := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hv
    omega
  · intro u hu v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    intro hz
    rw [← Nat.cast_add] at hz
    have hv := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hv
    omega
  · apply interval_character_fibers hsmall hP
    intro i hi
    simpa only [legendreSym, Int.cast_natCast] using hchars ⟨i, hi⟩

end Erdos66PrimeInterval
