import Submission.FiniteExactDilationBias
import Submission.QuantizedComparisonApproximation

/-! Exact fixed-multiplier invariance alone permits a biased ORDER comparison
on just three labels. This is an endpoint-dependent auxiliary family and not
the arithmetic max-prime sequence or a disproof of its density conjecture. -/
namespace Erdos371.ExactMultiplierChirpObstruction
open Finset Filter
open scoped Topology

variable {A : Type*} [DecidableEq A]

def pairOrder (a b x : A) : Fin 3 := if x = a then 0 else if x = b then 1 else 2

lemma pairOrder_skew_difference (a b x y : A) :
    orderSkew (pairOrder a b x) (pairOrder a b y)-
      orderSkew (pairOrder b a x) (pairOrder b a y) =
        2*((if x=a ∧ y=b then (1 : ℝ) else 0)-(if x=b ∧ y=a then 1 else 0)) := by
  by_cases hab : a = b
  · subst b; simp
  by_cases hxa : x = a <;> by_cases hxb : x = b <;>
    by_cases hya : y = a <;> by_cases hyb : y = b <;>
    simp_all [pairOrder,orderSkew] <;> norm_num

lemma skew_expansion_pairOrders [Fintype A] (C : A → A → ℝ)
    (hC : ∀ a b, C b a = -C a b) (x y : A) :
    4*C x y = ∑ a, ∑ b, C a b *
      (orderSkew (pairOrder a b x) (pairOrder a b y)-
        orderSkew (pairOrder b a x) (pairOrder b a y)) := by
  simp_rw [pairOrder_skew_difference]
  have he (a b : A) : C a b *
      (2*((if x=a ∧ y=b then (1 : ℝ) else 0)-(if x=b ∧ y=a then 1 else 0))) =
      (if x=a ∧ y=b then 2*C a b else 0)-(if x=b ∧ y=a then 2*C a b else 0) := by
    split_ifs <;> ring
  simp_rw [he,sum_sub_distrib]
  simp only [ite_and, sum_ite_irrel, sum_const_zero, sum_ite_eq, mem_univ, if_true]
  rw [hC]
  ring

noncomputable def orderedMean (L : ℕ → Fin 3) (N : ℕ) : ℝ :=
  (∑ n ∈ Icc 1 N, orderSkew (L n) (L (n+1)))/N

lemma skew_mean_expansion_pairOrders [Fintype A] (L : ℕ → A) (C : A → A → ℝ)
    (hC : ∀ a b, C b a = -C a b) (N : ℕ) :
    4*((∑ n ∈ Icc 1 N, C (L n) (L (n+1)))/N) =
      ∑ a, ∑ b, C a b * (orderedMean (pairOrder a b ∘ L) N-orderedMean (pairOrder b a ∘ L) N) := by
  unfold orderedMean
  simp only [← sub_div,← sum_sub_distrib,← mul_div_assoc,← sum_div]
  congr 1
  rw [mul_sum]
  simp_rw [skew_expansion_pairOrders C hC]
  simp only [mul_sum]
  simp_rw [sum_comm (s := (univ : Finset A)) (t := Icc 1 N)]
  rfl

/-- Some three-label projection detects any nonzero antisymmetric bias.
The constant need not depend on the sample size or on the label sequence. -/
lemma exists_biased_pairOrder [Fintype A] (L : ℕ → A) (C : A → A → ℝ)
    (hC : ∀ a b, C b a = -C a b) (hCb : ∀ a b, |C a b| ≤ 1)
    (N : ℕ) (β : ℝ) (hβ : 0 < β)
    (hb : β ≤ (∑ n ∈ Icc 1 N, C (L n) (L (n+1)))/N) :
    ∃ a b : A, β/((Fintype.card A : ℝ)^2+1) ≤ |orderedMean (pairOrder a b ∘ L) N| := by
  let δ := β/((Fintype.card A : ℝ)^2+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  by_contra! h
  have hsum : (∑ a, ∑ b, C a b *
      (orderedMean (pairOrder a b ∘ L) N-orderedMean (pairOrder b a ∘ L) N)) ≤
        2*δ*(Fintype.card A : ℝ)^2 := by
    calc
      _ ≤ ∑ a : A, ∑ b : A, 2*δ := by
        apply sum_le_sum
        intro a _
        apply sum_le_sum
        intro b _
        apply (le_abs_self _).trans
        rw [abs_mul]
        have hd : |orderedMean (pairOrder a b ∘ L) N-orderedMean (pairOrder b a ∘ L) N| ≤ 2*δ := by
          have ht := abs_sub (orderedMean (pairOrder a b ∘ L) N) (orderedMean (pairOrder b a ∘ L) N)
          have hab : |orderedMean (pairOrder a b ∘ L) N| < δ := h a b
          have hba : |orderedMean (pairOrder b a ∘ L) N| < δ := h b a
          linarith
        exact (mul_le_mul (hCb a b) hd (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
      _ = _ := by simp; ring
  rw [← skew_mean_expansion_pairOrders L C hC N] at hsum
  have he : δ*((Fintype.card A : ℝ)^2+1) = β := by dsimp [δ]; field_simp
  nlinarith

def reverseThree (a : Fin 3) : Fin 3 := ⟨2-a.val,by omega⟩

lemma orderSkew_reverseThree (a b : Fin 3) :
    orderSkew (reverseThree a) (reverseThree b) = -orderSkew a b := by
  fin_cases a <;> fin_cases b <;> norm_num [reverseThree,orderSkew,Fin.lt_def]

lemma orderedMean_reverseThree (L : ℕ → Fin 3) (N : ℕ) :
    orderedMean (reverseThree ∘ L) N = -orderedMean L N := by
  simp only [orderedMean,Function.comp_apply,orderSkew_reverseThree,sum_neg_distrib,neg_div]

lemma exists_negative_three_label_projection [Fintype A] (L : ℕ → A) (C : A → A → ℝ)
    (hC : ∀ a b, C b a = -C a b) (hCb : ∀ a b, |C a b| ≤ 1)
    (N : ℕ) (β : ℝ) (hβ : 0 < β)
    (hb : β ≤ (∑ n ∈ Icc 1 N, C (L n) (L (n+1)))/N) :
    ∃ T : A → Fin 3, orderedMean (T ∘ L) N ≤ -β/((Fintype.card A : ℝ)^2+1) := by
  obtain ⟨a,b,hab⟩ := exists_biased_pairOrder L C hC hCb N β hβ hb
  rcases le_total (orderedMean (pairOrder a b ∘ L) N) 0 with h | h
  · refine ⟨pairOrder a b,?_⟩
    rw [abs_of_nonpos h] at hab
    rw [neg_div]
    linarith
  · refine ⟨reverseThree ∘ pairOrder a b,?_⟩
    rw [Function.comp_assoc,orderedMean_reverseThree]
    rw [abs_of_nonneg h] at hab
    rw [neg_div]
    linarith

/-- A fixed THREE-label family with exact eventual invariance under each
fixed multiplier nevertheless has a uniformly negative adjacent order bias
along its natural endpoints. No max-multiplicative identity is asserted. -/
theorem exists_three_label_exact_dilation_order_bias :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ → ℕ, ∃ L : ℕ → ℕ → Fin 3,
      Tendsto N atTop atTop ∧
      (∀ j k, 0 < k → k ≤ j → ∀ n, L j (k*n) = L j n) ∧
      ∀ j, orderedMean (L j) (N j) ≤ -δ := by
  obtain ⟨Q,N,L,C,hN,hC,hCb,hstable,hbias⟩ := exists_finite_exact_dilation_stable_skew_bias
  have hex (j : ℕ) : ∃ T : Fin Q → Fin 3,
      orderedMean (T ∘ L j) (N j) ≤ -(1/240 : ℝ)/((Q : ℝ)^2+1) := by
    simpa only [Fintype.card_fin] using exists_negative_three_label_projection (L j) C hC hCb
      (N j) (1/240) (by norm_num) (hbias j)
  choose T hT using hex
  refine ⟨(1/240 : ℝ)/((Q : ℝ)^2+1),by positivity,N,fun j => T j ∘ L j,hN,?_,?_⟩
  · intro j k hk hkj n
    dsimp only [Function.comp_apply]
    rw [hstable j k hk hkj n]
  · intro j
    simpa only [neg_div] using hT j

lemma rising_fraction_le_orderedMean (L : ℕ → Fin 3) (N : ℕ) (hN : 0 < N) :
    (((Icc 1 N).filter fun n => L n < L (n+1)).card : ℝ)/N ≤ (1+orderedMean L N)/2 := by
  have hc : (∑ n ∈ Icc 1 N, if L n < L (n+1) then (1 : ℝ) else 0) =
      ((Icc 1 N).filter fun n => L n < L (n+1)).card := by simp
  have hp (a b : Fin 3) : 2*(if a<b then (1 : ℝ) else 0) ≤ 1+orderSkew a b := by
    unfold orderSkew
    split_ifs <;> norm_num
  have hs := sum_le_sum (s := Icc 1 N) (fun n _ => hp (L n) (L (n+1)))
  rw [← mul_sum,hc,sum_add_distrib] at hs
  simp only [sum_const,Nat.card_Icc,nsmul_eq_mul,mul_one,Nat.add_sub_cancel] at hs
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hd := (div_le_div_iff_of_pos_right hNr).mpr hs
  unfold orderedMean
  rw [add_div,div_self hNr.ne',mul_div_assoc] at hd
  nlinarith

/-- Even for an ordered three-label comparison, exact eventual invariance
under every fixed multiplier does not justify a uniform density-half claim
for endpoint-dependent label families. This is NOT the negation of Erdős 371. -/
theorem exists_three_label_exact_dilation_rise_deficit :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ → ℕ, ∃ L : ℕ → ℕ → Fin 3,
      Tendsto N atTop atTop ∧
      (∀ j k, 0 < k → k ≤ j → ∀ n, L j (k*n) = L j n) ∧
      ∀ j, (((Icc 1 (N j)).filter fun n => L j n < L j (n+1)).card : ℝ)/(N j) ≤ 1/2-δ := by
  obtain ⟨δ,hδ,N,L,hN,hstable,hbias⟩ := exists_three_label_exact_dilation_order_bias
  refine ⟨δ/2,by positivity,N,L,hN,hstable,?_⟩
  intro j
  have hNj : 0 < N j := by
    by_contra h
    have hz : N j = 0 := by omega
    have hb := hbias j
    norm_num [orderedMean,hz] at hb
    linarith
  have hb := rising_fraction_le_orderedMean (L j) (N j) hNj
  linarith [hbias j]

#print axioms exists_three_label_exact_dilation_order_bias
#print axioms exists_three_label_exact_dilation_rise_deficit
end Erdos371.ExactMultiplierChirpObstruction
