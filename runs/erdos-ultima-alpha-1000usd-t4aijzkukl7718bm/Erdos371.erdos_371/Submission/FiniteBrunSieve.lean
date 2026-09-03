import FormalConjecturesUtil

/-! Finite Bonferroni inequalities with an explicit elementary-symmetric
remainder, and their use as a finite upper-bound sieve. -/

namespace Erdos371
namespace FiniteSieve

open Finset

variable {ι α : Type*}

noncomputable def elementarySum (S : Finset ι) (g : ι → ℝ) (m : ℕ) : ℝ :=
  ∑ T ∈ S.powersetCard m, ∏ i ∈ T, g i

noncomputable def truncation (S : Finset ι) (g : ι → ℝ) (m : ℕ) : ℝ :=
  ∑ T ∈ S.powerset, if T.card ≤ m then (-1 : ℝ)^T.card * ∏ i ∈ T, g i else 0

lemma elementarySum_eq_powerset (S : Finset ι) (g : ι → ℝ) (m : ℕ) :
    elementarySum S g m = ∑ T ∈ S.powerset, if T.card = m then ∏ i ∈ T, g i else 0 := by
  classical
  simp only [elementarySum, powersetCard_eq_filter, sum_filter]

@[simp] lemma elementarySum_zero (S : Finset ι) (g : ι → ℝ) :
    elementarySum S g 0 = 1 := by
  simp [elementarySum]

@[simp] lemma elementarySum_empty (g : ι → ℝ) (m : ℕ) :
    elementarySum ∅ g (m+1) = 0 := by
  have h : (∅ : Finset ι).powersetCard (m+1) = ∅ :=
    powersetCard_eq_empty.mpr (by simp)
  simp [elementarySum, h]

@[simp] lemma truncation_empty (g : ι → ℝ) (m : ℕ) :
    truncation ∅ g m = 1 := by
  simp [truncation]

lemma elementarySum_nonneg (S : Finset ι) (g : ι → ℝ) (m : ℕ)
    (hg : ∀ i ∈ S, 0 ≤ g i) : 0 ≤ elementarySum S g m := by
  apply sum_nonneg
  intro T hT
  exact prod_nonneg fun i hi => hg i ((mem_powersetCard.mp hT).1 hi)

lemma elementarySum_insert [DecidableEq ι] (S : Finset ι) (g : ι → ℝ)
    (a : ι) (ha : a ∉ S) (m : ℕ) :
    elementarySum (insert a S) g (m+1) =
      elementarySum S g (m+1) + g a * elementarySum S g m := by
  simp only [elementarySum_eq_powerset, sum_powerset_insert ha]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro T hT
  have haT : a ∉ T := notMem_mono (mem_powerset.mp hT) ha
  simp [card_insert_of_notMem haT, prod_insert haT, mul_ite]

lemma truncation_insert [DecidableEq ι] (S : Finset ι) (g : ι → ℝ)
    (a : ι) (ha : a ∉ S) (m : ℕ) :
    truncation (insert a S) g m = (1-g a) * truncation S g m +
      g a * (-1 : ℝ)^m * elementarySum S g m := by
  simp only [truncation, elementarySum_eq_powerset, sum_powerset_insert ha,
    mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro T hT
  have haT : a ∉ T := notMem_mono (mem_powerset.mp hT) ha
  simp only [card_insert_of_notMem haT, prod_insert haT]
  rcases lt_trichotomy T.card m with h | h | h
  · simp only [if_pos h.le, if_pos (by omega : T.card+1 ≤ m), if_neg h.ne, mul_zero,
      add_zero, pow_succ]
    ring
  · simp only [h, le_refl, if_true, if_false, Nat.not_succ_le_self, add_zero]
    ring
  · simp only [if_neg (by omega : ¬T.card ≤ m), if_neg (by omega : ¬T.card+1 ≤ m),
      if_neg h.ne', mul_zero, add_zero]

/-- Both Bonferroni bounds, with the first omitted elementary symmetric sum
as an error bound. -/
theorem signed_remainder_bounds (S : Finset ι) (g : ι → ℝ) (m : ℕ)
    (hg : ∀ i ∈ S, 0 ≤ g i ∧ g i ≤ 1) :
    0 ≤ (-1 : ℝ)^m * (truncation S g m - ∏ i ∈ S, (1-g i)) ∧
      (-1 : ℝ)^m * (truncation S g m - ∏ i ∈ S, (1-g i)) ≤
        elementarySum S g (m+1) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have ha0 := (hg a (mem_insert_self a S)).1
    have ha1 := (hg a (mem_insert_self a S)).2
    have hgS : ∀ i ∈ S, 0 ≤ g i ∧ g i ≤ 1 := fun i hi => hg i (mem_insert_of_mem hi)
    obtain ⟨ih0, ih1⟩ := ih hgS
    have e0 := elementarySum_nonneg S g m (fun i hi => (hgS i hi).1)
    have e1 := elementarySum_nonneg S g (m+1) (fun i hi => (hgS i hi).1)
    have he : (-1 : ℝ)^m *
        (truncation (insert a S) g m - ∏ i ∈ insert a S, (1-g i)) =
        (1-g a) * ((-1 : ℝ)^m * (truncation S g m - ∏ i ∈ S, (1-g i))) +
          g a * elementarySum S g m := by
      rw [truncation_insert S g a ha m, prod_insert ha]
      have hs : ((-1 : ℝ)^m)^2 = 1 := by rw [← pow_mul, mul_comm m 2, pow_mul]; norm_num
      calc
        _ = (1-g a) * ((-1 : ℝ)^m * (truncation S g m - ∏ i ∈ S, (1-g i))) +
          g a * ((-1 : ℝ)^m)^2 * elementarySum S g m := by ring
        _ = _ := by rw [hs]; ring
    rw [he, elementarySum_insert S g a ha m]
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr ha1) ih0) (mul_nonneg ha0 e0)
    · have h := mul_le_mul_of_nonneg_left ih1 (sub_nonneg.mpr ha1)
      nlinarith [mul_nonneg ha0 e1]

lemma even_truncation_bounds (S : Finset ι) (g : ι → ℝ) (k : ℕ)
    (hg : ∀ i ∈ S, 0 ≤ g i ∧ g i ≤ 1) :
    (∏ i ∈ S, (1-g i)) ≤ truncation S g (2*k) ∧
      truncation S g (2*k) ≤ (∏ i ∈ S, (1-g i)) + elementarySum S g (2*k+1) := by
  have h := signed_remainder_bounds S g (2*k) hg
  have hp : (-1 : ℝ)^(2*k) = 1 := by rw [pow_mul]; norm_num
  rw [hp, one_mul] at h
  constructor <;> linarith [h.1, h.2]

/-- A coarse but uniform bound for elementary symmetric sums. -/
lemma factorial_mul_elementarySum_le (S : Finset ι) (g : ι → ℝ)
    (hg : ∀ i ∈ S, 0 ≤ g i) (m : ℕ) :
    (m.factorial : ℝ) * elementarySum S g m ≤ (∑ i ∈ S, g i)^m := by
  classical
  induction S using Finset.induction_on generalizing m with
  | empty => cases m <;> simp
  | @insert a S ha ih =>
    have ha0 := hg a (mem_insert_self a S)
    have hgS : ∀ i ∈ S, 0 ≤ g i := fun i hi => hg i (mem_insert_of_mem hi)
    cases m with
    | zero => simp
    | succ m =>
      have h1 := ih hgS (m+1)
      have h0 := ih hgS m
      have hS := sum_nonneg hgS
      have ht := pow_add_mul_le_add_pow hS
        (show 0 ≤ 2 * (∑ i ∈ S, g i) + g a by positivity) (m+1)
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at ht
      rw [elementarySum_insert S g a ha m, sum_insert ha]
      calc
        _ = ((m+1).factorial : ℝ) * elementarySum S g (m+1) +
            (m+1) * g a * ((m.factorial : ℝ) * elementarySum S g m) := by
          rw [Nat.factorial_succ]
          push_cast
          ring
        _ ≤ (∑ i ∈ S, g i)^(m+1) + (m+1) * g a * (∑ i ∈ S, g i)^m :=
          add_le_add h1 (mul_le_mul_of_nonneg_left h0 (by positivity))
        _ ≤ _ := by convert ht using 1 <;> ring

lemma elementarySum_le_pow_div_factorial (S : Finset ι) (g : ι → ℝ)
    (hg : ∀ i ∈ S, 0 ≤ g i) (m : ℕ) :
    elementarySum S g m ≤ (∑ i ∈ S, g i)^m / m.factorial := by
  apply (le_div_iff₀ (show (0 : ℝ) < m.factorial by exact_mod_cast Nat.factorial_pos m)).mpr
  simpa [mul_comm] using factorial_mul_elementarySum_le S g hg m

lemma even_truncation_le (S : Finset ι) (g : ι → ℝ) (k : ℕ)
    (hg : ∀ i ∈ S, 0 ≤ g i ∧ g i ≤ 1) :
    truncation S g (2*k) ≤ (∏ i ∈ S, (1-g i)) +
      (∑ i ∈ S, g i)^(2*k+1) / (2*k+1).factorial :=
  (even_truncation_bounds S g k hg).2.trans <|
    add_le_add le_rfl (elementarySum_le_pow_div_factorial S g (fun i hi => (hg i hi).1) _)

noncomputable def intersectionCount (A : Finset α) (E : ι → α → Prop) (T : Finset ι) : ℕ := by
  classical
  exact (A.filter fun a => ∀ i ∈ T, E i a).card

noncomputable def avoidanceCount (A : Finset α) (E : ι → α → Prop) (S : Finset ι) : ℕ := by
  classical
  exact (A.filter fun a => ∀ i ∈ S, ¬E i a).card

noncomputable def countTruncation (A : Finset α) (E : ι → α → Prop)
    (S : Finset ι) (m : ℕ) : ℝ :=
  ∑ T ∈ S.powerset, if T.card ≤ m then (-1 : ℝ)^T.card * intersectionCount A E T else 0

lemma avoidanceCount_le_countTruncation (A : Finset α) (E : ι → α → Prop)
    (S : Finset ι) (k : ℕ) :
    (avoidanceCount A E S : ℝ) ≤ countTruncation A E S (2*k) := by
  classical
  let g : α → ι → ℝ := fun a i => if E i a then 1 else 0
  have hg (a : α) (i : ι) : 0 ≤ g a i ∧ g a i ≤ 1 := by
    dsimp [g]; split_ifs <;> norm_num
  have hp (a : α) : (∏ i ∈ S, (1-g a i)) =
      if ∀ i ∈ S, ¬E i a then (1 : ℝ) else 0 := by
    have ht (i : ι) : 1-g a i = if ¬E i a then 1 else 0 := by
      dsimp [g]; split_ifs <;> norm_num
    simp only [ht, prod_boole]
  calc
    _ = ∑ a ∈ A, ∏ i ∈ S, (1-g a i) := by
      simp [hp, avoidanceCount]
    _ ≤ ∑ a ∈ A, truncation S (g a) (2*k) :=
      sum_le_sum fun a _ => (even_truncation_bounds S (g a) k (fun i _ => hg a i)).1
    _ = countTruncation A E S (2*k) := by
      simp only [truncation, countTruncation]
      rw [sum_comm]
      apply sum_congr rfl
      intro T hT
      by_cases h : T.card ≤ 2*k
      · simp only [if_pos h, ← mul_sum, g, prod_boole]
        congr 1
        simp [intersectionCount]
      · simp [h]

lemma countTruncation_le_main_error (A : Finset α) (E : ι → α → Prop)
    (S : Finset ι) (g : ι → ℝ) (m : ℕ) (X : ℝ) (R : Finset ι → ℝ)
    (hR : ∀ T ∈ S.powerset, T.card ≤ m →
      |(intersectionCount A E T : ℝ) - X * ∏ i ∈ T, g i| ≤ R T) :
    countTruncation A E S m ≤ X * truncation S g m +
      ∑ T ∈ S.powerset, if T.card ≤ m then R T else 0 := by
  classical
  simp only [countTruncation, truncation, mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro T hT
  by_cases hm : T.card ≤ m
  · simp only [if_pos hm]
    have hc : |(-1 : ℝ)^T.card| = 1 := by simp
    have h : (-1 : ℝ)^T.card * ((intersectionCount A E T : ℝ) - X * ∏ i ∈ T, g i) ≤ R T := by
      calc
        _ ≤ |(-1 : ℝ)^T.card * ((intersectionCount A E T : ℝ) - X * ∏ i ∈ T, g i)| := le_abs_self _
        _ = |(intersectionCount A E T : ℝ) - X * ∏ i ∈ T, g i| := by rw [abs_mul, hc, one_mul]
        _ ≤ _ := hR T hT hm
    nlinarith
  · simp [hm]

/-- A finite pure Brun upper-bound sieve. Only intersections up to degree
`2*k` need to be estimated. -/
theorem brun_upper_bound (A : Finset α) (E : ι → α → Prop)
    (S : Finset ι) (g : ι → ℝ) (k : ℕ) (X : ℝ) (R : Finset ι → ℝ)
    (hX : 0 ≤ X) (hg : ∀ i ∈ S, 0 ≤ g i ∧ g i ≤ 1)
    (hR : ∀ T ∈ S.powerset, T.card ≤ 2*k →
      |(intersectionCount A E T : ℝ) - X * ∏ i ∈ T, g i| ≤ R T) :
    (avoidanceCount A E S : ℝ) ≤
      X * ((∏ i ∈ S, (1-g i)) + (∑ i ∈ S, g i)^(2*k+1) / (2*k+1).factorial) +
      ∑ T ∈ S.powerset, if T.card ≤ 2*k then R T else 0 := by
  exact (avoidanceCount_le_countTruncation A E S k).trans <|
    (countTruncation_le_main_error A E S g (2*k) X R hR).trans <|
      add_le_add (mul_le_mul_of_nonneg_left (even_truncation_le S g k hg) hX) le_rfl

lemma complementary_product_le_exp (S : Finset ι) (g : ι → ℝ)
    (hg : ∀ i ∈ S, g i ≤ 1) :
    (∏ i ∈ S, (1-g i)) ≤ Real.exp (-(∑ i ∈ S, g i)) := by
  rw [← sum_neg_distrib, Real.exp_sum]
  apply prod_le_prod
  · intro i hi
    exact sub_nonneg.mpr (hg i hi)
  · intro i hi
    simpa only [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-g i)

lemma factorial_remainder_le_exp {H : ℝ} (hH : 0 ≤ H) (m : ℕ) :
    H^m / m.factorial ≤ Real.exp (2*H - m * Real.log 2) := by
  have h := Real.pow_div_factorial_le_exp (2*H) (show 0 ≤ 2*H by positivity) m
  have h2 : (0 : ℝ) < 2^m := by positivity
  have he : Real.exp (2*H - m*Real.log 2) = Real.exp (2*H) / 2^m := by
    rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [he]
  apply (le_div_iff₀ h2).mpr
  convert h using 1; ring

/-- Exponential form of the finite sieve, when the truncation degree is large
compared with the sum of the local densities. -/
theorem brun_upper_bound_exp (A : Finset α) (E : ι → α → Prop)
    (S : Finset ι) (g : ι → ℝ) (k : ℕ) (X : ℝ) (R : Finset ι → ℝ)
    (hX : 0 ≤ X) (hg : ∀ i ∈ S, 0 ≤ g i ∧ g i ≤ 1)
    (hk : 3 * (∑ i ∈ S, g i) ≤ (2*k+1 : ℕ) * Real.log 2)
    (hR : ∀ T ∈ S.powerset, T.card ≤ 2*k →
      |(intersectionCount A E T : ℝ) - X * ∏ i ∈ T, g i| ≤ R T) :
    (avoidanceCount A E S : ℝ) ≤
      2 * X * Real.exp (-(∑ i ∈ S, g i)) +
      ∑ T ∈ S.powerset, if T.card ≤ 2*k then R T else 0 := by
  have h0 := complementary_product_le_exp S g (fun i hi => (hg i hi).2)
  have h1 := factorial_remainder_le_exp (sum_nonneg (fun i hi => (hg i hi).1)) (2*k+1)
  have h2 : Real.exp (2 * (∑ i ∈ S, g i) - (2*k+1 : ℕ) * Real.log 2) ≤
      Real.exp (-(∑ i ∈ S, g i)) := Real.exp_le_exp.mpr (by linarith)
  have hb := brun_upper_bound A E S g k X R hX hg hR
  have ht := mul_le_mul_of_nonneg_left (add_le_add h0 (h1.trans h2)) hX
  nlinarith

lemma truncated_subset_product_sum (S : Finset ι) (w : ι → ℝ) (m : ℕ) :
    (∑ T ∈ S.powerset, if T.card ≤ m then ∏ i ∈ T, w i else 0) =
      ∑ j ∈ range (m+1), elementarySum S w j := by
  classical
  calc
    _ = ∑ T ∈ S.powerset, ∑ j ∈ range (m+1),
        if T.card = j then ∏ i ∈ T, w i else 0 := by
      apply sum_congr rfl
      intro T hT
      simp
    _ = _ := by
      rw [sum_comm]
      exact sum_congr rfl fun j _ => (elementarySum_eq_powerset S w j).symm

/-- A coarse bound on the total remainder when the error for a subset is
at most the product of its local moduli. -/
lemma truncated_subset_product_sum_le (S : Finset ι) (w : ι → ℝ) (m : ℕ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (Z : ℝ) (hZ : 1 ≤ Z) (hsum : (∑ i ∈ S, w i) ≤ Z) :
    (∑ T ∈ S.powerset, if T.card ≤ m then ∏ i ∈ T, w i else 0) ≤
      (m+1) * Z^m := by
  rw [truncated_subset_product_sum]
  calc
    _ ≤ ∑ j ∈ range (m+1), Z^m := by
      apply sum_le_sum
      intro j hj
      have hjm : j ≤ m := by simpa only [mem_range, Nat.lt_succ_iff] using hj
      calc
        _ ≤ (∑ i ∈ S, w i)^j / j.factorial := elementarySum_le_pow_div_factorial S w hw j
        _ ≤ (∑ i ∈ S, w i)^j := div_le_self (pow_nonneg (sum_nonneg hw) _)
          (by exact_mod_cast (show 1 ≤ j.factorial from Nat.factorial_pos j))
        _ ≤ Z^j := pow_le_pow_left₀ (sum_nonneg hw) hsum j
        _ ≤ Z^m := pow_le_pow_right₀ hZ hjm
    _ = _ := by simp

#print axioms brun_upper_bound
#print axioms brun_upper_bound_exp

end FiniteSieve
end Erdos371
