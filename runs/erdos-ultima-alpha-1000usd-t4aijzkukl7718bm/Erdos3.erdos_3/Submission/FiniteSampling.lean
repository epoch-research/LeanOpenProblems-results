import FormalConjecturesUtil

/-! Exact finite sampling estimates for an almost-periodicity approach.
These are auxiliary analytic results, not a proof of Erdős 3. -/
namespace Erdos3FiniteSampling

open Finset
open scoped BigOperators Classical
set_option maxHeartbeats 1000000

lemma expect_pi_prod {I A : Type*} [Fintype I] [Fintype A]
    (f : I → A → ℝ) :
    (𝔼 v : I → A, ∏ i, f i (v i)) = ∏ i, 𝔼 a, f i a := by
  classical
  simp only [Fintype.expect_eq_sum_div_card, Fintype.card_pi, ← Fintype.prod_sum,
    Nat.cast_prod, prod_div_distrib]

lemma expect_pi_apply {I A : Type*} [Fintype I] [Fintype A] [Nonempty A]
    (i : I) (f : A → ℝ) : (𝔼 v : I → A, f (v i)) = 𝔼 a, f a := by
  classical
  have h := expect_pi_prod (I := I) (A := A) (fun j a ↦ if j = i then f a else 1)
  have ht (j : I) : (𝔼 a, if j = i then f a else (1 : ℝ)) =
      if j = i then 𝔼 a, f a else 1 := by
    by_cases hj : j = i <;> simp [hj]
  simpa only [prod_ite_eq', mem_univ, if_true, ht] using h

lemma expect_pi_apply_mul {I A : Type*} [Fintype I] [Fintype A] [Nonempty A]
    {i j : I} (hij : i ≠ j) (f g : A → ℝ) :
    (𝔼 v : I → A, f (v i) * g (v j)) = (𝔼 a, f a) * (𝔼 a, g a) := by
  classical
  let u : I → A → ℝ := fun k a ↦
    (if k = i then f a else 1) * (if k = j then g a else 1)
  have hu (k : I) : (𝔼 a, u k a) =
      (if k = i then 𝔼 a, f a else 1) * (if k = j then 𝔼 a, g a else 1) := by
    by_cases hi : k = i <;> by_cases hj : k = j <;>
      simp_all [u]
  calc
    _ = 𝔼 v : I → A, ∏ k, u k (v k) := by
      apply expect_congr rfl
      intro v _
      dsimp only [u]
      rw [prod_mul_distrib]
      simp only [prod_ite_eq', mem_univ, if_true]
    _ = ∏ k, 𝔼 a, u k a := expect_pi_prod u
    _ = _ := by
      simp_rw [hu]
      rw [prod_mul_distrib]
      simp only [prod_ite_eq', mem_univ, if_true]

lemma expect_center_sq {A : Type*} [Fintype A] [Nonempty A] (f : A → ℝ) :
    (𝔼 a, (f a - 𝔼 b, f b)^2) = (𝔼 a, (f a)^2) - (𝔼 a, f a)^2 := by
  have he : ∀ a, (f a - 𝔼 b, f b)^2 =
      (f a)^2 - 2*(𝔼 b, f b)*f a + (𝔼 b, f b)^2 := by intro a; ring
  simp_rw [he]
  rw [expect_add_distrib, expect_sub_distrib, ← mul_expect, Fintype.expect_const]
  ring

lemma sample_mean_center_sq {I A : Type*} [Fintype I] [Nonempty I]
    [Fintype A] [Nonempty A] (f : A → ℝ) :
    (𝔼 v : I → A, ((𝔼 i, f (v i)) - (𝔼 a, f a))^2) =
      ((𝔼 a, (f a)^2) - (𝔼 a, f a)^2) / Fintype.card I := by
  classical
  let g : A → ℝ := fun a ↦ f a - 𝔼 b, f b
  have hg : (𝔼 a, g a) = 0 := by simp [g, expect_sub_distrib]
  have hm (v : I → A) : (𝔼 i, f (v i)) - (𝔼 a, f a) = 𝔼 i, g (v i) := by
    simp [g, expect_sub_distrib]
  have hpair (i j : I) : (𝔼 v : I → A, g (v i)*g (v j)) =
      if i = j then 𝔼 a, (g a)^2 else 0 := by
    by_cases h : i = j
    · subst j
      simp only [if_true, ← sq]
      exact expect_pi_apply i (fun a ↦ (g a)^2)
    · rw [if_neg h, expect_pi_apply_mul h, hg, zero_mul]
  have hinner (i : I) : (𝔼 j : I, if i = j then 𝔼 a, (g a)^2 else 0) =
      (𝔼 a, (g a)^2) / Fintype.card I := by
    rw [Finset.expect_eq_sum_div_card]
    simp
  calc
    _ = 𝔼 v : I → A, 𝔼 i : I, 𝔼 j : I, g (v i)*g (v j) := by
      apply expect_congr rfl
      intro v _
      rw [hm, sq, Fintype.expect_mul_expect]
    _ = 𝔼 i : I, 𝔼 j : I, 𝔼 v : I → A, g (v i)*g (v j) := by
      rw [expect_comm]
      apply expect_congr rfl
      intro i _
      exact expect_comm _ _ _
    _ = (𝔼 a, (g a)^2) / Fintype.card I := by
      simp_rw [hpair, hinner]
      exact Fintype.expect_const _
    _ = _ := by rw [show (𝔼 a, (g a)^2) = _ from expect_center_sq f]

/-- Mean squared sampling error, summed over an arbitrary finite set of coordinates. -/
theorem sample_mean_sq_bound {I A X : Type*} [Fintype I] [Nonempty I]
    [Fintype A] [Nonempty A] [Fintype X] (f : A → X → ℝ) :
    (𝔼 v : I → A, ∑ x, ((𝔼 i, f (v i) x) - (𝔼 a, f a x))^2) ≤
      (∑ x, 𝔼 a, (f a x)^2) / Fintype.card I := by
  rw [expect_sum_comm, sum_div]
  apply sum_le_sum
  intro x _
  rw [sample_mean_center_sq (I := I) (fun a ↦ f a x)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact sub_le_self _ (sq_nonneg _)

#print axioms sample_mean_sq_bound

/-- A finite Markov bound in cardinality form, including the zero-bound case. -/
lemma card_le_two_card_sublevel {V : Type*} [Fintype V]
    (E : V → ℝ) {B : ℝ} (hB : 0 ≤ B) (hE : ∀ v, 0 ≤ E v)
    (hsum : (∑ v, E v) ≤ Fintype.card V * B) :
    Fintype.card V ≤ 2 * (univ.filter (fun v ↦ E v ≤ 2*B)).card := by
  classical
  by_cases hB0 : B = 0
  · have hz (v : V) : E v = 0 := by
      have hsingle : E v ≤ ∑ w, E w := single_le_sum (fun w _ ↦ hE w) (mem_univ v)
      rw [hB0, mul_zero] at hsum
      exact le_antisymm (hsingle.trans hsum) (hE v)
    simp only [hB0, hz, mul_zero, le_refl, filter_true, card_univ]
    omega
  have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
  let D := univ.filter (fun v ↦ ¬ E v ≤ 2*B)
  have hd : (D.card : ℝ)*(2*B) ≤ ∑ v, E v := by
    calc
      _ = ∑ v ∈ D, 2*B := by simp
      _ ≤ ∑ v ∈ D, E v := sum_le_sum (fun v hv ↦ (lt_of_not_ge (mem_filter.mp hv).2).le)
      _ ≤ ∑ v, E v := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun v _ _ ↦ hE v)
  have hdc : 2*(D.card : ℝ) ≤ Fintype.card V := by
    apply (mul_le_mul_iff_of_pos_right hBp).mp
    calc
      (2*(D.card : ℝ))*B = (D.card : ℝ)*(2*B) := by ring
      _ ≤ Fintype.card V * B := hd.trans hsum
  have hdcN : 2*D.card ≤ Fintype.card V := by exact_mod_cast hdc
  have hpart := card_filter_add_card_filter_not (s := (univ : Finset V)) (fun v ↦ E v ≤ 2*B)
  simp only [card_univ] at hpart
  change (univ.filter (fun v ↦ E v ≤ 2*B)).card + D.card = Fintype.card V at hpart
  omega

/-- At least half of all samples satisfy twice the mean squared error bound. -/
theorem many_good_samples {I A X : Type*} [Fintype I] [Nonempty I]
    [Fintype A] [Nonempty A] [Fintype X] (f : A → X → ℝ) :
    ∃ L : Finset (I → A), Fintype.card (I → A) ≤ 2*L.card ∧
      ∀ v ∈ L, (∑ x, ((𝔼 i, f (v i) x) - (𝔼 a, f a x))^2) ≤
        (2 / (Fintype.card I : ℝ)) * ∑ x, 𝔼 a, (f a x)^2 := by
  classical
  let E : (I → A) → ℝ := fun v ↦ ∑ x, ((𝔼 i, f (v i) x) - (𝔼 a, f a x))^2
  let B : ℝ := (∑ x, 𝔼 a, (f a x)^2) / Fintype.card I
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hE (v : I → A) : 0 ≤ E v := by dsimp [E]; positivity
  have hmean : (𝔼 v, E v) ≤ B := sample_mean_sq_bound f
  have hsum : (∑ v, E v) ≤ Fintype.card (I → A)*B := by
    calc
      _ = Fintype.card (I → A)*(𝔼 v, E v) := (Fintype.card_mul_expect E).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg _)
  refine ⟨univ.filter (fun v ↦ E v ≤ 2*B), card_le_two_card_sublevel E hB hE hsum, ?_⟩
  intro v hv
  have hh := (mem_filter.mp hv).2
  dsimp only [E, B] at hh
  convert hh using 1
  ring

#print axioms many_good_samples
end Erdos3FiniteSampling
