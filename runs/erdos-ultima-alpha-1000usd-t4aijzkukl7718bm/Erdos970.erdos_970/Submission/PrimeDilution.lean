import FormalConjecturesUtil

/-! Finite prime sets with very large moduli can have a prescribed survival
factor near 63/64. This is an auxiliary thinning construction, not a bound
for Jacobsthal's function. -/
namespace Erdos970.PrimeDilution
open Finset Real Filter

lemma product_sum_le_one {α : Type*} (S : Finset α) (x : α → ℝ)
    (hx : ∀ a ∈ S, 0 ≤ x a ∧ x a ≤ 1) :
    (∏ a ∈ S, (1-x a)) * (1 + ∑ a ∈ S, x a) ≤ 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hS : ∀ b ∈ S, 0 ≤ x b ∧ x b ≤ 1 := fun b hb => hx b (mem_insert_of_mem hb)
    have hxa := hx a (mem_insert_self _ _)
    have hp : 0 ≤ ∏ b ∈ S, (1-x b) := prod_nonneg (fun b hb => by linarith [(hS b hb).2])
    have hs : 0 ≤ ∑ b ∈ S, x b := sum_nonneg (fun b hb => (hS b hb).1)
    rw [prod_insert ha, sum_insert ha]
    have hh := ih hS
    nlinarith [mul_nonneg hp (mul_nonneg hxa.1 hs), mul_nonneg hp (sq_nonneg (x a))]

lemma exists_crossing_product {α : Type*} (S : Finset α) (x : α → ℝ)
    (d e : ℝ) (he : e < 1) (hd : 0 ≤ d)
    (hx : ∀ a ∈ S, 0 ≤ x a ∧ x a ≤ 1 ∧ x a ≤ d)
    (hprod : (∏ a ∈ S, (1-x a)) ≤ e) :
    ∃ R ⊆ S, e-d ≤ (∏ a ∈ R, (1-x a)) ∧ (∏ a ∈ R, (1-x a)) ≤ e := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [prod_empty] at hprod; linarith
  | @insert a S ha ih =>
    have hS : ∀ b ∈ S, 0 ≤ x b ∧ x b ≤ 1 ∧ x b ≤ d :=
      fun b hb => hx b (mem_insert_of_mem hb)
    by_cases hle : (∏ b ∈ S, (1-x b)) ≤ e
    · obtain ⟨R, hR, hRl, hRu⟩ := ih hS hle
      exact ⟨R, hR.trans (subset_insert _ _), hRl, hRu⟩
    · refine ⟨insert a S, Subset.rfl, ?_, hprod⟩
      have hxa := hx a (mem_insert_self _ _)
      have hp : 0 ≤ ∏ b ∈ S, (1-x b) := prod_nonneg (fun b hb => by linarith [(hS b hb).2.1])
      have hp1 : (∏ b ∈ S, (1-x b)) ≤ 1 := prod_le_one
        (fun b hb => by linarith [(hS b hb).2.1]) (fun b hb => by linarith [(hS b hb).1])
      rw [prod_insert ha]
      have hm := mul_le_mul_of_nonneg_left hp1 hxa.1
      nlinarith

/-- Only the elementary half-unit prime reciprocal block from Mathlib is
needed; no prime number theorem or unverified computation is used. -/
theorem exists_dilution_primes (B : ℕ) (hB : 4 ≤ B) :
    ∃ R : Finset ℕ, (∀ p ∈ R, p.Prime ∧ B ≤ p) ∧
      (63/64 : ℝ) - 1/(B : ℝ) ≤ ∏ p ∈ R, (1-1/(p : ℝ)) ∧
      (∏ p ∈ R, (1-1/(p : ℝ))) ≤ 63/64 ∧
      (∑ p ∈ R, 1/(p : ℝ)) ≤ 1 := by
  let S := (4 ^ (B.primesBelow.card + 1)).succ.primesBelow \ B.primesBelow
  have hSp (p : ℕ) (hp : p ∈ S) : p.Prime ∧ B ≤ p := by
    obtain ⟨hp₁,hp₂⟩ := mem_sdiff.mp hp
    have hprime := Nat.prime_of_mem_primesBelow hp₁
    refine ⟨hprime, ?_⟩
    by_contra h
    exact hp₂ (Nat.mem_primesBelow.mpr ⟨by omega, hprime⟩)
  have hBr : (4 : ℝ) ≤ B := by exact_mod_cast hB
  have hB0 : (0 : ℝ) < B := by linarith
  have hx (p : ℕ) (hp : p ∈ S) :
      0 ≤ 1/(p : ℝ) ∧ 1/(p : ℝ) ≤ 1 ∧ 1/(p : ℝ) ≤ 1/(B : ℝ) := by
    have hpB : (B : ℝ) ≤ p := by exact_mod_cast (hSp p hp).2
    have hp0 : (0 : ℝ) < p := hB0.trans_le hpB
    exact ⟨by positivity, (div_le_one hp0).mpr (by linarith),
      one_div_le_one_div_of_le hB0 hpB⟩
  have hs : (1/2 : ℝ) ≤ ∑ p ∈ S, 1/(p : ℝ) := one_half_le_sum_primes_ge_one_div B
  have hprod := product_sum_le_one S (fun p => 1/(p : ℝ))
    (fun p hp => ⟨(hx p hp).1, (hx p hp).2.1⟩)
  have hp0 : 0 ≤ ∏ p ∈ S, (1-1/(p : ℝ)) := prod_nonneg (fun p hp => by linarith [(hx p hp).2.1])
  have hprod' : (∏ p ∈ S, (1-1/(p : ℝ))) ≤ (63/64 : ℝ) := by nlinarith
  obtain ⟨R,hR,hRl,hRu⟩ := exists_crossing_product S (fun p => 1/(p : ℝ))
    (1/(B : ℝ)) (63/64) (by norm_num) (by positivity) hx hprod'
  refine ⟨R, fun p hp => hSp p (hR hp), hRl, hRu, ?_⟩
  have hsum := product_sum_le_one R (fun p => 1/(p : ℝ))
    (fun p hp => ⟨(hx p (hR hp)).1, (hx p (hR hp)).2.1⟩)
  have hinv : 1/(B : ℝ) ≤ 1/4 := one_div_le_one_div_of_le (by norm_num) hBr
  have hs0 : 0 ≤ ∑ p ∈ R, 1/(p : ℝ) := sum_nonneg (fun p _ => by positivity)
  nlinarith

lemma power_linear_error (s : ℕ) (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ (1-x)^s - (1-(s : ℝ)*x) ∧
      (1-x)^s - (1-(s : ℝ)*x) ≤ (s : ℝ)^2*x^2 := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hn : 0 ≤ (s : ℝ) := Nat.cast_nonneg s
    have hbase : 0 ≤ 1-x := by linarith
    have hp := pow_nonneg hbase s
    have hm := mul_nonneg hbase ih.1
    have hu := mul_le_mul_of_nonneg_left ih.2 hbase
    rw [pow_succ]
    push_cast
    constructor
    · nlinarith [mul_nonneg hn (sq_nonneg x)]
    · have hsq : 0 ≤ (s : ℝ)^2*x^3 := by positivity
      nlinarith [mul_nonneg hn (sq_nonneg x)]

lemma prod_difference_le_sum {α : Type*} (S : Finset α) (a b : α → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) (hab : ∀ i ∈ S, a i ≤ b i)
    (hb : ∀ i ∈ S, b i ≤ 1) :
    0 ≤ (∏ i ∈ S, b i) - ∏ i ∈ S, a i ∧
      (∏ i ∈ S, b i) - ∏ i ∈ S, a i ≤ ∑ i ∈ S, (b i-a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have haS := fun j hj => ha j (mem_insert_of_mem hj)
    have habS := fun j hj => hab j (mem_insert_of_mem hj)
    have hbS := fun j hj => hb j (mem_insert_of_mem hj)
    have hh := ih haS habS hbS
    have hi' := mem_insert_self i S
    have hai := ha i hi'
    have habi := hab i hi'
    have hbi := hb i hi'
    have hp0 : 0 ≤ ∏ j ∈ S, a j := prod_nonneg haS
    have hp1 : (∏ j ∈ S, a j) ≤ 1 := prod_le_one haS (fun j hj => (habS j hj).trans (hbS j hj))
    have hs0 : 0 ≤ ∑ j ∈ S, (b j-a j) := sum_nonneg (fun j hj => sub_nonneg.mpr (habS j hj))
    rw [prod_insert hi, prod_insert hi, sum_insert hi]
    constructor
    · have hmul := mul_nonneg (show 0 ≤ b i by linarith) hh.1
      nlinarith [mul_nonneg (sub_nonneg.mpr habi) hp0]
    · have hmul := mul_le_mul_of_nonneg_left hh.2 (show 0 ≤ b i by linarith)
      have hmul' := mul_le_mul_of_nonneg_right hbi hs0
      have hd := mul_le_mul_of_nonneg_left hp1 (sub_nonneg.mpr habi)
      nlinarith

/-- The joint-survival product differs from independent thinning by a
quadratic reciprocal error. The hypothesis s<=p is retained. -/
lemma joint_product_error (R : Finset ℕ) (s : ℕ)
    (hR : ∀ p ∈ R, 0 < p ∧ s ≤ p) :
    0 ≤ (∏ p ∈ R, (1-1/(p : ℝ)))^s - ∏ p ∈ R, (1-(s : ℝ)/(p : ℝ)) ∧
      (∏ p ∈ R, (1-1/(p : ℝ)))^s - ∏ p ∈ R, (1-(s : ℝ)/(p : ℝ)) ≤
        (s : ℝ)^2 * ∑ p ∈ R, (1/(p : ℝ))^2 := by
  have hp (p : ℕ) (hp : p ∈ R) : (0 : ℝ) < p := by exact_mod_cast (hR p hp).1
  have hle (p : ℕ) (hp' : p ∈ R) : (s : ℝ) ≤ p := by exact_mod_cast (hR p hp').2
  have hunit (p : ℕ) (hp' : p ∈ R) : 1/(p : ℝ) ≤ 1 :=
    (div_le_one (hp p hp')).mpr (by exact_mod_cast (hR p hp').1)
  have herr (p : ℕ) (hp' : p ∈ R) := power_linear_error s (1/(p : ℝ)) (by positivity) (hunit p hp')
  have hh := prod_difference_le_sum R
    (fun p => 1-(s : ℝ)/(p : ℝ)) (fun p => (1-1/(p : ℝ))^s)
    (fun p hp' => sub_nonneg.mpr ((div_le_one (hp p hp')).mpr (hle p hp')))
    (fun p hp' => by have := (herr p hp').1; simp only [mul_one_div] at this; linarith)
    (fun p hp' => pow_le_one₀ (by linarith [hunit p hp']) (sub_le_self _ (by positivity)))
  rw [prod_pow] at hh
  refine ⟨hh.1, hh.2.trans ?_⟩
  rw [mul_sum]
  exact sum_le_sum (fun p hp' => by simpa only [mul_one_div] using (herr p hp').2)

#print axioms exists_dilution_primes
#print axioms joint_product_error
end Erdos970.PrimeDilution
