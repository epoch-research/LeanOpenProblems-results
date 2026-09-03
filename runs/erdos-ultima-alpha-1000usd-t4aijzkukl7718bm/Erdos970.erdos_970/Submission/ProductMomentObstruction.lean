import FormalConjecturesUtil

/-!
A nonnegative finite product model with the distinguished product atom deleted,
while preserving every proper block product moment. This is an abstract moment
construction, not a prime-residue interval cover.
-/
namespace Erdos970.ProductMomentObstruction
open Finset
variable {β : Type*} [Fintype β] [DecidableEq β]
variable {Ω : β → Type*} [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (Ω j)]

noncomputable def signedWeight {α : Type*} [DecidableEq α]
    (μ : α → ℝ) (a : α) (x : α) : ℝ :=
  if x = a then μ a else -(μ a / (1 - μ a)) * μ x

lemma signed_at_distinguished {α : Type*} [DecidableEq α]
    (μ : α → ℝ) (a : α) : signedWeight μ a a = μ a := by simp [signedWeight]

lemma signed_abs_le {α : Type*} [DecidableEq α]
    (μ : α → ℝ) (a x : α) (hμ : ∀ x, 0 ≤ μ x) (ha : μ a ≤ 1 / 2) :
    |signedWeight μ a x| ≤ μ x := by
  have hd : 0 < 1 - μ a := by linarith
  have hratio : 0 ≤ μ a / (1 - μ a) := div_nonneg (hμ a) hd.le
  have hratio1 : μ a / (1 - μ a) ≤ 1 := (div_le_one hd).mpr (by linarith)
  by_cases hx : x = a
  · subst x
    simp [signedWeight, abs_of_nonneg (hμ a)]
  · rw [signedWeight, if_neg hx, abs_mul, abs_neg,
      abs_of_nonneg hratio, abs_of_nonneg (hμ x)]
    simpa using mul_le_mul_of_nonneg_right hratio1 (hμ x)

lemma signed_sum_zero {α : Type*} [Fintype α] [DecidableEq α]
    (μ : α → ℝ) (a : α) (hsum : (∑ x, μ x) = 1) (ha : μ a < 1) :
    (∑ x, signedWeight μ a x) = 0 := by
  have hex : ∑ x ∈ univ.erase a, μ x = 1 - μ a := by
    have hh := sum_erase_add univ μ (mem_univ a)
    rw [hsum] at hh
    linarith
  rw [← sum_erase_add univ (signedWeight μ a) (mem_univ a)]
  have he : (∑ x ∈ univ.erase a, signedWeight μ a x) =
      -(μ a / (1 - μ a)) * (1 - μ a) := by
    calc
      _ = ∑ x ∈ univ.erase a, -(μ a / (1 - μ a)) * μ x := by
        apply sum_congr rfl
        intro x hx
        exact if_neg (mem_erase.mp hx).1
      _ = -(μ a / (1 - μ a)) * (∑ x ∈ univ.erase a, μ x) := (mul_sum _ _ _).symm
      _ = _ := by rw [hex]
  rw [he, signed_at_distinguished]
  have hd : 1 - μ a ≠ 0 := (sub_pos.mpr ha).ne'
  field_simp <;> ring

noncomputable def weight (μ : (j : β) → Ω j → ℝ) (a : (j : β) → Ω j)
    (v : (j : β) → Ω j) : ℝ :=
  (∏ j, μ j (v j)) - ∏ j, signedWeight (μ j) (a j) (v j)

lemma weight_nonneg (μ : (j : β) → Ω j → ℝ) (a : (j : β) → Ω j)
    (hμ : ∀ j x, 0 ≤ μ j x) (ha : ∀ j, μ j (a j) ≤ 1 / 2)
    (v : (j : β) → Ω j) : 0 ≤ weight μ a v := by
  apply sub_nonneg.mpr
  calc
    (∏ j, signedWeight (μ j) (a j) (v j)) ≤
        |∏ j, signedWeight (μ j) (a j) (v j)| := le_abs_self _
    _ = ∏ j, |signedWeight (μ j) (a j) (v j)| := abs_prod _ _
    _ ≤ ∏ j, μ j (v j) :=
      prod_le_prod (fun _ _ => abs_nonneg _) (fun j _ => signed_abs_le _ _ _ (hμ j) (ha j))

lemma weight_at_distinguished (μ : (j : β) → Ω j → ℝ) (a : (j : β) → Ω j) :
    weight μ a a = 0 := by simp [weight, signed_at_distinguished]

lemma weighted_product (μ : (j : β) → Ω j → ℝ) (a : (j : β) → Ω j)
    (f : (j : β) → Ω j → ℝ) :
    (∑ v, weight μ a v * ∏ j, f j (v j)) =
      (∏ j, ∑ x, μ j x * f j x) -
        ∏ j, ∑ x, signedWeight (μ j) (a j) x * f j x := by
  simp only [weight, sub_mul, sum_sub_distrib, ← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun j x => μ j x * f j x),
    ← Fintype.prod_sum (fun j x => signedWeight (μ j) (a j) x * f j x)]

/-- A product test omitting one block has exactly its original product mean. -/
theorem proper_product_moment (μ : (j : β) → Ω j → ℝ) (a : (j : β) → Ω j)
    (hsum : ∀ j, (∑ x, μ j x) = 1) (ha : ∀ j, μ j (a j) < 1)
    (f : (j : β) → Ω j → ℝ) (j : β) (hj : ∀ x, f j x = 1) :
    (∑ v, weight μ a v * ∏ j, f j (v j)) = ∏ j, ∑ x, μ j x * f j x := by
  rw [weighted_product]
  have hz : (∏ i, ∑ x, signedWeight (μ i) (a i) x * f i x) = 0 := by
    apply prod_eq_zero (mem_univ j)
    simp only [hj, mul_one]
    exact signed_sum_zero (μ j) (a j) (hsum j) (ha j)
  rw [hz, sub_zero]

lemma weight_sum [Nonempty β] (μ : (j : β) → Ω j → ℝ) (a : (j : β) → Ω j)
    (hsum : ∀ j, (∑ x, μ j x) = 1) (ha : ∀ j, μ j (a j) < 1) :
    (∑ v, weight μ a v) = 1 := by
  obtain ⟨j⟩ := ‹Nonempty β›
  have hh := proper_product_moment μ a hsum ha (fun _ _ => 1) j (fun _ => rfl)
  simpa [hsum] using hh

/-- A finite sum of proper block tests has the same expectation in the new
model. The tests may have arbitrary real coefficients. -/
theorem polynomial_moment {α : Type*} [Fintype α]
    (μ : (j : β) → Ω j → ℝ) (a : (j : β) → Ω j)
    (hsum : ∀ j, (∑ x, μ j x) = 1) (ha : ∀ j, μ j (a j) < 1)
    (c : α → ℝ) (f : α → (j : β) → Ω j → ℝ)
    (hproper : ∀ t, ∃ j, ∀ x, f t j x = 1) :
    (∑ v, weight μ a v * (∑ t, c t * ∏ j, f t j (v j))) =
      ∑ t, c t * ∏ j, ∑ x, μ j x * f t j x := by
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro t ht
  obtain ⟨j, hj⟩ := hproper t
  have he : (∑ v, weight μ a v * (c t * ∏ i, f t i (v i))) =
      c t * (∑ v, weight μ a v * ∏ i, f t i (v i)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro v hv
    ring
  rw [he, proper_product_moment μ a hsum ha (f t) j hj]

/-- No such proper-block polynomial can be nonpositive off the distinguished
atom while having positive product expectation. -/
theorem no_positive_lower_polynomial {α : Type*} [Fintype α]
    (μ : (j : β) → Ω j → ℝ) (a : (j : β) → Ω j)
    (hμ : ∀ j x, 0 ≤ μ j x) (hsum : ∀ j, (∑ x, μ j x) = 1)
    (ha : ∀ j, μ j (a j) ≤ 1 / 2)
    (c : α → ℝ) (f : α → (j : β) → Ω j → ℝ)
    (hproper : ∀ t, ∃ j, ∀ x, f t j x = 1)
    (hpoint : ∀ v, v ≠ a → (∑ t, c t * ∏ j, f t j (v j)) ≤ 0) :
    (∑ t, c t * ∏ j, ∑ x, μ j x * f t j x) ≤ 0 := by
  rw [← polynomial_moment μ a hsum (fun j => lt_of_le_of_lt (ha j) (by norm_num)) c f hproper]
  apply sum_nonpos
  intro v hv
  by_cases he : v = a
  · subst v
    simp [weight_at_distinguished]
  · exact mul_nonpos_of_nonneg_of_nonpos (weight_nonneg μ a hμ ha v) (hpoint v he)

#print axioms weight_nonneg
#print axioms weight_sum
#print axioms proper_product_moment
#print axioms no_positive_lower_polynomial
end Erdos970.ProductMomentObstruction
