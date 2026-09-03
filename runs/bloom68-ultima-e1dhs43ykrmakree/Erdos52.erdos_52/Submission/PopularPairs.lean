import Mathlib

/-!
# Jointly popular ordered sum/product pairs

This file contains only a finite counting reduction. It does not import
`Submission.Spec` or assert a sum-product lower bound.

The domain is the ordered Cartesian square `A ×ˢ A`, including diagonal pairs.
A union bound for small fibers of two finite functions gives the main estimate.
-/

open scoped BigOperators Pointwise

namespace Erdos52
namespace PopularPairs

/-- The number of elements of `S` mapped to `b` by `f`. -/
def fiberMultiplicity {α β : Type*} [DecidableEq β]
    (S : Finset α) (f : α → β) (b : β) : ℕ :=
  (S.filter fun x => f x = b).card

/-- The elements in fibers of size less than `t` number at most
`t` times the cardinality of the image. This also holds when `t = 0`. -/
theorem card_filter_fiberMultiplicity_lt_le {α β : Type*} [DecidableEq β]
    (S : Finset α) (f : α → β) (t : ℕ) :
    (S.filter fun x => fiberMultiplicity S f (f x) < t).card ≤
      t * (S.image f).card := by
  classical
  let B := (S.image f).filter fun b => fiberMultiplicity S f b < t
  have hfilter : (S.filter fun x => fiberMultiplicity S f (f x) < t) =
      S.filter (fun x => f x ∈ B) := by
    ext x
    simp only [B, Finset.mem_filter]
    constructor
    · intro hx
      exact ⟨hx.1, Finset.mem_image_of_mem f hx.1, hx.2⟩
    · intro hx
      exact ⟨hx.1, hx.2.2⟩
  calc
    _ = ∑ b ∈ B, fiberMultiplicity S f b := by
      rw [hfilter]
      exact (Finset.sum_card_fiberwise_eq_card_filter S B f).symm
    _ ≤ ∑ _b ∈ B, t := by
      apply Finset.sum_le_sum
      intro b hb
      exact (Finset.mem_filter.mp hb).2.le
    _ = t * B.card := by simp [Nat.mul_comm]
    _ ≤ t * (S.image f).card :=
      Nat.mul_le_mul_left t (Finset.card_filter_le _ _)

/-- For any two functions on a finite domain, all but at most
`t * (|image f| + |image g|)` elements belong to fibers of size at least `t`
for both functions. -/
theorem card_le_jointly_popular_add {α β γ : Type*}
    [DecidableEq β] [DecidableEq γ]
    (S : Finset α) (f : α → β) (g : α → γ) (t : ℕ) :
    S.card ≤
      (S.filter fun x =>
        t ≤ fiberMultiplicity S f (f x) ∧ t ≤ fiberMultiplicity S g (g x)).card +
      t * ((S.image f).card + (S.image g).card) := by
  classical
  let P := S.filter fun x =>
    t ≤ fiberMultiplicity S f (f x) ∧ t ≤ fiberMultiplicity S g (g x)
  let Bf := S.filter fun x => fiberMultiplicity S f (f x) < t
  let Bg := S.filter fun x => fiberMultiplicity S g (g x) < t
  have hcover : S ⊆ (P ∪ Bf) ∪ Bg := by
    intro x hx
    simp only [P, Bf, Bg, Finset.mem_union, Finset.mem_filter]
    by_cases hf : t ≤ fiberMultiplicity S f (f x)
    · by_cases hg : t ≤ fiberMultiplicity S g (g x)
      · exact Or.inl (Or.inl ⟨hx, hf, hg⟩)
      · exact Or.inr ⟨hx, Nat.lt_of_not_ge hg⟩
    · exact Or.inl (Or.inr ⟨hx, Nat.lt_of_not_ge hf⟩)
  change S.card ≤ P.card + t * ((S.image f).card + (S.image g).card)
  calc
    S.card ≤ ((P ∪ Bf) ∪ Bg).card := Finset.card_le_card hcover
    _ ≤ (P.card + Bf.card) + Bg.card :=
      (Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    _ ≤ (P.card + t * (S.image f).card) + t * (S.image g).card :=
      Nat.add_le_add
        (Nat.add_le_add_left (card_filter_fiberMultiplicity_lt_le S f t) _)
        (card_filter_fiberMultiplicity_lt_le S g t)
    _ = _ := by ring

end PopularPairs

/-- Ordered sum multiplicity: `σ_A(s) = #{(a,b) ∈ A × A : a + b = s}`. -/
def sumMultiplicity (A : Finset ℤ) (s : ℤ) : ℕ :=
  PopularPairs.fiberMultiplicity (A ×ˢ A) (fun ab => ab.1 + ab.2) s

/-- Ordered product multiplicity: `ρ_A(p) = #{(a,b) ∈ A × A : a * b = p}`. -/
def productMultiplicity (A : Finset ℤ) (p : ℤ) : ℕ :=
  PopularPairs.fiberMultiplicity (A ×ˢ A) (fun ab => ab.1 * ab.2) p

/-- Ordered pairs whose sum and product both have multiplicity at least `t`. -/
def jointlyPopular (A : Finset ℤ) (t : ℕ) : Finset (ℤ × ℤ) :=
  (A ×ˢ A).filter fun ab =>
    t ≤ sumMultiplicity A (ab.1 + ab.2) ∧
    t ≤ productMultiplicity A (ab.1 * ab.2)

@[simp]
theorem mem_jointlyPopular (A : Finset ℤ) (t : ℕ) (a b : ℤ) :
    (a, b) ∈ jointlyPopular A t ↔
      a ∈ A ∧ b ∈ A ∧ t ≤ sumMultiplicity A (a + b) ∧
        t ≤ productMultiplicity A (a * b) := by
  simp [jointlyPopular, and_assoc]

/-- Elementary counting reduction for ordered sum/product pairs, for every
finite set of integers and every natural threshold (including zero). -/
theorem card_sq_le_jointlyPopular_card_add (A : Finset ℤ) (t : ℕ) :
    A.card ^ 2 ≤ (jointlyPopular A t).card +
      t * ((A + A).card + (A * A).card) := by
  simpa only [jointlyPopular, sumMultiplicity, productMultiplicity,
    Finset.card_product, pow_two, Finset.image_add_product, Finset.image_mul_product] using
    PopularPairs.card_le_jointly_popular_add (A ×ˢ A)
      (fun ab : ℤ × ℤ => ab.1 + ab.2) (fun ab : ℤ × ℤ => ab.1 * ab.2) t

/-- Conditional on both supports being at most `N^(2 - ε)`, at least half of
all ordered pairs are jointly popular at any natural threshold `t ≤ N^ε / 4`.
Here `N = A.card`; no sum-product support bound is asserted by this theorem. -/
theorem half_card_sq_le_jointlyPopular_card_of_max_support_le
    (A : Finset ℤ) (ε : ℝ) (t : ℕ) (hA : A.Nonempty)
    (hsupport : (max (A + A).card (A * A).card : ℝ) ≤ (A.card : ℝ) ^ (2 - ε))
    (ht : (t : ℝ) ≤ (A.card : ℝ) ^ ε / 4) :
    (A.card : ℝ) ^ 2 / 2 ≤ ((jointlyPopular A t).card : ℝ) := by
  have hN : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hmax : max ((A + A).card : ℝ) ((A * A).card : ℝ) ≤
      (A.card : ℝ) ^ (2 - ε) := by
    simpa only [Nat.cast_max] using hsupport
  have hs := (le_max_left ((A + A).card : ℝ) ((A * A).card : ℝ)).trans hmax
  have hp := (le_max_right ((A + A).card : ℝ) ((A * A).card : ℝ)).trans hmax
  have hpow : (A.card : ℝ) ^ ε * (A.card : ℝ) ^ (2 - ε) = (A.card : ℝ) ^ 2 := by
    rw [← Real.rpow_add hN, show ε + (2 - ε) = (2 : ℝ) by ring, Real.rpow_two]
  have hbudget : (t : ℝ) * (((A + A).card : ℝ) + ((A * A).card : ℝ)) ≤
      (A.card : ℝ) ^ 2 / 2 := by
    calc
      _ ≤ ((A.card : ℝ) ^ ε / 4) * (2 * (A.card : ℝ) ^ (2 - ε)) :=
        mul_le_mul ht (by linarith only [hs, hp]) (by positivity) (by positivity)
      _ = ((A.card : ℝ) ^ ε * (A.card : ℝ) ^ (2 - ε)) / 2 := by ring
      _ = (A.card : ℝ) ^ 2 / 2 := by rw [hpow]
  have hcount : (A.card : ℝ) ^ 2 ≤ ((jointlyPopular A t).card : ℝ) +
      (t : ℝ) * (((A + A).card : ℝ) + ((A * A).card : ℝ)) := by
    exact_mod_cast card_sq_le_jointlyPopular_card_add A t
  linarith only [hcount, hbudget]

/-- An explicit natural threshold: at least half of the ordered pairs are
jointly `⌊N^ε / 4⌋₊`-popular under the assumed support bound. -/
theorem half_card_sq_le_jointlyPopular_floor
    (A : Finset ℤ) (ε : ℝ) (hA : A.Nonempty)
    (hsupport : (max (A + A).card (A * A).card : ℝ) ≤ (A.card : ℝ) ^ (2 - ε)) :
    (A.card : ℝ) ^ 2 / 2 ≤
      ((jointlyPopular A ⌊(A.card : ℝ) ^ ε / 4⌋₊).card : ℝ) := by
  exact half_card_sq_le_jointlyPopular_card_of_max_support_le A ε _ hA hsupport
    (Nat.floor_le (by positivity))

/-- For `N^ε ≥ 8`, the threshold in the preceding result is at least
`N^ε / 8`. Thus a positive fraction (at least one half) of all ordered pairs
have both multiplicities polynomially large when `ε > 0`.
The only support estimate used here is the explicit hypothesis. -/
theorem exists_many_polynomially_popular_pairs
    (A : Finset ℤ) (ε : ℝ) (hA : A.Nonempty)
    (hsupport : (max (A + A).card (A * A).card : ℝ) ≤ (A.card : ℝ) ^ (2 - ε))
    (hlarge : 8 ≤ (A.card : ℝ) ^ ε) :
    ∃ t : ℕ, (A.card : ℝ) ^ ε / 8 ≤ (t : ℝ) ∧
      (A.card : ℝ) ^ 2 / 2 ≤ ((jointlyPopular A t).card : ℝ) := by
  refine ⟨⌊(A.card : ℝ) ^ ε / 4⌋₊, ?_,
    half_card_sq_le_jointlyPopular_floor A ε hA hsupport⟩
  have hfloor := Nat.lt_floor_add_one ((A.card : ℝ) ^ ε / 4)
  linarith only [hlarge, hfloor]

end Erdos52

#print axioms Erdos52.PopularPairs.card_filter_fiberMultiplicity_lt_le
#print axioms Erdos52.PopularPairs.card_le_jointly_popular_add
#print axioms Erdos52.mem_jointlyPopular
#print axioms Erdos52.card_sq_le_jointlyPopular_card_add
#print axioms Erdos52.half_card_sq_le_jointlyPopular_card_of_max_support_le
#print axioms Erdos52.half_card_sq_le_jointlyPopular_floor
#print axioms Erdos52.exists_many_polynomially_popular_pairs
