import Submission.SharpSelbergWeights

/-!
# Finite upper-sieve kernels for nonnegative weights

The error is retained as a weighted sum over pairs of supports. No
pointwise maximum or support-pair cardinality loss is inserted here.
-/
open Finset
open scoped Classical BigOperators
namespace Erdos821.Sieve

lemma weighted_sifted_le_square_sum {α ι : Type*}
    (A : Finset α) (D : Finset ι) (E : ι → α → Prop) [∀ i, DecidablePred (E i)]
    (good : α → Prop) [DecidablePred good] (w : ι → ℝ) (h : α → ℝ)
    (hh : ∀ x ∈ A, 0 ≤ h x)
    (hgood : ∀ x ∈ A, good x → (∑ i ∈ D, if E i x then w i else 0)=1) :
    (∑ x ∈ A with good x, h x) ≤ ∑ x ∈ A, h x*(∑ i ∈ D, if E i x then w i else 0)^2 := by
  rw [sum_filter]
  apply sum_le_sum
  intro x hx
  by_cases hg : good x
  · rw [if_pos hg,hgood x hx hg,one_pow,mul_one]
  · rw [if_neg hg]
    exact mul_nonneg (hh x hx) (sq_nonneg _)

lemma weighted_sifted_le_main_error {α ι : Type*}
    (A : Finset α) (D : Finset ι) (E : ι → α → Prop) [∀ i, DecidablePred (E i)]
    (good : α → Prop) [DecidablePred good] (w : ι → ℝ) (h : α → ℝ)
    (hh : ∀ x ∈ A, 0 ≤ h x) (X : ℝ) (ν R : ι → ι → ℝ)
    (hgood : ∀ x ∈ A, good x → (∑ i ∈ D, if E i x then w i else 0)=1)
    (hcount : ∀ i ∈ D, ∀ j ∈ D,
      (∑ x ∈ A, if E i x ∧ E j x then h x else 0)=X*ν i j+R i j) :
    (∑ x ∈ A with good x, h x) ≤ X*(∑ i ∈ D, ∑ j ∈ D, w i*w j*ν i j)+
      ∑ i ∈ D, ∑ j ∈ D, |w i*w j| *|R i j| := by
  apply (weighted_sifted_le_square_sum A D E good w h hh hgood).trans
  rw [weighted_square_sum_expansion]
  calc
    _ = ∑ i ∈ D, ∑ j ∈ D, (X*(w i*w j*ν i j)+w i*w j*R i j) := by
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      rw [hcount i hi j hj]
      ring
    _ ≤ ∑ i ∈ D, ∑ j ∈ D, (X*(w i*w j*ν i j)+|w i*w j| *|R i j|) := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      apply add_le_add le_rfl
      simpa only [abs_mul] using le_abs_self (w i*w j*R i j)
    _ = _ := by simp only [sum_add_distrib,mul_sum]

lemma selberg_good_sum_on_support {α ι : Type*} [DecidableEq ι]
    (P : Finset ι) (W : Finset (Finset ι)) (hWP : W ⊆ P.powerset) (hW0 : ∅ ∈ W)
    (bad : ι → α → Prop) [∀ i, DecidablePred (bad i)] (w : Finset ι → ℝ) (hw0 : w ∅=1)
    (x : α) (hx : ∀ p ∈ P, ¬bad p x) :
    (∑ S ∈ W, if ∀ p ∈ S, bad p x then w S else 0)=1 := by
  rw [sum_eq_single ∅]
  · simpa using hw0
  · intro S hS hSne
    apply if_neg
    intro hbad
    obtain ⟨p,hp⟩ := nonempty_iff_ne_empty.mpr hSne
    exact hx p (mem_powerset.mp (hWP hS) hp) (hbad p hp)
  · exact fun h => (h hW0).elim

lemma selberg_quadratic_restrict_support {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (W : Finset (Finset ι)) (hWP : W ⊆ P.powerset)
    (w : Finset ι → ℝ) (hwzero : ∀ S ∈ P.powerset, S ∉ W → w S=0)
    (v : ι → ℝ) :
    (∑ S ∈ W, ∑ T ∈ W, w S*w T*(∏ p ∈ S∪T, v p))=
      ∑ S ∈ P.powerset, ∑ T ∈ P.powerset, w S*w T*(∏ p ∈ S∪T, v p) := by
  calc
    _ = ∑ S ∈ P.powerset, ∑ T ∈ W, w S*w T*(∏ p ∈ S∪T, v p) := by
      apply sum_subset hWP
      intro S hS hSW
      simp only [hwzero S hS hSW,zero_mul,sum_const_zero]
    _ = _ := by
      apply sum_congr rfl
      intro S hS
      apply sum_subset hWP
      intro T hT hTW
      simp only [hwzero T hT hTW,mul_zero,zero_mul]

end Erdos821.Sieve
