import Submission.IndependentLiftSampling

/-! Independent lifts in different branches share a single deletion budget.
This improves the joint hit bound but does not control a union of core events. -/
namespace Erdos7SharedBranchBudget
open scoped BigOperators
open Erdos7PresentCylinderArithmetic Erdos7IndependentPureLifts
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Removing D from two disjoint equal-sized branches incurs its budget once
in a product lower bound, rather than once per branch. -/
lemma two_branch_product_lower {X : Type*} [DecidableEq X]
    (S T D : Finset X) (hst : Disjoint S T) (he : S.card = T.card) :
    (S.card : ℚ)*((S.card : ℚ)-D.card) ≤
      ((S \ D).card : ℚ)*(T \ D).card := by
  have hd : Disjoint (S ∩ D) (T ∩ D) :=
    hst.mono Finset.inter_subset_left Finset.inter_subset_left
  have hsum : (S ∩ D).card+(T ∩ D).card ≤ D.card := by
    rw [← Finset.card_union_of_disjoint hd]
    apply Finset.card_le_card
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_inter.mp hx).2
    · exact (Finset.mem_inter.mp hx).2
  have hsumq : ((S ∩ D).card : ℚ)+(T ∩ D).card ≤ D.card := by exact_mod_cast hsum
  have hS : ((S \ D).card : ℚ)+(S ∩ D).card = S.card := by
    exact_mod_cast Finset.card_sdiff_add_card_inter S D
  have hT : ((T \ D).card : ℚ)+(T ∩ D).card = S.card := by
    rw [he]
    exact_mod_cast Finset.card_sdiff_add_card_inter T D
  have hn : (0 : ℚ) ≤ S.card := Nat.cast_nonneg _
  have hr : (0 : ℚ) ≤ (S ∩ D).card*(T ∩ D).card := by positivity
  have hm := mul_le_mul_of_nonneg_left hsumq hn
  nlinarith

/-- The two branches have a shared total higher-pure loss. -/
theorem branch_pair_card_lower (p E : ℕ) [NeZero p] (hp : 3 ≤ p)
    (hE : 1 ≤ E) (a : ℕ → ℤ) (b c : ℤ) (hbc : ¬ (p : ℤ) ∣ c-b) :
    (Fintype.card (ZMod (p^E)) : ℚ)^2*(p-2)/(p^2*(p-1)) ≤
      ((branchGood p E a b).card : ℚ)*(branchGood p E a c).card := by
  have hpq : (3 : ℚ) ≤ p := by exact_mod_cast hp
  have hdis : Disjoint (cylinder p E 1 b) (cylinder p E 1 c) :=
    cylinders_disjoint p E 1 1 le_rfl b c (by simpa only [pow_one] using hbc)
  have he : (cylinder p E 1 b).card = (cylinder p E 1 c).card := by
    have heq := (cylinder_card p E 1 hE b).trans (cylinder_card p E 1 hE c).symm
    exact_mod_cast heq
  have hh := two_branch_product_lower (cylinder p E 1 b) (cylinder p E 1 c)
    (higherBad p E a) hdis he
  change (↑(cylinder p E 1 b).card : ℚ)*
    (↑(cylinder p E 1 b).card-(higherBad p E a).card) ≤
      ((branchGood p E a b).card : ℚ)*(branchGood p E a c).card at hh
  rw [cylinder_card p E 1 hE b, pow_one] at hh
  have hb := higherBad_card_le p E (by omega) a
  have hmult := mul_le_mul_of_nonneg_left hb
    (show (0 : ℚ) ≤ Fintype.card (ZMod (p^E))*(p : ℚ)⁻¹ by positivity)
  have heq : (Fintype.card (ZMod (p^E)) : ℚ)^2*(p-2)/(p^2*(p-1)) =
      (Fintype.card (ZMod (p^E)) : ℚ)*(p : ℚ)⁻¹*
      ((Fintype.card (ZMod (p^E)) : ℚ)*(p : ℚ)⁻¹-
        (Fintype.card (ZMod (p^E)) : ℚ)/(p*(p-1))) := by
    field_simp [show (p : ℚ)-1 ≠ 0 by linarith]
    <;> ring
  rw [heq]
  nlinarith

/-- Exact product sampling in two prescribed, different first-digit branches.
The joint bound pays (p-1)/(p-2), not its square. -/
theorem branch_pair_hit_fraction_le (p E e f : ℕ) [NeZero p] (hp : 3 ≤ p)
    (hE : 1 ≤ E) (he : e ≤ E) (hf : f ≤ E)
    (a : ℕ → ℤ) (b c d v : ℤ) (hbc : ¬ (p : ℤ) ∣ c-b) :
    let S := branchGood p E a b
    let T := branchGood p E a c
    (((S ×ˢ T).filter (fun x => x.1 ∈ cylinder p E e d ∧
      x.2 ∈ cylinder p E f v)).card : ℚ) / (S ×ˢ T).card ≤
      ((p-1)/(p-2) : ℚ)*p^2*((p : ℚ)⁻¹)^(e+f) := by
  classical
  dsimp only
  rw [Finset.filter_product]
  simp only [Finset.filter_mem_eq_inter, Finset.card_product, Nat.cast_mul]
  have hpq : (3 : ℚ) ≤ p := by exact_mod_cast hp
  have hN : (0 : ℚ) < Fintype.card (ZMod (p^E)) := by exact_mod_cast Fintype.card_pos
  have hnum (t : ℕ) (ht : t ≤ E) (r s : ℤ) :
      ((branchGood p E a r ∩ cylinder p E t s).card : ℚ) ≤
        (Fintype.card (ZMod (p^E)) : ℚ)*((p : ℚ)⁻¹)^t := by
    rw [← cylinder_card p E t ht s]
    exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  have hn := mul_le_mul (hnum e he b d) (hnum f hf c v)
    (Nat.cast_nonneg _) (show (0 : ℚ) ≤ Fintype.card (ZMod (p^E))*((p : ℚ)⁻¹)^e by positivity)
  have hden : (0 : ℚ) < (Fintype.card (ZMod (p^E)) : ℚ)^2*(p-2)/(p^2*(p-1)) := by
    apply div_pos
    · exact mul_pos (sq_pos_of_pos hN) (by linarith)
    · exact mul_pos (sq_pos_of_pos (by linarith)) (by linarith)
  have hh := div_le_div₀ (show (0 : ℚ) ≤
      (Fintype.card (ZMod (p^E)) : ℚ)*((p : ℚ)⁻¹)^e*
      ((Fintype.card (ZMod (p^E)) : ℚ)*((p : ℚ)⁻¹)^f) by positivity)
    hn hden (branch_pair_card_lower p E hp hE a b c hbc)
  apply hh.trans_eq
  rw [pow_add]
  field_simp [ne_of_gt hN, show (p : ℚ)-2 ≠ 0 by linarith,
    show (p : ℚ)-1 ≠ 0 by linarith]
  <;> ring

#print axioms two_branch_product_lower
#print axioms branch_pair_card_lower
#print axioms branch_pair_hit_fraction_le
end Erdos7SharedBranchBudget
