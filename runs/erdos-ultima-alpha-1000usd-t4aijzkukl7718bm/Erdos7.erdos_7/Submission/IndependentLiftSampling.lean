import Submission.IndependentPureLifts

/-! Exact finite product sampling of pure-avoiding p-adic lifts. Independence
here refers to the sampled lifts, not to competing covering-core events. -/
namespace Erdos7IndependentLiftSampling
open scoped BigOperators
open Erdos7PresentCylinderArithmetic Erdos7IndependentPureLifts
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- A uniform finite product law gives the product of the coordinate hit
fractions. This statement explicitly constructs the finite sample space. -/
theorem product_hit_fraction {I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} [∀ i, DecidableEq (A i)] (S B : (i : I) → Finset (A i)) :
    (((Fintype.piFinset S).filter (fun x => ∀ i, x i ∈ B i)).card : ℚ) /
      (Fintype.piFinset S).card =
      ∏ i, ((S i ∩ B i).card : ℚ)/(S i).card := by
  classical
  have he : (Fintype.piFinset S).filter (fun x => ∀ i, x i ∈ B i) =
      Fintype.piFinset (fun i => S i ∩ B i) := by
    ext x
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_inter]
    exact forall_and.symm
  rw [he, Fintype.card_piFinset, Fintype.card_piFinset, Nat.cast_prod,
    Nat.cast_prod, Finset.prod_div_distrib]

/-- A prescribed exponent-e cylinder has conditional hit fraction at most
p*(p-1)/(p-2) * p^(-e) within any fixed pure-avoiding branch. -/
theorem branch_hit_fraction_le (p E e : ℕ) [NeZero p] (hp : 3 ≤ p)
    (hE : 1 ≤ E) (he : e ≤ E) (a : ℕ → ℤ) (b c : ℤ) :
    ((branchGood p E a b ∩ cylinder p E e c).card : ℚ) /
      (branchGood p E a b).card ≤
      (p*(p-1)/(p-2) : ℚ)*((p : ℚ)⁻¹)^e := by
  have hpq : (3 : ℚ) ≤ p := by exact_mod_cast hp
  have hN : (0 : ℚ) < Fintype.card (ZMod (p^E)) := by exact_mod_cast Fintype.card_pos
  have hb := branchGood_card_le p E hp hE a b
  have hi : ((branchGood p E a b ∩ cylinder p E e c).card : ℚ) ≤
      (Fintype.card (ZMod (p^E)) : ℚ)*((p : ℚ)⁻¹)^e := by
    rw [← cylinder_card p E e he c]
    exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  have hden : (0 : ℚ) < (Fintype.card (ZMod (p^E)) : ℚ)*(p-2)/(p*(p-1)) := by
    apply div_pos
    · exact mul_pos hN (by linarith)
    · exact mul_pos (by linarith) (by linarith)
  have hh := div_le_div₀ (show (0 : ℚ) ≤ Fintype.card (ZMod (p^E))*((p : ℚ)⁻¹)^e by positivity)
    hi hden hb
  apply hh.trans_eq
  field_simp [ne_of_gt hN, show (p : ℚ)-2 ≠ 0 by linarith,
    show (p : ℚ)-1 ≠ 0 by linarith]

/-- Product upper bound for independent prescribed lifts. Taking I to index
(prime, branch) permits independent higher digits even within the same prime.
This does not assert independence of events sharing one of those lifts. -/
theorem independent_hit_fraction_le {I : Type*} [Fintype I] [DecidableEq I]
    (p E e : I → ℕ) [∀ i, NeZero (p i)] (hp : ∀ i, 3 ≤ p i)
    (hE : ∀ i, 1 ≤ E i) (he : ∀ i, e i ≤ E i)
    (a : I → ℕ → ℤ) (b c : I → ℤ) :
    let S := fun i => branchGood (p i) (E i) (a i) (b i)
    (((Fintype.piFinset S).filter (fun x => ∀ i,
      x i ∈ cylinder (p i) (E i) (e i) (c i))).card : ℚ) /
      (Fintype.piFinset S).card ≤
      ∏ i, (p i*(p i-1)/(p i-2) : ℚ)*((p i : ℚ)⁻¹)^(e i) := by
  classical
  dsimp only
  rw [product_hit_fraction]
  apply Finset.prod_le_prod
  · intro i _
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro i _
    exact branch_hit_fraction_le (p i) (E i) (e i) (hp i) (hE i) (he i) (a i) (b i) (c i)

#print axioms product_hit_fraction
#print axioms branch_hit_fraction_le
#print axioms independent_hit_fraction_le
end Erdos7IndependentLiftSampling
