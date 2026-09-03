import Submission.PrimePowerMinimalEvent

/-! Uniform branch-pair averaging for prescribed deepest prime-power constraints.
The two branches are sampled first; surviving lifts are then sampled uniformly
and independently within those branches. This is a local signature bound. -/
namespace Erdos7UniformBranchSignature
open scoped BigOperators
open Finset Erdos7PresentCylinderArithmetic Erdos7IndependentPureLifts
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Ordered distinct nonzero first digits. -/
def branchPairs (p : ℕ) : Finset (ℕ × ℕ) := ((range p).erase 0).offDiag

lemma mem_branchPairs {p : ℕ} {b c : ℕ} :
    (b, c) ∈ branchPairs p ↔ 0 < b ∧ b < p ∧ 0 < c ∧ c < p ∧ b ≠ c := by
  simp only [branchPairs, mem_offDiag, mem_erase, mem_range]
  omega

lemma branchPairs_card (p : ℕ) (hp : 1 ≤ p) :
    (branchPairs p).card = (p - 1) * (p - 2) := by
  rw [branchPairs, offDiag_card]
  have hc : ((range p).erase 0).card = p - 1 := by
    rw [card_erase_of_mem (mem_range.mpr (by omega)), card_range]
  rw [hc]
  conv_rhs => rw [show p - 2 = p - 1 - 1 by omega, Nat.mul_sub_left_distrib, mul_one]

lemma branch_separated {p b c : ℕ} (h : (b, c) ∈ branchPairs p) :
    ¬ (p : ℤ) ∣ (c : ℤ) - b := by
  obtain ⟨hb, hbp, hc, hcp, hbc⟩ := mem_branchPairs.mp h
  intro hd
  have he : (b : ZMod p) = (c : ZMod p) := by
    simpa only [Int.cast_natCast] using
      (ZMod.intCast_eq_intCast_iff_dvd_sub (b : ℤ) (c : ℤ) p).mpr hd
  have hv := congrArg ZMod.val he
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hbp, Nat.mod_eq_of_lt hcp] at hv
  exact hbc hv

/-- Conditional probability for fixed first digits and an oriented pair of
prescribed deepest cylinders. It is not uniform over all surviving pairs
with different first digits: the branch pair itself is sampled uniformly. -/
noncomputable def directFraction (p E e f : ℕ) [NeZero p] (pure : ℕ → ℤ)
    (a d : ℤ) (bc : ℕ × ℕ) : ℚ :=
  let S := branchGood p E pure bc.1
  let T := branchGood p E pure bc.2
  (((S ×ˢ T).filter (fun x => x.1 ∈ cylinder p E e a ∧
    x.2 ∈ cylinder p E f d)).card : ℚ) / (S ×ˢ T).card

lemma directFraction_nonneg (p E e f : ℕ) [NeZero p] (pure : ℕ → ℤ)
    (a d : ℤ) (bc : ℕ × ℕ) : 0 ≤ directFraction p E e f pure a d bc := by
  unfold directFraction
  positivity

lemma directFraction_le (p E e f : ℕ) [NeZero p] (hp : 3 ≤ p)
    (hE : 1 ≤ E) (he : e ≤ E) (hf : f ≤ E) (pure : ℕ → ℤ)
    (a d : ℤ) (bc : ℕ × ℕ) (hbc : bc ∈ branchPairs p) :
    directFraction p E e f pure a d bc ≤
      ((p - 1) / (p - 2) : ℚ) * p ^ 2 * ((p : ℚ)⁻¹) ^ (e + f) := by
  exact Erdos7SharedBranchBudget.branch_pair_hit_fraction_le p E e f hp hE he hf
    pure bc.1 bc.2 a d (branch_separated hbc)

/-- A hit fixes the sampled first digit to the target residue's first digit. -/
lemma branch_eq_first_digit {p E e b : ℕ} [NeZero p] (he : 0 < e)
    (hb : b < p) (pure : ℕ → ℤ) (a : ℤ) (x : ZMod (p ^ E))
    (hx : x ∈ branchGood p E pure b) (ha : x ∈ cylinder p E e a) :
    b = (a : ZMod p).val := by
  have hb' := ((mem_branchGood p E pure b x).mp hx).1
  have ha' := (mem_cylinder p E e a x).mp ha
  have hr : ((x.val : ℤ) : ZMod p) = a :=
    Erdos7PrimePowerMinimalEvent.first_digit_of_power he ha'
  have hs : ((x.val : ℤ) : ZMod p) = (b : ℤ) :=
    ((ZMod.intCast_eq_intCast_iff_dvd_sub (b : ℤ) (x.val : ℤ) p).mpr hb').symm
  have hv := congrArg ZMod.val (hs.symm.trans hr)
  simpa only [Int.cast_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hb] using hv

/-- All other ordered branch pairs have probability zero. -/
lemma directFraction_zero (p E e f : ℕ) [NeZero p]
    (he : 0 < e) (hf : 0 < f) (pure : ℕ → ℤ) (a d : ℤ)
    (bc : ℕ × ℕ) (hbc : bc ∈ branchPairs p)
    (hne : bc ≠ ((a : ZMod p).val, (d : ZMod p).val)) :
    directFraction p E e f pure a d bc = 0 := by
  have hb := mem_branchPairs.mp hbc
  have hempty : ((branchGood p E pure bc.1 ×ˢ branchGood p E pure bc.2).filter
      (fun x => x.1 ∈ cylinder p E e a ∧ x.2 ∈ cylinder p E f d)) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hS, hT⟩ := mem_product.mp (mem_filter.mp hx).1
    obtain ⟨ha, hd⟩ := (mem_filter.mp hx).2
    exact hne (Prod.ext (branch_eq_first_digit he hb.2.1 pure a x.1 hS ha)
      (branch_eq_first_digit hf hb.2.2.2.1 pure d x.2 hT hd))
  simp only [directFraction, hempty, card_empty, Nat.cast_zero, zero_div]

lemma sum_directFraction_le (p E e f : ℕ) [NeZero p] (hp : 3 ≤ p)
    (hE : 1 ≤ E) (he0 : 0 < e) (hf0 : 0 < f) (he : e ≤ E) (hf : f ≤ E)
    (pure : ℕ → ℤ) (a d : ℤ) :
    (∑ bc ∈ branchPairs p, directFraction p E e f pure a d bc) ≤
      ((p - 1) / (p - 2) : ℚ) * p ^ 2 * ((p : ℚ)⁻¹) ^ (e + f) := by
  classical
  let v := ((a : ZMod p).val, (d : ZMod p).val)
  let B : ℚ := ((p - 1) / (p - 2) : ℚ) * p ^ 2 * ((p : ℚ)⁻¹) ^ (e + f)
  have hpq : (3 : ℚ) ≤ p := by exact_mod_cast hp
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg (div_nonneg (by linarith) (by linarith))
      (sq_nonneg _)) (by positivity)
  calc
    _ ≤ ∑ bc ∈ branchPairs p, if bc = v then B else 0 := by
      apply sum_le_sum
      intro bc hbc
      by_cases hv : bc = v
      · simpa only [if_pos hv] using directFraction_le p E e f hp hE he hf pure a d bc hbc
      · rw [if_neg hv, directFraction_zero p E e f he0 hf0 pure a d bc hbc hv]
    _ ≤ B := by
      simp only [sum_ite_eq']
      split_ifs <;> first | exact le_rfl | exact hB

/-- Sample an ordered nonzero branch pair uniformly, then the two surviving
lifts independently. This is the probability of an oriented signature. -/
noncomputable def orderedProbability (p E e f : ℕ) [NeZero p]
    (pure : ℕ → ℤ) (a d : ℤ) : ℚ :=
  (∑ bc ∈ branchPairs p, directFraction p E e f pure a d bc) / (branchPairs p).card

theorem ordered_probability_le (p E e f : ℕ) [NeZero p] (hp : 3 ≤ p)
    (hE : 1 ≤ E) (he0 : 0 < e) (hf0 : 0 < f) (he : e ≤ E) (hf : f ≤ E)
    (pure : ℕ → ℤ) (a d : ℤ) :
    orderedProbability p E e f pure a d ≤
      (p : ℚ) ^ 2 * ((p : ℚ)⁻¹) ^ (e + f) / (p - 2) ^ 2 := by
  have hpq : (3 : ℚ) ≤ p := by exact_mod_cast hp
  have hsum := sum_directFraction_le p E e f hp hE he0 hf0 he hf pure a d
  unfold orderedProbability
  apply (div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)).trans_eq
  rw [branchPairs_card p (by omega), Nat.cast_mul,
    Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_sub (by omega : 2 ≤ p)]
  norm_num only [Nat.cast_one, Nat.cast_ofNat]
  field_simp [show (p : ℚ) - 1 ≠ 0 by linarith,
    show (p : ℚ) - 2 ≠ 0 by linarith]

/-- The event allowing either orientation of the prescribed constraints. -/
noncomputable def unorderedFraction (p E e f : ℕ) [NeZero p] (pure : ℕ → ℤ)
    (a d : ℤ) (bc : ℕ × ℕ) : ℚ :=
  let S := branchGood p E pure bc.1
  let T := branchGood p E pure bc.2
  (((S ×ˢ T).filter (fun x =>
    (x.1 ∈ cylinder p E e a ∧ x.2 ∈ cylinder p E f d) ∨
    (x.1 ∈ cylinder p E f d ∧ x.2 ∈ cylinder p E e a))).card : ℚ) /
      (S ×ˢ T).card

lemma unorderedFraction_le (p E e f : ℕ) [NeZero p] (pure : ℕ → ℤ)
    (a d : ℤ) (bc : ℕ × ℕ) :
    unorderedFraction p E e f pure a d bc ≤
      directFraction p E e f pure a d bc + directFraction p E f e pure d a bc := by
  classical
  unfold unorderedFraction directFraction
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [← Nat.cast_add]
  apply Nat.cast_le.mpr
  rw [filter_or]
  exact card_union_le _ _

noncomputable def unorderedProbability (p E e f : ℕ) [NeZero p]
    (pure : ℕ → ℤ) (a d : ℤ) : ℚ :=
  (∑ bc ∈ branchPairs p, unorderedFraction p E e f pure a d bc) / (branchPairs p).card

/-- Exact finite two-stage sampling supplies the factor for a prescribed
unordered first-digit pair. No independence between core events is assumed. -/
theorem unordered_probability_le (p E e f : ℕ) [NeZero p] (hp : 3 ≤ p)
    (hE : 1 ≤ E) (he0 : 0 < e) (hf0 : 0 < f) (he : e ≤ E) (hf : f ≤ E)
    (pure : ℕ → ℤ) (a d : ℤ) :
    unorderedProbability p E e f pure a d ≤
      2 * (p : ℚ) ^ 2 * ((p : ℚ)⁻¹) ^ (e + f) / (p - 2) ^ 2 := by
  have hsum : unorderedProbability p E e f pure a d ≤
      orderedProbability p E e f pure a d + orderedProbability p E f e pure d a := by
    unfold unorderedProbability orderedProbability
    rw [← add_div, ← sum_add_distrib]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact sum_le_sum (fun bc _ => unorderedFraction_le p E e f pure a d bc)
  have h₁ := ordered_probability_le p E e f hp hE he0 hf0 he hf pure a d
  have h₂ := ordered_probability_le p E f e hp hE hf0 he0 hf he pure d a
  rw [Nat.add_comm f e] at h₂
  apply hsum.trans ((add_le_add h₁ h₂).trans_eq _)
  ring

/-- At depth one the whole surviving branch lies in its first-digit cylinder.
There is no higher-pure conditioning loss in this special case. -/
lemma directFraction_first_level (p E : ℕ) [NeZero p] (hp : 3 ≤ p)
    (hE : 1 ≤ E) (pure : ℕ → ℤ) (a d : ℤ)
    (bc : ℕ × ℕ) (hbc : bc ∈ branchPairs p) :
    directFraction p E 1 1 pure a d bc =
      if bc = ((a : ZMod p).val, (d : ZMod p).val) then 1 else 0 := by
  classical
  by_cases hv : bc = ((a : ZMod p).val, (d : ZMod p).val)
  · rw [if_pos hv]
    have hvp (t : ℤ) : (p : ℤ) ∣ ((t : ZMod p).val : ℤ) - t := by
      apply (ZMod.intCast_eq_intCast_iff_dvd_sub t ((t : ZMod p).val : ℤ) p).mp
      simp
    have hfilter : ((branchGood p E pure bc.1 ×ˢ branchGood p E pure bc.2).filter
        (fun x => x.1 ∈ cylinder p E 1 a ∧ x.2 ∈ cylinder p E 1 d)) =
        branchGood p E pure bc.1 ×ˢ branchGood p E pure bc.2 := by
      apply filter_eq_self.mpr
      intro x hx
      obtain ⟨hx, hy⟩ := mem_product.mp hx
      have hx' := ((mem_branchGood p E pure bc.1 x.1).mp hx).1
      have hy' := ((mem_branchGood p E pure bc.2 x.2).mp hy).1
      have ha := hvp a
      have hd := hvp d
      rw [hv] at hx' hy'
      simp only [mem_cylinder, pow_one]
      constructor
      · convert dvd_add hx' ha using 1
        ring
      · convert dvd_add hy' hd using 1
        ring
    unfold directFraction
    dsimp only
    rw [hfilter]
    apply div_self
    exact_mod_cast (branchGood_nonempty p E hp hE pure bc.1 |>.product
      (branchGood_nonempty p E hp hE pure bc.2)).card_pos.ne'
  · rw [if_neg hv]
    exact directFraction_zero p E 1 1 (by decide) (by decide) pure a d bc hbc hv

theorem ordered_probability_first_level (p E : ℕ) [NeZero p] (hp : 3 ≤ p)
    (hE : 1 ≤ E) (pure : ℕ → ℤ) (a d : ℤ)
    (hpair : ((a : ZMod p).val, (d : ZMod p).val) ∈ branchPairs p) :
    orderedProbability p E 1 1 pure a d = 1 / (branchPairs p).card := by
  classical
  unfold orderedProbability
  have hsum : (∑ bc ∈ branchPairs p, directFraction p E 1 1 pure a d bc) =
      ∑ bc ∈ branchPairs p,
        if bc = ((a : ZMod p).val, (d : ZMod p).val) then (1 : ℚ) else 0 := by
    apply sum_congr rfl
    exact fun bc hbc => directFraction_first_level p E hp hE pure a d bc hbc
  rw [hsum, sum_ite_eq', if_pos hpair]

/-- With different target first digits, the two orientations are disjoint. -/
lemma unorderedFraction_eq_sum (p E e f : ℕ) [NeZero p]
    (he : 0 < e) (hf : 0 < f) (pure : ℕ → ℤ) (a d : ℤ)
    (had : (a : ZMod p) ≠ (d : ZMod p)) (bc : ℕ × ℕ) :
    unorderedFraction p E e f pure a d bc =
      directFraction p E e f pure a d bc + directFraction p E f e pure d a bc := by
  classical
  unfold unorderedFraction directFraction
  dsimp only
  rw [filter_or, card_union_of_disjoint, Nat.cast_add, add_div]
  apply disjoint_left.mpr
  intro x hx hy
  have ha := (mem_cylinder p E e a x.1).mp (mem_filter.mp hx).2.1
  have hd := (mem_cylinder p E f d x.1).mp (mem_filter.mp hy).2.1
  exact had ((Erdos7PrimePowerMinimalEvent.first_digit_of_power he ha).symm.trans
    (Erdos7PrimePowerMinimalEvent.first_digit_of_power hf hd))

/-- For two different nonzero first-digit targets, the unordered depth-one
probability is exactly the reciprocal of the number of unordered pairs. -/
theorem unordered_probability_first_level (p E : ℕ) [NeZero p] (hp : 3 ≤ p)
    (hE : 1 ≤ E) (pure : ℕ → ℤ) (a d : ℤ)
    (hpair : ((a : ZMod p).val, (d : ZMod p).val) ∈ branchPairs p) :
    unorderedProbability p E 1 1 pure a d = 2 / (branchPairs p).card := by
  have hh := mem_branchPairs.mp hpair
  have hpair' : ((d : ZMod p).val, (a : ZMod p).val) ∈ branchPairs p :=
    mem_branchPairs.mpr ⟨hh.2.2.1, hh.2.2.2.1, hh.1, hh.2.1, hh.2.2.2.2.symm⟩
  have had : (a : ZMod p) ≠ (d : ZMod p) :=
    fun h => hh.2.2.2.2 (congrArg ZMod.val h)
  have heq : unorderedProbability p E 1 1 pure a d =
      orderedProbability p E 1 1 pure a d + orderedProbability p E 1 1 pure d a := by
    unfold unorderedProbability orderedProbability
    simp_rw [unorderedFraction_eq_sum p E 1 1 (by decide) (by decide) pure a d had]
    rw [sum_add_distrib, add_div]
  rw [heq, ordered_probability_first_level p E hp hE pure a d hpair,
    ordered_probability_first_level p E hp hE pure d a hpair']
  ring

/-- Finite two-stage product sampling tensorizes exactly. First choose the
branch indices uniformly, then the lifts uniformly in the corresponding
product of finite sets. Different branch choices can have different numbers
of lifts, and those conditional denominators are retained. -/
theorem two_stage_product_formula {I : Type*} [Fintype I] [DecidableEq I]
    {K A : I → Type*} [∀ i, DecidableEq (K i)] [∀ i, DecidableEq (A i)]
    (T : (i : I) → Finset (K i))
    (S B : (i : I) → K i → Finset (A i)) :
    (∑ k ∈ Fintype.piFinset T,
      (((Fintype.piFinset (fun i => S i (k i))).filter
        (fun x => ∀ i, x i ∈ B i (k i))).card : ℚ) /
        (Fintype.piFinset (fun i => S i (k i))).card) /
      (Fintype.piFinset T).card =
    ∏ i, (∑ k ∈ T i, ((S i k ∩ B i k).card : ℚ) / (S i k).card) / (T i).card := by
  classical
  simp_rw [Erdos7IndependentLiftSampling.product_hit_fraction]
  rw [← prod_univ_sum T (fun i k => ((S i k ∩ B i k).card : ℚ) / (S i k).card),
    Fintype.card_piFinset, Nat.cast_prod, prod_div_distrib]

noncomputable def pairTarget (p E e f : ℕ) [NeZero p] (a d : ℤ) :
    Finset (ZMod (p ^ E) × ZMod (p ^ E)) :=
  (cylinder p E e a ×ˢ cylinder p E f d) ∪ (cylinder p E f d ×ˢ cylinder p E e a)

/-- Actual finite probability for a prescribed signature at all coordinates.
This sums over branch choices and uses the appropriate conditional lift
cardinality for each choice. -/
noncomputable def signatureProductProbability {I : Type*} [Fintype I] [DecidableEq I]
    (p E e f : I → ℕ) [∀ i, NeZero (p i)]
    (pure : I → ℕ → ℤ) (a d : I → ℤ) : ℚ :=
  let T := fun i => branchPairs (p i)
  let S := fun i (bc : ℕ × ℕ) =>
    branchGood (p i) (E i) (pure i) bc.1 ×ˢ branchGood (p i) (E i) (pure i) bc.2
  (∑ k ∈ Fintype.piFinset T,
    (((Fintype.piFinset (fun i => S i (k i))).filter
      (fun x => ∀ i, x i ∈ pairTarget (p i) (E i) (e i) (f i) (a i) (d i))).card : ℚ) /
      (Fintype.piFinset (fun i => S i (k i))).card) / (Fintype.piFinset T).card

theorem signature_product_probability_eq {I : Type*} [Fintype I] [DecidableEq I]
    (p E e f : I → ℕ) [∀ i, NeZero (p i)]
    (pure : I → ℕ → ℤ) (a d : I → ℤ) :
    signatureProductProbability p E e f pure a d =
      ∏ i, unorderedProbability (p i) (E i) (e i) (f i) (pure i) (a i) (d i) := by
  classical
  unfold signatureProductProbability
  dsimp only
  rw [two_stage_product_formula (fun i => branchPairs (p i))
    (fun i (bc : ℕ × ℕ) => branchGood (p i) (E i) (pure i) bc.1 ×ˢ
      branchGood (p i) (E i) (pure i) bc.2)
    (fun i _ => pairTarget (p i) (E i) (e i) (f i) (a i) (d i))]
  apply prod_congr rfl
  intro i _
  unfold unorderedProbability
  congr 1
  apply sum_congr rfl
  intro bc _
  unfold unorderedFraction
  dsimp only
  rw [← filter_mem_eq_inter]
  simp only [pairTarget, mem_union, mem_product]

/-- Product bound for a fixed compatible unordered signature. This is not a
bound on a union over signatures, which remain correlated events. -/
theorem signature_product_probability_le {I : Type*} [Fintype I] [DecidableEq I]
    (p E e f : I → ℕ) [∀ i, NeZero (p i)] (hp : ∀ i, 3 ≤ p i)
    (hE : ∀ i, 1 ≤ E i) (he0 : ∀ i, 0 < e i) (hf0 : ∀ i, 0 < f i)
    (he : ∀ i, e i ≤ E i) (hf : ∀ i, f i ≤ E i)
    (pure : I → ℕ → ℤ) (a d : I → ℤ) :
    signatureProductProbability p E e f pure a d ≤
      ∏ i, 2 * (p i : ℚ) ^ 2 * ((p i : ℚ)⁻¹) ^ (e i + f i) / (p i - 2) ^ 2 := by
  rw [signature_product_probability_eq]
  apply prod_le_prod
  · intro i _
    unfold unorderedProbability unorderedFraction
    positivity
  · intro i _
    exact unordered_probability_le (p i) (E i) (e i) (f i) (hp i) (hE i)
      (he0 i) (hf0 i) (he i) (hf i) (pure i) (a i) (d i)

#print axioms directFraction_zero
#print axioms ordered_probability_le
#print axioms unordered_probability_le
#print axioms ordered_probability_first_level
#print axioms unordered_probability_first_level
#print axioms two_stage_product_formula
#print axioms signature_product_probability_eq
#print axioms signature_product_probability_le
end Erdos7UniformBranchSignature
