import Submission.UniformBranchSignature

/-! Bounds on the actual minimal-core event, not merely a chosen activity
predicate. Representatives are fixed clauses with different first digits.
There is still no bound on the union over all possible cores/signatures. -/
namespace Erdos7MinimalCoreProbability
open scoped BigOperators
open Finset Erdos7PresentCylinderArithmetic Erdos7IndependentPureLifts
open Erdos7PrimePowerMinimalEvent Erdos7UniformBranchSignature
set_option autoImplicit false
set_option maxHeartbeats 2000000

lemma two_targets_orientation (p e f : ℕ) (he : 0 < e) (hf : 0 < f)
    (a d : ℤ) (had : (a : ZMod p) ≠ (d : ZMod p)) (z : Fin 2 → ℤ)
    (ha : ∃ r, ((p ^ e : ℕ) : ℤ) ∣ z r - a)
    (hd : ∃ r, ((p ^ f : ℕ) : ℤ) ∣ z r - d) :
    (((p ^ e : ℕ) : ℤ) ∣ z 0 - a ∧ ((p ^ f : ℕ) : ℤ) ∣ z 1 - d) ∨
      (((p ^ f : ℕ) : ℤ) ∣ z 0 - d ∧ ((p ^ e : ℕ) : ℤ) ∣ z 1 - a) := by
  obtain ⟨r, hr⟩ := ha
  obtain ⟨t, ht⟩ := hd
  have hne : r ≠ t := by
    intro h
    subst t
    exact had ((first_digit_of_power he hr).symm.trans (first_digit_of_power hf ht))
  fin_cases r <;> fin_cases t
  · exact (hne rfl).elim
  · exact Or.inl ⟨hr, ht⟩
  · exact Or.inr ⟨ht, hr⟩
  · exact (hne rfl).elim

/-- Minimality forces each representative to have an actual point on the
selected cube. Two representatives in different first-digit branches must
therefore be hit in opposite positions of the sampled pair. -/
theorem minimal_event_forces_unordered_targets {I J : Type*}
    (p : I → ℕ) (S : J → Finset I) (e : J → I → ℕ)
    (he : ∀ j i, i ∈ S j → 0 < e j i) (a : J → I → ℤ)
    (s : Finset J) (k : I → Fin 2 → J)
    (hk : ∀ i r, k i r ∈ s ∧ i ∈ S (k i r))
    (hdiff : ∀ i, (a (k i 0) i : ZMod (p i)) ≠ (a (k i 1) i : ZMod (p i)))
    (z : I → Fin 2 → ℤ)
    (h : SectionMinimal (fun _ : I => ℤ) S
      (fun j i => {x | ((p i ^ e j i : ℕ) : ℤ) ∣ x - a j i}) s z) :
    ∀ i,
      ((((p i ^ e (k i 0) i : ℕ) : ℤ) ∣ z i 0 - a (k i 0) i) ∧
        (((p i ^ e (k i 1) i : ℕ) : ℤ) ∣ z i 1 - a (k i 1) i)) ∨
      ((((p i ^ e (k i 1) i : ℕ) : ℤ) ∣ z i 0 - a (k i 1) i) ∧
        (((p i ^ e (k i 0) i : ℕ) : ℤ) ∣ z i 1 - a (k i 0) i)) := by
  intro i
  have hactive (r : Fin 2) : ∃ t,
      ((p i ^ e (k i r) i : ℕ) : ℤ) ∣ z i t - a (k i r) i := by
    obtain ⟨x, hx⟩ := h.2 (k i r) (hk i r).1
    exact ⟨x i, ((hx (k i r) (hk i r).1).mpr rfl) i (hk i r).2⟩
  exact two_targets_orientation (p i) (e (k i 0) i) (e (k i 1) i)
    (he _ i (hk i 0).2) (he _ i (hk i 1).2) _ _ (hdiff i) (z i)
    (hactive 0) (hactive 1)

noncomputable def selectPair {I : Type*} (p E : I → ℕ)
    (x : (i : I) → ZMod (p i ^ E i) × ZMod (p i ^ E i)) (i : I) (r : Fin 2) : ℤ :=
  if r = 0 then (x i).1.val else (x i).2.val

/-- The actual probability that this fixed subfamily minimally covers the
sampled product. Ambient coordinates should be restricted to the used set
when applying the representative theorem below. -/
noncomputable def coreProbability {I J : Type*} [Fintype I] [DecidableEq I]
    (p E : I → ℕ) [∀ i, NeZero (p i)] (pure : I → ℕ → ℤ)
    (S : J → Finset I) (e : J → I → ℕ) (a : J → I → ℤ) (s : Finset J) : ℚ := by
  classical
  let T := fun i => branchPairs (p i)
  let U := fun i (bc : ℕ × ℕ) =>
    branchGood (p i) (E i) (pure i) bc.1 ×ˢ branchGood (p i) (E i) (pure i) bc.2
  exact (∑ k ∈ Fintype.piFinset T,
    (((Fintype.piFinset (fun i => U i (k i))).filter
      (fun x => SectionMinimal (fun _ : I => ℤ) S
        (fun j i => {y | ((p i ^ e j i : ℕ) : ℤ) ∣ y - a j i}) s
          (selectPair p E x))).card : ℚ) /
      (Fintype.piFinset (fun i => U i (k i))).card) / (Fintype.piFinset T).card

/-- Bound on a genuine minimal-core event by its representative signature.
Maximal depth and compatibility are unnecessary for this upper bound: taking
deepest representatives is what makes the bound stronger. -/
theorem core_probability_le_signature {I J : Type*} [Fintype I] [DecidableEq I]
    (p E : I → ℕ) [∀ i, NeZero (p i)] (pure : I → ℕ → ℤ)
    (S : J → Finset I) (e : J → I → ℕ)
    (he : ∀ j i, i ∈ S j → 0 < e j i) (a : J → I → ℤ)
    (s : Finset J) (k : I → Fin 2 → J)
    (hk : ∀ i r, k i r ∈ s ∧ i ∈ S (k i r))
    (hdiff : ∀ i, (a (k i 0) i : ZMod (p i)) ≠ (a (k i 1) i : ZMod (p i))) :
    coreProbability p E pure S e a s ≤
      signatureProductProbability p E (fun i => e (k i 0) i) (fun i => e (k i 1) i)
        pure (fun i => a (k i 0) i) (fun i => a (k i 1) i) := by
  classical
  unfold coreProbability signatureProductProbability
  dsimp only
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro bc hbc
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr
  apply card_le_card
  intro x hx
  have hh := minimal_event_forces_unordered_targets p S e he a s k hk hdiff
    (selectPair p E x) (mem_filter.mp hx).2
  refine mem_filter.mpr ⟨(mem_filter.mp hx).1, ?_⟩
  intro i
  simpa only [pairTarget, mem_union, mem_product, mem_cylinder, selectPair,
    if_pos rfl, show (1 : Fin 2) ≠ 0 by decide, if_false] using hh i

/-- The finite experiment therefore bounds each fixed core by a product of
two-deepest-constraint weights. It does not sum over different cores. -/
theorem core_probability_le {I J : Type*} [Fintype I] [DecidableEq I]
    (p E : I → ℕ) [∀ i, NeZero (p i)] (hp : ∀ i, 3 ≤ p i) (hE : ∀ i, 1 ≤ E i)
    (pure : I → ℕ → ℤ) (S : J → Finset I) (e : J → I → ℕ)
    (he : ∀ j i, i ∈ S j → 0 < e j i) (hbound : ∀ j i, e j i ≤ E i)
    (a : J → I → ℤ) (s : Finset J) (k : I → Fin 2 → J)
    (hk : ∀ i r, k i r ∈ s ∧ i ∈ S (k i r))
    (hdiff : ∀ i, (a (k i 0) i : ZMod (p i)) ≠ (a (k i 1) i : ZMod (p i))) :
    coreProbability p E pure S e a s ≤
      ∏ i, 2 * (p i : ℚ) ^ 2 * ((p i : ℚ)⁻¹) ^ (e (k i 0) i + e (k i 1) i) /
        (p i - 2) ^ 2 := by
  apply (core_probability_le_signature p E pure S e he a s k hk hdiff).trans
  exact signature_product_probability_le p E _ _ hp hE
    (fun i => he _ i (hk i 0).2) (fun i => he _ i (hk i 1).2)
    (fun i => hbound _ i) (fun i => hbound _ i) pure _ _

#print axioms minimal_event_forces_unordered_targets
#print axioms core_probability_le_signature
#print axioms core_probability_le
end Erdos7MinimalCoreProbability
