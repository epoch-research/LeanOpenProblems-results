import Submission.BuchstabRefinement

/-! Soundness of finite Buchstab refinement for arbitrary nonnegative weighted
populations with unit intersection errors and a valid upper-sieve source. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset

section Population
variable {α : Type*} (A : Finset α) (w : α → ℝ) (ω : α → ℕ → Bool)
    (q : ℕ → ℝ) (x D : ℝ) (K : ℕ) (keep : ℕ → ℝ → Prop)
    (base cost : ℕ → ℝ → ℝ)

/-- The required-hit product rescales both the expected population and the
available divisor level. The base upper estimate is an explicit hypothesis. -/
theorem refinement_sound (hw : ∀ a ∈ A, 0 ≤ w a) (hq : ∀ i, 0 ≤ q i)
    (hx : 0 ≤ x) (hcost : ∀ k d, 0 ≤ cost k d)
    (hmoment : ∀ T : Finset ℕ, T ⊆ range K →
      |moment A w ω T-x*∏ i ∈ T, q i| ≤ 1)
    (hbase : ∀ k ≤ K, ∀ T : Finset ℕ, T ⊆ range K →
      (∀ i ∈ T, k ≤ i) → sifted A w ω T k ≤
        (x*∏ i ∈ T, q i)*base k (D*∏ i ∈ T, q i)+cost k (D*∏ i ∈ T, q i))
    (n k : ℕ) (hk : k ≤ K) (T : Finset ℕ) (hTK : T ⊆ range K)
    (hT : ∀ i ∈ T, k ≤ i) :
    (x*∏ i ∈ T, q i)*lowerStep q keep (upperMain q keep base n) k (D*∏ i ∈ T, q i)-
        lowerErrorStep q keep (upperError q keep cost n) k (D*∏ i ∈ T, q i) ≤
      sifted A w ω T k ∧
    sifted A w ω T k ≤
      (x*∏ i ∈ T, q i)*upperMain q keep base n k (D*∏ i ∈ T, q i)+
        upperError q keep cost n k (D*∏ i ∈ T, q i) := by
  classical
  have hsub (k : ℕ) (hk : k ≤ K) (T : Finset ℕ) (hTK : T ⊆ range K) (i : Fin k) :
      insert i.val T ⊆ range K := by
    apply insert_subset (mem_range.mpr (i.isLt.trans_le hk)) hTK
  have hsep (k : ℕ) (T : Finset ℕ) (hT : ∀ j ∈ T, k ≤ j) (i : Fin k) :
      ∀ j ∈ insert i.val T, i.val ≤ j := by
    intro j hj
    rcases mem_insert.mp hj with rfl | hj
    · rfl
    · exact i.isLt.le.trans (hT j hj)
  have hprod (k : ℕ) (T : Finset ℕ) (hT : ∀ j ∈ T, k ≤ j) (i : Fin k) :
      (∏ j ∈ insert i.val T, q j) = (∏ j ∈ T, q j)*q i.val := by
    rw [prod_insert (show i.val ∉ T from fun hi => (not_lt_of_ge (hT i.val hi)) i.isLt)]
    ring
  have hX (T : Finset ℕ) : 0 ≤ x*∏ i ∈ T, q i :=
    mul_nonneg hx (prod_nonneg (fun i _ => hq i))
  have lower_of_upper (n : ℕ)
      (hU : ∀ k ≤ K, ∀ T : Finset ℕ, T ⊆ range K → (∀ i ∈ T, k ≤ i) →
        sifted A w ω T k ≤ (x*∏ i ∈ T, q i)*upperMain q keep base n k (D*∏ i ∈ T, q i)+
          upperError q keep cost n k (D*∏ i ∈ T, q i)) :
      ∀ k ≤ K, ∀ T : Finset ℕ, T ⊆ range K → (∀ i ∈ T, k ≤ i) →
        (x*∏ i ∈ T, q i)*lowerStep q keep (upperMain q keep base n) k (D*∏ i ∈ T, q i)-
          lowerErrorStep q keep (upperError q keep cost n) k (D*∏ i ∈ T, q i) ≤ sifted A w ω T k := by
    intro k hk T hTK hT
    apply lowerStep_sound q keep (upperMain q keep base n) (upperError q keep cost n)
      (upperError_nonneg q keep cost hcost n) k (D*∏ i ∈ T, q i)
      (x*∏ i ∈ T, q i) (sifted A w ω T k) (moment A w ω T)
      (fun i => sifted A w ω (insert i.val T) i.val)
      (hX T) (sifted_nonneg A w ω hw T k) (sifted_first_hit A w ω T k)
    · linarith [(abs_le.mp (hmoment T hTK)).1]
    · intro i
      have hh := hU i.val (i.isLt.le.trans hk) (insert i.val T)
        (hsub k hk T hTK i) (hsep k T hT i)
      simpa only [hprod k T hT i, mul_assoc] using hh
  have hu : ∀ n k, k ≤ K → ∀ T : Finset ℕ, T ⊆ range K → (∀ i ∈ T, k ≤ i) →
      sifted A w ω T k ≤ (x*∏ i ∈ T, q i)*upperMain q keep base n k (D*∏ i ∈ T, q i)+
        upperError q keep cost n k (D*∏ i ∈ T, q i) := by
    intro n
    induction n with
    | zero => exact hbase
    | succ n ih =>
      have hl := lower_of_upper n ih
      intro k hk T hTK hT
      change sifted A w ω T k ≤
        (x*∏ i ∈ T, q i)*min (upperMain q keep base n k (D*∏ i ∈ T, q i))
          (1-∑ i : Fin k, q i.val*lowerStep q keep (upperMain q keep base n)
            i.val ((D*∏ i ∈ T, q i)*q i.val))+
        max (upperError q keep cost n k (D*∏ i ∈ T, q i))
          (1+∑ i : Fin k, lowerErrorStep q keep (upperError q keep cost n)
            i.val ((D*∏ i ∈ T, q i)*q i.val))
      apply upperStep_sound q keep (upperMain q keep base n) (upperError q keep cost n)
        k (D*∏ i ∈ T, q i) (x*∏ i ∈ T, q i) (sifted A w ω T k) (moment A w ω T)
        (fun i => sifted A w ω (insert i.val T) i.val) (hX T)
        (sifted_first_hit A w ω T k)
      · linarith [(abs_le.mp (hmoment T hTK)).2]
      · exact ih k hk T hTK hT
      · intro i
        have hh := hl i.val (i.isLt.le.trans hk) (insert i.val T)
          (hsub k hk T hTK i) (hsep k T hT i)
        simpa only [hprod k T hT i, mul_assoc] using hh
  exact ⟨lower_of_upper n (hu n) k hk T hTK hT, hu n k hk T hTK hT⟩

/-- Positivity after ALL propagated errors, rather than positivity of the main
profile alone, forces an actual survivor in the weighted population. -/
theorem survivor_of_refinement (hw : ∀ a ∈ A, 0 ≤ w a) (hq : ∀ i, 0 ≤ q i)
    (hx : 0 ≤ x) (hcost : ∀ k d, 0 ≤ cost k d)
    (hmoment : ∀ T : Finset ℕ, T ⊆ range K →
      |moment A w ω T-x*∏ i ∈ T, q i| ≤ 1)
    (hbase : ∀ k ≤ K, ∀ T : Finset ℕ, T ⊆ range K → (∀ i ∈ T, k ≤ i) →
      sifted A w ω T k ≤ (x*∏ i ∈ T, q i)*base k (D*∏ i ∈ T, q i)+cost k (D*∏ i ∈ T, q i))
    (n : ℕ) (hpos : lowerErrorStep q keep (upperError q keep cost n) K D <
      x*lowerStep q keep (upperMain q keep base n) K D) :
    ∃ a ∈ A, ∀ i < K, ω a i = false := by
  classical
  have hb := (refinement_sound A w ω q x D K keep base cost hw hq hx hcost hmoment hbase
    n K le_rfl ∅ (empty_subset _) (by simp)).1
  simp only [prod_empty, mul_one] at hb
  have hp : 0 < sifted A w ω ∅ K := lt_of_lt_of_le (sub_pos.mpr hpos) hb
  by_contra hn
  push_neg at hn
  have hz : sifted A w ω ∅ K = 0 := by
    apply sum_eq_zero
    intro a ha
    obtain ⟨i, hi, hω⟩ := hn a ha
    have hbad : ¬∀ i < K, ω a i = false := fun h => hω (h i hi)
    simp [avoid, hbad]
  rw [hz] at hp
  exact lt_irrefl _ hp

end Population
#print axioms refinement_sound
#print axioms survivor_of_refinement
end Erdos970.RecursiveSieve.Buchstab
