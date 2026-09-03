import Submission.RecursiveEnvelopeShape

/-! Finite alternating Buchstab refinement of an arbitrary upper-sieve source.
The main terms and error budgets are kept separately. This file proves algebraic
monotonicity and sound one-node propagation, not a uniform asymptotic estimate. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset

/-- The level is multiplied by the marginal when a hit is required. The `keep`
test may discard any lower branch; it must be retained in the cost recursion. -/
noncomputable def lowerStep (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (U : ℕ → ℝ → ℝ) (k : ℕ) (D : ℝ) : ℝ := by
  classical
  exact if keep k D then max 0 (1-∑ i : Fin k, q i.val * U i.val (D*q i.val)) else 0

noncomputable def lowerErrorStep (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (E : ℕ → ℝ → ℝ) (k : ℕ) (D : ℝ) : ℝ := by
  classical
  exact if keep k D then 1+∑ i : Fin k, E i.val (D*q i.val) else 0

noncomputable def upperMain (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (base : ℕ → ℝ → ℝ) : ℕ → ℕ → ℝ → ℝ
  | 0 => base
  | n+1 => fun k D => min (upperMain q keep base n k D)
      (1-∑ i : Fin k, q i.val *
        lowerStep q keep (upperMain q keep base n) i.val (D*q i.val))

noncomputable def upperError (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (base : ℕ → ℝ → ℝ) : ℕ → ℕ → ℝ → ℝ
  | 0 => base
  | n+1 => fun k D => max (upperError q keep base n k D)
      (1+∑ i : Fin k,
        lowerErrorStep q keep (upperError q keep base n) i.val (D*q i.val))

lemma lowerStep_nonneg (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (U : ℕ → ℝ → ℝ) (k : ℕ) (D : ℝ) : 0 ≤ lowerStep q keep U k D := by
  classical
  unfold lowerStep
  split_ifs
  · exact le_max_left _ _
  · rfl

lemma lowerErrorStep_nonneg (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (E : ℕ → ℝ → ℝ) (hE : ∀ k D, 0 ≤ E k D) (k : ℕ) (D : ℝ) :
    0 ≤ lowerErrorStep q keep E k D := by
  classical
  unfold lowerErrorStep
  split_ifs
  · exact add_nonneg (by norm_num) (sum_nonneg (fun i _ => hE _ _))
  · rfl

lemma upperError_nonneg (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (base : ℕ → ℝ → ℝ) (hbase : ∀ k D, 0 ≤ base k D) (n k : ℕ) (D : ℝ) :
    0 ≤ upperError q keep base n k D := by
  induction n with
  | zero => exact hbase k D
  | succ n ih => exact ih.trans (le_max_left _ _)

/-- Refinement never increases an upper main term. -/
lemma upperMain_succ_le (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (base : ℕ → ℝ → ℝ) (n k : ℕ) (D : ℝ) :
    upperMain q keep base (n+1) k D ≤ upperMain q keep base n k D := min_le_left _ _

lemma lowerStep_antitone (q : ℕ → ℝ) (hq : ∀ i, 0 ≤ q i)
    (keep : ℕ → ℝ → Prop) (U V : ℕ → ℝ → ℝ) (hUV : ∀ k D, U k D ≤ V k D)
    (k : ℕ) (D : ℝ) : lowerStep q keep V k D ≤ lowerStep q keep U k D := by
  classical
  unfold lowerStep
  split_ifs
  · apply max_le_max_left
    apply sub_le_sub_left
    exact sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hUV _ _) (hq i.val))
  · rfl

lemma lowerStep_succ_ge (q : ℕ → ℝ) (hq : ∀ i, 0 ≤ q i)
    (keep : ℕ → ℝ → Prop) (base : ℕ → ℝ → ℝ) (n k : ℕ) (D : ℝ) :
    lowerStep q keep (upperMain q keep base n) k D ≤
      lowerStep q keep (upperMain q keep base (n+1)) k D :=
  lowerStep_antitone q hq keep _ _ (upperMain_succ_le q keep base n) k D

/-- Density bounds for the independent reference population are invariant
under the alternating refinement, regardless of the lower-branch cutoff. -/
theorem main_density_bounds (q : ℕ → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (keep : ℕ → ℝ → Prop) (base : ℕ → ℝ → ℝ)
    (hbase : ∀ k D, prefixDensity q k ≤ base k D) (n k : ℕ) (D : ℝ) :
    lowerStep q keep (upperMain q keep base n) k D ≤ prefixDensity q k ∧
      prefixDensity q k ≤ upperMain q keep base n k D := by
  classical
  have hlow (U : ℕ → ℝ → ℝ) (hU : ∀ k D, prefixDensity q k ≤ U k D) :
      ∀ k D, lowerStep q keep U k D ≤ prefixDensity q k := by
    intro k D
    have hd := prefixDensity_nonneg q k (fun i _ => hq i)
    unfold lowerStep
    split_ifs
    · apply max_le hd
      rw [prefixDensity_first_hit q k]
      apply sub_le_sub_left
      exact sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hU _ _) (hq i.val).1)
    · exact hd
  have hu : ∀ n k D, prefixDensity q k ≤ upperMain q keep base n k D := by
    intro n
    induction n with
    | zero => exact hbase
    | succ n ih =>
      intro k D
      apply le_min (ih k D)
      have hl := hlow (upperMain q keep base n) ih
      rw [prefixDensity_first_hit q k]
      apply sub_le_sub_left
      exact sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hl _ _) (hq i.val).1)
  exact ⟨hlow _ (hu n) k D, hu n k D⟩

/-- One lower step: the root unit error and every upper-child error are charged.
Clipping its main term at zero is sound only because the population is nonnegative. -/
theorem lowerStep_sound (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (U E : ℕ → ℝ → ℝ) (hE : ∀ k D, 0 ≤ E k D)
    (k : ℕ) (D X S M : ℝ) (C : Fin k → ℝ)
    (hX : 0 ≤ X) (hS : 0 ≤ S) (hid : S = M-∑ i, C i)
    (hM : X-1 ≤ M)
    (hC : ∀ i, C i ≤ (X*q i.val)*U i.val (D*q i.val)+E i.val (D*q i.val)) :
    X*lowerStep q keep U k D-lowerErrorStep q keep E k D ≤ S := by
  classical
  have hs := sum_le_sum (s := univ) (fun i _ => hC i)
  have he : (∑ i : Fin k, ((X*q i.val)*U i.val (D*q i.val)+E i.val (D*q i.val))) =
      X*(∑ i : Fin k, q i.val*U i.val (D*q i.val)) +
        ∑ i : Fin k, E i.val (D*q i.val) := by
    rw [sum_add_distrib, mul_sum]
    congr 1
    exact sum_congr rfl (fun _ _ => mul_assoc _ _ _)
  rw [he] at hs
  unfold lowerStep lowerErrorStep
  split_ifs with hk
  · by_cases ha : 0 ≤ 1-∑ i : Fin k, q i.val*U i.val (D*q i.val)
    · rw [max_eq_right ha]
      nlinarith only [hs, hM, hid]
    · rw [max_eq_left (le_of_not_ge ha)]
      have hne : 0 ≤ ∑ i : Fin k, E i.val (D*q i.val) := sum_nonneg (fun i _ => hE _ _)
      nlinarith only [hS, hne]
  · simpa using hS

/-- One upper step: using the smaller main term is sound with the larger of the
two error budgets. This avoids concealing the errors in the main-term minimum. -/
theorem upperStep_sound (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (U E : ℕ → ℝ → ℝ) (k : ℕ) (D X S M : ℝ) (C : Fin k → ℝ)
    (hX : 0 ≤ X) (hid : S = M-∑ i, C i) (hM : M ≤ X+1)
    (hOld : S ≤ X*U k D+E k D)
    (hC : ∀ i, (X*q i.val)*lowerStep q keep U i.val (D*q i.val)-
      lowerErrorStep q keep E i.val (D*q i.val) ≤ C i) :
    S ≤ X*min (U k D) (1-∑ i : Fin k, q i.val*lowerStep q keep U i.val (D*q i.val))+
      max (E k D) (1+∑ i : Fin k, lowerErrorStep q keep E i.val (D*q i.val)) := by
  have hs := sum_le_sum (s := univ) (fun i _ => hC i)
  have he : (∑ i : Fin k, ((X*q i.val)*lowerStep q keep U i.val (D*q i.val)-
      lowerErrorStep q keep E i.val (D*q i.val))) =
      X*(∑ i : Fin k, q i.val*lowerStep q keep U i.val (D*q i.val))-
        ∑ i : Fin k, lowerErrorStep q keep E i.val (D*q i.val) := by
    rw [sum_sub_distrib, mul_sum]
    congr 1
    exact sum_congr rfl (fun _ _ => mul_assoc _ _ _)
  rw [he] at hs
  have hnew : S ≤ X*(1-∑ i : Fin k, q i.val*lowerStep q keep U i.val (D*q i.val))+
      (1+∑ i : Fin k, lowerErrorStep q keep E i.val (D*q i.val)) := by
    nlinarith only [hs,hM,hid]
  by_cases h : U k D ≤ 1-∑ i : Fin k, q i.val*lowerStep q keep U i.val (D*q i.val)
  · rw [min_eq_left h]
    exact hOld.trans (add_le_add le_rfl (le_max_left _ _))
  · rw [min_eq_right (le_of_not_ge h)]
    exact hnew.trans (add_le_add le_rfl (le_max_right _ _))

#print axioms main_density_bounds
#print axioms lowerStep_sound
#print axioms upperStep_sound
end Erdos970.RecursiveSieve.Buchstab
