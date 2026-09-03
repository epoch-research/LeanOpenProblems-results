import FormalConjecturesUtil

/-! A partition obstruction for a pair/fourth-moment surrogate. These finite
weight inequalities are auxiliary; no odd covering theorem is asserted. -/
namespace Erdos7OrderedWeightBarrier
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {I : Type*} [DecidableEq I]

/-- Total product weight of ordered samples without replacement. -/
def orderedMass (w : I → ℚ) (S : Finset I) : ℕ → ℚ
  | 0 => 1
  | k+1 => ∑ i ∈ S, w i * orderedMass w (S.erase i) k

def falling (s h : ℚ) : ℕ → ℚ
  | 0 => 1
  | k+1 => s * falling (s-h) h k

lemma orderedMass_nonneg (w : I → ℚ) (S : Finset I) (hw : ∀ i ∈ S, 0 ≤ w i) (k : ℕ) :
    0 ≤ orderedMass w S k := by
  induction k generalizing S with
  | zero => simp [orderedMass]
  | succ k ih =>
    exact Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi)
      (ih (S.erase i) (fun j hj => hw j (Finset.mem_erase.mp hj).2)))

lemma falling_nonneg (h : ℚ) (hh : 0 ≤ h) (k : ℕ) (s : ℚ) (hs : (k:ℚ)*h ≤ s) :
    0 ≤ falling s h k := by
  induction k generalizing s with
  | zero => simp [falling]
  | succ k ih =>
    have hsk : (k:ℚ)*h ≤ s-h := by push_cast at hs; linarith
    have hsz : 0 ≤ s := le_trans (mul_nonneg (Nat.cast_nonneg _) hh) hs
    exact mul_nonneg hsz (ih (s-h) hsk)

/-- At most h mass is lost at each draw. The bound is for arbitrary finite
nonnegative weights, not independent or identically distributed samples. -/
theorem orderedMass_lower (w : I → ℚ) (h : ℚ) (hh : 0 ≤ h) (k : ℕ)
    (S : Finset I) (hw : ∀ i ∈ S, 0 ≤ w i ∧ w i ≤ h)
    (s : ℚ) (hs : (k:ℚ)*h ≤ s) (hmass : s ≤ ∑ i ∈ S,w i) :
    falling s h k ≤ orderedMass w S k := by
  induction k generalizing S s with
  | zero => simp [falling,orderedMass]
  | succ k ih =>
    have hsk : (k:ℚ)*h ≤ s-h := by push_cast at hs; linarith
    have hl (i : I) (hi : i ∈ S) : falling (s-h) h k ≤ orderedMass w (S.erase i) k := by
      apply ih (S.erase i) (fun j hj => hw j (Finset.mem_erase.mp hj).2) (s-h) hsk
      have he := Finset.sum_erase_add S w hi
      linarith [(hw i hi).2]
    have hf := falling_nonneg h hh k (s-h) hsk
    calc
      falling s h (k+1) = s*falling (s-h) h k := rfl
      _ ≤ (∑ i ∈ S,w i)*falling (s-h) h k := mul_le_mul_of_nonneg_right hmass hf
      _ = ∑ i ∈ S,w i*falling (s-h) h k := Finset.sum_mul _ _ _
      _ ≤ orderedMass w S (k+1) :=
        Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hl i hi) (hw i hi).1)

lemma pair_lower (w : I → ℚ) (S : Finset I)
    (hw : ∀ i ∈ S, 0 ≤ w i ∧ w i ≤ 1/2)
    (hs : 5/2 ≤ ∑ i ∈ S,w i) : 5 ≤ orderedMass w S 2 := by
  have hh := orderedMass_lower w (1/2) (by norm_num) 2 S hw (5/2) (by norm_num) hs
  norm_num [falling] at hh
  exact hh

lemma fourth_lower (w : I → ℚ) (S : Finset I)
    (hw : ∀ i ∈ S, 0 ≤ w i ∧ w i ≤ 1/2)
    (hs : 5/2 ≤ ∑ i ∈ S,w i) : 15/2 ≤ orderedMass w S 4 := by
  have hh := orderedMass_lower w (1/2) (by norm_num) 4 S hw (5/2) (by norm_num) hs
  norm_num [falling] at hh
  exact hh

/-- A nonnegative budget dominating one quarter of the inactive ordered-pair
mass plus one quarter of the active ordered-fourth mass cannot be below one
when the total prime weight is at least five. Arithmetic domination of a
specific orbit budget is a separate hypothesis, not assumed silently. -/
theorem partition_barrier [Fintype I] (w : I → ℚ)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1/2) (A : Finset I)
    (hs : 5 ≤ ∑ i,w i) (B : ℚ)
    (hb : orderedMass w (Finset.univ \ A) 2 / 4 + orderedMass w A 4 / 4 ≤ B) :
    5/4 ≤ B := by
  have hsplit := Finset.sum_sdiff (f := w) (Finset.subset_univ A)
  have hpair0 := orderedMass_nonneg w (Finset.univ \ A) (fun i _ => (hw i).1) 2
  have hfourth0 := orderedMass_nonneg w A (fun i _ => (hw i).1) 4
  by_cases hA : 5/2 ≤ ∑ i ∈ A,w i
  · have hh := fourth_lower w A (fun i _ => hw i) hA
    linarith
  · have hU : 5/2 ≤ ∑ i ∈ Finset.univ \ A,w i := by linarith
    have hh := pair_lower w (Finset.univ \ A) (fun i _ => hw i) hU
    linarith

/-- If every parent intersection costs at most half its child event, the
forest correction leaves at least half the total event weight. -/
theorem forest_half_lower [Fintype I] (w : I → ℚ) (hw : ∀ i,0 ≤ w i)
    (parent : I → Option I) (edge : I → I → ℚ)
    (he : ∀ i j,parent i = some j → edge i j ≤ w i / 2) :
    (∑ i,w i)/2 ≤ (∑ i,w i) - ∑ i,(parent i).elim 0 (edge i) := by
  have hl : (∑ i,(parent i).elim 0 (edge i)) ≤ ∑ i,w i/2 := by
    apply Finset.sum_le_sum
    intro i _
    cases hp : parent i with
    | none => simp only [Option.elim_none]; exact div_nonneg (hw i) (by norm_num)
    | some j => exact he i j hp
  rw [← Finset.sum_div] at hl
  linarith

#print axioms partition_barrier
#print axioms forest_half_lower
end Erdos7OrderedWeightBarrier
