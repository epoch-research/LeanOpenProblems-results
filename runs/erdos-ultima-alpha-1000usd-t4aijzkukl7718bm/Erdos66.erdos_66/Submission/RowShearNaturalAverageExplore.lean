import Submission.FirstRowFixingShearExplore
import Submission.OuterCarryProfileExplore

/-! Spatial carry averages for first-row-preserving shears, including the
actual first natural transition window. These are averages, not a simultaneous
selection theorem for all targets. -/
namespace Erdos66RowShearNaturalAverage
open Erdos66OriginRepair Erdos66PrefixFaithfulParabolaLift
  Erdos66FirstRowFixingShear Erdos66IntegerBlock Erdos66OuterCarryProfile
open AdditiveCombinatorics
open scoped Classical
set_option maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime]

lemma lower_weightedPair (A B : Finset (ZMod p)) (t : ℕ) :
    (lower p A B t : ℝ) =
      weightedPair A B (t : ZMod p) (fun x ↦ if x.val ≤ t then 1 else 0) := by
  unfold weightedPair
  have he (a c : ZMod p) : a+c=(t : ZMod p) ↔ c=(t : ZMod p)-a := by
    constructor <;> intro h <;> linear_combination h
  simp_rw [he]
  simp only [Finset.sum_ite_eq']
  rw [lower_zmod]
  push_cast
  calc
    _ = ∑ a : ZMod p,
        if a ∈ A then (if (t : ZMod p)-a ∈ B then (if a.val ≤ t then (1 : ℝ) else 0)
          else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases h1 : a.val ≤ t <;> by_cases h2 : a ∈ A <;>
        by_cases h3 : (t : ZMod p)-a ∈ B <;> simp [h1,h2,h3]
    _ = _ := by simp

lemma lower_comm (A B : Finset (ZMod p)) (t : ℕ) (ht : t < p) :
    lower p A B t = lower p B A t := by
  have he (a c : ZMod p) (hac : a+c=(t : ZMod p)) : a.val ≤ t ↔ c.val ≤ t := by
    have htc : (t : ZMod p).val = t := ZMod.val_natCast_of_lt ht
    constructor
    · intro ha
      have hc : c=(t : ZMod p)-a := by linear_combination hac
      rw [hc,ZMod.val_sub (by omega),htc]
      omega
    · intro hc
      have ha : a=(t : ZMod p)-c := by linear_combination hac
      rw [ha,ZMod.val_sub (by omega),htc]
      omega
  suffices hh : (lower p A B t : ℝ) = (lower p B A t : ℝ) by exact_mod_cast hh
  rw [lower_weightedPair,lower_weightedPair,weightedPair,weightedPair,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro c hc
  rw [add_comm c a]
  by_cases hac : a+c=(t : ZMod p)
  · simp only [hac,if_true,he a c hac]
  · simp only [hac,if_false]

lemma lower_row_shear_average (A B : Finset (ZMod p)) (y v : ZMod p)
    (hs : y+v ≠ 0) (t : ℕ) :
    (∑ b : ZMod p, (lower p (shiftSet A (b*y)) (shiftSet B (b*v)) t : ℝ)) =
      ∑ a ∈ A, ∑ c ∈ B,
        if ((v*a-y*c+y*(t : ZMod p))/(y+v)).val ≤ t then 1 else 0 := by
  simp_rw [lower_weightedPair]
  exact weighted_row_shear_average A B y v (t : ZMod p) hs _

lemma lower_retained_row_average (A B : Finset (ZMod p)) (v : ZMod p)
    (hv : v ≠ 0) (t : ℕ) :
    (∑ b : ZMod p, (lower p A (shiftSet B (b*v)) t : ℝ)) =
      (B.card : ℝ) * ((A.filter (fun a ↦ a.val ≤ t)).card : ℝ) := by
  simp_rw [lower_weightedPair]
  rw [retained_row_weighted_average A B v (t : ZMod p) hv]
  congr 1
  rw [Finset.card_filter]
  push_cast
  rfl

noncomputable def twoRows (A B : Finset (ZMod p)) (b : ZMod p) (k : ℕ) :
    Finset (ZMod p) := if k=0 then A else if k=1 then shiftSet B b else ∅

lemma twoRows_first_prefix (A B : Finset (ZMod p)) (b : ZMod p) (n : ℕ) (hn : n < p) :
    n ∈ blockSet p (twoRows p A B b) ↔ (n : ZMod p) ∈ A := by
  change ((n : ZMod p) ∈ twoRows p A B b (n/p)) ↔ _
  simp [twoRows,Nat.div_eq_of_lt hn]

lemma twoRows_first_window (A B : Finset (ZMod p)) (b : ZMod p)
    (t : ℕ) (ht : t < p) :
    sumRep (blockSet p (twoRows p A B b)) (p+t) =
      2*lower p A (shiftSet B b) t + upper p A A t := by
  have hh := block_formula p (twoRows p A B b) 1 t ht
  simp only [one_mul,Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty,
    zero_add,twoRows,ite_true,Nat.sub_zero,Nat.sub_self,zero_ne_one,ite_false,
    one_ne_zero] at hh
  rw [lower_comm p (shiftSet B b) A t ht] at hh
  omega

/-- Exact averaged ordinary count in [p,2p), with the old upper carry
untouched. This is generally not a constant profile. -/
theorem first_window_average (A B : Finset (ZMod p)) (t : ℕ) (ht : t < p) :
    (∑ b : ZMod p, (sumRep (blockSet p (twoRows p A B b)) (p+t) : ℝ)) =
      2*(B.card : ℝ)*((A.filter (fun a ↦ a.val ≤ t)).card : ℝ) +
        (p : ℝ)*upper p A A t := by
  simp_rw [twoRows_first_window p A B _ t ht]
  push_cast
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  have hh := lower_retained_row_average p A B 1 one_ne_zero t
  simp only [mul_one] at hh
  rw [hh]
  simp [mul_assoc]

end Erdos66RowShearNaturalAverage
