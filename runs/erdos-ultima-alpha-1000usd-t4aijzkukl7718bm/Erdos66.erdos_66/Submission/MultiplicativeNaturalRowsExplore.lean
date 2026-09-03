import Submission.MultiplicativeRowsExplore
import Submission.PhasedResidueCountingExplore
import Submission.CompactnessExplore

/-! Exact natural carry formulas and deterministic prefix masses for
multiplicative rows. No weighted-count asymptotic is assumed or proved here. -/
namespace Erdos66MultiplicativeNaturalRows
open Erdos66MultiplicativeRows Erdos66IntegerBlock Erdos66Counting
  Erdos66PhasedResidueCounting AdditiveCombinatorics
open scoped Classical
set_option maxHeartbeats 1800000
variable {p : ℕ} [Fact p.Prime]

lemma sum_range_cast (f : ZMod p → ℕ) :
    (∑ x∈Finset.range p, f ((x:ℕ):ZMod p))=∑ x : ZMod p, f x := by
  apply Finset.sum_bij (fun (x : ℕ) _ ↦ (x:ZMod p))
  · intro x hx
    exact Finset.mem_univ _
  · intro x hx y hy he
    have hh := congrArg ZMod.val he
    simpa only [ZMod.val_natCast_of_lt (Finset.mem_range.mp hx),
      ZMod.val_natCast_of_lt (Finset.mem_range.mp hy)] using hh
  · intro x hx
    exact ⟨x.val,Finset.mem_range.mpr x.val_lt,ZMod.natCast_zmod_val x⟩
  · intro x hx
    rfl

lemma lower_as_filter (C D : Finset (ZMod p)) (t : ℕ) :
    lower p C D t=(C.filter (fun x ↦ x.val≤t ∧ (t:ZMod p)-x∈D)).card := by
  unfold lower
  calc
    _ = ∑ x∈Finset.range p, if ((x:ℕ):ZMod p).val≤t ∧ (x:ZMod p)∈C ∧
        (t:ZMod p)-x∈D then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp hx)]
    _ = ∑ x : ZMod p, if x.val≤t ∧ x∈C ∧ (t:ZMod p)-x∈D then 1 else 0 :=
      by
      convert sum_range_cast (p:=p) (fun x ↦ if x.val≤t ∧ x∈C ∧ (t:ZMod p)-x∈D then 1 else 0) using 1
    _ = _ := by
      rw [←Finset.card_filter]
      congr 1
      ext x
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      tauto

lemma upper_as_filter (C D : Finset (ZMod p)) (t : ℕ) :
    upper p C D t=(C.filter (fun x ↦ t<x.val ∧ (t:ZMod p)-x∈D)).card := by
  unfold upper
  calc
    _ = ∑ x∈Finset.range p, if t<((x:ℕ):ZMod p).val ∧ (x:ZMod p)∈C ∧
        (t:ZMod p)-x∈D then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp hx)]
    _ = ∑ x : ZMod p, if t<x.val ∧ x∈C ∧ (t:ZMod p)-x∈D then 1 else 0 :=
      by
      convert sum_range_cast (p:=p) (fun x ↦ if t<x.val ∧ x∈C ∧ (t:ZMod p)-x∈D then 1 else 0) using 1
    _ = _ := by
      rw [←Finset.card_filter]
      congr 1
      ext x
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      tauto

noncomputable def lowerParameter (U V : Finset (ZMod p)) (a y z : ZMod p) (t : ℕ) : ℕ :=
  if y+1=0 ∨ z+1=0 then 0 else
    (U.filter (fun u ↦ (rowMap a y u).val≤t ∧ linearSolution a y z (t:ZMod p) u∈V)).card

noncomputable def upperParameter (U V : Finset (ZMod p)) (a y z : ZMod p) (t : ℕ) : ℕ :=
  if y+1=0 ∨ z+1=0 then 0 else
    (U.filter (fun u ↦ t<(rowMap a y u).val ∧ linearSolution a y z (t:ZMod p) u∈V)).card

lemma lower_rows (U V : Finset (ZMod p)) (a y z : ZMod p) (t : ℕ) :
    lower p (row U a y) (row V a z) t=lowerParameter U V a y z t := by
  rw [lower_as_filter]
  by_cases hy : y+1=0
  · simp [row,hy,lowerParameter]
  by_cases hz : z+1=0
  · simp [row,hz,lowerParameter]
  rw [lowerParameter,if_neg (by tauto)]
  convert filtered_row_count U V a y z (t:ZMod p) hy hz (fun x ↦ x.val≤t) using 1 <;>
    congr 1 <;> ext x <;> simp only [Finset.mem_filter]

lemma upper_rows (U V : Finset (ZMod p)) (a y z : ZMod p) (t : ℕ) :
    upper p (row U a y) (row V a z) t=upperParameter U V a y z t := by
  rw [upper_as_filter]
  by_cases hy : y+1=0
  · simp [row,hy,upperParameter]
  by_cases hz : z+1=0
  · simp [row,hz,upperParameter]
  rw [upperParameter,if_neg (by tauto)]
  convert filtered_row_count U V a y z (t:ZMod p) hy hz (fun x ↦ t<x.val) using 1 <;>
    congr 1 <;> ext x <;> simp only [Finset.mem_filter]

noncomputable def naturalSet (U : ℕ → Finset (ZMod p)) (a : ZMod p) : Set ℕ :=
  blockSet p (fun k ↦ row (U k) a (k:ZMod p))

lemma natural_prefix (U : ℕ → Finset (ZMod p)) (a : ZMod p)
    (n : ℕ) (hn : n<p) : n∈naturalSet U a ↔ (n:ZMod p)∈U 0 := by
  change (n:ZMod p)∈row (U (n/p)) a ((n/p:ℕ):ZMod p) ↔ _
  rw [Nat.div_eq_of_lt hn]
  simp only [Nat.cast_zero,row_zero]

lemma natural_representation_prefix (U : ℕ → Finset (ZMod p)) (a : ZMod p)
    (n : ℕ) (hn : n<p) :
    sumRep (naturalSet U a) n=sumRep {k : ℕ | k<p ∧ (k:ZMod p)∈U 0} n := by
  apply Erdos66Compactness.sumRep_congr_below
  intro k hk
  have hkp : k<p := by omega
  rw [natural_prefix U a k hkp]
  simp only [Set.mem_setOf_eq,hkp,true_and]

/-- Both ordinary carries are explicit; the formula is a sum of restricted
weighted linear counts of the chosen old parameter sets. -/
theorem natural_formula (U : ℕ → Finset (ZMod p)) (a : ZMod p)
    (q t : ℕ) (ht : t<p) :
    sumRep (naturalSet U a) (q*p+t)=
      (∑ k∈Finset.range (q+1), lowerParameter (U k) (U (q-k)) a
        (k:ZMod p) ((q-k:ℕ):ZMod p) t)+
      ∑ k∈Finset.range q, upperParameter (U k) (U (q-k-1)) a
        (k:ZMod p) ((q-k-1:ℕ):ZMod p) t := by
  rw [naturalSet,block_formula p _ q t ht]
  simp_rw [lower_rows,upper_rows]

/-- Unlike the earlier parabolic taper, row mass is exact for each fixed
translation, not just after averaging over translations. -/
theorem prefix_mass (U : ℕ → Finset (ZMod p)) (a : ZMod p) (N : ℕ) :
    count (naturalSet U a) (N*p)=
      ∑ k∈Finset.range N, if (k:ZMod p)+1=0 then 0 else (U k).card := by
  rw [naturalSet,count_blocks]
  apply Finset.sum_congr rfl
  intro k hk
  convert row_card (U k) a (k:ZMod p) using 1
  split_ifs <;> rfl

lemma small_row_nonsingular (k : ℕ) (hk : k+1<p) : (k:ZMod p)+1≠0 := by
  intro he
  have hv := congrArg ZMod.val he
  rw [show (k:ZMod p)+1=((k+1:ℕ):ZMod p) by simp,
    ZMod.val_natCast_of_lt hk,ZMod.val_zero] at hv
  omega

theorem prefix_mass_before_singular (U : ℕ → Finset (ZMod p)) (a : ZMod p)
    (N : ℕ) (hN : N<p) :
    count (naturalSet U a) (N*p)=∑ k∈Finset.range N, (U k).card := by
  rw [prefix_mass]
  apply Finset.sum_congr rfl
  intro k hk
  rw [if_neg (small_row_nonsingular k (by have := Finset.mem_range.mp hk; omega))]

end Erdos66MultiplicativeNaturalRows
