import Submission.AllowedProjectionBounds

/-! Exact five-cell geometry after removing pure3 and pure9, with all higher
pure powers also removed. These statements do not settle the covering problem. -/
namespace Erdos7FiveCellGeometry
open scoped BigOperators
open Erdos7PureProjectionLower Erdos7ArithmeticProjectionLower Erdos7AllowedProjectionBounds
set_option autoImplicit false
set_option maxHeartbeats 2000000

def allowed (r : ZMod 3) (s : ZMod 9) : Finset (ZMod 9) :=
  Finset.univ.filter (fun x => (x.val : ZMod 3) ≠ r ∧ x ≠ s)

def shortBranch (r : ZMod 3) (s : ZMod 9) : Finset (ZMod 9) :=
  (allowed r s).filter (fun x => (x.val : ZMod 3) = (s.val : ZMod 3))

lemma finite_cardinalities (r : ZMod 3) (s : ZMod 9)
    (h : (s.val : ZMod 3) ≠ r) :
    (allowed r s).card = 5 ∧ (shortBranch r s).card = 2 := by
  have hh : ∀ r : ZMod 3, ∀ s : ZMod 9, (s.val : ZMod 3) ≠ r →
      (allowed r s).card = 5 ∧ (shortBranch r s).card = 2 := by decide +kernel
  exact hh r s h

noncomputable def cellWeight (E : ℕ) (a : ℕ → ℤ) (r : ZMod 9) : ℝ :=
  let U := Finset.univ \ pureUnion (fun j => cylinder 3 E j (a j)) E
  mass (uniform 3 E) (cylinder 3 E 2 (r.val : ℤ) ∩ U) / mass (uniform 3 E) U

lemma cylinder_two_fiber (E : ℕ) (U : Finset (ZMod (3^E))) (r : ZMod 9) :
    cylinder 3 E 2 (r.val : ℤ) ∩ U = U.filter (fun x => (x.val : ZMod 9) = r) := by
  ext x
  simp only [cylinder,Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and,
    Nat.reducePow,Int.cast_natCast,ZMod.natCast_zmod_val]
  exact and_comm

lemma cellWeight_mass (E : ℕ) (a : ℕ → ℤ)
    (hU : 0 < mass (uniform 3 E)
      (Finset.univ \ pureUnion (fun j => cylinder 3 E j (a j)) E)) :
    (∑ r : ZMod 9, cellWeight E a r) = 1 := by
  let U := Finset.univ \ pureUnion (fun j => cylinder 3 E j (a j)) E
  unfold cellWeight
  rw [← Finset.sum_div]
  have he : (∑ r : ZMod 9, mass (uniform 3 E) (cylinder 3 E 2 (r.val : ℤ) ∩ U)) =
      mass (uniform 3 E) U := by
    simp only [cylinder_two_fiber,mass]
    exact Finset.sum_fiberwise U (fun x => (x.val : ZMod 9)) (uniform 3 E)
  change (∑ r : ZMod 9, mass (uniform 3 E) (cylinder 3 E 2 (r.val : ℤ) ∩ U)) / _ = 1
  rw [he,div_self (ne_of_gt hU)]

lemma cellWeight_zero (E : ℕ) (hE : 2 ≤ E) (a : ℕ → ℤ) (r : ZMod 9)
    (hr : r ∉ allowed (a 1 : ZMod 3) (a 2 : ZMod 9)) : cellWeight E a r = 0 := by
  have hbad : (r.val : ZMod 3) = (a 1 : ZMod 3) ∨ r = (a 2 : ZMod 9) := by
    simpa only [allowed,Finset.mem_filter,Finset.mem_univ,true_and,not_and_or,not_not] using hr
  have hsub : cylinder 3 E 2 (r.val : ℤ) ⊆ pureUnion (fun j => cylinder 3 E j (a j)) E := by
    intro x hx
    have hx9 := (mem_cylinder 3 E 2 (r.val : ℤ) x).mp hx
    norm_num only [Nat.reducePow,Nat.cast_ofNat] at hx9
    rcases hbad with h₁ | h₂
    · have hr3 : (3:ℤ) ∣ (r.val:ℤ)-a 1 := by
        apply (ZMod.intCast_eq_intCast_iff_dvd_sub (a 1) (r.val:ℤ) 3).mp
        simpa only [Int.cast_natCast] using h₁.symm
      have hx3 : (3:ℤ) ∣ (x.val:ℤ)-a 1 := by
        have hh := dvd_add ((show (3:ℤ) ∣ 9 by norm_num).trans hx9) hr3
        convert hh using 1 <;> ring
      apply Finset.mem_biUnion.mpr
      refine ⟨0,Finset.mem_range.mpr (by omega),?_⟩
      apply (mem_cylinder 3 E 1 (a 1) x).mpr
      simpa only [pow_one,Nat.cast_ofNat] using hx3
    · have hr9 : (9:ℤ) ∣ (r.val:ℤ)-a 2 := by
        apply (ZMod.intCast_eq_intCast_iff_dvd_sub (a 2) (r.val:ℤ) 9).mp
        simpa only [Int.cast_natCast,ZMod.natCast_zmod_val] using h₂.symm
      have hx9' : (9:ℤ) ∣ (x.val:ℤ)-a 2 := by
        have hh := dvd_add hx9 hr9
        convert hh using 1 <;> ring
      apply Finset.mem_biUnion.mpr
      refine ⟨1,Finset.mem_range.mpr (by omega),?_⟩
      apply (mem_cylinder 3 E 2 (a 2) x).mpr
      simpa only [Nat.reducePow,Nat.cast_ofNat] using hx9'
  have he : cylinder 3 E 2 (r.val : ℤ) ∩
      (Finset.univ \ pureUnion (fun j => cylinder 3 E j (a j)) E) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx).2).2 (hsub (Finset.mem_inter.mp hx).1)
  simp only [cellWeight,he,mass,Finset.sum_empty,zero_div]

lemma cellWeight_bounds (E : ℕ) (hE : 2 ≤ E) (a : ℕ → ℤ)
    (hdis : ∀ i j, 1 ≤ i → i ≤ E → 1 ≤ j → j ≤ E → i ≠ j →
      Disjoint (cylinder 3 E i (a i)) (cylinder 3 E j (a j)))
    (r : ZMod 9) (hr : r ∈ allowed (a 1 : ZMod 3) (a 2 : ZMod 9)) :
    1/9 ≤ cellWeight E a r ∧ cellWeight E a r ≤ 2/9 := by
  obtain ⟨hr₁,hr₂⟩ := (Finset.mem_filter.mp hr).2
  apply ternary_cell_bounds E hE a (r.val : ℤ) hdis
  · intro hd
    have hh := (ZMod.intCast_eq_intCast_iff_dvd_sub (a 1) (r.val:ℤ) 3).mpr hd
    apply hr₁
    simpa only [Int.cast_natCast] using hh.symm
  · intro hd
    have hh := (ZMod.intCast_eq_intCast_iff_dvd_sub (a 2) (r.val:ℤ) 9).mpr hd
    apply hr₂
    simpa only [Int.cast_natCast,ZMod.natCast_zmod_val] using hh.symm

/-- Purely geometric consequence of five cell masses in[1/9,2/9]: the branch
containing only two surviving cells has mass in[1/3,4/9]. -/
theorem short_branch_bounds (r : ZMod 3) (s : ZMod 9) (hsep : (s.val : ZMod 3) ≠ r)
    (w : ZMod 9 → ℝ) (hw : ∀ x ∈ allowed r s, 1/9 ≤ w x ∧ w x ≤ 2/9)
    (hm : ∑ x ∈ allowed r s, w x = 1) :
    1/3 ≤ ∑ x ∈ shortBranch r s, w x ∧ ∑ x ∈ shortBranch r s, w x ≤ 4/9 := by
  have hcard := finite_cardinalities r s hsep
  have hsub : shortBranch r s ⊆ allowed r s := Finset.filter_subset _ _
  have hupper : ∑ x ∈ shortBranch r s, w x ≤ 4/9 := by
    calc
      _ ≤ ∑ _x ∈ shortBranch r s, (2/9:ℝ) := Finset.sum_le_sum (fun x hx => (hw x (hsub hx)).2)
      _ = _ := by simp only [Finset.sum_const,hcard.2,nsmul_eq_mul]; norm_num
  have hc : ((allowed r s) \ shortBranch r s).card = 3 := by
    rw [Finset.card_sdiff_of_subset hsub,hcard.1,hcard.2]
  have hcupper : ∑ x ∈ (allowed r s) \ shortBranch r s, w x ≤ 2/3 := by
    calc
      _ ≤ ∑ _x ∈ (allowed r s) \ shortBranch r s, (2/9:ℝ) :=
        Finset.sum_le_sum (fun x hx => (hw x (Finset.mem_sdiff.mp hx).1).2)
      _ = _ := by simp only [Finset.sum_const,hc,nsmul_eq_mul]; norm_num
  have hsum := Finset.sum_sdiff (f := w) hsub
  rw [hm] at hsum
  exact ⟨by linarith,hupper⟩

/-- Complete five-cell conditional law, uniform in the upper ternary exponent.
The residue separation is precisely that of the disjoint pure3 and pure9 classes. -/
theorem five_cell_law (E : ℕ) (hE : 2 ≤ E) (a : ℕ → ℤ)
    (hdis : ∀ i j, 1 ≤ i → i ≤ E → 1 ≤ j → j ≤ E → i ≠ j →
      Disjoint (cylinder 3 E i (a i)) (cylinder 3 E j (a j)))
    (hsep : ((a 2 : ZMod 9).val : ZMod 3) ≠ (a 1 : ZMod 3)) :
    let A := allowed (a 1 : ZMod 3) (a 2 : ZMod 9)
    let S := shortBranch (a 1 : ZMod 3) (a 2 : ZMod 9)
    A.card = 5 ∧ S.card = 2 ∧ (∑ r ∈ A, cellWeight E a r) = 1 ∧
      (∀ r ∈ A, 1/9 ≤ cellWeight E a r ∧ cellWeight E a r ≤ 2/9) ∧
      1/3 ≤ ∑ r ∈ S, cellWeight E a r ∧ ∑ r ∈ S, cellWeight E a r ≤ 4/9 := by
  dsimp only
  have hc := finite_cardinalities (a 1 : ZMod 3) (a 2 : ZMod 9) hsep
  have hhalf := (allowed_cylinder_bounds 3 E 0 (by decide) a 0 (by omega) hdis
    (by intro j hj hj0; omega)).1
  have hpos : 0 < mass (uniform 3 E)
      (Finset.univ \ pureUnion (fun j => cylinder 3 E j (a j)) E) := by linarith
  have hmass : (∑ r ∈ allowed (a 1 : ZMod 3) (a 2 : ZMod 9), cellWeight E a r) = 1 := by
    rw [← cellWeight_mass E a hpos]
    exact Finset.sum_subset (Finset.subset_univ _) (fun r _ hr => cellWeight_zero E hE a r hr)
  have hb := cellWeight_bounds E hE a hdis
  exact ⟨hc.1,hc.2,hmass,hb,
    short_branch_bounds (a 1 : ZMod 3) (a 2 : ZMod 9) hsep (cellWeight E a) hb hmass⟩

#print axioms finite_cardinalities
#print axioms cellWeight_mass
#print axioms cellWeight_zero
#print axioms cellWeight_bounds
#print axioms short_branch_bounds
#print axioms five_cell_law
end Erdos7FiveCellGeometry
