import Submission.TernaryTwoSharedComparison

/-! The flat-current endpoint of the ternary-two root comparison. Together
with the full-current comparison this permits positive current mixtures. -/
namespace Erdos7TernaryTwoFlatComparison
open scoped BigOperators
open Erdos7TernaryTwoSharedPrefix Erdos7TernaryTwoSharedComparison
set_option maxHeartbeats 2000000
variable {J : Type*} [Fintype J]

noncomputable def actualWeight (r : J → ℝ) : Fin 5 ⊕ (J × Fin 5) → ℝ :=
  Sum.elim (fun _ => 11/100) (fun z => r z.1/5)
noncomputable def refWeight (r : J → ℝ) : Fin 3 ⊕ (J × Fin 3) → ℝ :=
  Sum.elim (fun n => 11*(starWeight n : ℝ)/100)
    (fun z => r z.1*(starWeight z.2 : ℝ)/5)

lemma actual_nonneg (r : J → ℝ) (hr : ∀ j,0≤r j) : ∀ z,0≤actualWeight r z := by
  intro z; cases z with
  | inl x => norm_num [actualWeight]
  | inr z => exact div_nonneg (hr _) (by norm_num)

lemma ref_nonneg (r : J → ℝ) (hr : ∀ j,0≤r j) : ∀ z,0≤refWeight r z := by
  intro z; cases z with
  | inl x => dsimp [refWeight]; positivity
  | inr z => exact div_nonneg (mul_nonneg (hr _) (Nat.cast_nonneg _)) (by norm_num)

lemma mass_eq (r : J → ℝ) : (∑ z,actualWeight r z)=∑ z,refWeight r z := by
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,actualWeight,refWeight,Sum.elim_inl,Sum.elim_inr]
  congr 1
  · norm_num [starWeight,Fin.sum_univ_succ]
  · apply Finset.sum_congr rfl
    intro j _
    norm_num [starWeight,Fin.sum_univ_succ]
    ring

lemma actual_hinge (a : ℕ → Fin 10) (r : J → ℝ) (d : J → ℕ) (t : ℕ) :
    (∑ z,actualWeight r z*((actualCount a d z-t : ℕ) : ℝ)) =
      (11/20)*prefixHinge a 1 t+∑ j,r j*prefixHinge a (d j) t := by
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,actualWeight,actualCount,Sum.elim_inl,Sum.elim_inr]
  congr 1
  · simp only [prefixHinge,prefixCount,Finset.sum_range_one]
    rw [← Finset.mul_sum]
    ring
  · apply Finset.sum_congr rfl
    intro j _
    unfold prefixHinge
    rw [← Finset.mul_sum]
    ring

lemma ref_hinge (r : J → ℝ) (d : J → ℕ) (t : ℕ) :
    (∑ z,refWeight r z*((refCount d z-t : ℕ) : ℝ)) =
      (11/20)*Erdos7TernaryTwoSharedPrefix.star 1 t +
      ∑ j,r j*Erdos7TernaryTwoSharedPrefix.star (d j) t := by
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,refWeight,refCount,Sum.elim_inl,Sum.elim_inr]
  congr 1
  · rw [← star_hinge]
    simp only [one_mul,Finset.sum_div,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  · apply Finset.sum_congr rfl
    intro j _
    rw [← star_hinge,Finset.sum_div,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring

lemma hinge_bound (a : ℕ → Fin 10) (r : J → ℝ) (d : J → ℕ)
    (hr : ∀ j,0≤r j) (hd : ∀ j,0<d j) (t : ℕ) :
    (∑ z,actualWeight r z*((actualCount a d z-t : ℕ) : ℝ)) ≤
      ∑ z,refWeight r z*((refCount d z-t : ℕ) : ℝ) := by
  rw [actual_hinge,ref_hinge]
  exact add_le_add (mul_le_mul_of_nonneg_left (prefix_hinge_le a 1 t (by omega)) (by norm_num))
    (Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (prefix_hinge_le a (d j) t (hd j)) (hr j)))

/-- Flat-current comparison with exact mass and nonnegative atoms. The test
may be signed and may belong to any independently selected future family. -/
theorem convex_comparison (a : ℕ → Fin 10) (r : J → ℝ) (d : J → ℕ)
    (hr : ∀ j,0≤r j) (hd : ∀ j,0<d j)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ) :
    (∑ z,actualWeight r z*φ (actualCount a d z)) ≤
      ∑ z,refWeight r z*φ (refCount d z) := by
  classical
  let D := 1+∑ j,d j
  have hD : 1≤D := by dsimp [D]; omega
  have hjD (j : J) : d j≤D := by
    have hh : d j ≤ ∑ k,d k := Finset.single_le_sum (fun k _ => Nat.zero_le _) (Finset.mem_univ j)
    dsimp [D]; omega
  have hX : ∀ z,actualCount a d z ≤ 3*D := by
    intro z; cases z with
    | inl x => exact (data.1 (a 0) x).2.trans (by omega)
    | inr z => exact (prefix_upper a (d z.1) z.2).trans (Nat.mul_le_mul_left _ (hjD _))
  have hY : ∀ z,refCount d z ≤ 3*D := by
    intro z; cases z with
    | inl x => dsimp [refCount]; omega
    | inr z =>
      dsimp [refCount]
      calc
        _ ≤ d z.1*3 := Nat.mul_le_mul_left _ (by omega)
        _ ≤ 3*D := by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left 3 (hjD z.1)
  have hmean : (∑ z,actualWeight r z*(actualCount a d z : ℝ)) ≤
      ∑ z,refWeight r z*(refCount d z : ℝ) := by
    simpa only [Nat.sub_zero] using hinge_bound a r d hr hd 0
  have hh := Erdos7FiniteHingeComparison.convex_monotone_comparison
    (actualWeight r) (refWeight r) (actualCount a d) (refCount d) (3*D)
    (actual_nonneg r hr) (ref_nonneg r hr) hX hY (mass_eq r) hmean
    (fun t _ => hinge_bound a r d hr hd (t+1)) φ hφ hmφ 0
  simpa only [zero_add] using hh

#print axioms convex_comparison
end Erdos7TernaryTwoFlatComparison
