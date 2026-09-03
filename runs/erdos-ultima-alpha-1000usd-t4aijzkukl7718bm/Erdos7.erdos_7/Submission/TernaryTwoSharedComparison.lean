import Submission.TernaryTwoSharedPrefix
import Submission.FiniteHingeComparison

/-!
# Convex-test lifting of the shared-prefix ternary-two comparison

The two laws have exactly equal mass and nonnegative weights. Consequently
signed convex monotone tests are allowed. This is not an arithmetic cover proof.
-/
namespace Erdos7TernaryTwoSharedComparison
open scoped BigOperators
open Erdos7TernaryTwoSharedPrefix
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000

variable {J : Type*} [Fintype J]
noncomputable def actualWeight (c : Fin 10) (r : J → ℝ) : Fin 5 ⊕ (J × Fin 5) → ℝ :=
  Sum.elim (fun x => (weightNum c x : ℝ)/100) (fun z => r z.1/5)
def actualCount (a : ℕ → Fin 10) (d : J → ℕ) : Fin 5 ⊕ (J × Fin 5) → ℕ :=
  Sum.elim (count (a 0)) (fun z => prefixCount a (d z.1) z.2)
def starWeight : Fin 3 → ℕ := ![2,2,1]
noncomputable def refWeight (c : Fin 10) (r : J → ℝ) : Fin 3 ⊕ (J × Fin 3) → ℝ :=
  Sum.elim (fun n => (lowNum c n : ℝ)/100) (fun z => r z.1*(starWeight z.2 : ℝ)/5)
def refCount (d : J → ℕ) : Fin 3 ⊕ (J × Fin 3) → ℕ :=
  Sum.elim (fun n => n.val+1) (fun z => d z.1*(z.2.val+1))

lemma actual_nonneg (c : Fin 10) (r : J → ℝ) (hr : ∀ j,0≤r j) :
    ∀ z,0≤actualWeight c r z := by
  intro z; cases z with
  | inl x => dsimp [actualWeight]; positivity
  | inr z => dsimp [actualWeight]; exact div_nonneg (hr _) (by norm_num)

lemma ref_nonneg (c : Fin 10) (r : J → ℝ) (hr : ∀ j,0≤r j) :
    ∀ z,0≤refWeight c r z := by
  intro z; cases z with
  | inl x => dsimp [refWeight]; positivity
  | inr z => dsimp [refWeight]; exact div_nonneg (mul_nonneg (hr _) (Nat.cast_nonneg _)) (by norm_num)

lemma actual_hinge (c : Fin 10) (a : ℕ → Fin 10) (r : J → ℝ) (d : J → ℕ) (t : ℕ) :
    (∑ z,actualWeight c r z*((actualCount a d z-t : ℕ) : ℝ)) =
      first c (a 0) t+∑ j,r j*prefixHinge a (d j) t := by
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,actualWeight,actualCount,Sum.elim_inl,Sum.elim_inr]
  congr 1
  · unfold first firstNum
    rw [Nat.cast_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x _
    rw [Nat.cast_mul]
    ring
  · apply Finset.sum_congr rfl
    intro j _
    unfold prefixHinge
    rw [← Finset.mul_sum]
    ring

lemma star_hinge (d t : ℕ) :
    (∑ n : Fin 3,(starWeight n : ℝ)*((d*(n.val+1)-t : ℕ) : ℝ))/5 = star d t := by
  simp [Erdos7TernaryTwoSharedPrefix.star,starNum,starWeight,Fin.sum_univ_succ,Nat.cast_add,Nat.cast_mul,Nat.mul_comm]
  ring

lemma ref_hinge (c : Fin 10) (r : J → ℝ) (d : J → ℕ) (t : ℕ) :
    (∑ z,refWeight c r z*((refCount d z-t : ℕ) : ℝ)) =
      base c t+∑ j,r j*star (d j) t := by
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,refWeight,refCount,Sum.elim_inl,Sum.elim_inr]
  congr 1
  · unfold base baseNum
    rw [Nat.cast_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n _
    rw [Nat.cast_mul]
    ring
  · apply Finset.sum_congr rfl
    intro j _
    rw [← star_hinge,Finset.sum_div,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring

lemma mass_eq (c : Fin 10) (r : J → ℝ) :
    (∑ z,actualWeight c r z) = ∑ z,refWeight c r z := by
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,actualWeight,refWeight,Sum.elim_inl,Sum.elim_inr]
  congr 1
  · rw [← Finset.sum_div,← Finset.sum_div,← Nat.cast_sum,← Nat.cast_sum,data.2.2.2 c]
  · apply Finset.sum_congr rfl
    intro j _
    norm_num [starWeight,Fin.sum_univ_succ]
    ring

lemma prefix_upper (a : ℕ → Fin 10) (d : ℕ) (x : Fin 5) : prefixCount a d x ≤ 3*d := by
  calc
    _ ≤ ∑ _j ∈ Finset.range d,3 := Finset.sum_le_sum (fun j _ => (data.1 (a j) x).2)
    _ = _ := by simp [Nat.mul_comm]

/-- A full increasing-convex comparison, for an arbitrary finite distribution
of prefix lengths. The first slice is shared in every actual prefix. -/
theorem convex_comparison (c : Fin 10) (a : ℕ → Fin 10) (r : J → ℝ) (d : J → ℕ)
    (hr : ∀ j,0≤r j) (hd : ∀ j,2≤d j) (hmass : (∑ j,r j)=1/5)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ) :
    (∑ z,actualWeight c r z*φ (actualCount a d z)) ≤
      ∑ z,refWeight c r z*φ (refCount d z) := by
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
  have hmean : (∑ z,actualWeight c r z*(actualCount a d z : ℝ)) ≤
      ∑ z,refWeight c r z*(refCount d z : ℝ) := by
    have hh := shared_prefix_hinge c a r d hr hd hmass 0
    rw [← actual_hinge,← ref_hinge] at hh
    simpa only [Nat.sub_zero] using hh
  have hh := Erdos7FiniteHingeComparison.convex_monotone_comparison
    (actualWeight c r) (refWeight c r) (actualCount a d) (refCount d) (3*D)
    (actual_nonneg c r hr) (ref_nonneg c r hr) hX hY (mass_eq c r) hmean
    (fun t _ => by
      rw [actual_hinge,ref_hinge]
      exact shared_prefix_hinge c a r d hr hd hmass (t+1)) φ hφ hmφ 0
  simpa only [zero_add] using hh

/-- Averages of complete integer-count sequences are covered too. Thus the
comparison does not require a normalized count itself to be integer-valued. -/
theorem averaged_comparison {I : Type*} (S : Finset I) (w : I → ℝ)
    (hw : ∀ i∈S,0≤w i) (hw1 : (∑ i∈S,w i)=1)
    (c : Fin 10) (a : I → ℕ → Fin 10) (r : J → ℝ) (d : J → ℕ)
    (hr : ∀ j,0≤r j) (hd : ∀ j,2≤d j) (hmass : (∑ j,r j)=1/5)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ) :
    (∑ z,actualWeight c r z*φ (∑ i∈S,w i*(actualCount (a i) d z : ℝ))) ≤
      ∑ z,refWeight c r z*φ (refCount d z) := by
  exact Erdos7FiniteHingeComparison.family_mixture_bound S w (actualWeight c r)
    (fun i z => (actualCount (a i) d z : ℝ)) φ hφ hw hw1 (actual_nonneg c r hr)
    _ (fun i _ => convex_comparison c (a i) r d hr hd hmass φ hφ hmφ)

/-- Each test may have a different sequence. Only the positive reference law
is common. A diagonal bound for their sum therefore remains usable. -/
theorem separate_sequences {I : Type*} [Fintype I]
    (c : Fin 10) (a : I → ℕ → Fin 10) (r : J → ℝ) (d : J → ℕ)
    (hr : ∀ j,0≤r j) (hd : ∀ j,2≤d j) (hmass : (∑ j,r j)=1/5)
    (φ : I → ℝ → ℝ) (hφ : ∀ i,ConvexOn ℝ Set.univ (φ i))
    (hmφ : ∀ i,Monotone (φ i)) (b : ℝ) (F : ℝ → ℝ)
    (hdiag : ∀ n : ℕ,b+(∑ i,φ i n)≤F n) :
    b*(∑ z,actualWeight c r z)+
      (∑ i,∑ z,actualWeight c r z*φ i (actualCount (a i) d z)) ≤
      ∑ z,refWeight c r z*F (refCount d z) := by
  calc
    _ ≤ b*(∑ z,actualWeight c r z)+
        (∑ i,∑ z,refWeight c r z*φ i (refCount d z)) := by
      exact add_le_add le_rfl (Finset.sum_le_sum (fun i _ =>
        convex_comparison c (a i) r d hr hd hmass (φ i) (hφ i) (hmφ i)))
    _ = ∑ z,refWeight c r z*(b+∑ i,φ i (refCount d z)) := by
      rw [mass_eq,Finset.sum_comm]
      simp only [mul_add,Finset.mul_sum,Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ ≤ _ := Finset.sum_le_sum (fun z _ =>
      mul_le_mul_of_nonneg_left (hdiag _) (ref_nonneg c r hr z))

noncomputable def geometricWeight (E : ℕ) (j : Fin (E+1)) : ℝ :=
  if j.val<E then 4/(5 : ℝ)^(j.val+2) else 1/(5 : ℝ)^(E+1)

def geometricLength (E : ℕ) (j : Fin (E+1)) : ℕ := j.val+2

lemma geometric_partial (E : ℕ) :
    (∑ j∈Finset.range E,4/(5 : ℝ)^(j+2)) = 1/5-1/(5 : ℝ)^(E+1) := by
  induction E with
  | zero => norm_num
  | succ E ih =>
    rw [Finset.sum_range_succ,ih]
    have hp : (5 : ℝ)^(E+2)=5^(E+1)*5 := by rw [show E+2=(E+1)+1 by omega,pow_succ]
    rw [show E+1+1=E+2 by omega,hp]
    field_simp
    ring

lemma geometric_mass (E : ℕ) : (∑ j,geometricWeight E j)=1/5 := by
  rw [Fin.sum_univ_castSucc]
  have hfirst : (∑ j : Fin E,geometricWeight E j.castSucc) =
      ∑ j∈Finset.range E,4/(5 : ℝ)^(j+2) := by
    simp only [geometricWeight,Fin.val_castSucc,Fin.isLt,if_true]
    exact Fin.sum_univ_eq_sum_range (fun j : ℕ => 4/(5 : ℝ)^(j+2)) E
  rw [hfirst,geometric_partial]
  simp [geometricWeight]

lemma geometric_nonneg (E : ℕ) (j : Fin (E+1)) : 0≤geometricWeight E j := by
  unfold geometricWeight
  split_ifs <;> positivity

/-- Every finite positive exponent cap is included, with the entire remaining
geometric mass placed at its actual terminal prefix, not discarded. -/
theorem geometric_comparison (c : Fin 10) (a : ℕ → Fin 10) (E : ℕ)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ) :
    (∑ z,actualWeight c (geometricWeight E) z*
      φ (actualCount a (geometricLength E) z)) ≤
      ∑ z,refWeight c (geometricWeight E) z*φ (refCount (geometricLength E) z) := by
  exact convex_comparison c a (geometricWeight E) (geometricLength E)
    (geometric_nonneg E) (fun j => by simp [geometricLength]) (geometric_mass E) φ hφ hmφ

#print axioms averaged_comparison
#print axioms separate_sequences
#print axioms geometric_comparison
#print axioms mass_eq
#print axioms convex_comparison
end Erdos7TernaryTwoSharedComparison
