import Submission.BoundaryCorrectionEligibilityExplore

/-! Two-sided finite target resets inside a fixed host set. Both insertion
and deletion collateral are controlled by host triple intersections. -/
namespace Erdos66CentralEndpointReset
open AdditiveCombinatorics Erdos66CentralTripleDeletion Erdos66CentralTripleCounts
  Erdos66BoundaryCorrectionEligibility Erdos66BoundaryPairCounts Erdos66Explore
open scoped Classical
set_option maxHeartbeats 2200000

lemma endpoints_reflect {A : Set ℕ} {N n a : ℕ} (ha : a∈endpoints A N n) : n-a∈endpoints A N n := by
  obtain ⟨han,hNa,hNb,ha,hb⟩ := mem_endpoints.mp ha
  exact mem_endpoints.mpr ⟨Nat.sub_le _ _,hNb,by simpa only [Nat.sub_sub_self han] using hNa,
    hb,by simpa only [Nat.sub_sub_self han] using ha⟩

lemma deletion_inside_host (A B : Set ℕ) (E : Finset ℕ) (hBA : B ⊆ A) (z : ℕ) :
    sumRep B z ≤ sumRep (B\(E : Set ℕ)) z+2*(hits A E z).card := by
  let D := E.filter (fun a ↦ a∈B)
  have hDB : (D : Set ℕ) ⊆ B := fun a ha ↦ (Finset.mem_filter.mp ha).2
  have he : B\(D : Set ℕ)=B\(E : Set ℕ) := by
    ext a
    simp only [Set.mem_diff,Finset.mem_coe,D,Finset.mem_filter]
    tauto
  have hh := deletion_loss_le B D hDB z
  rw [he] at hh
  have hsub : hits B D z ⊆ hits A E z := by
    intro a ha
    obtain ⟨ha,haz,hb⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1,haz,hBA hb⟩
  have hc := Finset.card_le_card hsub
  omega

lemma localized_edit_bound (A B C : Set ℕ) (E : Finset ℕ) (hBA : B ⊆ A) (hCA : C ⊆ A)
    (hagree : ∀ a, a∉E → (a∈B ↔ a∈C)) (z : ℕ) :
    |(sumRep C z:ℝ)-sumRep B z| ≤ 2*((hits A E z).card:ℝ) := by
  have he : B\(E : Set ℕ)=C\(E : Set ℕ) := by
    ext a
    simp only [Set.mem_diff,Finset.mem_coe]
    by_cases ha : a∈E
    · simp only [ha,not_true_eq_false,and_false]
    · simp only [ha,not_false_eq_true,and_true,hagree a ha]
  have hB := deletion_inside_host A B E hBA z
  have hC := deletion_inside_host A C E hCA z
  rw [he] at hB
  have hB0 := sumRep_mono (show B\(E : Set ℕ) ⊆ B from Set.diff_subset) z
  rw [he] at hB0
  have hC0 := sumRep_mono (show C\(E : Set ℕ) ⊆ C from Set.diff_subset) z
  have hB' : (sumRep B z:ℝ) ≤ sumRep (C\(E : Set ℕ)) z+2*((hits A E z).card:ℝ) := by exact_mod_cast hB
  have hC' : (sumRep C z:ℝ) ≤ sumRep (C\(E : Set ℕ)) z+2*((hits A E z).card:ℝ) := by exact_mod_cast hC
  have hB0' : (sumRep (C\(E : Set ℕ)) z:ℝ) ≤ sumRep B z := by exact_mod_cast hB0
  have hC0' : (sumRep (C\(E : Set ℕ)) z:ℝ) ≤ sumRep C z := by exact_mod_cast hC0
  rw [abs_le]
  constructor <;> linarith

lemma restored_target_lower (A B : Set ℕ) (d n : ℕ) (hd : 2 ≤ d) :
    sumRep A n ≤ sumRep (B∪(endpoints A (n/d^2) n : Set ℕ)) n+2*(boundary A d n).card+1 := by
  let F := B∪(endpoints A (n/d^2) n : Set ℕ)
  have hupper : upperEndpoints A (n/d^2) n ⊆ upperEndpoints F (n/d^2) n := by
    intro a ha
    have he := (Finset.mem_filter.mp ha).1
    obtain ⟨han,hNa,hNb,haA,hbA,hlt⟩ := mem_upperEndpoints.mp ha
    exact mem_upperEndpoints.mpr ⟨han,hNa,hNb,Or.inr he,Or.inr (endpoints_reflect he),hlt⟩
  have hh := upper_target_exact F (upperEndpoints A (n/d^2) n) (n/d^2) n hupper
  have hcap := central_capacity A d n hd
  change sumRep A n ≤ sumRep F n+2*(boundary A d n).card+1
  omega

 theorem exists_central_reset (A B : Set ℕ) (d n q : ℕ) (hd : 2 ≤ d) (hBA : B ⊆ A)
    (hlo : 2*(boundary A d n).card+2 ≤ q)
    (hhi : q+2*(boundary A d n).card+1 ≤ sumRep A n) :
    ∃ C : Set ℕ, C ⊆ A ∧
      (∀ a, a∉endpoints A (n/d^2) n → (a∈B ↔ a∈C)) ∧
      q-1 ≤ sumRep C n ∧ sumRep C n ≤ q ∧
      ∀ z, |(sumRep C z:ℝ)-sumRep B z| ≤ 2*((fiber A (n/d^2) n z).card:ℝ) := by
  let E := endpoints A (n/d^2) n
  let F := B∪(E : Set ℕ)
  have hFA : F ⊆ A := Set.union_subset hBA (endpoints_subset _ _ _)
  have hbound : 2*(boundary F d n).card+2 ≤ q := by
    have hh := Finset.card_le_card (boundary_mono hFA d n)
    omega
  obtain ⟨D,hD,hu,hl⟩ := exists_central_clipping F d n q hd hbound
  let C := F\(D : Set ℕ)
  have hCA : C ⊆ A := Set.Subset.trans Set.diff_subset hFA
  have hDE : D ⊆ E := by
    intro a ha
    obtain ⟨han,hNa,hNb,haF,hbF,hlt⟩ := mem_upperEndpoints.mp (hD ha)
    exact mem_endpoints.mpr ⟨han,hNa,hNb,hFA haF,hFA hbF⟩
  have hagree : ∀ a, a∉E → (a∈B ↔ a∈C) := by
    intro a ha
    have haD : a∉D := fun h ↦ ha (hDE h)
    simp only [C,F,Set.mem_diff,Set.mem_union,Finset.mem_coe,ha,haD,or_false,not_false_eq_true,and_true]
  have hqF : q ≤ sumRep F n := by
    have hh := restored_target_lower A B d n hd
    change sumRep A n ≤ sumRep F n+2*(boundary A d n).card+1 at hh
    omega
  refine ⟨C,hCA,hagree,by change q-1 ≤ sumRep (F\(D : Set ℕ)) n; omega,hu,?_⟩
  intro z
  have hh := localized_edit_bound A B C E hBA hCA hagree z
  have hs := Finset.card_le_card (hits_subset_fiber A E (n/d^2) n z (Finset.Subset.refl _))
  have hs' : ((hits A E z).card:ℝ) ≤ (fiber A (n/d^2) n z).card := by exact_mod_cast hs
  exact hh.trans (mul_le_mul_of_nonneg_left hs' (by norm_num))

end Erdos66CentralEndpointReset
