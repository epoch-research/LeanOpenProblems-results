import Submission.CentralEndpointResetExplore

/-! The restore-then-upper-delete reset preserves all lower-half endpoints.
This extra property is important when analyzing repeated resets. -/
namespace Erdos66OneSidedReset
open AdditiveCombinatorics Erdos66CentralEndpointReset Erdos66CentralTripleDeletion
  Erdos66BoundaryPairCounts Erdos66BoundaryCorrectionEligibility Erdos66CentralTripleCounts
open scoped Classical
set_option maxHeartbeats 2000000

lemma lower_half_not_deleted (F : Set ℕ) (N n : ℕ) (D : Finset ℕ)
    (hD : D ⊆ upperEndpoints F N n) (a : ℕ) (ha : 2*a ≤ n) : a∉D := by
  intro haD
  have hh := (mem_upperEndpoints.mp (hD haD)).2.2.2.2.2
  omega

lemma diagonal_endpoint (A : Set ℕ) (d a : ℕ) (hd : 2 ≤ d) (ha : a∈A) :
    a∈endpoints A ((2*a)/d^2) (2*a) := by
  have hpow : 2 ≤ d^2 := by nlinarith
  have hdiv : (2*a)/d^2 ≤ a :=
    (Nat.div_le_div_right (Nat.mul_le_mul_right a hpow)).trans (by rw [Nat.mul_div_right a (by omega : 0<d^2)])
  have he : 2*a-a=a := by omega
  exact mem_endpoints.mpr ⟨by omega,hdiv,by simpa only [he] using hdiv,ha,by simpa only [he] using ha⟩

 theorem exists_one_sided_reset (A B : Set ℕ) (d n q : ℕ) (hd : 2 ≤ d) (hBA : B ⊆ A)
    (hlo : 2*(boundary A d n).card+2 ≤ q)
    (hhi : q+2*(boundary A d n).card+1 ≤ sumRep A n) :
    ∃ C : Set ℕ, C ⊆ A ∧
      (∀ a, a∉endpoints A (n/d^2) n → (a∈B ↔ a∈C)) ∧
      q-1 ≤ sumRep C n ∧ sumRep C n ≤ q ∧
      (∀ z, |(sumRep C z:ℝ)-sumRep B z| ≤ 2*((fiber A (n/d^2) n z).card:ℝ)) ∧
      (∀ a, 2*a ≤ n → (a∈C ↔ a∈B ∨ a∈endpoints A (n/d^2) n)) := by
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
  refine ⟨C,hCA,hagree,by change q-1 ≤ sumRep (F\(D : Set ℕ)) n; omega,hu,?_,?_⟩
  · intro z
    have hh := localized_edit_bound A B C E hBA hCA hagree z
    have hs := Finset.card_le_card (hits_subset_fiber A E (n/d^2) n z (Finset.Subset.refl _))
    have hs' : ((hits A E z).card:ℝ) ≤ (fiber A (n/d^2) n z).card := by exact_mod_cast hs
    exact hh.trans (mul_le_mul_of_nonneg_left hs' (by norm_num))
  · intro a ha
    have hnot := lower_half_not_deleted F (n/d^2) n D hD a ha
    simp only [C,F,E,Set.mem_diff,Set.mem_union,Finset.mem_coe,hnot,not_false_eq_true,and_true]

end Erdos66OneSidedReset
