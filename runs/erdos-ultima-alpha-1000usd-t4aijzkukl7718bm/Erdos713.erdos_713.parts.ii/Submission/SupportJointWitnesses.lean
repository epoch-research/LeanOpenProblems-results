import FormalConjecturesUtil
import Submission.SupportPackingMass
import Submission.SupportRigidity

/-! Quantitative support packings on the same extremal expanding hosts.
The forward increment bound is retained rather than inferred for a separately
chosen family of graphs. -/
open SimpleGraph Finset Filter Asymptotics
namespace Erdos713BipExtremal
open Erdos713Cloning Erdos713SwitchGluing

lemma joint_with_increment {W : Type*} (H : SimpleGraph W) {α c r s : ℝ}
    (hr : 1 < r) (hra : r < α) (has : α < s) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 0 < n ∧ ∃ C : ℝ, 0 < C ∧ ∃ G : SimpleGraph (Fin n),
      H.Free G ∧ G.IsBipartite ∧ Nat.card G.edgeSet = number n H ∧
      extremalNumber n H ≤ 2*Nat.card G.edgeSet ∧
      (Nat.card G.edgeSet : ℝ) = C*(n : ℝ)^r ∧
      (∀ j : ℕ, j ≤ n → (number j H : ℝ) ≤ C*(j : ℝ)^r) ∧
      (∀ v, C*((n : ℝ)^r-((n-1 : ℕ) : ℝ)^r) ≤ (Nat.card (G.neighborSet v) : ℝ)) ∧
      (∀ S : Finset (Fin n), 2*S.card ≤ n →
        expansionConstant r*C*S.card*(n : ℝ)^(r-1) ≤
          (Nat.card (cross G (S : Set (Fin n))).edgeSet : ℝ)) ∧
      (n : ℝ)*((number (n+1) H : ℝ)-(number n H : ℝ)) ≤ s*(number n H : ℝ) ∧
      ∃ B : Finset (Fin n), (∀ v ∈ B, SingleFold H G v) ∧
        (2-s)*(Nat.card G.edgeSet : ℝ) ≤ ∑ v ∈ B, (Nat.card (G.neighborSet v) : ℝ) := by
  obtain ⟨t,hat,hts⟩ := exists_between has
  obtain ⟨n,hn,hnp,hpos,hpast,hinc⟩ :=
    Erdos713FutureRecords.small_increment_with_past_of_limits (hra.trans hat) (by linarith) hts
      (lower_ratio_top H hra hc h) (higher_ratio_zero H hat h) N
  have hnpR : (0 : ℝ) < n := by exact_mod_cast hnp
  have hpos' : 0 < number n H := by exact_mod_cast hpos
  let C : ℝ := (number n H : ℝ)/(n : ℝ)^r
  have hC : 0 < C := div_pos hpos (Real.rpow_pos_of_pos hnpR r)
  have hEq : (number n H : ℝ) = C*(n : ℝ)^r :=
    (div_mul_cancel₀ _ (Real.rpow_pos_of_pos hnpR r).ne').symm
  have hUpper : ∀ j : ℕ, j ≤ n → (number j H : ℝ) ≤ C*(j : ℝ)^r := by
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      simp [number_zero,Real.zero_rpow (by linarith : r ≠ 0)]
    · exact (div_le_iff₀ (Real.rpow_pos_of_pos (show (0 : ℝ) < j by exact_mod_cast Nat.pos_of_ne_zero hj0) r)).mp
        (hpast j (Nat.pos_of_ne_zero hj0) hj)
  obtain ⟨G,hfree,hB,he⟩ := exists_extremal_of_pos H n hpos'
  have hEqG : (Nat.card G.edgeSet : ℝ) = C*(n : ℝ)^r := by rwa [he]
  refine ⟨n,hn,hnp,C,hC,G,hfree,hB,he,by simpa only [he] using ordinary_le_two H n,
    hEqG,hUpper,degree_lower_of_record H G hfree hB he hEqG hUpper,?_,hinc,
    mass_bound H G hfree hB he (by linarith) hinc⟩
  intro S hS
  simpa only [Fintype.card_fin] using record_cut_bound H G hfree hB hr hC.le
    (by simpa only [Fintype.card_fin] using hEqG)
    (by simpa only [Fintype.card_fin] using hUpper) S
    (by simpa only [Fintype.card_fin] using hS)

end Erdos713BipExtremal
namespace Erdos713PartialCloning
open Erdos713BipExtremal Erdos713SwitchGluing Erdos713Cloning

open scoped Classical in
lemma distinct_packing_mass {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hNoIso : ∀ a, ∃ b, H.Adj a b) {n : ℕ} (G : SimpleGraph (Fin n))
    (hfree : H.Free G) (hB : G.IsBipartite)
    (he : Nat.card G.edgeSet = number n H) {s : ℝ}
    (hinc : (n : ℝ)*((number (n+1) H : ℝ)-(number n H : ℝ)) ≤ s*(number n H : ℝ)) :
    ∃ F : Fin n → Finset (Finset (Fin n)),
      (∀ v, Packing H G v (F v)) ∧
      (2-s)*(Nat.card G.edgeSet : ℝ) ≤ (Fintype.card W : ℝ)*∑ v, ((F v).card : ℝ) ∧
      (2-s)*(Nat.card G.edgeSet : ℝ) ≤
        (Fintype.card W : ℝ)*(Fintype.card W-1 : ℕ)*(univ.biUnion F).card := by
  classical
  obtain ⟨F,hF,hmass⟩ := packing_mass H hNoIso G hfree hB he hinc
  refine ⟨F,hF,hmass,hmass.trans ?_⟩
  have hCount := support_occurrences_le hfree F (fun v => (hF v).1)
  have hReal : (∑ v, ((F v).card : ℝ)) ≤
      (Fintype.card W-1 : ℕ)*(univ.biUnion F).card := by exact_mod_cast hCount
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hReal (Nat.cast_nonneg (Fintype.card W))

open scoped Classical in
/-- All properties refer to one and the same bipartite-extremal host. -/
lemma joint_supports_of_asymptotic {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hNoIso : ∀ a, ∃ b, H.Adj a b) {α c r s : ℝ}
    (hr : 1 < r) (hra : r < α) (has : α < s) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 0 < n ∧ ∃ C : ℝ, 0 < C ∧ ∃ G : SimpleGraph (Fin n),
      H.Free G ∧ G.IsBipartite ∧ Nat.card G.edgeSet = number n H ∧
      extremalNumber n H ≤ 2*Nat.card G.edgeSet ∧
      (Nat.card G.edgeSet : ℝ) = C*(n : ℝ)^r ∧
      (∀ j : ℕ, j ≤ n → (number j H : ℝ) ≤ C*(j : ℝ)^r) ∧
      (∀ v, C*((n : ℝ)^r-((n-1 : ℕ) : ℝ)^r) ≤ (Nat.card (G.neighborSet v) : ℝ)) ∧
      (∀ S : Finset (Fin n), 2*S.card ≤ n →
        expansionConstant r*C*S.card*(n : ℝ)^(r-1) ≤
          (Nat.card (cross G (S : Set (Fin n))).edgeSet : ℝ)) ∧
      (n : ℝ)*((number (n+1) H : ℝ)-(number n H : ℝ)) ≤ s*(number n H : ℝ) ∧
      ∃ F : Fin n → Finset (Finset (Fin n)),
        (∀ v, Packing H G v (F v)) ∧
        (2-s)*(Nat.card G.edgeSet : ℝ) ≤ (Fintype.card W : ℝ)*∑ v, ((F v).card : ℝ) ∧
        (2-s)*(Nat.card G.edgeSet : ℝ) ≤
          (Fintype.card W : ℝ)*(Fintype.card W-1 : ℕ)*(univ.biUnion F).card := by
  classical
  obtain ⟨n,hn,hnp,C,hC,G,hfree,hB,he,hhalf,hEq,hUpper,hDeg,hCut,hinc,hFold⟩ :=
    joint_with_increment H hr hra has hc h N
  exact ⟨n,hn,hnp,C,hC,G,hfree,hB,he,hhalf,hEq,hUpper,hDeg,hCut,hinc,
    distinct_packing_mass H hNoIso G hfree hB he hinc⟩

#print axioms Erdos713BipExtremal.joint_with_increment
#print axioms distinct_packing_mass
#print axioms joint_supports_of_asymptotic
end Erdos713PartialCloning
