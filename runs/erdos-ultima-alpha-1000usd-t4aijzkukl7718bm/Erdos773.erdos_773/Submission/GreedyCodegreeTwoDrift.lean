import Submission.GreedyCodegreeHigherDrift

/-!
Weighted loss identities and two-degree drift without linearity. Keeping
original-edge multiplicities as weights gives a sharper estimate than an
additive duplicate-excess bound at the tracked vertex.
-/
namespace Erdos773.GreedyCodegreeTwoDrift
open Finset GreedyHypergraphState GreedyCommonNeighbors GreedyLinearLocal
open GreedyLinearHigherDrift GreedyCodegreeLocal GreedyCodegreeDrift
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Swap weighted common-neighbor incidences over any available choice set. -/
lemma weighted_closure_swap (H : Finset (Finset α)) (I : Finset α) (u : α)
    (S : Finset α) (hS : S ⊆ available H I) (a : α → ℕ) :
    (∑ w ∈ S, ∑ x ∈ closes H I u ∩ closes H I w, a x) =
      ∑ x ∈ closes H I u, a x * (closes H I x ∩ S).card := by
  have he (w : α) (hw : w ∈ S) :
      closes H I u ∩ closes H I w = (closes H I u).filter (fun x => w ∈ closes H I x) := by
    ext x
    simp only [mem_inter,mem_filter]
    exact ⟨fun h => ⟨h.1,closes_symm (hS hw) h.2⟩,
      fun h => ⟨h.1,closes_symm (closes_subset H I u h.1) h.2⟩⟩
  simp_rw [sum_congr rfl (fun w hw => show
    (∑ x ∈ closes H I u ∩ closes H I w, a x) =
      ∑ x ∈ closes H I u, if w ∈ closes H I x then a x else 0 by rw [he w hw,sum_filter])]
  rw [sum_comm]
  apply sum_congr rfl
  intro x hx
  rw [← sum_filter]
  have hf : S.filter (fun w => w ∈ closes H I x) = closes H I x ∩ S := by
    ext w
    simp only [mem_filter,mem_inter,and_comm]
  simp [hf,mul_comm]

/-- Exact weighted form of the total duplicate loss. -/
theorem sum_lostDuplicate (H : Finset (Finset α)) (I : Finset α) (u : α) :
    (∑ w ∈ safeChoices H I u, lostDuplicate H I u w) =
      ∑ x ∈ closes H I u,
        ((pairReps H I u x).card-1)*(restrictedClosure H I u x).card := by
  exact weighted_closure_swap H I u _ (filter_subset _ _) _

/-- Duplicate losses are charged to closure degree, not to the number of
    available choices. -/
theorem sum_lostDuplicate_le {H : Finset (Finset α)} (I : Finset α) (u : α)
    (h : ℝ) (hh : ∀ x ∈ closes H I u, ((closes H I x).card:ℝ) ≤ h) :
    (∑ w ∈ safeChoices H I u, (lostDuplicate H I u w:ℝ)) ≤
      h*(duplicateExcess H I u:ℝ) := by
  have he : (∑ w ∈ safeChoices H I u, (lostDuplicate H I u w:ℝ)) =
      ∑ x ∈ closes H I u,
        (((pairReps H I u x).card-1:ℕ):ℝ)*(restrictedClosure H I u x).card := by
    exact_mod_cast sum_lostDuplicate H I u
  rw [he]
  calc
    _ ≤ ∑ x ∈ closes H I u, (((pairReps H I u x).card-1:ℕ):ℝ)*h := by
      apply sum_le_sum
      intro x hx
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hc : ((restrictedClosure H I u x).card:ℝ) ≤ (closes H I x).card := by
        exact_mod_cast card_le_card (inter_subset_left (s₁ := closes H I x) (s₂ := safeChoices H I u))
      exact hc.trans (hh x hx)
    _ = _ := by simp [duplicateExcess,Nat.cast_sum,mul_sum,mul_comm]

/-- The full two-edge loss has one weight per original pair representative. -/
theorem sum_localLost_two {H : Finset (Finset α)} (I : Finset α) (u : α) :
    (∑ w ∈ safeChoices H I u, (localLost H I 2 u w).card) =
      ∑ x ∈ closes H I u,
        (pairReps H I u x).card*(restrictedClosure H I u x).card := by
  have he (w : α) (hw : w ∈ safeChoices H I u) :
      (localLost H I 2 u w).card =
        ∑ x ∈ closes H I u ∩ closes H I w, (pairReps H I u x).card := by
    obtain ⟨hw,hu⟩ := mem_filter.mp hw
    rw [GreedyCodegreeLocal.localLost_two_card hw hu]
    have hp (x : α) (hx : x ∈ closes H I u ∩ closes H I w) :
        (pairReps H I u x).card = 1+((pairReps H I u x).card-1) := by
      have hx := (mem_inter.mp hx).1
      have hn := card_pos.mpr ((pairReps_nonempty_iff (closes_subset H I u hx)).mpr hx)
      omega
    rw [sum_congr rfl hp,sum_add_distrib]
    simp [commonDegree,lostDuplicate]
  rw [sum_congr rfl he]
  exact weighted_closure_swap H I u _ (filter_subset _ _) _

/-- For a closure neighbor, the omitted choices are exactly u and the
    common neighbors, even when original edges have repeated residual pairs. -/
lemma restrictedClosure_balance {H : Finset (Finset α)} {I : Finset α} {u x : α}
    (hu : u ∈ available H I) (hx : x ∈ closes H I u) :
    (restrictedClosure H I u x).card+1+commonDegree H I u x = (closes H I x).card := by
  have hux := closes_symm hu hx
  have hs : restrictedClosure H I u x = closes H I x \ insert u (closes H I u) := by
    rw [restrictedClosure,safeChoices_eq hu]
    ext w
    simp only [mem_inter,mem_sdiff]
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,closes_subset H I x h.1,h.2⟩⟩
  have hi : closes H I x ∩ insert u (closes H I u) =
      insert u (closes H I u ∩ closes H I x) := by
    ext w
    simp only [mem_inter,mem_insert]
    constructor
    · rintro ⟨hw,rfl | hw'⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hw',hw⟩
    · rintro (rfl | ⟨hw',hw⟩)
      · exact ⟨hux,Or.inl rfl⟩
      · exact ⟨hw,Or.inr hw'⟩
  have hun : u ∉ closes H I u ∩ closes H I x := by
    exact fun h => notMem_closes_self H I u (mem_inter.mp h).1
  have hh := card_sdiff_add_card_inter (closes H I x) (insert u (closes H I u))
  rw [hi,card_insert_of_notMem hun,← hs] at hh
  change _+1+(closes H I u ∩ closes H I x).card = _
  omega

/-- Profile bounds on the exact weighted loss. No error at u is multiplied
    by the number of available vertices. -/
theorem sum_localLost_two_bounds {H : Finset (Finset α)} {I : Finset α} {u : α}
    (hu : u ∈ available H I) (l h E : ℝ) (C : ℕ)
    (hl : ∀ x ∈ closes H I u, l ≤ ((incident H I 2 x).card:ℝ))
    (hh : ∀ x ∈ closes H I u, ((incident H I 2 x).card:ℝ) ≤ h)
    (hE : ∀ x ∈ closes H I u, (duplicateExcess H I x:ℝ) ≤ E)
    (hC : ∀ x ∈ closes H I u, commonDegree H I u x ≤ C) :
    (l-E-1-C)*(incident H I 2 u).card ≤
      (∑ w ∈ safeChoices H I u, ((localLost H I 2 u w).card:ℝ)) ∧
    (∑ w ∈ safeChoices H I u, ((localLost H I 2 u w).card:ℝ)) ≤
      (h-1)*(incident H I 2 u).card := by
  have hr (x : α) (hx : x ∈ closes H I u) :
      l-E-1-C ≤ ((restrictedClosure H I u x).card:ℝ) ∧
        ((restrictedClosure H I u x).card:ℝ) ≤ h-1 := by
    have hb : ((restrictedClosure H I u x).card:ℝ)+1+commonDegree H I u x = (closes H I x).card := by
      exact_mod_cast restrictedClosure_balance hu hx
    have hd : ((incident H I 2 x).card:ℝ) = (closes H I x).card+(duplicateExcess H I x:ℝ) := by
      exact_mod_cast incident_card_eq_closes_add_excess (closes_subset H I u hx)
    have hCR : (commonDegree H I u x:ℝ) ≤ C := by exact_mod_cast hC x hx
    have hc0 : (0:ℝ) ≤ commonDegree H I u x := by positivity
    have he0 : (0:ℝ) ≤ duplicateExcess H I x := by positivity
    have h₀ := hl x hx
    have h₁ := hh x hx
    have h₂ := hE x hx
    constructor <;> linarith only [hb,hd,hCR,hc0,he0,h₀,h₁,h₂]
  have he : (∑ w ∈ safeChoices H I u, ((localLost H I 2 u w).card:ℝ)) =
      ∑ x ∈ closes H I u, ((pairReps H I u x).card:ℝ)*(restrictedClosure H I u x).card := by
    exact_mod_cast sum_localLost_two I u
  have hw : (∑ x ∈ closes H I u, ((pairReps H I u x).card:ℝ)) = (incident H I 2 u).card := by
    exact_mod_cast (incident_two_card hu).symm
  rw [he]
  constructor
  · calc
      _ = ∑ x ∈ closes H I u, ((pairReps H I u x).card:ℝ)*(l-E-1-C) := by rw [← sum_mul,hw,mul_comm]
      _ ≤ _ := sum_le_sum (fun x hx => mul_le_mul_of_nonneg_left (hr x hx).1 (by positivity))
  · calc
      _ ≤ ∑ x ∈ closes H I u, ((pairReps H I u x).card:ℝ)*(h-1) :=
        sum_le_sum (fun x hx => mul_le_mul_of_nonneg_left (hr x hx).2 (by positivity))
      _ = _ := by rw [← sum_mul,hw,mul_comm]

/-- The two-degree drift interval retains the promotion defect and neighbor
    duplicate bound, but has no codegree-dependent leading coefficient. -/
theorem survival_two_profile_bounds {H : Finset (Finset α)} {I : Finset α} {u : α}
    (hu : u ∈ available H I) (l h E : ℝ) (C : ℕ)
    (hl : ∀ x ∈ closes H I u, l ≤ ((incident H I 2 x).card:ℝ))
    (hh : ∀ x ∈ closes H I u, ((incident H I 2 x).card:ℝ) ≤ h)
    (hE : ∀ x ∈ closes H I u, (duplicateExcess H I x:ℝ) ≤ E)
    (hC : ∀ x ∈ closes H I u, commonDegree H I u x ≤ C) :
    2*(incident H I 3 u).card-(promotionDefect H I 2 u:ℝ)-(h-1)*(incident H I 2 u).card ≤
      survivalDrift H I 2 u ∧
    survivalDrift H I 2 u ≤ 2*(incident H I 3 u).card-(promotionDefect H I 2 u:ℝ)-
      (l-E-1-C)*(incident H I 2 u).card := by
  obtain ⟨hlo,hhi⟩ := sum_localLost_two_bounds hu l h E C hl hh hE hC
  have hb := GreedyCodegreeDrift.survival_drift_balance H I 2 u
  norm_num only [Nat.cast_ofNat] at hb
  constructor <;> linarith only [hlo,hhi,hb]

#print axioms weighted_closure_swap
#print axioms sum_lostDuplicate
#print axioms sum_lostDuplicate_le
#print axioms sum_localLost_two
#print axioms restrictedClosure_balance
#print axioms sum_localLost_two_bounds
#print axioms survival_two_profile_bounds
end
end Erdos773.GreedyCodegreeTwoDrift
