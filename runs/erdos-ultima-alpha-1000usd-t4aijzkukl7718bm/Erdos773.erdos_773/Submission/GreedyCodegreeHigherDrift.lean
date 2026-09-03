import Submission.GreedyLinearHigherDrift
import Submission.GreedyCodegreeDrift

/-!
Higher local-degree drift without linearity. A bounded per-edge error
absorbs internal residual closures in loss counts; failed promotions and
contracted-edge duplicates remain explicit.
-/
namespace Erdos773.GreedyCodegreeHigherDrift
open Finset GreedyHypergraphState GreedyCommonNeighbors GreedyLinearDrift
open GreedyLinearLocal GreedyLinearHigherDrift GreedyCodegreeDrift
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma safeLossChoices_subsets {H : Finset (Finset α)} {I e : Finset α} {j : ℕ} {u : α}
    (he : e ∈ incident H I j u) :
    ((e \ I).erase u).biUnion (restrictedClosure H I u) ⊆ safeLossChoices H I e u ∧
    safeLossChoices H I e u ⊆ (e \ I).erase u ∪
      ((e \ I).erase u).biUnion (restrictedClosure H I u) := by
  obtain ⟨he,hur⟩ := mem_filter.mp he
  have hu := (mem_filter.mp he).2.1 hur
  constructor
  · intro w hw
    obtain ⟨x,hxr,hxc⟩ := mem_biUnion.mp hw
    obtain ⟨hxc,hws⟩ := mem_inter.mp hxc
    apply mem_inter.mpr
    refine ⟨?_,hws⟩
    rw [lossChoices_eq he]
    exact mem_union_right _ (mem_biUnion.mpr ⟨x,(mem_erase.mp hxr).2,hxc⟩)
  · intro w hw
    obtain ⟨hw,hws⟩ := mem_inter.mp hw
    rw [lossChoices_eq he] at hw
    rcases mem_union.mp hw with hwr | hwc
    · have hwu : w ≠ u := by
        intro h
        exact (mem_available.mp (mem_filter.mp hws).2).1 (by simp [h])
      exact mem_union_left _ (mem_erase.mpr ⟨hwu,hwr⟩)
    · obtain ⟨x,hxr,hxc⟩ := mem_biUnion.mp hwc
      have hxu : x ≠ u := by
        intro h
        subst x
        rw [safeChoices_eq hu] at hws
        exact (mem_sdiff.mp hws).2 (mem_insert_of_mem hxc)
      exact mem_union_right _ (mem_biUnion.mpr
        ⟨x,mem_erase.mpr ⟨hxu,hxr⟩,mem_inter.mpr ⟨hxc,hws⟩⟩)

/-- Restricting closures to safe choices discards common neighbors and at
    most one additional vertex (the tracked vertex itself). -/
lemma restrictedClosure_bounds {H : Finset (Finset α)} {I : Finset α} {u : α}
    (hu : u ∈ available H I) (x : α) :
    (restrictedClosure H I u x).card ≤ (closes H I x).card ∧
    (closes H I x).card ≤ (restrictedClosure H I u x).card+commonDegree H I u x+1 := by
  refine ⟨card_le_card inter_subset_left,?_⟩
  have hs : restrictedClosure H I u x = closes H I x \ insert u (closes H I u) := by
    rw [restrictedClosure,safeChoices_eq hu]
    ext w
    simp only [mem_inter,mem_sdiff]
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,closes_subset H I x h.1,h.2⟩⟩
  have hi : closes H I x ∩ insert u (closes H I u) ⊆
      insert u (closes H I u ∩ closes H I x) := by
    intro w hw
    obtain ⟨hw,hwu⟩ := mem_inter.mp hw
    rcases mem_insert.mp hwu with rfl | hwu
    · simp
    · exact mem_insert_of_mem (mem_inter.mpr ⟨hwu,hw⟩)
  have hc := (card_le_card hi).trans (card_insert_le _ _)
  have hh := card_sdiff_add_card_inter (closes H I x) (insert u (closes H I u))
  rw [← hs] at hh
  change _ ≤ commonDegree H I u x+1 at hc
  omega

lemma safeLossChoices_bounds {H : Finset (Finset α)} {I e : Finset α} {j : ℕ}
    (hj : 3 ≤ j) {u : α} (he : e ∈ incident H I j u) (C : ℕ)
    (hC : ∀ x ∈ available H I, ∀ y ∈ available H I, x ≠ y → commonDegree H I x y ≤ C) :
    (safeLossChoices H I e u).card ≤ j-1+∑ x ∈ (e \ I).erase u, (closes H I x).card ∧
    (∑ x ∈ (e \ I).erase u, (closes H I x).card) ≤
      (safeLossChoices H I e u).card+j.choose 2*C+(j-1) := by
  have hea := (mem_filter.mp he).1
  have hur := (mem_filter.mp he).2
  have hsub := (mem_filter.mp hea).2.1
  have hr : ((e \ I).erase u).card = j-1 := by
    rw [card_erase_of_mem hur,(mem_filter.mp hea).2.2]
  obtain ⟨hlo,hhi⟩ := safeLossChoices_subsets he
  have hc (x : α) (hx : x ∈ (e \ I).erase u) := restrictedClosure_bounds (hsub hur) x
  have hs := sum_le_sum (fun x hx => (hc x hx).1)
  have hs' := sum_le_sum (fun x hx => (hc x hx).2)
  rw [sum_add_distrib,sum_add_distrib,sum_const,hr,nsmul_eq_mul,mul_one] at hs'
  have hi : ∀ x ∈ (e \ I).erase u, ∀ y ∈ (e \ I).erase u, x ≠ y →
      ((restrictedClosure H I u x) ∩ (restrictedClosure H I u y)).card ≤ C := by
    intro x hx y hy hxy
    apply (card_le_card (show restrictedClosure H I u x ∩ restrictedClosure H I u y ⊆
      closes H I x ∩ closes H I y from fun z hz =>
        mem_inter.mpr ⟨(mem_inter.mp (mem_inter.mp hz).1).1,(mem_inter.mp (mem_inter.mp hz).2).1⟩)).trans
    exact hC x (hsub (mem_erase.mp hx).2) y (hsub (mem_erase.mp hy).2) hxy
  have hu := union_card_lower ((e \ I).erase u) (restrictedClosure H I u) C hi
  rw [hr] at hu
  have hcommon : (∑ x ∈ (e \ I).erase u, commonDegree H I u x) ≤ (j-1)*C := by
    calc
      _ ≤ ∑ _x ∈ (e \ I).erase u, C := sum_le_sum (fun x hx =>
        hC u (hsub hur) x (hsub (mem_erase.mp hx).2) (mem_erase.mp hx).1.symm)
      _ = _ := by simp [hr]
  have hchoose : (j-1).choose 2+(j-1) = j.choose 2 := by
    have hh := Nat.choose_succ_succ (j-1) 1
    rw [Nat.succ_eq_add_one (j-1),show j-1+1=j by omega] at hh
    simpa [Nat.add_comm] using hh.symm
  have hprod : (j-1).choose 2*C+(j-1)*C = j.choose 2*C := by rw [← Nat.add_mul,hchoose]
  constructor
  · have hh := (card_le_card hhi).trans (card_union_le _ _)
    have hb : (((e \ I).erase u).biUnion (restrictedClosure H I u)).card ≤
        ∑ x ∈ (e \ I).erase u, (restrictedClosure H I u x).card := card_biUnion_le
    rw [hr] at hh
    omega
  · have hh := card_le_card hlo
    norm_cast at hs'
    omega

theorem sum_localLost_bounds {H : Finset (Finset α)} (I : Finset α) (j : ℕ)
    (hj : 3 ≤ j) (u : α) (C : ℕ)
    (hC : ∀ x ∈ available H I, ∀ y ∈ available H I, x ≠ y → commonDegree H I x y ≤ C) :
    (∑ w ∈ safeChoices H I u, (localLost H I j u w).card) ≤
      (j-1)*(incident H I j u).card+neighborWeight H I j u ∧
    neighborWeight H I j u ≤
      (∑ w ∈ safeChoices H I u, (localLost H I j u w).card)+
        (j.choose 2*C+(j-1))*(incident H I j u).card := by
  rw [sum_localLost_eq]
  have hlo := sum_le_sum (s := incident H I j u) (fun e he => (safeLossChoices_bounds hj he C hC).1)
  have hhi := sum_le_sum (s := incident H I j u) (fun e he => (safeLossChoices_bounds hj he C hC).2)
  constructor
  · simpa [neighborWeight,sum_add_distrib,mul_comm] using hlo
  · simpa [neighborWeight,sum_add_distrib,mul_comm,add_mul,add_assoc] using hhi

theorem survival_drift_bounds {H : Finset (Finset α)} (I : Finset α) (j : ℕ)
    (hj : 3 ≤ j) (u : α) (C : ℕ)
    (hC : ∀ x ∈ available H I, ∀ y ∈ available H I, x ≠ y → commonDegree H I x y ≤ C) :
    (j:ℝ)*(incident H I (j+1) u).card-(promotionDefect H I j u:ℝ)-
      (j-1:ℕ)*(incident H I j u).card-neighborWeight H I j u ≤ survivalDrift H I j u ∧
    survivalDrift H I j u ≤
      (j:ℝ)*(incident H I (j+1) u).card-(promotionDefect H I j u:ℝ)-neighborWeight H I j u+
        ((j.choose 2:ℝ)*C+(j-1:ℕ))*(incident H I j u).card := by
  obtain ⟨hlo,hhi⟩ := sum_localLost_bounds I j hj u C hC
  have hloR : (∑ w ∈ safeChoices H I u, ((localLost H I j u w).card:ℝ)) ≤
      (j-1:ℕ)*(incident H I j u).card+(neighborWeight H I j u:ℝ) := by exact_mod_cast hlo
  have hhiR : (neighborWeight H I j u:ℝ) ≤
      (∑ w ∈ safeChoices H I u, ((localLost H I j u w).card:ℝ))+
        ((j.choose 2:ℝ)*C+(j-1:ℕ))*(incident H I j u).card := by exact_mod_cast hhi
  have hb := GreedyCodegreeDrift.survival_drift_balance H I j u
  constructor <;> linarith only [hloR,hhiR,hb]

/-- Incident two-degrees differ from closure degrees by the explicitly
    retained duplicate excess. -/
theorem neighborWeight_bounds {H : Finset (Finset α)} (I : Finset α) (j : ℕ) (u : α)
    (l h E : ℝ)
    (hl : ∀ x ∈ available H I, l ≤ ((incident H I 2 x).card:ℝ))
    (hh : ∀ x ∈ available H I, ((incident H I 2 x).card:ℝ) ≤ h)
    (hE : ∀ x ∈ available H I, (duplicateExcess H I x:ℝ) ≤ E) :
    (l-E)*(j-1:ℕ)*(incident H I j u).card ≤ (neighborWeight H I j u:ℝ) ∧
      (neighborWeight H I j u:ℝ) ≤ h*(j-1:ℕ)*(incident H I j u).card := by
  have hclose (x : α) (hx : x ∈ available H I) :
      l-E ≤ ((closes H I x).card:ℝ) ∧ ((closes H I x).card:ℝ) ≤ h := by
    have hb : ((incident H I 2 x).card:ℝ) = (closes H I x).card+(duplicateExcess H I x:ℝ) := by
      exact_mod_cast incident_card_eq_closes_add_excess hx
    have h₀ := hl x hx
    have h₁ := hh x hx
    have h₂ := hE x hx
    have h₃ : (0:ℝ) ≤ duplicateExcess H I x := by positivity
    constructor <;> linarith only [hb,h₀,h₁,h₂,h₃]
  have hc (e : Finset α) (he : e ∈ incident H I j u) : ((e \ I).erase u).card = j-1 := by
    obtain ⟨he,hu⟩ := mem_filter.mp he
    rw [card_erase_of_mem hu,(mem_filter.mp he).2.2]
  have hw : (neighborWeight H I j u:ℝ) =
      ∑ e ∈ incident H I j u, ∑ x ∈ (e \ I).erase u, ((closes H I x).card:ℝ) := by
    unfold neighborWeight
    push_cast
    rfl
  rw [hw]
  constructor
  · calc
      _ = ∑ e ∈ incident H I j u, ∑ _x ∈ (e \ I).erase u, (l-E) := by
        rw [sum_congr rfl (fun e he => show (∑ _x ∈ (e \ I).erase u, (l-E)) = (j-1:ℕ)*(l-E) by simp [hc e he,mul_sub])]
        simp [mul_comm]
      _ ≤ _ := sum_le_sum (fun e he => sum_le_sum (fun x hx =>
        (hclose x ((mem_incident.mp he).2.1 (mem_erase.mp hx).2)).1))
  · calc
      _ ≤ ∑ e ∈ incident H I j u, ∑ _x ∈ (e \ I).erase u, h :=
        sum_le_sum (fun e he => sum_le_sum (fun x hx =>
          (hclose x ((mem_incident.mp he).2.1 (mem_erase.mp hx).2)).2))
      _ = _ := by
        rw [sum_congr rfl (fun e he => show (∑ _x ∈ (e \ I).erase u, h) = (j-1:ℕ)*h by simp [hc e he])]
        simp [mul_comm]

theorem survival_drift_profile_bounds {H : Finset (Finset α)} (I : Finset α) (j : ℕ)
    (hj : 3 ≤ j) (u : α) (l h E : ℝ) (C : ℕ)
    (hl : ∀ x ∈ available H I, l ≤ ((incident H I 2 x).card:ℝ))
    (hh : ∀ x ∈ available H I, ((incident H I 2 x).card:ℝ) ≤ h)
    (hE : ∀ x ∈ available H I, (duplicateExcess H I x:ℝ) ≤ E)
    (hC : ∀ x ∈ available H I, ∀ y ∈ available H I, x ≠ y → commonDegree H I x y ≤ C) :
    (j:ℝ)*(incident H I (j+1) u).card-(promotionDefect H I j u:ℝ)-
      (j-1:ℕ)*(h+1)*(incident H I j u).card ≤ survivalDrift H I j u ∧
    survivalDrift H I j u ≤
      (j:ℝ)*(incident H I (j+1) u).card-(promotionDefect H I j u:ℝ)-
        (j-1:ℕ)*(l-E)*(incident H I j u).card+
        ((j.choose 2:ℝ)*C+(j-1:ℕ))*(incident H I j u).card := by
  obtain ⟨hdlo,hdhi⟩ := survival_drift_bounds I j hj u C hC
  obtain ⟨hwlo,hwhi⟩ := neighborWeight_bounds I j u l h E hl hh hE
  constructor <;> nlinarith only [hdlo,hdhi,hwlo,hwhi]

#print axioms safeLossChoices_subsets
#print axioms restrictedClosure_bounds
#print axioms safeLossChoices_bounds
#print axioms sum_localLost_bounds
#print axioms survival_drift_bounds
#print axioms neighborWeight_bounds
#print axioms survival_drift_profile_bounds
end
end Erdos773.GreedyCodegreeHigherDrift
