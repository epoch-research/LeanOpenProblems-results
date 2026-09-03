import Submission.GreedyLinearLocal

/-!
Survival-conditioned local drift for residual sizes at least three. All
profile bounds remain hypotheses, rather than assumed typical behavior.
-/
namespace Erdos773.GreedyLinearHigherDrift
open Finset GreedyHypergraphState GreedyCommonNeighbors GreedyLinearDrift GreedyLinearLocal
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

def safeLossChoices (H : Finset (Finset α)) (I e : Finset α) (u : α) : Finset α :=
  lossChoices H I e ∩ safeChoices H I u

def restrictedClosure (H : Finset (Finset α)) (I : Finset α) (u x : α) : Finset α :=
  closes H I x ∩ safeChoices H I u

lemma sum_localLost_eq (H : Finset (Finset α)) (I : Finset α) (j : ℕ) (u : α) :
    (∑ w ∈ safeChoices H I u, (localLost H I j u w).card) =
      ∑ e ∈ incident H I j u, (safeLossChoices H I e u).card := by
  have heq (w : α) : localLost H I j u w =
      (incident H I j u).filter (fun e => ¬e \ I ⊆ available H (insert w I)) := by
    ext e
    simp only [localLost,lost,incident,mem_filter]
    tauto
  simp_rw [heq]
  have hh : (∑ w ∈ safeChoices H I u,
      ((incident H I j u).filter (fun e => ¬e \ I ⊆ available H (insert w I))).card) =
      ∑ e ∈ incident H I j u,
        ((safeChoices H I u).filter (fun w => ¬e \ I ⊆ available H (insert w I))).card :=
    sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := safeChoices H I u) (t := incident H I j u)
      (fun w e => ¬e \ I ⊆ available H (insert w I))
  rw [hh]
  apply sum_congr rfl
  intro e he
  congr 1
  ext w
  simp only [safeLossChoices,lossChoices,safeChoices,mem_inter,mem_filter]
  tauto

lemma safeLossChoices_eq {H : Finset (Finset α)} (hlin : Linear H)
    {I e : Finset α} {j : ℕ} (hj : 3 ≤ j) {u : α} (he : e ∈ incident H I j u) :
    safeLossChoices H I e u = (e \ I).erase u ∪
      ((e \ I).erase u).biUnion (restrictedClosure H I u) := by
  obtain ⟨he,hur⟩ := mem_filter.mp he
  have hu := (mem_filter.mp he).2.1 hur
  have hsafe : ∀ v ∈ (e \ I).erase u, v ∈ safeChoices H I u := by
    intro v hv
    obtain ⟨hvu,hvr⟩ := mem_erase.mp hv
    exact mem_filter.mpr ⟨(mem_filter.mp he).2.1 hvr,
      hlin.residual_survives hj he hvr (mem_erase.mpr ⟨hvu.symm,hur⟩)⟩
  rw [safeLossChoices,lossChoices_eq he]
  ext w
  constructor
  · intro hw
    obtain ⟨hw,hws⟩ := mem_inter.mp hw
    rcases mem_union.mp hw with hwr | hwc
    · have hwu : w ≠ u := by
        intro h
        have hu' := (mem_filter.mp hws).2
        exact (mem_available.mp hu').1 (by simp [h])
      exact mem_union_left _ (mem_erase.mpr ⟨hwu,hwr⟩)
    · obtain ⟨x,hxr,hxc⟩ := mem_biUnion.mp hwc
      have hxu : x ≠ u := by
        intro h
        subst x
        rw [safeChoices_eq hu] at hws
        exact (mem_sdiff.mp hws).2 (mem_insert_of_mem hxc)
      exact mem_union_right _ (mem_biUnion.mpr
        ⟨x,mem_erase.mpr ⟨hxu,hxr⟩,mem_inter.mpr ⟨hxc,hws⟩⟩)
  · intro hw
    rcases mem_union.mp hw with hwr | hwc
    · exact mem_inter.mpr ⟨mem_union_left _ (mem_erase.mp hwr).2,hsafe w hwr⟩
    · obtain ⟨x,hxr,hxc⟩ := mem_biUnion.mp hwc
      obtain ⟨hxc,hws⟩ := mem_inter.mp hxc
      exact mem_inter.mpr ⟨mem_union_right _ (mem_biUnion.mpr
        ⟨x,(mem_erase.mp hxr).2,hxc⟩),hws⟩

lemma safeLossChoices_card {H : Finset (Finset α)} (hlin : Linear H)
    {I e : Finset α} {j : ℕ} (hj : 3 ≤ j) {u : α} (he : e ∈ incident H I j u) :
    (safeLossChoices H I e u).card = j-1+
      (((e \ I).erase u).biUnion (restrictedClosure H I u)).card := by
  rw [safeLossChoices_eq hlin hj he]
  obtain ⟨he,hur⟩ := mem_filter.mp he
  have hd : Disjoint ((e \ I).erase u)
      (((e \ I).erase u).biUnion (restrictedClosure H I u)) := by
    apply disjoint_left.mpr
    intro w hwr hwc
    obtain ⟨x,hxr,hxc⟩ := mem_biUnion.mp hwc
    exact hlin.no_internal_closure hj he (mem_erase.mp hxr).2 (mem_erase.mp hwr).2
      (mem_inter.mp hxc).1
  rw [card_union_of_disjoint hd,card_erase_of_mem hur,(mem_filter.mp he).2.2]

/-- Restricting a neighbor's closures to safe choices removes precisely its
    common neighbors with the tracked vertex. -/
lemma restrictedClosure_balance {H : Finset (Finset α)} (hlin : Linear H)
    {I e : Finset α} {j : ℕ} (hj : 3 ≤ j) {u : α} (he : e ∈ incident H I j u)
    {x : α} (hx : x ∈ (e \ I).erase u) :
    (restrictedClosure H I u x).card+commonDegree H I u x = (closes H I x).card := by
  obtain ⟨he,hur⟩ := mem_filter.mp he
  have hu := (mem_filter.mp he).2.1 hur
  have hun : u ∉ closes H I x := hlin.no_internal_closure hj he (mem_erase.mp hx).2 hur
  have hs : restrictedClosure H I u x = closes H I x \ insert u (closes H I u) := by
    rw [restrictedClosure,safeChoices_eq hu]
    ext w
    simp only [mem_inter,mem_sdiff]
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,closes_subset H I x h.1,h.2⟩⟩
  have hi : closes H I x ∩ insert u (closes H I u) = closes H I u ∩ closes H I x := by
    ext w
    simp only [mem_inter,mem_insert]
    constructor
    · rintro ⟨hw,rfl | hw'⟩
      · exact (hun hw).elim
      · exact ⟨hw',hw⟩
    · rintro ⟨hw',hw⟩
      exact ⟨hw,Or.inr hw'⟩
  have hh := card_sdiff_add_card_inter (closes H I x) (insert u (closes H I u))
  rw [hi,← hs] at hh
  exact hh

lemma safeLossChoices_bounds {H : Finset (Finset α)} (hlin : Linear H)
    {I e : Finset α} {j : ℕ} (hj : 3 ≤ j) {u : α} (he : e ∈ incident H I j u) (C : ℕ)
    (hC : ∀ x ∈ available H I, ∀ y ∈ available H I, x ≠ y → commonDegree H I x y ≤ C) :
    (safeLossChoices H I e u).card ≤ j-1+∑ x ∈ (e \ I).erase u, (closes H I x).card ∧
      j-1+(∑ x ∈ (e \ I).erase u, (closes H I x).card) ≤
        (safeLossChoices H I e u).card+j.choose 2*C := by
  have hea := (mem_filter.mp he).1
  have hur := (mem_filter.mp he).2
  have hsub := (mem_filter.mp hea).2.1
  have hr : ((e \ I).erase u).card = j-1 := by
    rw [card_erase_of_mem hur,(mem_filter.mp hea).2.2]
  have hi : ∀ x ∈ (e \ I).erase u, ∀ y ∈ (e \ I).erase u, x ≠ y →
      ((restrictedClosure H I u x) ∩ (restrictedClosure H I u y)).card ≤ C := by
    intro x hx y hy hxy
    apply (card_le_card (show restrictedClosure H I u x ∩ restrictedClosure H I u y ⊆
      closes H I x ∩ closes H I y from fun z hz =>
        mem_inter.mpr ⟨(mem_inter.mp (mem_inter.mp hz).1).1,(mem_inter.mp (mem_inter.mp hz).2).1⟩)).trans
    exact hC x (hsub (mem_erase.mp hx).2) y (hsub (mem_erase.mp hy).2) hxy
  have hu := union_card_lower ((e \ I).erase u) (restrictedClosure H I u) C hi
  rw [hr] at hu
  have hc : (∑ x ∈ (e \ I).erase u, commonDegree H I u x) ≤ (j-1)*C := by
    calc
      _ ≤ ∑ _x ∈ (e \ I).erase u, C := sum_le_sum (fun x hx =>
        hC u (hsub hur) x (hsub (mem_erase.mp hx).2) (mem_erase.mp hx).1.symm)
      _ = _ := by simp [hr]
  have hb := sum_congr (s₁ := (e \ I).erase u) rfl
    (fun x hx => restrictedClosure_balance hlin hj he hx)
  rw [sum_add_distrib] at hb
  have hj1 : j-1+1 = j := by omega
  have hchoose : (j-1).choose 2+(j-1) = j.choose 2 := by
    have hh := Nat.choose_succ_succ (j-1) 1
    rw [Nat.succ_eq_add_one (j-1),hj1] at hh
    simpa [Nat.add_comm] using hh.symm
  have hprod : (j-1).choose 2*C+(j-1)*C = j.choose 2*C := by rw [← Nat.add_mul,hchoose]
  rw [safeLossChoices_card hlin hj he]
  constructor
  · have hupper : (((e \ I).erase u).biUnion (restrictedClosure H I u)).card ≤
        ∑ x ∈ (e \ I).erase u, (restrictedClosure H I u x).card := card_biUnion_le
    omega
  · omega

/-- Neighbor degrees, counted once for each incident residual edge. -/
def neighborWeight (H : Finset (Finset α)) (I : Finset α) (j : ℕ) (u : α) : ℕ :=
  ∑ e ∈ incident H I j u, ∑ x ∈ (e \ I).erase u, (closes H I x).card

theorem sum_localLost_bounds {H : Finset (Finset α)} (hlin : Linear H)
    (I : Finset α) (j : ℕ) (hj : 3 ≤ j) (u : α) (C : ℕ)
    (hC : ∀ x ∈ available H I, ∀ y ∈ available H I, x ≠ y → commonDegree H I x y ≤ C) :
    (∑ w ∈ safeChoices H I u, (localLost H I j u w).card) ≤
      (j-1)*(incident H I j u).card+neighborWeight H I j u ∧
    (j-1)*(incident H I j u).card+neighborWeight H I j u ≤
      (∑ w ∈ safeChoices H I u, (localLost H I j u w).card)+j.choose 2*C*(incident H I j u).card := by
  rw [sum_localLost_eq]
  have heq : (j-1)*(incident H I j u).card+neighborWeight H I j u =
      ∑ e ∈ incident H I j u, (j-1+∑ x ∈ (e \ I).erase u, (closes H I x).card) := by
    simp [neighborWeight,sum_add_distrib,mul_comm]
  rw [heq]
  constructor
  · exact sum_le_sum (fun e he => (safeLossChoices_bounds hlin hj he C hC).1)
  · calc
      _ ≤ ∑ e ∈ incident H I j u, ((safeLossChoices H I e u).card+j.choose 2*C) :=
        sum_le_sum (fun e he => (safeLossChoices_bounds hlin hj he C hC).2)
      _ = _ := by simp [sum_add_distrib,mul_comm]

/-- Local drift bounds after assigning zero increment to unsafe choices. -/
theorem survival_drift_bounds {H : Finset (Finset α)} (hlin : Linear H)
    (I : Finset α) (j : ℕ) (hj : 3 ≤ j) (u : α) (C : ℕ)
    (hC : ∀ x ∈ available H I, ∀ y ∈ available H I, x ≠ y → commonDegree H I x y ≤ C) :
    (j:ℝ)*(incident H I (j+1) u).card-(j-1:ℕ)*(incident H I j u).card-neighborWeight H I j u ≤
      survivalDrift H I j u ∧
    survivalDrift H I j u ≤
      (j:ℝ)*(incident H I (j+1) u).card-(j-1:ℕ)*(incident H I j u).card-neighborWeight H I j u+
        (j.choose 2:ℝ)*C*(incident H I j u).card := by
  obtain ⟨hlo,hhi⟩ := sum_localLost_bounds hlin I j hj u C hC
  have hloR : (∑ w ∈ safeChoices H I u, ((localLost H I j u w).card:ℝ)) ≤
      (j-1:ℕ)*(incident H I j u).card+(neighborWeight H I j u:ℝ) := by exact_mod_cast hlo
  have hhiR : (j-1:ℕ)*(incident H I j u).card+(neighborWeight H I j u:ℝ) ≤
      (∑ w ∈ safeChoices H I u, ((localLost H I j u w).card:ℝ))+
        (j.choose 2:ℝ)*C*(incident H I j u).card := by exact_mod_cast hhi
  have hb := survival_drift_balance hlin I j (by omega) u
  constructor <;> linarith

/-- This step requires uniform degree bounds as hypotheses; it does not
    assert that the dynamics produce them. -/
theorem neighborWeight_bounds {H : Finset (Finset α)} (hlin : Linear H)
    (I : Finset α) (j : ℕ) (u : α) (l h : ℝ)
    (hl : ∀ x ∈ available H I, l ≤ ((incident H I 2 x).card:ℝ))
    (hh : ∀ x ∈ available H I, ((incident H I 2 x).card:ℝ) ≤ h) :
    l*(j-1:ℕ)*(incident H I j u).card ≤ (neighborWeight H I j u:ℝ) ∧
      (neighborWeight H I j u:ℝ) ≤ h*(j-1:ℕ)*(incident H I j u).card := by
  have hc (e : Finset α) (he : e ∈ incident H I j u) : ((e \ I).erase u).card = j-1 := by
    obtain ⟨he,hu⟩ := mem_filter.mp he
    rw [card_erase_of_mem hu,(mem_filter.mp he).2.2]
  have hw : (neighborWeight H I j u:ℝ) = ∑ e ∈ incident H I j u,
      ∑ x ∈ (e \ I).erase u, ((incident H I 2 x).card:ℝ) := by
    unfold neighborWeight
    push_cast
    apply sum_congr rfl
    intro e he
    apply sum_congr rfl
    intro x hx
    have hxA := (mem_incident.mp he).2.1 (mem_erase.mp hx).2
    rw [hlin.incident_two_card I x hxA]
  rw [hw]
  constructor
  · calc
      _ = ∑ e ∈ incident H I j u, ∑ _x ∈ (e \ I).erase u, l := by
        rw [sum_congr rfl (fun e he => show (∑ _x ∈ (e \ I).erase u, l) = (j-1:ℕ)*l by simp [hc e he])]
        simp [mul_comm]
      _ ≤ _ := sum_le_sum (fun e he => sum_le_sum (fun x hx =>
        hl x ((mem_incident.mp he).2.1 (mem_erase.mp hx).2)))
  · calc
      _ ≤ ∑ e ∈ incident H I j u, ∑ _x ∈ (e \ I).erase u, h :=
        sum_le_sum (fun e he => sum_le_sum (fun x hx =>
          hh x ((mem_incident.mp he).2.1 (mem_erase.mp hx).2)))
      _ = _ := by
        rw [sum_congr rfl (fun e he => show (∑ _x ∈ (e \ I).erase u, h) = (j-1:ℕ)*h by simp [hc e he])]
        simp [mul_comm]

/-- Explicit conditional mean-field interval for the higher local degrees. -/
theorem survival_drift_profile_bounds {H : Finset (Finset α)} (hlin : Linear H)
    (I : Finset α) (j : ℕ) (hj : 3 ≤ j) (u : α) (l h : ℝ) (C : ℕ)
    (hl : ∀ x ∈ available H I, l ≤ ((incident H I 2 x).card:ℝ))
    (hh : ∀ x ∈ available H I, ((incident H I 2 x).card:ℝ) ≤ h)
    (hC : ∀ x ∈ available H I, ∀ y ∈ available H I, x ≠ y → commonDegree H I x y ≤ C) :
    (j:ℝ)*(incident H I (j+1) u).card-(j-1:ℕ)*(h+1)*(incident H I j u).card ≤
      survivalDrift H I j u ∧
    survivalDrift H I j u ≤
      (j:ℝ)*(incident H I (j+1) u).card-(j-1:ℕ)*(l+1)*(incident H I j u).card+
        (j.choose 2:ℝ)*C*(incident H I j u).card := by
  obtain ⟨hdlo,hdhi⟩ := survival_drift_bounds hlin I j hj u C hC
  obtain ⟨hwlo,hwhi⟩ := neighborWeight_bounds hlin I j u l h hl hh
  constructor <;> nlinarith

#print axioms sum_localLost_bounds
#print axioms survival_drift_bounds
#print axioms neighborWeight_bounds
#print axioms survival_drift_profile_bounds
#print axioms sum_localLost_eq
#print axioms safeLossChoices_card
#print axioms restrictedClosure_balance
#print axioms safeLossChoices_bounds
end
end Erdos773.GreedyLinearHigherDrift
