import Submission.GreedyLinearDrift

/-!
Exact local incident-edge updates and bounded increments for linear original
hypergraphs, conditional on the tracked vertex remaining available.
-/
namespace Erdos773.GreedyLinearLocal
open Finset GreedyHypergraphState GreedyCommonNeighbors GreedyLinearDrift
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

def localLost (H : Finset (Finset α)) (I : Finset α) (j : ℕ) (u w : α) : Finset (Finset α) :=
  (lost H I j w).filter (fun e => u ∈ e \ I)

def localPromoted (H : Finset (Finset α)) (I : Finset α) (j : ℕ) (u w : α) : Finset (Finset α) :=
  (promoted H I j w).filter (fun e => u ∈ e \ I)

/-- Exact local update, with both losses and promotions retaining original
    edge indices. -/
theorem incident_card_step {H : Finset (Finset α)} {I : Finset α} {u w : α}
    (hw : w ∈ available H I) (huw : u ≠ w) (j : ℕ) :
    (incident H (insert w I) j u).card+(localLost H I j u w).card =
      (incident H I j u).card+(localPromoted H I j u w).card := by
  have hs : incident H (insert w I) j u =
      ((surviving H I j w).filter (fun e => u ∈ e \ I)) ∪ localPromoted H I j u w := by
    ext e
    simp only [incident,active_insert_split hw j,mem_filter,mem_union,localPromoted,
      residual_insert,mem_erase]
    tauto
  have hd : Disjoint ((surviving H I j w).filter (fun e => u ∈ e \ I))
      (localPromoted H I j u w) :=
    (surviving_promoted_disjoint H I j w).mono (filter_subset _ _) (filter_subset _ _)
  have heq1 : (surviving H I j w).filter (fun e => u ∈ e \ I) =
      (incident H I j u).filter (fun e => e \ I ⊆ available H (insert w I)) := by
    ext e
    simp only [surviving,incident,mem_filter]
    tauto
  have heq2 : localLost H I j u w =
      (incident H I j u).filter (fun e => ¬e \ I ⊆ available H (insert w I)) := by
    ext e
    simp only [localLost,lost,incident,mem_filter]
    tauto
  rw [hs,card_union_of_disjoint hd,heq1,heq2]
  have hh := card_filter_add_card_filter_not
    (s := incident H I j u) (fun e => e \ I ⊆ available H (insert w I))
  omega

lemma promoted_card_le_one {H : Finset (Finset α)} (hlin : Linear H)
    (I : Finset α) (j : ℕ) {u w : α} (huw : u ≠ w) :
    (localPromoted H I j u w).card ≤ 1 := by
  have hs : localPromoted H I j u w ⊆ H.filter (fun e => u ∈ e ∧ w ∈ e) := by
    intro e he
    obtain ⟨he,hu⟩ := mem_filter.mp he
    obtain ⟨he,hw,_⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨(mem_filter.mp he).1,(mem_sdiff.mp hu).1,(mem_sdiff.mp hw).1⟩
  exact (card_le_card hs).trans (hlin.pair_degree u w huw)

lemma lost_card_le_closes {H : Finset (Finset α)} (hlin : Linear H)
    {I : Finset α} {u w : α} (hw : w ∈ available H I)
    (hu : u ∈ available H (insert w I)) (j : ℕ) :
    (localLost H I j u w).card ≤ (closes H I w).card+1 := by
  have huD : u ∉ insert w (closes H I w) := by
    rw [available_insert hw] at hu
    exact (mem_sdiff.mp hu).2
  have hs : localLost H I j u w ⊆ (insert w (closes H I w)).biUnion
      (fun x => H.filter (fun e => u ∈ e ∧ x ∈ e)) := by
    intro e he
    obtain ⟨he,hur⟩ := mem_filter.mp he
    obtain ⟨he,hnot⟩ := mem_filter.mp he
    obtain ⟨x,hx,hx'⟩ := not_subset.mp hnot
    have hxA := (mem_filter.mp he).2.1 hx
    have hxD : x ∈ insert w (closes H I w) := by
      by_contra h
      apply hx'
      rw [available_insert hw]
      exact mem_sdiff.mpr ⟨hxA,h⟩
    exact mem_biUnion.mpr ⟨x,hxD,mem_filter.mpr
      ⟨(mem_filter.mp he).1,(mem_sdiff.mp hur).1,(mem_sdiff.mp hx).1⟩⟩
  calc
    _ ≤ ((insert w (closes H I w)).biUnion
        (fun x => H.filter (fun e => u ∈ e ∧ x ∈ e))).card := card_le_card hs
    _ ≤ ∑ x ∈ insert w (closes H I w), (H.filter (fun e => u ∈ e ∧ x ∈ e)).card := card_biUnion_le
    _ ≤ ∑ _x ∈ insert w (closes H I w), 1 := by
      apply sum_le_sum
      intro x hx
      exact hlin.pair_degree u x (fun h => huD (h ▸ hx))
    _ = _ := by simp [card_insert_of_notMem (notMem_closes_self H I w)]

/-- A bounded local increment as long as the tracked vertex survives. It is
    not asserted across the death of that vertex. -/
theorem incident_increment_bound {H : Finset (Finset α)} (hlin : Linear H)
    {I : Finset α} {u w : α} (hw : w ∈ available H I)
    (hu : u ∈ available H (insert w I)) (j : ℕ) :
    |((incident H (insert w I) j u).card:ℝ)-(incident H I j u).card| ≤
      (closes H I w).card+1 := by
  have huw : u ≠ w := by
    intro h
    exact (mem_available.mp hu).1 (by simp [h])
  have hb := incident_card_step hw huw j
  have hl := lost_card_le_closes hlin hw hu j
  have hp := promoted_card_le_one hlin I j huw
  have hbR : ((incident H (insert w I) j u).card:ℝ)+(localLost H I j u w).card =
      (incident H I j u).card+(localPromoted H I j u w).card := by exact_mod_cast hb
  have hlR : ((localLost H I j u w).card:ℝ) ≤ (closes H I w).card+1 := by exact_mod_cast hl
  have hpR : ((localPromoted H I j u w).card:ℝ) ≤ 1 := by exact_mod_cast hp
  have hnL : (0:ℝ) ≤ (localLost H I j u w).card := by positivity
  have hnP : (0:ℝ) ≤ (localPromoted H I j u w).card := by positivity
  have hnC : (0:ℝ) ≤ (closes H I w).card := by positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma localLost_two_eq {H : Finset (Finset α)} {I : Finset α} {u w : α}
    (hw : w ∈ available H I) (hu : u ∈ available H (insert w I)) :
    localLost H I 2 u w = (closes H I u ∩ closes H I w).biUnion (pairReps H I u) := by
  have hu0 := available_antitone (subset_insert w I) hu
  have huD : u ∉ insert w (closes H I w) := by
    rw [available_insert hw] at hu
    exact (mem_sdiff.mp hu).2
  ext e
  constructor
  · intro he
    obtain ⟨he,hur⟩ := mem_filter.mp he
    obtain ⟨he,hnot⟩ := mem_filter.mp he
    have hinc : e ∈ incident H I 2 u := mem_filter.mpr ⟨he,hur⟩
    obtain ⟨heH,x,hx,hux,heq⟩ := (incident_two_iff hu0).mp hinc
    have hxD : x ∈ insert w (closes H I w) := by
      by_contra h
      have hxa : x ∈ available H (insert w I) := by
        rw [available_insert hw]
        exact mem_sdiff.mpr ⟨hx,h⟩
      apply hnot
      rw [heq]
      exact insert_subset hu (singleton_subset_iff.mpr hxa)
    have hxw : x ≠ w := by
      intro hh
      have hclose : u ∈ closes H I w := mem_closes.mpr
        ⟨hu0,by simpa [hh] using hux,e,heH,by simpa [hh,pair_comm] using heq⟩
      exact huD (mem_insert_of_mem hclose)
    have hxc : x ∈ closes H I w := (mem_insert.mp hxD).resolve_left hxw
    have hxu : x ∈ closes H I u := mem_closes.mpr ⟨hx,hux.symm,e,heH,heq⟩
    exact mem_biUnion.mpr ⟨x,mem_inter.mpr ⟨hxu,hxc⟩,mem_filter.mpr ⟨heH,hux,heq⟩⟩
  · intro he
    obtain ⟨x,hx,he⟩ := mem_biUnion.mp he
    obtain ⟨hxu,hxw⟩ := mem_inter.mp hx
    obtain ⟨he,hux,heq⟩ := mem_filter.mp he
    have hinc := (incident_two_iff hu0).mpr
      ⟨he,x,closes_subset H I u hxu,hux,heq⟩
    obtain ⟨he,hur⟩ := mem_filter.mp hinc
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨he,?_⟩,hur⟩
    intro hs
    have hxr : x ∈ e \ I := by rw [heq]; simp
    have hxa := hs hxr
    rw [available_insert hw] at hxa
    exact (mem_sdiff.mp hxa).2 (mem_insert_of_mem hxw)

lemma localLost_two_card {H : Finset (Finset α)} (hlin : Linear H)
    {I : Finset α} {u w : α} (hw : w ∈ available H I)
    (hu : u ∈ available H (insert w I)) :
    (localLost H I 2 u w).card = commonDegree H I u w := by
  rw [localLost_two_eq hw hu]
  have hd : ((closes H I u ∩ closes H I w : Finset α):Set α).PairwiseDisjoint (pairReps H I u) := by
    intro x hx y hy hxy
    apply disjoint_left.mpr
    intro e hex hey
    obtain ⟨_,hux,heq⟩ := mem_filter.mp hex
    obtain ⟨_,_,hey⟩ := mem_filter.mp hey
    have hx : x ∈ ({u,y}:Finset α) := by rw [← hey,heq]; simp
    have hh := (mem_insert.mp hx).resolve_left hux.symm
    exact hxy (mem_singleton.mp hh)
  rw [card_biUnion hd]
  have hc (x : α) (hx : x ∈ closes H I u ∩ closes H I w) : (pairReps H I u x).card = 1 := by
    have hx := (mem_inter.mp hx).1
    have hne := (mem_closes.mp hx).2.1.symm
    have hn := card_pos.mpr ((pairReps_nonempty_iff (closes_subset H I u hx)).mpr hx)
    have hc := (pairReps_card_le H I u x).trans (hlin.pair_degree u x hne)
    omega
  rw [sum_congr rfl hc]
  simp [commonDegree]

/-- At a surviving tracked vertex, each common neighbor is exactly one lost
    two-edge, and there is at most one promoted edge. -/
theorem incident_two_increment_interval {H : Finset (Finset α)} (hlin : Linear H)
    {I : Finset α} {u w : α} (hw : w ∈ available H I)
    (hu : u ∈ available H (insert w I)) :
    -(commonDegree H I u w:ℝ) ≤
      ((incident H (insert w I) 2 u).card:ℝ)-(incident H I 2 u).card ∧
    ((incident H (insert w I) 2 u).card:ℝ)-(incident H I 2 u).card ≤
      1-(commonDegree H I u w:ℝ) := by
  have huw : u ≠ w := by
    intro h
    exact (mem_available.mp hu).1 (by simp [h])
  have hb := incident_card_step hw huw 2
  rw [localLost_two_card hlin hw hu] at hb
  have hp := promoted_card_le_one hlin I 2 huw
  have hbR : ((incident H (insert w I) 2 u).card:ℝ)+(commonDegree H I u w:ℝ) =
      (incident H I 2 u).card+(localPromoted H I 2 u w).card := by exact_mod_cast hb
  have hpR : ((localPromoted H I 2 u w).card:ℝ) ≤ 1 := by exact_mod_cast hp
  have hnP : (0:ℝ) ≤ (localPromoted H I 2 u w).card := by positivity
  constructor <;> linarith

theorem incident_two_increment_bound {H : Finset (Finset α)} (hlin : Linear H)
    {I : Finset α} {u w : α} (hw : w ∈ available H I)
    (hu : u ∈ available H (insert w I)) (C : ℕ)
    (hC : commonDegree H I u w ≤ C) :
    |((incident H (insert w I) 2 u).card:ℝ)-(incident H I 2 u).card| ≤ (C:ℝ)+1 := by
  obtain ⟨hl,hh⟩ := incident_two_increment_interval hlin hw hu
  have hCR : (commonDegree H I u w:ℝ) ≤ C := by exact_mod_cast hC
  have hnC : (0:ℝ) ≤ C := by positivity
  have hnd : (0:ℝ) ≤ commonDegree H I u w := by positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- Choices after which the tracked vertex is still available. -/
def safeChoices (H : Finset (Finset α)) (I : Finset α) (u : α) : Finset α :=
  (available H I).filter (fun w => u ∈ available H (insert w I))

lemma safeChoices_eq {H : Finset (Finset α)} {I : Finset α} {u : α}
    (hu : u ∈ available H I) : safeChoices H I u = available H I \ insert u (closes H I u) := by
  ext w
  constructor
  · intro hw
    obtain ⟨hw,hu'⟩ := mem_filter.mp hw
    rw [available_insert hw] at hu'
    have hun := (mem_sdiff.mp hu').2
    refine mem_sdiff.mpr ⟨hw,?_⟩
    intro hd
    rcases mem_insert.mp hd with rfl | hd
    · exact hun (mem_insert_self _ _)
    · exact hun (mem_insert_of_mem (closes_symm hu hd))
  · intro hw
    obtain ⟨hw,hn⟩ := mem_sdiff.mp hw
    refine mem_filter.mpr ⟨hw,?_⟩
    rw [available_insert hw]
    refine mem_sdiff.mpr ⟨hu,?_⟩
    intro hd
    rcases mem_insert.mp hd with hud | hd
    · exact hn (mem_insert.mpr (Or.inl hud.symm))
    · exact hn (mem_insert_of_mem (closes_symm hw hd))

lemma localPromoted_eq {H : Finset (Finset α)} (hlin : Linear H)
    (I : Finset α) (j : ℕ) (hj : 2 ≤ j) (u w : α) :
    localPromoted H I j u w = (incident H I (j+1) u).filter (fun e => w ∈ e \ I) := by
  rw [localPromoted,hlin.promoted_eq I j hj]
  ext e
  simp only [incident,mem_filter]
  tauto

/-- Every active (j+1)-edge through u has exactly j safe choices promoting it. -/
theorem sum_localPromoted {H : Finset (Finset α)} (hlin : Linear H)
    (I : Finset α) (j : ℕ) (hj : 2 ≤ j) (u : α) :
    (∑ w ∈ safeChoices H I u, (localPromoted H I j u w).card) =
      j*(incident H I (j+1) u).card := by
  simp_rw [localPromoted_eq hlin I j hj]
  have hs : (∑ w ∈ safeChoices H I u,
      ((incident H I (j+1) u).filter (fun e => w ∈ e \ I)).card) =
      ∑ e ∈ incident H I (j+1) u, ((safeChoices H I u).filter (fun w => w ∈ e \ I)).card :=
    sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := safeChoices H I u) (t := incident H I (j+1) u) (fun w e => w ∈ e \ I)
  rw [hs]
  have hc (e : Finset α) (he : e ∈ incident H I (j+1) u) :
      ((safeChoices H I u).filter (fun w => w ∈ e \ I)).card = j := by
    obtain ⟨he,hur⟩ := mem_filter.mp he
    have hs : (safeChoices H I u).filter (fun w => w ∈ e \ I) = (e \ I).erase u := by
      ext w
      constructor
      · intro hw
        obtain ⟨hw,hwr⟩ := mem_filter.mp hw
        obtain ⟨hw,hu⟩ := mem_filter.mp hw
        have hwu : w ≠ u := by intro h; exact (mem_available.mp hu).1 (by simp [h])
        exact mem_erase.mpr ⟨hwu,hwr⟩
      · intro hw
        obtain ⟨hwu,hwr⟩ := mem_erase.mp hw
        have hwa := (mem_filter.mp he).2.1 hwr
        have hu := hlin.residual_survives (by omega : 3 ≤ j+1) he hwr
          (mem_erase.mpr ⟨hwu.symm,hur⟩)
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨hwa,hu⟩,hwr⟩
    rw [hs,card_erase_of_mem hur,(mem_filter.mp he).2.2]
    omega
  rw [sum_congr rfl hc]
  simp [mul_comm]

/-- The sum of local increments, assigning zero to choices that close or
    select the tracked vertex. No probability or concentration claim is built
    into this definition. -/
def survivalDrift (H : Finset (Finset α)) (I : Finset α) (j : ℕ) (u : α) : ℝ :=
  ∑ w ∈ safeChoices H I u,
    (((incident H (insert w I) j u).card:ℝ)-(incident H I j u).card)

theorem survival_drift_balance {H : Finset (Finset α)} (hlin : Linear H)
    (I : Finset α) (j : ℕ) (hj : 2 ≤ j) (u : α) :
    survivalDrift H I j u + (∑ w ∈ safeChoices H I u, ((localLost H I j u w).card:ℝ)) =
      (j:ℝ)*(incident H I (j+1) u).card := by
  have hh : ∀ w ∈ safeChoices H I u,
      (((incident H (insert w I) j u).card:ℝ)-(incident H I j u).card)+
        (localLost H I j u w).card = (localPromoted H I j u w).card := by
    intro w hw
    obtain ⟨hw,hu⟩ := mem_filter.mp hw
    have huw : u ≠ w := by intro h; exact (mem_available.mp hu).1 (by simp [h])
    have hs := incident_card_step hw huw j
    have hsR : ((incident H (insert w I) j u).card:ℝ)+(localLost H I j u w).card =
        (incident H I j u).card+(localPromoted H I j u w).card := by exact_mod_cast hs
    linarith
  have hs := sum_congr (s₁ := safeChoices H I u) rfl hh
  rw [sum_add_distrib] at hs
  have hp : (∑ w ∈ safeChoices H I u, ((localPromoted H I j u w).card:ℝ)) =
      (j:ℝ)*(incident H I (j+1) u).card := by exact_mod_cast sum_localPromoted hlin I j hj u
  exact hs.trans hp

lemma common_sum_balance {H : Finset (Finset α)} {I : Finset α} {u : α}
    (hu : u ∈ available H I) :
    (∑ w ∈ safeChoices H I u, commonDegree H I u w) + (closes H I u).card +
      (∑ x ∈ closes H I u, commonDegree H I u x) =
        ∑ x ∈ closes H I u, (closes H I x).card := by
  have heq (w : α) (hw : w ∈ safeChoices H I u) :
      commonDegree H I u w = ((closes H I u).filter (fun x => w ∈ closes H I x)).card := by
    have hw := (mem_filter.mp hw).1
    unfold commonDegree
    congr 1
    ext x
    simp only [mem_inter,mem_filter]
    constructor
    · rintro ⟨hxu,hxw⟩
      exact ⟨hxu,closes_symm hw hxw⟩
    · rintro ⟨hxu,hwx⟩
      exact ⟨hxu,closes_symm (closes_subset H I u hxu) hwx⟩
  have hsum : (∑ w ∈ safeChoices H I u, commonDegree H I u w) =
      ∑ x ∈ closes H I u, ((safeChoices H I u).filter (fun w => w ∈ closes H I x)).card := by
    rw [sum_congr rfl heq]
    exact sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := safeChoices H I u) (t := closes H I u) (fun w x => w ∈ closes H I x)
  have hc (x : α) (hx : x ∈ closes H I u) :
      ((safeChoices H I u).filter (fun w => w ∈ closes H I x)).card+1+
        commonDegree H I u x = (closes H I x).card := by
    have hux := closes_symm hu hx
    have hs : (safeChoices H I u).filter (fun w => w ∈ closes H I x) =
        closes H I x \ insert u (closes H I u) := by
      rw [safeChoices_eq hu]
      ext w
      simp only [mem_filter,mem_sdiff]
      exact ⟨fun h => ⟨h.2,h.1.2⟩,
        fun h => ⟨⟨closes_subset H I x h.1,h.2⟩,h.1⟩⟩
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
      intro hm
      exact notMem_closes_self H I u (mem_inter.mp hm).1
    have hh := card_sdiff_add_card_inter (closes H I x) (insert u (closes H I u))
    rw [hi,card_insert_of_notMem hun] at hh
    rw [hs]
    change _+1+(closes H I u ∩ closes H I x).card = _
    omega
  rw [hsum]
  have hh := sum_congr (s₁ := closes H I u) rfl hc
  simpa only [sum_add_distrib,sum_const,nsmul_eq_mul,mul_one] using hh

/-- Exact two-degree drift on safe choices. The last sum is a genuine
    common-neighbor correction, not an assumed zero term. -/
theorem survival_drift_two {H : Finset (Finset α)} (hlin : Linear H)
    {I : Finset α} {u : α} (hu : u ∈ available H I) :
    survivalDrift H I 2 u =
      2*(incident H I 3 u).card - (∑ x ∈ closes H I u, ((incident H I 2 x).card:ℝ)) +
        (incident H I 2 u).card + (∑ x ∈ closes H I u, (commonDegree H I u x:ℝ)) := by
  have hb := survival_drift_balance hlin I 2 (by omega) u
  norm_num at hb
  have hl : (∑ w ∈ safeChoices H I u, ((localLost H I 2 u w).card:ℝ)) =
      ∑ w ∈ safeChoices H I u, (commonDegree H I u w:ℝ) := by
    apply sum_congr rfl
    intro w hw
    obtain ⟨hw,hu⟩ := mem_filter.mp hw
    rw [localLost_two_card hlin hw hu]
  rw [hl] at hb
  have hc := common_sum_balance hu
  have hd : (∑ x ∈ closes H I u, (closes H I x).card) =
      ∑ x ∈ closes H I u, (incident H I 2 x).card := by
    apply sum_congr rfl
    intro x hx
    exact (hlin.incident_two_card I x (closes_subset H I u hx)).symm
  rw [hd,← hlin.incident_two_card I u hu] at hc
  have hcR : (∑ w ∈ safeChoices H I u, (commonDegree H I u w:ℝ)) + (incident H I 2 u).card +
      (∑ x ∈ closes H I u, (commonDegree H I u x:ℝ)) =
        ∑ x ∈ closes H I u, ((incident H I 2 x).card:ℝ) := by exact_mod_cast hc
  linarith

/-- Conditional drift bounds from local-degree and common-neighbor controls.
    The hypotheses are not claimed to hold typically. -/
theorem survival_drift_two_bounds {H : Finset (Finset α)} (hlin : Linear H)
    {I : Finset α} {u : α} (hu : u ∈ available H I) (l h : ℝ) (C : ℕ)
    (hl : ∀ x ∈ closes H I u, l ≤ ((incident H I 2 x).card:ℝ))
    (hh : ∀ x ∈ closes H I u, ((incident H I 2 x).card:ℝ) ≤ h)
    (hC : ∀ x ∈ closes H I u, commonDegree H I u x ≤ C) :
    2*(incident H I 3 u).card-(h-1)*(incident H I 2 u).card ≤ survivalDrift H I 2 u ∧
      survivalDrift H I 2 u ≤
        2*(incident H I 3 u).card-(l-1-C)*(incident H I 2 u).card := by
  have hcard := hlin.incident_two_card I u hu
  have hlo : l*(incident H I 2 u).card ≤
      ∑ x ∈ closes H I u, ((incident H I 2 x).card:ℝ) := by
    calc
      _ = ∑ _x ∈ closes H I u, l := by simp [hcard,mul_comm]
      _ ≤ _ := sum_le_sum hl
  have hhi : (∑ x ∈ closes H I u, ((incident H I 2 x).card:ℝ)) ≤
      h*(incident H I 2 u).card := by
    calc
      _ ≤ ∑ _x ∈ closes H I u, h := sum_le_sum hh
      _ = _ := by simp [hcard,mul_comm]
  have hc : (∑ x ∈ closes H I u, (commonDegree H I u x:ℝ)) ≤
      (C:ℝ)*(incident H I 2 u).card := by
    calc
      _ ≤ ∑ _x ∈ closes H I u, (C:ℝ) := sum_le_sum (fun x hx => by exact_mod_cast hC x hx)
      _ = _ := by simp [hcard,mul_comm]
  have hn : 0 ≤ ∑ x ∈ closes H I u, (commonDegree H I u x:ℝ) :=
    sum_nonneg (fun _ _ => by positivity)
  rw [survival_drift_two hlin hu]
  constructor <;> nlinarith

#print axioms survival_drift_two_bounds
#print axioms sum_localPromoted
#print axioms survival_drift_balance
#print axioms common_sum_balance
#print axioms survival_drift_two
#print axioms localLost_two_card
#print axioms incident_two_increment_interval
#print axioms incident_two_increment_bound
#print axioms incident_card_step
#print axioms promoted_card_le_one
#print axioms lost_card_le_closes
#print axioms incident_increment_bound
end
end Erdos773.GreedyLinearLocal
