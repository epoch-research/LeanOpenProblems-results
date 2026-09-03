import Submission.FourUniformRegularization

/-!
Exact states and updates for greedy hypergraph independence. Residual edges
are indexed by their ORIGINAL edges; different contractions are not silently
identified. These identities do not constitute a random-greedy lower bound.
-/
namespace Erdos773.GreedyHypergraphState
open Finset FourUniformRegularization
set_option maxHeartbeats 1500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

def Independent (H : Finset (Finset α)) (I : Finset α) : Prop :=
  ∀ e ∈ H, ¬e ⊆ I

omit [Fintype α] [DecidableEq α] in
lemma Independent.mono {H : Finset (Finset α)} {I J : Finset α}
    (hI : Independent H I) (hJI : J ⊆ I) : Independent H J :=
  fun e he hsub => hI e he (hsub.trans hJI)

def available (H : Finset (Finset α)) (I : Finset α) : Finset α := by
  classical
  exact univ.filter (fun v => v ∉ I ∧ Independent H (insert v I))

lemma mem_available {H : Finset (Finset α)} {I : Finset α} {v : α} :
    v ∈ available H I ↔ v ∉ I ∧ Independent H (insert v I) := by
  classical
  simp [available]

lemma available_disjoint (H : Finset (Finset α)) (I : Finset α) :
    Disjoint (available H I) I :=
  disjoint_left.mpr (fun _ hv => (mem_available.mp hv).1)

lemma available_antitone {H : Finset (Finset α)} {I J : Finset α} (hIJ : I ⊆ J) :
    available H J ⊆ available H I := by
  intro v hv
  obtain ⟨hv,hind⟩ := mem_available.mp hv
  exact mem_available.mpr ⟨fun hi => hv (hIJ hi),hind.mono (insert_subset_insert v hIJ)⟩

lemma independent_of_available {H : Finset (Finset α)} {I : Finset α} {v : α}
    (hv : v ∈ available H I) : Independent H I :=
  (mem_available.mp hv).2.mono (subset_insert _ _)

/-- Original edges with exactly j still-unselected vertices, all available. -/
def active (H : Finset (Finset α)) (I : Finset α) (j : ℕ) : Finset (Finset α) :=
  H.filter (fun e => e \ I ⊆ available H I ∧ (e \ I).card = j)

def incident (H : Finset (Finset α)) (I : Finset α) (j : ℕ) (v : α) :=
  (active H I j).filter (fun e => v ∈ e \ I)

lemma mem_incident {H : Finset (Finset α)} {I e : Finset α} {j : ℕ} {v : α} :
    e ∈ incident H I j v ↔ e ∈ H ∧ e \ I ⊆ available H I ∧
      (e \ I).card = j ∧ v ∈ e \ I := by
  simp only [incident,active,mem_filter]
  tauto

lemma active_size_bounds {H : Finset (Finset α)} {I e : Finset α} {j r : ℕ}
    (hI : Independent H I) (hr : ∀ f ∈ H, f.card = r) (he : e ∈ active H I j) :
    2 ≤ j ∧ j ≤ r := by
  obtain ⟨he,hsub,hcard⟩ := mem_filter.mp he
  have hnon : (e \ I).Nonempty := sdiff_nonempty.mpr (hI e he)
  have hj0 : 0 < j := hcard ▸ card_pos.mpr hnon
  have hj1 : j ≠ 1 := by
    intro hj
    obtain ⟨v,hv⟩ := card_eq_one.mp (hcard.trans hj)
    have hm : v ∈ e \ I := by rw [hv]; simp
    have hi := (mem_available.mp (hsub hm)).2
    apply hi e he
    intro a ha
    by_cases hai : a ∈ I
    · exact mem_insert_of_mem hai
    · have ha' : a ∈ e \ I := mem_sdiff.mpr ⟨ha,hai⟩
      rw [hv] at ha'
      exact mem_insert.mpr (Or.inl (mem_singleton.mp ha'))
  constructor
  · omega
  · have hc := card_le_card (sdiff_subset : e \ I ⊆ e)
    rw [hcard,hr e he] at hc
    exact hc

/-- Available neighbors which are newly closed if v is selected. -/
def closes (H : Finset (Finset α)) (I : Finset α) (v : α) : Finset α := by
  classical
  exact (available H I).filter (fun w => w ≠ v ∧ ∃ e ∈ H, e \ I = {v,w})

lemma mem_closes {H : Finset (Finset α)} {I : Finset α} {v w : α} :
    w ∈ closes H I v ↔ w ∈ available H I ∧ w ≠ v ∧ ∃ e ∈ H, e \ I = {v,w} := by
  classical
  simp [closes]

lemma closes_subset (H : Finset (Finset α)) (I : Finset α) (v : α) :
    closes H I v ⊆ available H I := by
  classical
  exact filter_subset _ _

lemma notMem_closes_self (H : Finset (Finset α)) (I : Finset α) (v : α) :
    v ∉ closes H I v := by simp [mem_closes]

lemma closes_symm {H : Finset (Finset α)} {I : Finset α} {v w : α}
    (hv : v ∈ available H I) (hw : w ∈ closes H I v) : v ∈ closes H I w := by
  obtain ⟨hw,hwv,e,he,heq⟩ := mem_closes.mp hw
  exact mem_closes.mpr ⟨hv,hwv.symm,e,he,by simpa [pair_comm] using heq⟩

omit [Fintype α] in
lemma pair_residual_of_double_extension {e I : Finset α} {v w : α}
    (hv : v ∉ I) (hw : w ∉ I)
    (hsub : e ⊆ insert w (insert v I))
    (hnv : ¬ e ⊆ insert v I) (hnw : ¬ e ⊆ insert w I) :
    e \ I = {v,w} := by
  have hve : v ∈ e := by
    by_contra hvn
    apply hnw
    intro a ha
    have haa := mem_insert.mp (hsub ha)
    rcases haa with rfl | haa
    · simp
    rcases mem_insert.mp haa with rfl | haa
    · exact (hvn ha).elim
    · exact mem_insert_of_mem haa
  have hwe : w ∈ e := by
    by_contra hwn
    apply hnv
    intro a ha
    rcases mem_insert.mp (hsub ha) with rfl | haa
    · exact (hwn ha).elim
    · exact haa
  ext a
  simp only [mem_sdiff,mem_insert,mem_singleton]
  constructor
  · rintro ⟨ha,hai⟩
    have hh := hsub ha
    simp only [mem_insert] at hh
    tauto
  · rintro (rfl | rfl)
    · exact ⟨hve,hv⟩
    · exact ⟨hwe,hw⟩

/-- Exact update, including every shortened two-edge obstruction. -/
theorem available_insert {H : Finset (Finset α)} {I : Finset α} {v : α}
    (hv : v ∈ available H I) :
    available H (insert v I) = available H I \ insert v (closes H I v) := by
  ext w
  constructor
  · intro hw
    have hwold := available_antitone (subset_insert v I) hw
    have hwv : w ≠ v := by
      intro hh
      subst w
      exact (mem_available.mp hw).1 (mem_insert_self _ _)
    refine mem_sdiff.mpr ⟨hwold,?_⟩
    intro hmem
    rcases mem_insert.mp hmem with hmem | hmem
    · exact hwv hmem
    obtain ⟨_,_,e,he,heq⟩ := mem_closes.mp hmem
    apply (mem_available.mp hw).2 e he
    intro a ha
    by_cases hai : a ∈ I
    · exact mem_insert_of_mem (mem_insert_of_mem hai)
    have haa : a ∈ e \ I := mem_sdiff.mpr ⟨ha,hai⟩
    rw [heq] at haa
    simp only [mem_insert,mem_singleton] at haa ⊢
    tauto
  · intro hw
    obtain ⟨hwold,hwclosed⟩ := mem_sdiff.mp hw
    have hwv : w ≠ v := fun h => hwclosed (mem_insert.mpr (Or.inl h))
    have hwi := (mem_available.mp hwold).1
    refine mem_available.mpr ⟨by simpa only [mem_insert,not_or] using And.intro hwv hwi,?_⟩
    intro e he hsub
    have heq := pair_residual_of_double_extension (mem_available.mp hv).1 hwi
      hsub ((mem_available.mp hv).2 e he) ((mem_available.mp hwold).2 e he)
    exact hwclosed (mem_insert_of_mem (mem_closes.mpr ⟨hwold,hwv,e,he,heq⟩))

/-- The exact one-step loss in the number of available vertices. -/
theorem available_card_step {H : Finset (Finset α)} {I : Finset α} {v : α}
    (hv : v ∈ available H I) :
    (available H (insert v I)).card+1+(closes H I v).card = (available H I).card := by
  have hsub : insert v (closes H I v) ⊆ available H I :=
    insert_subset hv (closes_subset H I v)
  have hh := card_sdiff_add_card_eq_card hsub
  rw [card_insert_of_notMem (notMem_closes_self H I v),← available_insert hv] at hh
  omega

lemma incident_two_iff {H : Finset (Finset α)} {I e : Finset α} {v : α}
    (hv : v ∈ available H I) :
    e ∈ incident H I 2 v ↔ e ∈ H ∧
      ∃ w ∈ available H I, v ≠ w ∧ e \ I = {v,w} := by
  constructor
  · intro he
    obtain ⟨he,hsub,hcard,hve⟩ := mem_incident.mp he
    obtain ⟨a,b,hab,heq⟩ := card_eq_two.mp hcard
    rw [heq] at hve
    simp only [mem_insert,mem_singleton] at hve
    rcases hve with rfl | rfl
    · exact ⟨he,b,hsub (by rw [heq]; simp),hab,heq⟩
    · exact ⟨he,a,hsub (by rw [heq]; simp),hab.symm,by simpa [pair_comm] using heq⟩
  · rintro ⟨he,w,hw,hvw,heq⟩
    apply mem_incident.mpr
    refine ⟨he,?_,?_,?_⟩
    · rw [heq]
      intro a ha
      simp only [mem_insert,mem_singleton] at ha
      rcases ha with rfl | rfl <;> assumption
    · rw [heq]
      simp [hvw]
    · rw [heq]
      simp

/-- Multiplicity of a contracted two-edge, keeping original-edge indices. -/
def pairReps (H : Finset (Finset α)) (I : Finset α) (v w : α) :=
  H.filter (fun e => v ≠ w ∧ e \ I = {v,w})

lemma pairReps_nonempty_iff {H : Finset (Finset α)} {I : Finset α} {v w : α}
    (hw : w ∈ available H I) :
    (pairReps H I v w).Nonempty ↔ w ∈ closes H I v := by
  constructor
  · rintro ⟨e,he⟩
    obtain ⟨he,hvw,heq⟩ := mem_filter.mp he
    exact mem_closes.mpr ⟨hw,hvw.symm,e,he,heq⟩
  · intro hc
    obtain ⟨_,hwv,e,he,heq⟩ := mem_closes.mp hc
    exact ⟨e,mem_filter.mpr ⟨he,hwv.symm,heq⟩⟩

omit [Fintype α] in
lemma pairReps_card_le (H : Finset (Finset α)) (I : Finset α) (v w : α) :
    (pairReps H I v w).card ≤ pairDegree H v w := by
  apply card_le_card
  intro e he
  obtain ⟨he,hvw,heq⟩ := mem_filter.mp he
  have hv : v ∈ e \ I := by rw [heq]; simp
  have hw : w ∈ e \ I := by rw [heq]; simp
  exact mem_filter.mpr ⟨he,(mem_sdiff.mp hv).1,(mem_sdiff.mp hw).1⟩

lemma pair_fiber_card {H : Finset (Finset α)} {I e : Finset α} {v : α}
    (hv : v ∈ available H I) (he : e ∈ H) :
    ((available H I).filter (fun w => v ≠ w ∧ e \ I = {v,w})).card =
      if e ∈ incident H I 2 v then 1 else 0 := by
  classical
  by_cases hinc : e ∈ incident H I 2 v
  · rw [if_pos hinc]
    obtain ⟨_,w,hw,hvw,heq⟩ := (incident_two_iff hv).mp hinc
    have hh : (available H I).filter (fun w => v ≠ w ∧ e \ I = {v,w}) = {w} := by
      ext z
      constructor
      · intro hz
        obtain ⟨hz,hvz,hez⟩ := mem_filter.mp hz
        have hm : z ∈ ({v,w} : Finset α) := by rw [← heq,hez]; simp
        simp only [mem_insert,mem_singleton] at hm
        rcases hm with h | h
        · exact (hvz h.symm).elim
        · exact mem_singleton.mpr h
      · intro hz
        have hz := mem_singleton.mp hz
        subst z
        exact mem_filter.mpr ⟨hw,hvw,heq⟩
    rw [hh,card_singleton]
  · rw [if_neg hinc]
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨hw,hvw,heq⟩ := mem_filter.mp hw
    exact hinc ((incident_two_iff hv).mpr ⟨he,w,hw,hvw,heq⟩)

lemma incident_subset (H : Finset (Finset α)) (I : Finset α) (j : ℕ) (v : α) :
    incident H I j v ⊆ H := by
  intro e he
  exact (mem_incident.mp he).1

/-- Exact multiplicity count for the neighborhood closed by selecting v. -/
theorem incident_two_card {H : Finset (Finset α)} {I : Finset α} {v : α}
    (hv : v ∈ available H I) :
    (incident H I 2 v).card = ∑ w ∈ closes H I v, (pairReps H I v w).card := by
  classical
  have hsum : (∑ w ∈ available H I, (pairReps H I v w).card) =
      (incident H I 2 v).card := by
    calc
      _ = ∑ e ∈ H,
          ((available H I).filter (fun w => v ≠ w ∧ e \ I = {v,w})).card :=
        sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun w e => v ≠ w ∧ e \ I = {v,w})
      _ = ∑ e ∈ H, if e ∈ incident H I 2 v then (1:ℕ) else 0 :=
        sum_congr rfl (fun e he => pair_fiber_card hv he)
      _ = _ := by
        rw [← sum_filter]
        have hf : H.filter (fun e => e ∈ incident H I 2 v) = incident H I 2 v := by
          ext e
          simp only [mem_filter]
          exact ⟨fun h => h.2,fun h => ⟨incident_subset H I 2 v h,h⟩⟩
        rw [hf]
        simp
  rw [← hsum]
  symm
  apply sum_subset (closes_subset H I v)
  intro w hw hnc
  apply card_eq_zero.mpr
  exact not_nonempty_iff_eq_empty.mp (fun h => hnc ((pairReps_nonempty_iff hw).mp h))

/-- Counting contracted edges with multiplicity can only overcount closures. -/
theorem closes_card_le_incident {H : Finset (Finset α)} {I : Finset α} {v : α}
    (hv : v ∈ available H I) :
    (closes H I v).card ≤ (incident H I 2 v).card := by
  rw [incident_two_card hv]
  calc
    _ = ∑ _w ∈ closes H I v, (1:ℕ) := by simp
    _ ≤ _ := by
      apply sum_le_sum
      intro w hw
      exact card_pos.mpr ((pairReps_nonempty_iff (closes_subset H I v hw)).mpr hw)

lemma incident_card_le_mul_closes {H : Finset (Finset α)} {I : Finset α} {v : α}
    (hv : v ∈ available H I) (K : ℕ)
    (hK : ∀ w : α, v ≠ w → pairDegree H v w ≤ K) :
    (incident H I 2 v).card ≤ K*(closes H I v).card := by
  rw [incident_two_card hv]
  calc
    _ ≤ ∑ _w ∈ closes H I v, K := sum_le_sum (fun w hw =>
      (pairReps_card_le H I v w).trans (hK w (mem_closes.mp hw).2.1.symm))
    _ = _ := by simp [mul_comm]

def duplicateExcess (H : Finset (Finset α)) (I : Finset α) (v : α) : ℕ :=
  ∑ w ∈ closes H I v, ((pairReps H I v w).card-1)

/-- The precise correction to the naive degree-based closure count. -/
theorem incident_card_eq_closes_add_excess {H : Finset (Finset α)}
    {I : Finset α} {v : α} (hv : v ∈ available H I) :
    (incident H I 2 v).card = (closes H I v).card+duplicateExcess H I v := by
  rw [incident_two_card hv]
  have hp (w : α) (hw : w ∈ closes H I v) : 1 ≤ (pairReps H I v w).card :=
    card_pos.mpr ((pairReps_nonempty_iff (closes_subset H I v hw)).mpr hw)
  calc
    _ = ∑ w ∈ closes H I v, (1+((pairReps H I v w).card-1)) :=
      sum_congr rfl (fun w hw => (Nat.add_sub_of_le (hp w hw)).symm)
    _ = _ := by simp [sum_add_distrib,duplicateExcess]

/-- Degree sums for every residual-edge size, with original multiplicities. -/
theorem sum_incident_card (H : Finset (Finset α)) (I : Finset α) (j : ℕ) :
    (∑ v ∈ available H I, (incident H I j v).card) = j*(active H I j).card := by
  calc
    _ = ∑ e ∈ active H I j, ((available H I).filter (fun v => v ∈ e \ I)).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun v e => v ∈ e \ I)
    _ = ∑ e ∈ active H I j, j := by
      apply sum_congr rfl
      intro e he
      obtain ⟨_,hsub,hcard⟩ := mem_filter.mp he
      have hf : (available H I).filter (fun v => v ∈ e \ I) = e \ I := by
        ext v
        simp only [mem_filter]
        exact ⟨fun h => h.2,fun h => ⟨hsub h,h⟩⟩
      rw [hf,hcard]
    _ = _ := by simp [mul_comm]

/-- An integer form of the exact first-moment identity for one uniform choice. -/
theorem sum_available_card_step (H : Finset (Finset α)) (I : Finset α) :
    (∑ v ∈ available H I, (available H (insert v I)).card)+
      (available H I).card+(∑ v ∈ available H I, (closes H I v).card) =
        (available H I).card^2 := by
  have hh := sum_congr (s₁ := available H I) rfl (fun v hv => available_card_step hv)
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,mul_one] at hh
  nlinarith only [hh]

/-- The multiplicity correction is kept in the averaged drift rather than
    assuming all residual two-edges are distinct. -/
theorem sum_available_card_step_with_excess (H : Finset (Finset α)) (I : Finset α) :
    (∑ v ∈ available H I, (available H (insert v I)).card)+
      (available H I).card+2*(active H I 2).card =
        (available H I).card^2+(∑ v ∈ available H I, duplicateExcess H I v) := by
  have hsum := sum_congr (s₁ := available H I) rfl (fun v hv => incident_card_eq_closes_add_excess hv)
  rw [sum_add_distrib,sum_incident_card H I 2] at hsum
  have hstep := sum_available_card_step H I
  omega

/-- Exact expected number of available vertices after a uniformly random
    available choice, expressed as a finite real average. -/
theorem average_available_card_step {H : Finset (Finset α)} {I : Finset α}
    (hA : (available H I).Nonempty) :
    (∑ v ∈ available H I, ((available H (insert v I)).card:ℝ))/(available H I).card =
      (available H I).card-1-
        (2*(active H I 2).card-(∑ v ∈ available H I, (duplicateExcess H I v:ℝ)))/
          (available H I).card := by
  have hp : (0:ℝ) < (available H I).card := by exact_mod_cast card_pos.mpr hA
  have hh : (∑ v ∈ available H I, ((available H (insert v I)).card:ℝ))+
      (available H I).card+2*(active H I 2).card =
        (available H I).card^2+(∑ v ∈ available H I, (duplicateExcess H I v:ℝ)) := by
    exact_mod_cast sum_available_card_step_with_excess H I
  apply (div_eq_iff hp.ne').mpr
  field_simp
  nlinarith only [hh]

/-- Old j-edges whose whole residual survives the choice. -/
def surviving (H : Finset (Finset α)) (I : Finset α) (j : ℕ) (v : α) :=
  (active H I j).filter (fun e => e \ I ⊆ available H (insert v I))

/-- Old (j+1)-edges contracted by the chosen vertex, all other vertices surviving. -/
def promoted (H : Finset (Finset α)) (I : Finset α) (j : ℕ) (v : α) :=
  (active H I (j+1)).filter (fun e => v ∈ e \ I ∧
    (e \ I).erase v ⊆ available H (insert v I))

def lost (H : Finset (Finset α)) (I : Finset α) (j : ℕ) (v : α) :=
  (active H I j).filter (fun e => ¬e \ I ⊆ available H (insert v I))

omit [Fintype α] in
lemma residual_insert (e I : Finset α) (v : α) : e \ insert v I = (e \ I).erase v := by
  ext a
  simp only [mem_sdiff,mem_insert,mem_erase,not_or]
  tauto

lemma active_insert_split {H : Finset (Finset α)} {I : Finset α} {v : α}
    (hv : v ∈ available H I) (j : ℕ) :
    active H (insert v I) j = surviving H I j v ∪ promoted H I j v := by
  ext e
  constructor
  · intro he
    obtain ⟨he,hsub,hcard⟩ := mem_filter.mp he
    rw [residual_insert] at hsub hcard
    have hold : e \ I ⊆ available H I := by
      intro a ha
      by_cases hav : a = v
      · simpa [hav] using hv
      · exact available_antitone (subset_insert v I) (hsub (mem_erase.mpr ⟨hav,ha⟩))
    by_cases hve : v ∈ e \ I
    · apply mem_union_right
      have hc : (e \ I).card = j+1 := by
        rw [card_erase_of_mem hve] at hcard
        have hp := card_pos.mpr ⟨v,hve⟩
        omega
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨he,hold,hc⟩,hve,hsub⟩
    · apply mem_union_left
      rw [erase_eq_of_notMem hve] at hsub hcard
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨he,hold,hcard⟩,hsub⟩
  · intro he
    rcases mem_union.mp he with he | he
    · obtain ⟨he,hsub⟩ := mem_filter.mp he
      obtain ⟨he,hold,hcard⟩ := mem_filter.mp he
      have hve : v ∉ e \ I := by
        intro hv'
        exact (mem_available.mp (hsub hv')).1 (mem_insert_self _ _)
      apply mem_filter.mpr
      rw [residual_insert,erase_eq_of_notMem hve]
      exact ⟨he,hsub,hcard⟩
    · obtain ⟨he,hve,hsub⟩ := mem_filter.mp he
      obtain ⟨he,hold,hcard⟩ := mem_filter.mp he
      apply mem_filter.mpr
      rw [residual_insert]
      refine ⟨he,hsub,?_⟩
      rw [card_erase_of_mem hve,hcard]
      omega

lemma surviving_promoted_disjoint (H : Finset (Finset α)) (I : Finset α) (j : ℕ) (v : α) :
    Disjoint (surviving H I j v) (promoted H I j v) := by
  apply disjoint_left.mpr
  intro e he hf
  have hc := (mem_filter.mp (mem_filter.mp he).1).2.2
  have hd := (mem_filter.mp (mem_filter.mp hf).1).2.2
  omega

/-- Exact active-edge count update. Destruction by newly closed vertices is
    included, not just contraction by the selected vertex. -/
theorem active_card_step {H : Finset (Finset α)} {I : Finset α} {v : α}
    (hv : v ∈ available H I) (j : ℕ) :
    (active H (insert v I) j).card+(lost H I j v).card =
      (active H I j).card+(promoted H I j v).card := by
  rw [active_insert_split hv j,card_union_of_disjoint (surviving_promoted_disjoint H I j v)]
  have hh : (surviving H I j v).card+(lost H I j v).card = (active H I j).card :=
    card_filter_add_card_filter_not _
  omega

#print axioms sum_incident_card
#print axioms average_available_card_step
#print axioms active_card_step
#print axioms incident_two_card
#print axioms closes_card_le_incident
#print axioms incident_card_le_mul_closes
#print axioms incident_card_eq_closes_add_excess
#print axioms active_size_bounds
#print axioms available_insert
#print axioms available_card_step
end
end Erdos773.GreedyHypergraphState
