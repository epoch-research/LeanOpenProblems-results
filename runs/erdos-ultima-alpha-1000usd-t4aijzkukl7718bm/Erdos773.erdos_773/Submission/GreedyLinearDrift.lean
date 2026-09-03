import Submission.GreedyCommonNeighbors

/-!
First-moment drift bounds for a linear hypergraph. Newly closed vertices are
included in edge losses. These identities are not a running-time theorem.
-/
namespace Erdos773.GreedyLinearDrift
open Finset GreedyHypergraphState GreedyCommonNeighbors FourUniformRegularization
set_option maxHeartbeats 2500000
noncomputable section
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- A finite Bonferroni bound with only a uniform intersection hypothesis. -/
theorem union_card_lower (S : Finset β) (C : β → Finset α) (K : ℕ) :
    (∀ i ∈ S, ∀ j ∈ S, i ≠ j → (C i ∩ C j).card ≤ K) →
      (∑ i ∈ S, (C i).card) ≤ (S.biUnion C).card + S.card.choose 2*K := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    intro hK
    have hi := ih (fun i hi j hj hij => hK i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij)
    have hinter : C a ∩ S.biUnion C = S.biUnion (fun i => C a ∩ C i) := by
      ext x
      simp only [mem_inter, mem_biUnion]
      aesop
    have hc : (C a ∩ S.biUnion C).card ≤ S.card*K := by
      rw [hinter]
      calc
        _ ≤ ∑ i ∈ S, (C a ∩ C i).card := card_biUnion_le
        _ ≤ ∑ _i ∈ S, K := sum_le_sum (fun i hi => hK a (mem_insert_self _ _)
          i (mem_insert_of_mem hi) (fun h => ha (h ▸ hi)))
        _ = _ := by simp
    have hu := card_union_add_card_inter (C a) (S.biUnion C)
    rw [sum_insert ha, biUnion_insert, card_insert_of_notMem ha]
    have hchoose : (S.card+1).choose 2 = S.card.choose 2 + S.card := by
      rw [Nat.choose_succ_succ]
      simp [Nat.add_comm]
    rw [hchoose, Nat.add_mul]
    omega

variable [Fintype α]

def Linear (H : Finset (Finset α)) : Prop :=
  ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 1

omit [Fintype α] [DecidableEq β] in
lemma Linear.pair_unique {H : Finset (Finset α)} (hlin : Linear H)
    {e f : Finset α} (he : e ∈ H) (hf : f ∈ H)
    {u v : α} (huv : u ≠ v) (hue : u ∈ e) (hve : v ∈ e) (huf : u ∈ f) (hvf : v ∈ f) : e = f := by
  by_contra hef
  have hs : ({u,v}:Finset α) ⊆ e ∩ f := by
    simp only [insert_subset_iff, singleton_subset_iff, mem_inter]
    exact ⟨⟨hue,huf⟩,hve,hvf⟩
  have hc := (card_le_card hs).trans (hlin e he f hf hef)
  simp [huv] at hc

omit [Fintype α] [DecidableEq β] in
lemma Linear.pair_degree {H : Finset (Finset α)} (hlin : Linear H)
    (u v : α) (huv : u ≠ v) : pairDegree H u v ≤ 1 := by
  apply card_le_one.mpr
  intro e he f hf
  obtain ⟨he,hu,hv⟩ := mem_filter.mp he
  obtain ⟨hf,hu',hv'⟩ := mem_filter.mp hf
  exact hlin.pair_unique he hf huv hu hv hu' hv'

omit [DecidableEq β] in
lemma Linear.incident_two_card {H : Finset (Finset α)} (hlin : Linear H)
    (I : Finset α) (v : α) (hv : v ∈ available H I) :
    (incident H I 2 v).card = (closes H I v).card := by
  apply Nat.le_antisymm _ (closes_card_le_incident hv)
  simpa using incident_card_le_mul_closes hv 1 (hlin.pair_degree v)

omit [DecidableEq β] in
/-- An active residual of size at least three contains no adjacent pair in
    the residual two-graph of a linear original hypergraph. -/
lemma Linear.no_internal_closure {H : Finset (Finset α)} (hlin : Linear H)
    {I e : Finset α} {j : ℕ} (hj : 3 ≤ j) (he : e ∈ active H I j)
    {u v : α} (hu : u ∈ e \ I) (hv : v ∈ e \ I) : v ∉ closes H I u := by
  intro hclose
  obtain ⟨_,hvu,f,hf,hfq⟩ := mem_closes.mp hclose
  obtain ⟨he,hsub,hcard⟩ := mem_filter.mp he
  have huf : u ∈ f := by
    have hh : u ∈ f \ I := by rw [hfq]; simp
    exact (mem_sdiff.mp hh).1
  have hvf : v ∈ f := by
    have hh : v ∈ f \ I := by rw [hfq]; simp
    exact (mem_sdiff.mp hh).1
  have hef := hlin.pair_unique he hf hvu.symm (mem_sdiff.mp hu).1 (mem_sdiff.mp hv).1 huf hvf
  rw [hef,hfq] at hcard
  have hc : ({u,v}:Finset α).card = 2 := by simp [hvu.symm]
  omega

omit [DecidableEq β] in
lemma Linear.residual_survives {H : Finset (Finset α)} (hlin : Linear H)
    {I e : Finset α} {j : ℕ} (hj : 3 ≤ j) (he : e ∈ active H I j)
    {v : α} (hv : v ∈ e \ I) : (e \ I).erase v ⊆ available H (insert v I) := by
  have hsub := (mem_filter.mp he).2.1
  rw [available_insert (hsub hv)]
  intro u hu
  obtain ⟨huv,hu⟩ := mem_erase.mp hu
  apply mem_sdiff.mpr
  refine ⟨hsub hu,?_⟩
  simp only [mem_insert, not_or]
  exact ⟨huv,hlin.no_internal_closure hj he hv hu⟩

omit [DecidableEq β] in
/-- For target size at least two, every selected vertex of an active larger
    edge promotes that edge; there is no additional closure loss. -/
theorem Linear.promoted_eq {H : Finset (Finset α)} (hlin : Linear H)
    (I : Finset α) (j : ℕ) (hj : 2 ≤ j) (v : α) :
    promoted H I j v = incident H I (j+1) v := by
  ext e
  simp only [promoted, incident, mem_filter]
  exact ⟨fun h => ⟨h.1,h.2.1⟩,
    fun h => ⟨h.1,h.2,hlin.residual_survives (by omega) h.1 h.2⟩⟩

omit [DecidableEq β] in
theorem Linear.sum_promoted {H : Finset (Finset α)} (hlin : Linear H)
    (I : Finset α) (j : ℕ) (hj : 2 ≤ j) :
    (∑ v ∈ available H I, (promoted H I j v).card) = (j+1)*(active H I (j+1)).card := by
  simp_rw [hlin.promoted_eq I j hj]
  exact sum_incident_card H I (j+1)

/-- Choices which destroy a given active edge rather than leave its old size
    unchanged. This includes choosing one of its residual vertices. -/
def lossChoices (H : Finset (Finset α)) (I e : Finset α) : Finset α :=
  (available H I).filter (fun v => ¬e \ I ⊆ available H (insert v I))

/-- The available neighbors of every residual vertex. -/
def closureUnion (H : Finset (Finset α)) (I e : Finset α) : Finset α :=
  (e \ I).biUnion (closes H I)

omit [DecidableEq β] in
theorem lossChoices_eq {H : Finset (Finset α)} {I e : Finset α} {j : ℕ}
    (he : e ∈ active H I j) :
    lossChoices H I e = (e \ I) ∪ closureUnion H I e := by
  have hs := (mem_filter.mp he).2.1
  ext v
  constructor
  · intro hv
    obtain ⟨hv,hnot⟩ := mem_filter.mp hv
    obtain ⟨u,hu,hu'⟩ := not_subset.mp hnot
    rw [available_insert hv] at hu'
    have hh : u ∈ insert v (closes H I v) := by
      by_contra h
      exact hu' (mem_sdiff.mpr ⟨hs hu,h⟩)
    rcases mem_insert.mp hh with rfl | hclose
    · exact mem_union_left _ hu
    · exact mem_union_right _ (mem_biUnion.mpr ⟨u,hu,closes_symm hv hclose⟩)
  · intro hv
    rcases mem_union.mp hv with hv | hv
    · refine mem_filter.mpr ⟨hs hv,?_⟩
      intro hsub
      exact (mem_available.mp (hsub hv)).1 (mem_insert_self _ _)
    · obtain ⟨u,hu,hv⟩ := mem_biUnion.mp hv
      have hva := closes_subset H I u hv
      refine mem_filter.mpr ⟨hva,?_⟩
      intro hsub
      have hh := hsub hu
      rw [available_insert hva] at hh
      exact (mem_sdiff.mp hh).2 (mem_insert_of_mem (closes_symm (hs hu) hv))

omit [DecidableEq β] in
lemma Linear.residual_disjoint_closureUnion {H : Finset (Finset α)} (hlin : Linear H)
    {I e : Finset α} {j : ℕ} (hj : 3 ≤ j) (he : e ∈ active H I j) :
    Disjoint (e \ I) (closureUnion H I e) := by
  apply disjoint_left.mpr
  intro v hv hv'
  obtain ⟨u,hu,hv'⟩ := mem_biUnion.mp hv'
  exact hlin.no_internal_closure hj he hu hv hv'

omit [DecidableEq β] in
lemma Linear.lossChoices_card {H : Finset (Finset α)} (hlin : Linear H)
    {I e : Finset α} {j : ℕ} (hj : 3 ≤ j) (he : e ∈ active H I j) :
    (lossChoices H I e).card = j+(closureUnion H I e).card := by
  rw [lossChoices_eq he,card_union_of_disjoint (hlin.residual_disjoint_closureUnion hj he),
    (mem_filter.mp he).2.2]

omit [DecidableEq β] in
lemma lossChoices_two {H : Finset (Finset α)} {I e : Finset α}
    (he : e ∈ active H I 2) : lossChoices H I e = closureUnion H I e := by
  rw [lossChoices_eq he]
  apply union_eq_right.mpr
  obtain ⟨he,hs,hcard⟩ := mem_filter.mp he
  obtain ⟨u,v,huv,hev⟩ := card_eq_two.mp hcard
  intro a ha
  have hmem : u ∈ e \ I ∧ v ∈ e \ I := by rw [hev]; simp
  rw [hev] at ha
  rcases mem_insert.mp ha with rfl | ha
  · exact mem_biUnion.mpr ⟨v,hmem.2,mem_closes.mpr
      ⟨hs hmem.1,huv,e,he,by simpa [pair_comm] using hev⟩⟩
  · have ha := mem_singleton.mp ha
    subst a
    exact mem_biUnion.mpr ⟨u,hmem.1,mem_closes.mpr ⟨hs hmem.2,huv.symm,e,he,hev⟩⟩

omit [DecidableEq β] in
lemma closureUnion_card_bounds {H : Finset (Finset α)} {I e : Finset α} {j C : ℕ}
    (he : e ∈ active H I j)
    (hC : ∀ u ∈ available H I, ∀ v ∈ available H I, u ≠ v → commonDegree H I u v ≤ C) :
    (closureUnion H I e).card ≤ ∑ u ∈ e \ I, (closes H I u).card ∧
      (∑ u ∈ e \ I, (closes H I u).card) ≤ (closureUnion H I e).card+j.choose 2*C := by
  have hs := (mem_filter.mp he).2.1
  refine ⟨card_biUnion_le,?_⟩
  have hh := union_card_lower (e \ I) (closes H I) C
    (fun u hu v hv huv => hC u (hs hu) v (hs hv) huv)
  rw [(mem_filter.mp he).2.2] at hh
  exact hh

/-- Incidence weighted by the exact residual-two-graph degree. -/
def weightedClosure (H : Finset (Finset α)) (I : Finset α) (j : ℕ) : ℕ :=
  ∑ v ∈ available H I, (incident H I j v).card*(closes H I v).card

omit [DecidableEq β] in
lemma weightedClosure_eq (H : Finset (Finset α)) (I : Finset α) (j : ℕ) :
    weightedClosure H I j = ∑ e ∈ active H I j, ∑ u ∈ e \ I, (closes H I u).card := by
  calc
    _ = ∑ u ∈ available H I, ∑ e ∈ active H I j,
        if u ∈ e \ I then (closes H I u).card else 0 := by
      simp only [weightedClosure,incident,card_filter,sum_mul,ite_mul,one_mul,zero_mul]
    _ = ∑ e ∈ active H I j, ∑ u ∈ available H I,
        if u ∈ e \ I then (closes H I u).card else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro e he
      rw [← sum_filter]
      have hf : (available H I).filter (fun u => u ∈ e \ I) = e \ I := by
        ext u
        simp only [mem_filter]
        exact ⟨And.right,fun h => ⟨(mem_filter.mp he).2.1 h,h⟩⟩
      rw [hf]

omit [DecidableEq β] in
lemma sum_lost_eq (H : Finset (Finset α)) (I : Finset α) (j : ℕ) :
    (∑ v ∈ available H I, (lost H I j v).card) =
      ∑ e ∈ active H I j, (lossChoices H I e).card := by
  exact sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := available H I) (t := active H I j)
    (fun (v : α) (e : Finset α) => ¬e \ I ⊆ available H (insert v I))

omit [DecidableEq β] in
/-- The union-overlap error is the ONLY error in the global loss count for
    residual sizes at least three in a linear original hypergraph. -/
theorem Linear.loss_bounds {H : Finset (Finset α)} (hlin : Linear H)
    (I : Finset α) (j : ℕ) (hj : 3 ≤ j) (C : ℕ)
    (hC : ∀ u ∈ available H I, ∀ v ∈ available H I, u ≠ v → commonDegree H I u v ≤ C) :
    (∑ v ∈ available H I, (lost H I j v).card) ≤ j*(active H I j).card+weightedClosure H I j ∧
      j*(active H I j).card+weightedClosure H I j ≤
        (∑ v ∈ available H I, (lost H I j v).card)+j.choose 2*C*(active H I j).card := by
  rw [sum_lost_eq,weightedClosure_eq]
  have hbase : j*(active H I j).card + (∑ e ∈ active H I j, ∑ u ∈ e \ I, (closes H I u).card) =
      ∑ e ∈ active H I j, (j+∑ u ∈ e \ I, (closes H I u).card) := by
    simp [sum_add_distrib,mul_comm]
  rw [hbase]
  constructor
  · apply sum_le_sum
    intro e he
    rw [hlin.lossChoices_card hj he]
    exact Nat.add_le_add_left (closureUnion_card_bounds he hC).1 j
  · calc
      _ ≤ ∑ e ∈ active H I j, ((lossChoices H I e).card+j.choose 2*C) := by
        apply sum_le_sum
        intro e he
        rw [hlin.lossChoices_card hj he]
        have hh := (closureUnion_card_bounds he hC).2
        omega
      _ = _ := by simp [sum_add_distrib,mul_comm]

omit [DecidableEq β] in
/-- A two-edge is already covered by the neighborhoods of its endpoints;
    it must NOT contribute an extra direct-selection loss of two. -/
theorem loss_two_bounds (H : Finset (Finset α)) (I : Finset α) (C : ℕ)
    (hC : ∀ u ∈ available H I, ∀ v ∈ available H I, u ≠ v → commonDegree H I u v ≤ C) :
    (∑ v ∈ available H I, (lost H I 2 v).card) ≤ weightedClosure H I 2 ∧
      weightedClosure H I 2 ≤
        (∑ v ∈ available H I, (lost H I 2 v).card)+C*(active H I 2).card := by
  rw [sum_lost_eq,weightedClosure_eq]
  constructor
  · apply sum_le_sum
    intro e he
    rw [lossChoices_two he]
    exact (closureUnion_card_bounds he hC).1
  · calc
      _ ≤ ∑ e ∈ active H I 2, ((lossChoices H I e).card+C) := by
        apply sum_le_sum
        intro e he
        rw [lossChoices_two he]
        simpa using (closureUnion_card_bounds he hC).2
      _ = _ := by simp [sum_add_distrib,mul_comm]

omit [DecidableEq β] in
lemma sum_active_card_step (H : Finset (Finset α)) (I : Finset α) (j : ℕ) :
    (∑ v ∈ available H I, (active H (insert v I) j).card)+
      (∑ v ∈ available H I, (lost H I j v).card) =
        (available H I).card*(active H I j).card+
          (∑ v ∈ available H I, (promoted H I j v).card) := by
  have hh := sum_congr (s₁ := available H I) rfl (fun v hv => active_card_step hv j)
  simpa only [sum_add_distrib,sum_const,nsmul_eq_mul] using hh

/-- Sum of the changes in the global active-edge count over all available
    choices, before division by the number of choices. -/
def driftSum (H : Finset (Finset α)) (I : Finset α) (j : ℕ) : ℝ :=
  (∑ v ∈ available H I, ((active H (insert v I) j).card:ℝ))-
    (available H I).card*(active H I j).card

omit [DecidableEq β] in
lemma Linear.drift_balance {H : Finset (Finset α)} (hlin : Linear H)
    (I : Finset α) (j : ℕ) (hj : 2 ≤ j) :
    driftSum H I j + (∑ v ∈ available H I, ((lost H I j v).card:ℝ)) =
      ((j:ℝ)+1)*(active H I (j+1)).card := by
  have hh := sum_active_card_step H I j
  rw [hlin.sum_promoted I j hj] at hh
  have hhR : (∑ v ∈ available H I, ((active H (insert v I) j).card:ℝ))+
      (∑ v ∈ available H I, ((lost H I j v).card:ℝ)) =
      (available H I).card*(active H I j).card+((j:ℝ)+1)*(active H I (j+1)).card := by
    exact_mod_cast hh
  unfold driftSum
  linarith

omit [DecidableEq β] in
/-- Global first-moment drift interval, with the common-neighbor error
    displayed explicitly. No concentration or typical-degree claim is made. -/
theorem Linear.drift_bounds {H : Finset (Finset α)} (hlin : Linear H)
    (I : Finset α) (j : ℕ) (hj : 3 ≤ j) (C : ℕ)
    (hC : ∀ u ∈ available H I, ∀ v ∈ available H I, u ≠ v → commonDegree H I u v ≤ C) :
    ((j:ℝ)+1)*(active H I (j+1)).card-j*(active H I j).card-weightedClosure H I j ≤
      driftSum H I j ∧
    driftSum H I j ≤ ((j:ℝ)+1)*(active H I (j+1)).card-j*(active H I j).card-
      weightedClosure H I j+(j.choose 2:ℝ)*C*(active H I j).card := by
  obtain ⟨hlo,hhi⟩ := hlin.loss_bounds I j hj C hC
  have hloR : (∑ v ∈ available H I, ((lost H I j v).card:ℝ)) ≤
      (j:ℝ)*(active H I j).card+weightedClosure H I j := by exact_mod_cast hlo
  have hhiR : (j:ℝ)*(active H I j).card+weightedClosure H I j ≤
      (∑ v ∈ available H I, ((lost H I j v).card:ℝ))+
        (j.choose 2:ℝ)*C*(active H I j).card := by exact_mod_cast hhi
  have hh := hlin.drift_balance I j (by omega)
  constructor <;> linarith

omit [DecidableEq β] in
theorem Linear.drift_two_bounds {H : Finset (Finset α)} (hlin : Linear H)
    (I : Finset α) (C : ℕ)
    (hC : ∀ u ∈ available H I, ∀ v ∈ available H I, u ≠ v → commonDegree H I u v ≤ C) :
    3*(active H I 3).card-(weightedClosure H I 2:ℝ) ≤ driftSum H I 2 ∧
    driftSum H I 2 ≤ 3*(active H I 3).card-weightedClosure H I 2+
      (C:ℝ)*(active H I 2).card := by
  obtain ⟨hlo,hhi⟩ := loss_two_bounds H I C hC
  have hloR : (∑ v ∈ available H I, ((lost H I 2 v).card:ℝ)) ≤
      (weightedClosure H I 2:ℝ) := by exact_mod_cast hlo
  have hhiR : (weightedClosure H I 2:ℝ) ≤
      (∑ v ∈ available H I, ((lost H I 2 v).card:ℝ))+
        (C:ℝ)*(active H I 2).card := by exact_mod_cast hhi
  have hh := hlin.drift_balance I 2 (by omega)
  norm_num at hh
  constructor <;> linarith

omit [DecidableEq β] in
lemma Linear.weightedClosure_two {H : Finset (Finset α)} (hlin : Linear H) (I : Finset α) :
    weightedClosure H I 2 = ∑ v ∈ available H I, (incident H I 2 v).card^2 := by
  apply sum_congr rfl
  intro v hv
  rw [hlin.incident_two_card I v hv,pow_two]

omit [DecidableEq β] in
lemma Linear.duplicateExcess_zero {H : Finset (Finset α)} (hlin : Linear H)
    {I : Finset α} {v : α} (hv : v ∈ available H I) : duplicateExcess H I v = 0 := by
  have hh := incident_card_eq_closes_add_excess hv
  rw [hlin.incident_two_card I v hv] at hh
  omega

omit [DecidableEq β] in
/-- The exact available-set first moment for a linear original hypergraph. -/
theorem Linear.average_available {H : Finset (Finset α)} (hlin : Linear H)
    {I : Finset α} (hA : (available H I).Nonempty) :
    (∑ v ∈ available H I, ((available H (insert v I)).card:ℝ))/(available H I).card =
      (available H I).card-1-2*(active H I 2).card/(available H I).card := by
  have hz : (∑ v ∈ available H I, (duplicateExcess H I v:ℝ)) = 0 :=
    sum_eq_zero (fun v hv => by rw [hlin.duplicateExcess_zero hv]; norm_num)
  simpa only [hz,sub_zero] using average_available_card_step hA

omit [DecidableEq β] in
/-- Uniform local-degree bounds imply the expected weighted global bounds.
    The local-degree hypothesis is explicit; it has not been proved typical. -/
theorem Linear.weightedClosure_bounds {H : Finset (Finset α)} (hlin : Linear H)
    (I : Finset α) (j : ℕ) (l h : ℝ)
    (hl : ∀ v ∈ available H I, l ≤ ((incident H I 2 v).card:ℝ))
    (hh : ∀ v ∈ available H I, ((incident H I 2 v).card:ℝ) ≤ h) :
    l*j*(active H I j).card ≤ (weightedClosure H I j:ℝ) ∧
      (weightedClosure H I j:ℝ) ≤ h*j*(active H I j).card := by
  have hsum : (∑ v ∈ available H I, ((incident H I j v).card:ℝ)) =
      (j:ℝ)*(active H I j).card := by exact_mod_cast sum_incident_card H I j
  have hw : (weightedClosure H I j:ℝ) = ∑ v ∈ available H I,
      ((incident H I j v).card:ℝ)*(incident H I 2 v).card := by
    unfold weightedClosure
    push_cast
    apply sum_congr rfl
    intro v hv
    rw [hlin.incident_two_card I v hv]
  rw [hw]
  constructor
  · calc
      _ = ∑ v ∈ available H I, ((incident H I j v).card:ℝ)*l := by
        rw [← sum_mul,hsum]; ring
      _ ≤ _ := sum_le_sum (fun v hv => mul_le_mul_of_nonneg_left (hl v hv) (by positivity))
  · calc
      _ ≤ ∑ v ∈ available H I, ((incident H I j v).card:ℝ)*h :=
        sum_le_sum (fun v hv => mul_le_mul_of_nonneg_left (hh v hv) (by positivity))
      _ = _ := by rw [← sum_mul,hsum]; ring

#print axioms Linear.average_available
#print axioms Linear.weightedClosure_bounds
#print axioms Linear.drift_balance
#print axioms Linear.drift_bounds
#print axioms Linear.drift_two_bounds
#print axioms Linear.weightedClosure_two
#print axioms union_card_lower
#print axioms Linear.incident_two_card
#print axioms Linear.sum_promoted
#print axioms lossChoices_eq
#print axioms Linear.lossChoices_card
#print axioms lossChoices_two
#print axioms closureUnion_card_bounds
end
end Erdos773.GreedyLinearDrift
