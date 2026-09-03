import Submission.GreedyCodegreeDrift
import Submission.GreedyOverlapError

/-!
Three-selected-vertex witnesses for nonlinear failures to promote residual
three-edges to two-edges. The original edge indices and the marked selected
vertex are retained, including all multiplicities.
-/
namespace Erdos773.GreedyPromotionWitnesses
open Finset GreedyHypergraphState GreedyCodegreeDrift GreedyOverlapError
open GreedyCommonNeighbors FourUniformRegularization HypergraphDegreeTrim HypergraphLinearization
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [DecidableEq α]

def row (H : Finset (Finset α)) (e : Finset α) : Finset (Finset α) :=
  H.filter (fun f => e ≠ f ∧ 2 ≤ (e ∩ f).card)

lemma row_card_le {H : Finset (Finset α)} {e : Finset α} (he4 : e.card = 4)
    (K : ℕ) (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K) :
    (row H e).card ≤ 6*K := by
  have hs : row H e ⊆ (e.powersetCard 2).biUnion (fun P => H.filter (fun f => P ⊆ f)) := by
    intro f hf
    obtain ⟨hf,hne,hcard⟩ := mem_filter.mp hf
    obtain ⟨P,hP,hPc⟩ := exists_subset_card_eq hcard
    exact mem_biUnion.mpr ⟨P,mem_powersetCard.mpr ⟨hP.trans inter_subset_left,hPc⟩,
      mem_filter.mpr ⟨hf,hP.trans inter_subset_right⟩⟩
  calc
    _ ≤ ((e.powersetCard 2).biUnion (fun P => H.filter (fun f => P ⊆ f))).card := card_le_card hs
    _ ≤ ∑ P ∈ e.powersetCard 2, (H.filter (fun f => P ⊆ f)).card := card_biUnion_le
    _ ≤ ∑ _P ∈ e.powersetCard 2, K := sum_le_sum (fun P hP =>
      pair_subset_codegree K hK (mem_powersetCard.mp hP).2)
    _ = _ := by norm_num [card_powersetCard,he4,Nat.choose]

def rows (H E : Finset (Finset α)) : Finset (Finset α × Finset α) :=
  (E ×ˢ H).filter (fun ef => ef.1 ≠ ef.2 ∧ 2 ≤ (ef.1 ∩ ef.2).card)

lemma mem_rows {H E : Finset (Finset α)} {e f : Finset α} :
    (e,f) ∈ rows H E ↔ e ∈ E ∧ f ∈ H ∧ e ≠ f ∧ 2 ≤ (e ∩ f).card := by
  simp [rows,and_assoc]

lemma rows_card_le {H E : Finset (Finset α)} (h4 : ∀ e ∈ E, e.card = 4)
    (K : ℕ) (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K) :
    (rows H E).card ≤ 6*E.card*K := by
  calc
    _ = ∑ e ∈ E, (row H e).card := by simp only [rows,row,card_filter,sum_product]
    _ ≤ ∑ _e ∈ E, 6*K := sum_le_sum (fun e he => row_card_le (h4 e he) K hK)
    _ = _ := by simp [mul_comm,mul_left_comm]

/-- Attach one marked vertex to an indexed original-edge pair. -/
def marked (T : Finset (Finset α × Finset α)) (A : (Finset α × Finset α) → Finset α) :
    Finset (Pattern α) := T.biUnion (fun ef => (A ef).image (fun a => (ef.1,a,ef.2)))

lemma mem_marked {T : Finset (Finset α × Finset α)} {A : (Finset α × Finset α) → Finset α}
    {e f : Finset α} {a : α} : (e,a,f) ∈ marked T A ↔ (e,f) ∈ T ∧ a ∈ A (e,f) := by
  simp only [marked,mem_biUnion,mem_image,Prod.mk.injEq]
  constructor
  · rintro ⟨⟨e',f'⟩,hef,b,hb,he,hb',hf⟩
    dsimp only at he hf
    subst e'; subst f'; subst b
    exact ⟨hef,hb⟩
  · rintro ⟨hef,ha⟩
    exact ⟨(e,f),hef,a,ha,rfl,rfl,rfl⟩

lemma marked_card_le (T : Finset (Finset α × Finset α))
    (A : (Finset α × Finset α) → Finset α) (r : ℕ)
    (hA : ∀ ef ∈ T, (A ef).card ≤ r) : (marked T A).card ≤ T.card*r := by
  calc
    _ ≤ ∑ ef ∈ T, ((A ef).image (fun a => (ef.1,a,ef.2))).card := card_biUnion_le
    _ ≤ ∑ _ef ∈ T, r := sum_le_sum (fun ef hef => card_image_le.trans (hA ef hef))
    _ = _ := by simp

lemma difference_card {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    {e f : Finset α} (he : e ∈ H) (hf : f ∈ H) (hef : e ≠ f)
    (hc : 2 ≤ (e ∩ f).card) : (e \ f).card = 2 ∧ (f \ e).card = 2 := by
  have hint := Nat.le_antisymm (h2 e he f hf hef) hc
  have ha := card_sdiff_add_card_inter e f
  have hb := card_sdiff_add_card_inter f e
  rw [h4 e he,hint] at ha
  rw [h4 f hf,inter_comm f e,hint] at hb
  omega

def patterns (H : Finset (Finset α)) (u : α) : Finset (Pattern α) :=
  marked (rows H (H.filter (fun e => u ∈ e))) (fun ef => (ef.1 \ ef.2).erase u)

lemma mem_patterns {H : Finset (Finset α)} {u a : α} {e f : Finset α} :
    (e,a,f) ∈ patterns H u ↔ e ∈ H ∧ u ∈ e ∧ f ∈ H ∧ e ≠ f ∧
      2 ≤ (e ∩ f).card ∧ a ≠ u ∧ a ∈ e ∧ a ∉ f := by
  simp only [patterns,mem_marked,mem_rows,mem_filter,mem_erase,mem_sdiff]
  tauto

lemma patterns_card_le {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    (u : α) (D K : ℕ) (hD : degree H u ≤ D)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K) :
    (patterns H u).card ≤ 12*D*K := by
  have hs (ef : Finset α × Finset α) (hef : ef ∈ rows H (H.filter (fun e => u ∈ e))) :
      ((ef.1 \ ef.2).erase u).card ≤ 2 := by
    obtain ⟨he,hf,hne,hcard⟩ := mem_rows.mp hef
    have he := (mem_filter.mp he).1
    exact (card_erase_le).trans (difference_card h4 h2 he hf hne hcard).1.le
  have hm := marked_card_le _ (fun ef : Finset α × Finset α => (ef.1 \ ef.2).erase u) 2 hs
  have hr := rows_card_le (E := H.filter (fun e => u ∈ e))
    (fun e he => h4 e (mem_filter.mp he).1) K hK
  have hd : (H.filter (fun e => u ∈ e)).card ≤ D := hD
  change (patterns H u).card ≤ _ at hm
  nlinarith only [hm,hr,Nat.mul_le_mul_right K hd]

def witness (x : Pattern α) : Finset α := insert x.2.1 (x.2.2 \ x.1)

lemma witness_card {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    {u : α} {x : Pattern α} (hx : x ∈ patterns H u) : (witness x).card = 3 := by
  rcases x with ⟨e,a,f⟩
  obtain ⟨he,hu,hf,hne,hcard,hau,ha,haf⟩ := mem_patterns.mp hx
  have han : a ∉ f \ e := fun h => (mem_sdiff.mp h).2 ha
  change (insert a (f \ e)).card = 3
  rw [card_insert_of_notMem han,(difference_card h4 h2 he hf hne hcard).2]

/-- Fixing the marked vertex fixes one endpoint of an original pair-codegree
    constraint; there are at most 6K^2 such indexed patterns. -/
lemma marked_role_card {H : Finset (Finset α)} (h4 : ∀ e ∈ H, e.card = 4)
    (u a : α) (K : ℕ) (hK : ∀ b c : α, b ≠ c → pairDegree H b c ≤ K) :
    ((patterns H u).filter (fun x => x.2.1 = a)).card ≤ 6*K^2 := by
  by_cases hau : a = u
  · subst a
    have he : (patterns H u).filter (fun x => x.2.1 = u) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro ⟨e,b,f⟩ hx
      obtain ⟨hx,hbu⟩ := mem_filter.mp hx
      exact (mem_patterns.mp hx).2.2.2.2.2.1 hbu
    rw [he]
    exact Nat.zero_le _
  have hs : (patterns H u).filter (fun x => x.2.1 = a) ⊆
      (rows H (H.filter (fun e => u ∈ e ∧ a ∈ e))).image (fun ef => (ef.1,a,ef.2)) := by
    rintro ⟨e,b,f⟩ hx
    obtain ⟨hx,hba⟩ := mem_filter.mp hx
    obtain ⟨he,hu,hf,hne,hcard,hbu,hb,_⟩ := mem_patterns.mp hx
    dsimp only at hba
    subst b
    exact mem_image.mpr ⟨(e,f),mem_rows.mpr ⟨mem_filter.mpr ⟨he,hu,hb⟩,hf,hne,hcard⟩,rfl⟩
  have hc := (card_le_card hs).trans card_image_le
  have hr := rows_card_le (E := H.filter (fun e => u ∈ e ∧ a ∈ e))
    (fun e he => h4 e (mem_filter.mp he).1) K hK
  have hp : (H.filter (fun e => u ∈ e ∧ a ∈ e)).card ≤ K := hK u a (Ne.symm hau)
  nlinarith only [hc,hr,Nat.mul_le_mul_right K hp]

/-- The two vertices in the other-edge portion of a witness are also
    subject to a small original pair-codegree bound. -/
lemma other_pair_card {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    (u b c : α) (hbc : b ≠ c) (K : ℕ)
    (hK : ∀ a d : α, a ≠ d → pairDegree H a d ≤ K) :
    ((patterns H u).filter (fun x => b ∈ x.2.2 \ x.1 ∧ c ∈ x.2.2 \ x.1)).card ≤ 12*K^2 := by
  let T := rows H (H.filter (fun f => b ∈ f ∧ c ∈ f))
  have hs : ((patterns H u).filter (fun x => b ∈ x.2.2 \ x.1 ∧ c ∈ x.2.2 \ x.1)).card ≤
      (marked T (fun ef => ef.2 \ ef.1)).card := by
    apply card_le_card_of_injOn (fun x => (x.2.2,x.2.1,x.1))
    · rintro ⟨e,a,f⟩ hx
      obtain ⟨hx,hb,hc⟩ := mem_filter.mp hx
      obtain ⟨he,hu,hf,hne,hcard,hau,ha,haf⟩ := mem_patterns.mp hx
      apply mem_marked.mpr
      refine ⟨mem_rows.mpr ⟨mem_filter.mpr ⟨hf,(mem_sdiff.mp hb).1,(mem_sdiff.mp hc).1⟩,
        he,hne.symm,?_⟩,mem_sdiff.mpr ⟨ha,haf⟩⟩
      simpa only [inter_comm] using hcard
    · rintro ⟨e,a,f⟩ hx ⟨e',a',f'⟩ hy h
      simpa only [Prod.mk.injEq,and_comm,and_left_comm,and_assoc] using h
  have ha (ef : Finset α × Finset α) (hef : ef ∈ T) : (ef.2 \ ef.1).card ≤ 2 := by
    obtain ⟨he,hf,hne,hcard⟩ := mem_rows.mp hef
    exact (difference_card h4 h2 (mem_filter.mp he).1 hf hne hcard).2.le
  have hm := marked_card_le T (fun ef => ef.2 \ ef.1) 2 ha
  have hr : T.card ≤ 6*(H.filter (fun f => b ∈ f ∧ c ∈ f)).card*K :=
    rows_card_le (fun e he => h4 e (mem_filter.mp he).1) K hK
  have hp : (H.filter (fun f => b ∈ f ∧ c ∈ f)).card ≤ K := hK b c hbc
  nlinarith only [hs,hm,hr,Nat.mul_le_mul_right K hp]

lemma witness_pair_incidence {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    (u b c : α) (hbc : b ≠ c) (K : ℕ)
    (hK : ∀ a d : α, a ≠ d → pairDegree H a d ≤ K) :
    ((patterns H u).filter (fun x => b ∈ witness x ∧ c ∈ witness x)).card ≤ 24*K^2 := by
  have hs : (patterns H u).filter (fun x => b ∈ witness x ∧ c ∈ witness x) ⊆
      ((patterns H u).filter (fun x => x.2.1 = b)) ∪
      (((patterns H u).filter (fun x => x.2.1 = c)) ∪
        ((patterns H u).filter (fun x => b ∈ x.2.2 \ x.1 ∧ c ∈ x.2.2 \ x.1))) := by
    intro x hx
    obtain ⟨hx,hb,hc⟩ := mem_filter.mp hx
    simp only [witness,mem_insert] at hb hc
    by_cases hab : x.2.1 = b
    · exact mem_union_left _ (mem_filter.mpr ⟨hx,hab⟩)
    by_cases hac : x.2.1 = c
    · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hx,hac⟩))
    exact mem_union_right _ (mem_union_right _ (mem_filter.mpr
      ⟨hx,hb.resolve_left (Ne.symm hab),hc.resolve_left (Ne.symm hac)⟩))
  have hc := (card_le_card hs).trans (card_union_le _ _)
  have hd := card_union_le
    ((patterns H u).filter (fun x => x.2.1 = c))
    ((patterns H u).filter (fun x => b ∈ x.2.2 \ x.1 ∧ c ∈ x.2.2 \ x.1))
  have h1 := marked_role_card h4 u b K hK
  have h2' := marked_role_card h4 u c K hK
  have h3 := other_pair_card h4 h2 u b c hbc K hK
  omega

variable [Fintype α]

def cost (H : Finset (Finset α)) (u : α) (I : Finset α) : ℕ :=
  ((patterns H u).filter (fun x => witness x ⊆ I)).card

omit [Fintype α] in
lemma cost_mono (H : Finset (Finset α)) (u : α) {I J : Finset α} (hIJ : I ⊆ J) :
    cost H u I ≤ cost H u J := by
  apply card_le_card
  intro x hx
  obtain ⟨hx,hxi⟩ := mem_filter.mp hx
  exact mem_filter.mpr ⟨hx,hxi.trans hIJ⟩

/-- A blocked residual three-edge has a selected marked vertex in e\f,
    in addition to the two selected vertices in f\e. -/
lemma blocked_three_witness {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    {I e : Finset α} {u w : α} (he : e ∈ incident H I 3 u)
    (hw : w ∈ e \ I) (hbad : ¬(e \ I).erase w ⊆ available H (insert w I)) :
    ∃ x ∈ patterns H u, x.1 = e ∧ witness x ⊆ I := by
  obtain ⟨heactive,hu⟩ := mem_filter.mp he
  obtain ⟨x,hx,f,hf,hne,hpair,hfi⟩ := blocked_overlap_witness (by omega) heactive hw hbad
  obtain ⟨hH,hres,hcard⟩ := mem_filter.mp heactive
  have hxu : x ≠ w := (mem_erase.mp hx).1
  have hpc : ({w,x}:Finset α).card = 2 := by simp [hxu.symm]
  have hge : 2 ≤ (e ∩ f).card := by simpa only [hpc] using card_le_card hpair
  have heq : ({w,x}:Finset α) = e ∩ f := by
    apply eq_of_subset_of_card_le hpair
    rw [hpc]
    exact h2 e hH f hf hne
  have hi := card_sdiff_add_card_inter e I
  rw [hcard,h4 e hH] at hi
  have hpos : 0 < (e ∩ I).card := by omega
  obtain ⟨a,ha⟩ := card_pos.mp hpos
  obtain ⟨hae,hai⟩ := mem_inter.mp ha
  have haf : a ∉ f := by
    intro haf
    have hap : a ∈ ({w,x}:Finset α) := by rw [heq]; exact mem_inter.mpr ⟨hae,haf⟩
    have han : a ∉ I := by
      rcases mem_insert.mp hap with rfl | hap
      · exact (mem_sdiff.mp hw).2
      · have hax := mem_singleton.mp hap
        simpa only [hax] using (mem_sdiff.mp (mem_erase.mp hx).2).2
    exact han hai
  have hau : a ≠ u := fun h => (mem_sdiff.mp hu).2 (h ▸ hai)
  refine ⟨(e,a,f),mem_patterns.mpr ⟨hH,(mem_sdiff.mp hu).1,hf,hne,hge,hau,hae,haf⟩,rfl,?_⟩
  exact insert_subset hai hfi

omit [Fintype α] in
lemma sum_first_fibers_le (S : Finset (Finset α)) (T : Finset (Pattern α)) :
    (∑ e ∈ S, (T.filter (fun x => x.1 = e)).card) ≤ T.card := by
  have he := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := S) (t := T) (fun e x => x.1 = e)
  change (∑ e ∈ S, (T.filter (fun x => x.1 = e)).card) =
    ∑ x ∈ T, (S.filter (fun e => x.1 = e)).card at he
  rw [he]
  calc
    _ ≤ ∑ _x ∈ T, 1 := by
      apply sum_le_sum
      intro x _
      apply card_le_one.mpr
      intro e he f hf
      exact (mem_filter.mp he).2.symm.trans (mem_filter.mp hf).2
    _ = _ := by simp

/-- The failure count is bounded by twice a monotone selected-witness count. -/
theorem promotionDefect_two_bound {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    (I : Finset α) (u : α) : promotionDefect H I 2 u ≤ 2*cost H u I := by
  let T := (patterns H u).filter (fun x => witness x ⊆ I)
  have hrow (e : Finset α) (he : e ∈ incident H I 3 u) :
      (((e \ I).erase u).filter (fun w => ¬(e \ I).erase w ⊆ available H (insert w I))).card ≤
        2*(T.filter (fun x => x.1 = e)).card := by
    let B := ((e \ I).erase u).filter (fun w => ¬(e \ I).erase w ⊆ available H (insert w I))
    by_cases hb : B.Nonempty
    · obtain ⟨w,hw⟩ := hb
      obtain ⟨hw,hbad⟩ := mem_filter.mp hw
      obtain ⟨x,hx,hxe,hxi⟩ := blocked_three_witness h4 h2 he (mem_erase.mp hw).2 hbad
      have hp : 0 < (T.filter (fun x => x.1 = e)).card :=
        card_pos.mpr ⟨x,mem_filter.mpr ⟨mem_filter.mpr ⟨hx,hxi⟩,hxe⟩⟩
      obtain ⟨he,hu⟩ := mem_filter.mp he
      have hc : B.card ≤ 2 := by
        apply (card_filter_le _ _).trans
        rw [card_erase_of_mem hu,(mem_filter.mp he).2.2]
      have hh := Nat.mul_le_mul_left 2 hp
      dsimp only [B] at hc
      omega
    · have he := not_nonempty_iff_eq_empty.mp hb
      change B.card ≤ _
      rw [he]
      exact Nat.zero_le _
  calc
    _ ≤ ∑ e ∈ incident H I 3 u, 2*(T.filter (fun x => x.1 = e)).card := sum_le_sum hrow
    _ = 2*(∑ e ∈ incident H I 3 u, (T.filter (fun x => x.1 = e)).card) := by rw [mul_sum]
    _ ≤ 2*T.card := Nat.mul_le_mul_left 2 (sum_first_fibers_le _ T)
    _ = _ := rfl

#print axioms row_card_le
#print axioms rows_card_le
#print axioms patterns_card_le
#print axioms witness_card
#print axioms marked_role_card
#print axioms other_pair_card
#print axioms witness_pair_incidence
#print axioms blocked_three_witness
#print axioms promotionDefect_two_bound
end
end Erdos773.GreedyPromotionWitnesses
