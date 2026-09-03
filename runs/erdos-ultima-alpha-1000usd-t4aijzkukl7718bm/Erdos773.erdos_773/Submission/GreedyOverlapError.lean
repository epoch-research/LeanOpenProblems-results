import Submission.GreedyConfigurationTails
import Submission.HypergraphLinearization

/-!
Bounding duplicate contracted two-edges by four selected vertices from an
original pair of overlapping four-edges. This controls one error term, not
the running time of the greedy process.
-/
namespace Erdos773.GreedyOverlapError
open Finset GreedyHypergraphState StoppedGreedyMoments GreedyConfigurationTails
open FourUniformRegularization HypergraphLinearization HypergraphDegreeTrim
set_option maxHeartbeats 2000000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
lemma pair_subset_codegree {H : Finset (Finset α)} (K : ℕ)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    {P : Finset α} (hP : P.card = 2) : (H.filter (fun e => P ⊆ e)).card ≤ K := by
  obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hP
  have he : H.filter (fun e => ({a,b}:Finset α) ⊆ e) =
      H.filter (fun e => a ∈ e ∧ b ∈ e) := by
    ext e
    simp only [mem_filter,insert_subset_iff,singleton_subset_iff]
  rw [he]
  exact hK a b hab

omit [Fintype α] in
/-- Count overlap PAIRS rather than their union supports. The bound is linear
    in the edge count and pair codegree. -/
theorem overlaps_card_le {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4) (K : ℕ)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K) :
    (overlaps H).card ≤ 6*H.card*K := by
  have hrow (e : Finset α) (he : e ∈ H) :
      (H.filter (fun f => e ≠ f ∧ 2 ≤ (e ∩ f).card)).card ≤ 6*K := by
    have hsub : H.filter (fun f => e ≠ f ∧ 2 ≤ (e ∩ f).card) ⊆
        (e.powersetCard 2).biUnion (fun P => H.filter (fun f => P ⊆ f)) := by
      intro f hf
      obtain ⟨hf,hne,hcard⟩ := mem_filter.mp hf
      obtain ⟨P,hP,hPc⟩ := exists_subset_card_eq hcard
      exact mem_biUnion.mpr ⟨P,mem_powersetCard.mpr ⟨hP.trans inter_subset_left,hPc⟩,
        mem_filter.mpr ⟨hf,hP.trans inter_subset_right⟩⟩
    calc
      _ ≤ ((e.powersetCard 2).biUnion (fun P => H.filter (fun f => P ⊆ f))).card := card_le_card hsub
      _ ≤ ∑ P ∈ e.powersetCard 2, (H.filter (fun f => P ⊆ f)).card := card_biUnion_le
      _ ≤ ∑ _P ∈ e.powersetCard 2, K := sum_le_sum (fun P hP =>
        pair_subset_codegree K hK (mem_powersetCard.mp hP).2)
      _ = _ := by norm_num [card_powersetCard,h4 e he,Nat.choose]
  calc
    _ = ∑ e ∈ H, (H.filter (fun f => e ≠ f ∧ 2 ≤ (e ∩ f).card)).card := by
      simp only [overlaps,card_filter,sum_product]
    _ ≤ ∑ _e ∈ H, 6*K := sum_le_sum hrow
    _ = _ := by simp [mul_comm,mul_left_comm]

/-- The vertices which must already have been selected if these two original
    edges contract to the same two-element residual. -/
def witness (ef : Finset α × Finset α) : Finset α :=
  (ef.1 \ ef.2) ∪ (ef.2 \ ef.1)

omit [Fintype α] in
lemma overlap_inter_card {H : Finset (Finset α)}
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    {ef : Finset α × Finset α} (hef : ef ∈ overlaps H) : (ef.1 ∩ ef.2).card = 2 := by
  obtain ⟨hef,hne,hge⟩ := mem_filter.mp hef
  obtain ⟨he,hf⟩ := mem_product.mp hef
  exact Nat.le_antisymm (h2 _ he _ hf hne) hge

omit [Fintype α] in
lemma witness_card {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    {ef : Finset α × Finset α} (hef : ef ∈ overlaps H) : (witness ef).card = 4 := by
  have hint := overlap_inter_card h2 hef
  have hh := mem_product.mp (mem_filter.mp hef).1
  have hdis : Disjoint (ef.1 \ ef.2) (ef.2 \ ef.1) := by
    apply disjoint_left.mpr
    intro a ha hb
    exact (mem_sdiff.mp ha).2 (mem_sdiff.mp hb).1
  rw [witness,card_union_of_disjoint hdis]
  have hleft := card_sdiff_add_card_inter ef.1 ef.2
  have hright := card_sdiff_add_card_inter ef.2 ef.1
  rw [inter_comm ef.2 ef.1] at hright
  rw [hint,h4 _ hh.1] at hleft
  rw [hint,h4 _ hh.2] at hright
  omega

omit [Fintype α] in
lemma witness_subset_of_residual_eq {e f I : Finset α} (hef : e \ I = f \ I) :
    witness (e,f) ⊆ I := by
  intro a ha
  rcases mem_union.mp ha with ha | ha
  · obtain ⟨ha,haf⟩ := mem_sdiff.mp ha
    by_contra hai
    have hh : a ∈ f \ I := hef ▸ mem_sdiff.mpr ⟨ha,hai⟩
    exact haf (mem_sdiff.mp hh).1
  · obtain ⟨ha,hae⟩ := mem_sdiff.mp ha
    by_contra hai
    have hh : a ∈ e \ I := hef.symm ▸ mem_sdiff.mpr ⟨ha,hai⟩
    exact hae (mem_sdiff.mp hh).1

def overlapCost (H : Finset (Finset α)) (I : Finset α) : ℕ :=
  ((overlaps H).filter (fun ef => witness ef ⊆ I)).card

omit [Fintype α] in
lemma overlapCost_mono (H : Finset (Finset α)) {I J : Finset α} (hIJ : I ⊆ J) :
    overlapCost H I ≤ overlapCost H J := by
  apply card_le_card
  intro ef hef
  obtain ⟨hef,hsub⟩ := mem_filter.mp hef
  exact mem_filter.mpr ⟨hef,hsub.trans hIJ⟩

omit [Fintype α] in
lemma pairReps_offDiag_mem {H : Finset (Finset α)} {I : Finset α} {v w : α}
    {ef : Finset α × Finset α} (hef : ef ∈ (pairReps H I v w).offDiag) :
    ef ∈ overlaps H ∧ witness ef ⊆ I ∧ v ∈ ef.1 ∩ ef.2 := by
  obtain ⟨he,hf,hne⟩ := mem_offDiag.mp hef
  obtain ⟨he,hvw,heq⟩ := mem_filter.mp he
  obtain ⟨hf,_,hfq⟩ := mem_filter.mp hf
  have hp : ({v,w}:Finset α) ⊆ ef.1 ∩ ef.2 := by
    intro a ha
    have h1 : a ∈ ef.1 \ I := by rw [heq]; exact ha
    have h2 : a ∈ ef.2 \ I := by rw [hfq]; exact ha
    exact mem_inter.mpr ⟨(mem_sdiff.mp h1).1,(mem_sdiff.mp h2).1⟩
  have hc : 2 ≤ (ef.1 ∩ ef.2).card := by
    have hh := card_le_card hp
    simpa [hvw] using hh
  exact ⟨mem_filter.mpr ⟨mem_product.mpr ⟨he,hf⟩,hne,hc⟩,
    witness_subset_of_residual_eq (heq.trans hfq.symm),hp (by simp)⟩

lemma offDiag_disjoint (H : Finset (Finset α)) (I : Finset α) (v : α) :
    ((closes H I v):Set α).PairwiseDisjoint (fun w => (pairReps H I v w).offDiag) := by
  apply pairwiseDisjoint_iff.mpr
  intro w hw z hz hn
  obtain ⟨ef,hef⟩ := hn
  obtain ⟨hwf,hzf⟩ := mem_inter.mp hef
  have hwe := (mem_offDiag.mp hwf).1
  have hze := (mem_offDiag.mp hzf).1
  obtain ⟨_,hvw,heq⟩ := mem_filter.mp hwe
  have heq' := (mem_filter.mp hze).2.2
  have hm : w ∈ ({v,z}:Finset α) := by rw [← heq',heq]; simp
  simp only [mem_insert,mem_singleton] at hm
  exact hm.resolve_left hvw.symm

omit [Fintype α] [DecidableEq α] in
lemma offDiag_card_lower {s : Finset (Finset α)} (hs : s.Nonempty) :
    s.card-1 ≤ s.offDiag.card := by
  rw [offDiag_card]
  have hp : 1 ≤ s.card := card_pos.mpr hs
  have hh : s.card-1 ≤ s.card*(s.card-1) := Nat.le_mul_of_pos_left _ hp
  have he : s.card*(s.card-1) = s.card*s.card-s.card := by rw [Nat.mul_sub_left_distrib,mul_one]
  omega

lemma excess_at_vertex_bound (H : Finset (Finset α)) (I : Finset α) (v : α) :
    duplicateExcess H I v ≤
      (((overlaps H).filter (fun ef => witness ef ⊆ I)).filter
        (fun ef => v ∈ ef.1 ∩ ef.2)).card := by
  have hcount : duplicateExcess H I v ≤
      ((closes H I v).biUnion (fun w => (pairReps H I v w).offDiag)).card := by
    rw [card_biUnion (offDiag_disjoint H I v)]
    apply sum_le_sum
    intro w hw
    exact offDiag_card_lower ((pairReps_nonempty_iff (closes_subset H I v hw)).mpr hw)
  apply hcount.trans (card_le_card ?_)
  intro ef hef
  obtain ⟨w,hw,hef⟩ := mem_biUnion.mp hef
  obtain ⟨he,hs,hv⟩ := pairReps_offDiag_mem hef
  exact mem_filter.mpr ⟨mem_filter.mpr ⟨he,hs⟩,hv⟩

/-- Every duplicate correction is charged to an ordered original-edge pair
    with four selected witness vertices. The factor two counts common vertices. -/
theorem total_excess_bound {H : Finset (Finset α)}
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2) (I : Finset α) :
    (∑ v ∈ available H I, duplicateExcess H I v) ≤ 2*overlapCost H I := by
  calc
    _ ≤ ∑ v ∈ available H I,
        (((overlaps H).filter (fun ef => witness ef ⊆ I)).filter
          (fun ef => v ∈ ef.1 ∩ ef.2)).card :=
      sum_le_sum (fun v _ => excess_at_vertex_bound H I v)
    _ = ∑ ef ∈ (overlaps H).filter (fun ef => witness ef ⊆ I),
        ((available H I).filter (fun v => v ∈ ef.1 ∩ ef.2)).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (s := available H I) (t := (overlaps H).filter (fun ef => witness ef ⊆ I))
        (fun (v : α) (ef : Finset α × Finset α) => v ∈ ef.1 ∩ ef.2)
    _ ≤ ∑ _ef ∈ (overlaps H).filter (fun ef => witness ef ⊆ I), 2 := by
      apply sum_le_sum
      intro ef hef
      have hs : (available H I).filter (fun v => v ∈ ef.1 ∩ ef.2) ⊆ ef.1 ∩ ef.2 :=
        fun _ hv => (mem_filter.mp hv).2
      exact (card_le_card hs).trans_eq (overlap_inter_card h2 (mem_filter.mp hef).1)
    _ = _ := by simp [overlapCost,mul_comm]

def totalExcess (H : Finset (Finset α)) (I : Finset α) : ℕ :=
  ∑ v ∈ available H I, duplicateExcess H I v

lemma prefix_error_le {H : Finset (Finset α)}
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    {I J : Finset α} (hJI : J ⊆ I) : totalExcess H J ≤ 2*overlapCost H I :=
  (total_excess_bound h2 J).trans (Nat.mul_le_mul_left 2 (overlapCost_mono H hJI))

/-- The cost counts ORIGINAL ordered edge pairs, even when several pairs have
    identical four-vertex witnesses. -/
theorem expectation_overlapCost {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    (K : ℕ) (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    (L : ℕ) (hL : 0 < L) (t : ℕ) :
    expectation H L t (fun I => (overlapCost H I:ℝ)) ≤
      6*(H.card:ℝ)*K*((t:ℝ)/L)^4 := by
  have he : (fun I => (overlapCost H I:ℝ)) =
      fun I => ∑ ef ∈ overlaps H, included (witness ef) I := by
    funext I
    simp [overlapCost,included]
  rw [he,expectation_sum]
  calc
    _ ≤ ∑ ef ∈ overlaps H, ((t:ℝ)/L)^(witness ef).card :=
      sum_le_sum (fun ef _ => inclusion_bound H L hL t (witness ef))
    _ = (overlaps H).card*((t:ℝ)/L)^4 := by
      rw [sum_congr rfl (fun ef hef => congrArg (fun k => ((t:ℝ)/L)^k) (witness_card h4 h2 hef))]
      simp
    _ ≤ _ := by
      have hc : ((overlaps H).card:ℝ) ≤ 6*(H.card:ℝ)*K := by exact_mod_cast overlaps_card_le h4 K hK
      exact mul_le_mul_of_nonneg_right hc (by positivity)

/-- Mean bound for the duplicate correction in the exact available-set drift. -/
theorem expectation_totalExcess {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    (K : ℕ) (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    (L : ℕ) (hL : 0 < L) (t : ℕ) :
    expectation H L t (fun I => (totalExcess H I:ℝ)) ≤
      12*(H.card:ℝ)*K*((t:ℝ)/L)^4 := by
  calc
    _ ≤ expectation H L t (fun I => 2*(overlapCost H I:ℝ)) :=
      expectation_mono H L t (fun I => by exact_mod_cast total_excess_bound h2 I)
    _ = 2*expectation H L t (fun I => (overlapCost H I:ℝ)) := expectation_mul H L t 2 _
    _ ≤ _ := by
      have hh := expectation_overlapCost h4 h2 K hK L hL t
      linarith

/-- A bad duplicate correction at ANY selected subset of the final state.
    Thus a bound for this event controls every prefix of every realizing path. -/
def prefixBad (H : Finset (Finset α)) (B : ℝ) (I : Finset α) : Prop :=
  ∃ J ⊆ I, B < (totalExcess H J:ℝ)

theorem prefix_error_tail {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    (K : ℕ) (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    (L : ℕ) (hL : 0 < L) (t : ℕ) (B : ℝ) (hB : 0 < B) :
    expectation H L t (event (prefixBad H B)) ≤
      12*(H.card:ℝ)*K*((t:ℝ)/L)^4/B := by
  have hdom (I : Finset α) : B*event (prefixBad H B) I ≤ 2*(overlapCost H I:ℝ) := by
    classical
    by_cases hp : prefixBad H B I
    · obtain ⟨J,hJI,hJ⟩ := hp
      have hh : (totalExcess H J:ℝ) ≤ 2*(overlapCost H I:ℝ) := by exact_mod_cast prefix_error_le h2 hJI
      have hp' : prefixBad H B I := ⟨J,hJI,hJ⟩
      simpa only [event,if_pos hp',mul_one] using hJ.le.trans hh
    · simp only [event,if_neg hp,mul_zero]
      positivity
  calc
    _ ≤ expectation H L t (fun I => 2*(overlapCost H I:ℝ))/B :=
      markov_bound H L t _ _ B hB hdom
    _ = 2*expectation H L t (fun I => (overlapCost H I:ℝ))/B := by rw [expectation_mul]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hB.le
      have hh := expectation_overlapCost h4 h2 K hK L hL t
      linarith

lemma regular_edge_count {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4) (D : ℕ) (hD : ∀ v : α, degree H v = D) :
    4*H.card = Fintype.card α*D := by
  have hh := degree_sum (univ:Finset α) H (fun e _ => subset_univ e) h4
  rw [sum_congr rfl (fun v _ => hD v)] at hh
  simpa using hh.symm

/-- In a regular graph the bound scales as V*D*K, not the cruder V^2*K^2.
    This distinction matters after making many copies in regularization. -/
theorem prefix_error_tail_regular {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    (D K : ℕ) (hD : ∀ v : α, degree H v = D)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    (L : ℕ) (hL : 0 < L) (t : ℕ) (B : ℝ) (hB : 0 < B) :
    expectation H L t (event (prefixBad H B)) ≤
      3*(Fintype.card α:ℝ)*D*K*((t:ℝ)/L)^4/B := by
  have hc : 4*(H.card:ℝ) = (Fintype.card α:ℝ)*D := by exact_mod_cast regular_edge_count h4 D hD
  convert prefix_error_tail h4 h2 K hK L hL t B hB using 1
  congr 1
  rw [show 3*(Fintype.card α:ℝ)*D = 12*(H.card:ℝ) by nlinarith only [hc]]

/-- A concrete small-error regime. The event covers every selected subset,
    and hence all prefixes, not only the terminal state. -/
theorem prefix_error_power_tail [Nonempty α] {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    (D K : ℕ) (hD0 : 0 < D) (hD : ∀ v : α, degree H v = D)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    (hsmall : (K:ℝ) ≤ (D:ℝ)^(1/100:ℝ))
    (L : ℕ) (hL : 0 < L) (t : ℕ)
    (ht : (t:ℝ)/L ≤ (D:ℝ)^(-1/3+1/100:ℝ)) :
    expectation H L t
      (event (prefixBad H ((Fintype.card α:ℝ)*(D:ℝ)^(-1/100:ℝ)))) ≤
        3*(D:ℝ)^(-41/150:ℝ) := by
  have hd : (0:ℝ) < D := by exact_mod_cast hD0
  have hn : (0:ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hB : (0:ℝ) < (Fintype.card α:ℝ)*(D:ℝ)^(-1/100:ℝ) := by positivity
  have hp4 := pow_le_pow_left₀ (show (0:ℝ) ≤ (t:ℝ)/L by positivity) ht 4
  calc
    _ ≤ 3*(Fintype.card α:ℝ)*D*K*((t:ℝ)/L)^4/
        ((Fintype.card α:ℝ)*(D:ℝ)^(-1/100:ℝ)) :=
      prefix_error_tail_regular h4 h2 D K hD hK L hL t _ hB
    _ ≤ 3*(Fintype.card α:ℝ)*D*(D:ℝ)^(1/100:ℝ)*
        ((D:ℝ)^(-1/3+1/100:ℝ))^4/((Fintype.card α:ℝ)*(D:ℝ)^(-1/100:ℝ)) := by
      apply div_le_div_of_nonneg_right _ hB.le
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hsmall (by positivity)) hp4
        (by positivity) (by positivity)
    _ = 3*(D:ℝ)^(1+1/100+(-1/3+1/100)*4-(-1/100):ℝ) := by
      rw [← Real.rpow_mul_natCast hd.le,Real.rpow_sub hd,
        Real.rpow_add hd,Real.rpow_add hd,Real.rpow_one]
      field_simp
      norm_num
    _ = _ := by norm_num

#print axioms prefix_error_power_tail
#print axioms expectation_overlapCost
#print axioms expectation_totalExcess
#print axioms prefix_error_tail
#print axioms prefix_error_tail_regular
#print axioms overlaps_card_le
#print axioms witness_card
#print axioms total_excess_bound
end
end Erdos773.GreedyOverlapError
