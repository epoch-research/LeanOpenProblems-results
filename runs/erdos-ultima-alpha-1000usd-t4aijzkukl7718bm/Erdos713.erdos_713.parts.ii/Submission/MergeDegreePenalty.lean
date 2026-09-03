import FormalConjecturesUtil
import Submission.CloneResistance
import Submission.VertexMerging

/-! Degree-energy cost of identifying nonadjacent vertices, and a safe-pair
budget on globally penalized hosts. No exact edge maximality is assumed. -/
open SimpleGraph Finset
open scoped Classical
namespace Erdos713MergeDegreePenalty
open Erdos713DegreePenalty Erdos713DegreePenaltySupports Erdos713VertexMerging
variable {V W : Type*}
set_option maxHeartbeats 2000000

lemma degree_merge_root [Fintype V] (G : SimpleGraph V) {u v : V}
    (huv : u ≠ v) (hn : ¬G.Adj u v) :
    degreeR (merge G u v hn) ⟨u,huv⟩ ≤ degreeR G u+degreeR G v := by
  let M := merge G u v hn
  let f : M.neighborSet ⟨u,huv⟩ → G.neighborSet u ⊕ G.neighborSet v := fun z =>
    if h : G.Adj u z.val.val then .inl ⟨z.val.val,h⟩ else .inr ⟨z.val.val,by
      have hh := (merge_adj G u v hn _ _).mp z.property
      rcases hh with hh | ⟨_,hh⟩ | ⟨he,hh⟩
      · exact (h hh).elim
      · exact hh
      · exact (hn hh.symm).elim⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hp : a.val.val=b.val.val := by
      have hh := congrArg (Sum.elim (fun z : G.neighborSet u => z.val)
        (fun z : G.neighborSet v => z.val)) hab
      by_cases ha : G.Adj u a.val.val <;> by_cases hb : G.Adj u b.val.val <;>
        simpa [f,ha,hb] using hh
    exact Subtype.ext (Subtype.ext hp)
  have hh := Fintype.card_le_of_injective f hf
  unfold degreeR
  exact_mod_cast (by simpa only [Fintype.card_sum,Nat.card_eq_fintype_card] using hh)

lemma degree_merge_other [Fintype V] (G : SimpleGraph V) {u v : V}
    (hn : ¬G.Adj u v) (w : {x : V // x ≠ v}) (hwu : w.val ≠ u) :
    degreeR (merge G u v hn) w ≤ degreeR G w.val := by
  let M := merge G u v hn
  have hroot (z : M.neighborSet w) (hz : z.val.val=u) (hno : ¬G.Adj w.val u) :
      G.Adj w.val v := by
    have hh := (merge_adj G u v hn _ _).mp z.property
    rcases hh with hh | ⟨he,_⟩ | ⟨_,hh⟩
    · exact (hno (hz ▸ hh)).elim
    · exact (hwu he).elim
    · exact hh.symm
  have hold (z : M.neighborSet w) (hz : z.val.val ≠ u) : G.Adj w.val z.val.val := by
    have hh := (merge_adj G u v hn _ _).mp z.property
    rcases hh with hh | ⟨he,_⟩ | ⟨he,_⟩
    · exact hh
    · exact (hwu he).elim
    · exact (hz he).elim
  let f : M.neighborSet w → G.neighborSet w.val := fun z =>
    if hz : z.val.val=u then
      if hh : G.Adj w.val u then ⟨u,hh⟩ else ⟨v,hroot z hz hh⟩
    else ⟨z.val.val,hold z hz⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    have hh := congrArg Subtype.val hab
    by_cases ha : a.val.val=u
    · by_cases hb : b.val.val=u
      · exact ha.trans hb.symm
      · by_cases hadj : G.Adj w.val u
        · have he : u=b.val.val := by simpa only [f,dif_pos ha,dif_pos hadj,dif_neg hb] using hh
          exact (hb he.symm).elim
        · have he : v=b.val.val := by simpa only [f,dif_pos ha,dif_neg hadj,dif_neg hb] using hh
          exact (b.val.property he.symm).elim
    · by_cases hb : b.val.val=u
      · by_cases hadj : G.Adj w.val u
        · have he : a.val.val=u := by simpa only [f,dif_neg ha,dif_pos hadj,dif_pos hb] using hh
          exact (ha he).elim
        · have he : a.val.val=v := by simpa only [f,dif_neg ha,dif_neg hadj,dif_pos hb] using hh
          exact (a.val.property he).elim
      · simpa only [f,dif_neg ha,dif_neg hb] using hh
  unfold degreeR
  simp only [Nat.card_eq_fintype_card]
  exact_mod_cast Fintype.card_le_of_injective f hf

/-- Only the merged root can gain degree; every other degree weakly drops. -/
lemma merge_energy [Fintype V] (G : SimpleGraph V) {u v : V}
    (huv : u ≠ v) (hn : ¬G.Adj u v) :
    energy (merge G u v hn) ≤ energy G+2*degreeR G u*degreeR G v := by
  let M := merge G u v hn
  let b : ℝ := 2*degreeR G u*degreeR G v+degreeR G v^2
  have hpoint (w : {x : V // x ≠ v}) :
      degreeR M w^2 ≤ degreeR G w.val^2+if w.val=u then b else 0 := by
    by_cases hw : w.val=u
    · have he : w=⟨u,huv⟩ := Subtype.ext hw
      rw [he,if_pos rfl]
      have hh := degree_merge_root G huv hn
      have hp := pow_le_pow_left₀ (degreeR_nonneg M ⟨u,huv⟩) hh 2
      dsimp only [b]
      nlinarith only [hp]
    · rw [if_neg hw,add_zero]
      exact pow_le_pow_left₀ (degreeR_nonneg M w) (degree_merge_other G hn w hw) 2
  have hh := sum_le_sum (s := (univ : Finset {x : V // x ≠ v})) (fun w _ => hpoint w)
  rw [sum_add_distrib] at hh
  have hb : (∑ w : {x : V // x ≠ v}, if w.val=u then b else 0)=b := by
    have he (w : {x : V // x ≠ v}) : w.val=u ↔ w=⟨u,huv⟩ :=
      ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩
    simp_rw [he]
    simp
  rw [hb] at hh
  have hremove : (∑ w : {x : V // x ≠ v}, degreeR G w.val^2)+degreeR G v^2=energy G := by
    rw [← sum_subtype (univ.erase v) (fun x => by simp [ne_comm]) (fun x => degreeR G x^2)]
    exact sum_erase_add _ _ (mem_univ v)
  change energy M ≤ _ at hh
  dsimp only [b] at hh
  linarith

/-- A safe identification must pay the backward potential slope through
codegree or increased degree energy. -/
lemma safe_merge_cost [Fintype V] {H : SimpleGraph W} {G : SimpleGraph V}
    {lam mu : ℝ} (hg : GlobalOptimal H G lam mu) (hlam : 0 ≤ lam) {u v : V}
    (huv : u ≠ v) (hn : ¬G.Adj u v) (hf : H.Free (merge G u v hn)) :
    mu*(2*Fintype.card V-1) ≤ (Nat.card (G.commonNeighbors u v) : ℝ)+
      2*lam*degreeR G u*degreeR G v := by
  have hh := hg.compare_graph (merge G u v hn) hf
  have hcard : Fintype.card {x : V // x ≠ v}=Fintype.card V-1 := by
    rw [Fintype.card_subtype_compl]
    simp
  have hpos : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  unfold potential score at hh
  rw [hcard,Nat.cast_sub hpos,Nat.cast_one] at hh
  have he : edgesR (merge G u v hn)+(Nat.card (G.commonNeighbors u v) : ℝ)=edgesR G := by
    unfold edgesR
    exact_mod_cast merge_edge_count G huv hn
  have henergy := mul_le_mul_of_nonneg_left (merge_energy G huv hn) hlam
  nlinarith only [hh,he,henergy]

/-- Ordered distinct nonadjacent pairs with H-free merger. -/
def SafePair (H : SimpleGraph W) (G : SimpleGraph V) (u v : V) : Prop :=
  u ≠ v ∧ ∃ hn : ¬G.Adj u v, H.Free (merge G u v hn)

noncomputable def safePairs [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) : Finset (V × V) :=
  univ.filter (fun p => SafePair H G p.1 p.2)

lemma sum_common [Fintype V] (G : SimpleGraph V) :
    (∑ p : V × V, (Nat.card (G.commonNeighbors p.1 p.2) : ℝ))=energy G := by
  have hh := Erdos713DRC.sum_common_eq_sum_degree_sq G
  unfold energy degreeR
  simp only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree]
  exact_mod_cast hh

/-- This budget and a maximum-degree cap concern the very same host. -/
theorem safePairs_budget [Fintype V] {H : SimpleGraph W} {G : SimpleGraph V}
    {lam mu : ℝ} (hg : GlobalOptimal H G lam mu) (hlam : 0 ≤ lam) :
    mu*(2*Fintype.card V-1)*(safePairs H G).card ≤ energy G+8*lam*(edgesR G)^2 := by
  have hp (p : V × V) (hp : p ∈ safePairs H G) :
      mu*(2*Fintype.card V-1) ≤ (Nat.card (G.commonNeighbors p.1 p.2) : ℝ)+
        2*lam*degreeR G p.1*degreeR G p.2 := by
    obtain ⟨hne,hn,hf⟩ := (mem_filter.mp hp).2
    exact safe_merge_cost hg hlam hne hn hf
  have hh := sum_le_sum (fun p hp' => hp p hp')
  have ht := sum_le_sum_of_subset_of_nonneg
    (f := fun p : V × V => (Nat.card (G.commonNeighbors p.1 p.2) : ℝ)+
      2*lam*degreeR G p.1*degreeR G p.2)
    (subset_univ (safePairs H G)) (fun p _ _ => by
      exact add_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hlam)
          (degreeR_nonneg G p.1)) (degreeR_nonneg G p.2)))
  have he : (∑ p : V × V, 2*lam*degreeR G p.1*degreeR G p.2)=8*lam*(edgesR G)^2 := by
    rw [Fintype.sum_prod_type]
    simp_rw [← mul_sum,degreeR_sum]
    rw [← sum_mul,← mul_sum,degreeR_sum]
    ring
  rw [sum_const,nsmul_eq_mul] at hh
  simp only [sum_add_distrib,sum_common,he] at ht
  rw [sum_add_distrib] at hh
  nlinarith only [hh,ht]

lemma safePairs_energy_budget [Fintype V] {H : SimpleGraph W} {G : SimpleGraph V}
    {lam mu : ℝ} (hg : GlobalOptimal H G lam mu) (hlam : 0 ≤ lam) :
    mu*(2*Fintype.card V-1)*(safePairs H G).card ≤
      (1+2*lam*Fintype.card V)*energy G := by
  have hc := sq_sum_le_card_mul_sum_sq (s := (univ : Finset V)) (f := degreeR G)
  rw [card_univ,degreeR_sum] at hc
  change (2*edgesR G)^2 ≤ (Fintype.card V : ℝ)*energy G at hc
  have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2*lam by positivity)
  have hh := safePairs_budget hg hlam
  nlinarith only [hm,hh]

#print axioms merge_energy
#print axioms safe_merge_cost
#print axioms safePairs_energy_budget
end Erdos713MergeDegreePenalty
