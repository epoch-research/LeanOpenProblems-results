import Submission.GreedyCommonNeighbors
import Submission.RegularizationCommonNeighbors
import Submission.GreedySurvivalWitnesses

/-! Common-neighbor first-crossing tails for mixed hypergraphs of rank at
most four. Short-edge witnesses are charged at their actual support size;
zero-support witnesses are retained as a deterministic initial cost. -/
namespace Erdos773.GreedyMixedCommonTails
open Finset GreedyHypergraphState GreedyCommonNeighbors
open HypergraphDegreeTrim FourUniformRegularization
open FiniteKernelCrossing FiniteKilledKernel GreedySurvivalWitnesses
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [DecidableEq α]

/-- Witnesses of the first role have at most 2 K² occurrences at each vertex. -/
lemma first_role_incidence {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card ≤ 4) (u v a : α) (K : ℕ)
    (hK : ∀ b c : α, b ≠ c → pairDegree H b c ≤ K) :
    ((patterns H u v).filter (fun x => a ∈ x.1 \ {u,x.2.1})).card ≤ 2*K^2 := by
  by_cases hau : a = u
  · subst a
    simp
  have hsub : (patterns H u v).filter (fun x => a ∈ x.1 \ {u,x.2.1}) ⊆
      extensions H (H.filter (fun e => u ∈ e ∧ a ∈ e)) v (fun e => e \ {u,v,a}) := by
    rintro ⟨e,w,f⟩ hx
    obtain ⟨hx, ha⟩ := mem_filter.mp hx
    obtain ⟨he, hf, hu, hv, hw, hwf, hwu, hwv, _⟩ := mem_patterns.mp hx
    obtain ⟨ha, hna⟩ := mem_sdiff.mp ha
    have haw : a ≠ w := by intro h; exact hna (by simp [h])
    exact mem_extensions.mpr ⟨mem_filter.mpr ⟨he, hu, ha⟩,
      mem_sdiff.mpr ⟨hw, by simpa only [mem_insert, mem_singleton, not_or] using
        (And.intro hwu (And.intro hwv haw.symm))⟩, hf, hv, hwf⟩
  have hs (e : Finset α) (he : e ∈ H.filter (fun e => u ∈ e ∧ a ∈ e)) :
      (e \ {u,v,a}).card ≤ 2 := by
    obtain ⟨he, hu, ha⟩ := mem_filter.mp he
    have hp : ({u,a} : Finset α) ⊆ e := by simp [insert_subset_iff, hu, ha]
    have hh : e \ {u,v,a} ⊆ e \ {u,a} := by
      intro b hb
      simp only [mem_sdiff, mem_insert, mem_singleton] at *
      tauto
    have hh := card_le_card hh
    rw [card_sdiff_of_subset hp] at hh
    have hc := h4 e he
    have hpc : ({u,a} : Finset α).card=2 := by simp [Ne.symm hau]
    rw [hpc] at hh
    omega
  have hn (e : Finset α) (_he : e ∈ H.filter (fun e => u ∈ e ∧ a ∈ e))
      (w : α) (hw : w ∈ e \ {u,v,a}) : v ≠ w := by
    intro hvw
    exact (mem_sdiff.mp hw).2 (by simp [hvw])
  calc
    _ ≤ (extensions H (H.filter (fun e => u ∈ e ∧ a ∈ e)) v
        (fun e => e \ {u,v,a})).card := card_le_card hsub
    _ ≤ (H.filter (fun e => u ∈ e ∧ a ∈ e)).card*2*K :=
      extensions_card_le H _ v _ 2 K hs hn hK
    _ ≤ K*2*K := Nat.mul_le_mul_right K (Nat.mul_le_mul_right 2 (hK u a (Ne.symm hau)))
    _ = _ := by ring

lemma second_role_incidence {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card ≤ 4) (u v a : α) (K : ℕ)
    (hK : ∀ b c : α, b ≠ c → pairDegree H b c ≤ K) :
    ((patterns H u v).filter (fun x => a ∈ x.2.2 \ {v,x.2.1})).card ≤ 2*K^2 := by
  calc
    _ ≤ ((patterns H v u).filter (fun x => a ∈ x.1 \ {v,x.2.1})).card := by
      apply card_le_card_of_injOn (fun x : Pattern α => (x.2.2,x.2.1,x.1))
      · rintro ⟨e,w,f⟩ hx
        obtain ⟨hx, ha⟩ := mem_filter.mp hx
        exact mem_filter.mpr ⟨pattern_swap hx, ha⟩
      · rintro ⟨e,w,f⟩ _ ⟨e',w',f'⟩ _ h
        simpa only [Prod.mk.injEq, and_comm, and_left_comm, and_assoc] using h
    _ ≤ _ := first_role_incidence h4 v u a K hK

lemma witness_incidence {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card ≤ 4) (u v a : α) (K : ℕ)
    (hK : ∀ b c : α, b ≠ c → pairDegree H b c ≤ K) :
    ((patterns H u v).filter (fun x => a ∈ witness u v x)).card ≤ 4*K^2 := by
  have heq : (patterns H u v).filter (fun x => a ∈ witness u v x) =
      ((patterns H u v).filter (fun x => a ∈ x.1 \ {u,x.2.1})) ∪
      ((patterns H u v).filter (fun x => a ∈ x.2.2 \ {v,x.2.1})) := by
    ext x
    simp only [mem_filter, witness, mem_union]
    tauto
  rw [heq]
  have hh := card_union_le
    ((patterns H u v).filter (fun x => a ∈ x.1 \ {u,x.2.1}))
    ((patterns H u v).filter (fun x => a ∈ x.2.2 \ {v,x.2.1}))
  have h1 := first_role_incidence h4 u v a K hK
  have h2 := second_role_incidence h4 u v a K hK
  omega

lemma witness_card_le {H : Finset (Finset α)}
    (h4 : ∀ e∈H, e.card≤4) {u v : α} {x : Pattern α} (hx : x∈patterns H u v) :
    (witness u v x).card≤4 := by
  rcases x with ⟨e,w,f⟩
  obtain ⟨he,hf,hu,hv,hw,hwf,hwu,hwv,_⟩ := mem_patterns.mp hx
  have hp : ({u,w} : Finset α)⊆e := by simp [insert_subset_iff,hu,hw]
  have hq : ({v,w} : Finset α)⊆f := by simp [insert_subset_iff,hv,hwf]
  have hc : (e \ {u,w}).card≤2 := by
    rw [card_sdiff_of_subset hp]
    simp only [card_pair hwu.symm]
    have := h4 e he
    omega
  have hd : (f \ {v,w}).card≤2 := by
    rw [card_sdiff_of_subset hq]
    simp only [card_pair hwv.symm]
    have := h4 f hf
    omega
  change ((e \ {u,w})∪(f \ {v,w})).card≤4
  exact (card_union_le _ _).trans (by omega)

def supportLayer (H : Finset (Finset α)) (u v : α) (r : ℕ) : Finset (Pattern α) :=
  (patterns H u v).filter (fun x => (witness u v x).card=r)
def selectedCost (H : Finset (Finset α)) (u v : α) (r : ℕ) (I : Finset α) : ℕ :=
  ((supportLayer H u v r).filter (fun x => witness u v x⊆I)).card

lemma layer_incidence {H : Finset (Finset α)} (h4 : ∀ e∈H, e.card≤4)
    (u v a : α) (r K : ℕ) (hK : ∀ b c : α, b≠c → pairDegree H b c≤K) :
    ((supportLayer H u v r).filter (fun x => a∈witness u v x)).card≤4*K^2 := by
  apply (card_le_card (filter_subset_filter _ (filter_subset _ _))).trans
  exact witness_incidence h4 u v a K hK

lemma selectedCost_mono (H : Finset (Finset α)) (u v : α) (r : ℕ)
    {I J : Finset α} (hIJ : I⊆J) : selectedCost H u v r I≤selectedCost H u v r J := by
  apply card_le_card
  intro x hx
  obtain ⟨hx,hi⟩ := mem_filter.mp hx
  exact mem_filter.mpr ⟨hx,hi.trans hIJ⟩

lemma zero_cost (H : Finset (Finset α)) (u v : α) (I : Finset α) :
    selectedCost H u v 0 I=(supportLayer H u v 0).card := by
  unfold selectedCost
  congr 1
  apply filter_true_of_mem
  intro x hx
  have hc := (mem_filter.mp hx).2
  rw [card_eq_zero.mp hc]
  exact empty_subset I

lemma cost_decomposition {H : Finset (Finset α)} (h4 : ∀ e∈H, e.card≤4)
    (u v : α) (I : Finset α) :
    patternCost H u v I = (supportLayer H u v 0).card +
      ∑ r∈Icc 1 4, selectedCost H u v r I := by
  have hh := card_eq_sum_card_fiberwise (s := (patterns H u v).filter (fun x => witness u v x⊆I))
    (t := Icc 0 4) (f := fun x => (witness u v x).card)
    (fun x hx => mem_Icc.mpr ⟨Nat.zero_le _,witness_card_le h4 (mem_filter.mp hx).1⟩)
  have he (r : ℕ) : ((patterns H u v).filter (fun x => witness u v x⊆I)).filter
      (fun x => (witness u v x).card=r) =
      (supportLayer H u v r).filter (fun x => witness u v x⊆I) := by
    ext x
    simp only [supportLayer,mem_filter]
    tauto
  simp_rw [he] at hh
  change patternCost H u v I=∑ r∈Icc 0 4, selectedCost H u v r I at hh
  have hIcc : Icc 0 4=insert 0 (Icc 1 4) := by ext r; simp only [mem_Icc,mem_insert]; omega
  rw [hIcc,sum_insert (by simp),zero_cost] at hh
  exact hh

lemma empty_witness_edges {H : Finset (Finset α)} {u v w : α} {e f : Finset α}
    (hx : (e,w,f)∈patterns H u v) (h0 : (witness u v (e,w,f)).card=0) :
    e={u,w} ∧ f={v,w} := by
  obtain ⟨he,hf,hu,hv,hw,hwf,_⟩ := mem_patterns.mp hx
  have hz := card_eq_zero.mp h0
  change (e \ {u,w})∪(f \ {v,w})=∅ at hz
  obtain ⟨hz1,hz2⟩ := union_eq_empty.mp hz
  exact ⟨Subset.antisymm (sdiff_eq_empty_iff_subset.mp hz1) (by simp [insert_subset_iff,hu,hw]),
    Subset.antisymm (sdiff_eq_empty_iff_subset.mp hz2) (by simp [insert_subset_iff,hv,hwf])⟩

lemma zero_le_initial_common [Fintype α] (H : Finset (Finset α)) (u v : α) :
    (supportLayer H u v 0).card≤RegularizationCommonNeighbors.common H u v := by
  apply card_le_card_of_injOn (fun x : Pattern α => x.2.1)
  · rintro ⟨e,w,f⟩ hx
    obtain ⟨hx,h0⟩ := mem_filter.mp hx
    obtain ⟨he,hf⟩ := empty_witness_edges hx h0
    obtain ⟨heH,hfH,hu,hv,hw,hwf,hwu,hwv,_⟩ := mem_patterns.mp hx
    exact RegularizationCommonNeighbors.mem_both.mpr
      ⟨⟨hwu.symm,he ▸ heH⟩,⟨hwv.symm,hf ▸ hfH⟩⟩
  · rintro ⟨e,w,f⟩ hx ⟨e',w',f'⟩ hy heq
    obtain ⟨hx,hx0⟩ := mem_filter.mp hx
    obtain ⟨hy,hy0⟩ := mem_filter.mp hy
    obtain ⟨he,hf⟩ := empty_witness_edges hx hx0
    obtain ⟨he',hf'⟩ := empty_witness_edges hy hy0
    change w=w' at heq
    rw [he,hf,he',hf',heq]

variable {σ : Type*} [Fintype σ]

/-- A positive-support layer has its own packing tail. The power is r,
not three; this distinction is essential for initially present short edges. -/
theorem layer_tail {H : Finset (Finset α)} (h4 : ∀ e∈H, e.card≤4)
    (u v : α) (P r : ℕ) (hr : 0<r)
    (hP : ∀ a b : α, a≠b → pairDegree H a b≤P)
    (K : ℕ → Kernel (Option σ)) (carrier : σ → Finset α)
    (n h : ℕ) (x : σ) (p : ℝ) (cap k : ℕ)
    (hlaw : TargetLaw K carrier n h x p cap) (hp : 0≤p) (hp1 : p≤1)
    (hcap : r*(k+1)≤cap) :
    hit K (fun _ => liftEvent (fun y => r*(4*P^2)*k < selectedCost H u v r (carrier y)))
      n h (some x) ≤ (3*(supportLayer H u v r).card*p^r/(k+1))^(k+1) := by
  have hs (i : Pattern α) (hi : i∈supportLayer H u v r) : (witness u v i).card=r :=
    (mem_filter.mp hi).2
  exact packing_exponential_tail K carrier n h x p cap hlaw hp hp1
    (supportLayer H u v r) (witness u v) r (4*P^2) r k
    (fun i hi => card_pos.mp (by rw [hs i hi]; exact hr))
    (fun i hi => (hs i hi).le) (fun i hi => (hs i hi).ge)
    (fun a => layer_incidence h4 u v a r P hP) hcap

/-- All mixed common-neighbor prefix crossings are covered by four
positive-support layers plus the initial graph common-neighbor cap. -/
theorem prefix_common_tail [Fintype α] {H : Finset (Finset α)}
    (h4 : ∀ e∈H, e.card≤4) (u v : α) (huv : u≠v) (P C : ℕ)
    (hP : ∀ a b : α, a≠b → pairDegree H a b≤P)
    (hC : RegularizationCommonNeighbors.common H u v≤C)
    (K : ℕ → Kernel (Option σ)) (carrier : σ → Finset α)
    (n h : ℕ) (x : σ) (p : ℝ) (cap : ℕ) (k : ℕ → ℕ)
    (hlaw : TargetLaw K carrier n h x p cap) (hp : 0≤p) (hp1 : p≤1)
    (hcap : ∀ r∈Icc 1 4, r*(k r+1)≤cap) :
    hit K (fun _ => liftEvent (fun y => prefixBad H u v
      (C+∑ r∈Icc 1 4, r*(4*P^2)*k r) (carrier y))) n h (some x) ≤
      ∑ r∈Icc 1 4, (3*(supportLayer H u v r).card*p^r/(k r+1))^(k r+1) := by
  apply FiniteWitnessCrossing.witness_bound K (Icc 1 4) _
    (fun r _ => liftEvent (fun y => r*(4*P^2)*k r<selectedCost H u v r (carrier y)))
    (n+h) _ n h le_rfl (some x) _
    (fun r hr => layer_tail h4 u v P r (mem_Icc.mp hr).1 hP K carrier n h x p cap (k r)
      hlaw hp hp1 (hcap r hr))
  intro m hm y hy
  cases y with
  | none => exact hy.elim
  | some y =>
    obtain ⟨J,hJ,hu,hv,hbad⟩ := hy
    have hbound := (common_degree_bound huv hu hv).trans_eq (cost_decomposition h4 u v J)
    have hzero := (zero_le_initial_common H u v).trans hC
    have hex : ∃ r∈Icc 1 4, r*(4*P^2)*k r<selectedCost H u v r J := by
      by_contra! hh
      have hsum := sum_le_sum hh
      omega
    obtain ⟨r,hr,hrbad⟩ := hex
    exact ⟨r,hr,hrbad.trans_le (selectedCost_mono H u v r hJ)⟩

#print axioms witness_incidence
#print axioms witness_card_le
#print axioms layer_tail
#print axioms cost_decomposition
#print axioms zero_le_initial_common
#print axioms prefix_common_tail
end
end Erdos773.GreedyMixedCommonTails
