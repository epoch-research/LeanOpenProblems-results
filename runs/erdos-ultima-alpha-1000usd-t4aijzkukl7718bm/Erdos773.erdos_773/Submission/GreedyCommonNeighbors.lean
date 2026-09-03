import Submission.GreedyWitnessPacking

/-!
Common-neighbor witnesses in the residual two-graph. Original edge pairs are
kept as indices, so repeated witnesses are counted with their multiplicity.
-/
namespace Erdos773.GreedyCommonNeighbors
open Finset GreedyHypergraphState StoppedGreedyMoments GreedyConfigurationTails
open GreedyWitnessPacking FourUniformRegularization HypergraphDegreeTrim
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [DecidableEq α]

abbrev Pattern (α : Type*) := Finset α × α × Finset α

def extensions (H E : Finset (Finset α)) (v : α) (W : Finset α → Finset α) :
    Finset (Pattern α) :=
  E.biUnion (fun e => (W e).biUnion (fun w =>
    (H.filter (fun f => v ∈ f ∧ w ∈ f)).image (fun f => (e,w,f))))

lemma mem_extensions {H E : Finset (Finset α)} {v : α}
    {W : Finset α → Finset α} {e f : Finset α} {w : α} :
    (e,w,f) ∈ extensions H E v W ↔ e ∈ E ∧ w ∈ W e ∧ f ∈ H ∧ v ∈ f ∧ w ∈ f := by
  simp only [extensions, mem_biUnion, mem_image, mem_filter, Prod.mk.injEq]
  constructor
  · rintro ⟨e', he', w', hw', f', ⟨hf', hv', hwf'⟩, he, hw, hf⟩
    subst e'; subst w'; subst f'
    exact ⟨he', hw', hf', hv', hwf'⟩
  · rintro ⟨he, hw, hf, hvf, hwf⟩
    exact ⟨e, he, w, hw, f, ⟨hf, hvf, hwf⟩, rfl, rfl, rfl⟩

lemma extensions_card_le (H E : Finset (Finset α)) (v : α)
    (W : Finset α → Finset α) (r K : ℕ)
    (hsize : ∀ e ∈ E, (W e).card ≤ r)
    (hne : ∀ e ∈ E, ∀ w ∈ W e, v ≠ w)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K) :
    (extensions H E v W).card ≤ E.card*r*K := by
  calc
    _ ≤ ∑ e ∈ E, ((W e).biUnion (fun w =>
      (H.filter (fun f => v ∈ f ∧ w ∈ f)).image (fun f => (e,w,f)))).card := card_biUnion_le
    _ ≤ ∑ e ∈ E, ∑ w ∈ W e,
      ((H.filter (fun f => v ∈ f ∧ w ∈ f)).image (fun f => (e,w,f))).card :=
      sum_le_sum (fun _ _ => card_biUnion_le)
    _ ≤ ∑ e ∈ E, ∑ _w ∈ W e, K := by
      apply sum_le_sum
      intro e he
      apply sum_le_sum
      intro w hw
      exact card_image_le.trans (hK v w (hne e he w hw))
    _ = ∑ e ∈ E, (W e).card*K := by simp
    _ ≤ ∑ _e ∈ E, r*K := sum_le_sum (fun e he => Nat.mul_le_mul_right K (hsize e he))
    _ = _ := by simp [mul_assoc]

/-- e contains u,w, f contains v,w, and neither edge contains the opposite
    designated endpoint. -/
def patterns (H : Finset (Finset α)) (u v : α) : Finset (Pattern α) :=
  (extensions H (H.filter (fun e => u ∈ e)) v (fun e => e \ {u,v})).filter
    (fun x => v ∉ x.1 ∧ u ∉ x.2.2)

lemma mem_patterns {H : Finset (Finset α)} {u v w : α} {e f : Finset α} :
    (e,w,f) ∈ patterns H u v ↔
      e ∈ H ∧ f ∈ H ∧ u ∈ e ∧ v ∈ f ∧ w ∈ e ∧ w ∈ f ∧
        w ≠ u ∧ w ≠ v ∧ v ∉ e ∧ u ∉ f := by
  simp only [patterns, mem_filter, mem_extensions, mem_sdiff, mem_insert, mem_singleton]
  tauto

lemma pattern_swap {H : Finset (Finset α)} {u v w : α} {e f : Finset α}
    (h : (e,w,f) ∈ patterns H u v) : (f,w,e) ∈ patterns H v u := by
  simp only [mem_patterns] at *
  tauto

lemma patterns_card_le {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4) (u v : α) (D K : ℕ)
    (hD : degree H u ≤ D)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K) :
    (patterns H u v).card ≤ 3*D*K := by
  have hs (e : Finset α) (he : e ∈ H.filter (fun e => u ∈ e)) : (e \ {u,v}).card ≤ 3 := by
    obtain ⟨he, hu⟩ := mem_filter.mp he
    have hsub : e \ {u,v} ⊆ e.erase u := by
      intro a ha
      simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at ha
      exact mem_erase.mpr ⟨ha.2.1, ha.1⟩
    have hh := card_le_card hsub
    rw [card_erase_of_mem hu, h4 e he] at hh
    exact hh
  have hn (e : Finset α) (_he : e ∈ H.filter (fun e => u ∈ e))
      (w : α) (hw : w ∈ e \ {u,v}) : v ≠ w := by
    intro hvw
    exact (mem_sdiff.mp hw).2 (by simp [hvw])
  calc
    _ ≤ (extensions H (H.filter (fun e => u ∈ e)) v (fun e => e \ {u,v})).card :=
      card_filter_le _ _
    _ ≤ (H.filter (fun e => u ∈ e)).card*3*K := extensions_card_le H _ v _ 3 K hs hn hK
    _ ≤ D*3*K := Nat.mul_le_mul_right K (Nat.mul_le_mul_right 3 hD)
    _ = _ := by ring

def witness (u v : α) (x : Pattern α) : Finset α :=
  (x.1 \ {u,x.2.1}) ∪ (x.2.2 \ {v,x.2.1})

lemma witness_swap (u v : α) (e f : Finset α) (w : α) :
    witness u v (e,w,f) = witness v u (f,w,e) := union_comm _ _

lemma pattern_residual_cards {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4) {u v w : α} {e f : Finset α}
    (h : (e,w,f) ∈ patterns H u v) :
    (e \ {u,w}).card = 2 ∧ (f \ {v,w}).card = 2 := by
  obtain ⟨he, hf, hu, hv, hw, hwf, hwu, hwv, _⟩ := mem_patterns.mp h
  have hp : ({u,w} : Finset α) ⊆ e := by simp [insert_subset_iff, hu, hw]
  have hq : ({v,w} : Finset α) ⊆ f := by simp [insert_subset_iff, hv, hwf]
  constructor
  · rw [card_sdiff_of_subset hp, h4 e he]
    simp [hwu.symm]
  · rw [card_sdiff_of_subset hq, h4 f hf]
    simp [hwv.symm]

lemma witness_card_bounds {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    {u v : α} {x : Pattern α} (hx : x ∈ patterns H u v) :
    3 ≤ (witness u v x).card ∧ (witness u v x).card ≤ 4 := by
  rcases x with ⟨e,w,f⟩
  obtain ⟨hc, hd⟩ := pattern_residual_cards h4 hx
  obtain ⟨he, hf, hu, hv, hw, hwf, hwu, hwv, hve, huf⟩ := mem_patterns.mp hx
  have hef : e ≠ f := by rintro rfl; exact huf hu
  let A := (e \ {u,w}) ∩ (f \ {v,w})
  have hwa : w ∉ A := by simp [A]
  have hsub : insert w A ⊆ e ∩ f := by
    apply insert_subset_iff.mpr
    refine ⟨mem_inter.mpr ⟨hw, hwf⟩, ?_⟩
    intro a ha
    exact mem_inter.mpr ⟨(mem_sdiff.mp (mem_inter.mp ha).1).1,
      (mem_sdiff.mp (mem_inter.mp ha).2).1⟩
  have hi := (card_le_card hsub).trans (h2 e he f hf hef)
  rw [card_insert_of_notMem hwa] at hi
  have hh := card_union_add_card_inter (e \ {u,w}) (f \ {v,w})
  rw [hc, hd] at hh
  change 3 ≤ ((e \ {u,w}) ∪ (f \ {v,w})).card ∧
    ((e \ {u,w}) ∪ (f \ {v,w})).card ≤ 4
  dsimp [A] at hi
  omega

/-- Witnesses of the first role have at most 2 K² occurrences at each vertex. -/
lemma first_role_incidence {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4) (u v a : α) (K : ℕ)
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
    rw [card_sdiff_of_subset hp, h4 e he] at hh
    simpa [(Ne.symm hau)] using hh
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
    (h4 : ∀ e ∈ H, e.card = 4) (u v a : α) (K : ℕ)
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
    (h4 : ∀ e ∈ H, e.card = 4) (u v a : α) (K : ℕ)
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

variable [Fintype α]

/-- Every common residual neighbor has a selected original-edge witness. -/
lemma common_neighbor_witness {H : Finset (Finset α)} {I : Finset α} {u v w : α}
    (huv : u ≠ v) (hu : u ∈ available H I) (hv : v ∈ available H I)
    (hw : w ∈ closes H I u ∩ closes H I v) :
    ∃ x ∈ patterns H u v, x.2.1 = w ∧ witness u v x ⊆ I := by
  obtain ⟨hwu, hwv⟩ := mem_inter.mp hw
  obtain ⟨_, hwu, e, he, heq⟩ := mem_closes.mp hwu
  obtain ⟨_, hwv, f, hf, hfq⟩ := mem_closes.mp hwv
  have hue : u ∈ e := by
    have hh : u ∈ e \ I := by rw [heq]; simp
    exact (mem_sdiff.mp hh).1
  have hwe : w ∈ e := by
    have hh : w ∈ e \ I := by rw [heq]; simp
    exact (mem_sdiff.mp hh).1
  have hvf : v ∈ f := by
    have hh : v ∈ f \ I := by rw [hfq]; simp
    exact (mem_sdiff.mp hh).1
  have hwf : w ∈ f := by
    have hh : w ∈ f \ I := by rw [hfq]; simp
    exact (mem_sdiff.mp hh).1
  have hve : v ∉ e := by
    intro hve
    have hh : v ∈ e \ I := mem_sdiff.mpr ⟨hve, (mem_available.mp hv).1⟩
    rw [heq] at hh
    simp only [mem_insert, mem_singleton] at hh
    exact hh.elim huv.symm hwv.symm
  have huf : u ∉ f := by
    intro huf
    have hh : u ∈ f \ I := mem_sdiff.mpr ⟨huf, (mem_available.mp hu).1⟩
    rw [hfq] at hh
    simp only [mem_insert, mem_singleton] at hh
    exact hh.elim huv hwu.symm
  refine ⟨(e,w,f), mem_patterns.mpr ⟨he,hf,hue,hvf,hwe,hwf,hwu,hwv,hve,huf⟩, rfl, ?_⟩
  intro a ha
  by_contra hai
  rcases mem_union.mp ha with ha | ha
  · have hh : a ∈ e \ I := mem_sdiff.mpr ⟨(mem_sdiff.mp ha).1,hai⟩
    rw [heq] at hh
    exact (mem_sdiff.mp ha).2 hh
  · have hh : a ∈ f \ I := mem_sdiff.mpr ⟨(mem_sdiff.mp ha).1,hai⟩
    rw [hfq] at hh
    exact (mem_sdiff.mp ha).2 hh

def patternCost (H : Finset (Finset α)) (u v : α) (I : Finset α) : ℕ :=
  ((patterns H u v).filter (fun x => witness u v x ⊆ I)).card

omit [Fintype α] in
lemma patternCost_mono (H : Finset (Finset α)) (u v : α) {I J : Finset α} (hIJ : I ⊆ J) :
    patternCost H u v I ≤ patternCost H u v J := by
  apply card_le_card
  intro x hx
  obtain ⟨hx, hxi⟩ := mem_filter.mp hx
  exact mem_filter.mpr ⟨hx, hxi.trans hIJ⟩

def commonDegree (H : Finset (Finset α)) (I : Finset α) (u v : α) : ℕ :=
  (closes H I u ∩ closes H I v).card

lemma common_degree_bound {H : Finset (Finset α)} {I : Finset α} {u v : α}
    (huv : u ≠ v) (hu : u ∈ available H I) (hv : v ∈ available H I) :
    commonDegree H I u v ≤ patternCost H u v I := by
  have hs : closes H I u ∩ closes H I v ⊆
      ((patterns H u v).filter (fun x => witness u v x ⊆ I)).image (fun x => x.2.1) := by
    intro w hw
    obtain ⟨x,hx,hxw,hxi⟩ := common_neighbor_witness huv hu hv hw
    exact mem_image.mpr ⟨x,mem_filter.mpr ⟨hx,hxi⟩,hxw⟩
  exact (card_le_card hs).trans card_image_le

def prefixBad (H : Finset (Finset α)) (u v : α) (B : ℕ) (I : Finset α) : Prop :=
  ∃ J ⊆ I, u ∈ available H J ∧ v ∈ available H J ∧ B < commonDegree H J u v

/-- A single witness count controls all prefixes while both endpoints remain
    available. No assertion that the stopped process keeps running is made. -/
theorem prefix_common_tail {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    (u v : α) (huv : u ≠ v) (D K : ℕ) (hD : degree H u ≤ D)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    (L : ℕ) (hL : 0 < L) (n : ℕ) (hn : n ≤ L) (k : ℕ) :
    expectation H L n (event (prefixBad H u v (16*K^2*k))) ≤
      ((3*D*K).choose (k+1) : ℝ)*((n:ℝ)/L)^(3*(k+1)) := by
  have hdom (I : Finset α) : event (prefixBad H u v (16*K^2*k)) I ≤
      event (fun I => 4*(4*K^2)*k < patternCost H u v I) I := by
    classical
    by_cases hb : prefixBad H u v (16*K^2*k) I
    · have hlt : 4*(4*K^2)*k < patternCost H u v I := by
        obtain ⟨J,hJI,hu,hv,hb⟩ := hb
        have hh := hb.trans_le ((common_degree_bound huv hu hv).trans (patternCost_mono H u v hJI))
        convert hh using 1; ring
      simp only [event, if_pos hb, if_pos hlt, le_refl]
    · simpa only [event, if_neg hb] using event_nonneg
        (fun I => 4*(4*K^2)*k < patternCost H u v I) I
  have hs (x : Pattern α) (hx : x ∈ patterns H u v) := witness_card_bounds h4 h2 hx
  calc
    _ ≤ expectation H L n (event (fun I => 4*(4*K^2)*k < patternCost H u v I)) :=
      expectation_mono H L n hdom
    _ ≤ ((patterns H u v).card.choose (k+1) : ℝ)*((n:ℝ)/L)^(3*(k+1)) :=
      packing_tail H L hL n hn (patterns H u v) (witness u v) 4 (4*K^2) 3 k
        (fun x hx => card_pos.mp (by have := (hs x hx).1; omega))
        (fun x hx => (hs x hx).2) (fun x hx => (hs x hx).1)
        (fun a => witness_incidence h4 u v a K hK)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast Nat.choose_le_choose (k+1) (patterns_card_le h4 u v D K hD hK)

/-- Explicit exponentially small common-neighbor tail after packing. -/
theorem prefix_common_exponential_tail {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    (u v : α) (huv : u ≠ v) (D K : ℕ) (hD : degree H u ≤ D)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K)
    (L : ℕ) (hL : 0 < L) (n : ℕ) (hn : n ≤ L) (k : ℕ) :
    expectation H L n (event (prefixBad H u v (16*K^2*k))) ≤
      (9*D*K*((n:ℝ)/L)^3/(k+1))^(k+1) := by
  have hh := (prefix_common_tail h4 h2 u v huv D K hD hK L hL n hn k).trans
    (choose_mul_pow_le (3*D*K) (k+1) 3 (by omega) ((n:ℝ)/L) (by positivity))
  convert hh using 1
  push_cast
  ring

#print axioms common_degree_bound
#print axioms prefix_common_tail
#print axioms prefix_common_exponential_tail
#print axioms patterns_card_le
#print axioms witness_card_bounds
#print axioms witness_incidence
end
end Erdos773.GreedyCommonNeighbors
