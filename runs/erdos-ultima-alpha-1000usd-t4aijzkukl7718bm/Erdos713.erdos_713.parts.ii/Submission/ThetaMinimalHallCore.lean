import FormalConjecturesUtil
import Submission.ThetaBadPairDeficiency
import Submission.ThetaRigidOutsidePacking

/-! Minimal Hall-deficient families of heavy pairs. These lemmas retain
supporting-row information instead of bounding all bad pairs by zeros.
They do not settle the density gap or Erdos 713. -/
open Finset
open scoped Classical
namespace Erdos713ThetaMinimalHallCore
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaHeavyMatching Erdos713ThetaRigidHeavyMatching
set_option maxHeartbeats 3000000
variable {A B : Type*} [Fintype A] [Fintype B]

noncomputable def neighbors (R : A → B → Prop) (S : Finset (HeavyPair R)) : Finset A :=
  S.biUnion (fun p => supports R p.val)

noncomputable def load (R : A → B → Prop) (S : Finset (HeavyPair R)) (a : A) : ℕ :=
  (S.filter (fun p => p.val.val ⊆ row R a)).card

def Core (R : A → B → Prop) (S : Finset (HeavyPair R)) : Prop :=
  (neighbors R S).card < S.card ∧
    ∀ T : Finset (HeavyPair R), T ⊂ S → T.card ≤ (neighbors R T).card

lemma neighbors_mono (R : A → B → Prop) {S T : Finset (HeavyPair R)} (h : S ⊆ T) :
    neighbors R S ⊆ neighbors R T := by
  intro a ha
  obtain ⟨p,hp,hap⟩ := mem_biUnion.mp ha
  exact mem_biUnion.mpr ⟨p,h hp,hap⟩

lemma mem_neighbors (R : A → B → Prop) (S : Finset (HeavyPair R)) (a : A) :
    a ∈ neighbors R S ↔ ∃ p ∈ S, p.val.val ⊆ row R a := by
  simp [neighbors,mem_supports]

lemma erase_proper {R : A → B → Prop} {S : Finset (HeavyPair R)} {p : HeavyPair R}
    (hp : p ∈ S) : S.erase p ⊂ S := by
  exact erase_ssubset hp

/-- A deficient family contains an inclusion-minimal deficient subfamily. -/
theorem exists_core {R : A → B → Prop} (S : Finset (HeavyPair R))
    (hS : (neighbors R S).card < S.card) :
    ∃ T ⊆ S, Core R T := by
  let F := S.powerset.filter (fun T => (neighbors R T).card < T.card)
  have hF : F.Nonempty := ⟨S,mem_filter.mpr ⟨mem_powerset.mpr (Subset.refl _),hS⟩⟩
  obtain ⟨T,hT,hmin⟩ := exists_min_image F Finset.card hF
  have hsub : T ⊆ S := mem_powerset.mp (mem_filter.mp hT).1
  refine ⟨T,hsub,(mem_filter.mp hT).2,?_⟩
  intro U hU
  by_contra hu
  have hUF : U ∈ F := mem_filter.mpr ⟨mem_powerset.mpr ((Finset.ssubset_iff_subset_ne.mp hU).1.trans hsub),
    Nat.lt_of_not_ge hu⟩
  have hh := hmin U hUF
  have hc := card_lt_card hU
  omega

lemma core_nonempty {R : A → B → Prop} {S : Finset (HeavyPair R)} (h : Core R S) : S.Nonempty :=
  card_pos.mp (Nat.zero_le _ |>.trans_lt h.1)

/-- Every minimal deficit is exactly one. -/
theorem core_deficit_one {R : A → B → Prop} {S : Finset (HeavyPair R)} (h : Core R S) :
    (neighbors R S).card+1=S.card := by
  obtain ⟨p,hp⟩ := core_nonempty h
  have hh := (h.2 _ (erase_proper hp)).trans (card_le_card (neighbors_mono R (erase_subset p S)))
  rw [card_erase_of_mem hp] at hh
  have hd := h.1
  omega

/-- A row supporting the core cannot be private to just one selected pair. -/
theorem core_load_two {R : A → B → Prop} {S : Finset (HeavyPair R)} (h : Core R S)
    {a : A} (ha : a ∈ neighbors R S) : 2 ≤ load R S a := by
  by_contra hn
  have hsmall : load R S a ≤ 1 := by omega
  obtain ⟨p,hp,hap⟩ := (mem_neighbors R S a).mp ha
  have he := core_deficit_one h
  have hsub : neighbors R (S.erase p) ⊆ (neighbors R S).erase a := by
    intro b hb
    have hbN := neighbors_mono R (erase_subset p S) hb
    apply mem_erase.mpr
    refine ⟨?_,hbN⟩
    intro hba
    subst b
    obtain ⟨q,hq,haq⟩ := (mem_neighbors R (S.erase p) a).mp hb
    have hqS := (mem_erase.mp hq).2
    have hqp := (mem_erase.mp hq).1
    have heq := card_le_one.mp hsmall q (mem_filter.mpr ⟨hqS,haq⟩)
      p (mem_filter.mpr ⟨hp,hap⟩)
    exact hqp heq
  have hh := (h.2 _ (erase_proper hp)).trans (card_le_card hsub)
  rw [card_erase_of_mem hp,card_erase_of_mem ha] at hh
  have hpos := card_pos.mpr (show (neighbors R S).Nonempty from ⟨a,ha⟩)
  omega

/-- No pair in a minimal deficient family has an exact-pair supporting row. -/
theorem core_no_exact {R : A → B → Prop} {S : Finset (HeavyPair R)} (h : Core R S)
    {p : HeavyPair R} (hp : p ∈ S) : ¬ ∃ a, row R a=p.val.val := by
  rintro ⟨a,ha⟩
  have haN : a ∈ neighbors R S := (mem_neighbors R S a).mpr ⟨p,hp,by rw [ha]⟩
  have hlarge := core_load_two h haN
  have hqp (q : HeavyPair R) (hq : q ∈ S.filter (fun q => q.val.val ⊆ row R a)) : q=p := by
    have hs := (mem_filter.mp hq).2
    rw [ha] at hs
    apply Subtype.ext
    apply Subtype.ext
    exact eq_of_subset_of_card_le hs (by rw [pair_card,pair_card])
  have hsmall : load R S a ≤ 1 := card_le_one.mpr (fun q hq r hr => (hqp q hq).trans (hqp r hr).symm)
  omega

/-- All supporting rows of a core have degree at least three in the ORIGINAL relation. -/
theorem core_row_three {R : A → B → Prop} {S : Finset (HeavyPair R)} (h : Core R S)
    {a : A} (ha : a ∈ neighbors R S) : 3 ≤ (row R a).card := by
  obtain ⟨p,hp,hpa⟩ := (mem_neighbors R S a).mp ha
  by_contra hn
  have he : row R a=p.val.val := (eq_of_subset_of_card_le hpa (by rw [pair_card]; omega)).symm
  exact core_no_exact h hp ⟨a,he⟩

lemma load_capacity (R : A → B → Prop) (S : Finset (HeavyPair R)) (a : A) :
    load R S a ≤ (row R a).card.choose 2 := by
  rw [← card_powersetCard]
  apply card_le_card_of_injOn (fun p : HeavyPair R => p.val.val)
  · intro p hp
    exact mem_powersetCard.mpr ⟨(mem_filter.mp hp).2,pair_card p.val⟩
  · intro p hp q hq he
    exact Subtype.ext (Subtype.ext he)

lemma load_sum (R : A → B → Prop) (S : Finset (HeavyPair R)) :
    ∑ a ∈ neighbors R S, load R S a = ∑ p ∈ S, (supports R p.val).card := by
  let I : A → HeavyPair R → Prop := fun a p => p.val.val ⊆ row R a
  have hp (p : HeavyPair R) (hpS : p ∈ S) :
      (neighbors R S).bipartiteBelow I p = supports R p.val := by
    ext a
    simp only [bipartiteBelow,mem_filter,mem_supports,I]
    exact ⟨fun h => h.2,fun h => ⟨(mem_neighbors R S a).mpr ⟨p,hpS,h⟩,h⟩⟩
  calc
    _ = ∑ a ∈ neighbors R S, (S.bipartiteAbove I a).card := rfl
    _ = ∑ p ∈ S, ((neighbors R S).bipartiteBelow I p).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow I
    _ = _ := sum_congr rfl (fun p hpS => by rw [hp p hpS])

/-- A core has a row serving at least four of its selected heavy pairs. -/
theorem core_overloaded {R : A → B → Prop} {S : Finset (HeavyPair R)} (h : Core R S) :
    ∃ a ∈ neighbors R S, 4 ≤ load R S a := by
  by_contra hn
  push_neg at hn
  have hu := sum_le_sum (s := neighbors R S) (fun a ha => show load R S a ≤ 3 from by
    have hh := hn a ha
    omega)
  rw [load_sum] at hu
  have hl := sum_le_sum (s := S) (fun p _ => p.property)
  simp only [sum_const,Nat.nsmul_eq_mul] at hu hl
  have hd := h.1
  omega

/-- Each selected pair in a fixed row has two other supporting rows. If
all supporting rows have degree at least three, their private vertices
inject into the columns outside the fixed row. -/
theorem outside_of_selected_pairs {R : A → B → Prop} (hf : ¬ HasTheta R)
    (hr : ∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2)
    (S : Finset (HeavyPair R))
    (hmin : ∀ b ∈ neighbors R S, 3 ≤ (row R b).card) (a : A) :
    2*load R S a ≤ Fintype.card B-(row R a).card := by
  let T := S.filter (fun p => p.val.val ⊆ row R a)
  have haT (p : T) : a ∈ supports R p.val.val :=
    (mem_supports R _ _).mpr (mem_filter.mp p.property).2
  have hsize (p : T) : 2 ≤ ((supports R p.val.val).erase a).card := by
    rw [card_erase_of_mem (haT p)]
    have hh := p.val.property
    omega
  let f (p : T) : Fin 2 ↪ ↥((supports R p.val.val).erase a) :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (by
      simpa only [Fintype.card_fin,Fintype.card_coe] using hsize p))
  let b (u : T × Fin 2) : A := (f u.1 u.2).val
  have hb (u : T × Fin 2) : b u ≠ a ∧ b u ∈ supports R u.1.val.val :=
    mem_erase.mp (f u.1 u.2).property
  have hdeg (u : T × Fin 2) : 3 ≤ (row R (b u)).card := by
    apply hmin
    exact (mem_neighbors R S _).mpr ⟨u.1.val,(mem_filter.mp u.1.property).1,
      (mem_supports R _ _).mp (hb u).2⟩
  have hpair (u : T × Fin 2) : row R (b u) ∩ row R a=u.1.val.val.val := by
    apply (eq_of_subset_of_card_le (subset_inter
      ((mem_supports R _ _).mp (hb u).2) (mem_filter.mp u.1.property).2) ?_).symm
    rw [pair_card]
    exact hr _ _ (hb u).1
  have hex (u : T × Fin 2) : (row R (b u) \ row R a).Nonempty := by
    rw [← card_pos,card_sdiff]
    have hd := hdeg u
    have hh : (row R a ∩ row R (b u)).card ≤ 2 := by
      simpa only [inter_comm] using hr _ _ (hb u).1
    omega
  choose x hx using hex
  have hxi : Function.Injective x := by
    intro u v he
    have hbc : b u=b v := Erdos713ThetaRigidOutsidePacking.outside_unique hf hr
      (by simpa only [mem_row] using (mem_sdiff.mp (hx u)).2)
      ((mem_row R _ _).mp (mem_sdiff.mp (hx u)).1)
      (by rw [he]; exact (mem_row R _ _).mp (mem_sdiff.mp (hx v)).1)
      (by rw [hpair u,pair_card]) (by rw [hpair v,pair_card])
    have hP : u.1.val.val.val=v.1.val.val.val := (hpair u).symm.trans
      ((congrArg (fun b => row R b ∩ row R a) hbc).trans (hpair v))
    have hp : u.1=v.1 := by
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact hP
    obtain ⟨p,i⟩ := u
    obtain ⟨q,j⟩ := v
    dsimp only at hp
    subst q
    have hij : i=j := (f p).injective (Subtype.ext hbc)
    exact Prod.ext rfl hij
  let g : T × Fin 2 → ↥((univ : Finset B) \ row R a) :=
    fun u => ⟨x u,mem_sdiff.mpr ⟨mem_univ _,(mem_sdiff.mp (hx u)).2⟩⟩
  have hi : Function.Injective g := fun u v he => hxi (congrArg Subtype.val he)
  have hc : T.card*2 ≤ ((univ : Finset B) \ row R a).card := by
    simpa only [Fintype.card_prod,Fintype.card_coe,Fintype.card_fin] using
      Fintype.card_le_of_injective g hi
  rw [card_sdiff_of_subset (subset_univ _),card_univ] at hc
  change load R S a*2 ≤ _ at hc
  omega

/-- A Hall core in a rigid theta-free relation requires at least twelve columns. -/
theorem core_twelve_columns {R : A → B → Prop} (hf : ¬ HasTheta R)
    (hr : ∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2)
    {S : Finset (HeavyPair R)} (h : Core R S) : 12 ≤ Fintype.card B := by
  obtain ⟨a,ha,hload⟩ := core_overloaded h
  have hout := outside_of_selected_pairs hf hr S (fun b hb => core_row_three h hb) a
  have hcap := load_capacity R S a
  have hd : 4 ≤ (row R a).card := by
    by_contra hn
    have hd3 : (row R a).card ≤ 3 := by omega
    interval_cases he : (row R a).card <;> norm_num [he] at hcap <;> omega
  omega

/-- A kernel-checked small-column Hall bound, not a numerical search report. -/
theorem hall_of_at_most_eleven {R : A → B → Prop} (hf : ¬ HasTheta R)
    (hr : ∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2)
    (hB : Fintype.card B ≤ 11) (S : Finset (HeavyPair R)) :
    S.card ≤ (neighbors R S).card := by
  by_contra hn
  obtain ⟨T,_hT,hcore⟩ := exists_core S (Nat.lt_of_not_ge hn)
  have hh := core_twelve_columns hf hr hcore
  omega

/-- In this small-column range the heavy-pair cardinality is at most the
row cardinality, with no zero-pair error term. -/
theorem heavy_card_le_rows_of_at_most_eleven {R : A → B → Prop} (hf : ¬ HasTheta R)
    (hr : ∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2)
    (hB : Fintype.card B ≤ 11) : Nat.card (HeavyPair R) ≤ Nat.card A := by
  have hh := (hall_of_at_most_eleven hf hr hB univ).trans (card_le_univ _)
  simpa only [card_univ,Nat.card_eq_fintype_card] using hh

#print axioms outside_of_selected_pairs
#print axioms core_twelve_columns
#print axioms hall_of_at_most_eleven
#print axioms heavy_card_le_rows_of_at_most_eleven

#print axioms exists_core
#print axioms core_deficit_one
#print axioms core_load_two
#print axioms core_no_exact
#print axioms core_row_three
#print axioms core_overloaded
end Erdos713ThetaMinimalHallCore
