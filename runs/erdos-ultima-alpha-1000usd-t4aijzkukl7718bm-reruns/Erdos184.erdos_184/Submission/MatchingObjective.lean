import Submission.MatchingSmoothing
import Submission.ConePaths
import Submission.CountCritical
import Submission.TwoTerminalGluing

/-!
The objective optimized by matching smoothing. This module does not establish
a bounded-loss matching choice or the Erdős--Gallai conjecture.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.MatchingObjective
open MatchingSmoothing CountCritical CycleNumberSubmodularity
variable {V : Type*}
set_option maxHeartbeats 1000000

/-- A walk which stays off the new apex is exactly a lifted old walk. -/
lemma pullback_walk (A : SimpleGraph V) (S : Set V) {a b : V}
    (p : (FanPaths.cone A S).Walk (some a) (some b))
    (hn : none ∉ p.support) :
    ∃ q : A.Walk a b, q.map (FanPaths.someEmbedding A S).toHom = p := by
  let hs : ∀ x ∈ p.support, x ∈ Set.range (Option.some : V → Option V) := by
    intro x hx
    cases x with
    | none => exact (hn hx).elim
    | some x => exact ⟨x,rfl⟩
  let r := p.induce (Set.range (Option.some : V → Option V)) hs
  let q : A.Walk a b := r.map (FanPaths.pullbackHom A S a)
  refine ⟨q,?_⟩
  have hcomp : (FanPaths.someEmbedding A S).toHom.comp (FanPaths.pullbackHom A S a) =
      (Embedding.induce (Set.range (Option.some : V → Option V))).toHom := by
    apply RelHom.ext
    intro x
    obtain ⟨z,hz⟩ := x.property
    change some (x.val.getD a) = x.val
    rw [← hz]
    rfl
  dsimp only [q]
  rw [Walk.map_map]
  have hh := Walk.map_eq_of_eq r _ hcomp
  simpa only [r,Walk.map_induce,Walk.copy_rfl_rfl] using hh

/-- The two neighbors of a vertex in a cycle are distinct. -/
lemma cycle_neighbors [Fintype V] {G : SimpleGraph V} (H : G.Subgraph)
    (hr : H.coe.IsRegularOfDegree 2) {v : V} (hv : v ∈ H.verts) :
    ∃ a b, a ≠ b ∧ H.neighborSet v = {a,b} := by
  have hh := hr ⟨v,hv⟩
  rw [Subgraph.coe_degree] at hh
  have hn : (H.neighborSet v).ncard = 2 := by
    simpa only [Subgraph.degree,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] using hh
  exact Set.ncard_eq_two.mp hn

/-- Removing the apex from a cycle leaves one entire simple path, not merely
some path between its two neighbors. Both old-edge and spoke coverage are exact. -/
lemma remove_apex [Fintype V] (A : SimpleGraph V) (S : Set V)
    (H : (FanPaths.cone A S).Subgraph)
    (hc : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) (hv : none ∈ H.verts) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ ∃ p : A.Walk a b,
      p.IsPath ∧
      (∀ x y, s(x,y) ∈ p.edges ↔ H.Adj (some x) (some y)) ∧
      (∀ x, H.Adj none (some x) ↔ x = a ∨ x = b) := by
  obtain ⟨c,hcC,hcH⟩ := CycleRing.cycle_piece_walk_at H hc.1 hc.2 none hv
  cases c with
  | nil => exact (hcC.not_nil (by simp)).elim
  | @cons _ x _ hnx r =>
    cases x with
    | none => exact hnx.elim
    | some a =>
      obtain ⟨hr,hfirst⟩ := (Walk.cons_isCycle_iff _ _).mp hcC
      obtain ⟨y,hny,t,hrt⟩ := Walk.exists_eq_cons_of_ne (by simp :
        (none : Option V) ≠ some a) r.reverse
      cases y with
      | none => exact hny.elim
      | some b =>
        have hrtPath := hr.reverse
        rw [hrt,Walk.cons_isPath_iff] at hrtPath
        obtain ⟨q,hq⟩ := pullback_walk A S t hrtPath.2
        have hqp : q.IsPath := Walk.IsPath.of_map (by rw [hq]; exact hrtPath.1)
        have hab : a ≠ b := by
          intro h
          subst b
          apply hfirst
          have he : s(none,some a) ∈ r.reverse.edges := by rw [hrt]; simp
          simpa only [Walk.edges_reverse,List.mem_reverse] using he
        refine ⟨a,hnx,b,hny,hab,q.reverse,hqp.reverse,?_,?_⟩
        · intro x y
          have heH : H.Adj (some x) (some y) ↔ s(some x,some y) ∈ r.edges := by
            rw [← hcH]
            change s(some x,some y) ∈ (Walk.cons hnx r).toSubgraph.edgeSet ↔ _
            rw [Walk.mem_edges_toSubgraph,Walk.edges_cons,List.mem_cons]
            simp
          have hrr : s(some x,some y) ∈ r.edges ↔ s(some x,some y) ∈ t.edges := by
            calc
              _ ↔ s(some x,some y) ∈ r.reverse.edges := by simp
              _ ↔ _ := by rw [hrt,Walk.edges_cons,List.mem_cons]; simp
          rw [heH,hrr,← hq,Walk.edges_map,Walk.edges_reverse,List.mem_reverse]
          constructor
          · intro he
            exact List.mem_map.mpr ⟨s(x,y),he,rfl⟩
          · intro he
            obtain ⟨e,he,heq⟩ := List.mem_map.mp he
            have heq' : e = s(x,y) := (Sym2.map.injective (Option.some_injective V)) heq
            exact heq' ▸ he
        · intro x
          have hnr : H.neighborSet none = {some a,some b} := by
            rw [← hcH,hcC.neighborSet_toSubgraph_endpoint]
            rw [Walk.snd_cons]
            congr 1
            have hh := congrArg Walk.snd hrt
            have hh' : r.penultimate = some b := by
              simpa only [Walk.snd_reverse,Walk.snd_cons] using hh
            rw [Walk.penultimate_cons_of_not_nil,hh']
            exact Walk.not_nil_of_ne (by simp)
          change some x ∈ H.neighborSet none ↔ _
          rw [hnr]
          simp

/-- Pair the two apex neighbors belonging to each piece of a partition. -/
def pairing (A : SimpleGraph V) (S : Set V)
    (D : Finset (FanPaths.cone A S).Subgraph) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ∃ H ∈ D, H.Adj none (some x) ∧ H.Adj none (some y)
  symm := by
    rintro x y ⟨hne,H,hH,hx,hy⟩
    exact ⟨hne.symm,H,hH,hy,hx⟩
  loopless := by intro x h; exact h.1 rfl

lemma piece_unique {G : SimpleGraph V} (D : Finset G.Subgraph)
    (hd : IsDecomposition G D) {H K : G.Subgraph} (hH : H ∈ D) (hK : K ∈ D)
    {e : Sym2 V} (heH : e ∈ H.edgeSet) (heK : e ∈ K.edgeSet) : H = K := by
  by_contra hne
  exact Set.disjoint_left.mp (hd.1 hH hK hne) heH heK

lemma pairing_matching [Fintype V] (A : SimpleGraph V) (S : Set V)
    (D : Finset (FanPaths.cone A S).Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition (FanPaths.cone A S) D) : IsMatching (pairing A S D) := by
  rintro x y z ⟨hxy,H,hH,hx,hy⟩ ⟨hxz,K,hK,hx',hz⟩
  have hHK := piece_unique D hd hH hK (e := s(none,some x)) hx hx'
  subst K
  obtain ⟨a,ha,b,hb,hab,p,hp,hpe,hs⟩ := remove_apex A S H (hc H hH) (H.edge_vert hx)
  have hxa := (hs x).mp hx
  have hya := (hs y).mp hy
  have hza := (hs z).mp hz
  rcases hxa with rfl | rfl <;> rcases hya with rfl | rfl <;>
    rcases hza with rfl | rfl <;> tauto

lemma pairing_support [Fintype V] (A : SimpleGraph V) (S : Set V)
    (D : Finset (FanPaths.cone A S).Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition (FanPaths.cone A S) D) : (pairing A S D).support = S := by
  ext x
  constructor
  · rintro ⟨y,hxy,H,hH,hx,hy⟩
    exact H.adj_sub hx
  · intro hx
    have he : s(none,some x) ∈ (FanPaths.cone A S).edgeSet := hx
    rw [← hd.2] at he
    obtain ⟨H,hH,heH⟩ := Set.mem_iUnion₂.mp he
    obtain ⟨a,ha,b,hb,hab,p,hp,hpe,hs⟩ := remove_apex A S H (hc H hH) (H.edge_vert heH)
    rcases (hs x).mp heH with rfl | rfl
    · exact ⟨b,hab,H,hH,heH,(hs b).mpr (Or.inr rfl)⟩
    · exact ⟨a,hab.symm,H,hH,heH,(hs a).mpr (Or.inl rfl)⟩

lemma pairing_disjoint (A : SimpleGraph V) (S : Set V)
    (hind : ∀ x ∈ S, ∀ y ∈ S, ¬ A.Adj x y)
    (D : Finset (FanPaths.cone A S).Subgraph) :
    Disjoint A.edgeSet (pairing A S D).edgeSet := by
  apply Set.disjoint_left.mpr
  intro e heA heM
  induction e using Sym2.ind with
  | h x y =>
    obtain ⟨hxy,H,hH,hx,hy⟩ := heM
    exact hind x (H.adj_sub hx) y (H.adj_sub hy) heA

/-- Suppress the apex in one partition member. Independence prevents the
new closing edge from already belonging to its complementary path. -/
lemma suppress_piece [Fintype V] (A : SimpleGraph V) (S : Set V)
    (hind : ∀ x ∈ S, ∀ y ∈ S, ¬ A.Adj x y)
    (D : Finset (FanPaths.cone A S).Subgraph)
    (H : (FanPaths.cone A S).Subgraph) (hHD : H ∈ D)
    (hc : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) :
    ∃ K : (A ⊔ pairing A S D).Subgraph,
      (K.coe.Connected ∧ K.coe.IsRegularOfDegree 2) ∧
      ∀ x y, K.Adj x y ↔ H.Adj (some x) (some y) ∨
        (x ≠ y ∧ H.Adj none (some x) ∧ H.Adj none (some y)) := by
  let B := A ⊔ pairing A S D
  by_cases hv : none ∈ H.verts
  · obtain ⟨a,ha,b,hb,hab,p,hp,hpe,hs⟩ := remove_apex A S H hc hv
    have hbaM : (pairing A S D).Adj b a :=
      ⟨hab.symm,H,hHD,(hs b).mpr (Or.inr rfl),(hs a).mpr (Or.inl rfl)⟩
    have hm : ∀ e ∈ p.edges, e ∈ B.edgeSet :=
      fun e he => edgeSet_mono (show A ≤ B from le_sup_left) (p.edges_subset_edgeSet he)
    let q := p.transfer B hm
    have hq : q.IsPath := hp.transfer hm
    have hne : s(b,a) ∉ q.edges := by
      rw [Walk.edges_transfer]
      intro he
      exact hind b hb a ha (p.edges_subset_edgeSet he)
    let c := q.cons (show B.Adj b a from Or.inr hbaM)
    have hcy : c.IsCycle := (Walk.cons_isCycle_iff _ _).mpr ⟨hq,hne⟩
    have hcK := cycle_subgraph_regular B hcy
    refine ⟨c.toSubgraph,⟨hcK.1,?_⟩,?_⟩
    · intro z
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hcK.2 z
    intro x y
    change s(x,y) ∈ c.toSubgraph.edgeSet ↔ _
    rw [Walk.mem_edges_toSubgraph]
    simp only [c,Walk.edges_cons,List.mem_cons,q,Walk.edges_transfer,hpe,hs]
    have hh : s(x,y) = s(b,a) ↔ x ≠ y ∧ (x = a ∨ x = b) ∧ (y = a ∨ y = b) := by
      rw [Sym2.eq_iff]
      constructor
      · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;> tauto
      · rintro ⟨hne,(rfl | rfl),(rfl | rfl)⟩ <;> tauto
    rw [hh,or_comm]
  · obtain ⟨z⟩ := hc.1.nonempty
    obtain ⟨z,hz⟩ := z
    cases z with
    | none => exact (hv hz).elim
    | some a =>
      obtain ⟨c,hcy,hcH⟩ := CycleRing.cycle_piece_walk_at H hc.1 hc.2 (some a) hz
      have hnc : none ∉ c.support := by
        intro hn
        exact hv (hcH ▸ c.mem_verts_toSubgraph.mpr hn)
      obtain ⟨p,hp⟩ := pullback_walk A S c hnc
      have hpC : p.IsCycle := (Walk.map_isCycle_iff_of_injective
        (Option.some_injective V)).mp (hp.symm ▸ hcy)
      have hm : ∀ e ∈ p.edges, e ∈ B.edgeSet :=
        fun e he => edgeSet_mono (show A ≤ B from le_sup_left) (p.edges_subset_edgeSet he)
      let q := p.transfer B hm
      have hcK := cycle_subgraph_regular B (hpC.transfer hm)
      refine ⟨q.toSubgraph,⟨hcK.1,?_⟩,?_⟩
      · intro z
        simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hcK.2 z
      intro x y
      have hn : ¬H.Adj none (some x) := fun hh => hv (H.edge_vert hh)
      simp only [hn,false_and,and_false,or_false]
      change s(x,y) ∈ q.toSubgraph.edgeSet ↔ _
      rw [Walk.mem_edges_toSubgraph,Walk.edges_transfer]
      rw [← hcH]
      change _ ↔ s(some x,some y) ∈ c.toSubgraph.edgeSet
      rw [Walk.mem_edges_toSubgraph,← hp,Walk.edges_map]
      exact (List.mem_map_of_injective (Sym2.map.injective (Option.some_injective V))).symm

/-- Number of pieces avoiding all matching edges. -/
noncomputable def avoiding {G : SimpleGraph V} (M : SimpleGraph V)
    (D : Finset G.Subgraph) : ℕ :=
  (D.filter (fun H => Disjoint H.edgeSet M.edgeSet)).card

lemma suppress_decomposition [Fintype V] (A : SimpleGraph V) (S : Set V)
    (hind : ∀ x ∈ S, ∀ y ∈ S, ¬ A.Adj x y)
    (D : Finset (FanPaths.cone A S).Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition (FanPaths.cone A S) D) :
    ∃ E : Finset (A ⊔ pairing A S D).Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (A ⊔ pairing A S D) E ∧
      avoiding (pairing A S D) E ≤ (D.filter (fun H => none ∉ H.verts)).card := by
  have hex (i : D) := suppress_piece A S hind D i.val i.property (hc i.val i.property)
  choose f hf hfe using hex
  let E := Finset.univ.image f
  have hsame (i j : D) (x y : V) (hi : (f i).Adj x y) (hj : (f j).Adj x y) : i = j := by
    apply Subtype.ext
    rcases (hfe i x y).mp hi with hi | ⟨hxy,hix,hiy⟩ <;>
      rcases (hfe j x y).mp hj with hj | ⟨hxy',hjx,hjy⟩
    · exact piece_unique D hd i.property j.property (e := s(some x,some y)) hi hj
    · exact (hind x (j.val.adj_sub hjx) y (j.val.adj_sub hjy) (i.val.adj_sub hi)).elim
    · exact (hind x (i.val.adj_sub hix) y (i.val.adj_sub hiy) (j.val.adj_sub hj)).elim
    · exact piece_unique D hd i.property j.property (e := s(none,some x)) hix hjx
  have hmarked (i : D) : Disjoint (f i).edgeSet (pairing A S D).edgeSet ↔ none ∉ i.val.verts := by
    constructor
    · intro hdis hv
      obtain ⟨a,ha,b,hb,hab,p,hp,hpe,hs⟩ := remove_apex A S i.val (hc i.val i.property) hv
      have he : (f i).Adj a b := (hfe i a b).mpr (Or.inr
        ⟨hab,(hs a).mpr (Or.inl rfl),(hs b).mpr (Or.inr rfl)⟩)
      have hm : (pairing A S D).Adj a b :=
        ⟨hab,i.val,i.property,(hs a).mpr (Or.inl rfl),(hs b).mpr (Or.inr rfl)⟩
      exact Set.disjoint_left.mp hdis (show s(a,b) ∈ (f i).edgeSet from he) hm
    · intro hv
      apply Set.disjoint_left.mpr
      intro e he hm
      induction e using Sym2.ind with
      | h x y =>
        rcases (hfe i x y).mp he with ho | ⟨hne,hx,hy⟩
        · exact Set.disjoint_left.mp (pairing_disjoint A S hind D) (i.val.adj_sub ho) hm
        · exact hv (i.val.edge_vert hx)
  refine ⟨E,?_,⟨?_,?_⟩,?_⟩
  · intro K hK
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hK
    exact hf i
  · intro K hK L hL hne
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hK
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hL
    apply Set.disjoint_left.mpr
    intro e hi hj
    induction e using Sym2.ind with
    | h x y => exact hne (congrArg f (hsame i j x y hi hj))
  · ext e
    constructor
    · rintro he
      obtain ⟨K,hK,heK⟩ := Set.mem_iUnion₂.mp he
      exact K.edgeSet_subset heK
    · intro he
      induction e using Sym2.ind with
      | h x y =>
        rcases he with he | ⟨hne,H,hH,hx,hy⟩
        · have ho : s(some x,some y) ∈ (FanPaths.cone A S).edgeSet := he
          rw [← hd.2] at ho
          obtain ⟨H,hH,heH⟩ := Set.mem_iUnion₂.mp ho
          let i : D := ⟨H,hH⟩
          exact Set.mem_iUnion₂.mpr ⟨f i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,
            (hfe i x y).mpr (Or.inl heH)⟩
        · let i : D := ⟨H,hH⟩
          exact Set.mem_iUnion₂.mpr ⟨f i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,
            (hfe i x y).mpr (Or.inr ⟨hne,hx,hy⟩)⟩
  · let T : Finset D := Finset.univ.filter (fun i => none ∉ i.val.verts)
    have heq : E.filter (fun H => Disjoint H.edgeSet (pairing A S D).edgeSet) = T.image f := by
      ext K
      simp only [Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and,E,T]
      constructor
      · rintro ⟨⟨i,rfl⟩,hi⟩
        exact ⟨i,(hmarked i).mp hi,rfl⟩
      · rintro ⟨i,hi,rfl⟩
        exact ⟨⟨i,rfl⟩,(hmarked i).mpr hi⟩
    have hT : T.card = (D.filter (fun H => none ∉ H.verts)).card := by
      apply Finset.card_bij (fun i _ => i.val)
      · intro i hi
        exact Finset.mem_filter.mpr ⟨i.property,(Finset.mem_filter.mp hi).2⟩
      · intro i hi j hj hij
        exact Subtype.ext hij
      · intro H hH
        exact ⟨⟨H,(Finset.mem_filter.mp hH).1⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hH).2⟩,rfl⟩
    dsimp only [avoiding]
    rw [heq]
    exact Finset.card_image_le.trans_eq hT

lemma apex_eq_cone (A M : SimpleGraph V) (S : Set V) (hM : M.support = S) :
    apex A M = FanPaths.cone A S := by
  ext x y
  cases x <;> cases y <;> simp [apex,FanPaths.cone,hM]

lemma avoiding_add_marked {G : SimpleGraph V} (M : SimpleGraph V)
    (D : Finset G.Subgraph) :
    avoiding M D + (D.filter (fun H => (H.edgeSet ∩ M.edgeSet).Nonempty)).card = D.card := by
  have hh := Finset.card_filter_add_card_filter_not (s := D)
    (fun H => (H.edgeSet ∩ M.edgeSet).Nonempty)
  simp only [Set.not_nonempty_iff_eq_empty,← Set.disjoint_iff_inter_eq_empty] at hh
  dsimp only [avoiding]
  omega

/-- Every repaired partition bounds the original count by half the apex
degree plus the number of matching-avoiding pieces. -/
lemma number_le_objective [Fintype V] (A M : SimpleGraph V) (S : Set V)
    (hm : IsMatching M) (hM : M.support = S) (ham : Disjoint A.edgeSet M.edgeSet)
    (D : Finset (A ⊔ M).Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition (A ⊔ M) D) :
    cycleNumber (FanPaths.cone A S) ≤ S.ncard / 2 + avoiding M D := by
  obtain ⟨E,hcE,hdE,hb⟩ := MatchingSmoothing.lift_decomposition A M hm ham D hc hd
  have hn := number_le (apex A M) E (by
    simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using hcE) hdE
  have hn' : cycleNumber (FanPaths.cone A S) ≤ E.card := by
    calc
      _ = cycleNumber (apex A M) := congrArg cycleNumber (apex_eq_cone A M S hM).symm
      _ ≤ E.card := hn
  have hr := hm.support_card
  rw [hM] at hr
  have hr' : S.ncard / 2 = M.edgeSet.ncard := by omega
  have hf := avoiding_add_marked M D
  omega

/-- There is a matching and a repaired partition attaining that objective.
The repaired partition need not minimize its TOTAL piece count. -/
lemma exists_objective_attainer [Fintype V] (A : SimpleGraph V) (S : Set V)
    (hind : ∀ x ∈ S, ∀ y ∈ S, ¬ A.Adj x y)
    (he : ∀ v, Even ((FanPaths.cone A S).degree v)) :
    ∃ M : SimpleGraph V, IsMatching M ∧ M.support = S ∧
      Disjoint A.edgeSet M.edgeSet ∧
      ∃ E : Finset (A ⊔ M).Subgraph,
        (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
        IsDecomposition (A ⊔ M) E ∧
        cycleNumber (FanPaths.cone A S) = S.ncard / 2 + avoiding M E := by
  obtain ⟨D,hc,hd,hmin⟩ := minimum_exists (FanPaths.cone A S) he
  let M := pairing A S D
  have hm : IsMatching M := pairing_matching A S D hc hd
  have hM : M.support = S := pairing_support A S D hc hd
  have ham : Disjoint A.edgeSet M.edgeSet := pairing_disjoint A S hind D
  obtain ⟨E,hcE,hdE,havoid⟩ := suppress_decomposition A S hind D hc hd
  have hl := number_le_objective A M S hm hM ham E hcE hdE
  have hstar := cycle_decomposition_vertex_count (FanPaths.cone A S) D hc hd none
  have hdeg := degree_apex_new A M
  rw [apex_eq_cone A M S hM,hM] at hdeg
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hstar hdeg
  rw [hdeg] at hstar
  have hf := Finset.card_filter_add_card_filter_not (s := D)
    (fun H => none ∈ H.verts)
  refine ⟨M,hm,hM,ham,E,hcE,hdE,?_⟩
  dsimp only [M] at hl ⊢
  omega

/-- Attainable avoiding-piece counts, with all graph and partition conditions
included. The set is nonempty under the hypotheses of the next theorem. -/
def feasibleCosts [Fintype V] (A : SimpleGraph V) (S : Set V) : Set ℕ :=
  {n | ∃ M : SimpleGraph V, IsMatching M ∧ M.support = S ∧
    Disjoint A.edgeSet M.edgeSet ∧ ∃ E : Finset (A ⊔ M).Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (A ⊔ M) E ∧ avoiding M E = n}

noncomputable def minimumAvoidance [Fintype V] (A : SimpleGraph V) (S : Set V) : ℕ :=
  sInf (feasibleCosts A S)

lemma feasibleCosts_nonempty [Fintype V] (A : SimpleGraph V) (S : Set V)
    (hind : ∀ x ∈ S, ∀ y ∈ S, ¬ A.Adj x y)
    (he : ∀ v, Even ((FanPaths.cone A S).degree v)) : (feasibleCosts A S).Nonempty := by
  obtain ⟨M,hm,hM,ham,E,hcE,hdE,hval⟩ := exists_objective_attainer A S hind he
  exact ⟨avoiding M E,M,hm,hM,ham,E,hcE,hdE,rfl⟩

/-- The exact minimization identity. This does not equate minimum avoiding
count with the avoiding count of a minimum TOTAL-size partition. -/
theorem number_eq_half_add_minimum [Fintype V] (A : SimpleGraph V) (S : Set V)
    (hind : ∀ x ∈ S, ∀ y ∈ S, ¬ A.Adj x y)
    (he : ∀ v, Even ((FanPaths.cone A S).degree v)) :
    cycleNumber (FanPaths.cone A S) = S.ncard / 2 + minimumAvoidance A S := by
  have hmem := Nat.sInf_mem (feasibleCosts_nonempty A S hind he)
  obtain ⟨M,hm,hM,ham,E,hcE,hdE,hval⟩ := hmem
  have hlo := number_le_objective A M S hm hM ham E hcE hdE
  obtain ⟨N,hn,hN,han,F,hcF,hdF,hnum⟩ := exists_objective_attainer A S hind he
  have hle := Nat.sInf_le (show avoiding N F ∈ feasibleCosts A S from
    ⟨N,hn,hN,han,F,hcF,hdF,rfl⟩)
  dsimp only [minimumAvoidance]
  omega

end Erdos184.MatchingObjective
