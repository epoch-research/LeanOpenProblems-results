import Submission.RankReduction
import Submission.Blocks

/-!
One-vertex separations of rank-critical graphs. These are necessary
structural conditions, not an exclusion of all counterexamples.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184
namespace RankBlocks
open RankCritical RankCriticalPartitions RankGlobalMinimal
variable {V : Type*} [Fintype V]

lemma rank_le_support_sub_one (G : SimpleGraph V) (hne : G ≠ ⊥) :
    graphRank G ≤ G.support.ncard - 1 := by
  obtain ⟨u,v,huv⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hne
  have hu : u ∈ G.support := ⟨v,huv⟩
  let f : Option {w : V // w ∉ G.support} → G.ConnectedComponent := fun x =>
    match x with
    | none => G.connectedComponentMk u
    | some w => G.connectedComponentMk w.val
  have hi : Function.Injective f := by
    intro x y hxy
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some w =>
        have hw : w.val ≠ u := fun h => w.property (h.symm ▸ hu)
        have hr : G.Reachable w.val u := (ConnectedComponent.exact hxy).symm
        exact (w.property (mem_support_of_reachable hw hr)).elim
    | some w =>
      cases y with
      | none =>
        have hw : w.val ≠ u := fun h => w.property (h.symm ▸ hu)
        exact (w.property (mem_support_of_reachable hw (ConnectedComponent.exact hxy))).elim
      | some z =>
        have hval : w.val = z.val := by
          by_contra hn
          exact w.property (mem_support_of_reachable hn (ConnectedComponent.exact hxy))
        exact congrArg some (Subtype.ext hval)
  have hh := Fintype.card_le_of_injective f hi
  rw [Fintype.card_option] at hh
  have hs := Set.ncard_add_ncard_compl G.support
  have hp := support_card_two_le G hne
  simp only [← Nat.card_eq_fintype_card] at hh
  change Nat.card (G.supportᶜ : Set V) + 1 ≤ Nat.card G.ConnectedComponent at hh
  rw [Nat.card_coe_set_eq] at hh
  unfold graphRank
  simp only [← Nat.card_eq_fintype_card]
  omega

lemma rank_sum_le_of_one_vertex_union {G A B : SimpleGraph V}
    (hc : G.Connected) (ha : A ≠ ⊥) (hb : B ≠ ⊥)
    (hcover : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (hover : (A.support ∩ B.support).ncard ≤ 1) :
    graphRank A + graphRank B ≤ graphRank G := by
  have hA := rank_le_support_sub_one A ha
  have hB := rank_le_support_sub_one B hb
  have hs := Set.ncard_union_add_ncard_inter A.support B.support
  rw [support_union_of_edge_cover hcover] at hs
  have hGA : 2 ≤ A.support.ncard := support_card_two_le A ha
  have hGB : 2 ≤ B.support.ncard := support_card_two_le B hb
  have hn := connected_rank hc
  have hsup := Set.ncard_le_ncard (Set.subset_univ G.support)
  simp only [Set.ncard_univ,Nat.card_eq_fintype_card] at hsup
  omega

lemma critical_no_one_vertex_split {C : ℕ} {G : SimpleGraph V}
    (hG : IsCritical C G) (hc : G.Connected) : ¬HasEvenOneVertexSplit G := by
  rintro ⟨A,B,hA,hB,ha,hb,hea,heb,hab,hcover,hover⟩
  have hltA := edge_card_lt_of_disjoint_nonempty hA hB hb hab
  have hltB := edge_card_lt_of_disjoint_nonempty hB hA ha hab.symm
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hltA hltB
  obtain ⟨DA,hca,hda,hba⟩ := hG.2.2 A hA hltA hea
  obtain ⟨DB,hcb,hdb,hbb⟩ := hG.2.2 B hB hltB heb
  obtain ⟨D,hdcy,hdd,hbd⟩ := combine_decompositions hA hB hab hcover DA DB
    (fun H hH => Or.inl ⟨(hca H hH).1,by
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hca H hH).2 v⟩)
    (fun H hH => Or.inl ⟨(hcb H hH).1,by
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hcb H hH).2 v⟩)
    hda hdb
  obtain ⟨E,hce,hde,hbe⟩ := refine_even_decomposition G hG.1 D hdcy hdd
  apply hG.2.1
  refine ⟨E,hce,hde,?_⟩
  have hsum := Nat.mul_le_mul_left C (rank_sum_le_of_one_vertex_union hc ha hb hcover hover)
  rw [Nat.mul_add] at hsum
  omega

/-- Retain only edges with both endpoints in a specified set, on the same
ambient vertex type. Vertices outside the set become isolated. -/
def sideGraph (G : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∈ S ∧ y ∈ S
  symm := by intro x y h; exact ⟨h.1.symm,h.2.2,h.2.1⟩
  loopless := by intro x h; exact h.1.ne rfl

lemma split_of_deleted_unreachable {G : SimpleGraph V}
    (hc : G.Connected) (he : ∀ x, Even (G.degree x))
    {v u w : V} (hu : u ≠ v) (hw : w ≠ v)
    (hn : ¬(G.deleteIncidenceSet v).Reachable u w) : HasEvenOneVertexSplit G := by
  let R := G.deleteIncidenceSet v
  let S : Set V := {x | x = v ∨ R.Reachable u x}
  let A := sideGraph G S
  let B := G \ A
  have hA : A ≤ G := fun _ _ h => h.1
  have hB : B ≤ G := sdiff_le
  have huS : u ∈ S := Or.inr (Reachable.refl _)
  have hwS : w ∉ S := by
    rintro (h | h)
    · exact hw h
    · exact hn h
  have hclosed {x y : V} (hx : x ∈ S) (hxv : x ≠ v) (hxy : G.Adj x y) : y ∈ S := by
    by_cases hyv : y = v
    · exact Or.inl hyv
    · right
      have hux : R.Reachable u x := hx.resolve_left hxv
      exact hux.trans (Adj.reachable (deleteIncidenceSet_adj.mpr ⟨hxy,hxv,hyv⟩))
  have ha : A ≠ ⊥ := by
    obtain ⟨x,hx⟩ := mem_support_of_reachable hu (hc.preconnected u v)
    intro hbot
    have hax : A.Adj u x := ⟨hx,huS,hclosed huS hu hx⟩
    simp only [hbot,bot_adj] at hax
  have hb : B ≠ ⊥ := by
    obtain ⟨x,hx⟩ := mem_support_of_reachable hw (hc.preconnected w v)
    intro hbot
    have hbx : B.Adj w x := ⟨hx,fun h => hwS h.2.1⟩
    simp only [hbot,bot_adj] at hbx
  have hab : Disjoint A.edgeSet B.edgeSet := by
    change Disjoint A.edgeSet (G \ A).edgeSet
    rw [SimpleGraph.edgeSet_sdiff]
    exact Set.disjoint_sdiff_right
  have hcover : A.edgeSet ∪ B.edgeSet = G.edgeSet := by
    change A.edgeSet ∪ (G \ A).edgeSet = G.edgeSet
    rw [SimpleGraph.edgeSet_sdiff]
    exact Set.union_diff_cancel (SimpleGraph.edgeSet_mono hA)
  have hover : (A.support ∩ B.support).ncard ≤ 1 := by
    apply Set.ncard_le_one_iff_subsingleton.mpr
    have honly : ∀ x ∈ A.support ∩ B.support, x = v := by
      intro x ⟨⟨a,ha⟩,⟨b,hb⟩⟩
      by_contra hxv
      have hxS : x ∈ S := ha.2.1
      exact hb.2 ⟨hb.1,hxS,hclosed hxS hxv hb.1⟩
    intro x hx y hy
    exact (honly x hx).trans (honly y hy).symm
  exact (hasEvenOneVertexSplit_iff G he).mpr ⟨A,B,hA,hB,ha,hb,hab,hcover,hover⟩

/-- Deleting any vertex of a connected rank-critical graph preserves
reachability between all other vertices. -/
lemma critical_delete_vertex_reachable {C : ℕ} {G : SimpleGraph V}
    (hG : IsCritical C G) (hc : G.Connected)
    {v u w : V} (hu : u ≠ v) (hw : w ≠ v) :
    (G.deleteIncidenceSet v).Reachable u w := by
  by_contra hn
  exact critical_no_one_vertex_split hG hc (split_of_deleted_unreachable hc hG.1 hu hw hn)

omit [Fintype V] in
lemma induce_reachable_of_deleted_reachable (G : SimpleGraph V) {v u w : V}
    (hu : u ≠ v) (hw : w ≠ v) (h : (G.deleteIncidenceSet v).Reachable u w) :
    (G.induce {x | x ≠ v}).Reachable ⟨u,hu⟩ ⟨w,hw⟩ := by
  obtain ⟨p⟩ := h
  have lift : ∀ {x y : V} (q : (G.deleteIncidenceSet v).Walk x y)
      (hx : x ≠ v) (hy : y ≠ v),
      (G.induce {x | x ≠ v}).Reachable ⟨x,hx⟩ ⟨y,hy⟩ := by
    intro x y q
    induction q with
    | nil => intro hx hy; exact Reachable.refl _
    | @cons x y z h q ih =>
      intro hx hy
      have hh := deleteIncidenceSet_adj.mp h
      have ha : (G.induce {x | x ≠ v}).Adj ⟨x,hx⟩ ⟨y,hh.2.2⟩ := hh.1
      exact ha.reachable.trans (ih hh.2.2 hy)
  exact lift p hu hw

lemma critical_induce_without_connected {C : ℕ} {G : SimpleGraph V}
    (hG : IsCritical C G) (hc : G.Connected) (v : V) :
    (G.induce {x | x ≠ v}).Connected := by
  have hp : (G.induce {x | x ≠ v}).Preconnected := by
    intro u w
    exact induce_reachable_of_deleted_reachable G u.property w.property
      (critical_delete_vertex_reachable hG hc u.property w.property)
  obtain ⟨a,b,hab⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hG.ne_bot
  have hn : Nonempty {x : V // x ≠ v} := by
    by_cases ha : a = v
    · exact ⟨⟨b,fun hb => hab.ne (ha.trans hb.symm)⟩⟩
    · exact ⟨⟨a,ha⟩⟩
  exact { preconnected := hp, nonempty := hn }

universe u
/-- The no-cut-vertex condition is available on an extracted counterexample,
not an additional assumption that has to be justified separately. -/
lemma exists_biconnected_critical {V : Type u} [Fintype V]
    (C : ℕ) (G : SimpleGraph V) (he : ∀ v, Even (G.degree v)) (hb : ¬HasBound C G) :
    ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W),
      IsLexMinimal C H ∧ IsCritical C H ∧ H.Connected ∧
      ¬HasEvenOneVertexSplit H ∧ ∀ v, (H.induce {x | x ≠ v}).Connected := by
  obtain ⟨W,instW,H,hmin,hcrit,hconn⟩ := exists_connected_critical C G he hb
  letI := instW
  exact ⟨W,instW,H,hmin,hcrit,hconn,critical_no_one_vertex_split hcrit hconn,
    critical_induce_without_connected hcrit hconn⟩

/-- A narrower sufficient structural statement. Its separating-packing
premise is still unproved, even with these necessary conditions. -/
lemma conjecture_of_biconnected_small_separating_packing (C : ℕ) (hC : 0 < C)
    (hsep : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
      G.Connected → (∀ v, (G.induce {x | x ≠ v}).Connected) →
      (∀ v, 2*(C+2) ≤ G.degree v) → G ≠ ⊥ →
      (∀ v, Even (G.degree v)) → MinimalCounterexample.AllCyclesOptimal G →
      ∃ P : Finset G.Subgraph,
        (∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
        Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet) ∧
        P.card ≤ C ∧ ¬(G \ unionPieces G P).Preconnected) :
    ∃ f : ℕ → ℝ,
      (f =O[Filter.atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  apply RankReduction.conjecture_of_no_connected_critical C
  intro V _ G ⟨hmin,hcrit,hconn⟩
  obtain ⟨P,hcy,hd,hb,hn⟩ := hsep G hconn
    (critical_induce_without_connected hcrit hconn)
    (hmin.1.degree_lower hC) hcrit.ne_bot hcrit.1 hcrit.allCyclesOptimal
  apply hn
  intro u v
  exact (hcrit.small_packing_reachable P hcy hd hb u v).mpr (hconn.preconnected u v)

end RankBlocks
end Erdos184
