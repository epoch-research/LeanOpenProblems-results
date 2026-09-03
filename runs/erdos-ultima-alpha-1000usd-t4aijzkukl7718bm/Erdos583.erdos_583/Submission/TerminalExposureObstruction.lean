import Submission.TerminalCopyBounds

/-! A structural obstruction to maximum-terminal-weight exposure.
This concerns a stronger auxiliary claim, not the Gallai conjecture. -/
namespace Erdos583TerminalExposureObstructionDevelopment
open SimpleGraph Erdos583Work Erdos583Work.MatchingTrim
open Erdos583TerminalCapacityDevelopment Erdos583TerminalCopyBoundsDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384

/-- K7 minus the triangle on the last three vertices. -/
def core : SimpleGraph (Fin 7) where
  Adj x y := x ≠ y ∧ (x.val < 4 ∨ y.val < 4)
  symm := by intro x y h; exact ⟨h.1.symm,h.2.symm⟩
  loopless := by intro x h; exact h.1 rfl
instance : DecidableRel core.Adj := fun x y ↦
  inferInstanceAs (Decidable (x ≠ y ∧ (x.val < 4 ∨ y.val < 4)))

abbrev N := pairedCopies core ∅
abbrev J := pairedCopies core {6}
abbrev H := pairedCopies core Set.univ
instance (S : Set (Fin 7)) [DecidablePred (· ∈ S)] : DecidableRel (pairedCopies core S).Adj :=
  fun x y ↦ inferInstanceAs (Decidable
    ((x.1=y.1 ∧ core.Adj x.2 y.2) ∨ (x.1≠y.1 ∧ x.2=y.2 ∧ x.2 ∈ S)))

/-- All vertical edges. -/
abbrev M := H \ N
/-- All but the last vertical edge. -/
abbrev F := H \ J

lemma core_edge_card : core.edgeSet.ncard=18 := by
  have h : core.edgeFinset.card=18 := by decide
  simpa only [←Set.ncard_coe_finset,coe_edgeFinset] using h

lemma core_degree_four : core.degree 4=4 := by decide

lemma structural :
    (∀ v, Odd (H.degree v)) ∧ F ≤ H ∧
    (∀ v, (F.neighborSet v).Subsingleton) ∧
    TriangleFreeMatching.TriangleFreeEdges H F ∧ (H \ F).Connected := by
  refine ⟨by decide,sdiff_le,pairedCopies_sdiff_matching core Set.univ {6},?_,?_⟩
  · exact TriangleFreeMatching.pairedCopies_difference_triangleFree core Set.univ {6}
  · have hJH : J ≤ H := pairedCopies_mono core (Set.subset_univ _)
    rw [sdiff_sdiff_eq_self hJH]
    apply pairedCopies_connected core (by decide) {6}
    exact ⟨6,rfl⟩

lemma M_le : M ≤ H := sdiff_le
lemma M_matching : ∀ v, (M.neighborSet v).Subsingleton :=
  pairedCopies_sdiff_matching core Set.univ ∅
lemma F_le_M : F ≤ M := by
  intro x y h
  exact ⟨h.1,fun hn ↦ h.2 ((pairedCopies_mono core (Set.empty_subset _)) hn)⟩
lemma delete_M : H \ M=N := sdiff_sdiff_eq_self (pairedCopies_mono core (Set.empty_subset _))
lemma M_card : M.edgeSet.ncard=7 := by
  have h := Set.ncard_diff_add_ncard_of_subset
    (edgeSet_mono (pairedCopies_mono core (Set.empty_subset (Set.univ : Set (Fin 7)))))
  rw [←edgeSet_sdiff] at h
  change M.edgeSet.ncard+N.edgeSet.ncard=H.edgeSet.ncard at h
  simp only [N,H,GlobalCritical.pairedCopies_edge_ncard,Set.ncard_empty,
    Set.ncard_univ,Nat.card_eq_fintype_card,Fintype.card_fin] at h
  omega
lemma F_card : F.edgeSet.ncard=6 := by
  have h := Set.ncard_diff_add_ncard_of_subset
    (edgeSet_mono (pairedCopies_mono core (Set.subset_univ ({6} : Set (Fin 7)))))
  rw [←edgeSet_sdiff] at h
  change F.edgeSet.ncard+J.edgeSet.ncard=H.edgeSet.ncard at h
  simp only [J,H,GlobalCritical.pairedCopies_edge_ncard,Set.ncard_singleton,
    Set.ncard_univ,Nat.card_eq_fintype_card,Fintype.card_fin] at h
  omega

lemma core_lower_bound {D : Finset core.Subgraph} (hD : GoodDecomposition core D) :
    3 ≤ D.card := by
  have h := GoodDecomposition.card_edges_le hD
  rw [core_edge_card] at h
  simp only [Fintype.card_fin] at h
  omega

lemma inactive_peripheral_core_lower_bound {D : Finset core.Subgraph}
    (hD : GoodDecomposition core D) (hne : ∀ K ∈ D, K.edgeSet.Nonempty)
    (hv : endpointMultiplicity D 4=0) : 4 ≤ D.card := by
  have h := edge_capacity_at_vertex hD hne 4
  rw [core_edge_card,core_degree_four,hv] at h
  simp only [Fintype.card_fin] at h
  omega

lemma normal_endpoints {D : Finset H.Subgraph} (hD : GoodDecomposition H D)
    (hne : ∀ K ∈ D, K.edgeSet.Nonempty) (hcard : D.card=7) (v : Bool × Fin 7) :
    endpointMultiplicity D v=1 := by
  have hc : 2*D.card=Fintype.card {v : Bool × Fin 7 // Odd (H.degree v)} := by
    rw [hcard]
    have hodd : ∀ v, Odd (H.degree v) := structural.1
    simp [Fintype.card_subtype,hodd]
  have h := GoodDecomposition.endpointMultiplicity_of_exact_card hD hne hc v
  simpa only [if_pos (structural.1 v)] using h

lemma terminal_weight_le_eight {D : Finset H.Subgraph}
    (hD : GoodDecomposition H D) (hne : ∀ K ∈ D, K.edgeSet.Nonempty) (hcard : D.card=7) :
    terminalWeight D F ≤ 8 := by
  have hb := terminal_weight_copy_lower_bound M_le M_matching delete_M hD hne 3
    (fun _ hE ↦ core_lower_bound hE)
  have hm := terminalWeight_mono F_le_M D
  rw [M_card,hcard] at hb
  omega

/-- If the peripheral marked edge is terminal at either endpoint, the
maximum possible total weight drops from eight to at most seven. -/
lemma exposed_peripheral_weight_le_seven {D : Finset H.Subgraph}
    (hD : GoodDecomposition H D) (hne : ∀ K ∈ D, K.edgeSet.Nonempty) (hcard : D.card=7)
    (b : Bool) (ht : ∃ K ∈ D, (b,4) ∈ terminalVertices K F) :
    terminalWeight D F ≤ 7 := by
  have hterminal : ∃ K ∈ D, (b,4) ∈ terminalVertices K M := by
    obtain ⟨K,hK,ht⟩ := ht
    exact ⟨K,hK,terminalVertices_mono F_le_M K ht⟩
  have hex := trim_decomposition_exact M_le M_matching hD hne
  rw [delete_M] at hex
  obtain ⟨E,hE,hneE,hcardE,hendsE⟩ := hex
  have hz := hendsE (b,4) (normal_endpoints hD hne hcard _) hterminal
  obtain ⟨B,hB,hneB,hBc,hzero⟩ := decompose_both_copies hE hneE
  have hleft := core_lower_bound (hB false)
  have hright := core_lower_bound (hB true)
  have hstrict := inactive_peripheral_core_lower_bound (hB b) (hneB b) (hzero b 4 hz)
  have hEc : 7 ≤ E.card := by cases b <;> omega
  have hm := terminalWeight_mono F_le_M D
  rw [hcard,M_card] at hcardE
  omega

def p0 : H.Walk (false,0) (true,0) :=
  (.cons (by decide : H.Adj (false,0) (true,0)) .nil)

def p1 : H.Walk (false,1) (true,1) :=
  (.cons (by decide : H.Adj (false,1) (true,1)) .nil)

def p2 : H.Walk (false,2) (true,2) :=
  (.cons (by decide : H.Adj (false,2) (true,2)) .nil)

def p3 : H.Walk (false,3) (true,3) :=
  (.cons (by decide : H.Adj (false,3) (true,3)) .nil)

def p4 : H.Walk (false,6) (true,6) :=
  (.cons (by decide : H.Adj (false,6) (false,3)) (.cons (by decide : H.Adj (false,3) (false,5)) (.cons (by decide : H.Adj (false,5) (false,2)) (.cons (by decide : H.Adj (false,2) (false,1)) (.cons (by decide : H.Adj (false,1) (false,0)) (.cons (by decide : H.Adj (false,0) (false,4)) (.cons (by decide : H.Adj (false,4) (true,4)) (.cons (by decide : H.Adj (true,4) (true,0)) (.cons (by decide : H.Adj (true,0) (true,1)) (.cons (by decide : H.Adj (true,1) (true,2)) (.cons (by decide : H.Adj (true,2) (true,5)) (.cons (by decide : H.Adj (true,5) (true,3)) (.cons (by decide : H.Adj (true,3) (true,6)) .nil)))))))))))))

def p5 : H.Walk (false,4) (true,4) :=
  (.cons (by decide : H.Adj (false,4) (false,3)) (.cons (by decide : H.Adj (false,3) (false,1)) (.cons (by decide : H.Adj (false,1) (false,6)) (.cons (by decide : H.Adj (false,6) (false,2)) (.cons (by decide : H.Adj (false,2) (false,0)) (.cons (by decide : H.Adj (false,0) (false,5)) (.cons (by decide : H.Adj (false,5) (true,5)) (.cons (by decide : H.Adj (true,5) (true,0)) (.cons (by decide : H.Adj (true,0) (true,2)) (.cons (by decide : H.Adj (true,2) (true,6)) (.cons (by decide : H.Adj (true,6) (true,1)) (.cons (by decide : H.Adj (true,1) (true,3)) (.cons (by decide : H.Adj (true,3) (true,4)) .nil)))))))))))))

def p6 : H.Walk (false,5) (true,5) :=
  (.cons (by decide : H.Adj (false,5) (false,1)) (.cons (by decide : H.Adj (false,1) (false,4)) (.cons (by decide : H.Adj (false,4) (false,2)) (.cons (by decide : H.Adj (false,2) (false,3)) (.cons (by decide : H.Adj (false,3) (false,0)) (.cons (by decide : H.Adj (false,0) (false,6)) (.cons (by decide : H.Adj (false,6) (true,6)) (.cons (by decide : H.Adj (true,6) (true,0)) (.cons (by decide : H.Adj (true,0) (true,3)) (.cons (by decide : H.Adj (true,3) (true,2)) (.cons (by decide : H.Adj (true,2) (true,4)) (.cons (by decide : H.Adj (true,4) (true,1)) (.cons (by decide : H.Adj (true,1) (true,5)) .nil)))))))))))))

abbrev starts : Fin 7 → Bool × Fin 7 := ![(false,0),(false,1),(false,2),(false,3),(false,6),(false,4),(false,5)]
abbrev finishes : Fin 7 → Bool × Fin 7 := ![(true,0),(true,1),(true,2),(true,3),(true,6),(true,4),(true,5)]
def walks : ∀ i, H.Walk (starts i) (finishes i) :=
  (Fin.cases p0 (Fin.cases p1 (Fin.cases p2 (Fin.cases p3 (Fin.cases p4 (Fin.cases p5 (Fin.cases p6 (fun i ↦ Fin.elim0 i))))))))

lemma walks_isPath : ∀ i, (walks i).IsPath := by
  intro i
  simp only [Walk.isPath_def]
  revert i
  decide

def optimum : NormalTrailSystem H 7 where
  start := starts
  finish := finishes
  walk := walks
  isTrail := fun i ↦ (walks_isPath i).isTrail
  endpoint_bijective := by decide
  disjoint := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro e he hf
    simp only [Walk.mem_edges_toSubgraph] at he hf
    have hd : ∀ i j : Fin 7, i ≠ j → ∀ e : Sym2 (Bool × Fin 7),
        e ∈ (walks i).edges → e ∉ (walks j).edges := by decide
    exact hd i j hij e he hf
  cover := by
    intro e
    induction e using Sym2.ind with
    | h a b =>
      simp only [mem_edgeSet,Walk.mem_edges_toSubgraph]
      revert a b
      decide

lemma optimum_good : GoodDecomposition H optimum.parts := by
  refine ⟨?_,optimum.parts_decomposition⟩
  intro K hK
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hK
  exact ⟨_,_,_,walks_isPath i,rfl⟩

lemma optimum_nonempty : ∀ K ∈ optimum.parts, K.edgeSet.Nonempty := by
  intro K hK
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hK
  exact ⟨s(optimum.start i,(optimum.walk i).snd),
    (optimum.walk i).toSubgraph_adj_snd (Walk.not_nil_of_ne (optimum.endpoints_ne i))⟩

lemma optimum_card : optimum.parts.card=7 := by
  rw [NormalTrailSystem.parts,Finset.card_image_of_injective _ optimum.subgraph_injective]
  simp

lemma optimum_terminal_vertices (i : Fin 7) :
    terminalVertices (optimum.walk i).toSubgraph F =
      if i.val < 4 then {(false,i),(true,i)} else ∅ := by
  ext x
  simp only [terminalVertices,Finset.mem_filter,Finset.mem_univ,true_and,
    Subgraph.neighborSet,neighborSet,inf_adj,Subgraph.spanningCoe_adj,
    Walk.adj_toSubgraph_iff_mem_edges,Set.ncard_eq_toFinset_card',Set.toFinset_setOf]
  revert i x
  decide

lemma optimum_weight : terminalWeight optimum.parts F=8 := by
  have hs : terminalWeight optimum.parts F=
      ∑ i, (terminalVertices (optimum.walk i).toSubgraph F).card := by
    unfold terminalWeight NormalTrailSystem.parts
    rw [Finset.sum_image]
    intro i _ j _ heq
    exact optimum.subgraph_injective heq
  rw [hs]
  simp only [optimum_terminal_vertices]
  decide

/-- There is an optimum of weight eight, but every optimum leaves the
marked edge at coordinate four internal at both endpoints. -/
lemma optimum_has_unexposable_marked_edge :
    (∃ D : Finset H.Subgraph, GoodDecomposition H D ∧
      (∀ K ∈ D, K.edgeSet.Nonempty) ∧ D.card=7 ∧ terminalWeight D F=8) ∧
    ∀ D : Finset H.Subgraph, GoodDecomposition H D →
      (∀ K ∈ D, K.edgeSet.Nonempty) → D.card=7 → terminalWeight D F=8 →
      ∀ b, ¬∃ K ∈ D, (b,4) ∈ terminalVertices K F := by
  refine ⟨⟨optimum.parts,optimum_good,optimum_nonempty,optimum_card,optimum_weight⟩,?_⟩
  intro D hD hne hcard hw b ht
  have h := exposed_peripheral_weight_le_seven hD hne hcard b ht
  omega

lemma peripheral_edge_marked : F.Adj (false,4) (true,4) := by
  change H.Adj (false,4) (true,4) ∧ ¬J.Adj (false,4) (true,4)
  decide

/-- Explicit negation of the auxiliary maximum-weight exposure assertion
for this graph and this marked edge. It is not a disproof of erdos_583. -/
theorem maximum_weight_exposure_false :
    ¬∃ D : Finset H.Subgraph, GoodDecomposition H D ∧
      (∀ K ∈ D, K.edgeSet.Nonempty) ∧ D.card=7 ∧
      (∀ E : Finset H.Subgraph, GoodDecomposition H E →
        (∀ K ∈ E, K.edgeSet.Nonempty) → E.card=7 → terminalWeight E F ≤ terminalWeight D F) ∧
      ∃ b, ∃ K ∈ D, (b,4) ∈ terminalVertices K F := by
  rintro ⟨D,hD,hne,hcard,hmax,b,ht⟩
  have hlo := hmax optimum.parts optimum_good optimum_nonempty optimum_card
  rw [optimum_weight] at hlo
  have hhi := exposed_peripheral_weight_le_seven hD hne hcard b ht
  omega

end Erdos583TerminalExposureObstructionDevelopment
