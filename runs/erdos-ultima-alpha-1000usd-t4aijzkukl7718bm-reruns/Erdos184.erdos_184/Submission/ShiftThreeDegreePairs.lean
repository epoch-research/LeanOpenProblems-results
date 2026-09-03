import Submission.ShiftThreePackingConnectivity
import Submission.CycleThroughTwo

/-!
Small-packing resilience allows repeated cycles through any two vertices.
Combining this with the vertex-deletion budget strengthens degree-sum bounds.
These are necessary conditions, not a settlement of the conjecture.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.ShiftThreeCritical
open ExactVertexSmoothing StarElimination MinimalCounterexample
universe u
set_option maxHeartbeats 800000

/-- Repeatedly use the two-vertex cycle theorem in the residual. No assertion
that this prescribed packing extends to an optimum is needed. -/
lemma IsVertexMinimal.packing_through_pair {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G) (hC : 6 ≤ C)
    {u v : V} (huv : u ≠ v) :
    ∃ P : Finset G.Subgraph,
      (∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet) ∧
      (∀ H ∈ P, u ∈ H.verts ∧ v ∈ H.verts) ∧ P.card = C+1 := by
  have hex : ∀ n : ℕ, n ≤ C+1 →
      ∃ P : Finset G.Subgraph,
        (∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
        Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet) ∧
        (∀ H ∈ P, u ∈ H.verts ∧ v ∈ H.verts) ∧ P.card = n := by
    intro n
    induction n with
    | zero => exact fun _ => ⟨∅,by simp,by simp,by simp,by simp⟩
    | succ n ih =>
      intro hn
      obtain ⟨P,hc,hd,hvert,hcard⟩ := ih (by omega)
      have hp : P.card ≤ C := by omega
      let R := G \ unionPieces G P
      obtain ⟨H,hH,huH,hvH⟩ := CycleThroughTwo.cycle_through_pair (G := R) huv
        (by
          have hh := hG.small_packing_degree_lower hC P hc hd hp u
          simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh ⊢
          exact (by omega : 2 ≤ Nat.card ((G \ unionPieces G P).neighborSet u)))
        (by
          intro S hS a b
          exact hG.small_packing_induce_compl_reachable hC P hc hd hp S (by omega) a b)
      let J : G.Subgraph := promote (show R ≤ G from sdiff_le) H
      have hcJ : J.coe.Connected ∧ J.coe.IsRegularOfDegree 2 := by
        refine ⟨hH.1,?_⟩
        intro x
        simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hH.2 x
      have hdis : ∀ K ∈ P, Disjoint J.edgeSet K.edgeSet := by
        intro K hK
        apply Set.disjoint_left.mpr
        intro e heJ heK
        have heR : e ∈ R.edgeSet := H.edgeSet_subset heJ
        simp only [R,edgeSet_sdiff] at heR
        apply heR.2
        rw [unionPieces_edgeSet]
        exact Set.mem_iUnion₂.mpr ⟨K,hK,heK⟩
      have hnot : J ∉ P := by
        intro hJ
        obtain ⟨e,he⟩ := cycle_edgeSet_nonempty J hcJ.1 hcJ.2
        exact Set.disjoint_left.mp (hdis J hJ) he he
      refine ⟨insert J P,?_,?_,?_,by rw [Finset.card_insert_of_notMem hnot,hcard]⟩
      · intro K hK
        rcases Finset.mem_insert.mp hK with rfl | hK
        · exact hcJ
        · exact hc K hK
      · rw [Finset.coe_insert]
        exact hd.insert (fun K hK _ => hdis K hK)
      · intro K hK
        rcases Finset.mem_insert.mp hK with rfl | hK
        · exact ⟨huH,hvH⟩
        · exact hvert K hK
  exact hex (C+1) le_rfl

/-- A nonempty small vertex set meets strictly more than C times its size
many pieces of every decomposition. The explicit order condition handles
the small-order exception in `charge`. -/
lemma IsVertexMinimal.touching_card {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G) (hC : 6 ≤ C)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (S : Finset V) (hne : S.Nonempty)
    (hsmall : S.card + 4 ≤ Fintype.card V) : C * S.card < (touching D S).card := by
  have hs : (S : Set V) ⊆ G.support := by
    intro x _
    apply G.degree_pos_iff_mem_support x |>.mp
    have hh := hG.degree_lower hC x
    omega
  have hloss := touching_support_loss D hc hd S hs
  have hsG : G.support.ncard ≤ Fintype.card V := by
    simpa using Set.ncard_le_ncard (Set.subset_univ G.support)
  have hpos := Finset.card_pos.mpr hne
  let P := touching D S
  let R := G \ unionPieces G P
  have hlt : R.support.ncard < Fintype.card V := by
    change (G \ unionPieces G (touching D S)).support.ncard < _
    omega
  have hcP : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 :=
    fun H hH => hc H (touching_subset D S hH)
  have hdP : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet) :=
    fun H hH K hK hne => hd.1 (touching_subset D S hH) (touching_subset D S hK) hne
  obtain ⟨E,hcE,hdE,hbE⟩ := hG.bound_on_smaller_support R hlt (by
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using even_residual_of_cycle_packing G hG.1 P hcP hdP x)
  obtain ⟨F,hcF,hdF,hbF⟩ := complete_cycle_packing G P hcP hdP E (by
    intro H hH
    refine ⟨(hcE H hH).1,?_⟩
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hcE H hH).2 x) hdE
  have hcharge : S.card + charge R.support.ncard ≤ charge (Fintype.card V) := by
    have hh : R.support.ncard + S.card ≤ Fintype.card V := hloss.trans hsG
    unfold charge
    omega
  have hbudget := Nat.mul_le_mul_left C hcharge
  rw [Nat.mul_add] at hbudget
  by_contra! hbP
  apply hG.2.1
  exact ⟨F,hcF,hdF,by change (touching D S).card + E.card ≥ F.card at hbF; omega⟩

/-- A packing through both vertices saves one incident piece per common cycle.
Strict vertex deletion therefore imposes this exact degree-sum inequality. -/
lemma IsVertexMinimal.pair_packing_degree_budget {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G) (hC : 6 ≤ C)
    {u v : V} (huv : u ≠ v) (P : Finset G.Subgraph)
    (hcP : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdP : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    (hvert : ∀ H ∈ P, u ∈ H.verts ∧ v ∈ H.verts) :
    2 * P.card + 4 * C + 2 ≤ G.degree u + G.degree v := by
  obtain ⟨E,hcE,hdE⟩ := even_cycle_decomposition (G \ unionPieces G P) (by
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using even_residual_of_cycle_packing G hG.1 P hcP hdP x)
  obtain ⟨D,hc,hd,hPD,_⟩ := complete_cycle_packing_extension G P hcP hdP E (by
    intro H hH
    refine ⟨(hcE H hH).1,?_⟩
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hcE H hH).2 x) hdE
  have hdeg := hG.degree_lower hC u
  have hn := G.degree_lt_card_verts u
  have ht := hG.touching_card hC D hc hd {u,v} (Finset.insert_nonempty _ _) (by
    rw [Finset.card_pair huv]
    omega)
  simp only [touching,Finset.biUnion_insert,Finset.singleton_biUnion,Finset.card_pair huv] at ht
  have hdu := star_card D hc hd u
  have hdv := star_card D hc hd v
  have hi := Finset.card_union_add_card_inter (star D u) (star D v)
  have hsub : P ⊆ star D u ∩ star D v := by
    intro H hH
    exact Finset.mem_inter.mpr ⟨(mem_star D u H).mpr ⟨hPD hH,(hvert H hH).1⟩,
      (mem_star D v H).mpr ⟨hPD hH,(hvert H hH).2⟩⟩
  have hcard := Finset.card_le_card hsub
  omega

lemma IsVertexMinimal.degree_sum_lower {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G) (hC : 6 ≤ C)
    {u v : V} (huv : u ≠ v) : 6*C+4 ≤ G.degree u + G.degree v := by
  obtain ⟨P,hc,hd,hv,hcard⟩ := hG.packing_through_pair hC huv
  have hh := hG.pair_packing_degree_budget hC huv P hc hd hv
  omega

/-- At most one vertex can lie below this stronger degree threshold. -/
lemma IsVertexMinimal.low_degree_subsingleton {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G) (hC : 6 ≤ C) :
    {v : V | G.degree v < 3*C+2}.Subsingleton := by
  intro u hu v hv
  by_contra hn
  have hh := hG.degree_sum_lower hC hn
  change G.degree u < 3*C+2 at hu
  change G.degree v < 3*C+2 at hv
  omega

/-- At most one vertex attains the previously proved degree lower bound. -/
lemma IsVertexMinimal.degree_lower_attainment_unique {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G) (hC : 6 ≤ C)
    {u v : V} (hu : G.degree u = 2*(C+2)) (hv : G.degree v = 2*(C+2)) : u = v := by
  apply hG.low_degree_subsingleton hC
  · change G.degree u < 3*C+2
    omega
  · change G.degree v < 3*C+2
    omega

end Erdos184.ShiftThreeCritical
