import Submission.ShiftThreeDegreePairs

/-!
The incidence saving from a cycle packing through an arbitrary vertex set.
Packing existence is a separate issue; no such existence is assumed implicitly.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184

lemma common_biUnion_card {I J : Type*} (S : Finset I) (F : I → Finset J)
    (P : Finset J) (hS : S.Nonempty) (hP : ∀ i ∈ S, P ⊆ F i) :
    (S.biUnion F).card + (S.card-1)*P.card ≤ ∑ i ∈ S, (F i).card := by
  have hpU : P ⊆ S.biUnion F := by
    obtain ⟨i,hi⟩ := hS
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨i,hi,hP i hi hx⟩
  have hdiff : S.biUnion (fun i => F i \ P) = S.biUnion F \ P := by
    ext x
    simp only [Finset.mem_biUnion,Finset.mem_sdiff]
    aesop
  have hsum : (∑ i ∈ S, (F i \ P).card) + S.card*P.card = ∑ i ∈ S, (F i).card := by
    calc
      _ = ∑ i ∈ S, ((F i \ P).card + P.card) := by
        rw [Finset.sum_add_distrib]
        simp
      _ = _ := Finset.sum_congr rfl (fun i hi => Finset.card_sdiff_add_card_eq_card (hP i hi))
  have hU := Finset.card_sdiff_add_card_eq_card hpU
  have hle := Finset.card_biUnion_le (s := S) (t := fun i => F i \ P)
  rw [hdiff] at hle
  have hpos := Finset.card_pos.mpr hS
  have hmul : S.card*P.card = (S.card-1)*P.card+P.card := by
    have hh : S.card = (S.card-1)+1 := by omega
    conv_lhs => rw [hh]
    ring
  omega

namespace ShiftThreeCritical
open ExactVertexSmoothing StarElimination MinimalCounterexample
universe u
set_option maxHeartbeats 800000

/-- Every common cycle saves one incident-piece charge at each selected vertex
beyond the first. An arbitrary packing may be completed, not necessarily
optimally; criticality is applied to all decompositions. -/
lemma IsVertexMinimal.common_packing_degree_budget {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G) (hC : 6 ≤ C)
    (S : Finset V) (hS : S.Nonempty) (hsmall : S.card+4 ≤ Fintype.card V)
    (P : Finset G.Subgraph)
    (hcP : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdP : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    (hvert : ∀ H ∈ P, ∀ v ∈ S, v ∈ H.verts) :
    2*((S.card-1)*P.card+C*S.card+1) ≤ ∑ v ∈ S, G.degree v := by
  obtain ⟨E,hcE,hdE⟩ := even_cycle_decomposition (G \ unionPieces G P) (by
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using even_residual_of_cycle_packing G hG.1 P hcP hdP x)
  obtain ⟨D,hc,hd,hPD,_⟩ := complete_cycle_packing_extension G P hcP hdP E (by
    intro H hH
    refine ⟨(hcE H hH).1,?_⟩
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using (hcE H hH).2 x) hdE
  have hcommon := common_biUnion_card S (star D) P hS (by
    intro v hv H hH
    exact (mem_star D v H).mpr ⟨hPD hH,hvert H hH v hv⟩)
  have htouch := hG.touching_card hC D hc hd S hS hsmall
  have hsum : 2*(∑ v ∈ S, (star D v).card) = ∑ v ∈ S, G.degree v := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun v _ => star_card D hc hd v)
  change C*S.card < (S.biUnion (star D)).card at htouch
  omega

end ShiftThreeCritical
end Erdos184
