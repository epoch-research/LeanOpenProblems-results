import Submission.DoublePetersenGraph
import Submission.CriticalSaturation

/-! Identifying only degree-two vertices can destroy cycle-criticality.
The dense quotient below has a three-cycle partition. This is an auxiliary
obstruction to a proposed transformation, not a disproof of Erdos 184. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.PetersenIdentification
open Critical EvenCore
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN edges"
def edges : List (Sym2 (Fin 25)) := [s(0,10), s(1,10), s(0,23), s(1,23), s(0,11), s(4,11), s(0,24), s(4,24), s(0,12), s(5,12), s(0,14), s(5,14), s(1,13), s(2,13), s(1,22), s(2,22), s(1,14), s(6,14), s(1,21), s(6,21), s(2,15), s(3,15), s(2,11), s(3,11), s(2,16), s(7,16), s(2,19), s(7,19), s(3,17), s(4,17), s(3,10), s(4,10), s(3,18), s(8,18), s(3,16), s(8,16), s(4,19), s(9,19), s(4,20), s(9,20), s(5,20), s(7,20), s(5,18), s(7,18), s(5,21), s(8,21), s(5,13), s(8,13), s(6,22), s(8,22), s(6,15), s(8,15), s(6,23), s(9,23), s(6,17), s(9,17), s(7,24), s(9,24), s(7,12), s(9,12)]

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN graph"
def graph : SimpleGraph (Fin 25) := SimpleGraph.fromEdgeSet {e | e ∈ edges}
instance : DecidableRel graph.Adj := by unfold graph; infer_instance

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN degree_table"
lemma degree_table (v : Fin 25) : graph.degree v = if v.val < 10 then 6 else 4 := by
  fin_cases v <;> decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN even"
lemma even (v : Fin 25) : Even (graph.degree v) := by
  rw [degree_table]
  split_ifs <;> decide
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN degree_zero"
lemma degree_zero : graph.degree 0 = 6 := by simpa using degree_table 0
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN degree_lower"
lemma degree_lower (v : Fin 25) : 4 ≤ graph.degree v := by
  rw [degree_table]
  split_ifs <;> omega
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN edge_finset"
lemma edge_finset : graph.edgeFinset = edges.toFinset := by
  have hn : ∀ a : Fin 25, s(a,a) ∉ edges := by decide +kernel
  ext e
  induction e using Sym2.ind with
  | h a b =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, graph,
      SimpleGraph.fromEdgeSet_adj, Set.mem_setOf_eq, List.mem_toFinset]
    exact ⟨And.left, fun h => ⟨h, fun he => hn a (he.symm ▸ h)⟩⟩

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN edge_card"
lemma edge_card : graph.edgeFinset.card = 60 := by
  have hn : edges.Nodup := by simp [edges, Sym2.eq_iff]
  rw [edge_finset, List.toFinset_card_of_nodup hn]
  rfl

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_0_10"
lemma adj_0_10 : graph.Adj 0 10 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_0_11"
lemma adj_0_11 : graph.Adj 0 11 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_0_12"
lemma adj_0_12 : graph.Adj 0 12 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_1_13"
lemma adj_1_13 : graph.Adj 1 13 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_1_14"
lemma adj_1_14 : graph.Adj 1 14 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_1_22"
lemma adj_1_22 : graph.Adj 1 22 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_1_23"
lemma adj_1_23 : graph.Adj 1 23 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_10_1"
lemma adj_10_1 : graph.Adj 10 1 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_10_3"
lemma adj_10_3 : graph.Adj 10 3 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_11_2"
lemma adj_11_2 : graph.Adj 11 2 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_11_3"
lemma adj_11_3 : graph.Adj 11 3 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_12_7"
lemma adj_12_7 : graph.Adj 12 7 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_12_9"
lemma adj_12_9 : graph.Adj 12 9 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_13_1"
lemma adj_13_1 : graph.Adj 13 1 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_13_2"
lemma adj_13_2 : graph.Adj 13 2 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_13_8"
lemma adj_13_8 : graph.Adj 13 8 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_14_0"
lemma adj_14_0 : graph.Adj 14 0 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_14_5"
lemma adj_14_5 : graph.Adj 14 5 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_15_6"
lemma adj_15_6 : graph.Adj 15 6 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_15_8"
lemma adj_15_8 : graph.Adj 15 8 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_16_2"
lemma adj_16_2 : graph.Adj 16 2 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_16_3"
lemma adj_16_3 : graph.Adj 16 3 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_17_4"
lemma adj_17_4 : graph.Adj 17 4 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_17_6"
lemma adj_17_6 : graph.Adj 17 6 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_18_5"
lemma adj_18_5 : graph.Adj 18 5 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_18_8"
lemma adj_18_8 : graph.Adj 18 8 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_19_7"
lemma adj_19_7 : graph.Adj 19 7 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_19_9"
lemma adj_19_9 : graph.Adj 19 9 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_2_13"
lemma adj_2_13 : graph.Adj 2 13 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_2_15"
lemma adj_2_15 : graph.Adj 2 15 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_2_19"
lemma adj_2_19 : graph.Adj 2 19 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_2_22"
lemma adj_2_22 : graph.Adj 2 22 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_20_4"
lemma adj_20_4 : graph.Adj 20 4 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_20_7"
lemma adj_20_7 : graph.Adj 20 7 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_21_1"
lemma adj_21_1 : graph.Adj 21 1 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_21_5"
lemma adj_21_5 : graph.Adj 21 5 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_22_1"
lemma adj_22_1 : graph.Adj 22 1 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_22_2"
lemma adj_22_2 : graph.Adj 22 2 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_22_6"
lemma adj_22_6 : graph.Adj 22 6 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_23_0"
lemma adj_23_0 : graph.Adj 23 0 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_23_9"
lemma adj_23_9 : graph.Adj 23 9 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_24_0"
lemma adj_24_0 : graph.Adj 24 0 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_24_4"
lemma adj_24_4 : graph.Adj 24 4 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_3_15"
lemma adj_3_15 : graph.Adj 3 15 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_3_17"
lemma adj_3_17 : graph.Adj 3 17 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_3_18"
lemma adj_3_18 : graph.Adj 3 18 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_4_10"
lemma adj_4_10 : graph.Adj 4 10 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_4_11"
lemma adj_4_11 : graph.Adj 4 11 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_4_19"
lemma adj_4_19 : graph.Adj 4 19 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_5_12"
lemma adj_5_12 : graph.Adj 5 12 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_5_13"
lemma adj_5_13 : graph.Adj 5 13 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_5_20"
lemma adj_5_20 : graph.Adj 5 20 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_6_14"
lemma adj_6_14 : graph.Adj 6 14 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_6_21"
lemma adj_6_21 : graph.Adj 6 21 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_6_23"
lemma adj_6_23 : graph.Adj 6 23 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_7_16"
lemma adj_7_16 : graph.Adj 7 16 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_7_18"
lemma adj_7_18 : graph.Adj 7 18 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_7_24"
lemma adj_7_24 : graph.Adj 7 24 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_8_16"
lemma adj_8_16 : graph.Adj 8 16 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_8_21"
lemma adj_8_21 : graph.Adj 8 21 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_8_22"
lemma adj_8_22 : graph.Adj 8 22 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_9_17"
lemma adj_9_17 : graph.Adj 9 17 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_9_20"
lemma adj_9_20 : graph.Adj 9 20 := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN adj_9_24"
lemma adj_9_24 : graph.Adj 9 24 := by decide +kernel

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN cycle0"
def cycle0 : graph.Walk 0 0 :=
  .cons adj_0_10 (.cons adj_10_1 (.cons adj_1_14 (.cons adj_14_5 (.cons adj_5_12 (.cons adj_12_7 (.cons adj_7_18 (.cons adj_18_8 (.cons adj_8_16 (.cons adj_16_2 (.cons adj_2_19 (.cons adj_19_9 (.cons adj_9_24 (.cons adj_24_4 (.cons adj_4_11 (.cons adj_11_3 (.cons adj_3_17 (.cons adj_17_6 (.cons adj_6_23 (.cons adj_23_0 (.nil))))))))))))))))))))
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN cycle0_cycle"
lemma cycle0_cycle : cycle0.IsCycle := by
  simp [cycle0, Walk.isCycle_def, Walk.isTrail_def]

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN cycle1"
def cycle1 : graph.Walk 0 0 :=
  .cons adj_0_11 (.cons adj_11_2 (.cons adj_2_13 (.cons adj_13_1 (.cons adj_1_23 (.cons adj_23_9 (.cons adj_9_17 (.cons adj_17_4 (.cons adj_4_10 (.cons adj_10_3 (.cons adj_3_15 (.cons adj_15_8 (.cons adj_8_22 (.cons adj_22_6 (.cons adj_6_21 (.cons adj_21_5 (.cons adj_5_20 (.cons adj_20_7 (.cons adj_7_24 (.cons adj_24_0 (.nil))))))))))))))))))))
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN cycle1_cycle"
lemma cycle1_cycle : cycle1.IsCycle := by
  simp [cycle1, Walk.isCycle_def, Walk.isTrail_def]

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN cycle2"
def cycle2 : graph.Walk 0 0 :=
  .cons adj_0_12 (.cons adj_12_9 (.cons adj_9_20 (.cons adj_20_4 (.cons adj_4_19 (.cons adj_19_7 (.cons adj_7_16 (.cons adj_16_3 (.cons adj_3_18 (.cons adj_18_5 (.cons adj_5_13 (.cons adj_13_8 (.cons adj_8_21 (.cons adj_21_1 (.cons adj_1_22 (.cons adj_22_2 (.cons adj_2_15 (.cons adj_15_6 (.cons adj_6_14 (.cons adj_14_0 (.nil))))))))))))))))))))
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN cycle2_cycle"
lemma cycle2_cycle : cycle2.IsCycle := by
  simp [cycle2, Walk.isCycle_def, Walk.isTrail_def]

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN number_upper"
lemma number_upper : number graph ≤ 3 := by
  let P : Fin 3 → graph.Subgraph := ![cycle0.toSubgraph,cycle1.toSubgraph,cycle2.toSubgraph]
  let E : Fin 3 → Finset (Sym2 (Fin 25)) := ![cycle0.edges.toFinset,cycle1.edges.toFinset,cycle2.edges.toFinset]
  have hp : ∀ i : Fin 3, IsCycleOrEdge (P i).coe := by
    intro i
    fin_cases i
    all_goals apply Or.inl
    · simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using cycle_coe_regular graph cycle0_cycle
    · simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using cycle_coe_regular graph cycle1_cycle
    · simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using cycle_coe_regular graph cycle2_cycle
  have hd : IsDecomposition graph (Finset.univ.image P) := by
    apply Compression.finite_family_decomposition P E
    · intro i
      fin_cases i <;> ext e <;> simp [P,E]
    · intro i j hne
      fin_cases i <;> fin_cases j <;>
        first | exact (hne rfl).elim |
          simp [E, List.disjoint_toFinset_iff_disjoint, cycle0, cycle1, cycle2, Sym2.eq_iff]
    · intro a b
      change graph.Adj a b ↔ ∃ i : Fin 3, s(a,b) ∈ E i
      simp only [Fin.exists_fin_succ, E, List.mem_toFinset]
      revert a b
      decide +kernel
  have hb := number_le (Finset.univ.image P) (by
    intro H hH
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
    exact hp i) hd
  have hn : (Finset.univ.image P).card ≤ 3 :=
    (Finset.card_image_le).trans (by simp)
  omega

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN number_three"
lemma number_three : number graph = 3 := by
  have hb := StarCore.number_degree_bound graph 0
  have hd := degree_zero
  have hu := number_upper
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hb hd
  omega

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN square"
def square : graph.Walk 1 1 :=
  .cons adj_1_13 (.cons adj_13_2 (.cons adj_2_22 (.cons adj_22_1 (.nil))))
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN square_cycle"
lemma square_cycle : square.IsCycle := by
  simp [square, Walk.isCycle_def, Walk.isTrail_def]

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN not_critical"
lemma not_critical : ¬ CycleCritical graph := by
  intro hc
  have hh := CriticalSaturation.cycle_hits_saturated hc 0 (by rw [degree_zero,number_three])
  have hs := hh 1 square square_cycle
  have hn : (0 : Fin 25) ∉ square.support := by decide +kernel
  exact hn hs

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN not_minimal"
lemma not_minimal : ¬ EvenMinimal graph :=
  fun h => not_critical (h.cycleCritical even)

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN quotient"
def quotient : DoublePetersenGraph.Vertex → Fin 25
  | .inl v => ⟨v.val, by omega⟩
  | .inr (e,b) => if b then ![23,24,14,22,21,11,19,10,16,20,18,13,15,17,12] e else ⟨10 + e.val, by omega⟩

instance : DecidableRel DoublePetersenGraph.graph.Adj := by
  unfold DoublePetersenGraph.graph
  infer_instance

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN quotient_surjective"
lemma quotient_surjective : Function.Surjective quotient := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN quotient_hom"
lemma quotient_hom : ∀ x y, DoublePetersenGraph.graph.Adj x y →
    graph.Adj (quotient x) (quotient y) := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN quotient_edge_surjective"
lemma quotient_edge_surjective : ∀ a b, graph.Adj a b →
    ∃ x y, DoublePetersenGraph.graph.Adj x y ∧ quotient x = a ∧ quotient y = b := by
  decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN private_degree"
lemma private_degree : ∀ e : DoublePetersen.Edge,
    DoublePetersenGraph.graph.degree (.inr e) = 2 := by
  rintro ⟨e,b⟩
  fin_cases e <;> cases b <;> decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN identified_private"
lemma identified_private : ∀ x y, quotient x = quotient y → x ≠ y →
    (∃ e, x = Sum.inr e) ∧ (∃ e, y = Sum.inr e) := by decide +kernel
run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN identified_degree_two"
lemma identified_degree_two (x y : DoublePetersenGraph.Vertex)
    (h : quotient x = quotient y) (hne : x ≠ y) :
    DoublePetersenGraph.graph.degree x = 2 ∧ DoublePetersenGraph.graph.degree y = 2 := by
  obtain ⟨⟨e,rfl⟩,⟨f,rfl⟩⟩ := identified_private x y h hne
  exact ⟨private_degree e,private_degree f⟩

run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/PetersenIdentification-progress" "BEGIN obstruction"
lemma obstruction :
    CycleCritical DoublePetersenGraph.graph ∧
    number DoublePetersenGraph.graph = 5 ∧
    (∀ v, Even (graph.degree v)) ∧
    (∀ v, 4 ≤ graph.degree v) ∧
    graph.edgeFinset.card = 60 ∧
    number graph = 3 ∧ ¬ CycleCritical graph :=
  ⟨DoublePetersenGraph.cycle_critical,DoublePetersenGraph.number_eq_five,
    even,degree_lower,edge_card,number_three,not_critical⟩

#print axioms obstruction
#print axioms quotient_hom
#print axioms quotient_edge_surjective
#print axioms identified_degree_two
end Erdos184Work.PetersenIdentification
