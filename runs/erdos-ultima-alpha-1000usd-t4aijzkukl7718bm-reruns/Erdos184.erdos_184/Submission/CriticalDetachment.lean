import Submission.EvenCycleFactorization
import Submission.LowCountCritical

/-! An explicit count-critical graph whose cycle count drops after an even
vertex detachment, despite a minimum partition lifting through the detachment.
This is NOT a counterexample to Erdős 184. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.CriticalDetachment
open CountCritical CycleNumberSubmodularity FractionalEnvelope
set_option maxHeartbeats 200000
abbrev V := Fin 8

def gEdges : Finset (Sym2 V) :=
  {s(0,1),s(0,2),s(0,3),s(0,4),s(0,5),s(0,6),s(1,2),s(1,3),s(1,4),s(2,5),s(2,6)}
def kEdges : Finset (Sym2 V) :=
  {s(7,1),s(7,2),s(0,3),s(0,4),s(0,5),s(0,6),s(1,2),s(1,3),s(1,4),s(2,5),s(2,6)}
def G : SimpleGraph V := fromEdgeSet (gEdges : Set (Sym2 V))
def K : SimpleGraph V := fromEdgeSet (kEdges : Set (Sym2 V))
instance : DecidableRel G.Adj := by unfold G; infer_instance
instance : DecidableRel K.Adj := by unfold K; infer_instance

lemma G_even : ∀ v, Even (G.degree v) := by intro v; fin_cases v <;> decide
lemma K_even : ∀ v, Even (K.degree v) := by intro v; fin_cases v <;> decide
lemma G_degree_zero : G.degree 0 = 6 := by decide
lemma K_degree_zero : K.degree 0 = 4 := by decide
lemma K_degree_seven : K.degree 7 = 2 := by decide
lemma K_degree_le_four : ∀ v, K.degree v ≤ 4 := by intro v; fin_cases v <;> decide

/-- A cycle cannot survive deletion of a vertex if at most two of the
remaining vertices have degree at least two. -/
lemma every_cycle_hits {W : Type*} [Fintype W] [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (v a b : W) (hab : a ≠ b)
    (hcheck : ∀ w, 2 ≤ ((A.deleteIncidenceSet v).neighborSet w).ncard → w = a ∨ w = b)
    (H : A.Subgraph) (hc : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) : v ∈ H.verts := by
  by_contra hn
  have hle : H.spanningCoe ≤ A.deleteIncidenceSet v := by
    intro x y hxy
    apply deleteIncidenceSet_adj.mpr
    exact ⟨H.adj_sub hxy,fun h => hn (h ▸ H.edge_vert hxy),
      fun h => hn (h ▸ H.edge_vert hxy.symm)⟩
  have hsub : H.verts ⊆ ({a,b} : Set W) := by
    intro w hw
    have hh : (H.neighborSet w).ncard = 2 := by
      have hh := hc.2 ⟨w,hw⟩
      rw [Subgraph.coe_degree] at hh
      simpa only [Subgraph.degree,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] using hh
    have hh' : 2 ≤ ((A.deleteIncidenceSet v).neighborSet w).ncard := by
      rw [← hh]
      exact Set.ncard_le_ncard (fun z hz => hle hz)
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hcheck w hh'
  have hcard := Set.ncard_le_ncard hsub
  have hthree := cycle_edgeSet_three_le H hc.1 (by
    intro z
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hc.2 z)
  have heq := regular_two_edge_vertex_card H (by
    intro z
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hc.2 z)
  rw [heq] at hthree
  rw [Set.ncard_pair hab] at hcard
  omega


lemma G_every_cycle (H : G.Subgraph)
    (hc : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) : (0 : V) ∈ H.verts := by
  have hcheck : ∀ v : V, 2 ≤ (G.deleteIncidenceSet 0).degree v → v = 1 ∨ v = 2 := by
    intro v; fin_cases v <;> decide
  apply every_cycle_hits G 0 1 2 (by decide) (fun v hv => ?_) H hc
  apply hcheck v
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] using hv

lemma G_partition_card (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) : D.card = 3 := by
  have hh := cycle_decomposition_vertex_count G D (by simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hc) hd 0
  have hf : D.filter (fun H => (0 : V) ∈ H.verts) = D := by
    apply Finset.filter_eq_self.mpr
    exact fun H hH => G_every_cycle H (hc H hH)
  have hg := G_degree_zero
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh hg
  rw [hf,hg] at hh
  omega

lemma G_number : cycleNumber G = 3 := by
  obtain ⟨D,hc,hd,hn⟩ := minimum_exists G (by simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using G_even)
  rw [← hn]
  exact G_partition_card D (by simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hc) hd

lemma G_invariant : InvariantPartitions.HasInvariantCount G := by
  intro D E hcD hdD hcE hdE
  rw [G_partition_card D (by simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hcD) hdD,G_partition_card E (by simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hcE) hdE]

lemma G_critical : IsCountCritical 3 G := by
  have hh := of_invariant (by simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using G_even) G_invariant
  rwa [G_number] at hh

lemma G_optimum : optimum G = 3 := by
  apply le_antisymm
  · simpa only [G_number,Nat.cast_ofNat] using optimum_le_number G (by simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using G_even)
  · have hh := degree_le_twice_optimum G (by simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using G_even) 0
    have hg := G_degree_zero
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh hg
    rw [hg] at hh
    norm_num at hh
    linarith

/-- The two cycles of a minimum partition after detaching 01 and 02. -/
def q0 : K.Walk 0 0 :=
  .cons (by decide : K.Adj 0 3) <| .cons (by decide : K.Adj 3 1) <|
  .cons (by decide : K.Adj 1 2) <| .cons (by decide : K.Adj 2 5) <|
  .cons (by decide : K.Adj 5 0) .nil
def q1 : K.Walk 0 0 :=
  .cons (by decide : K.Adj 0 4) <| .cons (by decide : K.Adj 4 1) <|
  .cons (by decide : K.Adj 1 7) <| .cons (by decide : K.Adj 7 2) <|
  .cons (by decide : K.Adj 2 6) <| .cons (by decide : K.Adj 6 0) .nil
lemma q0_cycle : q0.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [q0],by decide⟩
lemma q1_cycle : q1.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [q1],by decide⟩

def q (i : Fin 2) : Σ v, K.Walk v v := if i = 0 then ⟨0,q0⟩ else ⟨0,q1⟩
lemma q_cycle : ∀ i, (q i).2.IsCycle := by
  intro i; fin_cases i
  · simpa [q] using q0_cycle
  · simpa [q] using q1_cycle
lemma q_disjoint : ∀ i j, i ≠ j → List.Disjoint (q i).2.edges (q j).2.edges := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | exact List.disjoint_of_nodup_append (by decide)
lemma q_cover : ∀ x y, K.Adj x y ↔ ∃ i, s(x,y) ∈ (q i).2.edges := by
  intro x y; fin_cases x <;> fin_cases y <;> decide

lemma K_number : cycleNumber K = 2 := by
  apply cycleNumber_eq_of_degree K 2 0
  · simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using K_degree_zero
  · have hh := upper_of_walk_family K q q_cycle q_disjoint q_cover
    simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,
      Nat.card_fin] using hh

lemma K_optimum : optimum K = 2 := by
  have hh := LowCountCritical.optimum_eq_number_of_number_le_two (by simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using K_even) (by rw [K_number])
  simpa only [K_number,Nat.cast_ofNat] using hh

/-- A proper even restriction leaves at least three edges unused. -/
lemma proper_even_number_bound {W : Type*} [Fintype W] {A B : SimpleGraph W}
    (heA : ∀ v, Even (A.degree v)) (heB : ∀ v, Even (B.degree v))
    (hle : B ≤ A) (hne : B ≠ A) : 3 * (cycleNumber B + 1) ≤ A.edgeSet.ncard := by
  have her := even_sdiff_of_even hle heA heB
  have hn : A \ B ≠ ⊥ := by
    intro hh
    exact hne (le_antisymm hle (sdiff_eq_bot_iff.mp hh))
  obtain ⟨v,p,hp⟩ := exists_cycle_of_even_nonempty (A \ B) (by
    intro w
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using her w) hn
  have hc := cycle_subgraph_regular (A \ B) hp
  have hthree := cycle_edgeSet_three_le p.toSubgraph hc.1 hc.2
  have hleC := Set.ncard_le_ncard p.toSubgraph.edgeSet_subset
  obtain ⟨D,hcD,hdD,hcard⟩ := minimum_exists B heB
  have hb := cycle_decomposition_three_mul_card_le_edges B D hcD hdD
  simp only [edgeFinset_card,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq,hcard] at hb
  have heq := Set.ncard_diff_add_ncard_of_subset (edgeSet_mono hle)
  rw [edgeSet_sdiff] at hleC
  omega

lemma K_edge_card : K.edgeFinset.card = 11 := by decide

lemma K_integral_envelope : CycleEnvelope.envelope K = 2 := by
  apply le_antisymm
  · apply CycleEnvelope.envelope_le
    intro H hHK heH
    by_cases hh : H = K
    · subst H
      exact K_number.le
    · have hb := proper_even_number_bound (by
        simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using K_even)
        heH hHK hh
      have hcard : K.edgeSet.ncard = 11 := by
        simpa only [edgeFinset_card,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] using K_edge_card
      rw [hcard] at hb
      omega
  · have hh := CycleEnvelope.number_le_envelope (G := K) le_rfl (by
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using K_even)
    rwa [K_number] at hh

lemma G_fractional_envelope : envelope G = 3 := by
  have h₁ := envelope_le_integral G
  have h₂ := optimum_le_envelope (G := G) le_rfl (by
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using G_even)
  rw [CycleEnvelope.critical_envelope G_critical] at h₁
  rw [G_optimum] at h₂
  norm_num at h₁
  exact le_antisymm h₁ h₂

lemma K_fractional_envelope : envelope K = 2 := by
  have h₁ := envelope_le_integral K
  have h₂ := optimum_le_envelope (G := K) le_rfl (by
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using K_even)
  rw [K_integral_envelope] at h₁
  rw [K_optimum] at h₂
  norm_num at h₁
  exact le_antisymm h₁ h₂

/-- Identifying 7 with 0 is edge-bijective and has just one two-element fibre. -/
def collapse (v : V) : V := if v = 7 then 0 else v
def hom : K →g G where
  toFun := collapse
  map_rel' := by
    have hh : ∀ x y : V, K.Adj x y → G.Adj (collapse x) (collapse y) := by decide
    exact fun {x y} h => hh x y h
lemma collapse_fiber : collapse ⁻¹' {(0 : V)} = {0,7} := by
  ext v
  change collapse v = 0 ↔ v = 0 ∨ v = 7
  fin_cases v <;> decide
lemma collapse_off : Set.InjOn collapse {0,7}ᶜ := by
  intro x hx y hy hxy
  have hx' : x ≠ 7 := fun h => hx (Or.inr h)
  have hy' : y ≠ 7 := by exact fun h => hy (Or.inr h)
  simpa only [collapse,if_neg hx',if_neg hy'] using hxy
lemma collapse_edges_injective : Set.InjOn (Sym2.map hom) K.edgeSet := by
  intro e he f hf hef
  induction e using Sym2.ind with
  | h a b =>
    induction f using Sym2.ind with
    | h c d =>
      have hh : ∀ a b c d : V, K.Adj a b → K.Adj c d →
          s(collapse a,collapse b) = s(collapse c,collapse d) → s(a,b) = s(c,d) := by decide
      exact hh a b c d he hf hef
lemma collapse_edges_surjective : Set.SurjOn (Sym2.map hom) K.edgeSet G.edgeSet := by
  intro e he
  induction e using Sym2.ind with
  | h a b =>
    have hh : ∀ a b : V, G.Adj a b → ∃ c d : V,
        K.Adj c d ∧ s(collapse c,collapse d) = s(a,b) := by decide
    obtain ⟨c,d,hcd,hce⟩ := hh a b he
    exact ⟨s(c,d),hcd,hce⟩

/-- A three-cycle partition that lifts a minimum partition of G. -/
def p0 : K.Walk 7 7 :=
  .cons (by decide : K.Adj 7 1) <| .cons (by decide : K.Adj 1 2) <|
  .cons (by decide : K.Adj 2 7) .nil
def p1 : K.Walk 0 0 :=
  .cons (by decide : K.Adj 0 3) <| .cons (by decide : K.Adj 3 1) <|
  .cons (by decide : K.Adj 1 4) <| .cons (by decide : K.Adj 4 0) .nil
def p2 : K.Walk 0 0 :=
  .cons (by decide : K.Adj 0 5) <| .cons (by decide : K.Adj 5 2) <|
  .cons (by decide : K.Adj 2 6) <| .cons (by decide : K.Adj 6 0) .nil

def p (i : Fin 3) : Σ v, K.Walk v v :=
  if i = 0 then ⟨7,p0⟩ else if i = 1 then ⟨0,p1⟩ else ⟨0,p2⟩
lemma p_cycle : ∀ i, (p i).2.IsCycle := by
  intro i; fin_cases i <;> simp only [p] <;> rw [Walk.isCycle_def,Walk.isTrail_def] <;>
    exact ⟨by decide,by simp [p0,p1,p2],by decide⟩
lemma p_disjoint : ∀ i j, i ≠ j → List.Disjoint (p i).2.edges (p j).2.edges := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | exact List.disjoint_of_nodup_append (by decide)
lemma p_cover : ∀ x y, K.Adj x y ↔ ∃ i, s(x,y) ∈ (p i).2.edges := by
  intro x y; fin_cases x <;> fin_cases y <;> decide
lemma p_projected_cycle : ∀ i, ((p i).2.map hom).IsCycle := by
  intro i; fin_cases i <;> simp only [p] <;> rw [Walk.isCycle_def,Walk.isTrail_def] <;>
    exact ⟨by decide,by simp [p0,p1,p2],by decide⟩

def projectedP (i : Fin 3) : Σ v, G.Walk v v :=
  ⟨hom (p i).1,(p i).2.map hom⟩
lemma projectedP_disjoint : ∀ i j, i ≠ j →
    List.Disjoint (projectedP i).2.edges (projectedP j).2.edges := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first | exact (hij rfl).elim | exact List.disjoint_of_nodup_append (by decide)
lemma projectedP_cover : ∀ x y, G.Adj x y ↔ ∃ i, s(x,y) ∈ (projectedP i).2.edges := by
  intro x y; fin_cases x <;> fin_cases y <;> decide

lemma projectedP_is_minimum :
    (∀ i, (projectedP i).2.IsCycle) ∧
    (∀ i j, i ≠ j → List.Disjoint (projectedP i).2.edges (projectedP j).2.edges) ∧
    (∀ x y, G.Adj x y ↔ ∃ i, s(x,y) ∈ (projectedP i).2.edges) ∧
    Fintype.card (Fin 3) = cycleNumber G := by
  exact ⟨p_projected_cycle,projectedP_disjoint,projectedP_cover,by simp [G_number]⟩

/-- Criticality does not preserve minimum cycle count under this even
vertex split, even though an original minimum partition lifts to it. -/
lemma critical_detachment_count_drop :
    IsCountCritical 3 G ∧ cycleNumber K = 2 ∧
    (∀ v, K.degree v ≤ 4) ∧ optimum G = 3 ∧ optimum K = 2 ∧
    (∀ i, (p i).2.IsCycle ∧ ((p i).2.map hom).IsCycle) ∧
    (∀ i j, i ≠ j → List.Disjoint (p i).2.edges (p j).2.edges) ∧
    (∀ x y, K.Adj x y ↔ ∃ i, s(x,y) ∈ (p i).2.edges) :=
  ⟨G_critical,K_number,K_degree_le_four,G_optimum,K_optimum,
    fun i => ⟨p_cycle i,p_projected_cycle i⟩,p_disjoint,p_cover⟩

/-- Both the integral and fractional envelopes drop in this critical example. -/
lemma critical_detachment_envelope_drop :
    IsCountCritical 3 G ∧ cycleNumber K = 2 ∧
    CycleEnvelope.envelope G = 3 ∧ CycleEnvelope.envelope K = 2 ∧
    envelope G = 3 ∧ envelope K = 2 ∧
    Set.InjOn (Sym2.map hom) K.edgeSet ∧
    Set.SurjOn (Sym2.map hom) K.edgeSet G.edgeSet :=
  ⟨G_critical,K_number,CycleEnvelope.critical_envelope G_critical,K_integral_envelope,
    G_fractional_envelope,K_fractional_envelope,collapse_edges_injective,collapse_edges_surjective⟩

end Erdos184.CriticalDetachment
