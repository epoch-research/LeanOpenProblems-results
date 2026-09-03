import Submission.InvariantPartitions

/-!
An explicit failure of submodularity for the minimum number of cycles in an
Eulerian graph. This rules out a proposed diminishing-returns argument; it is
not a counterexample to Erdos 184.
-/
open SimpleGraph
namespace Erdos184
namespace CycleNumberSubmodularity

open scoped Classical in
noncomputable def cycleNumber {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  if h : ∃ n : ℕ, ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card = n then Nat.find h else 0

open scoped Classical in
lemma cycleNumber_eq {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (hu : ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card ≤ k)
    (hl : ∀ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G D → k ≤ D.card) : cycleNumber G = k := by
  obtain ⟨D,hc,hd,hcard⟩ := hu
  have hex : ∃ n : ℕ, ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card = n := ⟨D.card,D,hc,hd,rfl⟩
  rw [cycleNumber, dif_pos hex]
  have hle := (Nat.find_min' hex ⟨D,hc,hd,rfl⟩).trans hcard
  obtain ⟨E,hcE,hdE,hcardE⟩ := Nat.find_spec hex
  have hge := hl E hcE hdE
  omega

open scoped Classical in
/-- A finite, explicitly checked family of closed walks supplies a cycle
partition upper bound. This uses ordinary proofs, not native computation. -/
lemma upper_of_walk_family {V I : Type*} [Fintype V] [Fintype I]
    (G : SimpleGraph V) (p : I → Σ v, G.Walk v v)
    (hp : ∀ i, (p i).2.IsCycle)
    (hdis : ∀ i j, i ≠ j → List.Disjoint (p i).2.edges (p j).2.edges)
    (hcover : ∀ u v, G.Adj u v ↔ ∃ i, s(u,v) ∈ (p i).2.edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card ≤ Fintype.card I := by
  let D : Finset G.Subgraph := Finset.univ.image (fun i => (p i).2.toSubgraph)
  refine ⟨D, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro H hH
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
    exact cycle_subgraph_regular G (hp i)
  · intro H hH K hK hne
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hK
    have hij : i ≠ j := fun h => hne (congrArg (fun k => (p k).2.toSubgraph) h)
    simp only [Walk.edgeSet_toSubgraph, Set.disjoint_left, Set.mem_setOf_eq]
    exact fun e he hf => hdis i j hij he hf
  · ext e
    induction e using Sym2.ind with
    | h u v =>
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨H,_,he⟩
        exact H.edgeSet_subset he
      · intro he
        obtain ⟨i,hi⟩ := (hcover u v).mp he
        exact ⟨(p i).2.toSubgraph, Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,
          (p i).2.mem_edges_toSubgraph.mpr hi⟩
  · exact (Finset.card_image_le).trans_eq (Finset.card_univ)

abbrev V := Fin 8

def coreEdges : Finset (Sym2 V) :=
  {s(0,1),s(0,2),s(0,3),s(0,4),s(1,2),s(1,3),s(1,4),s(2,3),s(2,4),s(3,4)}
def triangleEdges : Finset (Sym2 V) := {s(0,1),s(1,2),s(2,0)}
def addedEdges : Finset (Sym2 V) := {s(0,5),s(5,1),s(1,6),s(6,2),s(2,7),s(7,0)}

def A : SimpleGraph V := fromEdgeSet (coreEdges : Set (Sym2 V))
def C : SimpleGraph V := fromEdgeSet (triangleEdges : Set (Sym2 V))
def T : SimpleGraph V := fromEdgeSet (addedEdges : Set (Sym2 V))
def G : SimpleGraph V := A ⊔ T
def B : SimpleGraph V := G \ C
def R : SimpleGraph V := A \ C

instance : DecidableRel A.Adj := by unfold A; infer_instance
instance : DecidableRel C.Adj := by unfold C; infer_instance
instance : DecidableRel T.Adj := by unfold T; infer_instance
instance : DecidableRel G.Adj := by unfold G; infer_instance
instance : DecidableRel B.Adj := by unfold B; infer_instance
instance : DecidableRel R.Adj := by unfold R; infer_instance

lemma A_degree : A.degree 3 = 4 := by decide
lemma B_degree : B.degree 3 = 4 := by decide
lemma R_degree : R.degree 3 = 4 := by decide
lemma G_degree : G.degree 0 = 6 := by decide

lemma A_even : ∀ v, Even (A.degree v) := by intro v; fin_cases v <;> decide
lemma B_even : ∀ v, Even (B.degree v) := by intro v; fin_cases v <;> decide
lemma R_even : ∀ v, Even (R.degree v) := by intro v; fin_cases v <;> decide
lemma G_even : ∀ v, Even (G.degree v) := by intro v; fin_cases v <;> decide

lemma union_eq : A ⊔ B = G := by
  ext u v
  fin_cases u <;> fin_cases v <;> decide
lemma inter_eq : A ⊓ B = R := by
  ext u v
  fin_cases u <;> fin_cases v <;> decide

def a0 : A.Walk 0 0 :=
  .cons (by decide : A.Adj 0 1) <|
  .cons (by decide : A.Adj 1 2) <|
  .cons (by decide : A.Adj 2 3) <|
  .cons (by decide : A.Adj 3 4) <|
  .cons (by decide : A.Adj 4 0) .nil

lemma a0_cycle : a0.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [a0], by decide⟩

def a1 : A.Walk 0 0 :=
  .cons (by decide : A.Adj 0 2) <|
  .cons (by decide : A.Adj 2 4) <|
  .cons (by decide : A.Adj 4 1) <|
  .cons (by decide : A.Adj 1 3) <|
  .cons (by decide : A.Adj 3 0) .nil

lemma a1_cycle : a1.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [a1], by decide⟩

def b0 : B.Walk 0 0 :=
  .cons (by decide : B.Adj 0 5) <|
  .cons (by decide : B.Adj 5 1) <|
  .cons (by decide : B.Adj 1 6) <|
  .cons (by decide : B.Adj 6 2) <|
  .cons (by decide : B.Adj 2 3) <|
  .cons (by decide : B.Adj 3 4) <|
  .cons (by decide : B.Adj 4 0) .nil

lemma b0_cycle : b0.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [b0], by decide⟩

def b1 : B.Walk 0 0 :=
  .cons (by decide : B.Adj 0 7) <|
  .cons (by decide : B.Adj 7 2) <|
  .cons (by decide : B.Adj 2 4) <|
  .cons (by decide : B.Adj 4 1) <|
  .cons (by decide : B.Adj 1 3) <|
  .cons (by decide : B.Adj 3 0) .nil

lemma b1_cycle : b1.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [b1], by decide⟩

def r0 : R.Walk 0 0 :=
  .cons (by decide : R.Adj 0 3) <|
  .cons (by decide : R.Adj 3 4) <|
  .cons (by decide : R.Adj 4 0) .nil

lemma r0_cycle : r0.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [r0], by decide⟩

def r1 : R.Walk 1 1 :=
  .cons (by decide : R.Adj 1 3) <|
  .cons (by decide : R.Adj 3 2) <|
  .cons (by decide : R.Adj 2 4) <|
  .cons (by decide : R.Adj 4 1) .nil

lemma r1_cycle : r1.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [r1], by decide⟩

def g0 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 2) <|
  .cons (by decide : G.Adj 2 3) <|
  .cons (by decide : G.Adj 3 4) <|
  .cons (by decide : G.Adj 4 0) .nil

lemma g0_cycle : g0.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [g0], by decide⟩

def g1 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 2) <|
  .cons (by decide : G.Adj 2 4) <|
  .cons (by decide : G.Adj 4 1) <|
  .cons (by decide : G.Adj 1 3) <|
  .cons (by decide : G.Adj 3 0) .nil

lemma g1_cycle : g1.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [g1], by decide⟩

def g2 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 5) <|
  .cons (by decide : G.Adj 5 1) <|
  .cons (by decide : G.Adj 1 6) <|
  .cons (by decide : G.Adj 6 2) <|
  .cons (by decide : G.Adj 2 7) <|
  .cons (by decide : G.Adj 7 0) .nil

lemma g2_cycle : g2.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  exact ⟨by decide, by simp [g2], by decide⟩

def Awalks : Fin 2 → Σ v, A.Walk v v := ![⟨0,a0⟩,⟨0,a1⟩]

open scoped Classical in
lemma A_upper : ∃ D : Finset A.Subgraph,
    (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
    IsDecomposition A D ∧ D.card ≤ 2 := by
  simp only [IsRegularOfDegree, ← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
  have hu := upper_of_walk_family A Awalks
  simp only [IsRegularOfDegree, ← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card, Nat.card_fin] at hu
  apply hu
  · intro i
    fin_cases i
    · exact a0_cycle
    · exact a1_cycle
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | exact List.disjoint_of_nodup_append (by decide)
  · intro u v
    fin_cases u <;> fin_cases v <;> decide

def Bwalks : Fin 2 → Σ v, B.Walk v v := ![⟨0,b0⟩,⟨0,b1⟩]

open scoped Classical in
lemma B_upper : ∃ D : Finset B.Subgraph,
    (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
    IsDecomposition B D ∧ D.card ≤ 2 := by
  simp only [IsRegularOfDegree, ← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
  have hu := upper_of_walk_family B Bwalks
  simp only [IsRegularOfDegree, ← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card, Nat.card_fin] at hu
  apply hu
  · intro i
    fin_cases i
    · exact b0_cycle
    · exact b1_cycle
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | exact List.disjoint_of_nodup_append (by decide)
  · intro u v
    fin_cases u <;> fin_cases v <;> decide

def Rwalks : Fin 2 → Σ v, R.Walk v v := ![⟨0,r0⟩,⟨1,r1⟩]

open scoped Classical in
lemma R_upper : ∃ D : Finset R.Subgraph,
    (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
    IsDecomposition R D ∧ D.card ≤ 2 := by
  simp only [IsRegularOfDegree, ← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
  have hu := upper_of_walk_family R Rwalks
  simp only [IsRegularOfDegree, ← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card, Nat.card_fin] at hu
  apply hu
  · intro i
    fin_cases i
    · exact r0_cycle
    · exact r1_cycle
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | exact List.disjoint_of_nodup_append (by decide)
  · intro u v
    fin_cases u <;> fin_cases v <;> decide

def Gwalks : Fin 3 → Σ v, G.Walk v v := ![⟨0,g0⟩,⟨0,g1⟩,⟨0,g2⟩]

open scoped Classical in
lemma G_upper : ∃ D : Finset G.Subgraph,
    (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
    IsDecomposition G D ∧ D.card ≤ 3 := by
  simp only [IsRegularOfDegree, ← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
  have hu := upper_of_walk_family G Gwalks
  simp only [IsRegularOfDegree, ← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card, Nat.card_fin] at hu
  apply hu
  · intro i
    fin_cases i
    · exact g0_cycle
    · exact g1_cycle
    · exact g2_cycle
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | exact List.disjoint_of_nodup_append (by decide)
  · intro u v
    fin_cases u <;> fin_cases v <;> decide


open scoped Classical in
lemma cycleNumber_eq_of_degree {U : Type*} [Fintype U] (X : SimpleGraph U)
    (k : ℕ) (v : U) (hv : X.degree v = 2*k)
    (hu : ∃ D : Finset X.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition X D ∧ D.card ≤ k) : cycleNumber X = k := by
  apply cycleNumber_eq X k hu
  intro D hc hd
  have hh := cycle_decomposition_vertex_count X D hc hd v
  have hf := Finset.card_filter_le D (fun H => v ∈ H.verts)
  simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hv hh
  omega

open scoped Classical in
lemma A_number : cycleNumber A = 2 := by
  apply cycleNumber_eq_of_degree A 2 3
  · simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using A_degree
  · simpa only [IsRegularOfDegree, ← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using A_upper

open scoped Classical in
lemma B_number : cycleNumber B = 2 := by
  apply cycleNumber_eq_of_degree B 2 3
  · simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using B_degree
  · simpa only [IsRegularOfDegree, ← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using B_upper

open scoped Classical in
lemma R_number : cycleNumber R = 2 := by
  apply cycleNumber_eq_of_degree R 2 3
  · simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using R_degree
  · simpa only [IsRegularOfDegree, ← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using R_upper

open scoped Classical in
lemma G_number : cycleNumber G = 3 := by
  apply cycleNumber_eq_of_degree G 3 0
  · simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using G_degree
  · simpa only [IsRegularOfDegree, ← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using G_upper

/-- The four minimum cycle counts are 2,2,2,3, violating the submodular
inequality on a pair whose union and intersection are both even. -/
lemma strict_submodularity_failure :
    cycleNumber A + cycleNumber B < cycleNumber (A ⊔ B) + cycleNumber (A ⊓ B) := by
  rw [union_eq, inter_eq, A_number, B_number, G_number, R_number]
  decide

/-- Deleting the same triangle has zero marginal benefit in A, but benefit
one in its even supergraph G. A general diminishing-returns argument is false. -/
lemma marginal_gain_increases :
    A ≤ G ∧ C ≤ A ∧
    cycleNumber A - cycleNumber (A \ C) = 0 ∧
    cycleNumber G - cycleNumber (G \ C) = 1 := by
  refine ⟨le_sup_left, ?_, ?_, ?_⟩
  · intro u v
    fin_cases u <;> fin_cases v <;> decide
  · change cycleNumber A - cycleNumber R = 0
    rw [A_number,R_number]
  · change cycleNumber G - cycleNumber B = 1
    rw [G_number,B_number]

open scoped Classical in
lemma failure_on_even_graphs :
    ∃ X Y : SimpleGraph V,
      (∀ v, Even (X.degree v)) ∧ (∀ v, Even (Y.degree v)) ∧
      (∀ v, Even ((X ⊓ Y).degree v)) ∧ (∀ v, Even ((X ⊔ Y).degree v)) ∧
      cycleNumber X + cycleNumber Y < cycleNumber (X ⊔ Y) + cycleNumber (X ⊓ Y) := by
  refine ⟨A,B,?_,?_,?_,?_,strict_submodularity_failure⟩
  · intro v
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using A_even v
  · intro v
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using B_even v
  · intro v
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card, inter_eq] using R_even v
  · intro v
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card, union_eq] using G_even v

end CycleNumberSubmodularity
end Erdos184
