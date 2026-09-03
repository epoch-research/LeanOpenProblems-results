import Submission.IncidenceForest

/-!
A family showing that the incidence-forest property of all linear subfamilies
is not, by itself, sufficient to bound a cycle decomposition linearly.
The decompositions constructed here are NOT asserted to be minimum.
This is not a counterexample to Erdos 184.
-/

open SimpleGraph
open scoped Classical
namespace Erdos184.LinearFamilyGap

variable (A : Type*) [AddCommGroup A] [Fintype A]

/-- The independent blowup of a six-cycle. -/
def G : SimpleGraph (Fin 6 × A) := (cycleGraph 6).comap Prod.fst

/-- A Latin-square six-cycle; both copies of each of three labels occur. -/
def walk (a b : A) : (G A).Walk (0,a) (0,a) :=
  .cons (by change (cycleGraph 6).Adj 0 1; decide : (G A).Adj (0,a) (1,b)) <|
  .cons (by change (cycleGraph 6).Adj 1 2; decide : (G A).Adj (1,b) (2,a+b)) <|
  .cons (by change (cycleGraph 6).Adj 2 3; decide : (G A).Adj (2,a+b) (3,a)) <|
  .cons (by change (cycleGraph 6).Adj 3 4; decide : (G A).Adj (3,a) (4,b)) <|
  .cons (by change (cycleGraph 6).Adj 4 5; decide : (G A).Adj (4,b) (5,a+b)) <|
  .cons (by change (cycleGraph 6).Adj 5 0; decide : (G A).Adj (5,a+b) (0,a)) .nil

def piece (a b : A) : (G A).Subgraph := (walk A a b).toSubgraph

lemma walk_cycle (a b : A) : (walk A a b).IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  simp [walk, Sym2.eq_iff, Prod.mk.injEq]

lemma piece_cycles (a b : A) :
    (piece A a b).coe.Connected ∧ (piece A a b).coe.IsRegularOfDegree 2 := by
  have h := cycle_subgraph_regular (G A) (walk_cycle A a b)
  refine ⟨h.1, ?_⟩
  intro v
  simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    using h.2 v

lemma piece_injective : Function.Injective (fun p : A × A => piece A p.1 p.2) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  have h0 := congrArg (fun H : (G A).Subgraph => (0,a) ∈ H.verts) h
  have h1 := congrArg (fun H : (G A).Subgraph => (1,b) ∈ H.verts) h
  simp [piece, walk, Walk.verts_toSubgraph] at h0 h1
  exact Prod.ext h0 h1

lemma edge_determines_piece {a b c d : A} (u v : Fin 6 × A)
    (h1 : s(u,v) ∈ (piece A a b).edgeSet)
    (h2 : s(u,v) ∈ (piece A c d).edgeSet) : a = c ∧ b = d := by
  rcases u with ⟨i,x⟩
  rcases v with ⟨j,y⟩
  simp only [piece, Walk.edgeSet_toSubgraph, Set.mem_setOf_eq] at h1 h2
  fin_cases i <;> fin_cases j <;>
    simp [walk, Sym2.eq_iff, Prod.mk.injEq] at h1 h2 <;> aesop

lemma base_adj (i j : Fin 6) : (cycleGraph 6).Adj i j ↔
      (i = 0 ∧ j = 1) ∨
      (i = 1 ∧ j = 0) ∨
      (i = 1 ∧ j = 2) ∨
      (i = 2 ∧ j = 1) ∨
      (i = 2 ∧ j = 3) ∨
      (i = 3 ∧ j = 2) ∨
      (i = 3 ∧ j = 4) ∨
      (i = 4 ∧ j = 3) ∨
      (i = 4 ∧ j = 5) ∨
      (i = 5 ∧ j = 4) ∨
      (i = 5 ∧ j = 0) ∨
      (i = 0 ∧ j = 5) := by
  fin_cases i <;> fin_cases j <;> decide

set_option maxHeartbeats 1000000 in
lemma edge_covered (u v : Fin 6 × A) (h : (G A).Adj u v) :
    ∃ a b : A, s(u,v) ∈ (piece A a b).edgeSet := by
  rcases u with ⟨i,x⟩
  rcases v with ⟨j,y⟩
  change (cycleGraph 6).Adj i j at h
  rw [base_adj] at h
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨x,y,by simp [piece,walk]⟩
  · exact ⟨y,x,by simp [piece,walk]⟩
  · exact ⟨y-x,x,by simp [piece,walk]⟩
  · exact ⟨x-y,y,by simp [piece,walk]⟩
  · exact ⟨y,x-y,by simp [piece,walk]⟩
  · exact ⟨x,y-x,by simp [piece,walk]⟩
  · exact ⟨x,y,by simp [piece,walk]⟩
  · exact ⟨y,x,by simp [piece,walk]⟩
  · exact ⟨y-x,x,by simp [piece,walk]⟩
  · exact ⟨x-y,y,by simp [piece,walk]⟩
  · exact ⟨y,x-y,by simp [piece,walk]⟩
  · exact ⟨x,y-x,by simp [piece,walk]⟩

noncomputable def D : Finset (G A).Subgraph :=
  Finset.univ.image (fun p : A × A => piece A p.1 p.2)

lemma mem_D (H : (G A).Subgraph) : H ∈ D A ↔ ∃ a b, H = piece A a b := by
  simp [D, eq_comm]

lemma D_card : (D A).card = Fintype.card A ^ 2 := by
  rw [D, Finset.card_image_of_injective _ (piece_injective A)]
  simp [Fintype.card_prod, pow_two]

lemma D_cycles : ∀ H ∈ D A, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
  intro H hH
  obtain ⟨a,b,rfl⟩ := (mem_D A H).mp hH
  exact piece_cycles A a b

lemma D_decomposition : IsDecomposition (G A) (D A) := by
  constructor
  · intro H hH J hJ hne
    obtain ⟨a,b,rfl⟩ := (mem_D A H).mp hH
    obtain ⟨c,d,rfl⟩ := (mem_D A J).mp hJ
    change Disjoint (piece A a b).edgeSet (piece A c d).edgeSet
    rw [Set.disjoint_left]
    intro e he hf
    induction e using Sym2.ind with
    | h u v =>
      obtain ⟨rfl,rfl⟩ := edge_determines_piece A u v he hf
      exact hne rfl
  · ext e
    induction e using Sym2.ind with
    | h u v =>
      simp only [Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨H,_,he⟩
        exact H.edgeSet_subset he
      · intro he
        obtain ⟨a,b,h⟩ := edge_covered A u v he
        exact ⟨piece A a b,(mem_D A _).mpr ⟨a,b,rfl⟩,h⟩

lemma piece_length (a b : A) : (piece A a b).edgeSet.ncard = 6 := by
  rw [piece, Walk.edgeSet_toSubgraph]
  have heq : {e | e ∈ (walk A a b).edges} =
      ((walk A a b).edges.toFinset : Set (Sym2 (Fin 6 × A))) := by ext e; simp
  rw [heq, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup (walk_cycle A a b).isTrail.edges_nodup]
  rfl

def twin (v : Fin 6 × A) : Fin 6 × A := (v.1 + 3, v.2)

lemma twin_ne (v : Fin 6 × A) : twin A v ≠ v := by
  rcases v with ⟨i,x⟩
  fin_cases i <;> simp [twin]

lemma twin_mem_piece (a b : A) (v : Fin 6 × A) :
    twin A v ∈ (piece A a b).verts ↔ v ∈ (piece A a b).verts := by
  rcases v with ⟨i,x⟩
  fin_cases i <;> simp [twin,piece,walk]

lemma twin_mem {H : (G A).Subgraph} (hH : H ∈ D A) (v : Fin 6 × A) :
    twin A v ∈ H.verts ↔ v ∈ H.verts := by
  obtain ⟨a,b,rfl⟩ := (mem_D A H).mp hH
  exact twin_mem_piece A a b v

/-- In this family, linear subfamilies actually have pairwise disjoint
vertex sets. This is much stronger than having forest incidence graphs. -/
lemma linear_subfamily_disjoint (S : Finset (G A).Subgraph) (hS : S ⊆ D A)
    (hlin : ∀ H ∈ S, ∀ J ∈ S, H ≠ J → (H.verts ∩ J.verts).Subsingleton) :
    Set.PairwiseDisjoint (S : Set (G A).Subgraph) (fun H => H.verts) := by
  intro H hH J hJ hne
  change Disjoint H.verts J.verts
  rw [Set.disjoint_left]
  intro v hv hj
  have ht : twin A v ∈ H.verts ∩ J.verts :=
    ⟨(twin_mem A (hS hH) v).mpr hv,(twin_mem A (hS hJ) v).mpr hj⟩
  exact twin_ne A v (hlin H hH J hJ hne ht ⟨hv,hj⟩)

lemma disjoint_incidence_acyclic {V I : Type*} (s : I → Set V)
    (hd : Pairwise (fun i j => Disjoint (s i) (s j))) :
    (CycleIncidence.graph s).IsAcyclic := by
  by_contra hh
  have hlin : ∀ i j, i ≠ j → (s i ∩ s j).Subsingleton := by
    intro i j hij x hx y hy
    exact (Set.disjoint_left.mp (hd hij) hx.1 hx.2).elim
  obtain ⟨n,v,j,hn,_,hi,_,hs,he,_⟩ := CycleIncidence.exists_clean_ring s hlin hh
  have h0 : 0 < n := by omega
  have h1 : 1 < n := by omega
  have hne : j 0 h0 ≠ j 1 h1 := by
    intro heq
    have hh := hi (a₁ := ⟨0,h0⟩) (a₂ := ⟨1,h1⟩) heq
    exact Nat.zero_ne_one (congrArg Fin.val hh)
  exact Set.disjoint_left.mp (hd hne) (he 0 h0) (hs 1 h1)

lemma linear_subfamily_acyclic (S : Finset (G A).Subgraph) (hS : S ⊆ D A)
    (hlin : ∀ H ∈ S, ∀ J ∈ S, H ≠ J → (H.verts ∩ J.verts).Subsingleton) :
    (CycleIncidence.graph (fun H : S => H.val.verts)).IsAcyclic := by
  apply disjoint_incidence_acyclic
  intro H J hne
  exact linear_subfamily_disjoint A S hS hlin H.property J.property
    (fun h => hne (Subtype.ext h))

lemma graph_regular : (G A).IsRegularOfDegree (2 * Fintype.card A) := by
  intro v
  let e : (G A).neighborSet v ≃ (cycleGraph 6).neighborSet v.1 × A :=
    { toFun := fun w => (⟨w.val.1,w.property⟩,w.val.2)
      invFun := fun w => ⟨(w.1.val,w.2),w.1.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_congr e, Fintype.card_prod,
    SimpleGraph.card_neighborSet_eq_degree, cycleGraph_degree_three_le]

/-- The displayed decomposition size grows quadratically while the number
of vertices grows linearly. No minimality assertion is made. -/
theorem unbounded_size (C : ℕ) :
    C * Fintype.card (Fin 6 × ZMod (6*C+1)) < (D (ZMod (6*C+1))).card := by
  rw [D_card]
  simp only [Fintype.card_prod, Fintype.card_fin, ZMod.card]
  nlinarith

/-- There is no uniform linear bound for all decompositions satisfying
only the incidence-forest condition on their linear subfamilies. This
negates a proposed abstraction, NOT the original existence conjecture. -/
theorem no_uniform_incidence_bound :
    ¬ ∃ C : ℕ, ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (D : Finset G.Subgraph),
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G D →
      (∀ S : Finset G.Subgraph, S ⊆ D →
        (∀ H ∈ S, ∀ J ∈ S, H ≠ J → (H.verts ∩ J.verts).Subsingleton) →
        (CycleIncidence.graph (fun H : S => H.val.verts)).IsAcyclic) →
      D.card ≤ C * Fintype.card V := by
  rintro ⟨C,hC⟩
  have hh := hC (G (ZMod (6*C+1))) (D (ZMod (6*C+1)))
    (D_cycles _) (D_decomposition _) (linear_subfamily_acyclic _)
  exact Nat.not_le_of_gt (unbounded_size C) hh

end Erdos184.LinearFamilyGap
