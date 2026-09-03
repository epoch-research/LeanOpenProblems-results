import Submission.ChainRingDefinitions

/-! Block restrictions and parity identities for the chain graph. -/
open SimpleGraph
namespace Erdos184Work.ChainRing
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 10000

def leftPort : Fin 3 → Vertex := ![.inl 0,.inl 1,.inl 2]
def rightPort : Fin 3 → Vertex := ![.inl 1,.inl 2,.inl 3]
def middlePort : Fin 3 → Vertex := ![.inl 4,.inl 5,.inl 6]
def block (i : Fin 3) : SimpleGraph Vertex :=
  active false (fun k => if k = i then Finset.univ else ∅)
instance (i : Fin 3) : DecidableRel (block i).Adj := by unfold block; infer_instance

lemma ports_ne : ∀ i, leftPort i ≠ rightPort i := by decide
lemma block_le_source : ∀ i, block i ≤ source := by
  intro i x y
  revert i x y
  decide +kernel
lemma block_internal_or_zero : ∀ i v, v ≠ leftPort i → v ≠ rightPort i →
    (∀ w, (block i).Adj v w ↔ source.Adj v w) ∨ (∀ w, ¬ (block i).Adj v w) := by
  decide +kernel
lemma block_distinct_edges : ∀ i j, i ≠ j → ∀ x y, ¬ ((block i).Adj x y ∧ (block j).Adj x y) := by
  decide +kernel
lemma source_edge_cases : ∀ x y, source.Adj x y →
    closing.Adj x y ∨ ∃ i, (block i).Adj x y := by decide +kernel
lemma block_no_closing : ∀ i x y, ¬ ((block i).Adj x y ∧ closing.Adj x y) := by decide +kernel
lemma source_degree_right : ∀ i j, source.degree (.inr (i,j)) = 3 := by decide +kernel
lemma closing_degree_zero : closing.degree (.inl 0) = 1 := by decide +kernel
lemma closing_degree_three : closing.degree (.inl 3) = 1 := by decide +kernel
lemma closing_adj_iff : ∀ x y, closing.Adj x y ↔
    (x = .inl 0 ∧ y = .inl 3) ∨ (x = .inl 3 ∧ y = .inl 0) := by decide +kernel

def portA : Fin 4 → SimpleGraph Vertex := ![block 0,block 0,block 1,block 2]
def portB : Fin 4 → SimpleGraph Vertex := ![closing,block 1,block 2,closing]
def portVertex : Fin 4 → Vertex := ![.inl 0,.inl 1,.inl 2,.inl 3]
instance (i : Fin 4) : DecidableRel (portA i).Adj := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.cases ?_
    (fun l => Fin.cases ?_ (fun z => Fin.elim0 z) l) k) j) i
  all_goals dsimp [portA]; infer_instance
instance (i : Fin 4) : DecidableRel (portB i).Adj := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.cases ?_
    (fun l => Fin.cases ?_ (fun z => Fin.elim0 z) l) k) j) i
  all_goals dsimp [portB]; infer_instance
lemma port_cover : ∀ i w, source.Adj (portVertex i) w →
    (portA i).Adj (portVertex i) w ∨ (portB i).Adj (portVertex i) w := by decide +kernel
lemma port_disjoint : ∀ i w, ¬ ((portA i).Adj (portVertex i) w ∧ (portB i).Adj (portVertex i) w) := by
  decide +kernel

open scoped Classical

noncomputable abbrev deg {U : Type*} (G : SimpleGraph U) (v : U) : ℕ := Nat.card (G.neighborSet v)

lemma degree_eq_of_adj_iff {U : Type*} (G H : SimpleGraph U) (v : U)
    (h : ∀ w, G.Adj v w ↔ H.Adj v w) : deg G v = deg H v := by
  have he : G.neighborSet v = H.neighborSet v := Set.ext h
  exact congrArg (fun s : Set U => Nat.card s) he

lemma degree_zero_of_no_adj {U : Type*} (G : SimpleGraph U) (v : U)
    (h : ∀ w, ¬ G.Adj v w) : deg G v = 0 := by
  have he : G.neighborSet v = ∅ := by ext w; simp [h w]
  simp only [deg,he,Nat.card_eq_fintype_card,Fintype.card_ofIsEmpty]

lemma even_two_degrees {U : Type*} [Fintype U] (G : SimpleGraph U) {u v : U} (huv : u ≠ v)
    (h : ∀ w, w ≠ u → w ≠ v → Even (deg G w)) : Even (deg G u + deg G v) := by
  have hrest : Even (∑ w ∈ (Finset.univ \ {u,v}), deg G w) := by
    apply Finset.even_sum
    intro w hw
    have hh := (Finset.mem_sdiff.mp hw).2
    exact h w (fun he => hh (by simp [he])) (fun he => hh (by simp [he]))
  have hsum := Finset.sum_sdiff (f := fun w => deg G w)
    (show ({u,v} : Finset U) ⊆ Finset.univ from Finset.subset_univ _)
  have hall : (∑ w, deg G w) = 2 * G.edgeFinset.card := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using
      G.sum_degrees_eq_twice_card_edges
  rw [Finset.sum_pair huv,hall] at hsum
  rw [Nat.even_iff] at hrest ⊢
  dsimp only at hsum
  omega

lemma block_internal_degree {S : SimpleGraph Vertex} (hS : S ≤ source) (i : Fin 3) (v : Vertex)
    (hl : v ≠ leftPort i) (hr : v ≠ rightPort i) :
    deg (S ⊓ block i) v = deg S v ∨ deg (S ⊓ block i) v = 0 := by
  rcases block_internal_or_zero i v hl hr with h | h
  · left
    apply degree_eq_of_adj_iff
    intro w
    exact ⟨And.left,fun hw => ⟨hw,(h w).mpr (hS hw)⟩⟩
  · right
    exact degree_zero_of_no_adj (S ⊓ block i) v (fun w hw => h w hw.2)

lemma block_boundary_even {S : SimpleGraph Vertex} (hS : S ≤ source)
    (heven : ∀ v, Even (deg S v)) (i : Fin 3) :
    Even (deg (S ⊓ block i) (leftPort i) + deg (S ⊓ block i) (rightPort i)) := by
  apply even_two_degrees _ (ports_ne i)
  intro v hl hr
  rcases block_internal_degree hS i v hl hr with h | h
  · rw [h]; exact heven v
  · rw [h]; exact ⟨0,rfl⟩

lemma degree_split_at {U : Type*} [Fintype U] (G K L : SimpleGraph U) (v : U)
    (hcover : ∀ w, G.Adj v w → K.Adj v w ∨ L.Adj v w)
    (hdis : ∀ w, ¬ (K.Adj v w ∧ L.Adj v w)) :
    deg G v = deg (G ⊓ K) v + deg (G ⊓ L) v := by
  have he : G.neighborFinset v = (G ⊓ K).neighborFinset v ∪ (G ⊓ L).neighborFinset v := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset,Finset.mem_union,SimpleGraph.inf_adj]
    constructor
    · intro h
      exact (hcover w h).imp (fun hk => ⟨h,hk⟩) (fun hl => ⟨h,hl⟩)
    · rintro (⟨h,_⟩ | ⟨h,_⟩) <;> exact h
  have hd : Disjoint ((G ⊓ K).neighborFinset v) ((G ⊓ L).neighborFinset v) := by
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    exact hdis w ⟨((G ⊓ K).mem_neighborFinset _ _ |>.mp hw).2,
      ((G ⊓ L).mem_neighborFinset _ _ |>.mp hw').2⟩
  have hc := congrArg Finset.card he
  rw [Finset.card_union_of_disjoint hd] at hc
  simpa only [SimpleGraph.card_neighborFinset_eq_degree,← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] using hc

lemma degree_port_split {S : SimpleGraph Vertex} (hS : S ≤ source) (i : Fin 4) :
    deg S (portVertex i) = deg (S ⊓ portA i) (portVertex i) +
      deg (S ⊓ portB i) (portVertex i) :=
  degree_split_at S (portA i) (portB i) (portVertex i)
    (fun w hw => port_cover i w (hS hw)) (port_disjoint i)

lemma inf_closing (S : SimpleGraph Vertex) :
    S ⊓ closing = if S.Adj (.inl 0) (.inl 3) then closing else ⊥ := by
  ext x y
  simp only [SimpleGraph.inf_adj]
  split_ifs with h
  · constructor
    · exact And.right
    · intro hc
      rcases (closing_adj_iff x y).mp hc with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ⟨h,hc⟩
      · exact ⟨h.symm,hc⟩
  · constructor
    · rintro ⟨hs,hc⟩
      rcases (closing_adj_iff x y).mp hc with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact h hs
      · exact h hs.symm
    · exact False.elim

end Erdos184Work.ChainRing
#print axioms Erdos184Work.ChainRing.block_boundary_even
#print axioms Erdos184Work.ChainRing.degree_port_split
