import Submission.CycleForestCertificate

/-! A chain of three K_(3,6) blocks and its adjacent compression.
No general bound or conjecture disproof is asserted here. -/
open SimpleGraph
namespace Erdos184Work.ChainRing
open Critical
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 10000
abbrev Vertex := Fin 7 ⊕ (Fin 3 × Fin 6)

def hubs (ring : Bool) : Fin 3 → Finset (Fin 7) :=
  if ring then ![{0,4,1},{1,5,2},{2,6,0}] else ![{0,4,1},{1,5,2},{2,6,3}]

def active (ring : Bool) (A : Fin 3 → Finset (Fin 6)) : SimpleGraph Vertex where
  Adj
    | .inl h, .inr (i,j) => j ∈ A i ∧ h ∈ hubs ring i
    | .inr (i,j), .inl h => j ∈ A i ∧ h ∈ hubs ring i
    | _, _ => False
  symm := by intro x y; cases x <;> cases y <;> simp
  loopless := by intro x; cases x <;> simp
instance (ring : Bool) (A : Fin 3 → Finset (Fin 6)) : DecidableRel (active ring A).Adj := by
  intro x y
  cases x <;> cases y <;> dsimp [active] <;> infer_instance

def initial (a : Fin 7) : Finset (Fin 6) := Finset.univ.filter (fun j => j.val < a.val)
def canonical (ring : Bool) (a : Fin 3 → Fin 7) : SimpleGraph Vertex :=
  active ring (fun i => initial (a i))
instance (ring : Bool) (a : Fin 3 → Fin 7) : DecidableRel (canonical ring a).Adj := by
  unfold canonical
  infer_instance

def base : SimpleGraph Vertex := active false (fun _ => Finset.univ)
def closing : SimpleGraph Vertex := SimpleGraph.fromRel (fun x y => x = .inl 0 ∧ y = .inl 3)
instance : DecidableRel closing.Adj := by unfold closing; infer_instance
def source : SimpleGraph Vertex := base ⊔ closing
def target : SimpleGraph Vertex := active true (fun _ => Finset.univ) ⊔ closing
instance : DecidableRel base.Adj := by unfold base; infer_instance
instance : DecidableRel source.Adj := by unfold source; infer_instance
instance : DecidableRel target.Adj := by unfold target; infer_instance

lemma card_vertex : Fintype.card Vertex = 25 := by decide
lemma hubs_card : ∀ ring i, (hubs ring i).card = 3 := by decide
lemma initial_card : ∀ a, (initial a).card = a.val := by decide
lemma source_closing : source.Adj (.inl 0) (.inl 3) := by decide
lemma target_leaf : ∀ v, target.Adj (.inl 3) v ↔ v = .inl 0 := by decide

lemma transfer_eq : Compression.transfer source (.inl 0) (.inl 3) = target := by
  ext x y
  simp only [Compression.transfer, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj,
    SimpleGraph.fromRel_adj]
  revert x y
  decide +kernel

lemma delete_closing : source.deleteEdges {s(Sum.inl 0,Sum.inl 3)} = base := by
  ext x y
  simp only [SimpleGraph.deleteEdges_adj]
  revert x y
  decide +kernel

end Erdos184Work.ChainRing
#print axioms Erdos184Work.ChainRing.transfer_eq
