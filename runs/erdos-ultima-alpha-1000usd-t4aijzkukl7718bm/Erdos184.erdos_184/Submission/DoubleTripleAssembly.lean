import Submission.DoubleTripleCertificates
import Submission.FourPointSegmentation

/-! Realizing the doubled-contact triple certificates with unrestricted
cyclic orders. No assertion about arbitrary minimal cores is made. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.DoubleTripleCertificates
open PathSubstitution CycleSegments
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
def sourceTable : Fin 27 → Fin 12 → Fin 6 := ![Layout0.src,Layout1.src,Layout2.src,Layout3.src,Layout4.src,Layout5.src,Layout6.src,Layout7.src,Layout8.src,Layout9.src,Layout10.src,Layout11.src,Layout12.src,Layout13.src,Layout14.src,Layout15.src,Layout16.src,Layout17.src,Layout18.src,Layout19.src,Layout20.src,Layout21.src,Layout22.src,Layout23.src,Layout24.src,Layout25.src,Layout26.src]
def targetTable : Fin 27 → Fin 12 → Fin 6 := ![Layout0.dst,Layout1.dst,Layout2.dst,Layout3.dst,Layout4.dst,Layout5.dst,Layout6.dst,Layout7.dst,Layout8.dst,Layout9.dst,Layout10.dst,Layout11.dst,Layout12.dst,Layout13.dst,Layout14.dst,Layout15.dst,Layout16.dst,Layout17.dst,Layout18.dst,Layout19.dst,Layout20.dst,Layout21.dst,Layout22.dst,Layout23.dst,Layout24.dst,Layout25.dst,Layout26.dst]

theorem subdivision_at_least_four {V : Type*} [Fintype V] {G : SimpleGraph V}
    (k : Fin 27) (F : Family (Fin 12) (Fin 6) G)
    (hs : F.src = sourceTable k) (ht : F.dst = targetTable k)
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ 4 ≤ D.card := by
  fin_cases k
  · exact Layout0.subdivision_at_least_four F hs ht hcover
  · exact Layout1.subdivision_at_least_four F hs ht hcover
  · exact Layout2.subdivision_at_least_four F hs ht hcover
  · exact Layout3.subdivision_at_least_four F hs ht hcover
  · exact Layout4.subdivision_at_least_four F hs ht hcover
  · exact Layout5.subdivision_at_least_four F hs ht hcover
  · exact Layout6.subdivision_at_least_four F hs ht hcover
  · exact Layout7.subdivision_at_least_four F hs ht hcover
  · exact Layout8.subdivision_at_least_four F hs ht hcover
  · exact Layout9.subdivision_at_least_four F hs ht hcover
  · exact Layout10.subdivision_at_least_four F hs ht hcover
  · exact Layout11.subdivision_at_least_four F hs ht hcover
  · exact Layout12.subdivision_at_least_four F hs ht hcover
  · exact Layout13.subdivision_at_least_four F hs ht hcover
  · exact Layout14.subdivision_at_least_four F hs ht hcover
  · exact Layout15.subdivision_at_least_four F hs ht hcover
  · exact Layout16.subdivision_at_least_four F hs ht hcover
  · exact Layout17.subdivision_at_least_four F hs ht hcover
  · exact Layout18.subdivision_at_least_four F hs ht hcover
  · exact Layout19.subdivision_at_least_four F hs ht hcover
  · exact Layout20.subdivision_at_least_four F hs ht hcover
  · exact Layout21.subdivision_at_least_four F hs ht hcover
  · exact Layout22.subdivision_at_least_four F hs ht hcover
  · exact Layout23.subdivision_at_least_four F hs ht hcover
  · exact Layout24.subdivision_at_least_four F hs ht hcover
  · exact Layout25.subdivision_at_least_four F hs ht hcover
  · exact Layout26.subdivision_at_least_four F hs ht hcover

def place : Fin 3 → Fin 4 → Fin 6 := ![![0,1,2,3],![0,1,4,5],![2,3,4,5]]
def chosenPlace (o : Fin 3 → Fin 3) (k : Fin 3) : Fin 4 → Fin 6 :=
  fourOrder (place k 0) (place k 1) (place k 2) (place k 3) (o k)
lemma chosenPlace_range : ∀ o k w, (∃ i, chosenPlace o k i = w) ↔ ∃ i, place k i = w := by decide
lemma chosenPlace_ne : ∀ o k i, chosenPlace o k (src4 i) ≠ chosenPlace o k (dst4 i) := by decide
lemma src4_surjective : Function.Surjective src4 := by decide

def location : Fin 12 → (Σ _k : Fin 3, Fin 4) := ![⟨0,0⟩,⟨0,1⟩,⟨0,2⟩,⟨0,3⟩,⟨1,0⟩,⟨1,1⟩,⟨1,2⟩,⟨1,3⟩,⟨2,0⟩,⟨2,1⟩,⟨2,2⟩,⟨2,3⟩]
lemma location_bijective : Function.Bijective location := by decide
noncomputable def locationEquiv := Equiv.ofBijective location location_bijective

def layoutIndex (o : Fin 3 → Fin 3) : Fin 27 :=
  ⟨9 * (o 0).val + 3 * (o 1).val + (o 2).val,by have := (o 0).isLt; have := (o 1).isLt; have := (o 2).isLt; omega⟩
lemma source_match : ∀ o j, chosenPlace o (location j).1 (src4 (location j).2) = sourceTable (layoutIndex o) j := by decide
lemma target_match : ∀ o j, chosenPlace o (location j).1 (dst4 (location j).2) = targetTable (layoutIndex o) j := by decide

lemma assembled_at_least_four {V : Type*} [Fintype V] {G : SimpleGraph V}
    (o : Fin 3 → Fin 3) (vertex : Fin 6 → V) (hinj : Function.Injective vertex)
    (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (S : ∀ k, Segmentation (C k) (vertex ∘ chosenPlace o k) src4 dst4)
    (hdisC : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hpoints : ∀ w k, vertex w ∈ (C k).support → ∃ i, chosenPlace o k i = w)
    (hmeet : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ w, vertex w = x)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ 4 ≤ D.card := by
  let F := assemble_segments (fun _ : Fin 3 => 4) vertex hinj (chosenPlace o)
    (fun _ => src4) (fun _ => dst4) (chosenPlace_ne o) (fun _ => src4_surjective)
    root C hC S hdisC hpoints hmeet
  apply subdivision_at_least_four (layoutIndex o) (reindexFamily F locationEquiv)
  · funext j
    exact source_match o j
  · funext j
    exact target_match o j
  · intro x y hxy
    obtain ⟨j,hj⟩ := assemble_segments_cover (fun _ : Fin 3 => 4) vertex hinj (chosenPlace o)
      (fun _ => src4) (fun _ => dst4) (chosenPlace_ne o) (fun _ => src4_surjective)
      root C hC S hdisC hpoints hmeet hcover x y hxy
    refine ⟨locationEquiv.symm j,?_⟩
    change s(x,y) ∈ (F.path (locationEquiv (locationEquiv.symm j))).edges
    have he := congrArg (fun j => (F.path j).edges) (locationEquiv.apply_symm_apply j)
    dsimp only at he
    rw [he]
    exact hj

lemma fourOrder_comp {V : Type*} (vertex : Fin 6 → V) (o : Fin 3 → Fin 3) (k : Fin 3) :
    vertex ∘ chosenPlace o k =
      fourOrder (vertex (place k 0)) (vertex (place k 1)) (vertex (place k 2)) (vertex (place k 3)) (o k) := by
  funext i
  dsimp only [chosenPlace]
  generalize o k = j
  fin_cases j <;> fin_cases i <;> rfl

lemma contact_at_least_four {V : Type*} [Fintype V] {G : SimpleGraph V}
    (vertex : Fin 6 → V) (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k))
    (hC : ∀ k, (C k).IsCycle) (L : ContactLayout (fun _ : Fin 3 => 4) place vertex root C)
    (hdisC : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ 4 ≤ D.card := by
  have hp (k : Fin 3) (i : Fin 4) : vertex (place k i) ∈ (C k).support := L.mem ⟨i,rfl⟩
  have hs (k : Fin 3) := four_segments_orders_any (C k) (hC k)
    (hp k 0) (hp k 1) (hp k 2) (hp k 3) (L.ne (by fin_cases k <;> decide))
  choose o ho using hs
  have hS (k : Fin 3) : Nonempty (Segmentation (C k) (vertex ∘ chosenPlace o k) src4 dst4) := by
    rw [fourOrder_comp]
    exact ho k
  let S (k : Fin 3) := Classical.choice (hS k)
  apply assembled_at_least_four o vertex L.injective root C hC S hdisC _ L.meet hcover
  intro w k hw
  exact (chosenPlace_range o k w).mpr ((L.points k w).mp hw)

#print axioms contact_at_least_four
end Erdos184Work.DoubleTripleCertificates
