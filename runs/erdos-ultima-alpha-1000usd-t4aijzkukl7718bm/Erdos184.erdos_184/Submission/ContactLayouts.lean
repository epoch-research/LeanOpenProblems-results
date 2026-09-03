import Submission.JunctionAssembly

/-! Extracting the canonical junction layouts from unrooted cycle contacts. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.CycleSegments
open RigidSwitching
set_option maxHeartbeats 1500000
variable {V W J : Type*} {G : SimpleGraph V}

/-- Segmentation depends on the edges, not on the root of the closed walk. -/
def Segmentation.transfer {a b : V} {c : G.Walk a a} {d : G.Walk b b}
    {vertex : W → V} {src dst : J → W} (S : Segmentation c vertex src dst)
    (he : ∀ e, e ∈ c.edges ↔ e ∈ d.edges) : Segmentation d vertex src dst where
  path := S.path
  isPath := S.isPath
  disjoint := S.disjoint
  cover e := (he e).symm.trans (S.cover e)

lemma two_segments_any {a u v : V} (c : G.Walk a a) (hc : c.IsCycle)
    (hu : u ∈ c.support) (hv : v ∈ c.support) (huv : u ≠ v) :
    Nonempty (Segmentation c ![u,v] src2 dst2) := by
  obtain ⟨S⟩ := two_segments (c.rotate hu) (hc.rotate hu)
    ((c.mem_support_rotate_iff hu).mpr hv) huv
  exact ⟨S.transfer (fun e => (c.rotate_edges hu).mem_iff)⟩

lemma three_segments_any {a u v w : V} (c : G.Walk a a) (hc : c.IsCycle)
    (hu : u ∈ c.support) (hv : v ∈ c.support) (hw : w ∈ c.support) (huv : u ≠ v) :
    Nonempty (Segmentation c ![u,v,w] src3 dst3) := by
  obtain ⟨S⟩ := three_segments (c.rotate hu) (hc.rotate hu)
    ((c.mem_support_rotate_iff hu).mpr hv) ((c.mem_support_rotate_iff hu).mpr hw) huv
  exact ⟨S.transfer (fun e => (c.rotate_edges hu).mem_iff)⟩

lemma four_segments_of_rigid_any [Fintype V] (hrig : Rigidity.CycleRigid G)
    (heven : ∀ v, Even (G.degree v))
    {a b w u v x z : V} {c : G.Walk a a} {d : G.Walk b b} {t : G.Walk w w}
    (hc : c.IsCycle) (hd : d.IsCycle) (ht : t.IsCycle) (huv : u ≠ v)
    (huc : u ∈ c.support) (hud : u ∈ d.support)
    (hvc : v ∈ c.support) (hvd : v ∈ d.support)
    (hcd : c.edges.Disjoint d.edges) (hct : c.edges.Disjoint t.edges) (hdt : d.edges.Disjoint t.edges)
    (hinter : ∀ y, y ∈ c.support → y ∈ d.support → y = u ∨ y = v)
    (hut : u ∉ t.support) (hvt : v ∉ t.support)
    (hmeet : ∃ y, y ∈ d.support ∧ y ∈ t.support)
    (hxz : x ≠ z) (hxc : x ∈ c.support) (hzc : z ∈ c.support)
    (hxt : x ∈ t.support) (hzt : z ∈ t.support) :
    Nonempty (Segmentation c ![u,x,v,z] src4 dst4) := by
  have ec (e) : e ∈ (c.rotate huc).edges ↔ e ∈ c.edges := (c.rotate_edges huc).mem_iff
  have ed (e) : e ∈ (d.rotate hud).edges ↔ e ∈ d.edges := (d.rotate_edges hud).mem_iff
  have sc (y) : y ∈ (c.rotate huc).support ↔ y ∈ c.support := c.mem_support_rotate_iff huc
  have sd (y) : y ∈ (d.rotate hud).support ↔ y ∈ d.support := d.mem_support_rotate_iff hud
  obtain ⟨S⟩ := four_segments_of_rigid hrig heven (hc.rotate huc) (hd.rotate hud) ht huv
    ((sc v).mpr hvc) ((sd v).mpr hvd)
    (disjoint_mono hcd (fun e => (ec e).mp) (fun e => (ed e).mp))
    (disjoint_mono hct (fun e => (ec e).mp) (List.Subset.refl _))
    (disjoint_mono hdt (fun e => (ed e).mp) (List.Subset.refl _))
    (fun y hy hz => hinter y ((sc y).mp hy) ((sd y).mp hz)) hut hvt
    (hmeet.imp (fun y h => ⟨(sd y).mpr h.1,h.2⟩)) hxz ((sc x).mpr hxc) ((sc z).mpr hzc) hxt hzt
  exact ⟨S.transfer ec⟩

#print axioms four_segments_of_rigid_any
end Erdos184Work.CycleSegments

namespace Erdos184Work.CycleSegments
variable {V W K : Type*} {G : SimpleGraph V}

/-- An injective list of all junction vertices, with their exact piece incidences. -/
structure ContactLayout (m : K → ℕ) (place : ∀ k, Fin (m k) → W)
    (vertex : W → V) (root : K → V) (C : ∀ k, G.Walk (root k) (root k)) : Prop where
  injective : Function.Injective vertex
  points : ∀ k w, vertex w ∈ (C k).support ↔ ∃ i, place k i = w
  meet : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ w, vertex w = x

namespace ContactLayout
variable {m : K → ℕ} {place : ∀ k, Fin (m k) → W}
    {vertex : W → V} {root : K → V} {C : ∀ k, G.Walk (root k) (root k)}
    (L : ContactLayout m place vertex root C)
include L
lemma mem {k : K} {w : W} (h : ∃ i, place k i = w) : vertex w ∈ (C k).support :=
  (L.points k w).mpr h
lemma not_mem {k : K} {w : W} (h : ¬ ∃ i, place k i = w) : vertex w ∉ (C k).support :=
  fun hw => h ((L.points k w).mp hw)
lemma ne {w z : W} (h : w ≠ z) : vertex w ≠ vertex z := fun he => h (L.injective he)
lemma inter_two {k l : K} {u v : W} (hkl : k ≠ l)
    (h : ∀ w, (∃ i, place k i = w) → (∃ j, place l j = w) → w = u ∨ w = v)
    (x : V) (hx : x ∈ (C k).support) (hy : x ∈ (C l).support) :
    x = vertex u ∨ x = vertex v := by
  obtain ⟨w,rfl⟩ := L.meet k l hkl x hx hy
  exact (h w ((L.points k w).mp hx) ((L.points l w).mp hy)).imp (congrArg vertex) (congrArg vertex)
end ContactLayout
end Erdos184Work.CycleSegments
-- Generated layout extraction
namespace Erdos184Work.ThreeCycleKernels
open CycleSegments
set_option maxHeartbeats 1500000
namespace DoubleTriangle
lemma contact_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (vertex : Fin 3 → V) (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k))
    (hC : ∀ k, (C k).IsCycle) (L : ContactLayout sizes place vertex root C)
    (hdisC : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges) : Critical.number G ≤ 2 := by
  have hs0 : Nonempty (Segmentation (C 0) (vertex ∘ place 0) (localSrc 0) (localDst 0)) := by
    have hv : vertex ∘ place 0 = ![vertex 0,vertex 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    change Nonempty (Segmentation (C 0) ![vertex 0,vertex 1] src2 dst2)
    exact two_segments_any (C 0) (hC 0) (L.mem (k := 0) (w := 0) (by decide)) (L.mem (k := 0) (w := 1) (by decide)) (L.ne (by decide : (0 : Fin 3) ≠ 1))
  have hs1 : Nonempty (Segmentation (C 1) (vertex ∘ place 1) (localSrc 1) (localDst 1)) := by
    have hv : vertex ∘ place 1 = ![vertex 0,vertex 2] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    change Nonempty (Segmentation (C 1) ![vertex 0,vertex 2] src2 dst2)
    exact two_segments_any (C 1) (hC 1) (L.mem (k := 1) (w := 0) (by decide)) (L.mem (k := 1) (w := 2) (by decide)) (L.ne (by decide : (0 : Fin 3) ≠ 2))
  have hs2 : Nonempty (Segmentation (C 2) (vertex ∘ place 2) (localSrc 2) (localDst 2)) := by
    have hv : vertex ∘ place 2 = ![vertex 1,vertex 2] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    change Nonempty (Segmentation (C 2) ![vertex 1,vertex 2] src2 dst2)
    exact two_segments_any (C 2) (hC 2) (L.mem (k := 2) (w := 1) (by decide)) (L.mem (k := 2) (w := 2) (by decide)) (L.ne (by decide : (1 : Fin 3) ≠ 2))
  obtain ⟨S0⟩ := hs0
  obtain ⟨S1⟩ := hs1
  obtain ⟨S2⟩ := hs2
  let S : ∀ k, Segmentation (C k) (vertex ∘ place k) (localSrc k) (localDst k) :=
    Fin.cases S0 (Fin.cases S1 (Fin.cases S2 (fun i => Fin.elim0 i)))
  exact assembled_number_le_two vertex L.injective root C hC S hdisC
    (fun w k => (L.points k w).mp) L.meet hcover
#print axioms contact_number_le_two
end DoubleTriangle

namespace MatchedFour
lemma contact_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (vertex : Fin 4 → V) (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k))
    (hC : ∀ k, (C k).IsCycle) (L : ContactLayout sizes place vertex root C)
    (hdisC : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges) : Critical.number G ≤ 2 := by
  have hs0 : Nonempty (Segmentation (C 0) (vertex ∘ place 0) (localSrc 0) (localDst 0)) := by
    have hv : vertex ∘ place 0 = ![vertex 0,vertex 1,vertex 2] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    change Nonempty (Segmentation (C 0) ![vertex 0,vertex 1,vertex 2] src3 dst3)
    exact three_segments_any (C 0) (hC 0) (L.mem (k := 0) (w := 0) (by decide)) (L.mem (k := 0) (w := 1) (by decide)) (L.mem (k := 0) (w := 2) (by decide)) (L.ne (by decide : (0 : Fin 4) ≠ 1))
  have hs1 : Nonempty (Segmentation (C 1) (vertex ∘ place 1) (localSrc 1) (localDst 1)) := by
    have hv : vertex ∘ place 1 = ![vertex 0,vertex 1,vertex 3] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    change Nonempty (Segmentation (C 1) ![vertex 0,vertex 1,vertex 3] src3 dst3)
    exact three_segments_any (C 1) (hC 1) (L.mem (k := 1) (w := 0) (by decide)) (L.mem (k := 1) (w := 1) (by decide)) (L.mem (k := 1) (w := 3) (by decide)) (L.ne (by decide : (0 : Fin 4) ≠ 1))
  have hs2 : Nonempty (Segmentation (C 2) (vertex ∘ place 2) (localSrc 2) (localDst 2)) := by
    have hv : vertex ∘ place 2 = ![vertex 2,vertex 3] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    change Nonempty (Segmentation (C 2) ![vertex 2,vertex 3] src2 dst2)
    exact two_segments_any (C 2) (hC 2) (L.mem (k := 2) (w := 2) (by decide)) (L.mem (k := 2) (w := 3) (by decide)) (L.ne (by decide : (2 : Fin 4) ≠ 3))
  obtain ⟨S0⟩ := hs0
  obtain ⟨S1⟩ := hs1
  obtain ⟨S2⟩ := hs2
  let S : ∀ k, Segmentation (C k) (vertex ∘ place k) (localSrc k) (localDst k) :=
    Fin.cases S0 (Fin.cases S1 (Fin.cases S2 (fun i => Fin.elim0 i)))
  exact assembled_number_le_two vertex L.injective root C hC S hdisC
    (fun w k => (L.points k w).mp) L.meet hcover
#print axioms contact_number_le_two
end MatchedFour

namespace CompleteFive
lemma contact_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (vertex : Fin 5 → V) (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k))
    (hC : ∀ k, (C k).IsCycle) (L : ContactLayout sizes place vertex root C)
    (hdisC : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges) : Critical.number G ≤ 2 := by
  have hs0 : Nonempty (Segmentation (C 0) (vertex ∘ place 0) (localSrc 0) (localDst 0)) := by
    have hv : vertex ∘ place 0 = ![vertex 0,vertex 2,vertex 1,vertex 3] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    change Nonempty (Segmentation (C 0) ![vertex 0,vertex 2,vertex 1,vertex 3] src4 dst4)
    exact four_segments_of_rigid_any hrig heven (hC 0) (hC 1) (hC 2)
      (L.ne (by decide : (0 : Fin 5) ≠ 1))
      (L.mem (k := 0) (w := 0) (by decide)) (L.mem (k := 1) (w := 0) (by decide)) (L.mem (k := 0) (w := 1) (by decide)) (L.mem (k := 1) (w := 1) (by decide))
      (hdisC 0 1 (by decide)) (hdisC 0 2 (by decide)) (hdisC 1 2 (by decide))
      (L.inter_two (k := 0) (l := 1) (u := 0) (v := 1) (by decide) (by decide))
      (L.not_mem (k := 2) (w := 0) (by decide)) (L.not_mem (k := 2) (w := 1) (by decide))
      ⟨vertex 4,(L.mem (k := 1) (w := 4) (by decide)),(L.mem (k := 2) (w := 4) (by decide))⟩
      (L.ne (by decide : (2 : Fin 5) ≠ 3))
      (L.mem (k := 0) (w := 2) (by decide)) (L.mem (k := 0) (w := 3) (by decide)) (L.mem (k := 2) (w := 2) (by decide)) (L.mem (k := 2) (w := 3) (by decide))
  have hs1 : Nonempty (Segmentation (C 1) (vertex ∘ place 1) (localSrc 1) (localDst 1)) := by
    have hv : vertex ∘ place 1 = ![vertex 0,vertex 1,vertex 4] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    change Nonempty (Segmentation (C 1) ![vertex 0,vertex 1,vertex 4] src3 dst3)
    exact three_segments_any (C 1) (hC 1) (L.mem (k := 1) (w := 0) (by decide)) (L.mem (k := 1) (w := 1) (by decide)) (L.mem (k := 1) (w := 4) (by decide)) (L.ne (by decide : (0 : Fin 5) ≠ 1))
  have hs2 : Nonempty (Segmentation (C 2) (vertex ∘ place 2) (localSrc 2) (localDst 2)) := by
    have hv : vertex ∘ place 2 = ![vertex 2,vertex 3,vertex 4] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    change Nonempty (Segmentation (C 2) ![vertex 2,vertex 3,vertex 4] src3 dst3)
    exact three_segments_any (C 2) (hC 2) (L.mem (k := 2) (w := 2) (by decide)) (L.mem (k := 2) (w := 3) (by decide)) (L.mem (k := 2) (w := 4) (by decide)) (L.ne (by decide : (2 : Fin 5) ≠ 3))
  obtain ⟨S0⟩ := hs0
  obtain ⟨S1⟩ := hs1
  obtain ⟨S2⟩ := hs2
  let S : ∀ k, Segmentation (C k) (vertex ∘ place k) (localSrc k) (localDst k) :=
    Fin.cases S0 (Fin.cases S1 (Fin.cases S2 (fun i => Fin.elim0 i)))
  exact assembled_number_le_two vertex L.injective root C hC S hdisC
    (fun w k => (L.points k w).mp) L.meet hcover
#print axioms contact_number_le_two
end CompleteFive

namespace Octahedron
lemma contact_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    (vertex : Fin 6 → V) (root : Fin 3 → V) (C : ∀ k, G.Walk (root k) (root k))
    (hC : ∀ k, (C k).IsCycle) (L : ContactLayout sizes place vertex root C)
    (hdisC : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges) : Critical.number G ≤ 2 := by
  have hs0 : Nonempty (Segmentation (C 0) (vertex ∘ place 0) (localSrc 0) (localDst 0)) := by
    have hv : vertex ∘ place 0 = ![vertex 0,vertex 2,vertex 1,vertex 3] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    change Nonempty (Segmentation (C 0) ![vertex 0,vertex 2,vertex 1,vertex 3] src4 dst4)
    exact four_segments_of_rigid_any hrig heven (hC 0) (hC 1) (hC 2)
      (L.ne (by decide : (0 : Fin 6) ≠ 1))
      (L.mem (k := 0) (w := 0) (by decide)) (L.mem (k := 1) (w := 0) (by decide)) (L.mem (k := 0) (w := 1) (by decide)) (L.mem (k := 1) (w := 1) (by decide))
      (hdisC 0 1 (by decide)) (hdisC 0 2 (by decide)) (hdisC 1 2 (by decide))
      (L.inter_two (k := 0) (l := 1) (u := 0) (v := 1) (by decide) (by decide))
      (L.not_mem (k := 2) (w := 0) (by decide)) (L.not_mem (k := 2) (w := 1) (by decide))
      ⟨vertex 4,(L.mem (k := 1) (w := 4) (by decide)),(L.mem (k := 2) (w := 4) (by decide))⟩
      (L.ne (by decide : (2 : Fin 6) ≠ 3))
      (L.mem (k := 0) (w := 2) (by decide)) (L.mem (k := 0) (w := 3) (by decide)) (L.mem (k := 2) (w := 2) (by decide)) (L.mem (k := 2) (w := 3) (by decide))
  have hs1 : Nonempty (Segmentation (C 1) (vertex ∘ place 1) (localSrc 1) (localDst 1)) := by
    have hv : vertex ∘ place 1 = ![vertex 0,vertex 4,vertex 1,vertex 5] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    change Nonempty (Segmentation (C 1) ![vertex 0,vertex 4,vertex 1,vertex 5] src4 dst4)
    exact four_segments_of_rigid_any hrig heven (hC 1) (hC 0) (hC 2)
      (L.ne (by decide : (0 : Fin 6) ≠ 1))
      (L.mem (k := 1) (w := 0) (by decide)) (L.mem (k := 0) (w := 0) (by decide)) (L.mem (k := 1) (w := 1) (by decide)) (L.mem (k := 0) (w := 1) (by decide))
      (hdisC 1 0 (by decide)) (hdisC 1 2 (by decide)) (hdisC 0 2 (by decide))
      (L.inter_two (k := 1) (l := 0) (u := 0) (v := 1) (by decide) (by decide))
      (L.not_mem (k := 2) (w := 0) (by decide)) (L.not_mem (k := 2) (w := 1) (by decide))
      ⟨vertex 2,(L.mem (k := 0) (w := 2) (by decide)),(L.mem (k := 2) (w := 2) (by decide))⟩
      (L.ne (by decide : (4 : Fin 6) ≠ 5))
      (L.mem (k := 1) (w := 4) (by decide)) (L.mem (k := 1) (w := 5) (by decide)) (L.mem (k := 2) (w := 4) (by decide)) (L.mem (k := 2) (w := 5) (by decide))
  have hs2 : Nonempty (Segmentation (C 2) (vertex ∘ place 2) (localSrc 2) (localDst 2)) := by
    have hv : vertex ∘ place 2 = ![vertex 2,vertex 4,vertex 3,vertex 5] := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    change Nonempty (Segmentation (C 2) ![vertex 2,vertex 4,vertex 3,vertex 5] src4 dst4)
    exact four_segments_of_rigid_any hrig heven (hC 2) (hC 0) (hC 1)
      (L.ne (by decide : (2 : Fin 6) ≠ 3))
      (L.mem (k := 2) (w := 2) (by decide)) (L.mem (k := 0) (w := 2) (by decide)) (L.mem (k := 2) (w := 3) (by decide)) (L.mem (k := 0) (w := 3) (by decide))
      (hdisC 2 0 (by decide)) (hdisC 2 1 (by decide)) (hdisC 0 1 (by decide))
      (L.inter_two (k := 2) (l := 0) (u := 2) (v := 3) (by decide) (by decide))
      (L.not_mem (k := 1) (w := 2) (by decide)) (L.not_mem (k := 1) (w := 3) (by decide))
      ⟨vertex 0,(L.mem (k := 0) (w := 0) (by decide)),(L.mem (k := 1) (w := 0) (by decide))⟩
      (L.ne (by decide : (4 : Fin 6) ≠ 5))
      (L.mem (k := 2) (w := 4) (by decide)) (L.mem (k := 2) (w := 5) (by decide)) (L.mem (k := 1) (w := 4) (by decide)) (L.mem (k := 1) (w := 5) (by decide))
  obtain ⟨S0⟩ := hs0
  obtain ⟨S1⟩ := hs1
  obtain ⟨S2⟩ := hs2
  let S : ∀ k, Segmentation (C k) (vertex ∘ place k) (localSrc k) (localDst k) :=
    Fin.cases S0 (Fin.cases S1 (Fin.cases S2 (fun i => Fin.elim0 i)))
  exact assembled_number_le_two vertex L.injective root C hC S hdisC
    (fun w k => (L.points k w).mp) L.meet hcover
#print axioms contact_number_le_two
end Octahedron

end Erdos184Work.ThreeCycleKernels
