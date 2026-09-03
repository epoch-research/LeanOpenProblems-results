import Submission.RigidSwitching

/-! Building path-substitution models from segments of edge-disjoint cycles. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.CycleSegments
open PathSubstitution RigidSwitching
set_option maxHeartbeats 1500000

variable {V W J K : Type*} {G : SimpleGraph V}

lemma support_subset_of_edges_subset {a b c d : V} (p : G.Walk a b) (q : G.Walk c d)
    (hp : ¬ p.Nil) (he : p.edges ⊆ q.edges) : p.support ⊆ q.support := by
  intro x hx
  obtain ⟨e,hep,hxe⟩ := (Walk.mem_support_iff_exists_mem_edges_of_not_nil hp).mp hx
  exact Walk.mem_support_of_mem_edges (he hep) hxe

lemma paths_in_cycle_support_inter [Fintype V]
    {u a b d e : V} (c : G.Walk u u) (hc : c.IsCycle)
    (p : G.Walk a b) (q : G.Walk d e) (hp : p.IsPath) (hq : ¬ q.Nil)
    (hpc : p.edges ⊆ c.edges) (hqc : q.edges ⊆ c.edges)
    (hpq : p.edges.Disjoint q.edges) (x : V) (hxp : x ∈ p.support) (hxq : x ∈ q.support) :
    x = a ∨ x = b := by
  by_contra hx
  have hxa : x ≠ a := fun h => hx (Or.inl h)
  have hxb : x ≠ b := fun h => hx (Or.inr h)
  obtain ⟨i,hi,hil⟩ := Walk.mem_support_iff_exists_getVert.mp hxp
  have hi0 : i ≠ 0 := by rintro rfl; exact hxa (by simpa using hi.symm)
  have hil' : i < p.length := by
    by_contra hn
    have he : i = p.length := by omega
    exact hxb (by simpa [he] using hi.symm)
  obtain ⟨e,heq,hxe⟩ := (Walk.mem_support_iff_exists_mem_edges_of_not_nil hq).mp hxq
  obtain ⟨y,hey⟩ := Sym2.mem_iff_exists.mp hxe
  subst e
  have hxc : x ∈ c.support := c.fst_mem_support_of_mem_edges (hqc heq)
  have hcardp : (p.toSubgraph.neighborSet x).ncard = 2 := by
    rw [← hi]
    exact hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hil'
  have hcardc := hc.ncard_neighborSet_toSubgraph_eq_two hxc
  have hsub : p.toSubgraph.neighborSet x ⊆ c.toSubgraph.neighborSet x := by
    intro z hz
    exact c.mem_edges_toSubgraph.mpr (hpc (p.mem_edges_toSubgraph.mp (show s(x,z) ∈ p.toSubgraph.edgeSet from hz)))
  have hEq : p.toSubgraph.neighborSet x = c.toSubgraph.neighborSet x :=
    Set.eq_of_subset_of_ncard_le hsub (by omega)
  have hyc : y ∈ c.toSubgraph.neighborSet x := c.mem_edges_toSubgraph.mpr (hqc heq)
  have hyp : y ∈ p.toSubgraph.neighborSet x := hEq ▸ hyc
  exact List.disjoint_left.mp hpq (p.mem_edges_toSubgraph.mp hyp) heq

/-- Only edge partition data are needed: degree two on each original cycle
forces the required internal vertex disjointness automatically. -/
noncomputable def family_of_cycle_segments [Fintype V]
    (vertex : W → V) (hinj : Function.Injective vertex) (src dst : J → W)
    (hne : ∀ j, src j ≠ dst j)
    (P : ∀ j, G.Walk (vertex (src j)) (vertex (dst j)))
    (hP : ∀ j, (P j).IsPath)
    (root : K → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (color : J → K) (hPC : ∀ j, (P j).edges ⊆ (C (color j)).edges)
    (hdis : ∀ i j, i ≠ j → (P i).edges.Disjoint (P j).edges)
    (hincident : ∀ w k, vertex w ∈ (C k).support →
      ∃ j, color j = k ∧ (w = src j ∨ w = dst j))
    (hmeet : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support →
      ∃ w, vertex w = x) : Family J W G := by
  have hnotnil (j : J) : ¬ (P j).Nil := Walk.not_nil_of_ne (fun h => hne j (hinj h))
  have hsupport (j : J) : (P j).support ⊆ (C (color j)).support :=
    support_subset_of_edges_subset _ _ (hnotnil j) (hPC j)
  have hsame (i j : J) (hij : i ≠ j) (hcolor : color i = color j) (x : V)
      (hxi : x ∈ (P i).support) (hxj : x ∈ (P j).support) :
      x = vertex (src i) ∨ x = vertex (dst i) := by
    apply paths_in_cycle_support_inter (C (color i)) (hC _) (P i) (P j) (hP i) (hnotnil j)
      (hPC i) _ (hdis i j hij) x hxi hxj
    have he := congrArg (fun k => (C k).edges) hcolor.symm
    intro e hep
    dsimp only at he
    rw [← he]
    exact hPC j hep
  have hvmem (j : J) (w : W) : vertex w ∈ (P j).support ↔ w = src j ∨ w = dst j := by
    constructor
    · intro hw
      obtain ⟨i,hcolor,hwi⟩ := hincident w (color j) (hsupport j hw)
      by_cases hij : j = i
      · simpa only [← hij] using hwi
      have hwiP : vertex w ∈ (P i).support := by
        rcases hwi with rfl | rfl <;> simp
      exact (hsame j i hij hcolor.symm (vertex w) hw hwiP).imp (fun h => hinj h) (fun h => hinj h)
    · rintro (rfl | rfl) <;> simp
  refine ⟨vertex,hinj,src,dst,hne,P,hP,hvmem,hdis,?_⟩
  intro i j hij x hxi hxj
  by_cases hcolor : color i = color j
  · exact hsame i j hij hcolor x hxi hxj
  · obtain ⟨w,rfl⟩ := hmeet (color i) (color j) hcolor x (hsupport i hxi) (hsupport j hxj)
    exact ((hvmem i w).mp hxi).imp (congrArg vertex) (congrArg vertex)

lemma disjoint_mono {α : Type*} {A B C D : List α} (h : C.Disjoint D) (hA : A ⊆ C) (hB : B ⊆ D) :
    A.Disjoint B := by
  apply List.disjoint_left.mpr
  intro x hx hy
  exact List.disjoint_left.mp h (hA hx) (hB hy)

structure PathParts {u v : V} (p : G.Walk u v) (w : V) where
  first : G.Walk u w
  last : G.Walk w v
  first_path : first.IsPath
  last_path : last.IsPath
  edges_disjoint : first.edges.Disjoint last.edges
  edges_cover : ∀ e, (e ∈ first.edges ∨ e ∈ last.edges) ↔ e ∈ p.edges

lemma exists_pathParts {u v w : V} (p : G.Walk u v) (hp : p.IsPath) (hw : w ∈ p.support) :
    Nonempty (PathParts p w) := by
  refine ⟨⟨p.takeUntil w hw,p.dropUntil w hw,hp.takeUntil hw,hp.dropUntil hw,
    hp.isTrail.disjoint_edges_takeUntil_dropUntil hw,?_⟩⟩
  intro e
  rw [← List.mem_append,← Walk.edges_append,Walk.take_spec]

namespace PathParts
variable {u v w : V} {p : G.Walk u v}
lemma first_edges_subset (P : PathParts p w) : P.first.edges ⊆ p.edges :=
  fun e he => (P.edges_cover e).mp (Or.inl he)
lemma last_edges_subset (P : PathParts p w) : P.last.edges ⊆ p.edges :=
  fun e he => (P.edges_cover e).mp (Or.inr he)
end PathParts

/-- A finite collection of paths partitioning one cycle. -/
structure Segmentation {u : V} (c : G.Walk u u) (vertex : W → V) (src dst : J → W) where
  path : ∀ j, G.Walk (vertex (src j)) (vertex (dst j))
  isPath : ∀ j, (path j).IsPath
  disjoint : ∀ i j, i ≠ j → (path i).edges.Disjoint (path j).edges
  cover : ∀ e, e ∈ c.edges ↔ ∃ j, e ∈ (path j).edges

namespace Segmentation
variable {u : V} {c : G.Walk u u} {vertex : W → V} {src dst : J → W}
lemma edges_subset (S : Segmentation c vertex src dst) (j : J) : (S.path j).edges ⊆ c.edges :=
  fun e he => (S.cover e).mpr ⟨j,he⟩
end Segmentation

def src2 : Fin 2 → Fin 2 := ![0,1]
def dst2 : Fin 2 → Fin 2 := ![1,0]
def src3 : Fin 3 → Fin 3 := ![0,1,2]
def dst3 : Fin 3 → Fin 3 := ![1,2,0]
def src4 : Fin 4 → Fin 4 := ![0,1,2,3]
def dst4 : Fin 4 → Fin 4 := ![1,2,3,0]

lemma two_segments {u v : V} (c : G.Walk u u) (hc : c.IsCycle)
    (hv : v ∈ c.support) (huv : u ≠ v) :
    Nonempty (Segmentation c ![u,v] src2 dst2) := by
  obtain ⟨P⟩ := exists_cyclePaths c hc hv huv
  let paths : ∀ i : Fin 2, G.Walk (![u,v] (src2 i)) (![u,v] (dst2 i)) :=
    Fin.cases P.left (Fin.cases P.right.reverse (fun i => Fin.elim0 i))
  refine ⟨⟨paths,?_,?_,?_⟩⟩
  · intro i
    fin_cases i
    · exact P.left_path
    · exact P.right_path.reverse
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change P.left.edges.Disjoint P.right.reverse.edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_right] using P.edges_disjoint
    · change P.right.reverse.edges.Disjoint P.left.edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left] using P.edges_disjoint.symm
    · exact (hij rfl).elim
  · intro e
    rw [Fin.exists_fin_two]
    change e ∈ c.edges ↔ e ∈ P.left.edges ∨ e ∈ P.right.reverse.edges
    simpa only [Walk.edges_reverse,List.mem_reverse] using (P.edges_cover e).symm

lemma three_segments {u v w : V} (c : G.Walk u u) (hc : c.IsCycle)
    (hv : v ∈ c.support) (hw : w ∈ c.support) (huv : u ≠ v) :
    Nonempty (Segmentation c ![u,v,w] src3 dst3) := by
  obtain ⟨P⟩ := exists_cyclePaths c hc hv huv
  obtain ⟨P,hwP⟩ := P.exists_left_through hw
  obtain ⟨L⟩ := exists_pathParts P.left P.left_path hwP
  let paths : ∀ i : Fin 3, G.Walk (![u,v,w] (src3 i)) (![u,v,w] (dst3 i)) :=
    Fin.cases P.right (Fin.cases L.last.reverse (Fin.cases L.first.reverse (fun i => Fin.elim0 i)))
  have h01 : P.right.edges.Disjoint L.last.edges :=
    disjoint_mono P.edges_disjoint.symm (List.Subset.refl _) L.last_edges_subset
  have h02 : P.right.edges.Disjoint L.first.edges :=
    disjoint_mono P.edges_disjoint.symm (List.Subset.refl _) L.first_edges_subset
  have h12 : L.last.edges.Disjoint L.first.edges := L.edges_disjoint.symm
  refine ⟨⟨paths,?_,?_,?_⟩⟩
  · intro i
    fin_cases i
    · exact P.right_path
    · exact L.last_path.reverse
    · exact L.first_path.reverse
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change (P.right).edges.Disjoint (L.last.reverse).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h01
    · change (P.right).edges.Disjoint (L.first.reverse).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h02
    · change (L.last.reverse).edges.Disjoint (P.right).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h01.symm
    · exact (hij rfl).elim
    · change (L.last.reverse).edges.Disjoint (L.first.reverse).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h12
    · change (L.first.reverse).edges.Disjoint (P.right).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h02.symm
    · change (L.first.reverse).edges.Disjoint (L.last.reverse).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h12.symm
    · exact (hij rfl).elim
  · intro e
    rw [Fin.exists_fin_succ,Fin.exists_fin_two]
    change e ∈ c.edges ↔ e ∈ P.right.edges ∨ e ∈ L.last.reverse.edges ∨ e ∈ L.first.reverse.edges
    simp only [Walk.edges_reverse,List.mem_reverse]
    rw [← P.edges_cover e,← L.edges_cover e]
    tauto

lemma four_segments_of_paths {u v x y : V} {c : G.Walk u u}
    (P : CyclePaths c v) (hx : x ∈ P.left.support) (hy : y ∈ P.right.support) :
    Nonempty (Segmentation c ![u,x,v,y] src4 dst4) := by
  obtain ⟨L⟩ := exists_pathParts P.left P.left_path hx
  obtain ⟨R⟩ := exists_pathParts P.right P.right_path hy
  let paths : ∀ i : Fin 4, G.Walk (![u,x,v,y] (src4 i)) (![u,x,v,y] (dst4 i)) :=
    Fin.cases L.first (Fin.cases L.last (Fin.cases R.last.reverse
      (Fin.cases R.first.reverse (fun i => Fin.elim0 i))))
  have h01 : L.first.edges.Disjoint L.last.edges := L.edges_disjoint
  have h02 : L.first.edges.Disjoint R.last.edges :=
    disjoint_mono P.edges_disjoint L.first_edges_subset R.last_edges_subset
  have h03 : L.first.edges.Disjoint R.first.edges :=
    disjoint_mono P.edges_disjoint L.first_edges_subset R.first_edges_subset
  have h12 : L.last.edges.Disjoint R.last.edges :=
    disjoint_mono P.edges_disjoint L.last_edges_subset R.last_edges_subset
  have h13 : L.last.edges.Disjoint R.first.edges :=
    disjoint_mono P.edges_disjoint L.last_edges_subset R.first_edges_subset
  have h23 : R.last.edges.Disjoint R.first.edges := R.edges_disjoint.symm
  refine ⟨⟨paths,?_,?_,?_⟩⟩
  · intro i
    fin_cases i
    · exact L.first_path
    · exact L.last_path
    · exact R.last_path.reverse
    · exact R.first_path.reverse
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change (L.first).edges.Disjoint (L.last).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h01
    · change (L.first).edges.Disjoint (R.last.reverse).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h02
    · change (L.first).edges.Disjoint (R.first.reverse).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h03
    · change (L.last).edges.Disjoint (L.first).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h01.symm
    · exact (hij rfl).elim
    · change (L.last).edges.Disjoint (R.last.reverse).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h12
    · change (L.last).edges.Disjoint (R.first.reverse).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h13
    · change (R.last.reverse).edges.Disjoint (L.first).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h02.symm
    · change (R.last.reverse).edges.Disjoint (L.last).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h12.symm
    · exact (hij rfl).elim
    · change (R.last.reverse).edges.Disjoint (R.first.reverse).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h23
    · change (R.first.reverse).edges.Disjoint (L.first).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h03.symm
    · change (R.first.reverse).edges.Disjoint (L.last).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h13.symm
    · change (R.first.reverse).edges.Disjoint (R.last.reverse).edges
      simpa only [Walk.edges_reverse,List.disjoint_reverse_left,List.disjoint_reverse_right] using h23.symm
    · exact (hij rfl).elim
  · intro e
    rw [Fin.exists_fin_succ,Fin.exists_fin_succ,Fin.exists_fin_two]
    change e ∈ c.edges ↔ e ∈ L.first.edges ∨ e ∈ L.last.edges ∨
      e ∈ R.last.reverse.edges ∨ e ∈ R.first.reverse.edges
    simp only [Walk.edges_reverse,List.mem_reverse]
    rw [← P.edges_cover e,← L.edges_cover e,← R.edges_cover e]
    tauto

lemma four_segments_of_rigid [Fintype V] (hrig : Rigidity.CycleRigid G)
    (heven : ∀ v, Even (G.degree v))
    {u v w : V} {c d : G.Walk u u} {t : G.Walk w w}
    (hc : c.IsCycle) (hd : d.IsCycle) (ht : t.IsCycle) (huv : u ≠ v)
    (hvc : v ∈ c.support) (hvd : v ∈ d.support)
    (hcd : c.edges.Disjoint d.edges) (hct : c.edges.Disjoint t.edges) (hdt : d.edges.Disjoint t.edges)
    (hinter : ∀ x, x ∈ c.support → x ∈ d.support → x = u ∨ x = v)
    (hut : u ∉ t.support) (hvt : v ∉ t.support)
    (hmeet : ∃ y, y ∈ d.support ∧ y ∈ t.support)
    {x z : V} (hxz : x ≠ z) (hxc : x ∈ c.support) (hzc : z ∈ c.support)
    (hxt : x ∈ t.support) (hzt : z ∈ t.support) :
    Nonempty (Segmentation c ![u,x,v,z] src4 dst4) := by
  obtain ⟨P⟩ := exists_cyclePaths c hc hvc huv
  have ha := rigid_contacts_alternate hrig heven hd ht huv hvd P hcd hct hdt hinter hut hvt hmeet
    hxz hxc hzc hxt hzt
  rcases ha with ⟨hx,hz⟩ | ⟨hz,hx⟩
  · exact four_segments_of_paths P hx hz
  · exact four_segments_of_paths P.swap hx hz

/-- Relabel the edges of a path model; parallel edges remain distinct labels. -/
noncomputable def reindexFamily {J' : Type*} (F : Family J W G) (e : J' ≃ J) : Family J' W G where
  vertex := F.vertex
  injective := F.injective
  src := F.src ∘ e
  dst := F.dst ∘ e
  ne j := F.ne (e j)
  path j := F.path (e j)
  isPath j := F.isPath (e j)
  vertex_mem j := F.vertex_mem (e j)
  edge_disjoint i j hij := F.edge_disjoint (e i) (e j) (fun h => hij (e.injective h))
  support_inter i j hij := F.support_inter (e i) (e j) (fun h => hij (e.injective h))

/-- Assemble local cycle segmentations into a single labelled path model.
The global junction list contains every intersection of different cycles. -/
noncomputable def assemble_segments [Fintype V]
    (m : K → ℕ) (vertex : W → V) (hinj : Function.Injective vertex)
    (place : ∀ k, Fin (m k) → W) (src dst : ∀ k, Fin (m k) → Fin (m k))
    (hne : ∀ k i, place k (src k i) ≠ place k (dst k i))
    (hsrc : ∀ k, Function.Surjective (src k))
    (root : K → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (S : ∀ k, Segmentation (C k) (vertex ∘ place k) (src k) (dst k))
    (hdisC : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hpoints : ∀ w k, vertex w ∈ (C k).support → ∃ i, place k i = w)
    (hmeet : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support →
      ∃ w, vertex w = x) : Family (Σ k, Fin (m k)) W G := by
  let src' : (Σ k, Fin (m k)) → W := fun j => place j.1 (src j.1 j.2)
  let dst' : (Σ k, Fin (m k)) → W := fun j => place j.1 (dst j.1 j.2)
  let P : ∀ j : (Σ k, Fin (m k)), G.Walk (vertex (src' j)) (vertex (dst' j)) :=
    fun j => (S j.1).path j.2
  apply family_of_cycle_segments vertex hinj src' dst' (fun j => hne j.1 j.2)
    P (fun j => (S j.1).isPath j.2) root C hC Sigma.fst (fun j => (S j.1).edges_subset j.2)
    _ _ hmeet
  · rintro ⟨k,i⟩ ⟨l,j⟩ hij
    by_cases hkl : k = l
    · subst l
      exact (S k).disjoint i j (fun he => hij (by cases he; rfl))
    · exact disjoint_mono (hdisC k l hkl) ((S k).edges_subset i) ((S l).edges_subset j)
  · intro w k hw
    obtain ⟨i,hi⟩ := hpoints w k hw
    obtain ⟨j,hj⟩ := hsrc k i
    refine ⟨⟨k,j⟩,rfl,Or.inl ?_⟩
    change w = place k (src k j)
    rw [hj,hi]

lemma assemble_segments_src [Fintype V]
    (m : K → ℕ) (vertex : W → V) (hinj : Function.Injective vertex)
    (place : ∀ k, Fin (m k) → W) (src dst : ∀ k, Fin (m k) → Fin (m k))
    (hne : ∀ k i, place k (src k i) ≠ place k (dst k i))
    (hsrc : ∀ k, Function.Surjective (src k))
    (root : K → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (S : ∀ k, Segmentation (C k) (vertex ∘ place k) (src k) (dst k))
    (hdisC : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hpoints : ∀ w k, vertex w ∈ (C k).support → ∃ i, place k i = w)
    (hmeet : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ w, vertex w = x)
    (j : Σ k, Fin (m k)) :
    (assemble_segments m vertex hinj place src dst hne hsrc root C hC S hdisC hpoints hmeet).src j =
      place j.1 (src j.1 j.2) := rfl

lemma assemble_segments_cover [Fintype V]
    (m : K → ℕ) (vertex : W → V) (hinj : Function.Injective vertex)
    (place : ∀ k, Fin (m k) → W) (src dst : ∀ k, Fin (m k) → Fin (m k))
    (hne : ∀ k i, place k (src k i) ≠ place k (dst k i))
    (hsrc : ∀ k, Function.Surjective (src k))
    (root : K → V) (C : ∀ k, G.Walk (root k) (root k)) (hC : ∀ k, (C k).IsCycle)
    (S : ∀ k, Segmentation (C k) (vertex ∘ place k) (src k) (dst k))
    (hdisC : ∀ k l, k ≠ l → (C k).edges.Disjoint (C l).edges)
    (hpoints : ∀ w k, vertex w ∈ (C k).support → ∃ i, place k i = w)
    (hmeet : ∀ k l, k ≠ l → ∀ x, x ∈ (C k).support → x ∈ (C l).support → ∃ w, vertex w = x)
    (hcover : ∀ x y, G.Adj x y → ∃ k, s(x,y) ∈ (C k).edges) :
    ∀ x y, G.Adj x y → ∃ j,
      s(x,y) ∈ ((assemble_segments m vertex hinj place src dst hne hsrc root C hC S hdisC hpoints hmeet).path j).edges := by
  intro x y hxy
  obtain ⟨k,hk⟩ := hcover x y hxy
  obtain ⟨j,hj⟩ := (S k).cover s(x,y) |>.mp hk
  exact ⟨⟨k,j⟩,hj⟩

#print axioms assemble_segments
#print axioms assemble_segments_cover
#print axioms three_segments
#print axioms four_segments_of_paths
#print axioms four_segments_of_rigid
#print axioms paths_in_cycle_support_inter
#print axioms family_of_cycle_segments
#print axioms two_segments
end Erdos184Work.CycleSegments
