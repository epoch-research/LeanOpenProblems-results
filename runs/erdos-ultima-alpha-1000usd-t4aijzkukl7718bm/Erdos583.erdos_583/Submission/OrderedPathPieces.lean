import Submission.Work
import Submission.PathIntervals

/-! Consecutive marked subpaths of a simple path form a fresh piece system. -/
namespace Erdos583OrderedPathPiecesDevelopment
open SimpleGraph Erdos583Work Erdos583PathIntervalsDevelopment
open scoped Classical
set_option maxHeartbeats 1800000
variable {V : Type*} {G : SimpleGraph V} {a b : V} {n : ℕ}

lemma between_indices (h : Fin (n+1) → ℕ) {m : ℕ}
    (h0 : h 0 ≤ m) (hn : m < h (Fin.last n)) :
    ∃ i : Fin n, h i.castSucc ≤ m ∧ m < h i.succ := by
  classical
  let S := Finset.univ.filter (fun j : Fin (n+1) ↦ m < h j)
  have hS : S.Nonempty := ⟨Fin.last n,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩⟩
  let j := S.min' hS
  have hjm : m < h j := (Finset.mem_filter.mp (S.min'_mem hS)).2
  have hj0 : j ≠ 0 := fun he ↦ by rw [he] at hjm; omega
  have hjv : 0 < j.val := by simpa only [Fin.ext_iff,Fin.val_zero] using Nat.pos_of_ne_zero (fun he ↦ hj0 (Fin.ext he))
  let i : Fin n := ⟨j.val-1,by have hh := j.isLt; omega⟩
  have hs : i.succ=j := Fin.ext (by dsimp [i]; omega)
  refine ⟨i,?_,hs.symm ▸ hjm⟩
  by_contra hh
  have hiS : i.castSucc ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
  have hmin := S.min'_le _ hiS
  change j ≤ i.castSucc at hmin
  have hv : j.val ≤ i.val := hmin
  dsimp [i] at hv
  omega

def gap (P : G.Walk a b) (h : Fin (n+1) → ℕ) (hh : StrictMono h) (i : Fin n) :
    G.Walk (P.getVert (h i.castSucc)) (P.getVert (h i.succ)) :=
  interval P (h i.castSucc) (h i.succ) (hh.monotone (by exact Fin.castSucc_le_succ i))

lemma gap_isPath (P : G.Walk a b) (hp : P.IsPath)
    (h : Fin (n+1) → ℕ) (hh : StrictMono h) (i : Fin n) : (gap P h hh i).IsPath :=
  interval_isPath P hp _

lemma gap_core (P : G.Walk a b) (hp : P.IsPath)
    (h : Fin (n+1) → ℕ) (hh : StrictMono h) (hb : ∀ i, h i ≤ P.length)
    (i : Fin n) (x : Fin (n+1)) :
    P.getVert (h x) ∈ (gap P h hh i).support ↔ x=i.castSucc ∨ x=i.succ := by
  rw [gap,interval_core P hp _ (hb i.succ) (hb x),hh.le_iff_le,hh.le_iff_le]
  constructor
  · rintro ⟨hl,hu⟩
    have hli : i.val ≤ x.val := hl
    have hui : x.val ≤ i.val+1 := hu
    by_cases he : x.val=i.val
    · exact Or.inl (show x=i.castSucc from Fin.ext he)
    · exact Or.inr (show x=i.succ from Fin.ext (show x.val=i.val+1 by omega))
  · rintro (rfl|rfl)
    · exact ⟨le_rfl,Fin.castSucc_le_succ i⟩
    · exact ⟨Fin.castSucc_le_succ i,le_rfl⟩

lemma gap_intersection (P : G.Walk a b) (hp : P.IsPath)
    (h : Fin (n+1) → ℕ) (hh : StrictMono h) (hb : ∀ i, h i ≤ P.length)
    (i j : Fin n) (hij : i ≠ j) {x : V}
    (hxi : x ∈ (gap P h hh i).support) (hxj : x ∈ (gap P h hh j).support) :
    ∃ k : Fin (n+1), x=P.getVert (h k) := by
  rcases lt_or_gt_of_ne hij with hij|hji
  · have he : i.succ ≤ j.castSucc := by change i.val+1 ≤ j.val; exact hij
    have hx := interval_support_inter P hp _ _ (hh.monotone he) (hb j.succ) hxi hxj
    exact ⟨i.succ,hx.2⟩
  · have he : j.succ ≤ i.castSucc := by change j.val+1 ≤ i.val; exact hji
    have hx := interval_support_inter P hp _ _ (hh.monotone he) (hb i.succ) hxj hxi
    exact ⟨j.succ,hx.2⟩

lemma gap_edges_disjoint (P : G.Walk a b) (hp : P.IsPath)
    (h : Fin (n+1) → ℕ) (hh : StrictMono h) (hb : ∀ i, h i ≤ P.length)
    (i j : Fin n) (hij : i ≠ j) :
    Disjoint (gap P h hh i).toSubgraph.edgeSet (gap P h hh j).toSubgraph.edgeSet := by
  rcases lt_or_gt_of_ne hij with hij|hji
  · apply interval_edges_disjoint P hp _ _ _ (hb j.succ)
    apply hh.monotone
    change i.val+1 ≤ j.val
    exact hij
  · apply Disjoint.symm
    apply interval_edges_disjoint P hp _ _ _ (hb i.succ)
    apply hh.monotone
    change j.val+1 ≤ i.val
    exact hji

lemma gap_edges_subset (P : G.Walk a b) (h : Fin (n+1) → ℕ)
    (hh : StrictMono h) (hb : ∀ i, h i ≤ P.length) (i : Fin n) :
    (gap P h hh i).toSubgraph.edgeSet ⊆ P.toSubgraph.edgeSet :=
  interval_edges_subset P _ (hb i.succ)

lemma gap_cover (P : G.Walk a b) (h : Fin (n+1) → ℕ)
    (hh : StrictMono h) (hb : ∀ i, h i ≤ P.length) :
    (⋃ i : Fin n, (gap P h hh i).toSubgraph.edgeSet)=
      (interval P (h 0) (h (Fin.last n)) (hh.monotone (Fin.zero_le _))).toSubgraph.edgeSet := by
  ext e
  simp only [Set.mem_iUnion,gap,interval_edges P _ (hb _)]
  constructor
  · rintro ⟨i,m,him,hmi,he⟩
    have h0 := hh.monotone (Fin.zero_le i.castSucc)
    have hn := hh.monotone (Fin.le_last i.succ)
    exact ⟨m,by omega,by omega,he⟩
  · rintro ⟨m,hm0,hmn,he⟩
    obtain ⟨i,hi,hi'⟩ := between_indices h hm0 hmn
    exact ⟨i,m,hi,hi',he⟩

end Erdos583OrderedPathPiecesDevelopment
