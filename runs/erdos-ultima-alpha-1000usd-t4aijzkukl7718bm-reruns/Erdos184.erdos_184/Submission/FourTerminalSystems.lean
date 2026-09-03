import Submission.FourTerminalSewing

/-!
The three pairings of four distinct terminals, with exact path-system sewing.
A strong system consists of two vertex-disjoint paths. This is a routing
lemma only; no existence of such a system in an arbitrary graph is assumed.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.TerminalRouting
variable {V : Type*} {G : SimpleGraph V}
set_option maxHeartbeats 800000

def firstEnd (i : Fin 3) : Fin 4 := ![1,2,3] i
def secondStart (i : Fin 3) : Fin 4 := ![2,1,1] i
def secondEnd (i : Fin 3) : Fin 4 := ![3,3,2] i

structure PairedPaths (G : SimpleGraph V) (t : Fin 4 → V) (i : Fin 3) where
  p : G.Walk (t 0) (t (firstEnd i))
  q : G.Walk (t (secondStart i)) (t (secondEnd i))
  hp : p.IsPath
  hq : q.IsPath
  disjoint : Disjoint (walkEdges p) (walkEdges q)

def PairedPaths.edges {t : Fin 4 → V} {i : Fin 3} (P : PairedPaths G t i) : Set (Sym2 V) :=
  walkEdges P.p ∪ walkEdges P.q

def PairedPaths.verts {t : Fin 4 → V} {i : Fin 3} (P : PairedPaths G t i) : Set V :=
  walkVerts P.p ∪ walkVerts P.q

def PairedPaths.Strong {t : Fin 4 → V} {i : Fin 3} (P : PairedPaths G t i) : Prop :=
  P.p.support.Disjoint P.q.support

lemma four_terminal_range (t : Fin 4 → V) : Set.range t = {t 0,t 1,t 2,t 3} := by
  ext x
  simp only [Set.mem_range,Set.mem_insert_iff,Set.mem_singleton_iff]
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩

variable [Fintype V]

lemma paired_paths_compatible {t : Fin 4 → V} {i : Fin 3}
    (P Q : PairedPaths G t i) (hd : Disjoint P.edges Q.edges)
    (hi : P.verts ∩ Q.verts ⊆ Set.range t) :
    ∃ R : Packing G, R.edges = P.edges ∪ Q.edges ∧ R.pieces.card ≤ 6 := by
  obtain ⟨R,hR,hcard⟩ := packing_of_compatible_paths P.p P.q Q.p.reverse Q.q.reverse
    P.hp P.hq Q.hp.reverse Q.hq.reverse P.disjoint
    (by simpa only [walkEdges_reverse] using Q.disjoint)
    (by simpa only [walkEdges_reverse] using hd) (Set.range t)
    (by simpa only [walkVerts_reverse] using hi)
  have ht : (Set.range t).ncard ≤ 4 := by
    simpa using (Set.ncard_image_le (s := (Set.univ : Set (Fin 4))) (f := t))
  exact ⟨R,by simpa only [walkEdges_reverse] using hR,by omega⟩

private lemma strong01 {t : Fin 4 → V} (ht : Function.Injective t)
    (P : PairedPaths G t 0) (Q : PairedPaths G t 1)
    (hP : P.Strong) (hQ : Q.Strong) (hd : Disjoint P.edges Q.edges)
    (hi : P.verts ∩ Q.verts ⊆ Set.range t) :
    ∃ R : Packing G, R.edges = P.edges ∪ Q.edges ∧ R.pieces.card ≤ 6 := by
  obtain ⟨R,hR,hcard⟩ := packing_of_crossed_strong_paths P.p P.q Q.p Q.q
    P.hp P.hq Q.hp Q.hq (fun h => (by decide : (0 : Fin 4) ≠ 3) (ht h)) hP hQ hd
    (by simpa only [four_terminal_range] using hi)
  exact ⟨R,hR,by omega⟩

private lemma strong02 {t : Fin 4 → V} (ht : Function.Injective t)
    (P : PairedPaths G t 0) (Q : PairedPaths G t 2)
    (hP : P.Strong) (hQ : Q.Strong) (hd : Disjoint P.edges Q.edges)
    (hi : P.verts ∩ Q.verts ⊆ Set.range t) :
    ∃ R : Packing G, R.edges = P.edges ∪ Q.edges ∧ R.pieces.card ≤ 6 := by
  have hi' : (walkVerts P.p ∪ walkVerts P.q.reverse) ∩
      (walkVerts Q.p ∪ walkVerts Q.q) ⊆ {t 0,t 1,t 3,t 2} := by
    simp only [walkVerts_reverse]
    intro x hx
    have hh := hi hx
    rw [four_terminal_range] at hh
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hh ⊢
    tauto
  obtain ⟨R,hR,hcard⟩ := packing_of_crossed_strong_paths P.p P.q.reverse Q.p Q.q
    P.hp P.hq.reverse Q.hp Q.hq (fun h => (by decide : (0 : Fin 4) ≠ 2) (ht h))
    (by simpa only [Walk.support_reverse,List.disjoint_reverse_right] using hP) hQ
    (by simpa only [walkEdges_reverse] using hd) hi'
  exact ⟨R,by simpa only [walkEdges_reverse] using hR,by omega⟩

private lemma strong12 {t : Fin 4 → V} (ht : Function.Injective t)
    (P : PairedPaths G t 1) (Q : PairedPaths G t 2)
    (hP : P.Strong) (hQ : Q.Strong) (hd : Disjoint P.edges Q.edges)
    (hi : P.verts ∩ Q.verts ⊆ Set.range t) :
    ∃ R : Packing G, R.edges = P.edges ∪ Q.edges ∧ R.pieces.card ≤ 6 := by
  have hi' : (walkVerts P.p ∪ walkVerts P.q.reverse) ∩
      (walkVerts Q.p ∪ walkVerts Q.q.reverse) ⊆ {t 0,t 2,t 3,t 1} := by
    simp only [walkVerts_reverse]
    intro x hx
    have hh := hi hx
    rw [four_terminal_range] at hh
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hh ⊢
    tauto
  obtain ⟨R,hR,hcard⟩ := packing_of_crossed_strong_paths P.p P.q.reverse Q.p Q.q.reverse
    P.hp P.hq.reverse Q.hp Q.hq.reverse (fun h => (by decide : (0 : Fin 4) ≠ 1) (ht h))
    (by simpa only [Walk.support_reverse,List.disjoint_reverse_right] using hP)
    (by simpa only [Walk.support_reverse,List.disjoint_reverse_right] using hQ)
    (by simpa only [walkEdges_reverse] using hd) hi'
  exact ⟨R,by simpa only [walkEdges_reverse] using hR,by omega⟩

/-- Any two strong systems on the four terminals can be sewn with bounded
cost, regardless of whether their endpoint pairings agree. -/
lemma paired_paths_strong {t : Fin 4 → V} (ht : Function.Injective t) {i j : Fin 3}
    (P : PairedPaths G t i) (Q : PairedPaths G t j) (hP : P.Strong) (hQ : Q.Strong)
    (hd : Disjoint P.edges Q.edges) (hi : P.verts ∩ Q.verts ⊆ Set.range t) :
    ∃ R : Packing G, R.edges = P.edges ∪ Q.edges ∧ R.pieces.card ≤ 6 := by
  have hi' : Q.verts ∩ P.verts ⊆ Set.range t := by simpa only [Set.inter_comm] using hi
  fin_cases i <;> fin_cases j
  · exact paired_paths_compatible P Q hd hi
  · exact strong01 ht P Q hP hQ hd hi
  · exact strong02 ht P Q hP hQ hd hi
  · obtain ⟨R,hR,hcard⟩ := strong01 ht Q P hQ hP hd.symm hi'
    exact ⟨R,by rw [hR,Set.union_comm],hcard⟩
  · exact paired_paths_compatible P Q hd hi
  · exact strong12 ht P Q hP hQ hd hi
  · obtain ⟨R,hR,hcard⟩ := strong02 ht Q P hQ hP hd.symm hi'
    exact ⟨R,by rw [hR,Set.union_comm],hcard⟩
  · obtain ⟨R,hR,hcard⟩ := strong12 ht Q P hQ hP hd.symm hi'
    exact ⟨R,by rw [hR,Set.union_comm],hcard⟩
  · exact paired_paths_compatible P Q hd hi

end Erdos184.TerminalRouting
