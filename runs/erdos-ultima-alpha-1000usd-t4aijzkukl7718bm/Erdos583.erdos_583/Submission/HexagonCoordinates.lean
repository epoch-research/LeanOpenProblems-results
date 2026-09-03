import Submission.Work
import Submission.HexagonRoutes

/-! Shifted coordinates put a missing base vertex last on a six-cycle. -/
namespace Erdos583HexagonCoordinatesDevelopment
open SimpleGraph Erdos583Work Erdos583Work.PathIntervals
open Erdos583HexagonRoutesDevelopment
open scoped Classical
set_option maxHeartbeats 1800000
variable {V : Type*} {G : SimpleGraph V} {r a b : V}

def coordinates (C : G.Walk r r) (i : Fin 6) : V := C.getVert (i.val+1)

lemma coordinates_last (C : G.Walk r r) (hl : C.length=6) : coordinates C 5=r := by
  change C.getVert 6=r
  rw [←hl,Walk.getVert_length]

lemma coordinates_injective (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=6) :
    Function.Injective (coordinates C) := by
  intro i j he
  have hh := hC.getVert_injOn (show 1 ≤ i.val+1 ∧ i.val+1 ≤ C.length by constructor <;> omega)
    (show 1 ≤ j.val+1 ∧ j.val+1 ≤ C.length by constructor <;> omega) he
  exact Fin.ext (by omega)

lemma coordinates_support (C : G.Walk r r) (hl : C.length=6) (x : V) :
    x ∈ C.support ↔ ∃ i : Fin 6, coordinates C i=x := by
  constructor
  · intro hx
    obtain ⟨j,hj,hjl⟩ := Walk.mem_support_iff_exists_getVert.mp hx
    by_cases hj0 : j=0
    · refine ⟨5,?_⟩
      rw [coordinates_last C hl]
      simpa only [hj0,Walk.getVert_zero] using hj
    · refine ⟨⟨j-1,by omega⟩,?_⟩
      simpa only [coordinates,show j-1+1=j by omega] using hj
  · rintro ⟨i,rfl⟩
    exact C.getVert_mem_support _

lemma coordinates_edge_positions (C : G.Walk r r) (hl : C.length=6) (i : Fin 6) :
    s(coordinates C i,coordinates C (next i))=
      s(C.getVert ((i.val+1)%6),C.getVert (((i.val+1)%6)+1)) := by
  have h6 : C.getVert 6=C.getVert 0 := by rw [←hl,Walk.getVert_length,Walk.getVert_zero]
  fin_cases i <;> simp [coordinates,next,h6]

lemma coordinates_adj (C : G.Walk r r) (hl : C.length=6) (i : Fin 6) :
    G.Adj (coordinates C i) (coordinates C (next i)) := by
  apply G.adj_congr_of_sym2 (coordinates_edge_positions C hl i) |>.mpr
  exact C.adj_getVert_succ (by have hh := Nat.mod_lt (i.val+1) (by decide : 0<6); omega)

lemma coordinates_edges (C : G.Walk r r) (hl : C.length=6) :
    C.toSubgraph.edgeSet=⋃ i : Fin 6, ({s(coordinates C i,coordinates C (next i))} : Set (Sym2 V)) := by
  ext e
  rw [Walk.mem_edges_toSubgraph,edges_positions]
  simp only [Set.mem_iUnion,Set.mem_singleton_iff]
  constructor
  · rintro ⟨j,hj,he⟩
    let i : Fin 6 := if j=0 then 5 else ⟨j-1,by omega⟩
    have hij : (i.val+1)%6=j := by
      dsimp [i]
      split_ifs with h0
      · omega
      · have hh : j-1+1=j := by omega
        rw [hh,Nat.mod_eq_of_lt (by omega)]
    exact ⟨i,by rw [coordinates_edge_positions C hl i,hij]; exact he⟩
  · rintro ⟨i,he⟩
    rw [coordinates_edge_positions C hl i] at he
    exact ⟨(i.val+1)%6,by have hh := Nat.mod_lt (i.val+1) (by decide : 0<6); omega,he⟩

lemma coordinates_cycle_adj (C : G.Walk r r) (hl : C.length=6) (i j : Fin 5)
    (hij : adjacent i j) : C.toSubgraph.Adj (coordinates C i.castSucc) (coordinates C j.castSucc) := by
  change s(coordinates C i.castSucc,coordinates C j.castSucc) ∈ C.toSubgraph.edgeSet
  rw [coordinates_edges C hl]
  rcases hij with hij|hji
  · refine Set.mem_iUnion.mpr ⟨i.castSucc,?_⟩
    have he : next i.castSucc=j.castSucc := Fin.ext (by dsimp [next]; rw [hij,Nat.mod_eq_of_lt (by omega)])
    rw [he]; rfl
  · refine Set.mem_iUnion.mpr ⟨j.castSucc,?_⟩
    have he : next j.castSucc=i.castSucc := Fin.ext (by dsimp [next]; rw [hji,Nat.mod_eq_of_lt (by omega)])
    rw [he]; exact Sym2.eq_swap

lemma ordered_visit_position (C : G.Walk r r) (hl : C.length=6) (P : G.Walk a b) (hp : P.IsPath)
    (hmiss : r ∉ P.support)
    (h : Fin 5 → ℕ) (p : Fin 5 → Fin 5) (hpinj : Function.Injective p)
    (hb : ∀ i, h i ≤ P.length) (hc : ∀ i, P.getVert (h i)=coordinates C (p i).castSucc)
    {m : ℕ} (hm : m ≤ P.length) (hx : P.getVert m ∈ C.support) : ∃ i, m=h i := by
  obtain ⟨j,hj⟩ := (coordinates_support C hl _).mp hx
  have hj5 : j.val < 5 := by
    by_contra hn
    have he : j=5 := Fin.ext (by omega)
    rw [he,coordinates_last C hl] at hj
    exact hmiss (hj.symm ▸ P.getVert_mem_support m)
  let j' : Fin 5 := ⟨j.val,hj5⟩
  have hj' : j'.castSucc=j := Fin.ext rfl
  obtain ⟨i,hi⟩ := (Finite.injective_iff_surjective.mp hpinj) j'
  have he : P.getVert m=P.getVert (h i) := by rw [hc i,hi,hj',hj]
  exact ⟨i,hp.getVert_injOn hm (hb i) he⟩

end Erdos583HexagonCoordinatesDevelopment
