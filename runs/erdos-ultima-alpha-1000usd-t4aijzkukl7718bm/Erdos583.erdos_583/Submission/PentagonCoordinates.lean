import Submission.Work
import Submission.PathIntervals
import Submission.OrderedPathPieces
import Submission.PentagonRoutes

/-! Coordinates for a pentagon and its ordered visits along a simple path. -/
namespace Erdos583PentagonCoordinatesDevelopment
open SimpleGraph Erdos583Work
open Erdos583PathIntervalsDevelopment Erdos583OrderedPathPiecesDevelopment Erdos583PentagonRoutesDevelopment
open scoped Classical
set_option maxHeartbeats 2200000
variable {V : Type*} {G : SimpleGraph V} {a b r : V}

lemma ordered_vertices {n : ℕ} (P : G.Walk a b) (c : Fin n → V)
    (hc : Function.Injective c) (hvisit : ∀ i, c i ∈ P.support) :
    ∃ h : Fin n → ℕ, ∃ p : Fin n → Fin n, StrictMono h ∧ Function.Injective p ∧
      (∀ i, h i ≤ P.length) ∧ ∀ i, P.getVert (h i)=c (p i) := by
  classical
  have hex (i : Fin n) : ∃ j, P.getVert j=c i ∧ j ≤ P.length :=
    Walk.mem_support_iff_exists_getVert.mp (hvisit i)
  choose pos hpos using hex
  have hinj : Function.Injective pos := by
    intro i j he
    apply hc
    rw [←(hpos i).1,←(hpos j).1,he]
  let S := Finset.univ.image pos
  have hS : S.card=n := by simp [S,Finset.card_image_of_injective _ hinj]
  let h := S.orderEmbOfFin hS
  have hex' (i : Fin n) : ∃ j, pos j=h i := by
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp (S.orderEmbOfFin_mem hS i)
    exact ⟨j,hj⟩
  choose p hp using hex'
  have hpinj : Function.Injective p := by
    intro i j he
    apply h.injective
    rw [←hp i,←hp j,he]
  exact ⟨h,p,h.strictMono,hpinj,fun i ↦ (hp i) ▸ (hpos (p i)).2,
    fun i ↦ (hp i) ▸ (hpos (p i)).1⟩

def coordinates (C : G.Walk r r) (i : Fin 5) : V := C.getVert i.val

lemma coordinates_injective (C : G.Walk r r) (hC : C.IsCycle) (hl : C.length=5) :
    Function.Injective (coordinates C) := by
  intro i j he
  apply Fin.ext
  exact hC.getVert_injOn' (show i.val ≤ C.length-1 by omega)
    (show j.val ≤ C.length-1 by omega) he

lemma coordinates_support (C : G.Walk r r) (hl : C.length=5) (x : V) :
    x ∈ C.support ↔ ∃ i : Fin 5, coordinates C i=x := by
  constructor
  · intro hx
    obtain ⟨j,hj,hjlen⟩ := Walk.mem_support_iff_exists_getVert.mp hx
    by_cases hj5 : j=5
    · refine ⟨0,?_⟩
      have hlen : j=C.length := by omega
      simpa only [hlen,Walk.getVert_length,coordinates,Fin.val_zero,Walk.getVert_zero] using hj
    · exact ⟨⟨j,by omega⟩,hj⟩
  · rintro ⟨i,rfl⟩
    exact C.getVert_mem_support _

lemma coordinates_next (C : G.Walk r r) (hl : C.length=5) (i : Fin 5) :
    C.getVert (i.val+1)=C.getVert ((i.val+1)%5) := by
  by_cases hi : i.val=4
  · rw [hi]
    norm_num
    rw [←hl,Walk.getVert_length]
  · rw [Nat.mod_eq_of_lt (by omega)]

lemma coordinates_adj (C : G.Walk r r) (hl : C.length=5) (i : Fin 5) :
    G.Adj (coordinates C i) (coordinates C ⟨(i.val+1)%5,Nat.mod_lt _ (by decide)⟩) := by
  have hh := C.adj_getVert_succ (show i.val < C.length by omega)
  rw [coordinates_next C hl i] at hh
  exact hh

lemma coordinates_edges (C : G.Walk r r) (hl : C.length=5) :
    C.toSubgraph.edgeSet=⋃ i : Fin 5,
      ({s(coordinates C i,coordinates C ⟨(i.val+1)%5,Nat.mod_lt _ (by decide)⟩)} : Set (Sym2 V)) := by
  ext e
  rw [Walk.mem_edges_toSubgraph,edges_positions]
  simp only [Set.mem_iUnion,Set.mem_singleton_iff]
  constructor
  · rintro ⟨j,hj,he⟩
    let i : Fin 5 := ⟨j,by omega⟩
    refine ⟨i,?_⟩
    change e=s(C.getVert i.val,C.getVert ((i.val+1)%5))
    rw [←coordinates_next C hl i]
    exact he
  · rintro ⟨i,he⟩
    refine ⟨i.val,by omega,?_⟩
    rw [coordinates_next C hl i]
    exact he

lemma coordinates_cycle_adj (C : G.Walk r r) (hl : C.length=5) (i j : Fin 5)
    (hij : adjacent i j) : C.toSubgraph.Adj (coordinates C i) (coordinates C j) := by
  change s(coordinates C i,coordinates C j) ∈ C.toSubgraph.edgeSet
  rw [coordinates_edges C hl]
  rcases hij with hij|hji
  · refine Set.mem_iUnion.mpr ⟨i,?_⟩
    have he : (⟨(i.val+1)%5,Nat.mod_lt _ (by decide)⟩ : Fin 5)=j := Fin.ext hij
    rw [he]
    rfl
  · refine Set.mem_iUnion.mpr ⟨j,?_⟩
    have he : (⟨(j.val+1)%5,Nat.mod_lt _ (by decide)⟩ : Fin 5)=i := Fin.ext hji
    rw [he]
    exact Sym2.eq_swap

lemma ordered_visit_position (C : G.Walk r r) (hl : C.length=5) (P : G.Walk a b) (hp : P.IsPath)
    (h : Fin 5 → ℕ) (p : Fin 5 → Fin 5) (hpinj : Function.Injective p)
    (hb : ∀ i, h i ≤ P.length) (hc : ∀ i, P.getVert (h i)=coordinates C (p i))
    {m : ℕ} (hm : m ≤ P.length) (hx : P.getVert m ∈ C.support) : ∃ i, m=h i := by
  obtain ⟨j,hj⟩ := (coordinates_support C hl _).mp hx
  obtain ⟨i,hi⟩ := (Finite.injective_iff_surjective.mp hpinj) j
  have he : P.getVert m=P.getVert (h i) := by rw [hc i,hi,hj]
  exact ⟨i,hp.getVert_injOn hm (hb i) he⟩

def insertCut (h : Fin 5 → ℕ) (d : Fin 4) (m : ℕ) (i : Fin 6) : ℕ :=
  if hi : i.val ≤ d.val then h ⟨i.val,by omega⟩
  else if i.val=d.val+1 then m else h ⟨i.val-1,by omega⟩

lemma insertCut_strictMono (h : Fin 5 → ℕ) (hh : StrictMono h) (d : Fin 4) (m : ℕ)
    (hlo : h d.castSucc < m) (hhi : m < h d.succ) : StrictMono (insertCut h d m) := by
  intro i j hij
  have hv : i.val < j.val := hij
  unfold insertCut
  split_ifs
  all_goals try omega
  · exact hh (a := ⟨i.val,by omega⟩) (b := ⟨j.val,by omega⟩) hv
  · exact lt_of_le_of_lt (hh.monotone (a := ⟨i.val,by omega⟩) (b := d.castSucc)
      (show i.val ≤ d.val by omega)) hlo
  · exact hh (a := ⟨i.val,by omega⟩) (b := ⟨j.val-1,by omega⟩) (show i.val < j.val-1 by omega)
  · exact lt_of_lt_of_le hhi (hh.monotone (a := d.succ) (b := ⟨j.val-1,by omega⟩)
      (show d.val+1 ≤ j.val-1 by omega))
  · exact hh (a := ⟨i.val-1,by omega⟩) (b := ⟨j.val-1,by omega⟩) (show i.val-1 < j.val-1 by omega)

lemma insertCut_zero (h : Fin 5 → ℕ) (d : Fin 4) (m : ℕ) : insertCut h d m 0=h 0 := by
  simp [insertCut]

lemma insertCut_last (h : Fin 5 → ℕ) (d : Fin 4) (m : ℕ) : insertCut h d m 5=h 4 := by
  have hd := d.isLt
  simp [insertCut,show ¬5 ≤ d.val by omega,show 5 ≠ d.val+1 by omega]

lemma insertCut_bound (h : Fin 5 → ℕ) (d : Fin 4) (m N : ℕ)
    (hb : ∀ i, h i ≤ N) (hm : m ≤ N) : ∀ i, insertCut h d m i ≤ N := by
  intro i
  unfold insertCut
  split_ifs <;> first | exact hb _ | exact hm

lemma extend_injective (c : Fin 5 → V) (hc : Function.Injective c) (z : V) (hz : ∀ i, z ≠ c i) :
    Function.Injective (Fin.lastCases z c : Fin 6 → V) := by
  intro i j he
  revert he
  refine Fin.lastCases ?_ (fun i ↦ ?_) i
  · refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · intro _; rfl
    · intro he; exact (hz j (by simpa using he)).elim
  · refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · intro he; exact (hz i (by simpa using he.symm)).elim
    · intro he
      exact congrArg Fin.castSucc (hc (by simpa using he))

lemma inserted_coordinates (P : G.Walk a b) (c : Fin 5 → V) (h : Fin 5 → ℕ) (p : Fin 5 → Fin 5)
    (hc : ∀ i, P.getVert (h i)=c (p i)) (d : Fin 4) (m : ℕ) (z : V) (hz : P.getVert m=z) :
    ∀ i : Fin 6, P.getVert (insertCut h d m i)=(Fin.lastCases z c : Fin 6 → V) (extended p d i) := by
  intro i
  unfold insertCut extended
  split_ifs <;> simp [hz,hc]
  rfl

end Erdos583PentagonCoordinatesDevelopment
