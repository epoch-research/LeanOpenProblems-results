import Submission.PetersenDemandHole

/-! A concrete uniform four-cover on an even SIMPLE graph whose independent
floor-halving remainder is the Petersen demand hole. This is not Erdos 184. -/
open SimpleGraph
open scoped BigOperators
namespace Erdos184.PetersenFloorRemainder
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
abbrev V := Fin 11
abbrev E := Fin 25
abbrev I := Fin 15

def ends : E → V × V := ![(0,1),(0,4),(0,5),(1,2),(1,6),(2,3),(2,7),(3,4),(3,8),(4,9),(5,7),(5,8),(6,8),(6,9),(7,9),(0,10),(1,10),(2,10),(3,10),(4,10),(5,10),(6,10),(7,10),(8,10),(9,10)]
def edges : Finset (Sym2 V) := Finset.univ.image (fun e => s((ends e).1,(ends e).2))
def G : SimpleGraph V := fromEdgeSet (edges : Set (Sym2 V))
instance : DecidableRel G.Adj := by unfold G; infer_instance
lemma G_even (v : V) : Even (G.degree v) := by revert v; decide
lemma edges_injective : Function.Injective (fun e : E => s((ends e).1,(ends e).2)) := by decide

def p0 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 6) <|
  .cons (by decide : G.Adj 6 8) <|
  .cons (by decide : G.Adj 8 3) <|
  .cons (by decide : G.Adj 3 2) <|
  .cons (by decide : G.Adj 2 7) <|
  .cons (by decide : G.Adj 7 5) <|
  .cons (by decide : G.Adj 5 0) <|
  .nil
lemma p0_cycle : p0.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [p0],by decide⟩

def p1 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 6) <|
  .cons (by decide : G.Adj 6 9) <|
  .cons (by decide : G.Adj 9 4) <|
  .cons (by decide : G.Adj 4 3) <|
  .cons (by decide : G.Adj 3 8) <|
  .cons (by decide : G.Adj 8 5) <|
  .cons (by decide : G.Adj 5 0) <|
  .nil
lemma p1_cycle : p1.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [p1],by decide⟩

def p2 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 4) <|
  .cons (by decide : G.Adj 4 9) <|
  .cons (by decide : G.Adj 9 6) <|
  .cons (by decide : G.Adj 6 1) <|
  .cons (by decide : G.Adj 1 2) <|
  .cons (by decide : G.Adj 2 7) <|
  .cons (by decide : G.Adj 7 5) <|
  .cons (by decide : G.Adj 5 0) <|
  .nil
lemma p2_cycle : p2.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [p2],by decide⟩

def p3 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 4) <|
  .cons (by decide : G.Adj 4 9) <|
  .cons (by decide : G.Adj 9 7) <|
  .cons (by decide : G.Adj 7 2) <|
  .cons (by decide : G.Adj 2 3) <|
  .cons (by decide : G.Adj 3 8) <|
  .cons (by decide : G.Adj 8 5) <|
  .cons (by decide : G.Adj 5 0) <|
  .nil
lemma p3_cycle : p3.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [p3],by decide⟩

def p4 : G.Walk 1 1 :=
  .cons (by decide : G.Adj 1 2) <|
  .cons (by decide : G.Adj 2 7) <|
  .cons (by decide : G.Adj 7 9) <|
  .cons (by decide : G.Adj 9 4) <|
  .cons (by decide : G.Adj 4 3) <|
  .cons (by decide : G.Adj 3 8) <|
  .cons (by decide : G.Adj 8 6) <|
  .cons (by decide : G.Adj 6 1) <|
  .nil
lemma p4_cycle : p4.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [p4],by decide⟩

def p5 : G.Walk 10 10 :=
  .cons (by decide : G.Adj 10 0) <|
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 10) <|
  .nil
lemma p5_cycle : p5.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [p5],by decide⟩

def p6 : G.Walk 10 10 :=
  .cons (by decide : G.Adj 10 0) <|
  .cons (by decide : G.Adj 0 4) <|
  .cons (by decide : G.Adj 4 10) <|
  .nil
lemma p6_cycle : p6.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [p6],by decide⟩

def p7 : G.Walk 10 10 :=
  .cons (by decide : G.Adj 10 1) <|
  .cons (by decide : G.Adj 1 2) <|
  .cons (by decide : G.Adj 2 10) <|
  .nil
lemma p7_cycle : p7.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [p7],by decide⟩

def p8 : G.Walk 10 10 :=
  .cons (by decide : G.Adj 10 2) <|
  .cons (by decide : G.Adj 2 3) <|
  .cons (by decide : G.Adj 3 10) <|
  .nil
lemma p8_cycle : p8.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [p8],by decide⟩

def p9 : G.Walk 10 10 :=
  .cons (by decide : G.Adj 10 3) <|
  .cons (by decide : G.Adj 3 4) <|
  .cons (by decide : G.Adj 4 10) <|
  .nil
lemma p9_cycle : p9.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [p9],by decide⟩

def p10 : G.Walk 10 10 :=
  .cons (by decide : G.Adj 10 5) <|
  .cons (by decide : G.Adj 5 7) <|
  .cons (by decide : G.Adj 7 10) <|
  .nil
lemma p10_cycle : p10.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [p10],by decide⟩

def p11 : G.Walk 10 10 :=
  .cons (by decide : G.Adj 10 5) <|
  .cons (by decide : G.Adj 5 8) <|
  .cons (by decide : G.Adj 8 10) <|
  .nil
lemma p11_cycle : p11.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [p11],by decide⟩

def p12 : G.Walk 10 10 :=
  .cons (by decide : G.Adj 10 6) <|
  .cons (by decide : G.Adj 6 8) <|
  .cons (by decide : G.Adj 8 10) <|
  .nil
lemma p12_cycle : p12.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [p12],by decide⟩

def p13 : G.Walk 10 10 :=
  .cons (by decide : G.Adj 10 6) <|
  .cons (by decide : G.Adj 6 9) <|
  .cons (by decide : G.Adj 9 10) <|
  .nil
lemma p13_cycle : p13.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [p13],by decide⟩

def p14 : G.Walk 10 10 :=
  .cons (by decide : G.Adj 10 7) <|
  .cons (by decide : G.Adj 7 9) <|
  .cons (by decide : G.Adj 9 10) <|
  .nil
lemma p14_cycle : p14.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [p14],by decide⟩

def walk : I → Σ v, G.Walk v v := ![⟨0,p0⟩,⟨0,p1⟩,⟨0,p2⟩,⟨0,p3⟩,⟨1,p4⟩,⟨10,p5⟩,⟨10,p6⟩,⟨10,p7⟩,⟨10,p8⟩,⟨10,p9⟩,⟨10,p10⟩,⟨10,p11⟩,⟨10,p12⟩,⟨10,p13⟩,⟨10,p14⟩]
lemma walk_cycle (i : I) : (walk i).2.IsCycle := by
  fin_cases i
  · exact p0_cycle
  · exact p1_cycle
  · exact p2_cycle
  · exact p3_cycle
  · exact p4_cycle
  · exact p5_cycle
  · exact p6_cycle
  · exact p7_cycle
  · exact p8_cycle
  · exact p9_cycle
  · exact p10_cycle
  · exact p11_cycle
  · exact p12_cycle
  · exact p13_cycle
  · exact p14_cycle

def col (i : I) (e : E) : ℕ :=
  ((walk i).2.edges).count s((ends e).1,(ends e).2)
def multiplicity (i : I) : ℕ := if i.val < 5 then 1 else 2
def remainder (e : E) : ℕ :=
  if h : e.val < 15 then PetersenDemandHole.demand ⟨e.val,h⟩ else 0

lemma cols_injective : Function.Injective col := by decide
lemma four_cover (e : E) : ∑ i, multiplicity i * col i e = 4 := by revert e; decide
lemma input_count : ∑ i, multiplicity i = 25 := by decide
lemma floor_count : ∑ i, multiplicity i / 2 = 10 := by decide
lemma floor_remainder (e : E) :
    (∑ i, multiplicity i / 2 * col i e) + remainder e = 2 := by revert e; decide
lemma twice_remainder (e : E) :
    (∑ i, multiplicity i % 2 * col i e) = 2 * remainder e := by revert e; decide
lemma remainder_degree (v : V) :
    (∑ e, if v = (ends e).1 ∨ v = (ends e).2 then remainder e else 0) =
      if v = 10 then 0 else 4 := by revert v; decide

end Erdos184.PetersenFloorRemainder
