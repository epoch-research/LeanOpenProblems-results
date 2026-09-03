import Submission.LinePetersenMulticovers

/-! Port-compatible triple Hamilton covers of the labelled kernel.
This is an auxiliary finite certificate, not a proof of Erdős 184. -/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.LinePetersenMulticovers
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def pa0 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 5) <|
  .cons (by decide : G.Adj 5 12) <|
  .cons (by decide : G.Adj 12 2) <|
  .cons (by decide : G.Adj 2 3) <|
  .cons (by decide : G.Adj 3 7) <|
  .cons (by decide : G.Adj 7 13) <|
  .cons (by decide : G.Adj 13 10) <|
  .cons (by decide : G.Adj 10 6) <|
  .cons (by decide : G.Adj 6 11) <|
  .cons (by decide : G.Adj 11 9) <|
  .cons (by decide : G.Adj 9 4) <|
  .cons (by decide : G.Adj 4 14) <|
  .cons (by decide : G.Adj 14 8) <|
  .cons (by decide : G.Adj 8 0) .nil
lemma pa0_cycle : pa0.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [pa0],by decide⟩

def pa1 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 8) <|
  .cons (by decide : G.Adj 8 10) <|
  .cons (by decide : G.Adj 10 14) <|
  .cons (by decide : G.Adj 14 4) <|
  .cons (by decide : G.Adj 4 2) <|
  .cons (by decide : G.Adj 2 3) <|
  .cons (by decide : G.Adj 3 12) <|
  .cons (by decide : G.Adj 12 5) <|
  .cons (by decide : G.Adj 5 11) <|
  .cons (by decide : G.Adj 11 6) <|
  .cons (by decide : G.Adj 6 13) <|
  .cons (by decide : G.Adj 13 7) <|
  .cons (by decide : G.Adj 7 9) <|
  .cons (by decide : G.Adj 9 0) .nil
lemma pa1_cycle : pa1.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [pa1],by decide⟩

def pa2 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 8) <|
  .cons (by decide : G.Adj 8 14) <|
  .cons (by decide : G.Adj 14 10) <|
  .cons (by decide : G.Adj 10 6) <|
  .cons (by decide : G.Adj 6 5) <|
  .cons (by decide : G.Adj 5 11) <|
  .cons (by decide : G.Adj 11 4) <|
  .cons (by decide : G.Adj 4 2) <|
  .cons (by decide : G.Adj 2 12) <|
  .cons (by decide : G.Adj 12 3) <|
  .cons (by decide : G.Adj 3 13) <|
  .cons (by decide : G.Adj 13 7) <|
  .cons (by decide : G.Adj 7 9) <|
  .cons (by decide : G.Adj 9 0) .nil
lemma pa2_cycle : pa2.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [pa2],by decide⟩

def pa3 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 7) <|
  .cons (by decide : G.Adj 7 3) <|
  .cons (by decide : G.Adj 3 13) <|
  .cons (by decide : G.Adj 13 6) <|
  .cons (by decide : G.Adj 6 10) <|
  .cons (by decide : G.Adj 10 8) <|
  .cons (by decide : G.Adj 8 14) <|
  .cons (by decide : G.Adj 14 2) <|
  .cons (by decide : G.Adj 2 12) <|
  .cons (by decide : G.Adj 12 1) <|
  .cons (by decide : G.Adj 1 5) <|
  .cons (by decide : G.Adj 5 11) <|
  .cons (by decide : G.Adj 11 4) <|
  .cons (by decide : G.Adj 4 9) <|
  .cons (by decide : G.Adj 9 0) .nil
lemma pa3_cycle : pa3.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [pa3],by decide⟩

def pa4 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 7) <|
  .cons (by decide : G.Adj 7 3) <|
  .cons (by decide : G.Adj 3 13) <|
  .cons (by decide : G.Adj 13 10) <|
  .cons (by decide : G.Adj 10 14) <|
  .cons (by decide : G.Adj 14 2) <|
  .cons (by decide : G.Adj 2 4) <|
  .cons (by decide : G.Adj 4 9) <|
  .cons (by decide : G.Adj 9 11) <|
  .cons (by decide : G.Adj 11 6) <|
  .cons (by decide : G.Adj 6 5) <|
  .cons (by decide : G.Adj 5 12) <|
  .cons (by decide : G.Adj 12 1) <|
  .cons (by decide : G.Adj 1 8) <|
  .cons (by decide : G.Adj 8 0) .nil
lemma pa4_cycle : pa4.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [pa4],by decide⟩

def pa5 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 7) <|
  .cons (by decide : G.Adj 7 9) <|
  .cons (by decide : G.Adj 9 11) <|
  .cons (by decide : G.Adj 11 4) <|
  .cons (by decide : G.Adj 4 14) <|
  .cons (by decide : G.Adj 14 2) <|
  .cons (by decide : G.Adj 2 3) <|
  .cons (by decide : G.Adj 3 12) <|
  .cons (by decide : G.Adj 12 1) <|
  .cons (by decide : G.Adj 1 5) <|
  .cons (by decide : G.Adj 5 6) <|
  .cons (by decide : G.Adj 6 13) <|
  .cons (by decide : G.Adj 13 10) <|
  .cons (by decide : G.Adj 10 8) <|
  .cons (by decide : G.Adj 8 0) .nil
lemma pa5_cycle : pa5.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [pa5],by decide⟩

def portA (i : Fin 6) : G.Walk 0 0 := ![pa0,pa1,pa2,pa3,pa4,pa5] i

lemma portA_cycle (i : Fin 6) : (portA i).IsCycle := by
  fin_cases i
  · exact pa0_cycle
  · exact pa1_cycle
  · exact pa2_cycle
  · exact pa3_cycle
  · exact pa4_cycle
  · exact pa5_cycle

lemma portA_spanning (i : Fin 6) (v : V) : v ∈ (portA i).support := by
  fin_cases i <;> fin_cases v <;> decide

lemma portA_cover (x y : V) :
    (∑ i : Fin 6, if s(x,y) ∈ (portA i).edges then (1 : ℕ) else 0) =
      if G.Adj x y then 3 else 0 := by
  fin_cases x <;> fin_cases y <;> decide

lemma portA_left (i : Fin 6) :
    (if s(0,1) ∈ (portA i).edges then (1 : ℕ) else 0) +
    (if s(0,7) ∈ (portA i).edges then (1 : ℕ) else 0) = 1 := by
  fin_cases i <;> decide

lemma portA_right (i : Fin 6) :
    (if s(0,8) ∈ (portA i).edges then (1 : ℕ) else 0) +
    (if s(0,9) ∈ (portA i).edges then (1 : ℕ) else 0) = 1 := by
  fin_cases i <;> decide

def pb0 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 5) <|
  .cons (by decide : G.Adj 5 12) <|
  .cons (by decide : G.Adj 12 2) <|
  .cons (by decide : G.Adj 2 3) <|
  .cons (by decide : G.Adj 3 7) <|
  .cons (by decide : G.Adj 7 13) <|
  .cons (by decide : G.Adj 13 10) <|
  .cons (by decide : G.Adj 10 6) <|
  .cons (by decide : G.Adj 6 11) <|
  .cons (by decide : G.Adj 11 9) <|
  .cons (by decide : G.Adj 9 4) <|
  .cons (by decide : G.Adj 4 14) <|
  .cons (by decide : G.Adj 14 8) <|
  .cons (by decide : G.Adj 8 0) .nil
lemma pb0_cycle : pb0.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [pb0],by decide⟩

def pb1 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 8) <|
  .cons (by decide : G.Adj 8 14) <|
  .cons (by decide : G.Adj 14 4) <|
  .cons (by decide : G.Adj 4 2) <|
  .cons (by decide : G.Adj 2 12) <|
  .cons (by decide : G.Adj 12 5) <|
  .cons (by decide : G.Adj 5 11) <|
  .cons (by decide : G.Adj 11 6) <|
  .cons (by decide : G.Adj 6 10) <|
  .cons (by decide : G.Adj 10 13) <|
  .cons (by decide : G.Adj 13 3) <|
  .cons (by decide : G.Adj 3 7) <|
  .cons (by decide : G.Adj 7 9) <|
  .cons (by decide : G.Adj 9 0) .nil
lemma pb1_cycle : pb1.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [pb1],by decide⟩

def pb2 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 12) <|
  .cons (by decide : G.Adj 12 5) <|
  .cons (by decide : G.Adj 5 6) <|
  .cons (by decide : G.Adj 6 13) <|
  .cons (by decide : G.Adj 13 3) <|
  .cons (by decide : G.Adj 3 7) <|
  .cons (by decide : G.Adj 7 9) <|
  .cons (by decide : G.Adj 9 11) <|
  .cons (by decide : G.Adj 11 4) <|
  .cons (by decide : G.Adj 4 2) <|
  .cons (by decide : G.Adj 2 14) <|
  .cons (by decide : G.Adj 14 10) <|
  .cons (by decide : G.Adj 10 8) <|
  .cons (by decide : G.Adj 8 0) .nil
lemma pb2_cycle : pb2.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [pb2],by decide⟩

def pb3 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 7) <|
  .cons (by decide : G.Adj 7 9) <|
  .cons (by decide : G.Adj 9 11) <|
  .cons (by decide : G.Adj 11 5) <|
  .cons (by decide : G.Adj 5 6) <|
  .cons (by decide : G.Adj 6 13) <|
  .cons (by decide : G.Adj 13 10) <|
  .cons (by decide : G.Adj 10 14) <|
  .cons (by decide : G.Adj 14 4) <|
  .cons (by decide : G.Adj 4 2) <|
  .cons (by decide : G.Adj 2 3) <|
  .cons (by decide : G.Adj 3 12) <|
  .cons (by decide : G.Adj 12 1) <|
  .cons (by decide : G.Adj 1 8) <|
  .cons (by decide : G.Adj 8 0) .nil
lemma pb3_cycle : pb3.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [pb3],by decide⟩

def pb4 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 7) <|
  .cons (by decide : G.Adj 7 13) <|
  .cons (by decide : G.Adj 13 3) <|
  .cons (by decide : G.Adj 3 12) <|
  .cons (by decide : G.Adj 12 2) <|
  .cons (by decide : G.Adj 2 14) <|
  .cons (by decide : G.Adj 14 10) <|
  .cons (by decide : G.Adj 10 8) <|
  .cons (by decide : G.Adj 8 1) <|
  .cons (by decide : G.Adj 1 5) <|
  .cons (by decide : G.Adj 5 6) <|
  .cons (by decide : G.Adj 6 11) <|
  .cons (by decide : G.Adj 11 4) <|
  .cons (by decide : G.Adj 4 9) <|
  .cons (by decide : G.Adj 9 0) .nil
lemma pb4_cycle : pb4.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [pb4],by decide⟩

def pb5 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 7) <|
  .cons (by decide : G.Adj 7 13) <|
  .cons (by decide : G.Adj 13 6) <|
  .cons (by decide : G.Adj 6 10) <|
  .cons (by decide : G.Adj 10 8) <|
  .cons (by decide : G.Adj 8 14) <|
  .cons (by decide : G.Adj 14 2) <|
  .cons (by decide : G.Adj 2 3) <|
  .cons (by decide : G.Adj 3 12) <|
  .cons (by decide : G.Adj 12 1) <|
  .cons (by decide : G.Adj 1 5) <|
  .cons (by decide : G.Adj 5 11) <|
  .cons (by decide : G.Adj 11 4) <|
  .cons (by decide : G.Adj 4 9) <|
  .cons (by decide : G.Adj 9 0) .nil
lemma pb5_cycle : pb5.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [pb5],by decide⟩

def portB (i : Fin 6) : G.Walk 0 0 := ![pb0,pb1,pb2,pb3,pb4,pb5] i

lemma portB_cycle (i : Fin 6) : (portB i).IsCycle := by
  fin_cases i
  · exact pb0_cycle
  · exact pb1_cycle
  · exact pb2_cycle
  · exact pb3_cycle
  · exact pb4_cycle
  · exact pb5_cycle

lemma portB_spanning (i : Fin 6) (v : V) : v ∈ (portB i).support := by
  fin_cases i <;> fin_cases v <;> decide

lemma portB_cover (x y : V) :
    (∑ i : Fin 6, if s(x,y) ∈ (portB i).edges then (1 : ℕ) else 0) =
      if G.Adj x y then 3 else 0 := by
  fin_cases x <;> fin_cases y <;> decide

lemma portB_left (i : Fin 6) :
    (if s(0,1) ∈ (portB i).edges then (1 : ℕ) else 0) +
    (if s(0,7) ∈ (portB i).edges then (1 : ℕ) else 0) = 1 := by
  fin_cases i <;> decide

lemma portB_right (i : Fin 6) :
    (if s(0,8) ∈ (portB i).edges then (1 : ℕ) else 0) +
    (if s(0,9) ∈ (portB i).edges then (1 : ℕ) else 0) = 1 := by
  fin_cases i <;> decide

def align (i : Fin 6) : Fin 6 := ![1,0,2,3,4,5] i

def swapRight (v : V) : V := if v = 8 then 9 else if v = 9 then 8 else v

lemma align_bijective : Function.Bijective align := by decide

/-- Relabel the second triple cover to preserve left endpoints and interchange
right endpoints. This is the exact interface condition needed at a twist. -/
lemma aligned_endpoints (i : Fin 6) (v : V) :
    s(0,v) ∈ (portB (align i)).edges ↔ s(0,swapRight v) ∈ (portA i).edges := by
  fin_cases i <;> fin_cases v <;> decide

end Erdos184.LinePetersenMulticovers
