import FormalConjecturesUtil

/-! Finite Hamilton multicovers of a labelled fifteen-vertex kernel.
This is an auxiliary certificate, not a settlement of Erdős 184. -/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.LinePetersenMulticovers
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
abbrev V := Fin 15

def edges : Finset (Sym2 V) :=
  {s(0,1),s(0,7),s(0,8),s(0,9),s(1,5),s(1,8),s(1,12),s(2,3),s(2,4),s(2,12),s(2,14),s(3,7),s(3,12),s(3,13),s(4,9),s(4,11),s(4,14),s(5,6),s(5,11),s(5,12),s(6,10),s(6,11),s(6,13),s(7,9),s(7,13),s(8,10),s(8,14),s(9,11),s(10,13),s(10,14)}

def G : SimpleGraph V := fromEdgeSet (edges : Set (Sym2 V))
instance : DecidableRel G.Adj := by unfold G; infer_instance

lemma degree_four (v : V) : G.degree v = 4 := by fin_cases v <;> decide

def w0 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 8) <|
  .cons (by decide : G.Adj 8 10) <|
  .cons (by decide : G.Adj 10 14) <|
  .cons (by decide : G.Adj 14 2) <|
  .cons (by decide : G.Adj 2 12) <|
  .cons (by decide : G.Adj 12 3) <|
  .cons (by decide : G.Adj 3 7) <|
  .cons (by decide : G.Adj 7 13) <|
  .cons (by decide : G.Adj 13 6) <|
  .cons (by decide : G.Adj 6 5) <|
  .cons (by decide : G.Adj 5 11) <|
  .cons (by decide : G.Adj 11 4) <|
  .cons (by decide : G.Adj 4 9) <|
  .cons (by decide : G.Adj 9 0) .nil
lemma w0_cycle : w0.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w0],by decide⟩

def w1 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 12) <|
  .cons (by decide : G.Adj 12 5) <|
  .cons (by decide : G.Adj 5 11) <|
  .cons (by decide : G.Adj 11 6) <|
  .cons (by decide : G.Adj 6 10) <|
  .cons (by decide : G.Adj 10 13) <|
  .cons (by decide : G.Adj 13 3) <|
  .cons (by decide : G.Adj 3 7) <|
  .cons (by decide : G.Adj 7 9) <|
  .cons (by decide : G.Adj 9 4) <|
  .cons (by decide : G.Adj 4 2) <|
  .cons (by decide : G.Adj 2 14) <|
  .cons (by decide : G.Adj 14 8) <|
  .cons (by decide : G.Adj 8 0) .nil
lemma w1_cycle : w1.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w1],by decide⟩

def w2 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 7) <|
  .cons (by decide : G.Adj 7 9) <|
  .cons (by decide : G.Adj 9 11) <|
  .cons (by decide : G.Adj 11 6) <|
  .cons (by decide : G.Adj 6 13) <|
  .cons (by decide : G.Adj 13 10) <|
  .cons (by decide : G.Adj 10 14) <|
  .cons (by decide : G.Adj 14 4) <|
  .cons (by decide : G.Adj 4 2) <|
  .cons (by decide : G.Adj 2 3) <|
  .cons (by decide : G.Adj 3 12) <|
  .cons (by decide : G.Adj 12 5) <|
  .cons (by decide : G.Adj 5 1) <|
  .cons (by decide : G.Adj 1 8) <|
  .cons (by decide : G.Adj 8 0) .nil
lemma w2_cycle : w2.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w2],by decide⟩

def w3 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 7) <|
  .cons (by decide : G.Adj 7 13) <|
  .cons (by decide : G.Adj 13 3) <|
  .cons (by decide : G.Adj 3 2) <|
  .cons (by decide : G.Adj 2 12) <|
  .cons (by decide : G.Adj 12 1) <|
  .cons (by decide : G.Adj 1 5) <|
  .cons (by decide : G.Adj 5 6) <|
  .cons (by decide : G.Adj 6 10) <|
  .cons (by decide : G.Adj 10 8) <|
  .cons (by decide : G.Adj 8 14) <|
  .cons (by decide : G.Adj 14 4) <|
  .cons (by decide : G.Adj 4 11) <|
  .cons (by decide : G.Adj 11 9) <|
  .cons (by decide : G.Adj 9 0) .nil
lemma w3_cycle : w3.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w3],by decide⟩

def w4 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 8) <|
  .cons (by decide : G.Adj 8 14) <|
  .cons (by decide : G.Adj 14 10) <|
  .cons (by decide : G.Adj 10 13) <|
  .cons (by decide : G.Adj 13 6) <|
  .cons (by decide : G.Adj 6 11) <|
  .cons (by decide : G.Adj 11 5) <|
  .cons (by decide : G.Adj 5 12) <|
  .cons (by decide : G.Adj 12 3) <|
  .cons (by decide : G.Adj 3 2) <|
  .cons (by decide : G.Adj 2 4) <|
  .cons (by decide : G.Adj 4 9) <|
  .cons (by decide : G.Adj 9 7) <|
  .cons (by decide : G.Adj 7 0) .nil
lemma w4_cycle : w4.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w4],by decide⟩

def w5 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 1) <|
  .cons (by decide : G.Adj 1 12) <|
  .cons (by decide : G.Adj 12 2) <|
  .cons (by decide : G.Adj 2 3) <|
  .cons (by decide : G.Adj 3 7) <|
  .cons (by decide : G.Adj 7 13) <|
  .cons (by decide : G.Adj 13 10) <|
  .cons (by decide : G.Adj 10 6) <|
  .cons (by decide : G.Adj 6 5) <|
  .cons (by decide : G.Adj 5 11) <|
  .cons (by decide : G.Adj 11 9) <|
  .cons (by decide : G.Adj 9 4) <|
  .cons (by decide : G.Adj 4 14) <|
  .cons (by decide : G.Adj 14 8) <|
  .cons (by decide : G.Adj 8 0) .nil
lemma w5_cycle : w5.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w5],by decide⟩

def w6 : G.Walk 0 0 :=
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
lemma w6_cycle : w6.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w6],by decide⟩

def w7 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 7) <|
  .cons (by decide : G.Adj 7 3) <|
  .cons (by decide : G.Adj 3 13) <|
  .cons (by decide : G.Adj 13 6) <|
  .cons (by decide : G.Adj 6 10) <|
  .cons (by decide : G.Adj 10 8) <|
  .cons (by decide : G.Adj 8 1) <|
  .cons (by decide : G.Adj 1 5) <|
  .cons (by decide : G.Adj 5 12) <|
  .cons (by decide : G.Adj 12 2) <|
  .cons (by decide : G.Adj 2 14) <|
  .cons (by decide : G.Adj 14 4) <|
  .cons (by decide : G.Adj 4 11) <|
  .cons (by decide : G.Adj 11 9) <|
  .cons (by decide : G.Adj 9 0) .nil
lemma w7_cycle : w7.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w7],by decide⟩

def w8 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 7) <|
  .cons (by decide : G.Adj 7 13) <|
  .cons (by decide : G.Adj 13 10) <|
  .cons (by decide : G.Adj 10 8) <|
  .cons (by decide : G.Adj 8 14) <|
  .cons (by decide : G.Adj 14 2) <|
  .cons (by decide : G.Adj 2 3) <|
  .cons (by decide : G.Adj 3 12) <|
  .cons (by decide : G.Adj 12 1) <|
  .cons (by decide : G.Adj 1 5) <|
  .cons (by decide : G.Adj 5 6) <|
  .cons (by decide : G.Adj 6 11) <|
  .cons (by decide : G.Adj 11 4) <|
  .cons (by decide : G.Adj 4 9) <|
  .cons (by decide : G.Adj 9 0) .nil
lemma w8_cycle : w8.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w8],by decide⟩

def w9 : G.Walk 0 0 :=
  .cons (by decide : G.Adj 0 8) <|
  .cons (by decide : G.Adj 8 1) <|
  .cons (by decide : G.Adj 1 5) <|
  .cons (by decide : G.Adj 5 11) <|
  .cons (by decide : G.Adj 11 6) <|
  .cons (by decide : G.Adj 6 10) <|
  .cons (by decide : G.Adj 10 14) <|
  .cons (by decide : G.Adj 14 4) <|
  .cons (by decide : G.Adj 4 2) <|
  .cons (by decide : G.Adj 2 12) <|
  .cons (by decide : G.Adj 12 3) <|
  .cons (by decide : G.Adj 3 13) <|
  .cons (by decide : G.Adj 13 7) <|
  .cons (by decide : G.Adj 7 9) <|
  .cons (by decide : G.Adj 9 0) .nil
lemma w9_cycle : w9.IsCycle := by
  rw [Walk.isCycle_def,Walk.isTrail_def]
  exact ⟨by decide,by simp [w9],by decide⟩

def double (i : Fin 4) : G.Walk 0 0 := ![w0,w1,w2,w3] i
def triple (i : Fin 6) : G.Walk 0 0 := ![w4,w5,w6,w7,w8,w9] i

lemma double_cycle (i : Fin 4) : (double i).IsCycle := by
  fin_cases i
  · exact w0_cycle
  · exact w1_cycle
  · exact w2_cycle
  · exact w3_cycle

lemma triple_cycle (i : Fin 6) : (triple i).IsCycle := by
  fin_cases i
  · exact w4_cycle
  · exact w5_cycle
  · exact w6_cycle
  · exact w7_cycle
  · exact w8_cycle
  · exact w9_cycle

lemma double_spanning (i : Fin 4) (v : V) : v ∈ (double i).support := by
  fin_cases i <;> fin_cases v <;> decide

lemma triple_spanning (i : Fin 6) (v : V) : v ∈ (triple i).support := by
  fin_cases i <;> fin_cases v <;> decide

lemma double_cover (x y : V) :
    (∑ i : Fin 4, if s(x,y) ∈ (double i).edges then (1 : ℕ) else 0) =
      if G.Adj x y then 2 else 0 := by
  fin_cases x <;> fin_cases y <;> decide

lemma triple_cover (x y : V) :
    (∑ i : Fin 6, if s(x,y) ∈ (triple i).edges then (1 : ℕ) else 0) =
      if G.Adj x y then 3 else 0 := by
  fin_cases x <;> fin_cases y <;> decide

abbrev I := Fin 4 ⊕ Fin 6

def walk : I → G.Walk 0 0 := Sum.elim double triple

lemma walk_cycle (i : I) : (walk i).IsCycle := by
  cases i with
  | inl i => exact double_cycle i
  | inr i => exact triple_cycle i

lemma walk_spanning (i : I) (v : V) : v ∈ (walk i).support := by
  cases i with
  | inl i => exact double_spanning i v
  | inr i => exact triple_spanning i v

lemma sum_indicator_mul {J : Type*} [Fintype J] (p : J → Prop) [DecidablePred p] (a : ℕ) :
    (∑ j, if p j then a else 0) = a * (∑ j, if p j then (1 : ℕ) else 0) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

lemma represent_two_three {m : ℕ} (hm : 2 ≤ m) :
    ∃ a b : ℕ, 2*a+3*b=m := by
  have hr := Nat.mod_lt m (by decide : 0 < 2)
  have he := Nat.mod_add_div m 2
  by_cases h : m % 2 = 0
  · exact ⟨m/2,0,by omega⟩
  · exact ⟨m/2-1,1,by omega⟩

/-- For every multiplicity at least two, these ten fixed Hamilton cycles
supply an exact natural multicover with total cycle multiplicity 2*m. -/
theorem exists_uniform_hamilton_multicover (m : ℕ) (hm : 2 ≤ m) :
    ∃ k : I → ℕ,
      (∀ x y : V, (∑ i, if s(x,y) ∈ (walk i).edges then k i else 0) =
        if G.Adj x y then m else 0) ∧
      (∑ i, k i) = 2*m := by
  obtain ⟨a,b,hab⟩ := represent_two_three hm
  let k : I → ℕ := Sum.elim (fun _ => a) (fun _ => b)
  refine ⟨k,?_,?_⟩
  · intro x y
    rw [Fintype.sum_sum_type]
    change (∑ i : Fin 4, if s(x,y) ∈ (double i).edges then a else 0) +
      (∑ i : Fin 6, if s(x,y) ∈ (triple i).edges then b else 0) = _
    rw [sum_indicator_mul (fun i : Fin 4 => s(x,y) ∈ (double i).edges) a,
      sum_indicator_mul (fun i : Fin 6 => s(x,y) ∈ (triple i).edges) b,
      double_cover,triple_cover]
    split_ifs <;> omega
  · simp only [k,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
    omega

end Erdos184.LinePetersenMulticovers
