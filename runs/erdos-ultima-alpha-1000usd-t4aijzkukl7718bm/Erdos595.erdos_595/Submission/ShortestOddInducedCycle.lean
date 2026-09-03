import Submission.MinimalRobustOddWheel

/-!
A shortest odd closed walk has no repeated rim vertices and no chords.
Consequently the minimal persistent wheel reduction can be formulated with
induced wheels, not merely closed rim walks. This remains a necessary
condition for a hypothetical counterexample to Erdos 595.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open SimpleGraph Set
namespace Erdos595ShortestOddInducedCycle
open Erdos595Work Erdos595RobustOddWheel Erdos595MinimalRobustOddWheel

variable {V : Type*} {G : SimpleGraph V} {a b : V}

def segment (w : G.Walk a b) (i j : ℕ) (hij : i ≤ j) :
    G.Walk (w.getVert i) (w.getVert j) :=
  ((w.drop i).take (j - i)).copy rfl (by
    rw [SimpleGraph.Walk.drop_getVert]
    congr 1
    omega)

lemma segment_length (w : G.Walk a b) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ w.length) :
    (segment w i j hij).length = j - i := by
  simp only [segment,SimpleGraph.Walk.length_copy,SimpleGraph.Walk.take_length,
    SimpleGraph.Walk.drop_length,inf_eq_left]
  omega

def complement (w : G.Walk a a) (i j : ℕ) : G.Walk (w.getVert j) (w.getVert i) :=
  (w.drop j).append (w.take i)

lemma complement_length (w : G.Walk a a) {i j : ℕ} (hi : i ≤ w.length) :
    (complement w i j).length = w.length - j + i := by
  simp only [complement,SimpleGraph.Walk.length_append,SimpleGraph.Walk.drop_length,
    SimpleGraph.Walk.take_length,inf_eq_left.mpr hi]

/-- No odd closed walk in this graph is shorter than n. -/
def MinimalOdd (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∀ v (w : G.Walk v v), Odd w.length → n ≤ w.length

lemma distinct_of_minimal (w : G.Walk a a) (ho : Odd w.length)
    (hm : MinimalOdd G w.length) {i j : ℕ} (hij : i < j) (hj : j < w.length) :
    w.getVert i ≠ w.getVert j := by
  intro he
  let p := (segment w i j hij.le).copy rfl he.symm
  let q := (complement w i j).copy rfl he
  have hp : p.length = j - i := by
    simp only [p,SimpleGraph.Walk.length_copy,segment_length w hij.le hj.le]
  have hq : q.length = w.length - j + i := by
    simp only [q,SimpleGraph.Walk.length_copy,complement_length w (hij.le.trans hj.le)]
  have hpo : ¬Odd p.length := by
    intro h
    have hle := hm _ p h
    omega
  have hqo : ¬Odd q.length := by
    intro h
    have hle := hm _ q h
    omega
  have hep := Nat.not_odd_iff_even.mp hpo
  have heq := Nat.not_odd_iff_even.mp hqo
  obtain ⟨r,hr⟩ := hep
  obtain ⟨s,hs⟩ := heq
  obtain ⟨t,ht⟩ := ho
  omega

lemma no_chord_of_minimal (w : G.Walk a a) (ho : Odd w.length)
    (hm : MinimalOdd G w.length) {i j : ℕ}
    (hij : i + 1 < j) (hj : j < w.length) (hwrap : j + 1 < w.length + i) :
    ¬G.Adj (w.getVert i) (w.getVert j) := by
  intro he
  let p := (segment w i j (by omega)).concat he.symm
  let q := (complement w i j).concat he
  have hp : p.length = j - i + 1 := by
    simp only [p,SimpleGraph.Walk.length_concat,segment_length w (show i ≤ j by omega) hj.le]
  have hq : q.length = w.length - j + i + 1 := by
    simp only [q,SimpleGraph.Walk.length_concat,
      complement_length w (show i ≤ w.length by omega)]
  have hpo : ¬Odd p.length := by
    intro h
    have hle := hm _ p h
    omega
  have hqo : ¬Odd q.length := by
    intro h
    have hle := hm _ q h
    omega
  obtain ⟨r,hr⟩ := Nat.not_odd_iff_even.mp hpo
  obtain ⟨s,hs⟩ := Nat.not_odd_iff_even.mp hqo
  obtain ⟨t,ht⟩ := ho
  omega

lemma cycle_adj_of_lt {n : ℕ} (i j : Fin n) (hij : i.val < j.val) :
    (cycleGraph n).Adj i j ↔ j.val = i.val + 1 ∨ i.val = 0 ∧ j.val + 1 = n := by
  rw [SimpleGraph.cycleGraph_adj',(Fin.coe_sub_iff_lt.mpr hij),Fin.sub_val_of_le hij.le]
  have hi := i.isLt
  have hj := j.isLt
  omega

lemma walk_adj_of_lt (w : G.Walk a a) (ho : Odd w.length)
    (hm : MinimalOdd G w.length) (i j : Fin w.length) (hij : i.val < j.val) :
    G.Adj (w.getVert i.val) (w.getVert j.val) ↔
      j.val = i.val + 1 ∨ i.val = 0 ∧ j.val + 1 = w.length := by
  constructor
  · intro h
    by_contra hn
    have h₁ : i.val + 1 < j.val := by omega
    have h₂ : j.val + 1 < w.length + i.val := by have := j.isLt; omega
    exact no_chord_of_minimal w ho hm h₁ j.isLt h₂ h
  · rintro (h | ⟨hi,hj⟩)
    · rw [h]
      exact w.adj_getVert_succ i.isLt
    · have h := (w.adj_getVert_succ j.isLt).symm
      simpa only [hi,hj,SimpleGraph.Walk.getVert_zero,SimpleGraph.Walk.getVert_length] using h

/-- A shortest odd closed walk parameterizes an INDUCED cycle. -/
def inducedCycle (w : G.Walk a a) (ho : Odd w.length)
    (hm : MinimalOdd G w.length) : cycleGraph w.length ↪g G where
  toFun i := w.getVert i.val
  inj' := by
    intro i j he
    apply Fin.ext
    by_contra hn
    rcases lt_or_gt_of_ne hn with h | h
    · exact distinct_of_minimal w ho hm h j.isLt he
    · exact distinct_of_minimal w ho hm h i.isLt he.symm
  map_rel_iff' := by
    intro i j
    rcases lt_trichotomy i.val j.val with h | h | h
    · exact (walk_adj_of_lt w ho hm i j h).trans (cycle_adj_of_lt i j h).symm
    · have he : i = j := Fin.ext h
      subst j
      simp
    · rw [G.adj_comm,SimpleGraph.adj_comm (G := cycleGraph w.length)]
      exact (walk_adj_of_lt w ho hm j i h).trans (cycle_adj_of_lt j i h).symm


def inducedCycleLength {n : ℕ} (w : G.Walk a a) (hw : w.length = n)
    (ho : Odd n) (hm : MinimalOdd G n) : cycleGraph n ↪g G := by
  subst n
  exact inducedCycle w ho hm

@[simp] lemma inducedCycleLength_apply {n : ℕ} (w : G.Walk a a) (hw : w.length = n)
    (ho : Odd n) (hm : MinimalOdd G n) (i : Fin n) :
    inducedCycleLength w hw ho hm i = w.getVert i.val := by
  subst n
  rfl

/-- The standard n-wheel, with the extra apex represented by none. -/
def wheel (n : ℕ) : SimpleGraph (Option (Fin n)) := coneGraph (cycleGraph n)

def wheelEmbedding (v : V) {n : ℕ} (e : cycleGraph n ↪g G.induce (G.neighborSet v)) :
    wheel n ↪g G where
  toFun
    | none => v
    | some i => (e i).val
  inj' := by
    intro x y he
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some j => exact ((e j).property.ne he).elim
    | some i =>
      cases y with
      | none => exact ((e i).property.ne he.symm).elim
      | some j => exact congrArg some (e.injective (Subtype.ext he))
  map_rel_iff' := by
    intro x y
    cases x with
    | none =>
      cases y with
      | none => exact ⟨fun h => h.ne rfl,False.elim⟩
      | some j => exact ⟨fun _ => True.intro,fun _ => (e j).property⟩
    | some i =>
      cases y with
      | none => exact ⟨fun _ => True.intro,fun _ => (e i).property.symm⟩
      | some j => exact e.map_rel_iff

lemma minimal_neighbor (R : SimpleGraph V) {n : ℕ}
    (hmin : ∀ m < n, Odd m → ¬WheelWalk R m) (H : SimpleGraph V)
    (hHR : H ≤ R) (v : V) : MinimalOdd (H.induce (H.neighborSet v)) n := by
  intro a w ho
  by_contra hn
  exact hmin w.length (lt_of_not_ge hn) ho
    (wheelWalk_mono hHR ⟨v,a,w,rfl⟩)

/-- If the ambient graph has no shorter odd wheel, a wheel walk in ANY
subgraph gives a wheel induced in the ambient graph, with all its edges
in that subgraph. -/
theorem induced_wheel_in_subgraph (R H : SimpleGraph V) (hHR : H ≤ R) {n : ℕ}
    (ho : Odd n) (hmin : ∀ m < n, Odd m → ¬WheelWalk R m)
    (hw : WheelWalk H n) :
    ∃ e : wheel n ↪g R, ∀ x y, (wheel n).Adj x y → H.Adj (e x) (e y) := by
  obtain ⟨v,a,w,hw⟩ := hw
  let f : H.induce (H.neighborSet v) →g R.induce (R.neighborSet v) :=
    ⟨fun x => ⟨x.val,hHR x.property⟩,fun h => hHR h⟩
  have hwR : (w.map f).length = n := (SimpleGraph.Walk.length_map f w).trans hw
  let cR := inducedCycleLength (w.map f) hwR ho (minimal_neighbor R hmin R le_rfl v)
  let cH := inducedCycleLength w hw ho (minimal_neighbor R hmin H hHR v)
  let eR := wheelEmbedding v cR
  let eH := wheelEmbedding v cH
  have he : ∀ x, eR x = eH x := by
    intro x
    cases x with
    | none => rfl
    | some i =>
      change (cR i).val = (cH i).val
      simp only [cR,cH,inducedCycleLength_apply,SimpleGraph.Walk.getVert_map]
      rfl
  refine ⟨eR,?_⟩
  intro x y hxy
  rw [he x,he y]
  exact eH.map_rel_iff.mpr hxy

/-- Strengthened minimal-residual normal form: one fixed odd induced wheel
survives every covered edge deletion. Inducedness is in the SAME residual
R before D is deleted, not merely in R minus D. This is still conditional
on non-coverability; it supplies neither a witness nor a contradiction. -/
theorem minimal_induced_residual (G : SimpleGraph V) (hK : G.CliqueFree 4)
    (hG : ¬IsCountableUnionOfTriangleFree G) :
    ∃ (E : SimpleGraph V) (n : ℕ),
      IsCountableUnionOfTriangleFree E ∧
      (G \ E).CliqueFree 4 ∧ ¬IsCountableUnionOfTriangleFree (G \ E) ∧
      5 ≤ n ∧ Odd n ∧
      (∀ m < n, Odd m → ¬WheelWalk (G \ E) m) ∧
      ∀ D : SimpleGraph V, IsCountableUnionOfTriangleFree D →
        ∃ e : wheel n ↪g (G \ E),
          ∀ x y, (wheel n).Adj x y → ¬D.Adj (e x) (e y) := by
  obtain ⟨E,n,hE,hK',hG',h5,ho,hp,hmin⟩ := minimal_residual G hK hG
  refine ⟨E,n,hE,hK',hG',h5,ho,hmin,?_⟩
  intro D hD
  obtain ⟨e,he⟩ := induced_wheel_in_subgraph (G \ E) ((G \ E) \ D)
    (fun _ _ h => h.1) ho hmin (hp D hD)
  exact ⟨e,fun x y hxy => (he x y hxy).2⟩

#print axioms induced_wheel_in_subgraph
#print axioms minimal_induced_residual

#print axioms inducedCycle
#print axioms no_chord_of_minimal
end Erdos595ShortestOddInducedCycle
