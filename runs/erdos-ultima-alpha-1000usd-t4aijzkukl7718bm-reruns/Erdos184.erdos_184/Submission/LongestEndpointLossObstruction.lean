import Submission.ConeEnvelopeLoss
import Submission.CriticalVertexLoss

/-! A parameterized obstruction to bounding envelope loss at EVERY longest-path
endpoint. It does not refute existence of a favorable endpoint or the
count-critical-only hypothesis. -/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.LongestEndpointLossObstruction
open ConeEnvelopeLoss MengerMatching
set_option maxHeartbeats 1000000

abbrev W (r : ℕ) := Fin (r+3) × Bool

def prism (r : ℕ) : SimpleGraph (W r) where
  Adj x y := (x.1 = y.1 ∧ x.2 ≠ y.2) ∨ (x.2 = y.2 ∧ (cycleGraph (r+3)).Adj x.1 y.1)
  symm := by
    intro x y h
    rcases h with h | h
    · exact Or.inl ⟨h.1.symm,h.2.symm⟩
    · exact Or.inr ⟨h.1.symm,h.2.symm⟩
  loopless := by
    intro x h
    rcases h with h | h
    · exact h.2 rfl
    · exact (cycleGraph (r+3)).loopless _ h.2

lemma prism_degree (r : ℕ) (x : W r) : (prism r).degree x = 3 := by
  have hn : (prism r).neighborSet x = insert (x.1,!x.2)
      ((fun j : Fin (r+3) => (j,x.2)) '' (cycleGraph (r+3)).neighborSet x.1) := by
    ext y
    rcases x with ⟨i,b⟩
    rcases y with ⟨j,c⟩
    cases b <;> cases c <;> simp [SimpleGraph.neighborSet, prism] <;> aesop
  have hnot : (x.1,!x.2) ∉ (fun j : Fin (r+3) => (j,x.2)) '' (cycleGraph (r+3)).neighborSet x.1 := by
    rintro ⟨j,_,hj⟩
    have hh := congrArg Prod.snd hj
    cases x.2 <;> simp at hh
  have hinj : Function.Injective (fun j : Fin (r+3) => (j,x.2)) :=
    fun _ _ h => congrArg Prod.fst h
  have hd := cycleGraph_degree_three_le (n := r) (v := x.1)
  simp only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq] at hd ⊢
  rw [hn,Set.ncard_insert_of_notMem hnot,Set.ncard_image_of_injective _ hinj,hd]

/-- Traverse one row forward and the other backward. Values past the end
are immaterial; the modulus just makes the sequence total. -/
def vertex (r i : ℕ) : W r :=
  if h : i < r+3 then (⟨i,h⟩,true)
  else (⟨(2*(r+3)-1-i) % (r+3),Nat.mod_lt _ (by omega)⟩,false)

lemma vertex_first (r i : ℕ) (hi : i < r+3) :
    vertex r i = (⟨i,hi⟩,true) := by simp [vertex,hi]

lemma vertex_second (r i : ℕ) (hi : r+3 ≤ i) (hj : i < 2*(r+3)) :
    vertex r i = (⟨2*(r+3)-1-i,by omega⟩,false) := by
  simp [vertex,show ¬i<r+3 by omega,Nat.mod_eq_of_lt (show 2*(r+3)-1-i < r+3 by omega)]

lemma vertex_injective (r : ℕ) : Set.InjOn (vertex r) {i | i ≤ 2*(r+3)-1} := by
  intro i hi j hj he
  change i ≤ 2*(r+3)-1 at hi
  change j ≤ 2*(r+3)-1 at hj
  by_cases hi' : i < r+3 <;> by_cases hj' : j < r+3
  · rw [vertex_first r i hi',vertex_first r j hj'] at he
    exact congrArg (fun x : W r => x.1.val) he
  · rw [vertex_first r i hi',vertex_second r j (by omega) (by omega)] at he
    have hh := congrArg Prod.snd he
    cases hh
  · rw [vertex_second r i (by omega) (by omega),vertex_first r j hj'] at he
    have hh := congrArg Prod.snd he
    cases hh
  · rw [vertex_second r i (by omega) (by omega),vertex_second r j (by omega) (by omega)] at he
    have hh := congrArg (fun x : W r => x.1.val) he
    dsimp only at hh
    omega

lemma vertex_adj (r i : ℕ) (hi : i < 2*(r+3)-1) :
    (prism r).Adj (vertex r i) (vertex r (i+1)) := by
  by_cases hfirst : i+1 < r+3
  · rw [vertex_first r i (by omega),vertex_first r (i+1) hfirst]
    apply Or.inr
    refine ⟨rfl,pathGraph_le_cycleGraph ?_⟩
    exact pathGraph_adj.mpr (Or.inl rfl)
  by_cases hboundary : i+1 = r+3
  · rw [vertex_first r i (by omega),vertex_second r (i+1) (by omega) (by omega)]
    apply Or.inl
    refine ⟨Fin.ext (by dsimp; omega),by simp⟩
  · rw [vertex_second r i (by omega) (by omega),vertex_second r (i+1) (by omega) (by omega)]
    apply Or.inr
    refine ⟨rfl,pathGraph_le_cycleGraph ?_⟩
    apply pathGraph_adj.mpr
    right
    dsimp
    omega

lemma sequence_length {U : Type*} {A : SimpleGraph U} (v : ℕ → U) (n : ℕ)
    (h : ∀ i, i < n → A.Adj (v i) (v (i+1))) : (sequenceWalk v n h).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [sequenceWalk,ih]

lemma prism_hamilton_path (r : ℕ) :
    ∃ a b, ∃ p : (prism r).Walk a b, p.IsPath ∧ p.length + 1 = Fintype.card (W r) := by
  let p := sequenceWalk (vertex r) (2*(r+3)-1) (vertex_adj r)
  refine ⟨_,_,p,sequenceWalk_isPath _ _ _ (vertex_injective r),?_⟩
  simp [p,sequence_length,W]
  omega

/-- An unbounded-loss longest endpoint in a concrete finite even graph.
The conclusion concerns a specified endpoint, not all possible choices. -/
theorem exists_longest_endpoint_large_loss (C : ℕ) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (v w : V) (p : G.Walk v w),
      (∀ x, Even (G.degree x)) ∧ p.IsPath ∧
      (∀ a b (q : G.Walk a b), q.IsPath → q.length ≤ p.length) ∧
      CycleEnvelope.envelope (G.deleteIncidenceSet v) + C < CycleEnvelope.envelope G := by
  let r := 3*C
  let H := prism r
  have hn : Even (Fintype.card (W r)) := by simp [W]
  have hodd : ∀ x, Odd (H.degree x) := by intro x; rw [prism_degree]; decide
  have hdeg : ∀ x, H.degree x ≤ 3 := by intro x; rw [prism_degree]
  have he := cone_even_of_odd H hn hodd
  have hl := cone_loss_lower H hn hodd hdeg
  obtain ⟨a,b,p,hp,hlen⟩ := prism_hamilton_path r
  obtain ⟨q,hq,hmax⟩ := apex_longest_path H p hp hlen
  refine ⟨Option (W r),inferInstance,fullCone H,none,some b,q,he,hq,hmax,?_⟩
  simp only [W,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at hl
  dsimp only [r] at hl
  omega

/-- These examples nevertheless have an inexpensive supported vertex:
every old vertex has degree four. Thus they do not refute a favorable-vertex
existence assertion, even without restricting it to critical graphs. -/
lemma old_vertex_loss_le_two (r : ℕ) (x : W r) :
    CycleEnvelope.envelope (fullCone (prism r)) ≤
      CycleEnvelope.envelope ((fullCone (prism r)).deleteIncidenceSet (some x)) + 2 := by
  apply CycleEnvelope.vertex_loss_le_of_degree_le _ _ 2
  rw [degree_old,prism_degree]

end Erdos184.LongestEndpointLossObstruction
