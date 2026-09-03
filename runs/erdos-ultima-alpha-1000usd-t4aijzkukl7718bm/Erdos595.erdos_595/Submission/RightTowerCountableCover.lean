import Submission.CommonNeighborDetector
import Submission.ArcAdjoint

/-!
A countable biclique edge cover supplies a common-neighbor detector for the
right adjoint. In particular, the second right adjoint of a countable base is
countably vertex-colorable if K4-free; the third right adjoint is then
countably triangle-free edge-coverable. This does not settle Erdős 595.
-/

open SimpleGraph Set
namespace Erdos595RightTowerCountable
open Erdos595Work Erdos595ArcAdjoint

variable {V : Type*} (H : SimpleGraph V)

def HasRectangleCover : Prop :=
  ∃ r : ℕ → Biclique H, ∀ a b, H.Adj a b →
    ∃ n, a ∈ (r n).val.1 ∧ b ∈ (r n).val.2

/-- The row/column intersection construction needs only a 2 by 2 matrix. -/
def matrixBiclique (r : ℕ → Biclique H) (m : Fin 2 → Fin 2 → ℕ) : Biclique H :=
  ⟨({a | ∃ i, ∀ j, a ∈ (r (m i j)).val.1},
    {b | ∃ j, ∀ i, b ∈ (r (m i j)).val.2}), by
      rintro a ⟨i,hi⟩ b ⟨j,hj⟩
      exact (r (m i j)).property a (hi j) b (hj i)⟩

/-- Any common neighbor in right H has four intersection witnesses.
The four covering rectangles combine into one of countably many bicliques. -/
theorem detector_of_rectangle_cover (hH : HasRectangleCover H) :
    ∃ d : ℕ → Biclique H, ∀ p q,
      (∃ r, (right H).Adj p r ∧ (right H).Adj q r) →
      ∃ n, (right H).Adj p (d n) ∧ (right H).Adj q (d n) := by
  classical
  obtain ⟨r,hr⟩ := hH
  obtain ⟨e,he⟩ := exists_surjective_nat (Fin 2 → Fin 2 → ℕ)
  refine ⟨fun n => matrixBiclique H r (e n),?_⟩
  intro p q h
  obtain ⟨s,hps,hqs⟩ := h
  obtain ⟨a,haP,haS⟩ := hps.1
  obtain ⟨b,hbS,hbP⟩ := hps.2
  obtain ⟨c,hcQ,hcS⟩ := hqs.1
  obtain ⟨d,hdS,hdQ⟩ := hqs.2
  let x : Fin 2 → V := ![a,c]
  let y : Fin 2 → V := ![b,d]
  have hx : ∀ i, x i ∈ s.val.1 := by intro i; fin_cases i <;> assumption
  have hy : ∀ j, y j ∈ s.val.2 := by intro j; fin_cases j <;> assumption
  have hab : ∀ i j, H.Adj (x i) (y j) := fun i j => s.property _ (hx i) _ (hy j)
  choose m hm using fun i j => hr (x i) (y j) (hab i j)
  obtain ⟨n,hn⟩ := he m
  refine ⟨n,?_⟩
  dsimp only
  rw [hn]
  have hleft : ∀ i, x i ∈ (matrixBiclique H r m).val.1 :=
    fun i => ⟨i,fun j => (hm i j).1⟩
  have hright : ∀ j, y j ∈ (matrixBiclique H r m).val.2 :=
    fun j => ⟨j,fun i => (hm i j).2⟩
  exact ⟨⟨⟨a,haP,hleft 0⟩,⟨b,hright 0,hbP⟩⟩,
    ⟨⟨c,hcQ,hleft 1⟩,⟨d,hright 1,hdQ⟩⟩⟩

theorem right_countable_coloring (hH : HasRectangleCover H)
    (hR : (right H).CliqueFree 4) : Nonempty ((right H).Coloring ℕ) := by
  obtain ⟨d,hd⟩ := detector_of_rectangle_cover H hH
  exact Erdos595CommonNeighborDetector.countable_coloring (right H) d hR hd

/-- One fixed pair of original points describes a complete rectangle
of right-adjoint vertices. -/
def witnessRectangle (a b : V) : Biclique (right H) :=
  ⟨({p | a ∈ p.val.2 ∧ b ∈ p.val.1},
    {q | a ∈ q.val.1 ∧ b ∈ q.val.2}), by
      intro p hp q hq
      exact ⟨⟨a,hp.1,hq.1⟩,⟨b,hq.2,hp.2⟩⟩⟩

/-- A countable base gives a countable rectangle cover of its first right
adjoint, whether or not that adjoint is K4-free. -/
theorem right_rectangle_cover [Countable V] : HasRectangleCover (right H) := by
  classical
  obtain ⟨e,he⟩ := exists_surjective_nat (Option (V × V))
  let r : ℕ → Biclique (right H) := fun n => match e n with
    | none => ⟨(∅,∅),by simp⟩
    | some (a,b) => witnessRectangle H a b
  refine ⟨r,?_⟩
  intro p q hpq
  obtain ⟨a,haP,haQ⟩ := hpq.1
  obtain ⟨b,hbQ,hbP⟩ := hpq.2
  obtain ⟨n,hn⟩ := he (some (a,b))
  refine ⟨n,?_⟩
  simpa only [r,hn,witnessRectangle] using And.intro (And.intro haP hbP) (And.intro haQ hbQ)

/-- K4-freeness makes the SECOND right adjoint countably vertex-colorable. -/
theorem second_right_countable_coloring [Countable V]
    (h : (right (right H)).CliqueFree 4) :
    Nonempty ((right (right H)).Coloring ℕ) :=
  right_countable_coloring (right H) (right_rectangle_cover H) h

/-- A graph always maps into its own right adjoint. This differs from the
arc/right unit, whose target has an extra arc construction. -/
def singletonHom : H →g right H where
  toFun v := ⟨(H.neighborSet v,{v}),by
    intro a ha b hb
    have hb' : b = v := Set.mem_singleton_iff.mp hb
    subst b
    exact ha.symm⟩
  map_rel' := by
    intro v w hvw
    exact ⟨⟨v,Set.mem_singleton v,hvw.symm⟩,⟨w,Set.mem_singleton w,hvw⟩⟩

lemma cliqueFree_of_right (h : (right H).CliqueFree 4) : H.CliqueFree 4 := by
  classical
  by_contra hn
  let f := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  let g := (singletonHom H).comp f.toHom
  have ha : ∀ i j : Fin 4, i ≠ j → (right H).Adj (g i) (g j) := fun _ _ hij => g.map_adj hij
  exact no_adj_common_neighbors h (ha 0 1 (by decide)) (ha 0 2 (by decide))
    (ha 1 2 (by decide)) (ha 0 3 (by decide)) (ha 1 3 (by decide)) (ha 2 3 (by decide))

/-- The THIRD right adjoint of a countable base cannot be a witness. -/
theorem third_right_countable_cover [Countable V]
    (h : (right (right (right H))).CliqueFree 4) :
    IsCountableUnionOfTriangleFree (right (right (right H))) := by
  obtain ⟨c⟩ := second_right_countable_coloring H (cliqueFree_of_right (right (right H)) h)
  apply right_cover_of_rainbow (right (right H)) c
  intro a b d hab had hbd
  exact ⟨c.valid hab,c.valid had,c.valid hbd⟩

#print axioms detector_of_rectangle_cover
#print axioms right_countable_coloring
#print axioms right_rectangle_cover
#print axioms second_right_countable_coloring
#print axioms third_right_countable_cover
end Erdos595RightTowerCountable
