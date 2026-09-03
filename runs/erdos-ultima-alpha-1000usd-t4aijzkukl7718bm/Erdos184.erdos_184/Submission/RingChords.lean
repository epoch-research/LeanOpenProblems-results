import Submission.CycleRings

/-! Shortening a contact ring across a vertex met only at the ends of an interval. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.RingIndices
set_option maxHeartbeats 1500000

abbrev initial {m n : ℕ} (h : m+3 < n+3) : Fin (m+3) → Fin (n+3) := Fin.castLE (Nat.le_of_lt h)

lemma initial_incidence_nonzero {m n : ℕ} (h : m+3 < n+3) (i j : Fin (m+3)) (hi : i ≠ 0) :
    (initial h i = initial h j ∨ initial h i = initial h j + 1) ↔ i = j ∨ i = j+1 := by
  have hi0 : i.val ≠ 0 := by simpa using hi
  simp only [Fin.ext_iff,Fin.val_add_eq_ite,Fin.val_one,initial,Fin.val_castLE]
  split_ifs <;> omega

lemma initial_vertex_internal {m : ℕ} (j : Fin (m+3)) (hj : j ≠ 0) :
    ∃ i : Fin (m+3), 0 < i.val ∧ i.val < m+2 ∧ (j = i ∨ j = i+1) := by
  have hj0 : j.val ≠ 0 := by simpa using hj
  let i : Fin (m+3) := ⟨if j.val = 1 then 1 else j.val-1,by split_ifs <;> omega⟩
  refine ⟨i,?_,?_,?_⟩
  · dsimp [i]
    split_ifs <;> omega
  · dsimp [i]
    split_ifs <;> omega
  · simp only [Fin.ext_iff,Fin.val_add_eq_ite,Fin.val_one,i]
    split_ifs <;> omega

lemma zero_incidence (n : ℕ) (i : Fin (n+3)) :
    (0 = i ∨ (0 : Fin (n+3)) = i+1) ↔ i = 0 ∨ i = Fin.last (n+2) := by
  have hil := i.isLt
  simp only [Fin.ext_iff,Fin.val_add_eq_ite,Fin.val_one,Fin.val_zero,Fin.val_last]
  split_ifs <;> (try simp only [or_false]) <;> omega

#print axioms initial_incidence_nonzero
#print axioms initial_vertex_internal
end Erdos184Work.RingIndices

namespace Erdos184Work.CycleRings
open RingIndices
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma Ring.shorten_at (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    {n : ℕ} (R : Ring G (n+1)) (i : Fin (n+4)) {u : V}
    (hu0 : u ∈ (R.piece i).verts) (hu1 : u ∈ (R.piece (i+1)).verts)
    (hu : u ≠ R.vertex (i+1)) : Nonempty (Ring G n) := by
  apply (R.rotate i).shorten_at_zero hrig heven (u := u)
  · simpa only [Ring.rotate,zero_add] using hu0
  · simpa only [Ring.rotate,add_comm 1 i] using hu1
  · simpa only [Ring.rotate,add_comm 1 i] using hu

lemma Ring.adjacent_intersection (hrig : Rigidity.CycleRigid G) (heven : ∀ v, Even (G.degree v))
    {n : ℕ} (R : Ring G (n+1)) (hno : ¬ Nonempty (Ring G n))
    (i : Fin (n+4)) (u : V) (hu0 : u ∈ (R.piece i).verts) (hu1 : u ∈ (R.piece (i+1)).verts) :
    u = R.vertex (i+1) := by
  by_contra hu
  exact hno (R.shorten_at hrig heven i hu0 hu1 hu)

lemma Ring.shorten_chord {m n : ℕ} (R : Ring G n) (h : m+3 < n+3) {w : V}
    (hw0 : w ∈ (R.piece (initial h 0)).verts)
    (hwend : w ∈ (R.piece (initial h (Fin.last (m+2)))).verts)
    (havoid : ∀ i : Fin (m+3), 0 < i.val → i.val < m+2 → w ∉ (R.piece (initial h i)).verts) :
    Nonempty (Ring G m) := by
  have hwne (j : Fin (m+3)) (hj : j ≠ 0) : w ≠ R.vertex (initial h j) := by
    obtain ⟨i,hi0,hie,hi⟩ := initial_vertex_internal j hj
    have hv : R.vertex (initial h j) ∈ (R.piece (initial h i)).verts :=
      (R.incidence _ _).mpr ((initial_incidence_nonzero h j i hj).mpr hi)
    intro he
    exact havoid i hi0 hie (he.symm ▸ hv)
  have hwi (i : Fin (m+3)) : w ∈ (R.piece (initial h i)).verts ↔ i = 0 ∨ i = Fin.last (m+2) := by
    constructor
    · intro hw
      by_cases hi0 : i = 0
      · exact Or.inl hi0
      by_cases hie : i = Fin.last (m+2)
      · exact Or.inr hie
      have h0 : i.val ≠ 0 := by simpa using hi0
      have hend : i.val ≠ m+2 := by simpa only [Fin.ext_iff,Fin.val_last] using hie
      exact (havoid i (by omega) (by omega) hw).elim
    · rintro (rfl | rfl)
      · exact hw0
      · exact hwend
  refine ⟨{
    vertex := fun i => if i = 0 then w else R.vertex (initial h i)
    injective := ?_
    piece := fun i => R.piece (initial h i)
    cycle := fun i => R.cycle (initial h i)
    disjoint := fun i j hij => R.disjoint _ _ (fun he => hij (Fin.castLE_injective _ he))
    incidence := ?_
  }⟩
  · intro i j he
    by_cases hi : i = 0
    · subst i
      by_cases hj : j = 0
      · exact hj.symm
      · simp only [if_pos rfl,if_neg hj] at he
        exact (hwne j hj he).elim
    · by_cases hj : j = 0
      · subst j
        simp only [if_pos rfl,if_neg hi] at he
        exact (hwne i hi he.symm).elim
      · simp only [if_neg hi,if_neg hj] at he
        exact Fin.castLE_injective _ (R.injective he)
  · intro i j
    by_cases hi : i = 0
    · subst i
      simp only [ite_true,hwi,zero_incidence]
    · simp only [if_neg hi,R.incidence,initial_incidence_nonzero h i j hi]

#print axioms Ring.shorten_at
#print axioms Ring.shorten_chord
end Erdos184Work.CycleRings
