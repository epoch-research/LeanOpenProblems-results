import FormalConjecturesUtil

/-!
# Elementary hypercube and coordinate-face infrastructure

These results concern coordinate flips and copies of `C₄` in the Boolean hypercube.
They do not establish any asymptotic extremal bound or resolve Erdős Problem 86.
In particular, this file is independent of `Submission.Spec`.
-/

open SimpleGraph

namespace Erdos86.CubeBasics

variable {n : ℕ}

/-- Toggle coordinate `i` of a Boolean vertex, leaving all other coordinates fixed. -/
def flip (x : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  fun k ↦ if k = i then !(x k) else x k

@[simp]
theorem flip_apply_self (x : Fin n → Bool) (i : Fin n) :
    flip x i i = !(x i) := by
  simp [flip]

@[simp]
theorem flip_apply_of_ne (x : Fin n → Bool) {i k : Fin n} (h : k ≠ i) :
    flip x i k = x k := by
  simp [flip, h]

@[simp]
theorem flip_flip (x : Fin n → Bool) (i : Fin n) :
    flip (flip x i) i = x := by
  funext k
  by_cases h : k = i <;> simp [flip, h]

theorem flip_involutive (i : Fin n) :
    Function.Involutive (fun x : Fin n → Bool ↦ flip x i) :=
  fun x ↦ flip_flip x i

theorem flip_injective (i : Fin n) :
    Function.Injective (fun x : Fin n → Bool ↦ flip x i) :=
  (flip_involutive i).injective

@[simp]
theorem flip_ne_self (x : Fin n → Bool) (i : Fin n) : flip x i ≠ x := by
  intro h
  have hi := congrFun h i
  simp [flip] at hi

/-- Coordinate flips commute, including when the two coordinates coincide. -/
theorem flip_comm (x : Fin n → Bool) (i j : Fin n) :
    flip (flip x i) j = flip (flip x j) i := by
  funext k
  by_cases hi : k = i <;> by_cases hj : k = j <;> simp_all [flip]

@[simp]
theorem flip_eq_flip_iff (x : Fin n → Bool) (i j : Fin n) :
    flip x i = flip x j ↔ i = j := by
  constructor
  · intro h
    by_contra hij
    have hi := congrFun h i
    simp [flip, hij] at hi
  · rintro rfl
    rfl

/-- Every single-coordinate flip is a hypercube edge. -/
theorem hypercube_adj_flip (x : Fin n → Bool) (i : Fin n) :
    (hypercube n).Adj x (flip x i) := by
  rw [hypercube_adj]
  have h : (Finset.univ.filter fun k ↦ x k ≠ flip x i k) = {i} := by
    ext k
    by_cases hk : k = i <;> simp [flip, hk]
  rw [h]
  simp

/-- Hypercube adjacency is precisely one coordinate flip. -/
theorem hypercube_adj_iff_exists_flip {x y : Fin n → Bool} :
    (hypercube n).Adj x y ↔ ∃ i : Fin n, y = flip x i := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (hypercube_adj.mp h)
    have hd (k : Fin n) : x k ≠ y k ↔ k = i := by
      have hk := Finset.ext_iff.mp hi k
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton] using hk
    refine ⟨i, ?_⟩
    funext k
    by_cases hk : k = i
    · subst k
      rw [flip_apply_self]
      exact Bool.eq_not_iff.mpr (Ne.symm ((hd i).mpr rfl))
    · rw [flip_apply_of_ne x hk]
      exact (not_not.mp (fun hne ↦ hk ((hd k).mp hne))).symm
  · rintro ⟨i, rfl⟩
    exact hypercube_adj_flip x i

/-- The coordinate witnessing a hypercube edge is unique. -/
theorem hypercube_adj_iff_existsUnique_flip {x y : Fin n → Bool} :
    (hypercube n).Adj x y ↔ ∃! i : Fin n, y = flip x i := by
  constructor
  · intro h
    obtain ⟨i, rfl⟩ := hypercube_adj_iff_exists_flip.mp h
    refine ⟨i, rfl, ?_⟩
    intro j hj
    exact ((flip_eq_flip_iff x i j).mp hj).symm
  · rintro ⟨i, hi, _⟩
    exact hypercube_adj_iff_exists_flip.mpr ⟨i, hi⟩

/-- The six inequalities between the four vertices of a coordinate face. -/
theorem face_vertices_distinct (x : Fin n → Bool) {i j : Fin n} (hij : i ≠ j) :
    x ≠ flip x i ∧
    x ≠ flip (flip x i) j ∧
    x ≠ flip x j ∧
    flip x i ≠ flip (flip x i) j ∧
    flip x i ≠ flip x j ∧
    flip (flip x i) j ≠ flip x j := by
  refine ⟨(flip_ne_self x i).symm, ?_, (flip_ne_self x j).symm,
    (flip_ne_self (flip x i) j).symm, ?_, ?_⟩
  · intro h
    have hi := congrFun h i
    simp [flip, hij] at hi
  · exact fun h ↦ hij ((flip_eq_flip_iff x i j).mp h)
  · intro h
    exact flip_ne_self x i (flip_injective j h)

/-- The vertices of a coordinate face, in cyclic order. -/
def faceVertex (x : Fin n → Bool) (i j : Fin n) : Fin 4 → (Fin n → Bool) :=
  ![x, flip x i, flip (flip x i) j, flip x j]

@[simp] theorem faceVertex_zero (x : Fin n → Bool) (i j : Fin n) :
    faceVertex x i j 0 = x := rfl

@[simp] theorem faceVertex_one (x : Fin n → Bool) (i j : Fin n) :
    faceVertex x i j 1 = flip x i := rfl

@[simp] theorem faceVertex_two (x : Fin n → Bool) (i j : Fin n) :
    faceVertex x i j 2 = flip (flip x i) j := rfl

@[simp] theorem faceVertex_three (x : Fin n → Bool) (i j : Fin n) :
    faceVertex x i j 3 = flip x j := rfl

/-- Equivalently, the four face vertices form an injective `Fin 4`-indexed family. -/
theorem faceVertex_injective (x : Fin n → Bool) {i j : Fin n} (hij : i ≠ j) :
    Function.Injective (faceVertex x i j) := by
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := face_vertices_distinct x hij
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all [faceVertex]

/-- All four boundary edges of a specified coordinate face belong to `H`.
The distinct-coordinate condition is supplied separately when needed. -/
def FaceEdges (H : SimpleGraph (Fin n → Bool)) (x : Fin n → Bool) (i j : Fin n) : Prop :=
  H.Adj x (flip x i) ∧
  H.Adj (flip x i) (flip (flip x i) j) ∧
  H.Adj (flip (flip x i) j) (flip x j) ∧
  H.Adj (flip x j) x

/-- The cyclic ordering of a coordinate face gives an actual graph copy.
No ambient-subgraph assumption on `H` is needed in this direction. -/
def faceCopy {H : SimpleGraph (Fin n → Bool)} (x : Fin n → Bool)
    {i j : Fin n} (hij : i ≠ j) (h : FaceEdges H x i j) :
    (cycleGraph 4).Copy H where
  toHom := {
    toFun := faceVertex x i j
    map_rel' := by
      intro a b hab
      obtain ⟨h01, h12, h23, h30⟩ := h
      fin_cases a <;> fin_cases b <;>
        first
        | exact h01
        | exact h12
        | exact h23
        | exact h30
        | exact H.symm h01
        | exact H.symm h12
        | exact H.symm h23
        | exact H.symm h30
        | exact absurd hab (by decide) }
  injective' := faceVertex_injective x hij

/-- Four face edges in `H` suffice for the containment notation used in Problem 86. -/
theorem cycleGraph_four_isContained_of_faceEdges {H : SimpleGraph (Fin n → Bool)}
    (x : Fin n → Bool) {i j : Fin n} (hij : i ≠ j) (h : FaceEdges H x i j) :
    cycleGraph 4 ⊑ H :=
  ⟨faceCopy x hij h⟩

/-- An unpacked version with four individual edge hypotheses. -/
theorem cycleGraph_four_isContained_of_four_edges {H : SimpleGraph (Fin n → Bool)}
    (x : Fin n → Bool) {i j : Fin n} (hij : i ≠ j)
    (h01 : H.Adj x (flip x i))
    (h12 : H.Adj (flip x i) (flip (flip x i) j))
    (h23 : H.Adj (flip (flip x i) j) (flip x j))
    (h30 : H.Adj (flip x j) x) : cycleGraph 4 ⊑ H :=
  cycleGraph_four_isContained_of_faceEdges x hij ⟨h01, h12, h23, h30⟩

/-- If an edge is known to change coordinate `i`, that coordinate is its flip label. -/
theorem eq_flip_of_hypercube_adj_of_ne {x y : Fin n → Bool}
    (h : (hypercube n).Adj x y) {i : Fin n} (hi : x i ≠ y i) :
    y = flip x i := by
  obtain ⟨j, rfl⟩ := hypercube_adj_iff_exists_flip.mp h
  have hij : i = j := by
    by_contra hij
    exact hi (flip_apply_of_ne x hij).symm
  rw [hij]

/-- Two distinct neighbors of a vertex have exactly the two expected common neighbors:
the original vertex and the opposite corner of their coordinate face. -/
theorem hypercube_common_neighbor_iff (x y : Fin n → Bool) {i j : Fin n}
    (hij : i ≠ j) :
    ((hypercube n).Adj (flip x i) y ∧ (hypercube n).Adj (flip x j) y) ↔
      y = x ∨ y = flip (flip x i) j := by
  constructor
  · rintro ⟨hi, hj⟩
    obtain ⟨k, rfl⟩ := hypercube_adj_iff_exists_flip.mp hi
    by_cases hki : k = i
    · left
      subst k
      exact flip_flip x i
    · right
      have hd : (flip x j) i ≠ (flip (flip x i) k) i := by
        simp [flip, hij, Ne.symm hki]
      exact (eq_flip_of_hypercube_adj_of_ne hj hd).trans (flip_comm x j i)
  · intro h
    rcases h with h | h
    · subst y
      exact ⟨(hypercube_adj_flip x i).symm, (hypercube_adj_flip x j).symm⟩
    · subst y
      refine ⟨hypercube_adj_flip (flip x i) j, ?_⟩
      rw [flip_comm x i j]
      exact hypercube_adj_flip (flip x j) i

/-- Every coordinate face has its four boundary edges in the hypercube. -/
theorem hypercube_faceEdges (x : Fin n → Bool) (i j : Fin n) :
    FaceEdges (hypercube n) x i j := by
  refine ⟨hypercube_adj_flip x i, hypercube_adj_flip (flip x i) j, ?_,
    (hypercube_adj_flip x j).symm⟩
  rw [flip_comm x i j]
  exact (hypercube_adj_flip (flip x j) i).symm

/-- Every `C₄` copy in a subgraph of the hypercube is a coordinate face, with the
copy's own cyclic ordering and its vertex `0` as base point. -/
theorem copy_eq_faceVertex {H : SimpleGraph (Fin n → Bool)} (hH : H ≤ hypercube n)
    (f : (cycleGraph 4).Copy H) :
    ∃ i j : Fin n, i ≠ j ∧ (fun k ↦ f k) = faceVertex (f 0) i j := by
  have h01 : (hypercube n).Adj (f 0) (f 1) :=
    hH (f.toHom.map_adj (by decide : (cycleGraph 4).Adj 0 1))
  have h03 : (hypercube n).Adj (f 0) (f 3) :=
    hH (f.toHom.map_adj (by decide : (cycleGraph 4).Adj 0 3))
  obtain ⟨i, hi⟩ := hypercube_adj_iff_exists_flip.mp h01
  obtain ⟨j, hj⟩ := hypercube_adj_iff_exists_flip.mp h03
  have hij : i ≠ j := by
    intro heq
    have h13 : f 1 = f 3 := by rw [hi, hj, heq]
    exact (by decide : (1 : Fin 4) ≠ 3) (f.injective h13)
  have h12 : (hypercube n).Adj (flip (f 0) i) (f 2) := by
    rw [← hi]
    exact hH (f.toHom.map_adj (by decide : (cycleGraph 4).Adj 1 2))
  have h32 : (hypercube n).Adj (flip (f 0) j) (f 2) := by
    rw [← hj]
    exact hH (f.toHom.map_adj (by decide : (cycleGraph 4).Adj 3 2))
  have h2 : f 2 = flip (flip (f 0) i) j := by
    rcases (hypercube_common_neighbor_iff (f 0) (f 2) hij).mp ⟨h12, h32⟩ with h20 | h2
    · exact ((by decide : (2 : Fin 4) ≠ 0) (f.injective h20)).elim
    · exact h2
  refine ⟨i, j, hij, ?_⟩
  funext k
  fin_cases k
  · rfl
  · exact hi
  · exact h2
  · exact hj

/-- For subgraphs of the hypercube, containing a `C₄` is equivalent to containing
all four edges of some coordinate face. -/
theorem cycleGraph_four_isContained_iff_faceEdges {H : SimpleGraph (Fin n → Bool)}
    (hH : H ≤ hypercube n) :
    cycleGraph 4 ⊑ H ↔
      ∃ (x : Fin n → Bool) (i j : Fin n), i ≠ j ∧ FaceEdges H x i j := by
  constructor
  · rintro ⟨f⟩
    obtain ⟨i, j, hij, hf⟩ := copy_eq_faceVertex hH f
    refine ⟨f 0, i, j, hij, ?_⟩
    change H.Adj (faceVertex (f 0) i j 0) (faceVertex (f 0) i j 1) ∧
      H.Adj (faceVertex (f 0) i j 1) (faceVertex (f 0) i j 2) ∧
      H.Adj (faceVertex (f 0) i j 2) (faceVertex (f 0) i j 3) ∧
      H.Adj (faceVertex (f 0) i j 3) (faceVertex (f 0) i j 0)
    rw [← hf]
    exact ⟨f.toHom.map_adj (by decide : (cycleGraph 4).Adj 0 1),
      f.toHom.map_adj (by decide : (cycleGraph 4).Adj 1 2),
      f.toHom.map_adj (by decide : (cycleGraph 4).Adj 2 3),
      f.toHom.map_adj (by decide : (cycleGraph 4).Adj 3 0)⟩
  · rintro ⟨x, i, j, hij, h⟩
    exact cycleGraph_four_isContained_of_faceEdges x hij h

/-- The handshaking identity in terms of `edgeSet.ncard`, which counts undirected
edges once, not ordered adjacent pairs. Use `classical` when applying this to a graph
whose adjacency relation has no specified decision procedure. -/
theorem twice_edgeSet_ncard_eq_sum_degrees {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    2 * H.edgeSet.ncard = ∑ v : V, H.degree v := by
  classical
  simpa only [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card'] using
    H.sum_degrees_eq_twice_card_edges.symm

/-- A decision-procedure-independent version of the same identity, with degrees
written as cardinalities of neighbor sets. -/
theorem twice_edgeSet_ncard_eq_sum_neighborSet_ncard {V : Type*} [Fintype V]
    (H : SimpleGraph V) :
    2 * H.edgeSet.ncard = ∑ v : V, (H.neighborSet v).ncard := by
  classical
  simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
    Set.ncard_eq_toFinset_card'] using twice_edgeSet_ncard_eq_sum_degrees H

end Erdos86.CubeBasics
