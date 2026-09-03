import Submission.CartesianGridCover

/-! A geometric obstruction to completing a three-by-two Cartesian grid with
only three further points. This does not restrict arbitrary configurations or
the nonparallel Pappus template. -/
namespace Erdos213.ParallelGridCompletion
open EuclideanGeometry InversionReduction CartesianGridCover
noncomputable section
set_option maxHeartbeats 3000000

private lemma finite_rectangle_bound : ∀ S : Finset (Fin 3 × Fin 2),
    (∀ i j : Fin 3, i≠j →
      ¬ ((i,0)∈S ∧ (i,1)∈S ∧ (j,0)∈S ∧ (j,1)∈S)) → S.card≤4 := by
  decide

lemma rectangle_cospherical (a b c d : ℝ) :
    Cospherical ({pair a c,pair a d,pair b c,pair b d} : Set ℝ²) := by
  let o := pair ((a+b)/2) ((c+d)/2)
  refine ⟨o,dist (pair a c) o,?_⟩
  intro p hp
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl
  all_goals apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  all_goals simp only [o,InversionReduction.distance_sq,pair,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  all_goals ring

def gridPoint (x : Fin 3 → ℝ) (y : Fin 2 → ℝ) (i : Fin 3 × Fin 2) : ℝ² :=
  pair (x i.1) (y i.2)

def grid (x : Fin 3 → ℝ) (y : Fin 2 → ℝ) : Finset ℝ² :=
  Finset.univ.image (gridPoint x y)

lemma gridPoint_injective {x : Fin 3 → ℝ} {y : Fin 2 → ℝ}
    (hx : Function.Injective x) (hy : Function.Injective y) :
    Function.Injective (gridPoint x y) := by
  intro i j h
  apply Prod.ext
  · apply hx
    have he := congrArg (fun p : ℝ² => p 0) h
    change (x i.1 : ℝ)=(x j.1 : ℝ) at he
    exact_mod_cast he
  · apply hy
    have he := congrArg (fun p : ℝ² => p 1) h
    change (y i.2 : ℝ)=(y j.2 : ℝ) at he
    exact_mod_cast he

lemma grid_indices_card_le_four {x : Fin 3 → ℝ} {y : Fin 2 → ℝ}
    (hx : Function.Injective x) (hy : Function.Injective y)
    {S : Finset ℝ²} (hS : NoFourGeneralized (S : Set ℝ²)) :
    (Finset.univ.filter (fun i : Fin 3 × Fin 2 => gridPoint x y i∈S)).card≤4 := by
  classical
  apply finite_rectangle_bound
  intro i j hij h
  have hpinj := gridPoint_injective hx hy
  let Q : Set ℝ² := {gridPoint x y (i,0),gridPoint x y (i,1),
    gridPoint x y (j,0),gridPoint x y (j,1)}
  have hsub : Q⊆(S : Set ℝ²) := by
    intro p hp
    simp only [Q,Set.mem_insert_iff,Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact (Finset.mem_filter.mp h.1).2
    · exact (Finset.mem_filter.mp h.2.1).2
    · exact (Finset.mem_filter.mp h.2.2.1).2
    · exact (Finset.mem_filter.mp h.2.2.2).2
  have hcard : Q.ncard=4 := by
    apply Set.ncard_eq_four.mpr
    refine ⟨gridPoint x y (i,0),gridPoint x y (i,1),gridPoint x y (j,0),
      gridPoint x y (j,1),?_,?_,?_,?_,?_,?_,rfl⟩
    all_goals apply hpinj.ne
    all_goals simp [hij]
  apply hS Q hsub hcard
  apply generalized_of_cospherical
  exact rectangle_cospherical (x i) (x j) (y 0) (y 1)

/-- Four is an upper bound for how many of the six grid points a weak-GP
subset can retain. Consequently adjoining k arbitrary points gives at most
4+k weak-GP points. No metric assumptions on the new points are needed. -/
theorem weak_completion_bound {x : Fin 3 → ℝ} {y : Fin 2 → ℝ}
    (hx : Function.Injective x) (hy : Function.Injective y)
    {S T : Finset ℝ²} (hS : NoFourGeneralized (S : Set ℝ²))
    (hcover : S⊆grid x y∪T) : S.card≤4+T.card := by
  classical
  let K := Finset.univ.filter (fun i : Fin 3 × Fin 2 => gridPoint x y i∈S)
  have hK : K.card≤4 := grid_indices_card_le_four hx hy hS
  have hsub : S⊆K.image (gridPoint x y)∪T := by
    intro p hp
    rcases Finset.mem_union.mp (hcover hp) with hpG | hpT
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hpG
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩,rfl⟩
    · exact Finset.mem_union_right _ hpT
  calc
    S.card ≤ (K.image (gridPoint x y)∪T).card := Finset.card_le_card hsub
    _ ≤ (K.image (gridPoint x y)).card+T.card := Finset.card_union_le _ _
    _ ≤ K.card+T.card := Nat.add_le_add_right Finset.card_image_le _
    _ ≤ 4+T.card := Nat.add_le_add_right hK _

/-- Three added points cannot turn the six-point product into a weak-GP
or general-position octad, even if every new distance were rational. -/
theorem no_eight_with_three_added {x : Fin 3 → ℝ} {y : Fin 2 → ℝ}
    (hx : Function.Injective x) (hy : Function.Injective y)
    {S T : Finset ℝ²} (hT : T.card≤3) (hcover : S⊆grid x y∪T)
    (hcard : 8≤S.card) : ¬NoFourGeneralized (S : Set ℝ²) := by
  intro hS
  have hb := weak_completion_bound hx hy hS hcover
  omega

lemma no_general_position_eight_with_three_added {x : Fin 3 → ℝ} {y : Fin 2 → ℝ}
    (hx : Function.Injective x) (hy : Function.Injective y)
    {S T : Finset ℝ²} (hT : T.card≤3) (hcover : S⊆grid x y∪T)
    (hcard : 8≤S.card) : ¬InGeneralPosition (S : Set ℝ²) := by
  intro hS
  exact no_eight_with_three_added hx hy hT hcover hcard (noFour_of_general_position hS)

#print axioms finite_rectangle_bound
#print axioms rectangle_cospherical
#print axioms weak_completion_bound
#print axioms no_eight_with_three_added
#print axioms no_general_position_eight_with_three_added
end
end Erdos213.ParallelGridCompletion
