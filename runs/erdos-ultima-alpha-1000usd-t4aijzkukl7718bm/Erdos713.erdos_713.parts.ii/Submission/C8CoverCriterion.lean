import FormalConjecturesUtil
import Submission.ProductCoverObstructions

/-! A precise C8 preservation criterion for locally injective maps.
This supplies no degree amplification and does not settle Erdős 713. -/
open SimpleGraph
namespace Erdos713C8CoverCriterion
open Erdos713ProductCover
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

lemma next_adj (i : Fin 8) : (cycleGraph 8).Adj i (i+1) := by
  simp [cycleGraph_adj]

lemma next_two_adj (i : Fin 8) : (cycleGraph 8).Adj (i+1) (i+2) := by
  simpa only [show i+1+1=i+2 by abel] using next_adj (i+1)

lemma two_ne (i : Fin 8) : i ≠ i+2 := by
  intro h
  have he : (0 : Fin 8) = 2 := add_left_cancel ((add_zero i).trans h)
  exact (by decide : (0 : Fin 8) ≠ 2) he

lemma coloring_collision : ∀ c : Fin 8 → Fin 2,
    (∀ i, c i ≠ c (i+1)) → ∀ i j, c i = c j →
      i=j ∨ j=i+2 ∨ j=i+4 ∨ j=i+6 := by
  decide

variable {V : Type*} {G : SimpleGraph V}

lemma contains_four_of_collision (f : cycleGraph 8 →g G)
    (hTwo : ∀ i, f i ≠ f (i+2)) (i : Fin 8) (hFour : f i = f (i+4)) :
    cycleGraph 4 ⊑ G := by
  let g : Fin 4 → V := ![f i, f (i+1), f (i+2), f (i+3)]
  have h01 : G.Adj (f i) (f (i+1)) := f.map_adj (next_adj i)
  have h12 : G.Adj (f (i+1)) (f (i+2)) := f.map_adj (next_two_adj i)
  have h23 : G.Adj (f (i+2)) (f (i+3)) := by
    simpa only [show i+2+1=i+3 by abel] using f.map_adj (next_adj (i+2))
  have h30 : G.Adj (f (i+3)) (f i) := by
    rw [hFour]
    simpa only [show i+3+1=i+4 by abel] using f.map_adj (next_adj (i+3))
  have h02 : f i ≠ f (i+2) := hTwo i
  have h13 : f (i+1) ≠ f (i+3) := by
    simpa only [show i+1+2=i+3 by abel] using hTwo (i+1)
  refine ⟨⟨⟨g,?_⟩,?_⟩⟩
  · intro x y hxy
    fin_cases x <;> fin_cases y
    all_goals dsimp [g]
    all_goals
      first
      | exact absurd hxy (by decide)
      | exact h01
      | exact h01.symm
      | exact h12
      | exact h12.symm
      | exact h23
      | exact h23.symm
      | exact h30
      | exact h30.symm
  · intro x y hxy
    change g x = g y at hxy
    fin_cases x <;> fin_cases y
    all_goals dsimp [g] at hxy
    all_goals
      first
      | rfl
      | exact (h01.ne hxy).elim
      | exact (h01.ne hxy.symm).elim
      | exact (h12.ne hxy).elim
      | exact (h12.ne hxy.symm).elim
      | exact (h23.ne hxy).elim
      | exact (h23.ne hxy.symm).elim
      | exact (h30.ne hxy).elim
      | exact (h30.ne hxy.symm).elim
      | exact (h02 hxy).elim
      | exact (h02 hxy.symm).elim
      | exact (h13 hxy).elim
      | exact (h13 hxy.symm).elim

/-- The only possible nontrivial collision in such an eight-step map
would create C4 in the target. -/
theorem injective_of_two_step (f : cycleGraph 8 →g G)
    (hBip : G.IsBipartite) (hFree : (cycleGraph 4).Free G)
    (hTwo : ∀ i, f i ≠ f (i+2)) : Function.Injective f := by
  obtain ⟨χ⟩ := hBip
  intro i j hij
  have hc : ∀ i, χ (f i) ≠ χ (f (i+1)) :=
    fun i => χ.valid (f.map_adj (next_adj i))
  rcases coloring_collision (fun i => χ (f i)) hc i j (congrArg χ hij) with
    h | h | h | h
  · exact h
  · exact (hTwo i (h ▸ hij)).elim
  · exact (hFree (contains_four_of_collision f hTwo i (h ▸ hij))).elim
  · have he : j+2=i := by rw [h]; abel
    exact (hTwo j (by simpa only [he] using hij.symm)).elim

/-- A locally injective graph homomorphism cannot create C8 over a
bipartite base avoiding both C4 and C8. Surjectivity is unnecessary. -/
theorem free_of_locally_injective {U : Type*} {J : SimpleGraph U}
    (f : J →g G) (hLocal : ∀ u, Function.Injective (neighborMap f u))
    (hBip : G.IsBipartite) (hFour : (cycleGraph 4).Free G)
    (hEight : (cycleGraph 8).Free G) : (cycleGraph 8).Free J := by
  rintro ⟨p⟩
  let g : cycleGraph 8 →g G := f.comp p.toHom
  have hTwo (i : Fin 8) : g i ≠ g (i+2) := by
    intro he
    let x : J.neighborSet (p (i+1)) := ⟨p i, p.toHom.map_adj (next_adj i).symm⟩
    let y : J.neighborSet (p (i+1)) := ⟨p (i+2), p.toHom.map_adj (next_two_adj i)⟩
    have hxy : neighborMap f (p (i+1)) x = neighborMap f (p (i+1)) y :=
      Subtype.ext he
    have hh := congrArg Subtype.val (hLocal _ hxy)
    exact two_ne i (p.injective hh)
  exact hEight ⟨⟨g,injective_of_two_step g hBip hFour hTwo⟩⟩

theorem free_of_cover {U : Type*} {J : SimpleGraph U}
    (f : J →g G) (hf : IsCover f) (hBip : G.IsBipartite)
    (hFour : (cycleGraph 4).Free G) (hEight : (cycleGraph 8).Free G) :
    (cycleGraph 8).Free J :=
  free_of_locally_injective f (fun u => (hf.2 u).1) hBip hFour hEight

#print axioms coloring_collision
#print axioms contains_four_of_collision
#print axioms injective_of_two_step
#print axioms free_of_locally_injective
#print axioms free_of_cover
end Erdos713C8CoverCriterion
