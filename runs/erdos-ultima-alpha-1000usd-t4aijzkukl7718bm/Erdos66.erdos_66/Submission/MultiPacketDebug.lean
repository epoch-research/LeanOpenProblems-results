import Submission.HeterogeneousSelectionExplore
import Submission.LocalWindowExplore

/-! Several symmetric repair packets. Non-designated sums are required to be
Sidon across the whole collection, not separately in each packet. -/
namespace Erdos66MultiPacket
open Erdos66OriginRepair Erdos66LocalWindow
open scoped Classical
set_option maxHeartbeats 1200000

variable {ι : Type*} [DecidableEq ι]

/-- The two points of coordinate i are x_i and n_i-x_i. -/
def point (n x : ι → ℤ) (u : ι × Bool) : ℤ :=
  if u.2 then n u.1 - x u.1 else x u.1

def Designated (u v : ι × Bool) : Prop := u.1 = v.1 ∧ u.2 ≠ v.2

lemma point_designated (n x : ι → ℤ) {u v : ι × Bool} (h : Designated u v) :
    point n x u + point n x v = n u.1 := by
  obtain ⟨i, b⟩ := u
  obtain ⟨j, d⟩ := v
  obtain ⟨rfl, hbd⟩ := h
  cases b <;> cases d <;> simp_all [point]

/-- A point collision always has at most one bad value in either coordinate
that occurs in it. -/
lemma point_collision_fiber (n : ι → ℤ) (u v : ι × Bool) (huv : u ≠ v)
    (i : ι) (hi : i = u.1 ∨ i = v.1) :
    ∀ f : ι → ℤ, ∀ a b : ℤ,
      point n (Function.update f i a) u = point n (Function.update f i a) v →
      point n (Function.update f i b) u = point n (Function.update f i b) v → a = b := by
  obtain ⟨j, s⟩ := u
  obtain ⟨k, t⟩ := v
  intro f a b ha hb
  cases s <;> cases t <;>
    by_cases hj : j = i <;> by_cases hk : k = i <;>
    simp_all [point, Function.update_of_ne] <;> trace_state

end Erdos66MultiPacket

