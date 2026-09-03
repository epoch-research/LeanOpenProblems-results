import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! An elliptic family of split fibers on the genus-three auxiliary curve.
This does not give a general-position rational-distance configuration. -/
namespace Erdos213.SplitFiber

def branchA (x : ℚ) := (x - 3) * (x^2 + 3)
def branchB (x : ℚ) := x * (x^2 - 1) * (x + 3)
def branchF (x : ℚ) := x * (x^2 - 1) * (x^2 - 9) * (x^2 + 3)
def twist (X : ℚ) := X / ((X+1)*(X+2))
def firstQuad (X x : ℚ) := x^2 - X*x + 3*X + 3
def secondQuad (X x : ℚ) := X*x^2 - 2*x + 6 + 3*X

theorem branch_product (x : ℚ) : branchA x * branchB x = branchF x := by
  dsimp [branchA, branchB, branchF]
  ring

theorem pell_identity (t x : ℚ) :
    (branchA x + t*branchB x)^2 - 4*t*branchF x =
      (branchA x - t*branchB x)^2 := by
  dsimp [branchA, branchB, branchF]
  ring

theorem pencil_composition (X x : ℚ) (h1 : X+1 ≠ 0) (h2 : X+2 ≠ 0) :
    X * (branchA x - twist X * branchB x) =
      -twist X * firstQuad X x * secondQuad X x := by
  dsimp [branchA, branchB, twist, firstQuad, secondQuad]
  field_simp
  ring

theorem square_on_fiber (X x : ℚ) (h0 : X ≠ 0)
    (h1 : X+1 ≠ 0) (h2 : X+2 ≠ 0)
    (hx : firstQuad X x = 0 ∨ secondQuad X x = 0) :
    (branchA x)^2 = twist X * branchF x := by
  have hp := pencil_composition X x h1 h2
  have hz : X * (branchA x - twist X * branchB x) = 0 := by
    rcases hx with hx | hx <;> simp [hx] at hp ⊢ <;> exact hp
  have hb : branchA x = twist X * branchB x :=
    sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left h0)
  rw [← branch_product]
  calc
    (branchA x)^2 = branchA x * (twist X * branchB x) := by rw [← hb]; ring
    _ = twist X * (branchA x * branchB x) := by ring

theorem four_fiber_squares (X a b : ℚ) (h0 : X ≠ 0)
    (h1 : X+1 ≠ 0) (h2 : X+2 ≠ 0)
    (ha : a^2 = X^2 - 12*X - 12) (hb : b^2 = 1 - 6*X - 3*X^2) :
    ∀ x ∈ [((X+a)/2), ((X-a)/2), ((1+b)/X), ((1-b)/X)],
      (branchA x)^2 = twist X * branchF x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · apply square_on_fiber X _ h0 h1 h2
    left
    dsimp [firstQuad]
    linear_combination ha/4
  · apply square_on_fiber X _ h0 h1 h2
    left
    dsimp [firstQuad]
    linear_combination ha/4
  · apply square_on_fiber X _ h0 h1 h2
    right
    dsimp [secondQuad]
    field_simp
    linear_combination hb
  · apply square_on_fiber X _ h0 h1 h2
    right
    dsimp [secondQuad]
    field_simp
    linear_combination hb

def quartic (k : ℚ) := k^4 - 5*k^2 - 42*k - 146
def baseX (k : ℚ) := -(k^2+2*k+13)/(k^2-1)
def baseA (k : ℚ) := -(k^2+14*k+1)/(k^2-1)
def baseB (k y : ℚ) := 2*y/(k^2-1)

theorem base_first_square (k : ℚ) (hk : k^2-1 ≠ 0) :
    (baseA k)^2 = (baseX k)^2 - 12*baseX k - 12 := by
  dsimp [baseA, baseX]
  field_simp
  ring

theorem base_second_square (k y : ℚ) (hk : k^2-1 ≠ 0)
    (hy : y^2 = quartic k) :
    (baseB k y)^2 = 1 - 6*baseX k - 3*(baseX k)^2 := by
  dsimp [baseB, baseX]
  field_simp
  dsimp [quartic] at hy
  linear_combination 4*hy

def cubic (u : ℚ) := u^3 + 10*u^2 + 609*u + 1764
def curveK (u v : ℚ) := (v+42)/(2*u)
def curveY (u v : ℚ) := (u+5)/2 - (curveK u v)^2

theorem cubic_to_quartic (u v : ℚ) (hu : u ≠ 0) (hv : v^2 = cubic u) :
    (curveY u v)^2 = quartic (curveK u v) := by
  have hi : (curveY u v)^2 - quartic (curveK u v) = (cubic u-v^2)/(4*u) := by
    dsimp [curveY, curveK, quartic, cubic]
    field_simp
    ring
  rw [← hv, sub_self, zero_div] at hi
  exact sub_eq_zero.mp hi

theorem quartic_to_cubic (k y : ℚ) (hy : y^2 = quartic k) :
    let u := 2*y + 2*k^2 - 5
    (2*u*k-42)^2 = cubic u := by
  dsimp [cubic]
  dsimp [quartic] at hy
  linear_combination (-4*(2*y+2*k^2-5))*hy

#print axioms four_fiber_squares
#print axioms base_second_square
#print axioms cubic_to_quartic
#print axioms quartic_to_cubic
end Erdos213.SplitFiber
