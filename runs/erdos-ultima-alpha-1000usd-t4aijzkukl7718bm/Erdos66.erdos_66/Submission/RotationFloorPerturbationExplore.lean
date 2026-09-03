import Submission.RationalRotationGridExplore

/-! Floor-difference rotation counts are stable on a rational approximation
block. The estimate is uniform in the starting phase and interval width. -/
namespace Erdos66RotationFloorPerturbation
open Erdos66RationalRotationGrid
open scoped Classical
set_option maxHeartbeats 1800000

noncomputable def rotationSum (α x θ : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, ((⌊x+(k : ℝ)*α⌋-⌊x+(k : ℝ)*α-θ⌋ : ℤ) : ℝ)

lemma rotationSum_add (α x θ : ℝ) (N K : ℕ) :
    rotationSum α x θ (N+K) = rotationSum α x θ N + rotationSum α (x+N*α) θ K := by
  rw [rotationSum,Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have he : x+((N+k : ℕ) : ℝ)*α=x+(N : ℝ)*α+(k : ℝ)*α := by push_cast; ring
  rw [he]

lemma rotationSum_zero (α x θ : ℝ) : rotationSum α x θ 0=0 := by simp [rotationSum]

lemma floor_diff_error (x y : ℝ) : |((⌊x⌋-⌊y⌋ : ℤ) : ℝ)-(x-y)| ≤ 1 := by
  have hx := Int.floor_le x
  have hx' := Int.lt_floor_add_one x
  have hy := Int.floor_le y
  have hy' := Int.lt_floor_add_one y
  push_cast
  rw [abs_le]
  constructor <;> linarith

/-- A full reduced rational orbit has error at most one for every floor
window, including windows wider than one. -/
lemma rational_rotation_error (r : ℚ) (x θ : ℝ) :
    |rotationSum (r : ℝ) x θ r.den-(r.den : ℝ)*θ| ≤ 1 := by
  have he := rational_floor_difference r x (x-θ)
  have he' := congrArg (fun z : ℤ ↦ (z : ℝ)) he
  push_cast at he'
  have harg (k : ℕ) : x-θ+(k : ℝ)*(r : ℝ)=x+(k : ℝ)*(r : ℝ)-θ := by ring
  simp_rw [harg] at he'
  have hsum : rotationSum (r : ℝ) x θ r.den =
      (⌊(r.den : ℝ)*x⌋ : ℝ)-(⌊(r.den : ℝ)*(x-θ)⌋ : ℝ) := by
    simpa only [rotationSum,Int.cast_sub] using he'
  rw [hsum]
  have hh := floor_diff_error ((r.den : ℝ)*x) ((r.den : ℝ)*(x-θ))
  push_cast at hh
  rw [show (r.den : ℝ)*x-(r.den : ℝ)*(x-θ)=(r.den : ℝ)*θ by ring] at hh
  exact hh

/-- Pointwise displacement at most eps gives a two-sided expanded-window
comparison. The rational full-block formula controls the expanded windows. -/
theorem rational_block_perturbation (r : ℚ) (α x θ ε : ℝ) (_hε : 0 ≤ ε)
    (hnear : ∀ k < r.den, |(k : ℝ)*(α-(r : ℝ))| ≤ ε) :
    |rotationSum α x θ r.den-(r.den : ℝ)*θ| ≤ 2*(r.den : ℝ)*ε+1 := by
  have hlo : rotationSum (r : ℝ) (x-ε) (θ-2*ε) r.den ≤ rotationSum α x θ r.den := by
    apply Finset.sum_le_sum
    intro k hk
    have h := abs_le.mp (hnear k (Finset.mem_range.mp hk))
    have h1 := Int.floor_le_floor (show x-ε+(k : ℝ)*(r : ℝ) ≤ x+(k : ℝ)*α by nlinarith)
    have h2 := Int.floor_le_floor (show x+(k : ℝ)*α-θ ≤
      x-ε+(k : ℝ)*(r : ℝ)-(θ-2*ε) by nlinarith)
    exact_mod_cast (show (⌊x-ε+(k : ℝ)*(r : ℝ)⌋-⌊x-ε+(k : ℝ)*(r : ℝ)-(θ-2*ε)⌋ : ℤ) ≤
      ⌊x+(k : ℝ)*α⌋-⌊x+(k : ℝ)*α-θ⌋ by omega)
  have hup : rotationSum α x θ r.den ≤ rotationSum (r : ℝ) (x+ε) (θ+2*ε) r.den := by
    apply Finset.sum_le_sum
    intro k hk
    have h := abs_le.mp (hnear k (Finset.mem_range.mp hk))
    have h1 := Int.floor_le_floor (show x+(k : ℝ)*α ≤ x+ε+(k : ℝ)*(r : ℝ) by nlinarith)
    have h2 := Int.floor_le_floor (show x+ε+(k : ℝ)*(r : ℝ)-(θ+2*ε) ≤
      x+(k : ℝ)*α-θ by nlinarith)
    exact_mod_cast (show (⌊x+(k : ℝ)*α⌋-⌊x+(k : ℝ)*α-θ⌋ : ℤ) ≤
      ⌊x+ε+(k : ℝ)*(r : ℝ)⌋-⌊x+ε+(k : ℝ)*(r : ℝ)-(θ+2*ε)⌋ by omega)
  have h1 := abs_le.mp (rational_rotation_error r (x-ε) (θ-2*ε))
  have h2 := abs_le.mp (rational_rotation_error r (x+ε) (θ+2*ε))
  rw [abs_le]
  constructor <;> nlinarith

lemma block_error_of_approximation (r : ℚ) (α x θ B : ℝ)
    (h : (r.den : ℝ)^2*|α-(r : ℝ)| ≤ B) :
    |rotationSum α x θ r.den-(r.den : ℝ)*θ| ≤ 2*B+1 := by
  have hh := rational_block_perturbation r α x θ
    ((r.den : ℝ)*|α-(r : ℝ)|) (by positivity) (by
      intro k hk
      rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg k)]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk.le) (abs_nonneg _))
  nlinarith

end Erdos66RotationFloorPerturbation
