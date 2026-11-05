import FormalConjecturesUtil

/-! The integer-residue obstruction for the exceptional gap pattern (1,2,1).
 -/
namespace SquarefreeFourthSign

set_option autoImplicit false

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Four products whose quotients have both previous minors equal to one
at gaps `(1,2,1)` cannot fit in an interval of width less than the first base.
The integrality of `x,Q,k` is essential to the proof. -/
theorem exceptional_no_short_interval (N H x Q k : ℤ)
    (hx : 2 ≤ x) (hH : H < x)
    (h₀ : N < Q * x ^ 2) (h₀' : Q * x ^ 2 ≤ N + H)
    (h₁ : N < (Q-k-1) * (x+1) ^ 2) (h₁' : (Q-k-1) * (x+1) ^ 2 ≤ N+H)
    (h₂ : N < (Q-3*k-2) * (x+3) ^ 2) (h₂' : (Q-3*k-2) * (x+3) ^ 2 ≤ N+H)
    (h₃ : N < (Q-4*k-2) * (x+4) ^ 2) (h₃' : (Q-4*k-2) * (x+4) ^ 2 ≤ N+H) : False := by
  let X : ℝ := (x : ℝ) + 2
  let n₀ : ℤ := Q * x ^ 2
  let n₁ : ℤ := (Q-k-1) * (x+1) ^ 2
  let n₂ : ℤ := (Q-3*k-2) * (x+3) ^ 2
  let n₃ : ℤ := (Q-4*k-2) * (x+4) ^ 2
  let α : ℝ := (Q : ℝ) - 2*k - 5/3
  let β : ℝ := -(k : ℝ) - 1/2
  let l : ℝ := 2*α*X + β*X^2
  let m : ℝ := α + 2*β*X + X^2/6
  let d₁ : ℝ := (n₂ : ℝ) - n₁
  let d₂ : ℝ := (n₃ : ℝ) - n₀
  have hxR : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hHR : (H : ℝ) < x := by exact_mod_cast hH
  have hX : 4 ≤ X := by dsimp [X]; linarith
  have hX0 : 0 < X := by linarith
  have hn₀ : (N : ℝ) < n₀ := by exact_mod_cast h₀
  have hn₀' : (n₀ : ℝ) ≤ (N : ℝ)+H := by exact_mod_cast h₀'
  have hn₁ : (N : ℝ) < n₁ := by exact_mod_cast h₁
  have hn₁' : (n₁ : ℝ) ≤ (N : ℝ)+H := by exact_mod_cast h₁'
  have hn₂ : (N : ℝ) < n₂ := by exact_mod_cast h₂
  have hn₂' : (n₂ : ℝ) ≤ (N : ℝ)+H := by exact_mod_cast h₂'
  have hn₃ : (N : ℝ) < n₃ := by exact_mod_cast h₃
  have hn₃' : (n₃ : ℝ) ≤ (N : ℝ)+H := by exact_mod_cast h₃'
  have hd₁ : -(x : ℝ) < d₁ ∧ d₁ < x := by dsimp [d₁]; constructor <;> linarith
  have hd₂ : -(x : ℝ) < d₂ ∧ d₂ < x := by dsimp [d₂]; constructor <;> linarith
  have hlid : l = (2/3 : ℝ)*d₁ - (1/12 : ℝ)*d₂ := by
    dsimp [l, α, β, X, d₁, d₂, n₀, n₁, n₂, n₃]
    push_cast
    ring
  have hlabs : -(3*X/4) < l ∧ l < 3*X/4 := by
    rw [hlid]
    dsimp [X]
    constructor <;> linarith [hd₁.1, hd₁.2, hd₂.1, hd₂.2]
  -- `l/X` is in `(-10/3) + (1/2) ℤ`. The previous bound excludes
  -- the next residue below `-1/3`; this combines the even/odd cases.
  let K : ℤ := 4*Q - 8*k - 2*k*(x+2) - (x+2)
  have hKidentity : 6*l = X*(3*(K : ℝ)-20) := by
    dsimp [l, α, β, X, K]
    push_cast
    ring
  have hKreal : (31 : ℝ) < 6*(K : ℝ) := by
    have hmul : 31*X < (6*(K : ℝ))*X := by nlinarith [hlabs.1]
    exact (mul_lt_mul_iff_left₀ hX0).mp (by simpa only [mul_comm] using hmul)
  have hKint : (31 : ℤ) < 6*K := by exact_mod_cast hKreal
  have hKsix : (6 : ℤ) ≤ K := by omega
  have hKsixR : (6 : ℝ) ≤ K := by exact_mod_cast hKsix
  have hlower : -X/3 ≤ l := by
    have hp := mul_nonneg (show 0 ≤ (K : ℝ)-6 by linarith) hX0.le
    nlinarith [hKidentity]
  have hmid : 3*m+5/2 = ((n₀ : ℝ)+(n₃ : ℝ)-(n₁ : ℝ)-(n₂ : ℝ))/2 := by
    dsimp [m, α, β, X, n₀, n₁, n₂, n₃]
    push_cast
    ring
  have hmlower : -X/3-1/6 < m := by
    have hpair : -(x : ℝ) < ((n₀ : ℝ)+(n₃ : ℝ)-(n₁ : ℝ)-(n₂ : ℝ))/2 := by linarith
    rw [← hmid] at hpair
    dsimp [X]
    linarith
  have hid : 9*X^2*d₂ = (36*X^2-48)*l + 96*X*m + 32*X^3 := by
    dsimp [d₂, l, m, α, β, X, n₀, n₃]
    push_cast
    ring
  have hcoeff : 0 ≤ 36*X^2-48 := by nlinarith [sq_nonneg (X-4)]
  have h₄ := mul_le_mul_of_nonneg_left hlower hcoeff
  have h₅ := mul_lt_mul_of_pos_left hmlower (show 0 < 96*X by positivity)
  have hd₂lower : (20*X-32)*X^2 < 9*X^2*d₂ := by nlinarith [hid]
  have hd₂upper : 9*X^2*d₂ < 9*X^2*(X-2) := by
    apply mul_lt_mul_of_pos_left _ (by positivity)
    dsimp [X]
    linarith [hd₂.2]
  have hlast : 9*X^2*(X-2) < (20*X-32)*X^2 := by
    have hpos := mul_pos (show 0 < 11*X-14 by linarith) (sq_pos_of_pos hX0)
    nlinarith
  linarith

end SquarefreeFourthSign
