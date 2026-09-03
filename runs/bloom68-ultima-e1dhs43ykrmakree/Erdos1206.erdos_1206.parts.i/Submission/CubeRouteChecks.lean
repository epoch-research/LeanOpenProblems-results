import Mathlib

namespace CubeRouteChecks

/-- Three common translates already force triviality. -/
theorem three_translates_trivial (a b c d : ℚ)
    (h0 : a ^ 3 + b ^ 3 = c ^ 3 + d ^ 3)
    (h1 : (1+a) ^ 3 + (1+b) ^ 3 = (1+c) ^ 3 + (1+d) ^ 3)
    (hm : (-1+a) ^ 3 + (-1+b) ^ 3 = (-1+c) ^ 3 + (-1+d) ^ 3) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hs : a + b = c + d := by nlinarith [h0, h1, hm]
  have hq : a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2 := by nlinarith [h0, h1, hm]
  have hp : a*b = c*d := by
    nlinarith [congrArg (fun x : ℚ => x ^ 2) hs]
  have hz : (a-c)*(a-d) = 0 := by
    nlinarith [congrArg (fun x : ℚ => a*x) hs]
  rcases mul_eq_zero.mp hz with h | h
  · left
    constructor <;> linarith
  · right
    constructor <;> linarith

theorem free_translate_trivial (a b c d : ℚ)
    (h : ∀ t : ℚ, (t+a)^3 + (t+b)^3 = (t+c)^3 + (t+d)^3) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  apply three_translates_trivial a b c d
  · simpa using h 0
  · exact h 1
  · exact h (-1)

def A (t : ℤ) : ℤ :=
  7776*t^6 + 9072*t^5 + 7128*t^4 + 1692*t^3 + 282*t^2 + 33*t + 1

def B (t : ℤ) : ℤ :=
  1296*t^5 - 1296*t^4 - 1188*t^3 - 96*t^2 + 3*t + 1

def C (t : ℤ) : ℤ :=
  7776*t^6 + 9072*t^5 + 7128*t^4 + 1692*t^3 + 138*t^2 + 9*t + 1

def D (t : ℤ) : ℤ :=
  1296*t^5 + 3888*t^4 + 1404*t^3 + 336*t^2 + 27*t + 1

set_option maxHeartbeats 2000000 in
theorem polynomial_collision (t : ℤ) :
    A t ^ 3 + B t ^ 3 = C t ^ 3 + D t ^ 3 := by
  dsimp [A, B, C, D]
  ring

theorem congruence (m k : ℤ) :
    A (m*k) % m = 1 % m ∧ B (m*k) % m = 1 % m ∧
    C (m*k) % m = 1 % m ∧ D (m*k) % m = 1 % m := by
  simp [A, B, C, D, Int.add_emod, Int.sub_emod, Int.mul_emod, pow_succ]

theorem diff_AC (t : ℤ) : A t - C t = 24*t*(6*t+1) := by
  dsimp [A, C]
  ring

theorem diff_DB (t : ℤ) : D t - B t = 24*t*(6*t+1)^3 := by
  dsimp [D, B]
  ring

theorem positive_and_ordered (t : ℤ) (ht : 2 ≤ t) :
    0 < B t ∧ B t < D t ∧ D t < C t ∧ C t < A t := by
  have ht0 : 0 < t := by omega
  have hx : 0 ≤ t - 2 := by omega
  have hb : B t = 1296*(t-2)^5 + 11664*(t-2)^4 + 40284*(t-2)^3 +
      65352*(t-2)^2 + 47571*(t-2) + 10855 := by
    dsimp [B]
    ring
  have hcd : C t - D t = 7776*(t-2)^6 + 101088*(t-2)^5 +
      547560*(t-2)^4 + 1581408*(t-2)^3 + 2567610*(t-2)^2 +
      2221398*(t-2) + 799812 := by
    dsimp [C, D]
    ring
  have hB : 0 < B t := by rw [hb]; positivity
  have hDB : 0 < D t - B t := by rw [diff_DB]; positivity
  have hCD : 0 < C t - D t := by rw [hcd]; positivity
  have hAC : 0 < A t - C t := by rw [diff_AC]; positivity
  exact ⟨hB, by omega, by omega, by omega⟩

/-- A growth bound explaining why this family alone cannot force density regularity. -/
theorem B_ge_fifth_power (t : ℤ) (ht : 2 ≤ t) : t^5 ≤ B t := by
  have hx : 0 ≤ t - 2 := by omega
  have hid : B t - t^5 = 1295*(t-2)^5 + 11654*(t-2)^4 +
      40244*(t-2)^3 + 65272*(t-2)^2 + 47491*(t-2) + 10823 := by
    dsimp [B]
    ring
  have hpos : 0 ≤ B t - t^5 := by rw [hid]; positivity
  omega

/-- Every positive residue progression has a nontrivial positive four-cube collision. -/
theorem residue_collision (m r : ℤ) (hm : 0 < m) (hr : 0 < r) :
    ∃ a b c d : ℤ,
      0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
      a % m = r % m ∧ b % m = r % m ∧ c % m = r % m ∧ d % m = r % m ∧
      a^3 + b^3 = c^3 + d^3 ∧ a ≠ c ∧ a ≠ d := by
  have ht : 2 ≤ m*2 := by omega
  obtain ⟨hB, hBD, hDC, hCA⟩ := positive_and_ordered (m*2) ht
  have hD : 0 < D (m*2) := lt_trans hB hBD
  have hC : 0 < C (m*2) := lt_trans hD hDC
  have hA : 0 < A (m*2) := lt_trans hC hCA
  obtain ⟨hAm, hBm, hCm, hDm⟩ := congruence m 2
  have hscale : ∀ z : ℤ, z % m = 1 % m → (r*z) % m = r % m := by
    intro z hz
    rw [Int.mul_emod, hz, ← Int.mul_emod, mul_one]
  refine ⟨r*A (m*2), r*B (m*2), r*C (m*2), r*D (m*2),
    mul_pos hr hA, mul_pos hr hB, mul_pos hr hC, mul_pos hr hD,
    hscale _ hAm, hscale _ hBm, hscale _ hCm, hscale _ hDm, ?_, ?_, ?_⟩
  · calc
      (r*A (m*2))^3 + (r*B (m*2))^3 = r^3*(A (m*2)^3 + B (m*2)^3) := by ring
      _ = r^3*(C (m*2)^3 + D (m*2)^3) := by rw [polynomial_collision]
      _ = (r*C (m*2))^3 + (r*D (m*2))^3 := by ring
  · exact ne_of_gt (mul_lt_mul_of_pos_left hCA hr)
  · exact ne_of_gt (mul_lt_mul_of_pos_left (lt_trans hDC hCA) hr)

#print axioms three_translates_trivial
#print axioms polynomial_collision
#print axioms congruence
#print axioms positive_and_ordered
#print axioms residue_collision
#print axioms B_ge_fifth_power

end CubeRouteChecks
