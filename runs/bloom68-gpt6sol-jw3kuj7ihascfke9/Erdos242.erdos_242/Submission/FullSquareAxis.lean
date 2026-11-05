import Submission.ReciprocityFamilies

/-!
# The square-divisor modular axis is not the `d ∣ m` B-axis

`BAxisInvestigation.md` and its certificate programs use `d ∣ m`.
The broader condition `d ∣ m²` has witnesses even at all three of that
axis's recorded exceptions. Nothing in this file proves pointwise coverage
of all hard primes or imports `Submission/Spec.lean`.
-/

namespace Erdos242

/-- The question's modular condition, including its two size restrictions. -/
def FullSquareAxis (p : ℕ) : Prop :=
  ∃ m d : ℕ, 0 < m ∧ m ≤ (p - 1) / 6 ∧ 0 < d ∧
    d ∣ m ^ 2 ∧ 4 * d < p ∧ 4 * m - 1 ∣ p + 4 * d

/-- For `p ≡ 1 (mod 24)`, the `m` bound already follows from `4d < p`.
Indeed, if `a = (p+4d)/(4m-1)`, then `a ≡ 3 (mod 4)`, so
`3(4m-1) ≤ p+4d < 2p`. -/
theorem full_square_axis_bound (p m d : ℕ) (h24 : p % 24 = 1)
    (hm : 0 < m) (hsmall : 4 * d < p)
    (hdiv : 4 * m - 1 ∣ p + 4 * d) : m ≤ (p - 1) / 6 := by
  let h := 4 * m - 1
  let a := (p + 4 * d) / h
  have hfour : h + 1 = 4 * m := by dsimp [h]; omega
  have heq : h * a = p + 4 * d := by
    simpa only [h, a] using (Nat.mul_div_cancel' hdiv)
  have hmod : p + 4 * d + a = 4 * (m * a) := by
    calc
      p + 4 * d + a = h * a + a := by rw [heq]
      _ = (h + 1) * a := by ring
      _ = 4 * (m * a) := by rw [hfour]; ring
  have ha3 : a % 4 = 3 := by
    have hp4 : p % 4 = 1 := by omega
    have hmod4 : (p + 4 * d + a) % 4 = 0 := by rw [hmod]; omega
    omega
  have ha : 3 ≤ a := by simpa only [ha3] using (Nat.mod_le a 4)
  have hbound : 3 * h ≤ p + 4 * d := by
    calc
      3 * h ≤ a * h := Nat.mul_le_mul_right h ha
      _ = p + 4 * d := by rw [mul_comm, heq]
  omega

/-- Equivalently, for the stated hard residue class only the offset bound
`4d < p` needs to be imposed explicitly. -/
theorem full_square_axis_iff (p : ℕ) (h24 : p % 24 = 1) :
    FullSquareAxis p ↔
      ∃ m d : ℕ, 0 < m ∧ 0 < d ∧ d ∣ m ^ 2 ∧
        4 * d < p ∧ 4 * m - 1 ∣ p + 4 * d := by
  constructor
  · rintro ⟨m, d, hm, _, hd, hdsq, hsmall, hdiv⟩
    exact ⟨m, d, hm, hd, hdsq, hsmall, hdiv⟩
  · rintro ⟨m, d, hm, hd, hdsq, hsmall, hdiv⟩
    exact ⟨m, d, hm, full_square_axis_bound p m d h24 hm hsmall hdiv,
      hd, hdsq, hsmall, hdiv⟩


/-- The square-divisor condition and `4d<p` already give a strictly ordered
Erdős–Straus solution, with no primality hypothesis. -/
theorem full_square_axis_good (p : ℕ) (hp : FullSquareAxis p) : Good p := by
  obtain ⟨m, d, hm, _, hd, hdsq, hsmall, hdiv⟩ := hp
  exact good_of_shifted_offset p m d hsmall hm hd hdsq hdiv


/-- Pointwise coverage by this restricted Type-II axis would prove the full
ordered Erdős–Straus assertion; no such coverage is asserted here. -/
theorem all_good_of_full_square_axis
    (hfull : ∀ p : ℕ, p.Prime → p % 24 = 1 → FullSquareAxis p) :
    ∀ n : ℕ, 2 < n → Good n := by
  apply good_of_hard_primes
  intro p hp h24
  exact full_square_axis_good p (hfull p hp h24)

/-- A genuine `d ∣ m²`, `d ∤ m` witness at the first `d ∣ m` B exception:
`15 ∣ 193 + 4*8 = 225`. -/
theorem full_square_axis_193 :
    (193).Prime ∧ 193 % 24 = 1 ∧ FullSquareAxis 193 ∧ Good 193 := by
  have hw : FullSquareAxis 193 := by
    refine ⟨4, 8, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num
  exact ⟨by norm_num, by norm_num, hw, full_square_axis_good 193 hw⟩

/-- Another `d ∣ m²` witness: `47 ∣ 2521 + 4*16 = 2585`. -/
theorem full_square_axis_2521 :
    (2521).Prime ∧ 2521 % 24 = 1 ∧ FullSquareAxis 2521 ∧ Good 2521 := by
  have hw : FullSquareAxis 2521 := by
    refine ⟨12, 16, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num
  exact ⟨by norm_num, by norm_num, hw, full_square_axis_good 2521 hw⟩

/-- A third `d ∣ m²` witness: `39 ∣ 66529 + 4*50 = 66729`. -/
theorem full_square_axis_66529 :
    (66529).Prime ∧ 66529 % 24 = 1 ∧ FullSquareAxis 66529 ∧ Good 66529 := by
  have hw : FullSquareAxis 66529 := by
    refine ⟨10, 50, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num
  exact ⟨by norm_num, by norm_num, hw, full_square_axis_good 66529 hw⟩

/-- In all three witnesses the divisor `d` does not divide `m`. -/
theorem full_square_axis_witnesses_not_restricted :
    ¬ 8 ∣ 4 ∧ ¬ 16 ∣ 12 ∧ ¬ 50 ∣ 10 := by norm_num

/-- For the full `d ∣ m²` condition, a fixed `m` need not have only one
eligible divisor. Both `d=1` and `d=32` work for `p=337`, `m=8`. -/
theorem full_square_axis_two_divisors_at_m8 :
    (337).Prime ∧ 337 % 24 = 1 ∧ 8 ≤ (337 - 1) / 6 ∧
      1 ∣ 8 ^ 2 ∧ 32 ∣ 8 ^ 2 ∧ 4 * 1 < 337 ∧ 4 * 32 < 337 ∧
      (4 * 8 - 1 ∣ 337 + 4 * 1) ∧ (4 * 8 - 1 ∣ 337 + 4 * 32) := by
  norm_num

end Erdos242
