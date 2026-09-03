import Submission.SquareRootObstruction
import Submission.ValuationStructure

/-! Classification of dyadic fractions whose multiplication-by-three orbit
never has leading ternary digit two. This is a periodic-orbit result, not
a proof of finiteness for the integer powers in Erdős 406. -/
namespace Erdos406DyadicOrbit
open Erdos406Work Erdos406Structure

/-- Exact reachability inside an odd residue class modulo eight. -/
lemma nine_orbit_residue (a r k : ℕ) (ha : Odd a)
    (hr : r < 2 ^ (k + 3)) (har : a % 8 = r % 8) :
    ∃ j : ℕ, a * 9 ^ j % 2 ^ (k + 3) = r := by
  let N := 2 ^ (k + 3)
  have h8 : 8 ∣ N := by
    change 2 ^ 3 ∣ 2 ^ (k + 3)
    exact pow_dvd_pow 2 (by omega)
  have hcr : (N - r) + r = N := Nat.sub_add_cancel (by omega)
  have hab : 8 ∣ N - r + a := by
    apply Nat.dvd_of_mod_eq_zero
    have hn := Nat.mod_eq_zero_of_dvd h8
    have hc := congrArg (fun x : ℕ => x % 8) hcr
    omega
  obtain ⟨j, _, hd⟩ := affine_nine_pow_divisible (N-r) a 0 k ha hab
  have hm : Nat.ModEq N (N-r+a*9^j) (N-r+r) := by
    rw [hcr]
    exact (Nat.modEq_zero_iff_dvd.mpr hd).trans (by simp [N, Nat.ModEq])
  have he := hm.add_left_cancel' (N-r)
  change a * 9 ^ j % N = r % N at he
  exact ⟨j, he.trans (Nat.mod_eq_of_lt hr)⟩

lemma odd_large_orbit_escape (a k : ℕ) (ha : Odd a) :
    ∃ j : ℕ, 2 * 2 ^ (k + 4) ≤ 3 * (3 ^ j * a % 2 ^ (k + 4)) := by
  let N := 2 ^ (k + 4)
  have hN : 16 ≤ N := by
    change 2 ^ 4 ≤ 2 ^ (k + 4)
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have h8 : N % 8 = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    change 2 ^ 3 ∣ 2 ^ (k + 4)
    exact pow_dvd_pow 2 (by omega)
  have hodd := Nat.odd_iff.mp ha
  have hcases : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by omega
  have hstep (b : ℕ) (hb : Odd b) (hb3 : 3 ≤ b % 8) :
      ∃ j : ℕ, 2 * N ≤ 3 * (b * 9 ^ j % N) := by
    let r := N - 8 + b % 8
    have hr : r < N := by dsimp [r]; omega
    have hbr : b % 8 = r % 8 := by
      have hh : (N-8)%8 = 0 := by omega
      dsimp [r]
      rw [Nat.add_mod, hh]
      simp
    obtain ⟨j, hj⟩ := nine_orbit_residue b r (k+1) hb hr hbr
    refine ⟨j, ?_⟩
    change b * 9 ^ j % N = r at hj
    rw [hj]
    dsimp [r]
    omega
  rcases hcases with h | h | h | h
  · have hb : (3*a)%8 = 3 := by omega
    obtain ⟨j, hj⟩ := hstep (3*a) ((by decide : Odd (3 : ℕ)).mul ha) (by omega)
    refine ⟨2*j+1, ?_⟩
    have he : 3 ^ (2*j+1) * a = (3*a)*9^j := by
      rw [pow_add, pow_mul]
      norm_num
      ring
    simpa only [he] using hj
  all_goals
    obtain ⟨j, hj⟩ := hstep a ha (by omega)
    refine ⟨2*j, ?_⟩
    have he : 3 ^ (2*j) * a = a*9^j := by
      rw [pow_mul]
      norm_num
      ring
    simpa only [he] using hj

/-- The leading ternary digit of every orbit point is zero or one. -/
def AvoidsTwo (a k : ℕ) : Prop :=
  ∀ j : ℕ, 3 * (3 ^ j * a % 2 ^ k) < 2 * 2 ^ k

lemma avoidsTwo_double (a k : ℕ) (h : AvoidsTwo (2*a) (k+1)) :
    AvoidsTwo a k := by
  intro j
  have hh := h j
  rw [pow_succ', show 3^j*(2*a) = 2*(3^j*a) by ring,
    Nat.mul_mod_mul_left] at hh
  omega

/-- In reduced terms, only denominators two and eight are possible. -/
theorem avoidsTwo_necessary (a k : ℕ) (ha : a < 2 ^ k) (h : AvoidsTwo a k) :
    a = 0 ∨ 2*a = 2^k ∨ 8*a = 2^k ∨ 8*a = 3*2^k := by
  induction k generalizing a with
  | zero => simp only [pow_zero] at ha ⊢; omega
  | succ k ih =>
    rcases Nat.even_or_odd a with ⟨b, hb⟩ | ho
    · have hab : a = 2*b := by omega
      have hba : b < 2^k := by rw [pow_succ'] at ha; omega
      have hbb := ih b hba (avoidsTwo_double b k (by rwa [← hab]))
      rw [pow_succ']
      rcases hbb with hbb | hbb | hbb | hbb
      · left; omega
      · right; left; omega
      · right; right; left; omega
      · right; right; right; omega
    · have hk : k ≤ 2 := by
        by_contra hn
        obtain ⟨j, hj⟩ := odd_large_orbit_escape a (k-3) ho
        have he : k-3+4 = k+1 := by omega
        rw [he] at hj
        exact (not_lt_of_ge hj) (h j)
      have h0 := h 0
      have h1 := h 1
      have hao := Nat.odd_iff.mp ho
      interval_cases k <;> norm_num at ha ⊢ <;> interval_cases a <;>
        norm_num at *

lemma scaled_orbit_remainder (a N c d j : ℕ) (h : c*a = d*N) :
    c * (3^j*a % N) = (3^j*d % c)*N := by
  rw [← Nat.mul_mod_mul_left]
  have he : c*(3^j*a) = (3^j*d)*N := by
    calc
      _ = 3^j*(c*a) := by ring
      _ = _ := by rw [h]; ring
  rw [he, Nat.mul_mod_mul_right]

/-- Exact integer formulation of the four dyadic fractions
`0`, `1/2`, `1/8`, and `3/8`. -/
theorem avoidsTwo_iff (a k : ℕ) (ha : a < 2^k) :
    AvoidsTwo a k ↔ a = 0 ∨ 2*a = 2^k ∨ 8*a = 2^k ∨ 8*a = 3*2^k := by
  refine ⟨avoidsTwo_necessary a k ha, ?_⟩
  intro h j
  have hp : 0 < 2^k := by positivity
  rcases h with rfl | h | h | h
  · simp
  · have hh := scaled_orbit_remainder a (2^k) 2 1 j (by simpa using h)
    have hm : 3^j%2 = 1 := by norm_num [Nat.pow_mod]
    simp only [mul_one, hm, one_mul] at hh
    omega
  · have hh := scaled_orbit_remainder a (2^k) 8 1 j (by simpa using h)
    simp only [mul_one] at hh
    rcases three_pow_mod_eight j with hm | hm <;> rw [hm] at hh <;> omega
  · have hh := scaled_orbit_remainder a (2^k) 8 3 j h
    rw [← pow_succ] at hh
    rcases three_pow_mod_eight (j+1) with hm | hm <;> rw [hm] at hh <;> omega

#print axioms nine_orbit_residue
#print axioms odd_large_orbit_escape
#print axioms avoidsTwo_iff
end Erdos406DyadicOrbit
