import Submission.Classification

/-!
# Type I witnesses arbitrarily close to the ordered upper bound

This file proves conditional Type I identities and applies the ordinary
Dirichlet theorem (already in Mathlib) to infinitely many hard primes. It
never claims a decomposition for *every* hard prime and never imports or
modifies `Submission/Spec.lean`.
-/

namespace Erdos242

/-- Reparametrization of `p=4r(r+1)s-(2r+1)` with `r=v+1`, `s=t+1`,
written without any Nat subtraction. -/
def nearHalfP (v t : ℕ) : ℕ :=
  4 * (v + 1) * (v + 2) * t + 4 * v ^ 2 + 10 * v + 5

/-- The corresponding first denominator. -/
def nearHalfX (v t : ℕ) : ℕ :=
  (v + 1) * ((2 * v + 3) * t + 2 * (v + 1))

/-- The key identity makes the first denominator approach `p/2` from below
as `v` grows; the `+1` is exact and important for coprimality. -/
theorem nearHalf_identity (v t : ℕ) :
    4 * (v + 2) * nearHalfX v t =
      (2 * v + 3) * nearHalfP v t + 1 := by
  simp only [nearHalfP, nearHalfX]
  ring

/-- All members of this elementary family have a positive Type I divisor.
No primality is needed for this conditional assertion. -/
theorem nearHalf_typeI (v t : ℕ) : TypeI (nearHalfP v t) (nearHalfX v t) := by
  let r := v + 1
  let q := 2 * r + 1
  let p := nearHalfP v t
  let x := nearHalfX v t
  let a := 4 * r ^ 2 * t + 4 * v ^ 2 + 6 * v + 3
  let c := r * x
  have haeq : a + p = 4 * x := by
    dsimp [a, p, x, nearHalfP, nearHalfX, r]
    ring
  have ha : 0 < a := by dsimp [a]; positivity
  have hax : 4 * x - p = a := by omega
  have hc : 0 < c := by dsimp [c, r, x, nearHalfX]; positivity
  have hcdvd : c ∣ x ^ 2 := by
    refine ⟨q * t + 2 * r, ?_⟩
    dsimp [c, x, nearHalfX, q, r]
    ring
  have hmult : q * a = 4 * c + 1 := by
    dsimp [q, a, c, x, nearHalfX, r]
    ring
  change TypeI p x
  exact ⟨c, hc, hcdvd, by rw [hax]; exact ⟨q, by simpa only [mul_comm] using hmult.symm⟩⟩

/-- For every parameter choice, the Type I construction gives an ordered
solution; `p/4<x<p/2` is proved explicitly rather than assumed. -/
theorem nearHalf_good (v t : ℕ) : Good (nearHalfP v t) := by
  let r := v + 1
  let p := nearHalfP v t
  let x := nearHalfX v t
  have haeq : p + 1 = 2 * x + 2 * r * (t + 1) := by
    dsimp [p, x, r, nearHalfP, nearHalfX]
    ring
  have hrt : 0 < r * (t + 1) := Nat.mul_pos (by dsimp [r]; omega) (by omega)
  have hhi : 2 * x < p := by nlinarith only [haeq, hrt]
  have hlow : p < 4 * x := by
    have ha : 0 < 4 * r ^ 2 * t + 4 * v ^ 2 + 6 * v + 3 := by positivity
    have ha4 : 4 * x = p + (4 * r ^ 2 * t + 4 * v ^ 2 + 6 * v + 3) := by
      dsimp [p, x, r, nearHalfP, nearHalfX]
      ring
    omega
  exact good_of_typeI p x (by dsimp [p, nearHalfP]; positivity)
    hlow hhi (nearHalf_typeI v t)

/-- The residue `b=A-(2v+3)` is coprime to `A`; indeed
`(2v+3)^2=A+1`, and `b+(2v+3)=A`. -/
theorem nearHalf_progression_coprime (v : ℕ) :
    (4 * v ^ 2 + 10 * v + 5).Coprime (4 * (v + 1) * (v + 2)) := by
  let b := 4 * v ^ 2 + 10 * v + 5
  let q := 2 * v + 3
  let A := 4 * (v + 1) * (v + 2)
  have hsum : b + q = A := by dsimp [b, q, A]; ring
  have hsq : q * q = A + 1 := by dsimp [q, A]; ring
  change b.Coprime A
  apply Nat.coprime_of_dvd
  intro ell hell hellb hellA
  have hellq : ell ∣ q := by
    have hsumdiv : ell ∣ b + q := by rw [hsum]; exact hellA
    exact (Nat.dvd_add_iff_left hellb).mpr (by simpa only [add_comm] using hsumdiv)
  have hellextra : ell ∣ A + 1 := by
    rw [← hsq]
    exact hellq.mul_right q
  have hellone : ell ∣ 1 :=
    (Nat.dvd_add_iff_left hellA).mpr (by simpa only [add_comm] using hellextra)
  exact (ne_of_gt hell.one_lt) (Nat.dvd_one.mp hellone)

/-- For each `B`, there are hard primes arbitrarily far out with a Type I
ordered solution whose first denominator obeys
`4(12B+12)x=(24B+23)p+1`. The ratio `x/p` therefore approaches `1/2`
from below as `B` increases. This is a *family*, not an all-prime proof. -/
theorem infinitely_many_near_half_typeI (B N : ℕ) :
    ∃ p x : ℕ, N < p ∧ p.Prime ∧ p % 24 = 1 ∧
      TypeI p x ∧ Good p ∧ 2 * x < p ∧
      4 * (12 * B + 12) * x = (24 * B + 23) * p + 1 := by
  let v := 12 * B + 10
  let A := 4 * (v + 1) * (v + 2)
  let b := 4 * v ^ 2 + 10 * v + 5
  have hA : A ≠ 0 := by dsimp [A]; positivity
  have hcop : b.Coprime A := nearHalf_progression_coprime v
  obtain ⟨p, hpN, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq N (q := A) (a := b) hA hcop
  have hb_lt : b < A := by
    have hsum : b + (2 * v + 3) = A := by dsimp [b, A]; ring
    omega
  have hrem : p % A = b := by
    have h := hmod
    change p % A = b % A at h
    simpa only [Nat.mod_eq_of_lt hb_lt] using h
  let t := p / A
  have heq : p = nearHalfP v t := by
    have hdiv : p = A * t + b := by
      calc
        p = p % A + A * (p / A) := (Nat.mod_add_div p A).symm
        _ = A * t + b := by rw [hrem]; simp only [t, add_comm]
    calc
      p = A * t + b := hdiv
      _ = nearHalfP v t := by dsimp [A, b, nearHalfP]; ring
  let x := nearHalfX v t
  have hprime : (nearHalfP v t).Prime := by rw [← heq]; exact hp
  have hp24 : p % 24 = 1 := by
    have hform : p = 24 *
        (2 * (12 * B + 11) * (B + 1) * t + 24 * B ^ 2 + 45 * B + 21) + 1 := by
      rw [heq]
      dsimp [nearHalfP, v]
      ring
    rw [hform]
    simp
  have htype : TypeI p x := by rw [heq]; exact nearHalf_typeI v t
  have hgood : Good p := by rw [heq]; exact nearHalf_good v t
  have hhi : 2 * x < p := by
    have haeq : p + 1 = 2 * x + 2 * (v + 1) * (t + 1) := by
      rw [heq]
      dsimp [x, nearHalfP, nearHalfX]
      ring
    have hpos : 0 < (v + 1) * (t + 1) := by positivity
    nlinarith only [haeq, hpos]
  refine ⟨p, x, hpN, hp, hp24, htype, hgood, hhi, ?_⟩
  have hkey := nearHalf_identity v t
  rw [← heq] at hkey
  dsimp [v, x] at hkey ⊢
  convert hkey using 1; ring

end Erdos242
