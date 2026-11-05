import Submission.CoveringGap
import Submission.HardTypeISize

/-!
# Bounded Type-II obstructions do not rule out Type I

A CRT/Dirichlet construction can force every Type-II modular parameter `m ≤ B`
to fail. It is *not* a route to a counterexample without also excluding Type I:
this file proves that infinitely many primes in the obstructing progression
still admit explicit ordered Type-I solutions. No theorem from `Spec.lean` is
imported, and no universal solution or counterexample is asserted here.
-/

namespace Erdos242

/-- For each bound and threshold there is a prime `p ≡ 1 (mod 840*(4B)!)`
with a Type-I solution. Every Type-II modular test `4m-1 ∣ p+4d`,
`0<m≤B`, `d∣m²`, fails at this *same* prime. The prime comes from the
near-half Type-I family with `r=840*(4B)!-1`, not a finite search. -/
theorem typeI_primes_escaping_bounded_typeII (B N : ℕ) :
    ∃ p x : ℕ, N < p ∧ p.Prime ∧
      p % (840 * (4 * B).factorial) = 1 ∧ TypeI p x ∧ Good p ∧
      ∀ m d : ℕ, 0 < m → m ≤ B → 0 < d → d ∣ m ^ 2 →
        ¬ (4 * m - 1 ∣ p + 4 * d) := by
  let L := 840 * (4 * B).factorial
  let v := L - 2
  let A := 4 * (v + 1) * (v + 2)
  let b := 4 * v ^ 2 + 10 * v + 5
  have hf : 0 < (4 * B).factorial := Nat.factorial_pos _
  have hLge : 840 ≤ L := by dsimp [L]; nlinarith
  have hv : v + 2 = L := by dsimp [v]; omega
  have hA : A ≠ 0 := by dsimp [A]; positivity
  obtain ⟨p, hpN, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq N (q := A) (a := b) hA
      (nearHalf_progression_coprime v)
  have hb_lt : b < A := by dsimp [b, A]; nlinarith
  have hpmodA : p % A = b := by
    change p % A = b % A at hmod
    simpa only [Nat.mod_eq_of_lt hb_lt] using hmod
  let t := p / A
  have hpform : p = nearHalfP v t := by
    have heq : p = A * t + b := by
      calc
        p = p % A + A * (p / A) := (Nat.mod_add_div p A).symm
        _ = A * t + b := by rw [hpmodA]; simp only [t, add_comm]
    calc
      p = A * t + b := heq
      _ = nearHalfP v t := by dsimp [A, b, nearHalfP]; ring
  have hpmult : p = L * (4 * (v + 1) * t + 4 * v + 2) + 1 := by
    rw [hpform]
    calc
      nearHalfP v t = (v + 2) * (4 * (v + 1) * t + 4 * v + 2) + 1 := by
        dsimp [nearHalfP]
        ring
      _ = L * (4 * (v + 1) * t + 4 * v + 2) + 1 := by rw [hv]
  have hpmodL : p % L = 1 := by
    rw [hpmult]
    simp [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < L)]
  have hmodL : Nat.ModEq L p 1 := by
    change p % L = 1 % L
    simpa only [Nat.mod_eq_of_lt (by omega : 1 < L)] using hpmodL
  refine ⟨p, nearHalfX v t, hpN, hp, by simpa only [L] using hpmodL,
    ?_, ?_, ?_⟩
  · rw [hpform]
    exact nearHalf_typeI v t
  · rw [hpform]
    exact nearHalf_good v t
  · intro m d hm hmB hd hdsq
    have hfact : 4 * m - 1 ∣ (4 * B).factorial :=
      Nat.dvd_factorial (by omega) (by omega)
    have hdivL : 4 * m - 1 ∣ L := by
      dsimp [L]
      exact dvd_mul_of_dvd_right hfact 840
    have hrem : p % (4 * m - 1) = 1 := by
      have hc := Nat.ModEq.of_dvd hdivL hmodL
      change p % (4 * m - 1) = 1 % (4 * m - 1) at hc
      simpa only [Nat.mod_eq_of_lt (by omega : 1 < 4 * m - 1)] using hc
    exact no_modular_divisor_if_one_remainder p m d hm hd hdsq hrem

/-- The obstruction above also excludes *actual* Type-II witnesses with
`m=(x+d)/(4x-p)≤B`, without excluding the exhibited Type-I solution. -/
theorem good_primes_escaping_bounded_typeII_at_x (B N : ℕ) :
    ∃ p : ℕ, N < p ∧ p.Prime ∧ p % 840 = 1 ∧ Good p ∧
      ∀ x d : ℕ, p < 4 * x → 2 * x < p →
        0 < d → d < x → d ∣ x ^ 2 → (4 * x - p) ∣ x + d →
        B < (x + d) / (4 * x - p) := by
  obtain ⟨p, x, hpN, hp, hmodL, _hI, hgood, hno⟩ :=
    typeI_primes_escaping_bounded_typeII B N
  have hdiv : 840 ∣ 840 * (4 * B).factorial := dvd_mul_right _ _
  have hmod840 : p % 840 = 1 := by
    have hbig : 1 < 840 * (4 * B).factorial := by
      have hf := Nat.factorial_pos (4 * B)
      nlinarith
    have hmod : Nat.ModEq (840 * (4 * B).factorial) p 1 := by
      change p % (840 * (4 * B).factorial) = 1 % (840 * (4 * B).factorial)
      simpa only [Nat.mod_eq_of_lt hbig] using hmodL
    have h840 := Nat.ModEq.of_dvd hdiv hmod
    change p % 840 = 1 % 840 at h840
    simpa using h840
  refine ⟨p, hpN, hp, hmod840, hgood, ?_⟩
  intro x d hlo hhi hd hdx hdsq hadiv
  obtain ⟨hm, hdm, _hh, hmod, _hx⟩ :=
    typeII_modular_parameter p x d hp hlo hhi hd hdx hdsq hadiv
  by_contra h
  have hle : (x + d) / (4 * x - p) ≤ B := by omega
  exact hno ((x + d) / (4 * x - p)) d hm hle hd hdm hmod

end Erdos242

#print axioms Erdos242.typeI_primes_escaping_bounded_typeII
#print axioms Erdos242.good_primes_escaping_bounded_typeII_at_x
