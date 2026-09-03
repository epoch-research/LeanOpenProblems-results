import Submission.Work

/-! A growing-precision necessary condition on the exponent.
No global descent or finiteness result is asserted. -/

namespace Erdos406Work

lemma scaledQuotient_zero (s : ℕ) : scaledQuotient 0 s = 0 := by
  have h := scaledQuotient_identity 0 s
  have hp : 0 < 3 ^ (s + 1) := by positivity
  simp only [zero_mul, pow_zero] at h
  nlinarith

lemma scaledQuotient_add (u v s : ℕ) :
    scaledQuotient (u + v) s = scaledQuotient u s + scaledQuotient v s +
      3 ^ (s + 1) * scaledQuotient u s * scaledQuotient v s := by
  have h : 4 ^ ((u + v) * 3 ^ s) = 4 ^ (u * 3 ^ s) * 4 ^ (v * 3 ^ s) := by
    rw [Nat.add_mul, pow_add]
  rw [scaledQuotient_identity, scaledQuotient_identity, scaledQuotient_identity] at h
  have hp : 0 < 3 ^ (s + 1) := by positivity
  apply Nat.eq_of_mul_eq_mul_left hp
  nlinarith only [h]

/-- The modulus increases with the power of three dividing the exponent.
This identity is valid for every u, not just for a finite list of unit parts. -/
lemma scaledQuotient_linear_mod (u s : ℕ) :
    Nat.ModEq (3 ^ (s + 1)) (scaledQuotient u s) (u * scaledQuotient 1 s) := by
  induction u with
  | zero => simp [scaledQuotient_zero, Nat.ModEq]
  | succ u ih =>
    change scaledQuotient (u + 1) s % 3 ^ (s + 1) =
      ((u + 1) * scaledQuotient 1 s) % 3 ^ (s + 1)
    rw [scaledQuotient_add]
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, zero_mul, Nat.zero_mod,
      add_zero, Nat.mod_mod, Nat.add_mul, one_mul]
    change scaledQuotient u s % 3 ^ (s + 1) =
      (u * scaledQuotient 1 s) % 3 ^ (s + 1) at ih
    rw [Nat.mul_mod] at ih
    rw [ih]
    simp only [Nat.mod_mod]

lemma scaledQuotient_linear_mod_of_le (u s r : ℕ) (hr : r ≤ s + 1) :
    Nat.ModEq (3 ^ r) (scaledQuotient u s) (u * scaledQuotient 1 s) :=
  (scaledQuotient_linear_mod u s).of_dvd (pow_dvd_pow 3 hr)

/-- Any good power in this family must pass a linear modular digit test.
The allowed unit parts have not been globally bounded. -/
lemma good_scaled_exponent_linear_bound {u s r : ℕ} (hr : r ≤ s + 1)
    (hg : Nat.digits 3 (4 ^ (u * 3 ^ s)) ⊆ [0, 1]) :
    2 * (u * scaledQuotient 1 s % 3 ^ r) < 3 ^ r := by
  have hm := scaledQuotient_linear_mod_of_le u s r hr
  by_contra h
  have hbad : 3 ^ r ≤ 2 * (scaledQuotient u s % 3 ^ r) := by
    rw [hm]
    omega
  exact bad_scaled_exponent_of_residue u s r hbad hg

#print axioms scaledQuotient_add
#print axioms scaledQuotient_linear_mod
#print axioms good_scaled_exponent_linear_bound
end Erdos406Work
