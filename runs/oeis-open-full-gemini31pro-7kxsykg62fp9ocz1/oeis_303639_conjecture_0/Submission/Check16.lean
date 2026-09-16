import Mathlib

lemma no_sum_sq_of_padic (R q k M : ℕ)
    (hq_prime : q.Prime)
    (hR : R = q ^ (2 * k + 1) * M)
    (hM : ¬ q ∣ M)
    (hq3 : q % 4 = 3) :
    ∀ a b : ℕ, a ^ 2 + b ^ 2 ≠ R := by
  intro a b hab
  have h_eq : ∃ x y, R = x ^ 2 + y ^ 2 := ⟨a, b, hab.symm⟩
  have h_iff := Nat.eq_sq_add_sq_iff.mp h_eq q
  -- now we need to show q ∈ R.primeFactors and padicValNat q R is not Even
  sorry
