import FormalConjecturesUtil

/-!
An arithmetic limit of a particular first-moment certificate. This is not an
upper bound for arbitrary free graphs and does not settle Erdős 714. The
monomial budget in `first_moment_bound` is an explicit hypothesis, not an
asserted estimate for every sampling model or every code selection.
-/

namespace Erdos714TensorSampling

/-- If the usual edge and copy monomials already make deletion affordable,
the edge monomial cannot exceed the standard alteration scale. -/
theorem first_moment_bound (r : ℕ) (hr : 2 ≤ r) (n p : ℝ)
    (hn : 0 < n) (hp : 0 < p)
    (hbudget : n ^ (2*r) * p ^ (r*r) ≤ n^2*p) :
    (n^2*p)^(r+1) ≤ n^(2*r) := by
  have h₁ : 2*(r-1)+2 = 2*r := by omega
  have h₂ : (r+1)*(r-1)+1 = r*r := by
    have : r-1+1 = r := by omega
    nlinarith
  have hfactor : (n^2*p^(r+1))^(r-1)*(n^2*p) =
      n^(2*r)*p^(r*r) := by
    rw [mul_pow, ← pow_mul, ← pow_mul]
    calc
      n^(2*(r-1))*p^((r+1)*(r-1))*(n^2*p) =
          n^(2*(r-1)+2)*p^((r+1)*(r-1)+1) := by
        rw [pow_add, pow_add, pow_one]
        ring
      _ = _ := by rw [h₁, h₂]
  have hsmall : (n^2*p^(r+1))^(r-1) ≤ 1 := by
    apply (mul_le_mul_iff_left₀ (show 0 < n^2*p by positivity)).mp
    simpa only [mul_comm (n^2*p), hfactor, one_mul] using hbudget
  have hunit : n^2*p^(r+1) ≤ 1 :=
    (pow_le_one_iff_of_nonneg (by positivity) (by omega : r-1 ≠ 0)).mp hsmall
  calc
    (n^2*p)^(r+1) = n^(2*r)*(n^2*p^(r+1)) := by
      rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add]
      congr 1
    _ ≤ n^(2*r)*1 := mul_le_mul_of_nonneg_left hunit (by positivity)
    _ = n^(2*r) := mul_one _

/-- The same calculation with a fixed multiplicative loss. Integer powers
avoid any convention about real roots or asymptotic notation. -/
theorem first_moment_bound_with_constant (r : ℕ) (hr : 2 ≤ r)
    (n p K : ℝ) (hn : 0 < n) (hp : 0 < p)
    (hbudget : n^(2*r)*p^(r*r) ≤ K*(n^2*p)) :
    (n^2*p)^((r+1)*(r-1)) ≤ K*n^((2*r)*(r-1)) := by
  have h₁ : 2*(r-1)+2 = 2*r := by omega
  have h₂ : (r+1)*(r-1)+1 = r*r := by
    have : r-1+1 = r := by omega
    nlinarith
  have hfactor : (n^2*p^(r+1))^(r-1)*(n^2*p) =
      n^(2*r)*p^(r*r) := by
    rw [mul_pow, ← pow_mul, ← pow_mul]
    calc
      n^(2*(r-1))*p^((r+1)*(r-1))*(n^2*p) =
          n^(2*(r-1)+2)*p^((r+1)*(r-1)+1) := by
        rw [pow_add, pow_add, pow_one]
        ring
      _ = _ := by rw [h₁, h₂]
  have hsmall : (n^2*p^(r+1))^(r-1) ≤ K := by
    apply (mul_le_mul_iff_left₀ (show 0 < n^2*p by positivity)).mp
    simpa only [hfactor] using hbudget
  have hrew : (n^2*p)^(r+1) = n^(2*r)*(n^2*p^(r+1)) := by
    rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add]
    congr 1
  calc
    (n^2*p)^((r+1)*(r-1)) =
        n^((2*r)*(r-1))*(n^2*p^(r+1))^(r-1) := by
      rw [pow_mul, hrew, mul_pow, ← pow_mul]
    _ ≤ n^((2*r)*(r-1))*K :=
      mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = K*n^((2*r)*(r-1)) := mul_comm _ _

/-- At any fixed `r ≥ 2`, the target exponent forces bounded order if one also
imposes the unit first-moment bound. The edge parameter must be nonnegative. -/
theorem critical_size_budget (r : ℕ) (hr : 2 ≤ r)
    (n e c : ℝ) (hn : 0 < n) (he : 0 ≤ e) (hc : 0 < c)
    (htarget : c*n^(2*r-1) ≤ e^r) (hfirst : e^(r+1) ≤ n^(2*r)) :
    c^(r+1)*n^(r-1) ≤ 1 := by
  have hdeg : (2*r-1)*(r+1) = (2*r)*r+(r-1) := by
    have h₁ : 2*r-1+1 = 2*r := by omega
    have h₂ : r-1+1 = r := by omega
    nlinarith
  have hpow : c^(r+1)*n^((2*r-1)*(r+1)) ≤ n^((2*r)*r) := by
    calc
      c^(r+1)*n^((2*r-1)*(r+1)) = (c*n^(2*r-1))^(r+1) := by
        rw [mul_pow, ← pow_mul]
      _ ≤ (e^r)^(r+1) := pow_le_pow_left₀ (by positivity) htarget _
      _ = (e^(r+1))^r := by simp only [← pow_mul, Nat.mul_comm]
      _ ≤ (n^(2*r))^r := pow_le_pow_left₀ (pow_nonneg he _) hfirst _
      _ = n^((2*r)*r) := (pow_mul _ _ _).symm
  rw [hdeg, pow_add n ((2*r)*r) (r-1)] at hpow
  apply (mul_le_mul_iff_right₀ (pow_pos hn ((2*r)*r))).mp
  simpa only [mul_one, mul_assoc, mul_left_comm, mul_comm] using hpow

/-- A Sidorenko-type lower monomial and an upper deletion budget imply the same
bound. Neither hypothesis is silently assumed for a proposed tensor code. -/
theorem copy_budget_bound (r : ℕ) (hr : 2 ≤ r) (n p b : ℝ)
    (hn : 0 < n) (hp : 0 < p)
    (hlower : n^(2*r)*p^(r*r) ≤ b) (hdelete : b ≤ n^2*p) :
    (n^2*p)^(r+1) ≤ n^(2*r) :=
  first_moment_bound r hr n p hn hp (hlower.trans hdelete)

/-- The fourth-case target and the first-moment scale cannot coexist at
unbounded orders with a fixed positive target constant. This is conditional
on the first-moment bound, not a disproof of the fourth case. -/
theorem fourth_case_size_budget (n e c : ℝ) (hn : 0 < n) (hc : 0 < c)
    (he : 0 ≤ e) (htarget : c*n^7 ≤ e^4) (hfirst : e^5 ≤ n^8) :
    c^5*n^3 ≤ 1 := by
  have hpow : c^5*n^35 ≤ n^32 := by
    calc
      c^5*n^35 = (c*n^7)^5 := by ring
      _ ≤ (e^4)^5 := pow_le_pow_left₀ (by positivity) htarget 5
      _ = (e^5)^4 := by ring
      _ ≤ (n^8)^4 := pow_le_pow_left₀ (pow_nonneg he 5) hfirst 4
      _ = n^32 := by ring
  have hf : c^5*n^35 = n^32*(c^5*n^3) := by ring
  rw [hf] at hpow
  exact (mul_le_mul_iff_right₀ (pow_pos hn 32)).mp (by simpa using hpow)

end Erdos714TensorSampling

#print axioms Erdos714TensorSampling.first_moment_bound
#print axioms Erdos714TensorSampling.copy_budget_bound
#print axioms Erdos714TensorSampling.fourth_case_size_budget

#print axioms Erdos714TensorSampling.first_moment_bound_with_constant
#print axioms Erdos714TensorSampling.critical_size_budget
