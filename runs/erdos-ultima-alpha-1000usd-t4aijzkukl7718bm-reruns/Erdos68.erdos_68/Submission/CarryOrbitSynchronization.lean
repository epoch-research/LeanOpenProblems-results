import Submission.ExplicitCarryOrbit

/-!
Rational initial states synchronize in the prime/composite carry recurrence.
This holds for arbitrary rational forcing. It is not an irrationality result.
-/

namespace CarryOrbitSynchronization

/-- The forcing at the step with original index `r+4`. -/
def step (f : ℕ → ℚ) (r : ℕ) (x : ℚ) : ℚ :=
  let v := (r+4 : ℚ)*x+f r
  if (r+4).Prime then v else v-(r+3)*(⌊v/(r+3)⌋ : ℤ)

def run (f : ℕ → ℚ) (x : ℚ) : ℕ → ℚ
  | 0 => x
  | r+1 => step f r (run f x r)

lemma step_difference (f : ℕ → ℚ) (r : ℕ) (x y : ℚ) :
    ∃ k : ℤ, step f r x-step f r y = (r+4 : ℚ)*(x-y)-k := by
  by_cases hp : (r+4).Prime
  · refine ⟨0, ?_⟩
    simp only [step, if_pos hp, Int.cast_zero, sub_zero]
    ring
  · refine ⟨(r+3 : ℤ)*(⌊((r+4 : ℚ)*x+f r)/(r+3)⌋ -
        ⌊((r+4 : ℚ)*y+f r)/(r+3)⌋), ?_⟩
    simp only [step, if_neg hp]
    push_cast
    ring

lemma run_difference (f : ℕ → ℚ) (x y : ℚ) (r : ℕ) :
    ∃ k : ℤ, run f x r-run f y r = ((4 : ℕ).ascFactorial r : ℚ)*(x-y)-k := by
  induction r with
  | zero => exact ⟨0, by simp [run]⟩
  | succ r ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨j, hj⟩ := step_difference f r (run f x r) (run f y r)
    refine ⟨(r+4 : ℤ)*k+j, ?_⟩
    simp only [run, hj, hk, Nat.ascFactorial_succ]
    push_cast
    ring

lemma rational_multiple_integral (q : ℚ) (r : ℕ) (hr : q.den ≤ r) :
    ∃ k : ℤ, ((4 : ℕ).ascFactorial r : ℚ)*q = k := by
  have hd : q.den ∣ (4 : ℕ).ascFactorial r :=
    (Nat.dvd_factorial q.pos hr).trans (Nat.factorial_dvd_ascFactorial 4 r)
  obtain ⟨k, hk⟩ := hd
  refine ⟨(k : ℤ)*q.num, ?_⟩
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  calc
    _ = (q.den : ℚ)*k*((q.num : ℚ)/q.den) := by
      rw [hk, q.num_div_den]
      push_cast
      rfl
    _ = _ := by push_cast; field_simp

lemma run_difference_integral (f : ℕ → ℚ) (x y : ℚ) (r : ℕ)
    (hr : (x-y).den ≤ r) :
    ∃ k : ℤ, run f x r-run f y r = k := by
  obtain ⟨k, hk⟩ := run_difference f x y r
  obtain ⟨j, hj⟩ := rational_multiple_integral (x-y) r hr
  exact ⟨j-k, by rw [hk, hj]; push_cast; rfl⟩

lemma composite_step_eq_of_multiple (f : ℕ → ℚ) (r : ℕ)
    (hp : ¬(r+4).Prime) (x y : ℚ) (k : ℤ)
    (hxy : x-y = (r+3 : ℚ)*k) : step f r x = step f r y := by
  have hm : (r+3 : ℚ) ≠ 0 := by positivity
  have he : ((r+4 : ℚ)*x+f r)/(r+3) =
      ((r+4 : ℚ)*y+f r)/(r+3)+((r+4 : ℤ)*k : ℤ) := by
    push_cast
    field_simp
    nlinarith [hxy]
  simp only [step, if_neg hp, he, Int.floor_add_intCast]
  push_cast
  nlinarith [hxy]

/-- Once the incoming difference is integral, a prime and its successor
remove it exactly. -/
lemma prime_reset (f : ℕ → ℚ) (x y : ℚ) (r : ℕ)
    (hp : (r+4).Prime) (k : ℤ)
    (hxy : run f x r-run f y r = k) :
    run f x (r+2) = run f y (r+2) := by
  have hnp : ¬(r+5).Prime := by
    have ho := hp.eq_two_or_odd.resolve_left (by omega)
    intro hq
    have ho' := hq.eq_two_or_odd.resolve_left (by omega)
    omega
  have hnext : run f x (r+1)-run f y (r+1) = (r+4 : ℚ)*k := by
    simp only [run, step, if_pos hp]
    nlinarith [hxy]
  exact composite_step_eq_of_multiple f (r+1) (by simpa [Nat.add_assoc] using hnp)
    (run f x (r+1)) (run f y (r+1)) k (by convert hnext using 1; push_cast; ring)

lemma equality_persists (f : ℕ → ℚ) (x y : ℚ) (N : ℕ)
    (he : run f x N = run f y N) : ∀ r ≥ N, run f x r = run f y r := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base => exact he
  | succ r hr ih => simp only [run, ih]

/-- Synchronization occurs after any sufficiently late prime. -/
theorem synchronize_after_prime (f : ℕ → ℚ) (x y : ℚ) (r : ℕ)
    (hp : (r+4).Prime) (hr : (x-y).den ≤ r) :
    ∀ n ≥ r+2, run f x n = run f y n := by
  obtain ⟨k, hk⟩ := run_difference_integral f x y r hr
  exact equality_persists f x y (r+2) (prime_reset f x y r hp k hk)

/-- All rational initial states have the same eventual orbit, for arbitrary
rational forcing. No distribution statement about that orbit follows. -/
theorem eventually_equal (f : ℕ → ℚ) (x y : ℚ) :
    ∃ N, ∀ n ≥ N, run f x n = run f y n := by
  obtain ⟨p, hlarge, hp⟩ := Nat.exists_infinite_primes ((x-y).den+4)
  have hp4 : 4 ≤ p := by omega
  refine ⟨p-4+2, synchronize_after_prime f x y (p-4) ?_ ?_⟩
  · simpa [Nat.sub_add_cancel hp4] using hp
  · omega

lemma actual_orbit (r : ℕ) :
    run CongruencePreservingCarry.delta (16/5) r = ExplicitCarryOrbit.orbit r := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [run, step, CongruencePreservingCarry.delta,
      ExplicitCarryOrbit.orbit, ih]

/-- Changing the rational initial value cannot change the eventual actual
carry orbit. This does not prove that it escapes the rationality pattern. -/
theorem eventually_actual_orbit (x : ℚ) :
    ∃ N, ∀ n ≥ N,
      run CongruencePreservingCarry.delta x n = ExplicitCarryOrbit.orbit n := by
  obtain ⟨N, hN⟩ := eventually_equal CongruencePreservingCarry.delta x (16/5)
  exact ⟨N, fun n hn => (hN n hn).trans (actual_orbit n)⟩

/-- The existing small-fraction criterion can be tested with any rational
initial state. The infinite-occurrence hypothesis is still required. -/
theorem irrational_of_frequent_small_fraction (x : ℚ)
    (h : ∀ N : ℕ, ∃ r ≥ N,
      Int.fract (run CongruencePreservingCarry.delta x r) ≤ (1/2 : ℚ)) :
    Irrational (∑' n : ℕ, Erdos68Development.term n) := by
  obtain ⟨N, hN⟩ := eventually_actual_orbit x
  apply ExplicitCarryOrbit.irrational_of_frequent_small_fraction
  intro M
  obtain ⟨r, hr, hf⟩ := h (max M N)
  refine ⟨r, (le_max_left _ _).trans hr, ?_⟩
  rw [← hN r ((le_max_right _ _).trans hr)]
  exact hf

end CarryOrbitSynchronization

#print axioms CarryOrbitSynchronization.synchronize_after_prime
#print axioms CarryOrbitSynchronization.eventually_equal
#print axioms CarryOrbitSynchronization.eventually_actual_orbit

#print axioms CarryOrbitSynchronization.irrational_of_frequent_small_fraction
