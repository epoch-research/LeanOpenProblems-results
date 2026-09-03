import Submission.Investigation

/-! Uniform obstructions to prime walks with eventually periodic increments. -/
namespace Erdos952Investigation

set_option maxHeartbeats 0

lemma prime_arithmetic_progression_not_injective (a b : GaussianInt)
    (h : ∀ n : ℕ, Prime (a + (n : GaussianInt) * b)) :
    ¬ Function.Injective (fun n : ℕ => a + (n : GaussianInt) * b) := by
  intro hinj
  have ha : Prime a := by simpa using h 0
  have ha1 : a.norm.natAbs ≠ 1 := by
    intro he
    have hnorm : a.norm = 1 := by
      have hnonneg := GaussianInt.norm_nonneg a
      have hcast := Int.natCast_natAbs a.norm
      omega
    exact ha.not_unit ((Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) a).mp hnorm)
  obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd ha1
  have hpdiv : (p : ℤ) ∣ a.norm := by
    exact Int.natCast_dvd.mpr hpa
  let y : ℕ → GaussianInt := fun n => a + ((p * n : ℕ) : GaussianInt) * b
  have hyinj : Function.Injective y := by
    intro i j hij
    have he : p * i = p * j := hinj hij
    exact Nat.eq_of_mul_eq_mul_left hp.pos he
  have hbound : ∀ n, (y n).norm ≤ (p : ℤ)^2 := by
    intro n
    apply prime_norm_divisor_bound (h (p * n)) hp
    obtain ⟨k, hk⟩ := hpdiv
    refine ⟨k + (n : ℤ) * (2 * a.re * b.re + 2 * a.im * b.im) +
      (p : ℤ) * (n : ℤ)^2 * (b.re^2 + b.im^2), ?_⟩
    dsimp [y]
    simp only [gaussian_norm_sq, Zsqrtd.re_add, Zsqrtd.im_add,
      Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_natCast, Zsqrtd.im_natCast,
      Nat.cast_mul, zero_mul, mul_zero, add_zero]
    rw [gaussian_norm_sq] at hk
    nlinarith [hk]
  obtain ⟨N, hN⟩ := injective_escapes_norm y hyinj ((p : ℤ)^2)
  have := hN N le_rfl
  have := hbound N
  omega

/-- An injective sequence of Gaussian primes cannot have an eventually periodic
sequence of increments, regardless of the size of its steps. -/
theorem prime_walk_increments_not_eventually_periodic (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hprime : ∀ n, Prime (x n)) :
    ¬ ∃ N k : ℕ, 0 < k ∧ ∀ n ≥ N,
      x (n + k + 1) - x (n + k) = x (n + 1) - x n := by
  rintro ⟨N, k, hk, hperiod⟩
  let d := x (N + k) - x N
  have hshift : ∀ m : ℕ, x (N + m + k) - x (N + m) = d := by
    intro m
    induction m with
    | zero => simp [d]
    | succ m ih =>
      have hp := hperiod (N + m) (Nat.le_add_right _ _)
      have he : N + (m + 1) + k = N + m + k + 1 := by omega
      rw [he, show N + (m + 1) = N + m + 1 by omega]
      calc
        _ = (x (N + m + k + 1) - x (N + m + k)) +
          (x (N + m + k) - x (N + m)) -
          (x (N + m + 1) - x (N + m)) := by abel
        _ = d := by rw [hp, ih]; abel
  have hformula : ∀ m : ℕ, x (N + k * m) = x N + (m : GaussianInt) * d := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have he : N + k * (m + 1) = N + k * m + k := by ring
      rw [he, eq_add_of_sub_eq (hshift (k * m)), ih]
      push_cast
      ring
  apply prime_arithmetic_progression_not_injective (x N) d
    (fun m => hformula m ▸ hprime (N + k * m))
  intro i j hij
  have he : N + k * i = N + k * j := hx (by simpa only [hformula] using hij)
  exact Nat.mul_left_cancel hk (Nat.add_left_cancel he)

#print axioms prime_arithmetic_progression_not_injective
#print axioms prime_walk_increments_not_eventually_periodic

end Erdos952Investigation
