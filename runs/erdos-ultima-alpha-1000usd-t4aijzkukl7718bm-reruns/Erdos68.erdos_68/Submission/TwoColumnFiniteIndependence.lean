import FormalConjecturesUtil

/-!
Finite independence of two factorial columns for small integer coefficients.
This is auxiliary arithmetic, not a proof of Erdős 68.
-/

namespace TwoColumnFiniteIndependence

open Finset

def numerator (r : ℕ → ℕ) (c : ℕ → ℤ) : ℕ → ℤ
  | 0 => c 0
  | n + 1 => (r n : ℤ) * numerator r c n + c (n + 1)

lemma scaled_sum (d r : ℕ → ℕ) (c : ℕ → ℤ)
    (hd : ∀ n, 0 < d n) (hr : ∀ n, d (n+1) = r n * d n) (N : ℕ) :
    (d N : ℚ) * (∑ i ∈ range (N+1), (c i : ℚ) / d i) = numerator r c N := by
  induction N with
  | zero =>
    have hn : (d 0 : ℚ) ≠ 0 := by exact_mod_cast (hd 0).ne'
    simp [numerator, hn, mul_div_cancel₀]
  | succ N ih =>
    rw [sum_range_succ, mul_add]
    have hn : (d (N+1) : ℚ) ≠ 0 := by exact_mod_cast (hd (N+1)).ne'
    rw [mul_div_cancel₀ _ hn, hr]
    simp only [Nat.cast_mul, numerator, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    rw [mul_assoc, ih]

lemma numerator_zero (r : ℕ → ℕ) (c : ℕ → ℤ) (N : ℕ)
    (hr : ∀ i < N, 0 < r i)
    (hc : ∀ i < N, |c (i+1)| < (r i : ℤ))
    (hz : numerator r c N = 0) : ∀ i ≤ N, c i = 0 := by
  induction N with
  | zero => simpa [numerator] using hz
  | succ N ih =>
    have hd : (r N : ℤ) ∣ c (N+1) := by
      refine ⟨-numerator r c N, ?_⟩
      dsimp only [numerator] at hz
      linarith
    have hlast := Int.eq_zero_of_abs_lt_dvd hd (hc N (by omega))
    have hprev : numerator r c N = 0 := by
      simp only [numerator, hlast, add_zero] at hz
      have hn : (r N : ℤ) ≠ 0 := by exact_mod_cast (hr N (by omega)).ne'
      exact (mul_eq_zero.mp hz).resolve_left hn
    intro i hi
    by_cases he : i = N+1
    · simpa [he] using hlast
    · exact ih (fun j hj => hr j (by omega)) (fun j hj => hc j (by omega)) hprev i
        (by omega)

/-- Finite uniqueness for integer digits strictly smaller than successive
integer denominator ratios. -/
theorem chain_zero (d r : ℕ → ℕ) (c : ℕ → ℤ) (N : ℕ)
    (hd : ∀ n, 0 < d n) (hr : ∀ n, d (n+1) = r n * d n)
    (hrpos : ∀ i < N, 0 < r i)
    (hc : ∀ i < N, |c (i+1)| < (r i : ℤ))
    (hz : (∑ i ∈ range (N+1), (c i : ℚ) / d i) = 0) :
    ∀ i ≤ N, c i = 0 := by
  have h := scaled_sum d r c hd hr N
  rw [hz, mul_zero] at h
  apply numerator_zero r c N hrpos hc
  exact_mod_cast h.symm

lemma square_factorial_zero (H N : ℕ) (c : ℕ → ℤ)
    (hc : ∀ i ≤ N, |c i| ≤ (H : ℤ)^2)
    (hz : (∑ i ∈ range (N+1), (c i : ℚ) / ((H+i).factorial : ℚ)^2) = 0) :
    ∀ i ≤ N, c i = 0 := by
  apply chain_zero (fun i => (H+i).factorial^2) (fun i => (H+i+1)^2) c N
  · intro i
    positivity
  · intro i
    rw [show H+(i+1) = H+i+1 by omega, Nat.factorial_succ, mul_pow]
  · intro i _
    positivity
  · intro i hi
    have h := hc (i+1) (by omega)
    have hH : (0 : ℤ) ≤ H := by positivity
    have hi' : (0 : ℤ) ≤ i := by positivity
    push_cast
    nlinarith
  · simpa only [Nat.cast_pow] using hz

lemma odd_factorial_zero (H N : ℕ) (c : ℕ → ℤ)
    (hc : ∀ i ≤ N, |c i| ≤ (H : ℤ)^2)
    (hz : (∑ i ∈ range (N+1), (c i : ℚ) / (2*H+2*i+1).factorial) = 0) :
    ∀ i ≤ N, c i = 0 := by
  apply chain_zero (fun i => (2*H+2*i+1).factorial)
    (fun i => (2*H+2*i+3)*(2*H+2*i+2)) c N
  · intro i
    positivity
  · intro i
    rw [show 2*H+2*(i+1)+1 = (2*H+2*i+1)+1+1 by omega,
      Nat.factorial_succ, Nat.factorial_succ]
    ring
  · intro i _
    positivity
  · intro i hi
    have h := hc (i+1) (by omega)
    have hH : (0 : ℤ) ≤ H := by positivity
    have hi' : (0 : ℤ) ≤ i := by positivity
    push_cast
    nlinarith [sq_nonneg (H : ℤ), sq_nonneg (i : ℤ)]
  · exact hz

/-- In a finite even/odd block, small integer coefficients cannot annihilate
both the factorial column and the even square-factorial column. -/
theorem two_column_zero (H N : ℕ) (a b : ℕ → ℤ)
    (ha : ∀ i ≤ N, |a i| ≤ (H : ℤ)^2)
    (hb : ∀ i ≤ N, |b i| ≤ (H : ℤ)^2)
    (hfirst : (∑ i ∈ range (N+1),
      ((a i : ℚ) / (2*H+2*i).factorial +
      (b i : ℚ) / (2*H+2*i+1).factorial)) = 0)
    (hsecond : (∑ i ∈ range (N+1),
      (a i : ℚ) / ((H+i).factorial : ℚ)^2) = 0) :
    (∀ i ≤ N, a i = 0) ∧ (∀ i ≤ N, b i = 0) := by
  have hae := square_factorial_zero H N a ha hsecond
  refine ⟨hae, odd_factorial_zero H N b hb ?_⟩
  convert hfirst using 1
  apply sum_congr rfl
  intro i hi
  rw [hae i (by have := mem_range.mp hi; omega)]
  simp

#print axioms chain_zero
#print axioms square_factorial_zero
#print axioms odd_factorial_zero
#print axioms two_column_zero

end TwoColumnFiniteIndependence
