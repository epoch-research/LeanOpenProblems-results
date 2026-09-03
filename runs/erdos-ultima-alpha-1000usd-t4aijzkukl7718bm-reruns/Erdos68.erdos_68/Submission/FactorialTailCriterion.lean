import FormalConjecturesUtil

/-!
An auxiliary factorial-tail descent criterion. This file does not settle Erdős 68:
the factorial Lambert coefficients do not satisfy the required tail bound.
-/

namespace FactorialTailCriterion

lemma integer_tail_descent (t : ℕ → ℤ) (N : ℕ)
    (hb : ∀ n ≥ N, 1 ≤ t n ∧ t n ≤ (n : ℤ) - 2)
    (hd : ∀ n ≥ N, (n : ℤ) ∣ t (n + 1) - t n + 1) : False := by
  let M := max N 3
  have hM : N ≤ M := le_max_left _ _
  have step (n : ℕ) (hn : M ≤ n) : t (n + 1) = t n - 1 := by
    have h0 := hb n (hM.trans hn)
    have h1 := hb (n + 1) (by omega)
    have hnpos : (0 : ℤ) < n := by dsimp [M] at hn; omega
    obtain ⟨k, hk⟩ := hd n (hM.trans hn)
    have hk0 : k = 0 := by
      by_contra h
      rcases lt_or_gt_of_ne h with h | h
      · have : k ≤ -1 := by omega
        have hm := mul_le_mul_of_nonneg_left this hnpos.le
        push_cast at h1
        nlinarith
      · have : 1 ≤ k := by omega
        have hm := mul_le_mul_of_nonneg_left this hnpos.le
        push_cast at h1
        nlinarith
    simp only [hk0, mul_zero] at hk
    omega
  have desc (k : ℕ) : t (M + k) = t M - k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show M + (k + 1) = (M + k) + 1 by omega, step (M + k) (by omega), ih]
      push_cast
      ring
  have htM := (hb M hM).1
  have hcast : ((t M).toNat : ℤ) = t M := Int.toNat_of_nonneg (by omega)
  have hlast := (hb (M + (t M).toNat) (by omega)).1
  rw [desc, hcast] at hlast
  omega

noncomputable def scaledTail (c : ℕ → ℤ) (n : ℕ) : ℝ :=
  (n.factorial : ℝ) *
    ((∑' k : ℕ, (c k : ℝ) / k.factorial) -
      ∑ k ∈ Finset.range (n + 1), (c k : ℝ) / k.factorial)

def factorialPrefix (c : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), c k * (n.factorial / k.factorial : ℕ)

lemma cast_factorialPrefix (c : ℕ → ℤ) (n : ℕ) :
    (factorialPrefix c n : ℝ) = (n.factorial : ℝ) *
      ∑ k ∈ Finset.range (n + 1), (c k : ℝ) / k.factorial := by
  simp only [factorialPrefix, Int.cast_sum, Int.cast_mul, Int.cast_natCast,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa using Finset.mem_range.mp hk
  rw [Nat.cast_div (Nat.factorial_dvd_factorial hkn) (by positivity : (k.factorial : ℝ) ≠ 0)]
  ring

lemma scaledTail_succ (c : ℕ → ℤ) (n : ℕ) :
    scaledTail c (n + 1) = (n + 1 : ℝ) * scaledTail c n - c (n + 1) := by
  unfold scaledTail
  rw [Finset.sum_range_succ]
  have hf : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
  rw [mul_sub, mul_sub, mul_add, mul_div_cancel₀ _ hf]
  rw [Nat.factorial_succ]
  push_cast
  ring

lemma irrational_of_small_congruent_tails (c : ℕ → ℤ) (N : ℕ)
    (hc : ∀ n ≥ N, (n : ℤ) ∣ c (n + 1) - 1)
    (ht : ∀ n ≥ N, 0 < scaledTail c n ∧ scaledTail c n < (n : ℝ) - 1) :
    Irrational (∑' k : ℕ, (c k : ℝ) / k.factorial) := by
  rintro ⟨q, hq⟩
  let t : ℕ → ℤ := fun n => q.num * (n.factorial / q.den : ℕ) - factorialPrefix c n
  have htcast (n : ℕ) (hn : q.den ≤ n) : (t n : ℝ) = scaledTail c n := by
    have hd : q.den ∣ n.factorial := Nat.dvd_factorial q.pos hn
    have hden : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
    simp only [t, scaledTail, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    rw [← hq, cast_factorialPrefix, Nat.cast_div hd hden, Rat.cast_def]
    ring
  apply integer_tail_descent t (max N q.den)
  · intro n hn
    have h := ht n ((le_max_left _ _).trans hn)
    rw [← htcast n ((le_max_right _ _).trans hn)] at h
    have h0 : (0 : ℤ) < t n := by exact_mod_cast h.1
    have h1 : t n < (n : ℤ) - 1 := by exact_mod_cast h.2
    omega
  · intro n hn
    have hrec : t (n + 1) = (n + 1 : ℤ) * t n - c (n + 1) := by
      have h := scaledTail_succ c n
      rw [← htcast n ((le_max_right _ _).trans hn),
        ← htcast (n + 1) (by omega)] at h
      exact_mod_cast h
    rw [hrec]
    have hd := hc n ((le_max_left _ _).trans hn)
    convert dvd_sub (dvd_mul_right (n : ℤ) (t n)) hd using 1 <;> ring

end FactorialTailCriterion

#print axioms FactorialTailCriterion.irrational_of_small_congruent_tails
