import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ :=
  ∑ k ∈ range n, (n.choose k) ^ 2 * multichoose n k

lemma term_mod_p_zero_of_ne_zero_of_ne_top {p r k : ℕ} (hp : Nat.Prime p)
    (hk0 : k ≠ 0) (hktop : k ≠ p ^ r) :
    ((p ^ r).choose k ^ 2 * (p ^ r).multichoose k : ℤ) ≡ 0 [ZMOD (p : ℕ)] := by
  have hdvd : p ∣ (p ^ r).choose k := hp.dvd_choose_pow hk0 hktop
  rw [Int.modEq_zero_iff_dvd]
  have hdvdz : (p : ℤ) ∣ ((p ^ r).choose k : ℤ) := Int.natCast_dvd_natCast.mpr hdvd
  simpa [pow_two, mul_assoc] using dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hdvdz (((p ^ r).choose k : ℤ))) (((p ^ r).multichoose k : ℤ))

lemma a_prime_power_mod_p {p r : ℕ} (hp : Nat.Prime p) (hrpos : 0 < r) :
    (a (p ^ r) : ℤ) ≡ 1 [ZMOD (p : ℕ)] := by
  rw [a]
  let N := p ^ r
  have hNpos : 0 < N := by exact pow_pos hp.pos r
  have hterms : ∀ k ∈ range N,
      (((N.choose k) ^ 2 * N.multichoose k : ℕ) : ℤ) ≡ (if k = 0 then (1 : ℤ) else 0) [ZMOD (p : ℕ)] := by
    intro k hk
    by_cases hk0 : k = 0
    · subst k
      simp [N]
    · have hklt : k < N := by simpa using hk
      have hktop : k ≠ N := _root_.ne_of_lt hklt
      have hz := term_mod_p_zero_of_ne_zero_of_ne_top (p := p) (r := r) (k := k) hp hk0 (by simpa [N] using hktop)
      simpa [hk0, N] using hz
  have hsum := Int.ModEq.sum (s := range N) hterms
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow] at hsum
  have hind : (∑ x ∈ range N, (if x = 0 then (1 : ℤ) else 0)) = 1 := by
    rw [sum_eq_single 0]
    · simp [hNpos]
    · intro b hb hb0
      simp [hb0]
    · intro h0
      exact (h0 (by simpa using hNpos)).elim
  simpa [hind, N] using hsum

example (p r : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 2 ≤ r) :
  (a (p ^ r) : ℤ) ≡ a (p ^ (r - 1)) [ZMOD (p : ℕ)] := by
  have h1 : (a (p ^ r) : ℤ) ≡ 1 [ZMOD (p : ℕ)] := a_prime_power_mod_p hp (by omega)
  have h2 : (a (p ^ (r - 1)) : ℤ) ≡ 1 [ZMOD (p : ℕ)] := a_prime_power_mod_p hp (by omega)
  exact h1.trans h2.symm
