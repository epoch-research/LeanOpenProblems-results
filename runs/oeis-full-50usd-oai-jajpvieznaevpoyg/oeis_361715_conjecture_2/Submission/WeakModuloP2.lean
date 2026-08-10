import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ :=
  ∑ k ∈ range n, (n.choose k) ^ 2 * multichoose n k

lemma term_mod_p2_zero_of_ne_zero_of_ne_top {p r k : ℕ} (hp : Nat.Prime p)
    (hk0 : k ≠ 0) (hktop : k ≠ p ^ r) :
    ((p ^ r).choose k ^ 2 * (p ^ r).multichoose k : ℤ) ≡ 0 [ZMOD (p ^ 2 : ℕ)] := by
  have hdvd : p ∣ (p ^ r).choose k := hp.dvd_choose_pow hk0 hktop
  rw [Int.modEq_zero_iff_dvd]
  rcases hdvd with ⟨c, hc⟩
  have hcz : (((p ^ r).choose k : ℕ) : ℤ) = (p : ℤ) * c := by exact_mod_cast hc
  rw [pow_two, hcz]
  have hdiv : (p : ℤ) * (p : ℤ) ∣ ((p : ℤ) * (p : ℤ)) * ((c : ℤ) ^ 2 * (((p ^ r).multichoose k : ℕ) : ℤ)) := by
    exact dvd_mul_right ((p : ℤ) * (p : ℤ)) _
  convert hdiv using 1 <;> ring

lemma a_prime_power_mod_p2 {p r : ℕ} (hp : Nat.Prime p) :
    (a (p ^ r) : ℤ) ≡ 1 [ZMOD (p ^ 2 : ℕ)] := by
  rw [a]
  let N := p ^ r
  have hNpos : 0 < N := by exact pow_pos hp.pos r
  have hterms : ∀ k ∈ range N,
      (((N.choose k) ^ 2 * N.multichoose k : ℕ) : ℤ) ≡ (if k = 0 then (1 : ℤ) else 0) [ZMOD (p ^ 2 : ℕ)] := by
    intro k hk
    by_cases hk0 : k = 0
    · subst k
      simp [N]
    · have hklt : k < N := by simpa using hk
      have hktop : k ≠ N := _root_.ne_of_lt hklt
      have hz := term_mod_p2_zero_of_ne_zero_of_ne_top (p := p) (r := r) (k := k) hp hk0 (by simpa [N] using hktop)
      simpa [hk0, N] using hz
  have hsum := Int.ModEq.sum (s := range N) hterms
  simp only [Nat.cast_mul, Nat.cast_pow] at hsum
  have hind : (∑ x ∈ range N, (if x = 0 then (1 : ℤ) else 0)) = 1 := by
    rw [sum_eq_single 0]
    · simp
    · intro b hb hb0
      simp [hb0]
    · intro h0
      exact (h0 (by simpa using hNpos)).elim
  simpa [hind, N] using hsum

example (p r : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 2 ≤ r) :
  (a (p ^ r) : ℤ) ≡ a (p ^ (r - 1)) [ZMOD (p ^ 2 : ℕ)] := by
  have h1 : (a (p ^ r) : ℤ) ≡ 1 [ZMOD (p ^ 2 : ℕ)] := a_prime_power_mod_p2 hp
  have h2 : (a (p ^ (r - 1)) : ℤ) ≡ 1 [ZMOD (p ^ 2 : ℕ)] := a_prime_power_mod_p2 hp
  exact h1.trans h2.symm
