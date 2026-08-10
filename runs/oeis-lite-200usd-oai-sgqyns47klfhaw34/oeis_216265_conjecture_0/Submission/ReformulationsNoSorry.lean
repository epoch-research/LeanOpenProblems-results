import FormalConjectures.Util.ProblemImports

open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

lemma A_pos_of_exists_prime {n p : ℕ}
    (hp : Nat.Prime p)
    (hlo : n ^ 3 - n < p)
    (hhi : p ≤ n ^ 3) :
    A216265 n > 0 := by
  unfold A216265 Nat.primeCounting Nat.primeCounting'
  simp only [gt_iff_lt, tsub_pos_iff_lt]
  have hlt : p < n ^ 3 + 1 := Nat.lt_succ_iff.mpr hhi
  have hge : n ^ 3 - n + 1 ≤ p := Nat.succ_le_iff.mpr hlo
  exact lt_of_le_of_lt
    (Nat.count_monotone Nat.Prime hge)
    (Nat.count_strict_mono hp hlt)

lemma exists_prime_of_A_pos {n : ℕ} (h : A216265 n > 0) :
    ∃ p, Nat.Prime p ∧ n ^ 3 - n < p ∧ p ≤ n ^ 3 := by
  unfold A216265 Nat.primeCounting Nat.primeCounting' at h
  have hlt : Nat.count Nat.Prime (n ^ 3 - n + 1) <
      Nat.count Nat.Prime (n ^ 3 + 1) := by
    exact Nat.lt_of_sub_pos h
  obtain ⟨p, hpI, hpprime⟩ := Nat.exists_of_count_lt_count (p := Nat.Prime) hlt
  exact ⟨p, hpprime, Nat.lt_of_succ_le hpI.1, Nat.le_of_lt_succ hpI.2⟩

lemma A_pos_iff_exists_prime (n : ℕ) :
    A216265 n > 0 ↔ ∃ p, Nat.Prime p ∧ n ^ 3 - n < p ∧ p ≤ n ^ 3 := by
  constructor
  · exact exists_prime_of_A_pos
  · rintro ⟨p, hp, hlo, hhi⟩
    exact A_pos_of_exists_prime hp hlo hhi

lemma n_le_cube_sub_self_of_two_le {n : ℕ} (hn : 2 ≤ n) : n ≤ n ^ 3 - n := by
  have h2n : 2 * n ≤ n ^ 3 := by
    nlinarith [sq_nonneg (n : ℤ), hn]
  exact Nat.le_sub_of_add_le (by simpa [two_mul] using h2n)

lemma interval_prime_dvd_choose {n p : ℕ} (hn : 2 ≤ n)
    (hp : Nat.Prime p) (hlo : n ^ 3 - n < p) (hhi : p ≤ n ^ 3) :
    p ∣ Nat.choose (n ^ 3) n := by
  have hnle : n ≤ n ^ 3 - n := n_le_cube_sub_self_of_two_le hn
  have ha : n < p := lt_of_le_of_lt hnle hlo
  exact hp.dvd_choose ha hlo hhi

lemma large_prime_dvd_choose_le {n p : ℕ}
    (hp : Nat.Prime p) (hdiv : p ∣ Nat.choose (n ^ 3) n) (hlo : n ^ 3 - n < p) :
    p ≤ n ^ 3 := by
  by_contra h
  have hgt : n ^ 3 < p := Nat.lt_of_not_ge h
  have hz : (Nat.choose (n ^ 3) n).factorization p = 0 := by
    exact Nat.factorization_choose_eq_zero_of_lt hgt
  have hchoose_ne : Nat.choose (n ^ 3) n ≠ 0 := by
    exact (Nat.choose_pos (by
      by_cases hn : n = 0
      · simp [hn]
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have : n ≤ n ^ 3 := by
          calc n = n * 1 := by rw [mul_one]
            _ ≤ n * (n * n) := Nat.mul_le_mul_left n (by nlinarith [hnpos])
            _ = n ^ 3 := by ring
        exact this)).ne'
  have hle : 1 ≤ (Nat.choose (n ^ 3) n).factorization p :=
    (Nat.Prime.dvd_iff_one_le_factorization hp hchoose_ne).mp hdiv
  omega

lemma exists_interval_prime_iff_large_prime_dvd_choose (n : ℕ) (hn : 2 ≤ n) :
    (∃ p, Nat.Prime p ∧ n ^ 3 - n < p ∧ p ≤ n ^ 3) ↔
    (∃ p, Nat.Prime p ∧ p ∣ Nat.choose (n ^ 3) n ∧ n ^ 3 - n < p) := by
  constructor
  · rintro ⟨p,hp,hlo,hhi⟩
    exact ⟨p,hp, interval_prime_dvd_choose hn hp hlo hhi, hlo⟩
  · rintro ⟨p,hp,hdiv,hlo⟩
    exact ⟨p,hp,hlo, large_prime_dvd_choose_le hp hdiv hlo⟩

-- A very compact restatement of the conjecture.
example (n : ℕ) (h : n > 13) : A216265 n > 0 ↔
    ∃ p, Nat.Prime p ∧ p ∣ Nat.choose (n ^ 3) n ∧ n ^ 3 - n < p := by
  exact (A_pos_iff_exists_prime n).trans (exists_interval_prime_iff_large_prime_dvd_choose n (by omega))
