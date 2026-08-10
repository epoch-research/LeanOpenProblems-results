import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 200000


namespace ArithLemma

def M : ℕ := 2 * 100943 * 3 ^ 39101

lemma prime100943 : Nat.Prime 100943 := by norm_num

lemma prime_dvd_M {r : ℕ} (hrp : Nat.Prime r) (hr : r ∣ M) : r = 2 ∨ r = 3 ∨ r = 100943 := by
  unfold M at hr
  rcases (hrp.dvd_mul.mp hr) with hleft | h3pow
  · rcases (hrp.dvd_mul.mp hleft) with h2 | h100943
    · left
      exact (Nat.prime_dvd_prime_iff_eq hrp Nat.prime_two).mp h2
    · right; right
      exact (Nat.prime_dvd_prime_iff_eq hrp prime100943).mp h100943
  · right; left
    have h3 : r ∣ 3 := hrp.dvd_of_dvd_pow h3pow
    exact (Nat.prime_dvd_prime_iff_eq hrp (by norm_num : Nat.Prime 3)).mp h3

lemma dvd_div_of_mul_eq_of_prime_dvd_cofactor {d c q M : ℕ}
    (hqpos : 0 < q) (hM : M = d * c) (hqc : q ∣ c) : d ∣ M / q := by
  rcases hqc with ⟨c', hc'⟩
  subst c
  refine ⟨c', ?_⟩
  rw [hM]
  have hcomm : d * (q * c') = q * (d * c') := by ring
  rw [hcomm, Nat.mul_div_cancel_left _ hqpos]

lemma divisor_eq_M {d : ℕ} (hd : d ∣ M)
    (h2 : ¬ d ∣ M / 2) (h3 : ¬ d ∣ M / 3) (h100943 : ¬ d ∣ M / 100943) : d = M := by
  rcases hd with ⟨c, hM'⟩
  have hM : M = d * c := hM'
  have hc1 : c = 1 := by
    rw [Nat.eq_one_iff_not_exists_prime_dvd]
    intro r hrp hrc
    have hrM : r ∣ M := by
      rw [hM]
      exact dvd_mul_of_dvd_right hrc d
    rcases prime_dvd_M hrp hrM with rfl | rfl | rfl
    · exact h2 (dvd_div_of_mul_eq_of_prime_dvd_cofactor (by norm_num) hM hrc)
    · exact h3 (dvd_div_of_mul_eq_of_prime_dvd_cofactor (by norm_num) hM hrc)
    · exact h100943 (dvd_div_of_mul_eq_of_prime_dvd_cofactor (by norm_num) hM hrc)
  rw [hM, hc1, mul_one]

end ArithLemma
