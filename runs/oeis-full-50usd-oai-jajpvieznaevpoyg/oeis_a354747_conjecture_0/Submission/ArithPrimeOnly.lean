import FormalConjectures.Util.ProblemImports

namespace ArithPrimeOnly

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

end ArithPrimeOnly
